import java.util.*;
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;

public class AnalysisTransformer extends SceneTransformer {

    static CallGraph cg;

    // ── Instance fields (shared across ALL method analyses) ───────────────────
    final Map<Integer, String>       allocLabels      = new LinkedHashMap<>();
    final Map<Integer, Boolean>      isSR             = new LinkedHashMap<>();
    final Map<Integer, Set<Integer>> escapeLines      = new LinkedHashMap<>();
    final Set<SootMethod>            analyzedForAlloc = new HashSet<>();

    @Override
    protected void internalTransform(String phaseName, Map<String, String> options) {
        // Store the call graph once as a static field...
        cg = Scene.v().getCallGraph();

        // This code lets us get the main method, our testcases will only have one start point that is the main m
        // in the Test class...
        var entrypoints = Scene.v().getEntryPoints();
        assert (entrypoints.size() == 1);
        SootMethod entryMethod = entrypoints.get(0);

        handleMainMethod(entryMethod);
    }

    void handleMainMethod(SootMethod myMethod) {
        // Get the body
        Body body = myMethod.getActiveBody();

        analyzeMethodAllocations(body, new HashSet<>());

        // ── Print output ──────────────────────────────────────────────────────
        List<Integer> sortedSites = new ArrayList<>(allocLabels.keySet());
        Collections.sort(sortedSites);

        for (int site : sortedSites) {
            String label = allocLabels.get(site);
            if (!isSR.getOrDefault(site, false)) {
                System.out.println(label + " = N");
            } else {
                Set<Integer> lines = escapeLines.get(site);
                StringBuilder sb = new StringBuilder();
                sb.append(label).append(" = Y[");
                boolean first = true;
                for (int l : lines) {
                    if (!first) sb.append(",");
                    sb.append(l);
                    first = false;
                }
                sb.append("]");
                System.out.println(sb.toString());
            }
        }
    }

    void analyzeMethodAllocations(Body body, Set<SootMethod> callStack) {
        SootMethod method = body.getMethod();

        if (analyzedForAlloc.contains(method)) return;
        analyzedForAlloc.add(method);

        // local → set of alloc-site lines it may point to (flow-sensitive,
        // tracks only objects NEW'd in THIS body)
        Map<Local, Set<Integer>> pointsTo = new HashMap<>();

        // ── BUG 3 FIX: field-content map ─────────────────────────────────────
        // Tracks what allocation sites are stored in each local object's fields.
        // Needed to propagate pointsTo through field stores and loads like:
        //   b.a = a;       ← store:  fieldContents[b]["sig"] = {21}
        //   A q = b.a;     ← load:   pointsTo[q] = fieldContents[b]["sig"] = {21}
        // Without this, 'q' has empty pointsTo and O21 never gets escape lines.
        Map<Local, Map<String, Set<Integer>>> fieldContents = new HashMap<>();

        // ── Pass 1: register every allocation site in this body ──────────────
        for (Unit u : body.getUnits()) {
            Stmt stmt = (Stmt) u;
            if (stmt instanceof AssignStmt) {
                AssignStmt assign = (AssignStmt) stmt;
                if (assign.getRightOp() instanceof NewExpr
                        && assign.getLeftOp() instanceof Local) {
                    int line = stmt.getJavaSourceStartLineNumber();
                    allocLabels.put(line, "O" + line);
                    isSR.put(line, true);
                    escapeLines.put(line, new TreeSet<>());
                }
            }
        }

        // ── Pass 2: flow-sensitive scan ───────────────────────────────────────
        // Iterate over statements
        for (Unit u : body.getUnits()) {
            Stmt stmt = (Stmt) u;
            int lineNumber = stmt.getJavaSourceStartLineNumber();

            // Track assignments so we always know what each local points to
            if (stmt instanceof AssignStmt) {
                AssignStmt assign = (AssignStmt) stmt;
                Value lhs = assign.getLeftOp();
                Value rhs = assign.getRightOp();

                if (rhs instanceof NewExpr && lhs instanceof Local) {
                    // x = new T()  →  x points only to this allocation site
                    Set<Integer> pts = new HashSet<>();
                    pts.add(lineNumber);
                    pointsTo.put((Local) lhs, pts);

                } else if (rhs instanceof Local && lhs instanceof Local) {
                    // x = y  →  copy points-to set
                    Set<Integer> src = pointsTo.getOrDefault(
                            (Local) rhs, Collections.emptySet());
                    pointsTo.put((Local) lhs, new HashSet<>(src));

                } else if (lhs instanceof StaticFieldRef && rhs instanceof Local) {
                    // StaticField = x  →  escapes to GLOBAL → always NOT SR
                    for (int site : pointsTo.getOrDefault(
                            (Local) rhs, Collections.emptySet())) {
                        isSR.put(site, false);
                    }

                } else if (lhs instanceof ArrayRef && rhs instanceof Local) {
                    // arr[i] = x  →  x escapes into heap array → NOT SR
                    for (int site : pointsTo.getOrDefault(
                            (Local) rhs, Collections.emptySet())) {
                        isSR.put(site, false);
                    }

                } else if (lhs instanceof InstanceFieldRef && rhs instanceof Local) {
                    // ── BUG 1 FIX: b.a = x  ─────────────────────────────────
                    // OLD (wrong): marked x (the RHS object) as N immediately.
                    // WHY IT WAS WRONG: the spec only mandates N for escaping to
                    // GLOBAL (static) variables. Storing into a field of a LOCAL
                    // object in the same method is NOT a disqualifier — the object
                    // may still be scalar-replaceable if it is only read afterwards.
                    //
                    // NEW (correct): store the RHS alloc sites into fieldContents
                    // so that when the field is read back later (e.g. A q = b.a),
                    // we can propagate the points-to set to the new local.
                    InstanceFieldRef storeRef = (InstanceFieldRef) lhs;
                    if (storeRef.getBase() instanceof Local) {
                        Local baseLocal = (Local) storeRef.getBase();
                        String sig = storeRef.getField().getSignature();
                        Set<Integer> rhsPts = pointsTo.getOrDefault(
                                (Local) rhs, Collections.emptySet());
                        // record what sites are now in base.field
                        fieldContents
                                .computeIfAbsent(baseLocal, k -> new HashMap<>())
                                .put(sig, new HashSet<>(rhsPts));
                    }
                    // Do NOT mark as N here — safety is checked by analyzeInCallee
                    // when the object is eventually passed to a method.

                } else if (lhs instanceof Local && rhs instanceof InstanceFieldRef) {
                    // ── BUG 3 FIX: q = b.a  (field load) ────────────────────
                    // OLD (missing): this case was never handled, so pointsTo[q]
                    // stayed empty, and any call using q (e.g. b.foo(q)) would not
                    // track that the argument might point to an allocation site.
                    //
                    // NEW (correct): look up what was stored into b.a (via the
                    // fieldContents map populated above) and copy those alloc sites
                    // into pointsTo[q], so later call-site escape checks work.
                    InstanceFieldRef loadRef = (InstanceFieldRef) rhs;
                    if (loadRef.getBase() instanceof Local) {
                        Local baseLocal = (Local) loadRef.getBase();
                        String sig = loadRef.getField().getSignature();
                        Set<Integer> stored = fieldContents
                                .getOrDefault(baseLocal, Collections.emptyMap())
                                .getOrDefault(sig, Collections.emptySet());
                        if (!stored.isEmpty()) {
                            pointsTo.put((Local) lhs, new HashSet<>(stored));
                        }
                    }
                }

                // ── BUG 2 FIX: removed the field-write-on-base block ─────────
                // OLD (wrong): when b.a = something was processed, we fired:
                //   if (lhs instanceof InstanceFieldRef) {
                //       mark pointsTo[base] (i.e. O22) as N
                //   }
                // WHY IT WAS WRONG (two reasons):
                //   (a) Writing to an object's OWN fields in the method that
                //       allocated it is fine for scalar replacement — those
                //       writes just become variable assignments in the SR'd code.
                //       O22 = Y[25] is correct because B::foo never writes to
                //       'this's fields; the b.a = a write is in main (allocating
                //       method), not in a callee.
                //   (b) The same check incorrectly fired for   o1.x = 8   in
                //       Test1 (base = o1, pointsTo[o1] = {31}), marking O31 as N
                //       when the correct answer is Y[].
                // Field writes on the TRACKED object inside a CALLEE are still
                // caught by analyzeInCallee (the InstanceFieldRef-on-aliases check
                // inside that method is unchanged and correct).
            }

            // Return escape: if a locally-allocated object is returned it escapes
            // the method and cannot be scalar-replaced.
            if (stmt instanceof ReturnStmt) {
                ReturnStmt returnStmt = (ReturnStmt) stmt;
                Value retVal = returnStmt.getOp();
                if (retVal instanceof Local) {
                    for (int site : pointsTo.getOrDefault(
                            (Local) retVal, Collections.emptySet())) {
                        isSR.put(site, false);
                    }
                }
            }

            // If a statement contains a call expression, find and check its call targets.
            if (stmt.containsInvokeExpr()) {
                InvokeExpr invoke = stmt.getInvokeExpr();

                if (invoke.getMethod().getName().equals("<init>")) continue;

                // Collect all CHA-resolved targets for this call site
                List<SootMethod> targets = new ArrayList<>();
                Iterator<Edge> targetIter = cg.edgesOutOf(stmt);
                while (targetIter.hasNext()) {
                    Edge edge = targetIter.next();
                    SootMethod targetMethod = edge.tgt();
                    targets.add(targetMethod);
                }

                // Recursively analyse allocations in every callee
                Set<SootMethod> newCallStack = new HashSet<>(callStack);
                newCallStack.add(method);
                for (SootMethod target : targets) {
                    if (target.hasActiveBody() && !callStack.contains(target)) {
                        analyzeMethodAllocations(target.getActiveBody(), newCallStack);
                    }
                }

                // ── Check the receiver (this pointer) for escape ───────────────
                if (invoke instanceof InstanceInvokeExpr) {
                    Local base = (Local) ((InstanceInvokeExpr) invoke).getBase();
                    Set<Integer> basePts = new HashSet<>(
                            pointsTo.getOrDefault(base, Collections.emptySet()));

                    for (int site : basePts) {
                        if (!isSR.getOrDefault(site, false)) continue;

                        for (SootMethod target : targets) {
                            if (!target.hasActiveBody()) continue;
                            Local thisLocal = target.getActiveBody().getThisLocal();

                            Set<Integer> result = analyzeInCallee(
                                    target.getActiveBody(), thisLocal, new HashSet<>());

                            if (result == null) {
                                isSR.put(site, false);
                                break;
                            }
                            escapeLines.get(site).addAll(result);
                        }

                        if (isSR.getOrDefault(site, false)) {
                            escapeLines.get(site).add(lineNumber);
                        }
                    }
                }

                // ── Check each argument for escape ────────────────────────────
                List<Value> args = invoke.getArgs();
                for (int i = 0; i < args.size(); i++) {
                    if (!(args.get(i) instanceof Local)) continue;
                    Local argLocal = (Local) args.get(i);
                    Set<Integer> argPts = new HashSet<>(
                            pointsTo.getOrDefault(argLocal, Collections.emptySet()));

                    final int argIdx = i;
                    for (int site : argPts) {
                        if (!isSR.getOrDefault(site, false)) continue;

                        for (SootMethod target : targets) {
                            if (!target.hasActiveBody()) continue;
                            Local param = target.getActiveBody().getParameterLocal(argIdx);

                            Set<Integer> result = analyzeInCallee(
                                    target.getActiveBody(), param, new HashSet<>());

                            if (result == null) {
                                isSR.put(site, false);
                                break;
                            }
                            escapeLines.get(site).addAll(result);
                        }

                        if (isSR.getOrDefault(site, false)) {
                            escapeLines.get(site).add(lineNumber);
                        }
                    }
                }
            }
        }
    }

    /**
     * Escape analysis for one callee body.
     *
     * Tracks the object held in trackedLocal (and any aliases created inside
     * the body). Scans every statement for:
     *   - InstanceFieldRef on the LHS  →  field WRITE  →  return null (not SR)
     *   - Storing tracked object into a static/instance field  →  return null
     *   - Call sites where the object escapes further  →  recurse, collect lines
     *
     * Returns:
     *   null            if a field write is found anywhere (object NOT scalar-replaceable)
     *   Set<Integer>    sorted call-site line numbers inside this body (and its
     *                   transitive callees) where the object escapes — but fields
     *                   are only read, so it IS still scalar-replaceable.
     */
    Set<Integer> analyzeInCallee(Body body, Local trackedLocal,
                                  Set<SootMethod> visited) {

        Set<Local>   aliases       = new HashSet<>();
        Set<Integer> calleeEscapes = new TreeSet<>();
        aliases.add(trackedLocal);

        for (Unit u : body.getUnits()) {
            Stmt stmt = (Stmt) u;
            int lineNumber = stmt.getJavaSourceStartLineNumber();

            // ── Alias propagation + field-write detection ──────────────────────
            if (stmt instanceof AssignStmt) {
                AssignStmt assign = (AssignStmt) stmt;
                Value lhs = assign.getLeftOp();
                Value rhs = assign.getRightOp();

                // y = tracked  →  y is also an alias of the tracked object
                if (rhs instanceof Local && aliases.contains((Local) rhs)) {
                    if (lhs instanceof Local) {
                        aliases.add((Local) lhs);
                    } else {
                        // Tracked object stored into a non-local (field, array, static)
                        // inside a callee — we cannot track it further → NOT SR
                        return null;
                    }
                }

                // tracked.field = ...  →  field WRITE on the tracked object → NOT SR
                if (lhs instanceof InstanceFieldRef) {
                    InstanceFieldRef fieldRef = (InstanceFieldRef) lhs;
                    if (fieldRef.getBase() instanceof Local
                            && aliases.contains((Local) fieldRef.getBase())) {
                        return null;
                    }
                }
            }

            // ── Return-escape detection ────────────────────────────────────────
            if (stmt instanceof ReturnStmt) {
                ReturnStmt returnStmt = (ReturnStmt) stmt;
                Value retVal = returnStmt.getOp();
                if (retVal instanceof Local && aliases.contains((Local) retVal)) {
                    return null;   // tracked object escapes via return → NOT SR
                }
            }

            // ── Recurse into further call sites ───────────────────────────────
            if (stmt.containsInvokeExpr()) {
                InvokeExpr invoke = stmt.getInvokeExpr();

                if (invoke.getMethod().getName().equals("<init>")) continue;

                boolean escapedHere = false;

                List<SootMethod> targets = new ArrayList<>();
                Iterator<Edge> targetIter = cg.edgesOutOf(stmt);
                while (targetIter.hasNext()) {
                    SootMethod t = targetIter.next().tgt();
                    if (!visited.contains(t)) targets.add(t);
                }

                // Check receiver
                if (invoke instanceof InstanceInvokeExpr) {
                    Local base = (Local) ((InstanceInvokeExpr) invoke).getBase();
                    if (aliases.contains(base)) {
                        escapedHere = true;
                        for (SootMethod target : targets) {
                            if (!target.hasActiveBody()) continue;
                            Set<SootMethod> newVisited = new HashSet<>(visited);
                            newVisited.add(target);
                            Set<Integer> result = analyzeInCallee(
                                    target.getActiveBody(),
                                    target.getActiveBody().getThisLocal(),
                                    newVisited);
                            if (result == null) return null;
                            calleeEscapes.addAll(result);
                        }
                    }
                }

                // Check each argument
                List<Value> callArgs = invoke.getArgs();
                for (int i = 0; i < callArgs.size(); i++) {
                    if (!(callArgs.get(i) instanceof Local)) continue;
                    if (!aliases.contains((Local) callArgs.get(i))) continue;
                    escapedHere = true;
                    for (SootMethod target : targets) {
                        if (!target.hasActiveBody()) continue;
                        Set<SootMethod> newVisited = new HashSet<>(visited);
                        newVisited.add(target);
                        Set<Integer> result = analyzeInCallee(
                                target.getActiveBody(),
                                target.getActiveBody().getParameterLocal(i),
                                newVisited);
                        if (result == null) return null;
                        calleeEscapes.addAll(result);
                    }
                }

                if (escapedHere) {
                    calleeEscapes.add(lineNumber);
                }
            }
        }

        return calleeEscapes;
    }
}