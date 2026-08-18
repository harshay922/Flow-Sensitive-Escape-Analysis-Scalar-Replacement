# Flow-Sensitive Escape Analysis & Scalar Replacement

A whole-program, flow-sensitive escape analysis built on the [Soot](https://soot-oss.github.io/soot/) framework. For every object allocation site (`new`) reachable from the program's entry point, the analysis determines whether the object is **scalar-replaceable (SR)** — i.e. never escapes the method(s) that use it and could be broken into local variables instead of a heap object — or whether it **escapes**, and if so, exactly where.

## How it works

The analysis runs as a `SceneTransformer` on Soot's whole-program pack (`wjtp`), after the call graph has been built, starting from the program's single entry point (`main`).

For each reachable method, it:

1. **Registers allocation sites** — every `x = new T()` statement becomes a tracked site, labeled `O<line>` by its source line number.
2. **Tracks points-to sets per local** — flow-sensitively, following assignments (`x = y`), copies, and object creation.
3. **Propagates through fields** — stores (`b.a = x`) and loads (`q = b.a`) are tracked via a field-contents map, so an allocation's identity survives being written into and read back out of an object's field.
4. **Detects direct escapes** — an allocation is marked "not scalar-replaceable" the moment it is:
   - assigned to a static field, or
   - stored into an array, or
   - returned from its allocating method.
5. **Detects interprocedural escapes** — when a tracked object (or an alias of it) is passed as a call receiver or argument, the analysis recurses into the callee (using CHA-resolved call targets) to check whether the object is written to a field, stored non-locally, or returned. If so, the site is marked as escaping; otherwise, the call site's line number is recorded as a (non-disqualifying) escape point.
6. **Resolves aliases** inside callees, so an object passed under a different local variable name is still tracked correctly.

## Output format

For each allocation site, one line is printed:

- `O<line> = N` — the object escapes and is **not** scalar-replaceable.
- `O<line> = Y[l1,l2,...]` — the object **is** scalar-replaceable; the bracketed line numbers are the call sites where it is passed around (read-only) but never escapes.

## Project structure

```
.
├── PA3.java                  # Entry point: configures and runs Soot with the analysis
├── AnalysisTransformer.java  # Core escape / scalar-replacement analysis
├── soot-dependencies.jar     # Soot library dependency
├── testcases/                # Test programs (Test1, Test2, ...)
├── testcasesPA3/             # Additional/alternate test programs
└── sootOutput/                # Generated Jimple IR for the analyzed test classes
```

## Running

From this directory, with `soot-dependencies.jar` and the compiled classes on the classpath:

```bash
javac -cp soot-dependencies.jar PA3.java AnalysisTransformer.java
java -cp .:soot-dependencies.jar PA3 <TestFolderName>   # e.g. Test1
```

`<TestFolderName>` refers to a subdirectory under `testcasesPA3/` containing a `Test` class with a `main` method — this is the analysis entry point.
