import soot.*;
import soot.options.Options;

public class PA3 {
    public static void main(String[] args) {

        String classPath = "./testcasesPA3/" + args[0];

        // 1. Soot Options
        Options.v().set_keep_line_number(true);


        // 2. Add Transformer to wjtp pack
        SceneTransformer sceneTransformer = new AnalysisTransformer();
        PackManager.v().getPack("wjtp").add(new Transform("wjtp.dfa", sceneTransformer));

        // 3. SPrepare arguments for Soot
       
        String[] sootArgs = {
            "-cp", classPath,
            "-pp",                      // sets the class path for Soot
            "-w",
            "-app",
            "-allow-phantom-refs",
            "-no-bodies-for-excluded",
            "-exclude", "java.*",
            "-exclude", "javax.*",
            "-exclude", "sun.*",
            "-exclude", "com.sun.*",
            "-exclude", "jdk.*",
            "-f", "J",
            "-t", "1",
            "-main-class", "Test",      // specify the main class
            "-process-dir", classPath
        };

        // 4. Just call main. It will parse args, load classes, and run the packs.
        soot.Main.main(sootArgs);
   
    }
}
