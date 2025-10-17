import java.io.*;
import java.util.Arrays;

public class DelayWrapper {
    static BufferedReader stdin = new BufferedReader(new InputStreamReader(System.in));
    public static void main(String[] args) throws Exception {
        int numberOfAsserts = 0;
        boolean internalError = false;
        String benchmark = stdin.readLine();
        String[] arithmetic = {"m135", "m158",  "m159", "m164", "m172", "m181", "m183", "m185", "m201", "m24", "m45", "m54", "m55", "m76", "m95"};
        String[] dataStructures= {"m106", "m131", "m132", "m167", "m173", "m182", "m189", "m190", "m196", "m199", "m22", "m27", "m41", "m49", "m65"};
        String cwd;
        if (Arrays.asList(arithmetic).contains(benchmark)){
            cwd = "arithmetic/" + benchmark;
        } else {
            if (Arrays.asList(dataStructures).contains(benchmark)){
                cwd = "data-structures/" + benchmark;
            } else {
                throw new Exception("Exception message");
            }
        }
        ProcessBuilder processBuilder = new ProcessBuilder();
        processBuilder.directory(new java.io.File(cwd));
        processBuilder.command("java", benchmark + "_Reach");
        Process process = processBuilder.start();
        String state = stdin.readLine();
        if (state.equals("init")) {
            try (BufferedWriter writer = new BufferedWriter(
                new OutputStreamWriter(process.getOutputStream()))) {
            writer.write("init\n");
            writer.flush();
        }
        } else {
            String[] stateValues = state.split("/");
            String asserts = stateValues[0];
            String input = stdin.readLine();
            if (!asserts.equals("-")){
                internalError = true;
                numberOfAsserts = Integer.parseInt(asserts);
                if (input.equals("assert")) {
                    numberOfAsserts = Math.min(numberOfAsserts+1, 3);
                }
            }
            try (BufferedWriter writer = new BufferedWriter(
                new OutputStreamWriter(process.getOutputStream()))) {
            writer.write(state.substring(1) + "\n");
            writer.write(input + "\n");
            writer.flush();
        }
        }

        try (BufferedReader reader = new BufferedReader(
                new InputStreamReader(process.getInputStream()))) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.equals("error") && (!internalError || (numberOfAsserts < 3))){
                    internalError = true;
                    System.out.println("_none_");
                } else{
                    if (line.startsWith("/")) {
                        if (internalError) {
                            line = String.valueOf(numberOfAsserts) + line;
                        } else {
                            line = "-" + line;
                        }
                    }
                    System.out.println(line);
                }
            }
        }
        int exitCode = process.waitFor();

    }
}
