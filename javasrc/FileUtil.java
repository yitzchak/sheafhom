package shh2.javasrc;

import java.io.*;
import java.util.ArrayList;

public class FileUtil {

    /** Converts <CODE>(a b c)(d e f g)(h i)(j k l)</CODE> to
        <CODE>(j k l)(h i)(d e f g)(a b c)</CODE>, without holding the
        whole input in RAM.
        @param filenameIn The relative name of a file holding the
        input.
        @param filenameOut Writes the output here.
        @return null if everything worked, the Exception message if
        there was an exception. */

    public static String reverseLists(String filenameIn, String filenameOut) {
        try {
            RandomAccessFile in = new RandomAccessFile(filenameIn, "r");
            RandomAccessFile out = new RandomAccessFile(filenameOut, "rwd");
            long n = in.length();
            out.setLength(n);
            long i = 0;
            ArrayList buf = new ArrayList();
            while (i < n) {
                byte b = in.readByte();
                buf.add(new Byte(b));
                ++i;
                if ((char)b == ')') {
                    out.seek(n - i);
                    int bufN = buf.size();
                    for (int j = 0; j < bufN; ++j) {
                        out.writeByte(((Byte)buf.get(j)).byteValue());
                    }
                    buf.clear();
                }
            }
            in.close();
            out.close();
            return null;
        } catch (Exception e) {
            return e.getMessage();
        }
    }

    public static void main(String[] fileIn_fileOut) {
        String err = reverseLists(fileIn_fileOut[0], fileIn_fileOut[1]);
        if (err != null) {
            System.err.println(err);
        }
    }

}
