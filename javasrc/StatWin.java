package shh2.javasrc;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.BufferedImage;
import java.io.*;
import java.util.*;
import javax.imageio.ImageIO;
import javax.swing.*;

/** {@link StatWin#show} displays a window with a line graph.  See
    {@link LineChart} for details.  Killing the window terminates the
    entire Java session.

    <P> {@link #saveComponent} is a general utility for saving image
    files.

    @author Mark McConnell */

public class StatWin extends LineChart {

   /** Constructor.  See {@link LineChart} for details.
    @param yArr The <I>y</I>-coordinates of the line graph.
    @param lim Only the <CODE>yArr[j]</CODE> with 0 &le;
    <CODE>j</CODE> &lt; <CODE>lim</CODE> are used. */ 

   public StatWin(double[] yArr, int lim) {
      super();
      lim = Math.min(lim, yArr.length);
      float[][] yy = new float[1][];
      yy[0] = new float[lim];
      float yMax = 0.0f;
      for (int i = 0; i < lim; ++i) {
         yy[0][i] = (float)yArr[i];
         yMax = Math.max(yMax, yy[0][i]);
      }
      setMaxY(yMax);
      String[] labels = new String[lim];
      if (lim <= 20) {
         for (int i = 0; i < lim; ++i) {
            labels[i] = ""+i;
         }
      } else {
         Arrays.fill(labels, "");
         for (int i = 0; i < 10; ++i) {
            labels[i*lim/10] = ""+(i*lim/10);
         }
         labels[lim-1] = ""+(lim-1);
      }
      setTitles("", "", "");
      setData(yy, labels, new Color[]{Color.black});
   }

   // ------------------------------------------------------------

   /** Shows a line graph.  See {@link LineChart} for details.
       @param yArr The <I>y</I>-coordinates.
       @param title The title.
       @param lim Only the <CODE>yArr[j]</CODE> with 0 &le;
       <CODE>j</CODE> &lt; <CODE>lim</CODE> are used. */ 

   public static void show(double[] yArr, String title, int lim) {
      final JFrame jFrame = new JFrame(title);
      jFrame.addWindowListener(new WindowAdapter() {
         public void windowClosing(WindowEvent e) {
            System.exit(0);
         }
      });

      final StatWin w = new StatWin(yArr, lim);

      final JButton btn_header = new JButton("Set Header...");
      final JButton btn_save = new JButton("Save Image...");
      ActionListener lis = new ActionListener() {
         public void actionPerformed(ActionEvent e) {
            Object src = e.getSource();
            if (src == btn_header) {
               String s = JOptionPane.showInputDialog(jFrame, "Please enter the new header.");
               if (s != null) {
                  w.setTitles(s, "", "");
               }
            } else if (src == btn_save) {
               saveComponent(w, jFrame, "shhchart");
            }
         }
      };
      btn_header.addActionListener(lis);
      btn_save.addActionListener(lis);
      JPanel btnPanel = new JPanel();
      btnPanel.add(btn_header);
      btnPanel.add(btn_save);

      jFrame.getContentPane().add("North", w);
      jFrame.getContentPane().add("South", btnPanel);
      jFrame.pack();
      jFrame.setLocation(47, 33);
      jFrame.show();
   }

   // ------------------------------------------------------------

   /** The last directory used by a file chooser in this class;
       defaults to the user's current working directory. */
   private static File LAST_DIR_USED = new File(System.getProperty("user.dir"));

   /** Saves a JComponent's image to a file in a format like png or
       jpg.  The component should be showing on screen.
       @param comptToSave The JComponent to save.
       @param dialogParent The parent for the dialog boxes.
       @param suggestedFilename An initial default like
       <CODE>myfile</CODE>.  The method will convert this to
       <CODE>myfile.png</CODE>, <CODE>myfile.jpg</CODE>, etc.  It can
       be null. */

   public static void saveComponent(JComponent comptToSave,
                                    Component dialogParent,
                                    String suggestedFilename) {
      // Get image formats.  Remove duplicates, prefer lowercase,
      // change jpeg to jpg, sort.
      String[] formats = ImageIO.getWriterFormatNames();
      HashSet formatSet = new HashSet();
      formatSet.addAll(Arrays.asList(formats));
      for (Iterator iter = formatSet.iterator(); iter.hasNext(); ) {
         String Xxx = (String)iter.next();
         String xxx = Xxx.toLowerCase();
         if (!xxx.equals(Xxx) && formatSet.contains(xxx)) {
            iter.remove();
         }
      }
      if (formatSet.remove("jpeg")) {
         formatSet.add("jpg");
      }
      formats = (String[])formatSet.toArray(new String[formatSet.size()]);
      Arrays.sort(formats, String.CASE_INSENSITIVE_ORDER);

      String format = (String)JOptionPane.showInputDialog(dialogParent,
                                                          "Please choose an output format.",
                                                          "Format",
                                                          JOptionPane.QUESTION_MESSAGE,
                                                          null,
                                                          formats,
                                                          "png");
      if (format == null)
         return; // user cancelled

      if (suggestedFilename == null || suggestedFilename.equals("")) {
         suggestedFilename = "shh";
      }
      JFileChooser fileCh = new JFileChooser(LAST_DIR_USED);
      fileCh.setSelectedFile(new File(LAST_DIR_USED,
                                      suggestedFilename + '.' + format));
      int chResult = fileCh.showSaveDialog(dialogParent);
      if (chResult != JFileChooser.APPROVE_OPTION)
         return;
      LAST_DIR_USED = fileCh.getCurrentDirectory();
      File file = fileCh.getSelectedFile();
       if (file == null)
          return; // user cancelled, or some other problem
      if (file.exists()) {
         int overwr = JOptionPane.showConfirmDialog(dialogParent,
                                                    file.getAbsolutePath() + "\nalready exists.  OK to overwrite?",
                                                    "File Exists",
                                                    JOptionPane.YES_NO_OPTION);
         if (overwr != JOptionPane.YES_OPTION)
            return;
      }

      try {
         FileOutputStream os = new FileOutputStream(file);
         Dimension dim = comptToSave.getSize();
         BufferedImage im =
            (BufferedImage)comptToSave.createImage(dim.width, dim.height);
         comptToSave.paint(im.createGraphics());
         ImageIO.write(im, format, os);
         os.flush();
         os.close();
      } catch (Exception e) {
         String errorMessage = e.getMessage();
         String text = "Sorry, the save operation failed.";
         if (errorMessage != null && !errorMessage.equals(""))
            text += "\n\n" + errorMessage;
         JOptionPane.showMessageDialog(dialogParent, text, "Can't Save",
                                       JOptionPane.ERROR_MESSAGE); 
      }
   }

}
