package shh2.javasrc;

import java.awt.*;
import java.awt.event.*;
import java.net.URL;
import javax.swing.*;

/** As we perform linear algebra operations on a sparse matrix, this
    window displays the changing sparsity pattern and other
    information.  The pixels represent consecutive
    &delta;&nbsp;&times;&nbsp;&delta; submatrices, where
    &delta;&nbsp;&ge;&nbsp;1 is chosen so the whole matrix fits in the
    window.  Each pixel is colored in grayscale by what proportion of
    the &delta;<SUP>2</SUP> entries of the submatrix are non-zero.
    White means the whole submatrix is zero; black means its entries
    are all non-zero, or you're on the diagonal that has already been
    reduced (see {@link #setCorner}).

    <P> Displaying a CSparseWin0 slows down the computation.
    Minimizing the window eliminates the slowdown.

    @author Mark McConnell */

public class CSparseWin0 extends JFrame {

   private static final int MARGIN = 20;

   /** Shades of gray indexed by [0,256].  The 0th is black, and the
       255th and 256th are white. */
   private static final Color[] grayArr = new Color[257];
   static {
      for (int c = 0; c < 256; ++c) {
         grayArr[c] = new Color(c, c, c);
      }
      grayArr[256] = grayArr[255];
   }

   private final CSparsePanel panel = new CSparsePanel();
   private final JTextField tf_note = new JTextField(21);

   private final int m, n, W, H, delta, deltaSq;
   private final Dimension dimWH;

   /** Same syntax as at setCounter(...). */
   private int[] counter = null;

   /** See {@link #setCorner}. */
   private int corner = -1;
   
   /** See {@link #setYellow}. */
   private int yellowA, yellowB;
   
   // --------------------

   /** Constructor.
       @param m and n are the size of the matrix.
       @param W and H are the size of the painted panel, in pixels.
       @param delta See the main doc comment. */

   public CSparseWin0(String title, int m, int n, int W, int H, int delta) {
      super(title);
      this.m = m;
      this.n = n;
      this.W = W;
      this.H = H;
      this.delta = delta;
      deltaSq = delta * delta;
      dimWH = new Dimension(W,H);
      yellowA = yellowB = n;
      GUI();
      pack();
   }

   /** Resets the data showing the sparsity pattern, and requests a
       repaint.
       @param newCounter Stores a width-by-height rectangular array of
       Java int's in column-major order.  Each entry is the number of
       non-zeros in the corresponding
       &delta;&nbsp;&times;&nbsp;&delta;. */

   public void setCounter(int[] newCounter) {
      counter = newCounter;
      panel.repaint(0, 0, W, H);
   }

   /** Says the upper-left block 0&nbsp;&le;&nbsp;<I>i</I>,
       <I>j</I>&nbsp;&lt;&nbsp;<CODE>corner</CODE> should be assumed
       to be diagonal.  The diagonal pixels are painted black, because
       a grayscale of &delta;/&delta;<SUP>2</SUP> = 1/&delta; may be
       too faint. */

   public void setCorner(int corner) {
      this.corner = corner;
   }

   /** Sets a note at the top of the screen. */

   public void setNote(String note) {
      tf_note.setText(note);
   }

   /** Sets columns
       <I>a</I>&nbsp;&le;&nbsp;<I>j</I>&nbsp;&lt;&nbsp;<I>b</I> to be
       solid yellow.  If <I>a</I>&nbsp;&ge;&nbsp;<I>b</I>, the feature
       is turned off. */

   public void setYellow(int a, int b) {
      yellowA = a;
      yellowB = b;
      panel.repaint(0, 0, W, H);
   }

   private void GUI() {
      tf_note.setEditable(false);
      tf_note.setBackground(getBackground());
      JPanel tfHolder = new JPanel();
      tfHolder.add(new JLabel("" + m + " \u00D7 "/*times*/ + n +
                              "     " + delta + ":1"));
      tfHolder.add(Box.createHorizontalStrut(10));
      tfHolder.add(tf_note);
      getContentPane().add("North", tfHolder);
      getContentPane().add("South", Box.createVerticalStrut(MARGIN));
      getContentPane().add("East", Box.createHorizontalStrut(MARGIN));
      getContentPane().add("West", Box.createHorizontalStrut(MARGIN));
      getContentPane().add("Center", panel);
      addWindowListener(new WindowAdapter() {
            public void windowClosing(WindowEvent e) {
               System.exit(0);
            }
         });
   }

   // -------------------- Inner class CSparsePanel --------------------

   class CSparsePanel extends JPanel {
      
      public void paintComponent(Graphics g) {
         super.paintComponent(g);
         boolean pastCorner = false;
         for (int pj = 0; pj < W; ++pj) {
            boolean useYellow = false;
            for (int j = pj*delta, j0 = 0; j < n && j0 < delta; ++j, ++j0) {
               if (!pastCorner && j >= corner) pastCorner = true;
               if (yellowA <= j && j < yellowB) useYellow = true;
            }
            if (!useYellow) {
               if (counter != null) {
                  for (int pi = 0; pi < H; ++pi) {
                     int denom = deltaSq;
                     if (!pastCorner) denom = delta;
                     float fill = counter[pi + H * pj] / (float)denom;
                     int grayIndex = Math.round(256.0f * (1.0f - fill));
                     Color c = grayArr[grayIndex];
                     g.setColor(c);
                     g.drawLine(pj, pi, pj, pi);
                  }
               }
            } else {
               g.setColor(Color.yellow);
               g.drawLine(pj, 0, pj, H-1);
            }
         }
         if (corner >= 0) {
            int pCor = corner/delta;
            g.setColor(Color.green);
            g.drawLine(pCor, 0, pCor, H-1);
            g.drawLine(0, pCor, W-1, pCor);
         }
      }

      public Dimension getPreferredSize() { return dimWH; }
      public Dimension getMaxSize() { return dimWH; }
      public Dimension getMinSize() { return dimWH; }
      public Dimension getSize() { return dimWH; }

   }

}
