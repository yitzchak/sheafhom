package shh2.javasrc;

import java.awt.*;
import java.awt.event.*;
import java.util.Arrays;
import javax.swing.*;

/** A simple chart showing one or more line graphs.  As the mouse
    moves over the chart, a tooltip displays the coordinates of the
    points.  To use the chart, call the <CODE>setXXX</CODE> methods in
    roughly the order they appear here.  Only handles <I>y</I> &ge; 0,
    and always displays the <I>y</I>-axis.  The <I>x</I>-coordinates
    in the line graphs are the consecutive integers 0, 1, 2, ....

    @author Karen Wang, Mark McConnell */

public class LineChart extends JPanel {

   static final Dimension DIM = new Dimension(480,380);
   float max = 1.54f;
   int numBar = 1;
   float w = 21.0f;
   int sigFig = 3;

   float[][] data = {{0.0f}};
   String[] label = null;
   Color[] color = {Color.black};
   boolean[] visible = {true};
   String title = "Title", ytitle = "Y Axis", xtitle = "X Axis";

   // Shadow colors for drawing the lines.  The points are in the
   // corresponding pure color.
   final static Color sGreen = new Color(80,215,80);
   final static Color sRed = new Color(215,80,80);
   final static Color sYellow = new Color(215,215,80);
   final static Color sMagenta = new Color(215,80,215);
   final static Color sBlue = new Color(80,80,215);
   final static Color sCyan = new Color(80,215,215);
   final static Color sOrange = new Color(215,165,80);
   final static Color sBlack = new Color(80,80,80);

   // ------------------------------------------------------------

   public LineChart() {
      super();
      addMouseMotionListener(new MouseMotionAdapter() {
         public void mouseMoved(MouseEvent e) {
            setToolTip(e);
         }
      });
   }

   /** Sets the maximum <I>y</I> value. */

   public void setMaxY(float max) {
      this.max = max;
      repaint();
   }

   /** Sets the titles. */

   public void setTitles(String title, String xaxis, String yaxis) {
      this.title = notNull(title);
      this.xtitle = notNull(xaxis);
      this.ytitle = notNull(yaxis);
      repaint();
   }

   private String notNull(String s) {
      return (s == null) ? "" : s;
   }

   /** Main method to set the chart's data.
       @param dd Holds the <I>y</I> values.  Of size
       (number of <I>x</I>-coordinates) &times; (number of line
       graphs).
       @param l Labels for the <I>x</I> values.  Of length
       (number of <I>x</I>-coordinates).  If it's null, no labels are
       used.
       @param c Colors for the line graphs.  Of length (number of line
       graphs).
       @exception NullPointerException If <CODE>dd</CODE> is null. */

   public void setData(float[][] dd, String[] l, Color[] c) {
      data = dd;
      label = l;
      color = c;
      numBar = 1;
      for (int i = 0; i < dd.length; ++i) {
         numBar = Math.max(numBar, dd[i].length);
      }
      w = ((float)DIM.height / (numBar * 1.1f));
      if (color == null) {
         color = new Color[dd.length];
         Arrays.fill(color, Color.black);
      }
      visible = new boolean[dd.length];
      Arrays.fill(visible, true);
      repaint();
   }

   /** Set the visibility of the <CODE>i</CODE>-th data series
       (default true). */

   public void setDataSetVisible(int i, boolean isVisible) {
      if (visible[i] != isVisible) {
         visible[i] = isVisible; 
         repaint();
      }
   }

   /** Sets the number of significant figures (default 3) in the
       labels on the <I>y</I>-axis.  See {@link Format#roundToSigFig}
       for restrictions. */

   public void setSignificantFigures(int sigFig) {
      this.sigFig = sigFig;
      repaint();
   }

   // ------------------------------------------------------------

   Color getShadow(Color c) {
      if (c == Color.green) return sGreen;
      if (c == Color.red) return sRed;
      if (c == Color.yellow) return sYellow;
      if (c == Color.magenta) return sMagenta;
      if (c == Color.blue) return sBlue;
      if (c == Color.cyan) return sCyan;
      if (c == Color.orange) return sOrange;
      if (c == Color.black) return sBlack;
      else return Color.gray;
   }

   public Dimension getMinimumSize() {
      return DIM;
   }

   public Dimension getPreferredSize() {
      return DIM;
   }

   protected void paintComponent(Graphics g) {
      Image buffer = createImage(getSize().width,getSize().height);
      Graphics bg = buffer.getGraphics();   
      bg.setColor(Color.white);
      bg.fillRect(0,0,this.getSize().width,this.getSize().height);
      
      bg.setColor(Color.black);
      bg.drawLine(75,80,75,292);
      bg.drawLine(74,80,74,292);

      final float hash = 10.0f;
      bg.setFont(new Font("Helvetica",Font.PLAIN,12));
      for (int i=0; i <= hash; i++) {
         String mesg = Format.roundToSigFig(i*max/hash, sigFig);
         int y = Math.round(i*200/hash);
         int sw = bg.getFontMetrics().stringWidth(mesg);
         bg.drawString(mesg,70-sw,295-y);
         if (i !=0)
            bg.drawLine(75,290-y,440,290-y);
      }

      bg.setFont(new Font("Monospaced",Font.BOLD,12));
      int l = ytitle.length();
      int ytoffset = (200 - bg.getFontMetrics().getHeight()*l)/2;
      for (int i=0; i < l; i++)
         bg.drawString(ytitle.substring(i,i+1), 18, 290-ytoffset-(l-i)*bg.getFontMetrics().getHeight()); 

      bg.setFont(new Font("Monospaced",Font.BOLD,15));
      int sw = bg.getFontMetrics().stringWidth(xtitle);
      int xx = (315-sw)/2;
      bg.drawString(xtitle,xx+75,325); 
      bg.setFont(new Font("Helvetica",Font.BOLD,15));
      int tw = bg.getFontMetrics().stringWidth(title);
      int tx = (getSize().width-tw)/2;
      bg.drawString(title,tx,50); 
      for (int ct=0; ct < data.length; ct++) {
         if (visible[ct]) {   
            Color color1 = color[ct];
            Color shadow1 = getShadow(color1);
            for (int i=1; i  <data[ct].length; i++) {
               int x1 = 90+Math.round((i-1)*w);
               int x2 = 90+Math.round(i*w);
               int y1 = 290 - Math.round(((float)data[ct][i-1]/max)*200);
               int y2 = 290 - Math.round(((float)data[ct][i]/max)*200);
               bg.setColor(shadow1);
               bg.drawLine(x1,y1,x2,y2);
            }
            for (int i=0; i < data[ct].length; i++) {
               int x1 = 90+Math.round(i*w);
               int y1 = 290 - Math.round(((float)data[ct][i]/max)*200);
               bg.setColor(color1);
               bg.fillRect(x1-2,y1-2,4,4);   
            }
         }
      }
      if (label != null) {
         for (int i=0; i < numBar; i++) {
            int x = 90+Math.round(i*w);
            bg.setColor(Color.black);   
            bg.setFont(new Font("Helvetica",Font.PLAIN,10));
            if (label[i] != null && !label[i].equals("")) {
               bg.drawString(label[i],x,305);
               bg.drawLine(x,292,x,297);
            }
         }
      }
      bg.setColor(Color.black);   
      bg.drawLine(75,292,440,292);
      g.drawImage(buffer,0,0,this);
   }

   /** Sets a tooltip on this LineChart. */

   protected void setToolTip(MouseEvent e) {
      int i = Math.round((e.getX() - 90) / w);
      if (0 <= i && i < numBar) {
         StringBuffer sb = new StringBuffer();
         sb.append("x = ");
         sb.append(i);
         sb.append("   y = ");
         for (int k = 0; k < data.length; ++k) {
            if (i < data[k].length) {
               if (Character.isDigit(sb.charAt(sb.length()-1))) {
                  sb.append(" ,  ");
               }
               sb.append(data[k][i]);
            }
         }
         setToolTipText(sb.toString());
      } else {
         setToolTipText(null);
      }
   }

   // ------------------------------------------------------------

   /** Takes arguments <CODE>u0 v0 u1 v1 u2 v2</CODE>, etc., all &ge;
       0, and plots a chart with two line graphs, one for
       <CODE>u</CODE> and one for <CODE>v</CODE>.  If there is no
       data, plots two sine waves. */

   public static void main(String[] args) {
      int n = (args.length > 0
               ? Math.round((float)Math.ceil(args.length / 2.0))
               : 1000);
      float[][] data = new float[2][];
      data[0] = new float[n];
      data[1] = new float[n];
      float yMax;
      String[] xLabels = null;
      if (args.length == 0) {
         double omega = 2.0 * Math.PI / n;
         for (int x = 0; x < n; ++x) {
            data[0][x] = 1.0f + (float)Math.sin(omega * x);
            data[1][x] = 1.0f + (float)Math.sin(5.0 * omega * x);
         }
         yMax = 2.0f;
      } else {
         yMax = Float.NEGATIVE_INFINITY;
         try {
            for (int i = 0; i < args.length; ++i) {
               float y = Float.parseFloat(args[i]);
               data[i%2][i/2] = y;
               yMax = Math.max(yMax, y);
            }
         } catch (NumberFormatException e) {
            System.out.println("Please provide numeric arguments u0 v0 u1 v1 u2 v2...");
            return;
         }
         xLabels = new String[n];
         for (int i = 0; i < n; ++i) {
            xLabels[i] = ""+i;
         }
      }

      LineChart chart = new LineChart();
      chart.setMaxY(yMax);
      chart.setData(data, xLabels, new Color[]{Color.red, Color.green});
      
      JFrame jFrame = new JFrame("LineChart Test");
      jFrame.addWindowListener(new WindowAdapter() {
         public void windowClosing(WindowEvent e) {
            System.exit(0);
         }
      });
      jFrame.getContentPane().add(chart);
      jFrame.pack();
      jFrame.setLocation(47, 33);
      jFrame.show();
   }
      

}


