package shh2.javasrc;

/** Formatting utilities.

    @author Mark McConnell */

public class Format {

   /** Given the float <CODE>x</CODE>, rounds it off to the nearest
       <CODE>dec_places</CODE> decimal places, if any.  Examples:
       <UL>
       <LI> <CODE>Format.round(1.7320508, 3, true)</CODE> returns 1.732
       <LI> <CODE>Format.round(1.7320508, 4, true)</CODE> returns 1.7321
       </UL>
       <P> WARNING: there will be errors if rounding <CODE>x *
       10^(dec_places)</CODE> to the nearest integer overflows the
       <CODE>int</CODE> datatype. 
       @return A String containing the rounded-off value.
       @exception IllegalArgumentException If <CODE>dec_places</CODE>
       is less than 0 (just because we haven't written that case). */

   public static String round(float x, int dec_places) {
      if (dec_places < 0)
         throw new IllegalArgumentException("dec_places should be >= 0.");
      int powerOf10 = 1;
      for (int i = 0; i < dec_places; i++) powerOf10 *= 10;
      int y = Math.round(x * powerOf10);
      if (dec_places == 0)   return "" + y;
      else if (y < 0) return "-" + Format.roundAux(-y, dec_places);
      else return Format.roundAux(y, dec_places);      
   }

   // We know dec_places > 0 and y >= 0.
   private static String roundAux(int y, int dec_places) {
      String s = "" + y;
      int n = s.length();
      StringBuffer result = new StringBuffer();
      if (n > dec_places) {
         for (int i = 0; i < n - dec_places; i++)
            result.append(s.charAt(i));
      } else {
         result.append("0");
      }
      result.append(".");
      for (int i = n - dec_places; i < n; i++) {
         if (i < 0)
            result.append("0");
         else
            result.append(s.charAt(i));
      }
      return result.toString();
   }

   /** Converts the number of significant figures
       (<CODE>sig_figs</CODE>) into the appropriate number of decimal
       places, then passes off the work to {@link #round(float, int)}.

       <P> The result is incorrect in some ways.
       <UL>
       <LI> Does not do any rounding to the left of the decimal point
       of <CODE>x</CODE>.  For instance, <CODE>roundToSigFig(1001,
       3)</CODE> is 1001.
       <LI> Never takes more decimal places than
       <CODE>sig_figs</CODE>.  For instance, <CODE>roundToSigFig(.001,
       3)</CODE> is .001, not .00100.  This is what you want, say,
       when you're labeling the interval [0,1] on a chart.
       <LI> 0 goes to 0, not 0.000.
       </UL> */

   public static String roundToSigFig(float x, int sig_figs) {
      if (x == 0.0f) {
         return "0";
      } else {
         float xTest = Math.abs(x);
         int places = sig_figs;
         while (true) {
            if (xTest > 1.0f) {
               if (places <= 0) { // don't go left of decimal point
                  break;
               } else {
                  xTest /= 10.0f;
                  places--;
               }
               // don't increase places
//              } else if (xTest < 0.1f) {
//                 xTest *= 10.0f;
//                 places++;
            } else {
               break;
            }
         }
         return round(x, places);
      }
   }      

}
