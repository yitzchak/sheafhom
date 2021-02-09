#include <stdio.h>
#include <stdlib.h>

#define BUFSIZE_INIT 10000
#define BUFSIZE_FACTOR 1.5

/* Converts a text file with contents (a b c)(d e f g)(h i)(j k l) to
   a text file with contents (j k l)(h i)(d e f g)(a b c), without
   holding the whole input in RAM.  argv[1] is the input filename, and
   argv[2] the output filename.  Returns 0 normally, or > 0 if there's
   an error. */

int main(int argc, char *argv[]) {
  FILE *in, *out;
  int bufi = 0, buflen = BUFSIZE_INIT, err;
  long i = 0L, n;
  char *buf;

  if (argc < 3) return 1;
  in = fopen(argv[1], "r");
  if (in == NULL) return 2;
  out = fopen(argv[2], "w");
  if (out == NULL) return 3;
  err = fseek(in, 0L, SEEK_END);
  if (err) return 4;
  n = ftell(in);
  if (n == -1L) return 5;
  rewind(in);
  buf = (char *)malloc(buflen * sizeof(char));
  if (buf == NULL) return 6;
  while (i < n) {
    int c = fgetc(in);
    if (c == EOF) {
      if (bufi != 0) return 7;
      else break;
    }
    if (bufi == buflen) {
      buflen = (int)(buflen * BUFSIZE_FACTOR);
      buf = (char *)realloc(buf, buflen * sizeof(char));
      if (buf == NULL) return 8;
    }
    buf[bufi++] = c;
    ++i;
    if (c == ')') {
      int j;
      fseek(out, n-i, SEEK_SET);
      for (j = 0; j < bufi; ++j) {
	err = fputc(buf[j], out);
	if (err == EOF) return 9;
      }
      bufi = 0;
    }
  }
  err = fclose(in);
  if (err == EOF) return 10;
  err = fclose(out);
  if (err == EOF) return 11;
  return 0;
}
