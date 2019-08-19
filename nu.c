#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <setjmp.h>
#include <time.h>
#include <math.h>
#include <sys/stat.h>
#include <errno.h>

#define VER "0.0.4"

typedef char * string;
typedef string * strings;
typedef long long i64;
typedef unsigned long long u64;
typedef double f64;
typedef int i16;
typedef struct timeval tv;
typedef void none;
typedef char i8;
typedef enum { false, true } bool;
typedef FILE * fl;
#define nil NULL
#define buf(n, s) char n[s]

#define In stdin
#define Out stdout
#define Err stderr

none end(i16);
none e(string, string);

#define MAS(x) malloc((x)*sizeof(i8))
#define MEC(x) if (x == nil) { fprintf(Err, "%s", "memory error"); exit(1); }

#define MKS(n, s) string n = MAS(s); \
                                 MEC(n)

#define EQS(s, ss) (strcmp(s, ss) == 0)

#define SRR(n, s) n = MAS(s); MEC(n); n[0] = '\0'

#define F64F "%.15g"
#define I64F "%lld"

typedef struct 
{
  enum _T { t_num, t_str, t_nil, t_err, t_inf, t_file } type;
  union { f64 num; string str; fl fle; } value;
} Val;

typedef struct _Entry
{
  buf(s, 9);
  Val a;
  struct _Entry *n;
} En;

#define NUM(x) (x.type == t_num)
#define STR(x) (x.type == t_str)
#define NIL(x) (x.type == t_nil)
#define ERR(x) (x.type == t_err)
#define INF(x) (x.type == t_inf)
#define FLE(x) (x.type == t_file)

Val NIL;
Val INF;
Val Error;

Val
mkvs(s)
  string s;
{
  Val n;
  n.type = t_str;
  n.value.str = strdup(s);
  return n;
}

Val
mkvn(x)
  f64 x;
{
  Val n;
  if (x == INFINITY) {
    return INF;
  }
  n.type = t_num;
  n.value.num = x;
  return n;
}

string Prl = nil;
string File;
string File2;
i64 Line = 1;
i64 Line2 = 1;
i64 C = 0;
jmp_buf J;

#define TS 10
static string Trace[TS];
i16 Tt = 0;

#define L(n) SRR(Trace[Tt], strlen(n)+1); \
                       strcpy(Trace[Tt], n); \
                       Tt++; \
                       if (Tt >= TS) Tt = 0
#define UL Trace[Tt] = nil; \
                    if (Tt != 0) Tt--

none
ptrc()
{
  i16 i, j;
  for (i = 0; i < TS; i++)
    if (Trace[i] != nil) break;
  if (i == TS) return;
  i = Tt;
  for (j = 0; j < TS; j++) {
    if (i >= TS) i = 0;
    if (Trace[i] != nil) {
      printf("\tfrom '%s'\n", Trace[i]);
    }
    i++;
  }
}

none
rtrc()
{
  for(i16 i = 0; i < TS; i++)
    Trace[i] = nil;
}

bool Quote = false;

string
ass(s, ss)
  string s, ss;
{
  MKS(b, strlen(s) + strlen(ss) + 1);
  strcpy(b, s);
  strcat(b, ss);
  return b;
}

string
asc(s, c)
  string s;
  i8 c;
{
   i64 a = strlen(s);
   MKS(b, a + 2);
   strcpy(b, s);
   b[a] = c;
   b[a+1] = '\0';
   return b;
}

string
cts(c)
  i8 c;
{
  MKS(b, 2);
  b[0] = c;
  b[1] = '\0';
  return b;
}

string
i2s(x)
  i64 x;
{
  i16 s = (i16)((ceil(log10(x))+2) * sizeof(i8));
  MKS(b, s);
  snprintf(b, s, I64F, x);
  return b;
}

f64
pf64(s)
  string s;
{
  string err;
  f64 r;
  errno = 0;
  r = strtod(s, &err);
  if (r == 0 && !isspace(*err) && s == err) e("malformed number literal", s);
  return r;
}

none 
e(s, m)
  string s, m;
{
  fflush(Out);
  if (m && strlen(m) > 0)
    fprintf(Err, "%s:" I64F ":" I64F ": %s: %s\n", File, Line, C, s, m);
  else fprintf(Err, "%s:" I64F ":" I64F ": %s\n", File, Line, C, s);
  printf("\t%s\n", Prl);
  printf("\t~\n");
  ptrc();
  longjmp(J, 1);
}

string
tn(x)
  i16 x;
{
  if (x == t_num || x == t_inf) return "number";
  else if (x == t_str) return "string";
  else if (x == t_nil) return "nil";
  else if (x == t_inf) return "infinity";
  else if (x == t_file) return "file";
  else e("domain error", nil);
  return nil;
}

#define MS 1024
#define BS 1024
#define ES 999

En *E[ES];
strings Fs;
i16 Fst = 0;
#define OVFS(b) for (i16 i = 0; i < ES; i++) { b }

none
drf(s)
  string s;
{
  OVFS(
    if (EQS(s, Fs[i])) {
      SRR(Fs[i], 9);
    })
}

none
adf(s)
  string s;
{
  if (strlen(s) > 8) e("symbol is too long", s);
  if (Fst >= ES) e("memory error", nil);
  else { 
    Fs[Fst] = strdup(s);
    Fst++;
  }
}

bool
isfu(s)
  string s;
{
  OVFS(
    if (EQS(s, Fs[i])) {
      return true;
    }
  )
  return false;
}

i64
h(s)
  string s;
{
  string q;
  i64 k;
  for (k = 0, q = s; *q; q++)
    k = (k<<3) ^ *q;
  return k % ES;
}

Val
f(s)
  string s;
{
  En *p;
  i64 k;

  k = h(s);
  for (p = E[k]; p; p = p->n)
    if (!strcmp(s, p->s))
      return p->a;
  return Error;
}

none
bv(s, x)
  string s;
  Val x;
{
  En *p;
  i64 k;

  k = h(s);
  for (p = E[k]; p; p = p->n)
    if (!strcmp(s, p->s)) {
      p->a = x;
      return;
  }
  p = malloc(sizeof(En));
  strncpy(p->s, s, 8);
  p->s[8] = '\0';
  p->a = x;
  p->n = E[k];
  E[k] = p;
}

typedef struct _St 
{
  i64 t; 
  u64 c;
  Val *a;
} St;

St *S;
St *Rs;

#define LN(s) s->t+1
#define EM(s) (LN(s) == 0)

Val
at(s, x)
  St *s;
  i64 x;
{
  if (x < 0 || x > s->c) return NIL;
  if (x > s->t) return NIL;
  return s->a[x];
}

none 
_u(s, x)
  St *s;
  Val x;     
{ 
  if (LN(s) == s->c - 1) e("stack overflow", nil);
  s->a[++s->t] = x;
}

Val
_t(s)
  St *s;
{
  if (EM(s)) e("stack underflow", nil);
  return s->a[s->t--];
}

Val
_s(s)
  St *s;
{
  if (EM(s)) e("stack underflow", nil);
  return s->a[s->t];
}

#define u(x) _u(S, x)
#define t() _t(S)
#define s() _s(S)

none
ul()
{
  u(NIL);
}

none
ui()
{
  u(INF);
}

none
un(x)
  f64 x;
{
  if (x == INFINITY) {
    ui(); 
    return;
  }
  Val n;
  n.type = t_num;
  n.value.num = x;
  u(n);
}

none
us(s)
  string s;
{
  Val n;
  n.type = t_str;
  n.value.str = strdup(s);
  u(n);
}

none
uf(f)
  fl f;
{
  Val n;
  n.type = t_file;
  n.value.fle = f;
  u(n);
}

none
p(x)
  Val x;
{
  if (NUM(x))
    printf(F64F, x.value.num);
  else if(INF(x))
    printf("<infinity>");
  else if (STR(x))
    printf((strlen(x.value.str) == 1 && Quote)?"'%s'":Quote?"\"%s\"":"%s", x.value.str);
  else if(NIL(x))
    printf("<nil>");
  else if(FLE(x))
    printf("<file>");
  else e("domain error", nil);
}

#define nl() printf("\n")

none
d(s)
  St *s;
{
  if (EM(s)) { 
    printf("[]\n");
    return;
  }

  printf("[");
  for(i64 i = 0; i < LN(s); i++) {
    Quote = true;
    p(at(s, i));
    Quote = false;
    if (i != LN(s)-1) printf(", ");
  }
  printf("]\n");
}

#define ct(x, t) if (x.type != t) e("type error: expected", ass(ass(tn(t), ", got: "), tn(x.type)))
#define isnu(x) if (x.type != t_num && x.type != t_inf) e("type error: expected: number, got", tn(x.type))

#define LOP L(cts(s[i-1]))

#define AR(op) LOP; \
                            y = t(); x = t();  \
                            isnu(x); isnu(y); \
                            un(x.value.num op y.value.num); \
                            UL

#define DIV(op) LOP; \
                             y = t(); x = t(); \
                             isnu(x); isnu(y); \
                             if (x.value.num != 0 && y.value.num == 0) ui(); \
                             else if(x.value.num == 0 && y.value.num == 0) ul(); \
                             else un(x.value.num op y.value.num); \
                             UL


bool
feq(f, ff)
  fl f, ff;
{
  struct stat s, ss;
  if(fstat((i16)f, &s) < 0) e("domain error", nil);
  if(fstat((i16)ff, &ss) < 0) e("domain error", nil);
  return (s.st_dev == ss.st_dev) && (s.st_ino == ss.st_ino);
}

bool
cmp(x, y)
  Val x, y;
{
  if (STR(x) && STR(y))
     return EQS(x.value.str, y.value.str);
  else if (NUM(x) && NUM(y))
    return x.value.num == y.value.num;
  else if (NIL(x) && NIL(y))
    return true;
  else if (INF(x) && INF(y))
    return true;
  else if (FLE(x) && FLE(y))
    return feq(x.value.fle, y.value.fle);    
  else return false;
}

#define ctf(x) ct(x, t_file); \
              if (x.value.fle == nil) e("I/O operation on invalid file", nil);

string
cfm(s, b)
  string s;
  bool b;
{
  if (strlen(s) < 1 || strlen(s) > 2) e("invalid mode", s);
  if (EQS(s, "r"))
    return b?"rb":s;
  else if (EQS(s, "w"))
    return b?"wb":s;
  else if (EQS(s, "a"))
   return b?"ab":s;
  else if (EQS(s, "r+"))
   return b?"rb+":s;
  else if (EQS(s, "w+"))
   return b?"wb+":s;
  else e("invalid mode", s);
  return "";
}

#define isb(s) (EQS(s, "and") \
                          || EQS(s, "or") \
                          || EQS(s, "not") \
                          || EQS(s, "rand") \
                          || EQS(s, "err") \
                          || EQS(s, "at"))
#define chb(s) if (!isb(s)) goto skip; \
                           L(s); \
                           if (EQS(s, "and")) { \
                             y = t(); x = t(); ct(x, t_num); ct(y, t_num); \
                             un(x.value.num && y.value.num); \
                             goto away; \
                           } else if (EQS(s, "or")) { \
                             y = t(); x = t(); ct(x, t_num); ct(y, t_num); \
                             un(x.value.num || y.value.num); \
                             goto away; \
                           } else if (EQS(s, "not")) { \
                             x = t(); ct(x, t_num); \
                             un(!x.value.num); \
                             goto away; \
                           } else if (EQS(s, "rand")) { \
                             x = t(); ct(x, t_num); \
                             un((f64)rand()/(f64)(RAND_MAX/x.value.num)); \
                             goto away; \
                           } else if (EQS(s, "err")) { \
                             y = t(); x = t(); ct(x, t_str); \
                             if (NIL(y)) e(x.value.str, nil); \
                             else { \
                               ct(y, t_str); \
                               e(x.value.str, y.value.str); \
                             } \
                             goto away; \
                           } else if (EQS(s, "at")) { \
                             y = t(); x = t(); ct(x, t_str); ct(y, t_num); \
                             if (y.value.num < 0 || (i64)y.value.num >= strlen(x.value.str)) \
                               ul(); \
                             else us(cts(x.value.str[(i64)y.value.num])); \
                             goto away; \
                           } \
                           skip:
                           
i64
r(s)
  string s;
{
  i64 i, a;
  bool bl;
  Val acc, x, y;
  string b, b2;
  fl fd;
  tv ti;
  i16 ch;
  #define sym(c) (isalnum(c))
  #define name() for(a = 0, b = ""; s[i] && sym(s[i]) && a < 8; i++) { \
                                b = asc(b, s[i]); \
                                a++; \
                              } \
                              if (strlen(b) > 8) e("symbol is too long", b)
  #define nx()       if (s[i]) i++;
  #define rdb(o, c)     a = 1; b = "";          \
                                    while (true) {          \
                                      if (a == 0) break;  \
                                      if (s[i] == c) a--;     \
                                      if (s[i] == o) a++;   \
                                      if ((s[i] == '\0' || i >= strlen(s)-1) && a > 0) e("missing closing " #c " after " #o, nil); \
                                      if (a > 0) b = asc(b, s[i]); \
                                      i++; \
                                   }
  #define cey(x) if (x == 1) goto bye;
  for(i = 0;;) {
    SRR(Prl, strlen(&s[i])+1);
    strcpy(Prl, &s[i]);
    C = i+1;
    switch(s[i++]) {
      case '"':
        for(b = "", a = 0; s[i] && s[i] != '"'; i++) {
          if (s[i] == '\0' || i >= strlen(s)-1) e("non-terminated string", nil);
          if (s[i] == '~') {
            nx();
            switch(s[i++]) {
              case '"': b = asc(b, '"'); break;
              case '~': b = asc(b, '~'); break;
              case 'n': b = asc(b, '\n'); break;
              case 't': b = asc(b, '\t'); break;
              case 's': b = asc(b, ' '); break;
              default: e("unrecognized escape-sequence", cts(s[i-1])); break;
            }
            i--;
            continue;
          } else b = asc(b, s[i]);
        }
        if (s[i] != '"') e("non-terminated string", nil);
        nx();
        us(b);
      break;
      case '#':
        if (!s[i] || s[i] < 1) e("expected a character after '#'", nil);
        un((f64)s[i]);
        nx();
      break;
      case '\'':              
        if (!s[i] || (!isdigit(s[i]) && s[i] != '.')) e("expected a number literal after \"'\"", nil);
        for (b = ""; isdigit(s[i]) || s[i] == 'e' || s[i] == '.'; i++) {
          b = asc(b, s[i]);
        }
        un(pf64(b));
      break;      
      case '%': x = t(); ct(x, t_num); un(-x.value.num); break;
      case '_':
        if (!sym(s[i])) e("expected symbol after '_'", nil); name();
        acc = f(b);
        if (ERR(acc)) e("unbound symbol", b);
        else u(acc);
      break;
      case ':':
        if (!sym(s[i]) && s[i] == ':') {
          bl = true;
          nx();
        } else bl = false;
        if (!sym(s[i])) e(ass("expected symbol after ", bl?"'::'":"':'"), nil); 
        name();
        if (isb(b)) e("built-in cannot be redefined", b);
        SRR(b2, strlen(b)+1);
        strcpy(b2, b);
        if (s[i] != '(') e(ass("expected '(' after ", bl?"'::'":"':'"), nil);
        nx();
        rdb('(', ')');
        if (bl) {
          r(b);
          bv(b2, t());
        } else {
          bv(b2, mkvs(b));
          adf(b2);
        }
      break;
      case '@':
        if (!sym(s[i])) e("expected symbol after '@'", nil); name();
        chb(b);
        acc = f(b);
        if (ERR(acc)) e("unbound symbol", b);
        else {
          if (!isfu(b)) e("call of non-routine", b);
          L(b);
          b = acc.value.str;
          r(b);          
          UL;
        } 
      break;
away: UL;
      break;
      case '.': p(t()); break;
      case ',': SRR(b, 128); scanf("%[^\n]%*c", b); us(b); break;
      case '[':
        x = t(); 
        ct(x, t_num);
        rdb('[', ']');
        if (x.value.num == 1) cey(r(b));
      break;      
      case '{':
        rdb('{', '}');
        while (true) {
          x =  t(); ct(x, t_num);
          if (x.value.num == 0) break;
          cey(r(b));
        }
      break;      
      case '(':
        rdb('(', ')');
        x = t();
        ct(x, t_num);
        for (f64 cc = 1; cc != x.value.num+1; cc++) {
          bv("i", mkvn(cc));
          cey(r(b));
        }
      break;    
      case '=':
        y = t(); x = t();
        un(cmp(x, y));
      break;
      case '<':
        AR(<);
      break;
      case '>':
        AR(>);
      break;
      case '~':
        x = t(); ct(x, t_num);
        if (x.value.num == 0) 
          un(1);
        else if (x.value.num == 1)
          un(0);
        else u(x);
      break;
      case '+': AR(+); break;
      case '-': 
          AR(-);
      break;
      case '*': AR(*); break;
      case '/': 
        DIV(/);      
        un(fmod(x.value.num, y.value.num));
      break;
      case '$': switch(s[i++]) {
        case '!': _t(Rs); break;
        case '&': _u(Rs, _s(Rs)); break;
        case '\\': y = _t(Rs); x = _t(Rs); _u(Rs, y); _u(Rs, x); break;
        case '?': un(LN(Rs)); break;
        case 'c':
          while (!EM(Rs)) {
            u(_t(Rs));
          }
        break;
        case 'o':
          while (!EM(S)) {
            _u(Rs, t());
          }
        break; 
        case 's': u(_s(Rs)); break;
        case 'g': u(_t(Rs)); break;
        case 'r':
          Rs = (St *)malloc(sizeof(St));
          MEC(Rs);
          Rs->c = MS;
          Rs->t = -1;
          Rs->a = (Val *)malloc(Rs->c * sizeof(Val));
        break;
        default: _u(Rs, t()); i--; break;
      }
      break;
      case '!': t(); break;
      case '&': u(s()); break;
      case '\\': y = t(); x = t(); u(y); u(x); break;
      case ';': y = t(); x = t(); u(x); u(x); u(y); break;
      case '?': un(LN(S)); break;
      case '\0': goto ok; break;
      case 'q': end(0); break;
      case '|':
        for(; s[i] && s[i] != '|'; i++) {
          if (s[i] == '\0' || i >= strlen(s)-1) e("non-terminated comment", nil);
        }
        if (s[i] != '|') e("non-terminated comment", nil);
        nx();
      break;
      case '`':        
        if (!isalpha(s[i])) e("expected a letter after '`'", nil);
        switch(s[i]) {
          case 'y': goto bye; break;
          case 'o':
            AR(||);
          break;
          case 'a':
            AR(&&);
          break;
          case 't':
            SRR(b, 513);
            gettimeofday(&ti, nil);
            snprintf(b, 512, "%lu.%lu", ti.tv_sec, ti.tv_usec);
            un(atof(b));
            free(b);
         break;
         case 'c': switch(s[++i]) {
           case 'n': 
             x = t(); 
             if (STR(x))
               un(pf64(x.value.str));
           else if (NUM(x))
             u(x);
           else if (NIL(x))
             ul();
           else if (INF(x))
             ui();
           else e(ass(ass("cannot cast ", tn(x.type)), " to"), "number");
         break;
         case 's': 
           x = t(); 
           SRR(b, 128);
           if (NUM(x)) {
             snprintf(b, 128, F64F, x.value.num);
             us(b);
           } else if (STR(x))
             u(x);
           else if (NIL(x))
             us("");
           else if (INF(x))
             us("infinity");
           else { 
             free(b);
             e(ass(ass("cannot cast ", tn(x.type)), " to"), "string");         
           }
           free(b);
         break;
         case 'c': x = t(); ct(x, t_str); if (strlen(x.value.str) != 1) e("expected a one-character string, got", x.value.str); un((f64)x.value.str[0]); break;
         case 'h': x = t(); ct(x, t_num); us(cts((i8)x.value.num)); break;
         default: e("invalid syntax after 'c'", cts(s[i])); break;
        }
        break;
        case 'f': switch(s[++i]) {
          case 'o': 
            y = t(); x = t();
            ct(x, t_str); ct(y, t_str);
            fd = fopen(x.value.str, cfm(y.value.str, true));
            if (fd == nil) ul();
            else uf(fd);
          break;
          case 'r':
            x = t(); 
            ctf(x);
            fd = x.value.fle;
            fseek(fd, 0, SEEK_END);
            a = ftell(fd);
            rewind(fd);
            SRR(b, a + 1);
            fread(b, 1, a, fd);
            b[a] = '\0';
            us(b);
            free(b);
          break;
          case 'i':
            x = t();
            ctf(x);
            fd = x.value.fle;
            rewind(fd);
          break;
          case 'h':
            x = t();
            ctf(x);
            fd = x.value.fle;
            ch = fgetc(fd);
            if (ch == EOF || ferror(fd) != 0) ul();
            else us(cts((i8)ch));
          break;
          case 'w':
            y = t(); x = t();
            ctf(x); ct(y, t_str);
            fd = x.value.fle;
            SRR(b, strlen(y.value.str) + 1);
            strncpy(b, y.value.str, strlen(y.value.str));
            a = fwrite(b, sizeof(i8), sizeof(b), fd);
            if (a != sizeof(b)) un(0);
            else un(1);
            free(b);
          break;
          case 'l':
            x = t();
            ctf(x);
            fd = x.value.fle;
            SRR(b, 512);
            if (fgets(b, 512, fd) == nil) ul();
            else us(b);          
            free(b);
          break;
          case 'c':
            x = t();
            ct(x, t_file);
            fd = x.value.fle;
            if (fd != nil) fclose(fd);
          break;
          default: e("invalid syntax after 'f'", cts(s[i])); break;
        }
      }
      nx();
      break;
      case 'N': ul(); break;
      case 'I': ui(); break;
      case 'P': un(3.141592653589793); break;
      case 'T': un(6.283185307179586); break;
      case 'E': un(2.718281828459045); break;
      case ' ': case '\n': case '\r': case '\t': break;
      default: e("syntax error", cts(s[i-1])); break;
    }
    if (Prl) free(Prl);
  }
ok:
  return 0;
bye:
  return 1;
}

none
_load(p)
  fl p;
{  
  buf(b, BS);
  Line2 = Line;
  Line = 1;
  while(fgets(b, BS+1, p) != nil) {
    rtrc();
    r(b);
    Line++;
    C = 0;
  }
  Line = Line2;
}

bool
l(n)
  string n;
{
  if (File) File2 = strdup(File);
  File = n;
  fl p = fopen(n, "r");
  if (p == nil) goto fail;
  _load(p);
  fclose(p); 
  return true;

fail:
  if (File2) File = strdup(File2);
  return false;
}

none
logo()
{
  printf("nulang v.%s(b.%s)\n", VER, __DATE__);
  printf("by @txlyre, www: txlyre.website\n");
  nl();
}

none
rl()
{
  logo();
  printf("REPL-mode started\n");
  printf("(press Ctrl+C or type q to exit)\n");
  File = "<repl>";
  Line = 1;
  setjmp(J);
  buf(b, 65);  
  i64 i;
  while (true) {
    C = 0;
    rtrc();
    printf(": ");
    fgets(b, 64, In);
    i = strlen(b);
    if (b[i-1] == '\n') b[i-1] = '\0';
    if (feof(In)) break;
    r(b);
    nl();
    d(S);
    d(Rs);
  }
}

none
init()
{
  S = (St *)malloc(sizeof(St));
  MEC(S);

  S->c = MS;
  S->t = -1;
  S->a = (Val *)malloc(S->c * sizeof(Val));
  Rs = (St *)malloc(sizeof(St));
  MEC(Rs);

  Rs->c = MS;
  Rs->t = -1;
  Rs->a = (Val *)malloc(Rs->c * sizeof(Val));

  NIL.type = t_nil;
  INF.type = t_inf;
  INF.value.num = INFINITY;
  Error.type = t_err;
  En *a, *b;
  for (i64 i = 0; i < ES; i++) {
    for (a = E[i]; a; a = b) {
      b = a->n;
      free(a);
    }
    E[i] = nil;
  }
  Fs = malloc(ES * sizeof(string));
  for (i16 i = 0; i < ES; i++) {
    SRR(Fs[i], 9);
  }
  rtrc();
  srand(time(nil));
}

none
end(c)
  i16 c;
{
  free(S);
  free(Rs);
  free(Fs);
  exit(c);
}

i16 
main(argc, argv)
  i16 argc;
  strings argv;
{
  init();

  if (!setjmp(J)) if (!l("prelude")) e("failed to load", "prelude");

  if (!setjmp(J)) {
    if (argc > 1) {
      if(!l(argv[1])) e("failed to load", argv[1]);
      end(0);
    }
  } else end(1);
  
  if(!setjmp(J)) rl();
  end(0);
}
