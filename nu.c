#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <setjmp.h>
#include <time.h>
#include <math.h>

#define VER "0.0.1"

typedef char * string;
typedef string * strings;
typedef long i32;
typedef unsigned long u32;
typedef float f32;
typedef int i16;
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

#define F32F "%.6g"

typedef struct 
{
  enum _T { t_num, t_str, t_nil, t_err, t_inf } type;
  union { f32 num; string str; } value;
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
  f32 x;
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
i32 Line = 1;
i32 Line2 = 1;
jmp_buf J;

#define TS 10
static string Trace[TS];
i16 Tt = 0;

#define L(n) SRR(Trace[Tt], strlen(n)+1); \
                       strcpy(Trace[Tt], n); \
                       Tt++; \
                       if (Tt >= TS) Tt = 0

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
  b[0] = '\0';
  strcat(b, s);
  strcat(b, ss);
  return b;
}

string
asc(s, c)
  string s;
  i8 c;
{
   i32 a = strlen(s);
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
  i32 x;
{
  i16 s = (i16)((ceil(log10(x))+2) * sizeof(i8));
  MKS(b, s);
  snprintf(b, s, "%ld", x);
  return b;
}

none 
e(s, m)
  string s, m;
{
  fflush(Out);
  if (m && strlen(m) > 0)
    fprintf(Err, "%s:%ld: %s: %s\n", File, Line, s, m);
  else fprintf(Err, "%s:%ld: %s\n", File, Line, s);
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
  else if(x == t_str) return "string";
  else if(x == t_nil) return "nil";
  else e("domain error", nil);
  return nil;
}

#define MS 1024
#define BS 1024
#define ES 999

En *E[ES];
En *Js[ES];
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

i32
h(s)
  string s;
{
  string q;
  i32 k;
  for (k = 0, q = s; *q; q++)
    k = (k<<3) ^ *q;
  return k % ES;
}

Val
fj(s)
  string s;
{
  En *p;
  i32 k;

  k = h(s);
  for (p = Js[k]; p; p = p->n)
    if (!strcmp(s, p->s))
      return p->a;
  return Error;
}

none
bj(s, x)
  string s;
  Val x;
{
  En *p;
  i32 k;

  k = h(s);
  for (p = Js[k]; p; p = p->n)
    if (!strcmp(s, p->s)) {
      p->a = x;
      return;
  }
  p = malloc(sizeof(En));
  strncpy(p->s, s, 8);
  p->s[8] = '\0';
  p->a = x;
  p->n = Js[k];
  Js[k] = p;
}

Val
f(s)
  string s;
{
  En *p;
  i32 k;

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
  i32 k;

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
  i32 t; 
  u32 c;
  Val *a;
} St;

St *S;
St *Rs;

#define LN(s) s->t+1
#define EM(s) (LN(s) == 0)

Val
at(s, x)
  St *s;
  i32 x;
{
  if (x < 0 || x > s->c) return NIL;
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
  f32 x;
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
p(x)
  Val x;
{
  if (NUM(x))
    printf(F32F, x.value.num);
  else if(INF(x))
    printf("<infinity>");
  else if (STR(x))
    printf(Quote?"\"%s\"":"%s", x.value.str);
  else if(NIL(x))
    printf("<nil>");
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
  for(i32 i = 0; i < LN(s); i++) {
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
                            un(x.value.num op y.value.num)

#define DIV(op) LOP; \
                             y = t(); x = t(); \
                             isnu(x); isnu(y); \
                             if (x.value.num != 0 && y.value.num == 0) ui(); \
                             else if(x.value.num == 0 && y.value.num == 0) ul(); \
                             else un(x.value.num op y.value.num)
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
  else return false;
}

none
r(s)
  string s;
{
  i32 i, a;
  Val acc, x, y;
  string b, b2;
  //printf("\"%s\"\n", s);
  #define sym(c) (isdigit(c) || isalpha(c))
  #define name() for(a = 0, b = ""; s[i] && sym(s[i]) && a < 8; i++) { \
                                b = asc(b, s[i]); \
                                a++; \
                              } \
                              if (strlen(b) > 8) e("symbol is too long", b)
  #define nx()       if (s[i]) i++
  #define nxe(s)   if (s[i]) i++; else e(s, nil)
  #define ex(s)     if (!s[i] || s[i] == '\0') e(s, nil);
  #define rdb(o, c)     a = 1; b = "";          \
                                    while (true) {          \
                                      if (a == 0) break;  \
                                      if (s[i] == c) a--;     \
                                      if (s[i] == o) a++;   \
                                      if ((s[i] == '\0' || i >= strlen(s)-1) && a > 0) e("missing closing " #c " after " #o, nil); \
                                      if (s[i] != c && a > 0) b = asc(b, s[i]); \
                                      i++; \
                                   }
  for(i = 0;;) {
    SRR(Prl, strlen(&s[i])+1);
    strcpy(Prl, &s[i]);
    
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
        un((f32)s[i]);
        nx();
      break;
      case '\'':              
        for (b = ""; isdigit(s[i]) || s[i] == 'e' || s[i] == '.'; i++) {
          b = asc(b, s[i]);
        }
        un(atof(b));
      break;      
      case '%': x = t(); ct(x, t_num); un(-x.value.num); break;
      case '_':
        if (!sym(s[i])) e("expected symbol after '_'", nil); name();
        acc = f(b);
        if (ERR(acc)) e("unbound symbol", b);
        else u(acc);
      break;
      case ':':
        if (!sym(s[i])) e("expected symbol after ':'", nil); 
        name();
        b2 = strdup(b);
        if (s[i] == '\0' || s[i] == '\n') e("expected routine body after ':'", nil);
        for(b = ""; s[i] != '\n' && s[i] != '\0'; i++) {
          if (s[i] == '\r' || s[i] == '\n') { nx(); continue; }
          b = asc(b, s[i]);
        }
        bv(b2, mkvs(b));
        adf(b2);
      break;
      case '@':
        if (!sym(s[i])) e("expected symbol after '@'", nil); name();
        acc = f(b);
        if (ERR(acc)) e("unbound symbol", b);
        else {
          if (!isfu(b)) e("call of non-routine", b);
          L(b);
          b = acc.value.str;
          r(b);
        }
      break;
      case '.': p(t()); break;
      case ',': SRR(b, 128); scanf("%[^\n]%*c", b); us(b); break;
      case '[':
        x = t(); 
        ct(x, t_num);
        rdb('[', ']');
        if (x.value.num == 1) r(b);
      break;      
      case '{':
        rdb('{', '}');
        while (true) {
          x =  t(); ct(x, t_num);
          if (x.value.num == 1) break;
          r(b);
        }
      break;      
      case '(':
        rdb('(', ')');
        x = t();
        ct(x, t_num);
        for (f32 cc = 1; cc != x.value.num+1; cc++) {
          bv("i", mkvn(cc));
          r(b);
        }
      break;    
      case '`':
        if (!sym(s[i])) e("expected symbol after '`'", nil); name();
        if (!ERR(fj(b))) e("label redefined", b);
        bj(b, mkvn((f32)i));
      break;  
      case 'g':
        if (!sym(s[i])) e("expected symbol after 'g'", nil); name();
        acc = fj(b);
        if (ERR(acc)) e("undefined label", b);
        i = (i32)acc.value.num;
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
      case '+': AR(+); break;
      case '-': 
        if (s[i] == '>') {
          nx();
          if (!sym(s[i])) e("expected symbol after '->'", nil); 
          name();
          bv(b, t());
        } else {
          AR(-); 
        }
      break;
      case '*': AR(*); break;
      case '/': DIV(/); break;
      case '!': t(); break;
      case '&': u(s()); break;
      case '\\': y = t(); x = t(); u(y); u(x); break;
      case '\0': case 'y': goto bye; break;
      case 'q': end(0); break;
      case '|':
        for(; s[i] && s[i] != '|'; i++) {
          if (s[i] == '\0' || i >= strlen(s)-1) e("non-terminated comment", nil);
        }
        if (s[i] != '|') e("non-terminated comment", nil);
        nx();
      break;
      case 'c': switch(s[i++]) {
        case 'n': 
          x = t(); 
          if (STR(x))
            un(atof(x.value.str));
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
            snprintf(b, 128, F32F, x.value.num);
            us(b);
          } else if (STR(x))
            u(x);
          else if (NIL(x))
            us("");
          else if (INF(x))
            us("infinity");
          else e(ass(ass("cannot cast ", tn(x.type)), " to"), "string");
          
        break;
        default: x = t(); ct(x, t_num); us(cts((i8)x.value.num)); i--; break;
      }
      break;
      case 'N': ul(); break;
      case 'I': ui(); break;
      case ' ': case '\n': case '\r': case '\t': break;
      default: e("syntax error", cts(s[i-1])); break;
    }
  }
bye:
  return;
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
  i32 i;
  while (true) {
    rtrc();
    printf(": ");
    fgets(b, 64, In);
    i = strlen(b);
    if (b[i-1] == '\n') b[i-1] = 0;
    if (feof(In)) break;
    r(b);
    nl();
    d(S);
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
  for (i32 i = 0; i < ES; i++) {
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