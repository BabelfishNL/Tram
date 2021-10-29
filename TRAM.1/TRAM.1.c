#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#define error(...) {\
    fprintf( stderr, "***ERROR***\n"); \
    fprintf( stderr, __VA_ARGS__); \
    fprintf( stderr, "\n"); \
    fflush(stderr); \
    exit(1); \
}

typedef uint32_t tval; // tagged value

// Layered tagged values:
// x0 ref (idx)
// d01 dta (d is int, char, bin/dec/hex digit, small float, ...)
// LVvvv0..011 var: V=[*&A-Z], v=[^A-Za-z0-9] or null (right-to-left), L=1 if longer than 4
// ffffFL11 id, F=[@$A-Z], f=[^A-Za-z0-9] or null (right-to-left), L=1 if longer than 5

#define isREF(t) (((t)&1)==0)
#define isNREF(t) (((t)&1)==1)
#define isVAR(t) (((t)&0xff)==3)
#define isFUN(t) (((t)&3==3)&&((t)&0xff)>3)

#define ref(t) (mem+(t)/2)
#define idx(r) ((r-mem)*2)

typedef struct _node {
    tval car, cdr, nxt;
} node;
typedef node *ref;

ref new(tval x,tval y);

#define Push(X,a) X=new(a,idx(X));
#define Pop(X) X->car; X=ref(X->cdr);
#define PopRef(X) ref(X->car); X=ref(X->cdr);

int MEMSIZE=100000; //nodes
ref mem, usedNodes, freeNodes;
#define nil mem

int Dbg=0;
enum DbgSt {DNone,DIO,DGC,DSteps,DStepDump,DCycles};
//debug levels -- 0: none, 1: I/O, 2: gc, 3: rewr steps, 4:: dump steps, 5:dump cycles
int Drulei,Drewrcnt=0;

//registers safe from GC
ref P, S, X;
tval T, V;

void init() {
    if (sizeof(tval)!=4 || sizeof(node)!=12) {
        error("Bad size tval: %ld (=4), sizeof node: %ld (=12)\n",sizeof(tval), sizeof(node))
    }
    mem = (ref)malloc(MEMSIZE * sizeof(node));
    mem -= 1; // index 0 is nil and not a node
    freeNodes = nil;
    for (ref r=mem+1; r-mem<MEMSIZE; r++) {
        r->nxt=idx(freeNodes);
        freeNodes = r;
    }
    P = S = X = usedNodes = nil;
    T = V = 0;
}

#define MARK 1
#define set(t,n) ((n)|=(t))
#define has(t,n) ((n)&(t))
#define rst(t,n) ((n)&=(~(t)))

int gen=0;
void gc() {
	if (Dbg>=DGC) fprintf( stdout, "GC gen %d: ",gen++);
	ref trail=nil;
	long cnt = 0;

    if (P!=nil) set(MARK,P->nxt);
    if (X!=nil) set(MARK,X->nxt);
	if (S!=nil) set(MARK,S->nxt);
	if (isREF(T)&&T!=0) set(MARK,ref(T)->nxt);
	if (isREF(V)&&V!=0) set(MARK,ref(V)->nxt);

	for (ref r = usedNodes; r!=nil; ) {
		if (has(MARK,r->nxt)) {
			rst(MARK,r->nxt);
			if (isREF(r->car)) {
				set(MARK,ref(r->car)->nxt);
			}
			if (isREF(r->cdr)) {
				set(MARK,ref(r->cdr)->nxt);
			}
			if (trail==nil) {
				usedNodes = trail = r;
			} else {
				trail = r;
			}
			r=ref(r->nxt);
		} else {
			ref nxt;
			if (trail==nil) {
				usedNodes = nxt = ref(r->nxt);
			} else {
				trail->nxt = r->nxt;
                nxt = ref(r->nxt);
            }
			r->nxt = idx(freeNodes);
			freeNodes = r;
			cnt++;
			r = nxt;
		}
	}
	if (Dbg>=DGC) fprintf( stdout, "%ld freed\n",cnt);
}

ref new(tval x, tval y) {
    if (freeNodes==nil) {
        gc();
    }
    if (freeNodes==nil) {
        error("Out of Memory");
    }
    ref tmp = freeNodes;
    freeNodes = ref(freeNodes->nxt);
    tmp->nxt = idx(usedNodes);
    usedNodes=tmp;
    tmp->car = x;
    tmp->cdr = y;
    return tmp;
}

void pval(tval v,int nl);

FILE *in;
int c;

tval readTerm(char *nm) {
    tval num, v;
    int sgn, len;
    if ((in = fopen(nm, "r"))==NULL) {
        error("unknown file %s",nm);
    };
    c = fgetc(in);
    for (;;) {
        switch (c) {
            case ' ': case '\n': case '\r': case '\t': case '\v': case '\f':
                break;
            case '!': // comment
                while ((c=fgetc(in))!='\n') {}
                break;
             case '#': // data (hex or dec)
                 if ((c=fgetc(in))=='0') {
                    if ((c=fgetc(in))=='x') {
                        num = 0;
                        while ((c = fgetc(in)) >= '0' && c <= '9' || c >= 'a' && c <= 'f' || c >= 'A' && c <= 'F') {
                            num = 16 * num + (c <= '9' ? c - '0' : c <= 'F' ? 10 + c - 'A' : 10 + c - 'a');
                        }
                        v = (num << 2) | 1;
                        continue;
                    } else if (c>='0'&&c<='9') {
                        sgn = 1;
                        num = c-'0';
                        goto decimal;
                    } else {
                            v = 1;
                            continue;
                    }
                } else {
                    if (c=='-') {
                        sgn = -1;
                        num = 0;
                    } else {
                        sgn = 1;
                        num = c-'0';
                    }
                  decimal:
                    while ((c=fgetc(in))>='0'&&c<='9') {
                        num = 10*num+c-'0';
                    }
                    v = ((sgn*num)<<2)|1;
                    continue;
                }
            case '\'': //data (char)
                v = (fgetc(in)<<2)|1;
                if ((c=fgetc(in))!='\'') error("expected ' got character %c (%d)",c,c);
                break;
            case '%': // dec (meta-variable)
                num = 0;
                while ((c=fgetc(in))>='0'&&c<='9') {
                    num = 10*num+c-'0';
                }
                for (v=T, len=0; v!=0; v=ref(v)->cdr) len++;
                num = len-num;
                for (v=T; num--; v=ref(v)->cdr) {}
                v = ref(v)->car;
                continue;
            case '*': case '&': // Var
            case 'A': case 'B': case 'C': case 'D': case 'E': case 'F': case 'G':
            case 'H': case 'I': case 'J': case 'K': case 'L': case 'M': case 'N':
            case 'O': case 'P': case 'Q': case 'R': case 'S': case 'T': case 'U':
            case 'V': case 'W': case 'X': case 'Y': case 'Z':
                len = 1;
                num = c=='*'?1:c=='&'?2:c-'A'+3;
                while ((c=fgetc(in))=='.'||c>='0'&&c<='9'||c>='a'&&c<='z'||c>='A'&&c<='Z') {
                    if (++len<=4) {
                        num = num << 6 | (c == '^' ? 1 : c - (c <= '9' ? '0'-2 : (c <= 'Z' ? 'A'-12 : 'a'-38)));
                    }
                }
                sgn = len>4?1<<31:0;
                while (++len<=4) {
                    num <<= 6;
                }
                v = (num<<8)|sgn|3;
                continue;
            case '@': case '$': // Id
            case 'a': case 'b': case 'c': case 'd': case 'e': case 'f': case 'g':
            case 'h': case 'i': case 'j': case 'k': case 'l': case 'm': case 'n':
            case 'o': case 'p': case 'q': case 'r': case 's': case 't': case 'u':
            case 'v': case 'w': case 'x': case 'y': case 'z':
                len = 1;
                num = c=='@'?1:c=='$'?2:c-'a'+3;
                while ((c=fgetc(in))=='.'||c>='0'&&c<='9'||c>='a'&&c<='z'||c>='A'&&c<='Z') {
                    if (++len<=5) {
                        num = num << 6 | (c == '^' ? 1 : c - (c <= '9' ? '0'-2 : (c <= 'Z' ? 'A'-12 : 'a'-38)));
                    }
                }
                sgn = len>5?4:0;
                while (++len<=5) {
                    num <<= 6;
                }
                v = (num<<8) | (num>>21)&0xf8 | sgn | 3;
                continue;
            case '(':
                Push(S, idx(new(v,0)));
                v=0;
                break;
            case ',':
                if (isFUN(v)) v=idx(new(v,0));
                V = Pop(S);
                Push(S, idx(new(v,V)));
                V=v=0;
                break;
            case ')':
                if (isFUN(v)) v=idx(new(v,0));
                v=idx(new(v,0));
                V = Pop(S);
                while (V!=0) {
                    v=idx(new(ref(V)->car,v));
                    V = ref(V)->cdr;
                }
                break;
            case '=':
                if (isFUN(v)) v=idx(new(v,0));
                Push(S,v);
                v=0;
                break;
            case ';':
                if (isFUN(v)) v=idx(new(v,0));
                V = Pop(S);
                Push(S, idx(new(V,v)));
                v=0; V=0;
                break;
            case EOF:
                if (S!=nil) {
                    v=idx(S);
                    S=nil;
                }
                if (isFUN(v)) v=idx(new(v,0));
                return v;
            default:
                error("unexpected character %c (%d)",c,c);
        };
        c = fgetc(in);
    }
}

enum states {BURED=1000, BUDONECDR, BUDONEBOTH, TOPRED, FORRULES, MATCH, MATCHDONE, MATCHDONECAR,
    INSTDONECAR, INSTDONEBOTH, BUILD, ALLDONE, INST, INSTCONT, PRINT, PRT, PRINTDONECAR, PRINTDONEBOTH};
const char * prstates[] = {"BURED", "BUDONECDR", "BUDONEBOTH", "TOPRED", "FORRULES", "MATCH", "MATCHDONE", "MATCHDONECAR",
    "INSTDONECAR", "INSTDONEBOTH", "BUILD", "ALLDONE", "INST", "INSTCONT"};
#define asDTA(d)  1+4*d
#define PopDTA(X) (X->car-1)>>2; X=ref(X->cdr);

#define FSYMeos 0xD380003B
#define FSYMstr 0xE77000AB
#define FSYMlst 0xE3900073
#define FSYMeol 0xD310003B

char *var0="~*&ABCDEFGHIJKLMNOPQRSTUVWXYZ",
*idc="~^0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz",
*fun0="~@$abcdefghijklmnopqrstuvwxyz";
void qpc(char const c) {
    if (c!='~') fprintf(stdout, "%c",c);
}
void pval(tval v,int nl) {
    if ((v&1)==0) {//ref
        fprintf(stdout, "\\%d",v);
    } else if ((v&3)==1) {//data
        fprintf(stdout, "#0x%x",v>>2);
    } else if ((v&0xff)==3) {//Var
        fprintf(stdout, "%c",var0[(v>>26)&31]);
        qpc(idc[(v>>20)&63]); qpc(idc[(v>>14)&63]); qpc(idc[(v>>8)&63]);
        fprintf(stdout, "%s",(v>>31)&1?"...":"");
    } else {//Id
        fprintf(stdout, "%c",fun0[(v>>3)&31]);
        qpc(idc[(v>>26)&63]); qpc(idc[(v>>20)&63]); qpc(idc[(v>>14)&63]); qpc(idc[(v>>8)&63]);
        fprintf(stdout, "%s",((v>>2)&1)?"...":"");
    }
    if (nl) fprintf(stdout, "\n");
}

int flats=0;
void ptrm(tval t) {
    ref ptr;
    X=nil;
    int instr = 0;
    for(;;) {
        if (isREF(t)) {
            ptr = ref(t);
            if (isFUN(ptr->car)) {
                if (flats && ptr->car == FSYMstr) {
                    if (!instr) {
                        instr = 1;
                        fprintf(stdout, "\"");
                    }
                    fprintf(stdout, "%c", (char)((ref(ref(ptr->cdr)->car)->car) >> 2));
                    t = ref(ref(ptr->cdr)->cdr)->car;
                    continue;
                } else if (flats && ptr->car == FSYMeos) {
                    if (instr) {
                        instr = 0;
                        fprintf(stdout, "\"");
                    } else {
                        fprintf(stdout, "\"\"");
                    }
                } else {
                    pval(ptr->car,0);
                    if (ptr->cdr != 0) {
                        fprintf(stdout, "(");
                        Push(X, (')' << 2) + 1);
                        t = ptr->cdr;
                        continue;
                    }
                }
            } else {
                if (ptr->cdr!=0) {
                    Push(X,ptr->cdr);
                    Push(X,(','<<2)+1);
                }
                t = ptr->car;
                continue;
            }
        } else {
            pval(t,0);
        }
        while (X!=nil && isNREF(X->car)) {
            t=Pop(X);
            fprintf(stdout, "%c", t>>2);
        }
        if (X==nil) return;
        t = Pop(X);
        continue;
    }
}

void pprg(ref p) {
    while(p!=nil) {
        ptrm(ref(p->car)->car);
        fprintf(stdout, " = ");
        ptrm(ref(p->car)->cdr);
        fprintf(stdout, ";\n");
        p=ref(p->cdr);
    }
    fprintf(stdout, "\n");
}

ref reduce (/*tval T, ref P*/) {
    S = nil;
    int state=BURED;
    tval f, t, pat;
    ref p, sub;
    Push(S,asDTA(ALLDONE));
    for (;;) {
        if (Dbg >= DCycles) fprintf(stdout, "%s ", prstates[state - 1000]);
        switch (state) { // T is subject term, V is result
            case BURED: //T is term
                if (isNREF(T) || T == 0) {
                    V = T;
                    state = PopDTA(S);
                    break;
                }
                Push(S, ref(T)->car);
                Push(S, asDTA(BUDONECDR));
                T = ref(T)->cdr;
                break;
            case BUDONECDR: //V is cdr, tos is car-to-do
                T = Pop(S);
                Push(S, V);
                Push(S, asDTA(BUDONEBOTH));
                state = BURED;
                break;
            case BUDONEBOTH: //(V is car), tos is cdr
                if (isREF(V)) {
                    T = Pop(S);
                    V = idx(new(V, T));
                    state = PopDTA(S);
                    break;
                }
                f = V;
                T = Pop(S);
                state = TOPRED;
                break;
            case TOPRED: //(f is fun,T = args)
                if (Dbg >= DStepDump) pval(f, 1);
                p = P;
                t = T;
                state = FORRULES;
                if (Dbg >= DSteps) Drulei = 0;
                break;
            case FORRULES: //(f,t,p, T, P)
                if (p == nil) { // eor
                    state = BUILD;
                    break;
                }
                if (Dbg >= DSteps) Drulei++;
                if (ref(ref(p->car)->car)->car != f) {
                    p = ref(p->cdr);
                    break;
                }
                sub = nil;
                Push(S, asDTA(MATCHDONE));
                state = MATCH;
                pat = ref(ref(p->car)->car)->cdr;
                break;
            case MATCH: //(t,pat,sub,p, T, P)
                if (isREF(pat) && pat != 0) { // compound
                    if (isNREF(t)) goto fail;
                    Push(S, ref(t)->cdr);
                    Push(S, ref(pat)->cdr);
                    Push(S, asDTA(MATCHDONECAR));
                    pat = ref(pat)->car;
                    t = ref(t)->car;
                    break;
                }
                if (isVAR(pat)) {
                    sub = new(idx(new(pat, t)), idx(sub));
                    state = PopDTA(S);
                    break;
                }
                if (pat == t) {
                    state = PopDTA(S);
                    break;
                }
                //fallthrough intended
            fail:
                p = ref(p->cdr);
                t = T;
                do {
                    state = PopDTA(S);
                } while (state != MATCHDONE);
                state = FORRULES;
                break;
            case MATCHDONECAR://(sub,p) tos is pat.cdr, 2nd is trm.cdr
                pat = Pop(S);
                t = Pop(S);
                state = MATCH;
                break;
            case MATCHDONE://(sub,p)
                pat = ref(p->car)->cdr; //rhs
                state = INST;
                if (Dbg >= DSteps) Drewrcnt++;
                if (Dbg >= DSteps) printf("Rule %d, Steps %d\n", Drulei, Drewrcnt);
                break;
            case INST: //(pat,sub)
                if (isREF(pat) && pat != 0) {
                    Push(S, ref(pat)->cdr);
                    pat = ref(pat)->car;
                    Push(S, asDTA(INSTDONECAR));
                    break;
                }
                if (isVAR(pat)) {// use p as tmp in sub
                    p = sub;
                    while (ref(p->car)->car != pat) {
                        p = ref(p->cdr);
                    }
                    V = ref(p->car)->cdr;
                    state = PopDTA(S);
                    break;
                }
                V = pat;
                state = PopDTA(S);
                break;
            case INSTDONECAR: // V is car
                pat = Pop(S);
                Push(S, V);
                Push(S, asDTA(INSTDONEBOTH));
                state = INST;
                break;
            case INSTDONEBOTH: // V is cdr, ToS = car
                t = Pop(S);
                if (isFUN(t)) {
                    f = t;
                    T = V;
                    Push(S, pat);
                    Push(S, idx(sub));
                    Push(S, asDTA(INSTCONT));
                    state = TOPRED;
                    break;
                }
                V = idx(new(t, V));
                state = PopDTA(S);
                break;
            case INSTCONT: {// V is car
                    sub = PopRef(S);
                    pat = Pop(S);
                    state = PopDTA(S);
                    break;
                }
            case BUILD:
                V = idx(new(f, T));
                state = PopDTA(S);
                break;
            case ALLDONE: //done
                //res = Pop(S);
                if (S != nil) {
                    error("Stack should be empty!");
                }
                return ref(V);
            default: error("Bad state!");
        }
    }
}

ref rcat(ref r, ref s) {//prepend reverse r to s
    while (r!=nil) {
        Push(s,r->car);
        r=ref(r->cdr);
    }
    return s;
}
#define rev(r) rcat(r,nil)

int main(int argc, char *argv[]) {
    int i=1;
    tval t;
    char *nm;
    int fln,fi=0;

    if (argc<2) {
        printf(
        "      Note that D and X must appear as 1st and 2nd cli switch when used\n"
        "-D n         generate level n (1..3) debugging info\n"
        "-X nnn       set memory size to nnn*1000\n"
        "\n"
        "-P <fname>   Load program\n"
        "-p <fname>   Load program segment\n"
        "-C           Compile all segments into one program\n"
        "      Note that either -P or -p...-p -C should be used\n"
        "-T <fname>   Read term as subject\n"
        "-t <fname>   Read sub-term\n"
        "-s <fname>   Read string sub-term\n"
        "-b <fname> <todo> Read binary sub-term\n"
        "-M <fname>   Read meta-term as subject\n"
        "-m <fname> <todo> Read meta term as sub-term\n"
        "-I <fname>   dump program\n"
        "-i <fname>   dump subject term\n"
        "-r           reduce subject using program\n"
        "-O <fname>   dump result term\n"
        "-S <fname> <todo> print result as text\n"
        "-B <fname> <todo> print result as binary\n"
        );
    }
    if (i<argc && argv[i][1]=='D') { Dbg = argv[++i][0]-'0'; i++; }
    if (i<argc && argv[i][1]=='X') { sscanf(argv[++i], "%i", &MEMSIZE); MEMSIZE*=100000; i++; }

    init();

    P=nil;
    V=0;
    while (i<argc && argv[i][0]=='-') {
        switch (argv[i++][1]) {
            case 'P':   P = rev(ref(readTerm(argv[i++])));
                        break;
            case 'p':   P = new(readTerm(argv[i++]),idx(P));
                        break;
            case 'C':   for (X=nil; P!=nil; ) {
                            t = Pop(P);
                            while ( t!=0) {
                                Push(X,ref(t)->car);
                                t = ref(t)->cdr;
                            }
                        }
                        P = X; X=nil;
                        break;
            case 'T':
            case 'M':   T = readTerm(argv[i++]);
                        break;
            case 't':   T = idx(new(readTerm(argv[i++]), T));
                        break;
            case 's':   if ((in = fopen(argv[i++], "r"))==NULL) {
                            error("unknown file %s",argv[i++]);
                        };
                        fseek(in,0,SEEK_END);
                        fln=ftell(in);
                        V = idx(new(FSYMeos,0));
                        for(fi=1;fi<=fln;fi++) {
                            fseek(in,-fi,SEEK_END);
                            c = fgetc(in);
                            V = idx(new(V,0));
                            V = idx(new(idx(new((c<<2)|1,0)),V));
                            V = idx(new(FSYMstr,V));
                        }
                        fclose(in);
                        T = idx(new(V, T));
                        break;
            case 'b':
            case 'm':   error("not yet implemented");
            case 'I':   pprg(P);
                        printf("\n");
                        break;
            case 'i':   if (Dbg>=DIO) flats=1;
                        ptrm(T);
                        printf("\n");
                        flats=0;
                        break;
            case 'r':   if (Dbg>=DIO) printf("\n### Start ###\n");
                        X = reduce(); //uses T
	                    if (Dbg>=DIO) printf("### Done! ###\n");
                        break;
            case 'O':   if (Dbg>=DIO) flats=1;
                        ptrm(idx(X));
                        printf("\n");
                        flats=0;
                        break;
            default:    error("No such option: %c. Use %s for help.",argv[i-1][1],argv[0]);
        }
    }
}
