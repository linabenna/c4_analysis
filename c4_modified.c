// c4.c - C in four functions

// char, int, and pointer types
// if, while, return, and expression statements
// just enough features to allow self-compilation and a bit more

// Written by Robert Swierczek

#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include <unistd.h>
#include <fcntl.h>
#define int long long

char *p, *lp, // current position in source code
     *data;   // data/bss pointer

int *e, *le,  // current position in emitted code
    *id,      // currently parsed identifier
    *sym,     // symbol table (simple list of identifiers)
    tk,       // current token
    ival,     // current token value
    ty,       // current expression type
    loc,      // local variable offset
    line,     // current line number
    src,      // print source and assembly flag
    debug;    // print executed instructions

// tokens and classes (operators last and in precedence order)
enum {
  Num = 128, Fun, Sys, Glo, Loc, Id,
  Char, Else, Enum, If, Int, Return, Sizeof, While, Do,
  Assign, Cond, Lor, Lan, Or, Xor, And, Eq, Ne, Lt, Gt, Le, Ge, Shl, Shr, Add, Sub, Mul, Div, Mod, Inc, Dec, Brak
};

// opcodes
enum { LEA ,IMM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,
       OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,
       OPEN,READ,CLOS,PRTF,MALC,FREE,MSET,MCMP,EXIT };

// types
enum { CHAR, INT, PTR };

// identifier offsets (since we can't create an ident struct)
enum { Tk, Hash, Name, Class, Type, Val, HClass, HType, HVal, Idsz };

/*
  next()

  This function reads characters from the source code and identifies tokens 
  keywords, identifiers, numbers, operators, etc.)

  This is a fundamental step in compiling, converting the source code into manageable 
  tokens that can be parsed and compiled.

*/ 

void next()
{
  char *pp;

  while (tk = *p) { // loop through each character in the source code
    ++p;
    if (tk == '\n') {  // if the character is a newline
      if (src) { // if debugging then print the source code
        printf("%d: %.*s", line, p - lp, lp); // print the current line
        lp = p;
        while (le < e) { // print the emitted code
          printf("%8.4s", &"LEA ,IMM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,"
                           "OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,"
                           "OPEN,READ,CLOS,PRTF,MALC,FREE,MSET,MCMP,EXIT,"[*++le * 5]);
          if (*le <= ADJ) printf(" %d\n", *++le); else printf("\n");
        }
      }
      ++line; // increment the line number
    }
    else if (tk == '#') { // if the character is a #
      while (*p != 0 && *p != '\n') ++p; // skip till the end
    }
    else if ((tk >= 'a' && tk <= 'z') || (tk >= 'A' && tk <= 'Z') || tk == '_') { // if the character is a letter or underscore
      pp = p - 1; // store the start of identifier
      while ((*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') || (*p >= '0' && *p <= '9') || *p == '_')
        tk = tk * 147 + *p++; // compute the hash value of the identifier
      tk = (tk << 6) + (p - pp);
      id = sym;
      while (id[Tk]) { // check if the identifier is already in the symbol table
        if (tk == id[Hash] && !memcmp((char *)id[Name], pp, p - pp)) { tk = id[Tk]; return; }
        id = id + Idsz;
      }
      id[Name] = (int)pp; // add the identifier to the symbol table
      id[Hash] = tk; // save the hash of the identifier
      tk = id[Tk] = Id;
      return;
    }
    else if (tk >= '0' && tk <= '9') { // if the character is a digit
      if (ival = tk - '0') { while (*p >= '0' && *p <= '9') ival = ival * 10 + *p++ - '0'; }
      else if (*p == 'x' || *p == 'X') { // if the current token is an x or X
        while ((tk = *++p) && ((tk >= '0' && tk <= '9') || (tk >= 'a' && tk <= 'f') || (tk >= 'A' && tk <= 'F')))
          ival = ival * 16 + (tk & 15) + (tk >= 'A' ? 9 : 0); // convert the hexadecimal into an integer
      }
      else { while (*p >= '0' && *p <= '7') ival = ival * 8 + *p++ - '0'; }
      tk = Num; // token is a number
      return;
    }
    else if (tk == '/') { // if the character is a slash
      if (*p == '/') { // if it's a comment
        ++p;
        while (*p != 0 && *p != '\n') ++p; // skip the comment
      }
      else {
        tk = Div; // it's a division operator
        return;
      }
    }
    else if (tk == '\'' || tk == '"') { // if the character is a quote
      pp = data;
      while (*p != 0 && *p != tk) { // loop through the full quote
        if ((ival = *p++) == '\\') { // look for a '\'
          if ((ival = *p++) == 'n') ival = '\n'; // if n follows the '\', then its a new line
        }
        if (tk == '"') *data++ = ival; // when its a string, store it in data
      }
      ++p;
      if (tk == '"') ival = (int)pp; else tk = Num;
      return;
    }
    // the code below continues to evaluate each token in the source code
    else if (tk == '=') { if (*p == '=') { ++p; tk = Eq; } else tk = Assign; return; }
    else if (tk == '+') { if (*p == '+') { ++p; tk = Inc; } else tk = Add; return; }
    else if (tk == '-') { if (*p == '-') { ++p; tk = Dec; } else tk = Sub; return; }
    else if (tk == '!') { if (*p == '=') { ++p; tk = Ne; } return; }
    else if (tk == '<') { if (*p == '=') { ++p; tk = Le; } else if (*p == '<') { ++p; tk = Shl; } else tk = Lt; return; }
    else if (tk == '>') { if (*p == '=') { ++p; tk = Ge; } else if (*p == '>') { ++p; tk = Shr; } else tk = Gt; return; }
    else if (tk == '|') { if (*p == '|') { ++p; tk = Lor; } else tk = Or; return; }
    else if (tk == '&') { if (*p == '&') { ++p; tk = Lan; } else tk = And; return; }
    else if (tk == '^') { tk = Xor; return; }
    else if (tk == '%') { tk = Mod; return; }
    else if (tk == '*') { tk = Mul; return; }
    else if (tk == '[') { tk = Brak; return; }
    else if (tk == '?') { tk = Cond; return; }
    else if (tk == '~' || tk == ';' || tk == '{' || tk == '}' || tk == '(' || tk == ')' || tk == ']' || tk == ',' || tk == ':') return;
  }
}

/*

  Function: expr(int lev)

  This function handles various types of expressions, including numbers, strings, 
  identifiers, unary and binary operators, and more.

  The function uses a technique called "precedence climbing" 
  to ensure operators are evaluated in the correct order.

*/

void expr(int lev)
{
  int t, *d; // t, an int variable and *d, a pointer to an int variable.

  // this block checks if tk (a token) is not present. If it's not, it prints an error message and exits the program
  if (!tk) { printf("%d: unexpected eof in expression\n", line); exit(-1); } // error if end of file
  else if (tk == Num) { // if the token is a number
    *++e = IMM; // store it in the expression array (e)
    *++e = ival; // advance to the next token
    next(); ty = INT; // set the type (ty) to integer (INT)
  } 
  else if (tk == '"') { // if the token is a string (")
    *++e = IMM; *++e = ival; next(); // store the string in the expression array
    while (tk == '"') next(); // go to next token
    data = (char *)((int)data + sizeof(int) & -sizeof(int)); ty = PTR;
  }
  else if (tk == Sizeof) { // handles sizeof operator which returns the size of a data type
    next(); 
    if (tk == '(') next(); // ensure '(' follows 'sizeof' otherwise exit
    else { printf("%d: open paren expected in sizeof\n", line); exit(-1); } 
    ty = INT; // default type is int
    
    if (tk == Int) next(); // check if the token is 'int' or 'char' and set the type accordingly
    else if (tk == Char) { next(); ty = CHAR; }

    // handle pointer types by counting '*' and adjusting the type
    while (tk == Mul) { next(); ty = ty + PTR; }

    if (tk == ')') next(); // ensure closing ')'
    else { printf("%d: close paren expected in sizeof\n", line); exit(-1); }

    // generate the appropriate instruction to push the size onto the evaluation stack
    *++e = IMM; 
    *++e = (ty == CHAR) ? sizeof(char) : sizeof(int); // push size of char or int

    ty = INT; // reset type to int
  }

  /* 
    This block handles identifiers (variables or function names). 
    It checks if the identifier is a function call, a number, or a variable,
    and processes it accordingly.
  */

  else if (tk == Id) { // handle identifier (either variable or function)
    d = id; next();

    if (tk == '(') { // if followed by '(', it's a function call
      next();
      t = 0;

      // parse function arguments
      while (tk != ')') { 
        expr(Assign); // evaluate argument expression
        *++e = PSH;  // push argument onto the stack
        ++t;
        if (tk == ',') next();  // handle multiple arguments
      }
      next();

      // check if identifier is a system function or user-defined function
      if (d[Class] == Sys) *++e = d[Val]; // system function call
      else if (d[Class] == Fun) { 
        *++e = JSR; // call user-defined function
        *++e = d[Val]; 
      }
      else { printf("%d: bad function call\n", line); exit(-1); }
      if (t) { *++e = ADJ; *++e = t; } // adjust the stack pointer after function call
      ty = d[Type]; // set the return type of the function
    }

    else if (d[Class] == Num) { *++e = IMM; *++e = d[Val]; ty = INT; } // handling numeric constant
    else { // handling variables
      if (d[Class] == Loc) { *++e = LEA; *++e = loc - d[Val]; } // Local variable
      else if (d[Class] == Glo) { *++e = IMM; *++e = d[Val]; } // Global variable
      else { printf("%d: undefined variable\n", line); exit(-1); }
      *++e = ((ty = d[Type]) == CHAR) ? LC : LI; // load variable value based on type
    }
  }
  else if (tk == '(') { // handles expressions within parentheses
    next();
    if (tk == Int || tk == Char) { // checks for type casts and processes the expression inside the parentheses.
      t = (tk == Int) ? INT : CHAR; next();
      while (tk == Mul) { next(); t = t + PTR; } // handles pointer types in cast
      if (tk == ')') next(); else { printf("%d: bad cast\n", line); exit(-1); }
      expr(Inc);
      ty = t;
    }
    else { // handle normal expressions inside parentheses
      expr(Assign);
      if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    }
  }
  else if (tk == Mul) { // handles dereferencing pointers (using `*`). 
    next(); expr(Inc); // evaluate the expression
    if (ty > INT) ty = ty - PTR; // adjust type (dereferencing reduces pointer level)
    else { printf("%d: bad dereference\n", line); exit(-1); }
    *++e = (ty == CHAR) ? LC : LI;
  }
  else if (tk == And) { // handle address-of (&)
    next(); expr(Inc); // evaluate the expression
    if (*e == LC || *e == LI) --e; // remove load instruction, keep address
    else { printf("%d: bad address-of\n", line); exit(-1); }
    ty = ty + PTR; // convert type to pointer
  }

  // These lines handle various unary operators like !, ~, +, -, ++, and --. 
  // They process the expression and adjust the type accordingly.

  else if (tk == '!') { next(); expr(Inc); *++e = PSH; *++e = IMM; *++e = 0; *++e = EQ; ty = INT; } // pushes 0 onto the stack and checks if the expression is equal to 0
  else if (tk == '~') { next(); expr(Inc); *++e = PSH; *++e = IMM; *++e = -1; *++e = XOR; ty = INT; } // XORing all bits with -1
  else if (tk == Add) { next(); expr(Inc); ty = INT; } // evaluates the expression (has no real effect)
  else if (tk == Sub) { // handle unary minus- negates the value of the expression
    next(); *++e = IMM;
    // if a number follows '-', negate it directly
    if (tk == Num) { *++e = -ival; next(); } 
    // otherwise, multiply by -1 to negate the result of the expression
    else { *++e = -1; *++e = PSH; expr(Inc); *++e = MUL; }
    ty = INT;
  }
  else if (tk == Inc || tk == Dec) { // handle pre-increment and pre-decrement
    t = tk; next(); expr(Inc);
    if (*e == LC) { *e = PSH; *++e = LC; }
    else if (*e == LI) { *e = PSH; *++e = LI; }
    else { printf("%d: bad lvalue in pre-increment\n", line); exit(-1); }
    // push the value onto the stack, then adjust it by 1 (or size of type if a pointer)
    *++e = PSH;
    *++e = IMM; *++e = (ty > PTR) ? sizeof(int) : sizeof(char);
    *++e = (t == Inc) ? ADD : SUB; // increase or decrease the value
    *++e = (ty == CHAR) ? SC : SI; // store back in memory
  }
  else { printf("%d: bad expression\n", line); exit(-1); } // Error for bad expression

  // This loop handles operators based on their precedence. 
  // It ensures that operators with higher precedence are evaluated before those with lower precedence.

  while (tk >= lev) { // "precedence climbing" or "Top Down Operator Precedence" method
    t = ty;
    if (tk == Assign) { // handle assignment (=)
      next();
      if (*e == LC || *e == LI) *e = PSH; // ensure it's a valid variable
      else { printf("%d: bad lvalue in assignment\n", line); exit(-1); }

      expr(Assign); 
      *++e = ((ty = t) == CHAR) ? SC : SI; // store the assigned value
    }
    else if (tk == Cond) { // handle conditional operator (?:) - condition ? expr1 : expr2
      next();
      *++e = BZ; d = ++e; // jump if false
      expr(Assign);
      if (tk == ':') next(); else { printf("%d: conditional missing colon\n", line); exit(-1); }
      *d = (int)(e + 3); *++e = JMP; d = ++e;
      expr(Cond);
      *d = (int)(e + 1);
    }
    else if (tk == Lor) { next(); *++e = BNZ; d = ++e; expr(Lan); *d = (int)(e + 1); ty = INT; } // logical OR (||)
    else if (tk == Lan) { next(); *++e = BZ;  d = ++e; expr(Or);  *d = (int)(e + 1); ty = INT; } 
    else if (tk == Or)  { next(); *++e = PSH; expr(Xor); *++e = OR;  ty = INT; } 
    else if (tk == Xor) { next(); *++e = PSH; expr(And); *++e = XOR; ty = INT; }
    else if (tk == And) { next(); *++e = PSH; expr(Eq);  *++e = AND; ty = INT; }
    else if (tk == Eq)  { next(); *++e = PSH; expr(Lt);  *++e = EQ;  ty = INT; }
    else if (tk == Ne)  { next(); *++e = PSH; expr(Lt);  *++e = NE;  ty = INT; }
    else if (tk == Lt)  { next(); *++e = PSH; expr(Shl); *++e = LT;  ty = INT; }
    else if (tk == Gt)  { next(); *++e = PSH; expr(Shl); *++e = GT;  ty = INT; }
    else if (tk == Le)  { next(); *++e = PSH; expr(Shl); *++e = LE;  ty = INT; }
    else if (tk == Ge)  { next(); *++e = PSH; expr(Shl); *++e = GE;  ty = INT; }
    else if (tk == Shl) { next(); *++e = PSH; expr(Add); *++e = SHL; ty = INT; }
    else if (tk == Shr) { next(); *++e = PSH; expr(Add); *++e = SHR; ty = INT; }
    else if (tk == Add) { // addition (+)
      next(); *++e = PSH; expr(Mul);
      if ((ty = t) > PTR) { *++e = PSH; *++e = IMM; *++e = sizeof(int); *++e = MUL;  }
      *++e = ADD;
    }
    else if (tk == Sub) { // subtraction (-)
      next(); *++e = PSH; expr(Mul);
      if (t > PTR && t == ty) { *++e = SUB; *++e = PSH; *++e = IMM; *++e = sizeof(int); *++e = DIV; ty = INT; }
      else if ((ty = t) > PTR) { *++e = PSH; *++e = IMM; *++e = sizeof(int); *++e = MUL; *++e = SUB; }
      else *++e = SUB;
    }
    else if (tk == Mul) { next(); *++e = PSH; expr(Inc); *++e = MUL; ty = INT; }
    else if (tk == Div) { next(); *++e = PSH; expr(Inc); *++e = DIV; ty = INT; }
    else if (tk == Mod) { next(); *++e = PSH; expr(Inc); *++e = MOD; ty = INT; }

    else if (tk == Inc || tk == Dec) { // handles post-increment and post-decrement
      if (*e == LC) { *e = PSH; *++e = LC; }
      else if (*e == LI) { *e = PSH; *++e = LI; }
      else { printf("%d: bad lvalue in post-increment\n", line); exit(-1); }
      *++e = PSH; *++e = IMM; *++e = (ty > PTR) ? sizeof(int) : sizeof(char);
      *++e = (tk == Inc) ? ADD : SUB;
      *++e = (ty == CHAR) ? SC : SI;
      *++e = PSH; *++e = IMM; *++e = (ty > PTR) ? sizeof(int) : sizeof(char);
      *++e = (tk == Inc) ? SUB : ADD;
      next();
    }
    else if (tk == Brak) { // handles array indexing
      next(); *++e = PSH; expr(Assign);
      if (tk == ']') next(); else { printf("%d: close bracket expected\n", line); exit(-1); }
      if (t > PTR) { *++e = PSH; *++e = IMM; *++e = sizeof(int); *++e = MUL;  }
      else if (t < PTR) { printf("%d: pointer type expected\n", line); exit(-1); }
      *++e = ADD;
      *++e = ((ty = t - PTR) == CHAR) ? LC : LI;
    }
    else { printf("%d: compiler error tk=%d\n", line, tk); exit(-1); } // error for unknown token
  }
}

/*

  Function: stmt()

  This function parses different types of statements, including if, 
  while, return, block, and expression statements.

  It uses a recursive descent parsing technique to handle different types of statements.

  Required to generate the correct machine code for statements in the source code.

*/

void stmt()
{
  int *a, *b; // these pointers are used for jump addresses in control flow structures

  if (tk == If) { // handles 'if' statements
    next();
    if (tk == '(') next(); else { printf("%d: open paren expected\n", line); exit(-1); }
    expr(Assign);// evaluates the condition inside the if-statement
    if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }

    *++e = BZ;  // branch if zero (condition is false)
    b = ++e; // store jump address for the 'else' part
    stmt(); // process the 'then' block

    if (tk == Else) { // if there's an 'else' block, handle it
      *b = (int)(e + 3); 
      *++e = JMP; // jump over the 'else' block if 'if' was true
      b = ++e; 
      next();
      stmt(); // process the 'else' block
    }
    *b = (int)(e + 1);
  }
  else if (tk == While) { // handles 'while' loops
    next();
    a = e + 1; // store loop start address

    if (tk == '(') next(); else { printf("%d: open paren expected\n", line); exit(-1); }
    expr(Assign); // evaluate the loop condition
    if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }
    *++e = BZ; // if condition is false, exit loop
    b = ++e; // store address to jump past loop
    stmt(); // process loop body
    *++e = JMP; 
    *++e = (int)a;// jump back to loop start
    *b = (int)(e + 1); // exit after loop
  }

  else if (tk == Do) { // handles 'do-while' loops
    next();
    a = e + 1; // store address for the start of the loop

    stmt(); // execute loop body

    if (tk == While) { // check for 'while' after the loop body
      next();
      if (tk == '(') next(); else { printf("%d: open paren expected\n", line); exit(-1); }
      expr(Assign); // evaluate the loop condition
      if (tk == ')') next(); else { printf("%d: close paren expected\n", line); exit(-1); }

      *++e = BZ; // if condition is false, exit loop
      b = ++e; // store address to jump past loop
      *++e = JMP; // jump back to the loop start
      *++e = (int)a; // jump to loop start
      *b = (int)(e + 1); // exit after loop
    } else {
      printf("%d: while expected after do\n", line); 
      exit(-1);
    }
  }

  else if (tk == Return) { // handles 'return' statements
    next();
    if (tk != ';') expr(Assign); // evaluate return value (if any)
    *++e = LEV; // return from function
    if (tk == ';') next(); else { printf("%d: semicolon expected\n", line); exit(-1); }
  }
  else if (tk == '{') { // handles blocks (multiple statements inside curly braces)
    next();
    while (tk != '}') stmt(); // process all statements inside the block
    next(); // move past closing '}'
  }
  else if (tk == ';') { // empty statement (e.g., just a semicolon)
    next();
  }
  else { // default case: process an expression as a statement
    expr(Assign); // evaluate the expression
    if (tk == ';') next(); else { printf("%d: semicolon expected\n", line); exit(-1); }
  }
}

int main(int argc, char **argv)
{
  int fd, bt, ty, poolsz, *idmain;
  int *pc, *sp, *bp, a, cycle; // vm registers
  int i, *t; // temps

  // parse command line arguments
  --argc; ++argv;
  if (argc > 0 && **argv == '-' && (*argv)[1] == 's') { src = 1; --argc; ++argv; } // enable source mode
  if (argc > 0 && **argv == '-' && (*argv)[1] == 'd') { debug = 1; --argc; ++argv; } // enable debug mode
  if (argc < 1) { printf("usage: c4 [-s] [-d] file ...\n"); return -1; } // ensure a file is provided

  // open source file
  if ((fd = open(*argv, 0)) < 0) { printf("could not open(%s)\n", *argv); return -1; }

  // allocate memory for symbol table, code section, data section, and stack
  poolsz = 256*1024; // arbitrary size
  if (!(sym = malloc(poolsz))) { printf("could not malloc(%d) symbol area\n", poolsz); return -1; }
  if (!(le = e = malloc(poolsz))) { printf("could not malloc(%d) text area\n", poolsz); return -1; }
  if (!(data = malloc(poolsz))) { printf("could not malloc(%d) data area\n", poolsz); return -1; }
  if (!(sp = malloc(poolsz))) { printf("could not malloc(%d) stack area\n", poolsz); return -1; }

  // initialize allocated memory
  memset(sym,  0, poolsz);
  memset(e,    0, poolsz);
  memset(data, 0, poolsz);

  // initialize keywords and library functions
  p = "char else enum if int return sizeof while "
      "open read close printf malloc free memset memcmp exit void main";
  i = Char; while (i <= While) { next(); id[Tk] = i++; } // add keywords to symbol table - assigns tokens to keywords
  i = OPEN; while (i <= EXIT) { next(); id[Class] = Sys; id[Type] = INT; id[Val] = i++; } // add library to symbol table - assigns tokens to system functions
  next(); id[Tk] = Char; // handle void type
  next(); idmain = id; // keep track of main

  // read source file into memory
  if (!(lp = p = malloc(poolsz))) { printf("could not malloc(%d) source area\n", poolsz); return -1; }
  if ((i = read(fd, p, poolsz-1)) <= 0) { printf("read() returned %d\n", i); return -1; } // read file content
  p[i] = 0; // null terminate source file content
  close(fd); // close source file

  // parse declarations and definitions
  line = 1;
  next();
  while (tk) { // loop through tokens
    bt = INT; // default basetype is int
    if (tk == Int) next(); // check for int keyword
    else if (tk == Char) { next(); bt = CHAR; } // check for char keyword
    else if (tk == Enum) {  // handle enum type
      next();
      if (tk != '{') next(); // if not immediately an enum block, move forward
      if (tk == '{') {
        next(); // move to first enum identifier
        i = 0;// initialize enum value
        while (tk != '}') { // process enum elements
          if (tk != Id) { printf("%d: bad enum identifier %d\n", line, tk); return -1; }
          next();
          if (tk == Assign) { // handle assigned values in enum
            next();
            if (tk != Num) { printf("%d: bad enum initializer\n", line); return -1; } // ensure valid number
            i = ival; // set enum value
            next();
          }
          id[Class] = Num; id[Type] = INT; id[Val] = i++; // store enum properties
          if (tk == ',') next(); // move to next enum entry if comma is present
        }
        next(); // move past closing brace
      }
    }
    while (tk != ';' && tk != '}') { // parse global variables and function definitions
      ty = bt; // set type to base type
      while (tk == Mul) { next(); ty = ty + PTR; } // handle pointer type
      if (tk != Id) { printf("%d: bad global declaration\n", line); return -1; }
      if (id[Class]) { printf("%d: duplicate global definition\n", line); return -1; } // check for duplicate definition
      next();
      id[Type] = ty;// store type information

      if (tk == '(') { // function definition
        id[Class] = Fun;
        id[Val] = (int)(e + 1);
        next(); i = 0;
        while (tk != ')') { // parse function parameters
          ty = INT;
          if (tk == Int) next();
          else if (tk == Char) { next(); ty = CHAR; }
          while (tk == Mul) { next(); ty = ty + PTR; } // handle pointer parameters
          if (tk != Id) { printf("%d: bad parameter declaration\n", line); return -1; } // ensure valid parameter name
          if (id[Class] == Loc) { printf("%d: duplicate parameter definition\n", line); return -1; } // check duplicate params
          id[HClass] = id[Class]; id[Class] = Loc; // store class
          id[HType]  = id[Type];  id[Type] = ty; // store type
          id[HVal]   = id[Val];   id[Val] = i++; // store value
          next();
          if (tk == ',') next();
        }
        next();
        if (tk != '{') { printf("%d: bad function definition\n", line); return -1; } // check function block
        loc = ++i;
        next();
        while (tk == Int || tk == Char) { // parse local variables
          bt = (tk == Int) ? INT : CHAR;
          next();
          while (tk != ';') {
            ty = bt;
            while (tk == Mul) { next(); ty = ty + PTR; } // handle pointers
            if (tk != Id) { printf("%d: bad local declaration\n", line); return -1; }
            if (id[Class] == Loc) { printf("%d: duplicate local definition\n", line); return -1; }
            id[HClass] = id[Class]; id[Class] = Loc;
            id[HType]  = id[Type];  id[Type] = ty;
            id[HVal]   = id[Val];   id[Val] = ++i;
            next();
            if (tk == ',') next();
          }
          next();
        }
        *++e = ENT; *++e = i - loc;
        while (tk != '}') stmt();
        *++e = LEV;
        id = sym; // unwind symbol table locals
        while (id[Tk]) {
          if (id[Class] == Loc) {
            id[Class] = id[HClass];
            id[Type] = id[HType];
            id[Val] = id[HVal];
          }
          id = id + Idsz;
        }
      }
      else { // global variable
        id[Class] = Glo;
        id[Val] = (int)data;
        data = data + sizeof(int);
      }
      if (tk == ',') next();
    }
    next();
  }

  if (!(pc = (int *)idmain[Val])) { printf("main() not defined\n"); return -1; }
  if (src) return 0;

  // setup stack and execute
  bp = sp = (int *)((int)sp + poolsz);
  *--sp = EXIT; // call exit if main returns
  *--sp = PSH; t = sp;
  *--sp = argc;
  *--sp = (int)argv;
  *--sp = (int)t;

  // run... main execution loop
  cycle = 0;
  while (1) {
    i = *pc++; ++cycle;
    if (debug) {
      printf("%d> %.4s", cycle,
        &"LEA ,IMM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,"
         "OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,"
         "OPEN,READ,CLOS,PRTF,MALC,FREE,MSET,MCMP,EXIT,"[i * 5]);
      if (i <= ADJ) printf(" %d\n", *pc); else printf("\n");
    }
    if      (i == LEA) a = (int)(bp + *pc++);                             // load local address
    else if (i == IMM) a = *pc++;                                         // load global address or immediate
    else if (i == JMP) pc = (int *)*pc;                                   // jump
    else if (i == JSR) { *--sp = (int)(pc + 1); pc = (int *)*pc; }        // jump to subroutine
    else if (i == BZ)  pc = a ? pc + 1 : (int *)*pc;                      // branch if zero
    else if (i == BNZ) pc = a ? (int *)*pc : pc + 1;                      // branch if not zero
    else if (i == ENT) { *--sp = (int)bp; bp = sp; sp = sp - *pc++; }     // enter subroutine
    else if (i == ADJ) sp = sp + *pc++;                                   // stack adjust
    else if (i == LEV) { sp = bp; bp = (int *)*sp++; pc = (int *)*sp++; } // leave subroutine
    else if (i == LI)  a = *(int *)a;                                     // load int
    else if (i == LC)  a = *(char *)a;                                    // load char
    else if (i == SI)  *(int *)*sp++ = a;                                 // store int
    else if (i == SC)  a = *(char *)*sp++ = a;                            // store char
    else if (i == PSH) *--sp = a;                                         // push

    else if (i == OR)  a = *sp++ |  a;
    else if (i == XOR) a = *sp++ ^  a;
    else if (i == AND) a = *sp++ &  a;
    else if (i == EQ)  a = *sp++ == a;
    else if (i == NE)  a = *sp++ != a;
    else if (i == LT)  a = *sp++ <  a;
    else if (i == GT)  a = *sp++ >  a;
    else if (i == LE)  a = *sp++ <= a;
    else if (i == GE)  a = *sp++ >= a;
    else if (i == SHL) a = *sp++ << a;
    else if (i == SHR) a = *sp++ >> a;
    else if (i == ADD) a = *sp++ +  a;
    else if (i == SUB) a = *sp++ -  a;
    else if (i == MUL) a = *sp++ *  a;
    else if (i == DIV) a = *sp++ /  a;
    else if (i == MOD) a = *sp++ %  a;

    else if (i == OPEN) a = open((char *)sp[1], *sp);
    else if (i == READ) a = read(sp[2], (char *)sp[1], *sp);
    else if (i == CLOS) a = close(*sp);
    else if (i == PRTF) { t = sp + pc[1]; a = printf((char *)t[-1], t[-2], t[-3], t[-4], t[-5], t[-6]); }
    else if (i == MALC) a = (int)malloc(*sp);
    else if (i == FREE) free((void *)*sp);
    else if (i == MSET) a = (int)memset((char *)sp[2], sp[1], *sp);
    else if (i == MCMP) a = memcmp((char *)sp[2], (char *)sp[1], *sp);
    else if (i == EXIT) { printf("exit(%d) cycle = %d\n", *sp, cycle); return *sp; }
    else { printf("unknown instruction = %d! cycle = %d\n", i, cycle); return -1; }
  }
}
