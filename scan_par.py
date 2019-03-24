## Eduardo Benitez
## Armando Aguiar

import ply.lex as lex
import ply.yacc as yacc
import sys

# Inicialización de variables, diccionarios, listas.
aprobado = true;
dir_func = {}
pOper = []
pType = []
pilaO = []
quad = []
count = 0

# Scope global
actual_scope = 'global'

# Directorio de funciones vacio
dir_func[actual_scope] = { 'type' : 'VOID', 'scope' : {}, 'numParams' : 0}

# Declaración del cubo semántico


######## Scanner ##########

literals = "{}()<>=;:,+-*/%&|^"

reserved = {

 'PROGRAM' : 'PROGRAM',
 'FUNCTION': 'FUNCTION',
 'RETURN'  : 'RETURN',
 'MAIN'    : 'MAIN',


 'calculaRegresion' : 'calculaRegresion',
 'prediceResultado' : 'prediceResultado',
 'calculaModa'      : 'calculaModa',
 'calculaMediana'   : 'calculaMediana',
 'calculaMedia'     : 'calculaMedia',
 'calculaPoisson'   : 'calculaPoisson',
 'calculaBinomial'  : 'calculaBinomial',
 'calculaNormal'    : 'calculaNormal',
 

 'IF'      : 'IF',
 'ELSE'    : 'ELSE',
 'PRINT'   : 'PRINT',
 'READ'    : 'READ',
 'VAR'     : 'VAR',
 'REPEAT'  : 'REPEAT',
 'TRUE'    : 'true',
 'FALSE'   : 'FALSE',
 'INT'     : 'INT',
 'FLOAT'   : 'FLOAT',
 'BOOL'    : 'BOOL',
 'STRING'  : 'STRING',
 'AND'     : 'AND',
 'OR'      : 'OR',
 'NOT'     : 'NOT',

}

tokens = [  
        #Operadores Relacionales
        "LE",
        "GE",
        "EQ",
        "NEQ",

        #Caracteres especiales
        "ARR",

        #Otros
        "ID",  
        "CTEI",
        "CTEF",
        "CTES",

    ] + list(reserved.values())
         
t_ignore = ' \t\f'

t_LE = r"<="
t_GE = r">="
t_EQ = r"=="
t_NEQ = r"/="
t_ARR = r"->"

def t_ID(t):
    r"[a-zA-Z_]\w*"
    t.type = reserved.get(t.value, 'ID')
    return t

def t_CTEF(t):
    r"\d+\.\d+"
    return t

def t_CTEI(t):
    r"\d+"
    return t

def t_CTES(t):
    r'\"([^\\\n]|(\\.))*?\"'
    return t

def t_error(t):
    global aprobado
    aprobado = FALSE
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)    

#Construye Lexer
lexer = lex.lex()


## Code to display all found tokens ######
# lexer.input("<=")

# print("List of Tokens: ")
# while True:
#    tok = lexer.token()
#    if not tok:
#        break
#    print(tok)

##################################################################################################################################
########## Parser ##########

def p_empty(p):
    '''empty : '''
    pass

def p_programa(p):
    '''programa : PROGRAM '{' more_vars more_funcs main '}' '''

def p_more_vars(p):
    '''more_vars : vars 
                 | vars more_vars
                 | empty '''

def p_more_funcs(p):
    '''more_funcs : func
                  | func more_funcs
                  | empty '''

def p_main(p):
    '''main : MAIN '{' more_vars more_bloques '}' '''

def p_more_bloques(p):
    '''more_bloques : bloque
                    | bloque more_bloques 
                    | empty '''

def p_vars(p):
    '''vars : VAR ids '''

def p_ids(p):
    '''ids : type ID arr_mat  '''

def p_arr_mat(p):
    '''arr_mat : '[' CTE_I ']'
               | '[' CTE_I ']' '[' CTE_I ']'
               | empty '''

def p_type(p):
    '''type : INT
            | FLOAT
            | BOOL
            | STRING '''

def p_func(p):
    '''func : FUNCTION func_type ID '(' more_ids ')' '{' more_vars more_bloques '}' '''

def p_more_ids(p):
    '''more_ids : ids 
                | ids more_ids
                | empty '''

def p_func_type(p):
    '''func_type : type
                 | VOID '''

def p_bloque(p):
    '''bloque : assignation
              | loop
              | cond
              | return
              | lecture
              | writing
              | call 
              | func_pred '''

def p_assignation(p):
    '''assignation : ID other_arr_mat '=' mega_exp '''

def p_other_arr_mat(p):
    '''other_arr_mat : '[' exp ']'
                     | '[' exp ']' '[' exp ']'
                     | empty '''
   
def p_loop(p):
    '''loop : REPEAT '(' exp ')' '{' more_bloques '}' '''

def p_cond(p):
    '''cond : IF '(' mega_exp ')' '{' more_bloques '}'
            | IF '(' mega_exp ')' '{' more_bloques '}' ELSE '{' more_bloques '}' '''

def p_return(p):
    '''return : RETURN exp '''

def p_lecture(p):
    '''lecture : READ ARR ID arr_mat '''

def p_writing(p):
    '''writing : PRINT '(' mega_exp ')' '''

def p_call(p):
    '''call : ID '(' exp ')' '''

def p_func_pred(p):
    '''func_pred : calculaRegresion '(' exp ')'
                 | prediceResultado '(' exp ')'
                 | calculaModa '(' exp ')'
                 | calculaMediana '(' exp ')'
                 | calculaMedia '(' exp ')' 
                 | calculaPoisson '(' exp ')'
                 | calculaBinomial '(' exp ')'
                 | calculaNormal '(' exp ')' '''

def p_mega_exp(p):
    '''mega_exp : opt_not super_exp
                | opt_not super_exp log_op mega_exp '''

def p_log_op(p):
    '''log_op : AND
              | OR
              | NOT '''

def p_opt_not(p):
    '''opt_not : NOT
               | empty '''

def p_super_exp(p):
    '''super_exp : exp 
                 | exp rel_op super_exp '''

def p_rel_op(p):
    '''rel_op : LE
              | GE
              | EQ
              | NEQ '''

def p_exp(p):
    '''exp : termino
           | termino '+' exp
           | termino '-' exp '''

def p_termino(p):
    '''termino : factor
               | factor '*' termino
               | factor '/' termino '''

def p_factor(p): 
    '''factor : '(' super_exp ')'
              | '+' var_cte
              | '-' var_cte
              | var_cte '''

def p_var_cte(p):
    '''var_cte : other
               | CTE_I
               | CTE_F
               | CTE_S
               | TRUE
               | FALSE '''

def p_other(p):
    '''other : ID other_arr_mat
             | call
             | empty '''



###############################################################################

########## Test ##########
# fName = input("Which file do you want to use? (correct.txt / incorrect.txt): ")

# with open(fName, 'r') as myfile:
#     s=myfile.read().replace('\n', '')

# Construye Parser
parser = yacc.yacc()

parser.parse(s)

if aprobado == True:
    print("Archivo aprobado")
    sys.exit()
else: 
    print("Archivo no aprobado")
    sys.exit()