## Eduardo Benitez
## Armando Aguiar

import ply.lex as lex
import ply.yacc as yacc
import sys

# Inicialización de variables, diccionarios, listas.
aprobado = True
dir_func = {}
pOper = []
pType = []
pilaO = []
quad = []
pJumps = []
pIterator = []
pReturnTo = []
pFunc = []
pVar = []
pArr =[]
contQuads = 0
contParam = 0
funcToCall = ''
currentQuad = 0

# Scope global
actual_scope = 'global'

# Directorio de funciones vacio
dir_func[actual_scope] = { 'type' : 'VOID', 'scope' : {}, 'numParams' : 0}

# Agrega al diccionario de cuadruplos el cuadruplo que recibe
def add_quad(operator,leftOperand,rightOperand,result):
  quad.append({'operator':operator,'leftOperand':leftOperand,'rightOperand':rightOperand,'result':result})
  global contQuads
  contQuads = contQuads + 1

add_quad('GOTO', '','','')

# Actualiza las casillas que se agregan en blanco a la lista de cuadruplos
def updateQuad(i, llave, val):
  (quad[i])[llave] = val


# Validación de semántica
def semantic_check(l_OP_type,R_OP_type,oper):
    if L_OP_type in sem_cube:
        if R_OP_type in sem_cube[L_OP_type]:
            if oper in sem_cube[L_OP_type][R_OP_type]:
                return sem_cube[L_OP_type][R_OP_type][oper]
    return 'error'

# Funcion auxiliar que revisa si lo que se recibe es un numero
def is_number(s):
    try:
        float(s)
        return True
    except ValueError:
        return False


# Declaración del cubo semántico
cubo_semantico = {'INT' :   { 'INT' : { '+': 'INT',
                                    '-': 'INT',
                                    '/': 'FLOAT',
                                    '*': 'INT',
                                    '%': 'INT',
                                    '<': 'BOOL',
                                    '>': 'BOOL',
                                    '<=': 'BOOL',
                                    '>=': 'BOOL',
                                    '/=': 'BOOL',
                                    '==': 'BOOL',
                                    '=': 'INT'},
                          'FLOAT': {'+': 'FLOAT',
                                    '-': 'FLOAT',
                                    '/': 'FLOAT',
                                    '*': 'FLOAT',
                                    '%': 'FLOAT',
                                    '<': 'BOOL',
                                    '>': 'BOOL',
                                    '<=': 'BOOL',
                                    '>=': 'BOOL',
                                    '/=': 'BOOL',
                                    '==': 'BOOL',
                                    '=': 'int'}},
                 'FLOAT' : {'INT' : {'+': 'FLOAT',
                                    '-': 'FLOAT',
                                    '/': 'FLOAT',
                                    '*': 'FLOAT',
                                    '%': 'FLOAT',
                                    '<': 'BOOL',
                                    '>': 'BOOL',
                                    '<=': 'BOOL',
                                    '>=': 'BOOL',
                                    '/=': 'BOOL',
                                    '==': 'BOOL',
                                     '=': 'FLOAT'},
                          'FLOAT': {'+': 'FLOAT',
                                    '-': 'FLOAT',
                                    '/': 'FLOAT',
                                    '*': 'FLOAT',
                                    '%': 'FLOAT',
                                    '<': 'BOOL',
                                    '>': 'BOOL',
                                    '<=': 'BOOL',
                                    '>=': 'BOOL',
                                    '/=': 'BOOL',
                                    '==': 'BOOL',
                                    '=': 'FLOAT'}},
                 'BOOL' : {'BOOL' : {'AND' : 'BOOL',
                                     'OR' : 'BOOL',
                                     '=' : 'BOOL'}}}


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
 'VOID'    : 'VOID',
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


def p_vars(p):
    '''vars : VAR ids '''

def p_ids(p):
    'ids : type ID index'
    #print(actual_scope)
    dir_func[actual_scope]['scope'][p[2]] = {'type' : p[1]}
    #print(dir_func.get(actual_scope))

def p_index(p):
    '''index : '[' CTE_I ']'
             | '[' CTE_I ']' '[' CTE_I ']'
             | empty '''

def p_type(p):
    '''type : INT
            | FLOAT
            | BOOL
            | STRING '''
    p[0] = p[1]



### Revisar ###########################################
 
def p_func(p):
  'func : func1 func2'

def p_func1(p):
  'func1 : func1_1 func1_2'


def p_func1_1(p):
  '''func1_1 : FUNCTION func_type ID '(' '''
  if not p[3] in dir_func:
      global actual_scope
    
      if p[2] != 'VOID':
          dir_func['global']['scope'][p[3]] = {'type' : p[2]}
          
      actual_scope = p[3]
      dir_func[p[3]] = { 'type' : p[2], 'scope' : {}, 'numParams' : 0, 'quadStart' : contQuads }
  else:
      print("Funcion " + p[3] +" ya declarada")
      sys.exit()

def p_func1_2(p):
  '''func1_2 : more_ids ')' '{' '''

def p_func2(p):
  '''func2 : more_vars more_bloques '}' '''
  add_quad('ENDPROC','','','')

### Revisar #######################################




def p_more_ids(p):
    '''more_ids : ids 
                | ids more_ids
                | empty '''

def p_func_type(p):
    '''func_type : type
                 | VOID '''
    p[0] = p[1]

def p_bloque(p):
    '''bloque : assignation
              | loop
              | cond
              | return
              | lecture
              | writing
              | call  '''

def p_more_vars(p):
    '''more_vars : vars 
                 | vars more_vars
                 | empty '''

def p_more_funcs(p):
    '''more_funcs : func
                  | func more_funcs
                  | empty '''

def p_more_bloques(p):
    '''more_bloques : bloque
                    | bloque more_bloques 
                    | empty '''

def p_assignation(p):
    'assignation : assignTo '=' mega_exp'
    myVar = p[1]
    rightOperand = pilaO.pop()
    R_OP_type = pType.pop()

    try:
        varscope = dir_func[actual_scope]['scope'][myVar]
    except KeyError:
        varscope = dir_func['global']['scope'][myVar]
        result_check = semantic_check(varscope.get('type'),R_OP_type,'=')
        if result_check != 'error':
          add_quad('=','',rightOperand,myVar)
        else:
          print("Error de tipos al asignar")
          sys.exit()
    else:
        result_check = semantic_check(varscope.get('type'),R_OP_type,'=')
        if result_check != 'error':
          add_quad('=','',rightOperand,myVar)
        else:
          print("Error de tipos al asignar")
          sys.exit()


def p_assignTo(p):
  '''assignTo : ID arrayIndex'''
  p[0] = p[1]

def p_other_index(p):
    '''other_index : '[' exp ']'
                   | '[' exp ']' '[' exp ']'
                   | empty '''
   
def p_loop(p):
    '''loop : REPEAT '(' exp ')' '{' more_bloques '}' '''

def p_cond(p):
    '''cond : IF '(' mega_exp ')' '{' more_bloques '}'
            | IF '(' mega_exp ')' '{' more_bloques '}' ELSE '{' more_bloques '}' '''


def p_cond(p):
  'cond : cond1 cond2'


def p_cond1(p):
  '''cond1 : IF '(' mega_exp ')' '{' '''
  exp_type = pType.pop()
  if exp_type == 'BOOL':
    global contQuads
    resultado = pilaO.pop()
    add_quad('GOTOF', resultado, '', '')
    pJumps.append(contQuads - 1)
  else:
    print('Error de tipo en IF')
    sys.exit()

def p_cond2(p):
  '''cond2 : more_bloques '}' maybe_else'''
  fin = pJumps.pop()
  global contQuads
  updateQuad(fin,'result',contQuads)

def p_maybe_else(p):
  '''maybe_else : check_else do_else 
                | empty'''
  
def p_checkElse(p):
  '''check_else : ELSE '{' '''
  add_quad('GOTO','','','')
  falso = pJumps.pop()
  global contQuads
  pJumps.append(contQuads - 1)
  updateQuad(falso,'result',contQuads)

def p_doElse(p):
  '''doElse : more_bloques '}' '''

def p_return(p):
    '''return : RETURN mega_exp '''
    rightOperand = pilaO.pop()
    R_OP_type = pType.pop()
    result_type = semantic_check(dir_func[actual_scope].get('type'),R_OP_type,'=')
    if result_type != 'error':
        add_quad('RET','',rightOperand,'')
    else:
        print('Error de tipo al retornar en la funcion ' + actual_scope)
    sys.exit()

def p_lecture(p):
    '''lecture : READ ARR ID arr_mat '''

def p_writing(p):
    '''writing : PRINT '(' mega_exp ')' '''

def p_func_pred(p):
    '''func_pred : calculaRegresion '(' exp ')'
                 | prediceResultado '(' exp ')'
                 | calculaModa '(' exp ')'
                 | calculaMediana '(' exp ')'
                 | calculaMedia '(' exp ')' 
                 | calculaPoisson '(' exp ')'
                 | calculaBinomial '(' exp ')'
                 | calculaNormal '(' exp ')' '''

def p_call(p):
    '''call : call_1 call_2 
            | func_pred '''


def p_call_1(p):
  '''call_1 : ID '(' '''
  if p[1] in dir_func:
    add_quad('ERA','',p[1],'')
    global funcToCall
    funcToCall = p[1]
  else:
    print('Error la funcion ' + p[1] + ' no existe')
    sys.exit()  

def p_call_2(p):
  '''call_2 : exp ')' '''
  global contParam
  if contParam == dir_func[funcToCall].get('numParams'):
    add_quad('GOSUB',funcToCall,'','')
    if dir_func[funcToCall].get('type') != 'VOID':
      nextT = nextTemp(dir_func[funcToCall].get('type'))
      add_quad('=','',funcToCall,'(' + str(nextT) + ')') 
      pilaO.append('(' + str(nextT) + ')')
      pType.append(dir_func[funcToCall].get('type'))
    contParam = 0
  else:
    print('Error en el numero de parametros de ' + funcToCall)
    sys.exit()

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
    if p[1] == 'TRUE':
        pType.append('BOOL')
        pilaO.append(True)

    elif p[1] == 'FALSE':
        pType.append('BOOL')
        pilaO.append(False)

    elif not is_number(p[1]):
        try:
            varscope = dir_func[actual_scope]['scope'][p[1]]
        except KeyError:
            varscope = dir_func['global']['scope'][p[1]]
            pilaO.append(p[1])
            pType.append(varscope.get('type'))
        else:
            pilaO.append(p[1])
            pType.append(varscope.get('type'))

    elif float(p[1]) % 1 != 0:
        pType.append('FLOAT')
        pilaO.append(float(p[1]))
    elif int(p[1]):
        pType.append('INT')
        pilaO.append(int(p[1]))
    else: 
        pType.append('STRING')
        pilaO.append(string(p[1]))


def p_other(p):
    '''other : ID other_index
             | call
             | empty '''

def p_main(p):
    'main : MAIN '{' more_vars more_bloques '}' '
    actual_scope = p[1]
    dir_func[p[1]] = {'type' : 'VOID', 'scope' : {}}
    updateQuad(0, 'result', contQuads)
    #print(dir_func.get('move'))


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