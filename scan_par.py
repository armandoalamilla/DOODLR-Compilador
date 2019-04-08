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
contQuads = 0
contParam = 0
funcToCall = ''
currentQuad = 0
memFunc = 30000
Dim = 0
R = 1
toDim = ''
axuDim = 0

# Scope global
actual_scope = 'global'

# Directorio de funciones vacio
dir_func[actual_scope] = {'type' : 'VOID', 'scope' : {}, 'numParams' : 0, 'quadStart' : -1}

# Declaración de direcciones para variables globales, temporales y de tipos.
nextAvailable = {'gInt':1000, 'gFloat':5000, 'gBool':10000, 'tInt':15000, 'tFloat':20000,'tBool':25000 }

# Inicializacion de la memoria vacia
memoria = {}

# Funcion que regresa el siguiente valor de memoria TEMPORAL disponible en base al tipo.
def nextTemp(result_type):
  if result_type == 'INT':
    availableTemp = nextAvailable['tInt']
    nextAvailable['tInt'] = availableTemp + 1
    return availableTemp
  elif result_type == 'FLOAT':
    availableTemp = nextAvailable['tFloat']
    nextAvailable['tFloat'] = availableTemp + 1
    return availableTemp
  elif result_type == 'BOOL':
    availableTemp = nextAvailable['tBool']
    nextAvailable['tBool'] = availableTemp + 1
    return availableTemp

# Funcion que regresa el siguiente valor de memoria GLOBAL disponible en base al tipo.
def nextGlobal(result_type):
  global actual_scope
  if actual_scope =='global':
    if result_type == 'INT':
      availableGlobal = nextAvailable['gInt']
      nextAvailable['gInt'] = availableGlobal + 1
      return availableGlobal
    elif result_type == 'FLOAT':
      availableGlobal = nextAvailable['gFloat']
      nextAvailable['gFloat'] = availableGlobal + 1
      return availableGlobal
    elif result_type == 'BOOL':
      availableGlobal = nextAvailable['gBool']
      nextAvailable['gBool'] = availableGlobal + 1
      return availableGlobal
  else:
    print('Es funcion')

####### Inicio de  Funciones auxiliares #####################
# Funciones para agregar valores a pilas 
def add_pFunc(id):
  pFunc.append(id)

def add_pVar(num):
  pVar.append(num)

def add_pilaReturn(quad):
  pReturnTo.append(quad)

def add_pilaO(id):
    pilaO.append(id)

def add_pOper(oper):
    pOper.append(oper)

def add_pType(type):
    pType.append(type)

def add_pJumps(quad):
  pJumps.append(quad)

def add_pIterator(iterator):
  pIterator.append(iterator)

# Funciones para sacar el ultimo elemento de pilas 
def pop_pFunc():
    if (len(pFunc) > 0):
        return pFunc.pop()

def pop_pVar():
    if (len(pVar) > 0):
        return pVar.pop()

def pop_pilaReturn():
  if(len(pReturnTo) > 0):
    return pReturnTo.pop()

def pop_pilaO():
    if (len(pilaO) > 0):
        return pilaO.pop()

def pop_pOper():
    if (len(pOper) > 0):
        return pOper.pop()

def pop_pType():
    if (len(pType) > 0):
        return pType.pop()

def pop_pJumps():
  if (len(pJumps) > 0):
    return pJumps.pop()

def pop_pIterator():
  if (len(pIterator) > 0):
    return pIterator.pop()


# Funciones para regresar el tope de diferentes pilas 
def top_pOper():
    if (len(pOper) > 0):
        temp = pop_pOper()
        add_pOper(temp)
        return temp
    else:
        return -1

def top_pIterator():
  if (len(pIterator) > 0):
    temp = pop_pIterator()
    add_pIterator(temp)
    return temp
  else:
    return -1

def top_pFunc():
    if (len(pFunc) > 0):
        temp = pop_pFunc()
        add_pFunc(temp)
        return temp
    else:
        return -1

def top_pVar():
    if (len(pVar) > 0):
        temp = pop_pVar()
        add_pVar(temp)
        return temp
    else:
        return -1

######## Fin de funciones auxiliares ########################

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
cubo_semantico = {
        'INT' : { 
            'INT' : { 
                '+': 'INT',
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
                '=': 'INT'
            },
            'FLOAT': {
                '+': 'FLOAT',
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
                '=': 'INT'
            }
        },
        'FLOAT' : {
            'INT' : {
                '+': 'FLOAT',
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
                 '=': 'FLOAT'
            },
            'FLOAT': {
                '+': 'FLOAT',
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
                '=': 'FLOAT'
            }
        },
        'BOOL' : {
            'BOOL' : {
               'AND' : 'BOOL',
               'OR' : 'BOOL',
               '=' : 'BOOL'
            }
        },
        'STRING': {
            'STRING' : {
               '+': 'STRING',
               '=': 'STRING',
               '==': 'BOOL',
               '/=': 'BOOL'
            }
        }
}
            


######## Palabras reservadas y 'literals' del lenguaje ##########
literals = "}{()<>=;:,+-*/%&|^[]"

reserved = {

 'PROGRAM' : 'PR_PROGRAM',
 'PR_FUNCTION': 'PR_FUNCTION',
 'RETURN'  : 'PR_RETURN',
 'MAIN'    : 'PR_MAIN',


 'calculaRegresion' : 'PR_calculaRegresion',
 'prediceResultado' : 'PR_prediceResultado',
 'calculaModa'      : 'PR_calculaModa',
 'calculaMediana'   : 'PR_calculaMediana',
 'calculaMedia'     : 'PR_calculaMedia',
 'calculaPoisson'   : 'PR_calculaPoisson',
 'calculaBinomial'  : 'PR_calculaBinomial',
 'calculaNormal'    : 'PR_calculaNormal',
 

 'IF'      : 'PR_IF',
 'ELSE'    : 'PR_ELSE',
 'PRINT'   : 'PR_PRINT',
 'READ'    : 'PR_READ',
 'VAR'     : 'PR_VAR',
 'REPEAT'  : 'PR_REPEAT',
 'TRUE'    : 'PR_TRUE',
 'FALSE'   : 'PR_FALSE',
 'INT'     : 'PR_INT',
 'FLOAT'   : 'PR_FLOAT',
 'BOOL'    : 'PR_BOOL',
 'STRING'  : 'PR_STRING',
 'VOID'    : 'PR_VOID',
 'AND'     : 'PR_AND',
 'OR'      : 'PR_OR',
 'NOT'     : 'PR_NOT',

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
    aprobado = False
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)    

#Construye Lexer
lexer = lex.lex()

##################################################################################################################################
########## Parser ##########
def p_programa(p):
    '''programa : PR_PROGRAM '{' more_vars more_funcs main '}' '''


def p_vars(p):
    '''vars : PR_VAR ids '''

def p_ids(p):
   '''ids : type ID index'''

def p_index(p):
    '''index : '[' CTEI ']'
             | '[' CTEI ']' '[' CTEI ']'
             | empty '''

def p_type(p):
    '''type : PR_INT
            | PR_FLOAT
            | PR_BOOL
            | PR_STRING '''

### Revisar ###########################################
 
def p_func(p):
  '''func : func1 func2'''

def p_func1(p):
  '''func1 : func1_1 func1_2'''


def p_func1_1(p):
  '''func1_1 : PR_FUNCTION func_type ID '(' '''


def p_func1_2(p):
  '''func1_2 : more_ids ')' '{' '''

def p_func2(p):
  '''func2 : more_vars more_bloques '}' '''
  
### Revisar #######################################

def p_more_ids(p):
    '''more_ids : ids 
                | ids more_ids
                | empty '''

def p_func_type(p):
    '''func_type : type
                 | PR_VOID '''

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
    '''assignation : assignTo '=' mega_exp'''
   
def p_assignTo(p):
  '''assignTo : ID other_index'''

def p_other_index(p):
    '''other_index : '[' exp ']'
                   | '[' exp ']' '[' exp ']'
                   | empty '''
   
def p_loop(p):
    '''loop : PR_REPEAT '(' mega_exp ')' '{' more_bloques '}' '''


def p_cond(p):
  '''cond : cond1 cond2'''

def p_cond1(p):
  '''cond1 : PR_IF '(' mega_exp ')' '{' '''

def p_cond2(p):
  '''cond2 : more_bloques '}' maybe_else'''

def p_maybe_else(p):
  '''maybe_else : check_else do_else 
                | empty'''
  
def p_checkElse(p):
  '''check_else : PR_ELSE '{' '''

def p_do_else(p):
  '''do_else : more_bloques '}' '''

def p_return(p):
    '''return : PR_RETURN mega_exp '''

def p_lecture(p):
    '''lecture : PR_READ ARR ID index '''

def p_writing(p):
    '''writing : PR_PRINT '(' mega_exp ')' '''

def p_func_pred(p):
    '''func_pred : PR_calculaRegresion '(' exp ')'
                 | PR_prediceResultado '(' exp ')'
                 | PR_calculaModa '(' exp ')'
                 | PR_calculaMediana '(' exp ')'
                 | PR_calculaMedia '(' exp ')' 
                 | PR_calculaPoisson '(' exp ')'
                 | PR_calculaBinomial '(' exp ')'
                 | PR_calculaNormal '(' exp ')' '''

def p_call(p):
    '''call : call_1 call_2 
            | func_pred '''


def p_call_1(p):
  '''call_1 : ID '(' ''' 

def p_call_2(p):
  '''call_2 : exp ')' '''

def p_mega_exp(p):
    '''mega_exp : opt_not super_exp
                | opt_not super_exp log_op mega_exp '''

def p_log_op(p):
    '''log_op : PR_AND
              | PR_OR
              | PR_NOT '''

def p_opt_not(p):
    '''opt_not : PR_NOT
               | empty '''


def p_super_exp(p):
    '''super_exp : exp 
                 | exp rel_op super_exp '''

def p_rel_op(p):
    '''rel_op : '<'
              | '>'
              | LE
              | GE
              | EQ
              | NEQ '''

##################################################
def p_exp(p):
    '''exp : termino another_exp'''
    top = top_pOper()
    if top == '+' or top == '-':
        rightOperand = pop_pilaO()
        R_OP_type = pop_pType()
        leftOperand = pop_pilaO()
        L_OP_type = pop_pType()
        operator = pop_pOper()
        result_type = semantic_check(L_OP_type, R_OP_type, operator)
        if result_type != 'error':
            nextT = nextTemp(result_type)
            add_quad(operator,leftOperand,rightOperand,'(' + str(nextT) + ')')
            memoria[nextT] = 0
            add_pilaO('(' + str(nextT) + ')')
            add_pType(result_type)
            #for q in quad: print q
            #print(pType)
    else:
        print('Error de tipo en una suma o resta')
        sys.exit()

def p_another_exp(p):
  '''another_exp : '+' exp
                 | '-' exp 
                 | empty'''
  if len(p) > 2:
      add_pOper(p[1])   
##################################################

def p_termino(p):
'''termino : factor another_termino'''
    

def p_another_termino(p)
'''another_termino : '*' termino
                   | '/' termino 
                   | empty '''
  top = top_pOper()
  if top == '*' or top == '/':
    rightOperand = pop_pilaO()
    R_OP_type = pop_pType()
    leftOperand = pop_pilaO()
    L_OP_type = pop_pType()
    operator = pop_pOper()

    result_type = semantic_check(L_OP_type, R_OP_type, operator)

    if result_type != 'error':
      nextT = nextTemp(result_type)
      #cont de termporales
      add_quad(operator,leftOperand,rightOperand,'(' + str(nextT) + ')')
      memoria[nextT] = 0
      add_pilaO('(' + str(nextT) + ')')
      add_pType(result_type)
      #for q in quad: print q
      #print(pType)
    else:
      print('Error de tipo en una multiplicacion o division')
      sys.exit()



def p_factor(p): 
    '''factor : '(' super_exp ')'
              | '+' var_cte
              | '-' var_cte
              | var_cte '''

def p_var_cte(p):
    '''var_cte : other
               | CTEI
               | CTEF
               | CTES
               | PR_TRUE
               | PR_FALSE '''

def p_other(p):
    '''other : ID other_index
             | call
             | empty '''

def p_main(p):
    '''main : PR_MAIN '{' more_vars more_bloques '}' '''

def p_empty(p):
    '''empty : '''
    pass

def p_error(p):
    global aprobado
    aprobado = False
    print("Error de sintaxis en '%s'" % p.value)
    sys.exit()



###############################################################################

########## Test ##########
fName = input("Enter file name: ")

with open(fName, 'r') as myfile:
    s = myfile.read().replace('\n', '')

# Construye Parser
parser = yacc.yacc()

parser.parse(s)


## Code to display all found tokens ######
lexer.input(s)

print("List of Tokens: ")
while True:
   tok = lexer.token()
   if not tok:
       break
   print(tok)


if aprobado == True:
    print("Aprobado")
    sys.exit()
else: 
    print("NO aprobado")
    sys.exit()