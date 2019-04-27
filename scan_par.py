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
    '''programa : PR_PROGRAM '{' declarations main '}' '''

def p_value(p):
    '''value : CTEI
             | CTEF
             | CTES
             | PR_TRUE
             | PR_FALSE
             | ID'''
    if p[1] == 'TRUE':
        add_pType('BOOL')
        add_pilaO(True)
    elif p[1] == 'FALSE':
        add_pType('BOOL')
        add_pilaO(False)
    elif not is_number(p[1]):
        try:
            varscope = dir_func[actual_scope]['scope'][p[1]]
        except KeyError:
            varscope = dir_func['global']['scope'][p[1]]
            add_pilaO(p[1])
            add_pType(varscope.get('type'))
        else:
            add_pilaO(p[1])
            add_pType(varscope.get('type'))
    elif float(p[1]) % 1 != 0:
        add_pType('FLOAT')
        add_pilaO(float(p[1]))
    else:
        add_pType('INT')
        add_pilaO(int(p[1]))

def p_declarations(p):
    '''declarations : dec_var dec_func'''

def p_dec_var(p):
    '''dec_var : var dec_var 
               | empty '''

def p_dec_func(p):
    '''dec_func : func dec_func 
                | empty '''

def p_var(p):
    '''var : PR_VAR type ID index'''
    if not p[3] in dir_func[actual_scope]['scope']:
      varAddress = 0
      if actual_scope == 'global':
        varAddress = nextGlobal(p[2])
        dir_func[actual_scope]['scope'][p[3]] = {'type' : p[2], 'address':varAddress}
        memoria[varAddress] = 0
      else:
        dir_func[actual_scope]['scope'][p[3]] = {'type' : p[2]}
    else:
      print('Variable ' + p[3] + ' ya declarada')
      sys.exit()

def p_index(p):
    '''index : '[' CTEI ']'
             | '[' CTEI ']' '[' CTEI ']'
             | empty '''

def p_type(p):
    '''type : PR_INT
            | PR_FLOAT
            | PR_BOOL
            | PR_STRING '''
    p[0] = p[1]

def p_assignation(p):
    '''assignation : assignTo '=' mega_exp'''
    varia = p[1]
    rightOperand = pop_pilaO()
    R_OP_type = pop_pType()
    try:
        varscope = dir_func[actual_scope]['scope'][varia]
    except KeyError:
        varscope = dir_func['global']['scope'][varia]
        result_check = semantic_check(varscope.get('type'),R_OP_type,'=')
        if result_check != 'error':
            add_quad('=','',rightOperand,varia)
        else:
            print("Error de tipos al asignar")
            sys.exit()
    else:
        result_check = semantic_check(varscope.get('type'),R_OP_type,'=')
        if result_check != 'error':
            add_quad('=','',rightOperand,varia)
        else:
            print("Error de tipos al intentar asignar.")
            sys.exit()
   
def p_assignTo(p):
  '''assignTo : ID other_index'''
  p[0] = p[1]

def p_other_index(p):
    '''other_index : '[' exp ']'
                   | '[' exp ']' '[' exp ']'
                   | empty '''
 
def p_func(p):
  '''func : func1 func2'''

def p_func1(p):
  '''func1 : func1_1 func1_2'''

def p_func1_1(p):
  '''func1_1 : PR_FUNCTION func_type ID '(' '''
  if not p[3] in dir_func:
      global actual_scope
      if p[2] != 'VOID':
          varAddress = nextGlobal(p[2])
          dir_func['global']['scope'][p[3]] = {'type' : p[2], 'address':varAddress }
          memoria[varAddress] = 0

      actual_scope = p[3]
      dir_func[p[3]] = { 'type' : p[2], 'scope' : {}, 'numParams' : 0, 'quadStart' : contQuads }
  else:
      print("Funcion "+ p[3] +" ya declarada.")
      sys.exit()


def p_func1_2(p):
  '''func1_2 : params ')' '{' '''

def p_func2(p):
  '''func2 : dec_var block '}' '''
  add_quad('ENDPROC','','','')

def p_func_type(p):
  '''func_type : type
               | PR_VOID '''
  p[0] = p[1]

def p_params(p):
  '''params : type ID more_params
            | empty'''
  if len (p) > 2:
    dir_func[actual_scope]['scope'][p[2]] = {'type' : p[1]}
    dir_func[actual_scope]['numParams'] = dir_func[actual_scope]['numParams'] + 1

def p_more_params(p):
  '''more_params : ',' type ID more_params 
                 | empty'''
  if len(p) > 2:
    dir_func[actual_scope]['scope'][p[3]] = {'type' : p[2]}
    dir_func[actual_scope]['numParams'] = dir_func[actual_scope]['numParams'] + 1

def p_main_block(p):
  '''main_block : main_block1 block '}' '''

def p_main_block1(p):
  '''main_block1 : PR_MAIN '{' '''
  global actual_scope
  actual_scope = p[1]
  dir_func[p[1]] = {'type' : 'VOID', 'scope' : {}}
  updateQuad(0,'result', contQuads)

def p_log_op(p):
    '''log_op : PR_AND
              | PR_OR '''
    if len(p) > 1:
        add_pOper(p[1])
        #print(pOper)

def p_loop(p):
  '''loop : loop1 loop2 loop3'''
  fin = pop_pJumps()
  inicio = pop_pJumps()
  iterator = pop_pIterator()
  add_quad('+',iterator,1,iterator)
  add_quad('GOTO', '','',inicio)
  global contQuads
  updateQuad(fin,'result',contQuads)
  add_quad('=','',1,iterator)

def p_loop1(p):
  '''loop1 : PR_REPEAT'''
  add_pJumps(contQuads)
  nextT = nextTemp('INT')
  add_pIterator('(' + str(nextT) + ')')
  memoria[nextT] = 1

def p_loop2(p):
  '''loop2 : '(' exp ')' '''
  exp_type = pop_pType()
  if exp_type == 'INT':
    resultado = pop_pilaO()
    nextT = nextTemp('BOOL')
    memoria[nextT]= False
    iterator = top_pIterator()
    add_quad('<=', iterator, resultado,'(' + str(nextT) + ')')
    add_quad('GOTOF','(' + str(nextT) + ')','','')
    global contQuads
    add_pJumps(contQuads - 1)
  else:
    print('Error de tipo en ciclo')
    sys.exit()

def p_loop3(p):
  '''loop3 : '{' block '}' '''

def p_rel_op(p):
    '''rel_op : '<'
              | '>'
              | LE
              | GE
              | EQ
              | NEQ '''

def p_block(p):
  '''block : estructura block '''

def p_estructura(p):
  '''estructura : assignation 
                | loop 
                | cond
                | return 
                | func_call 
                | dec_var '''

def p_func_call(p):
  '''func_call : func_call1 func_call2
              | PR_calculaRegresion '(' exp ')'
              | PR_prediceResultado '(' exp ')'
              | PR_calculaModa '(' exp ')'
              | PR_calculaMediana '(' exp ')'
              | PR_calculaMedia '(' exp ')' 
              | PR_calculaPoisson '(' exp ')'
              | PR_calculaBinomial '(' exp ')'
              | PR_calculaNormal '(' exp ')' '''
  
def p_func_call1(p):
  '''func_call1 : ID TO_PARABRE'''
  if p[1] in dir_func:
    add_quad('ERA','',p[1],'')
    global funcToCall
    funcToCall = p[1]
  else:
    print('Error, la funcion ' + p[1] + ' no existe')
    sys.exit()  

def p_func_call2(p):
  '''func_call2 : param_vals TO_PARCIERRA'''
  global contParam
  if contParam == dir_func[funcToCall].get('numParams'):
    add_quad('GOSUB',funcToCall,'','')
    if dir_func[funcToCall].get('type') != 'VOID':
      nextT = nextTemp(dir_func[funcToCall].get('type'))
      add_quad('=','',funcToCall,'(' + str(nextT) + ')') 
      memoria[nextT] = 0
      add_pilaO('(' + str(nextT) + ')')
      add_pType(dir_func[funcToCall].get('type'))
    contParam = 0
  else:
    print('Error en el numero de parametros de ' + funcToCall)
    sys.exit()

def p_param_vals(p):
  '''param_vals : un_param more_param_vals 
                | empty'''

def p_more_param_vals(p):
  '''more_param_vals : ',' un_param more_param_vals 
                     | empty'''

def p_un_param(p):
  '''un_param : ID ':' mega_exp'''
  global funcToCall
  val = pop_pilaO()
  valType = pop_pType()
  funcTable = dir_func[funcToCall]
  try:
    result = semantic_check(funcTable['scope'][p[1]].get('type'),valType, '=')
  except KeyError:
    print('Error parametro ' + p[1] + ' no existe para la funcion ' + funcToCall )
    sys.exit()
  if result != 'error':
    global contParam
    contParam = contParam + 1
    #print('Aqui es memoria')

    add_quad('PARAM', val, '',funcToCall + ':' + p[1])

  else:
    print('Error de tipo al enviar parametro ' + p[1])
    sys.exit()

def p_return(p):
    '''return : PR_RETURN mega_exp '''
    rightOperand = pop_pilaO()
    R_OP_type = pop_pType()
    result_type = semantic_check(dir_func[actual_scope].get('type'),R_OP_type,'=')
    if result_type != 'error':
        add_quad('RET','',rightOperand,'')
    else:
        print('Error de tipo al retornar en la funcion ' + actual_scope)
        sys.exit()



def p_cond(p):
  '''cond : cond1 cond2'''

def p_cond1(p):
  '''cond1 : PR_IF '(' mega_exp ')' '{' '''
  exp_type = pop_pType()
  if exp_type == 'BOOL':
    global contQuads
    resultado = pop_pilaO()
    add_quad('GOTOF', resultado, '', '')
    add_pJumps(contQuads - 1)
  else:
    print('Error de tipo en IF.')
    sys.exit()

def p_cond2(p):
  '''cond2 : block '}' maybe_else'''
  fin = pop_pJumps()
  global contQuads
  updateQuad(fin,'result',contQuads)

def p_maybe_else(p):
  '''maybe_else : check_else do_else 
                | empty'''
  
def p_check_else(p):
  '''check_else : PR_ELSE '{' '''
  add_quad('GOTO','','','')
  falso = pop_pJumps()
  global contQuads
  add_pJumps(contQuads - 1)
  updateQuad(falso,'result',contQuads)

def p_do_else(p):
  '''do_else : block '}' '''

#######################################################
def p_mega_exp(p):
    '''mega_exp : opt_not super_exp another_mega_exp '''
    top = top_pOper()
    if top == 'OR' or top == 'AND' or top == 'NOT':
        rightOperand = pop_pilaO()
        R_OP_type = pop_pType()
        operator = pop_pOper()
        if operator == 'NOT':
            if R_OP_type == 'BOOL':
                nextT = nextTemp(R_OP_type)
                add_quad(operator,'',rightOperand,'(' + str(nextT) + ')')
                memoria[nextT] = 0
                add_pilaO('(' + str(nextT) + ')')
                add_pType('BOOL')
            else:
                print('Error de tipo en negacion')
                sys.exit()
        else:
            leftOperand = pop_pilaO()
            L_OP_type = pop_pType()
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
                print('Error de tipo en una comparacion')
                sys.exit()

def p_opt_not(p):
    '''opt_not : PR_NOT
               | empty '''
    if p[1] == 'NOT':
        add_pOper(p[1])
        #print(pOper) 

def p_another_mega_exp(p):
    '''another_mega_exp : log_op mega_exp
                        | empty'''
#######################################################
def p_super_exp(p):
    '''super_exp : exp opt_rel'''

def p_opt_rel(p):
    '''opt_rel : rel_op exp
               | empty'''
    top = top_pOper()
    if top == '>' or top == '<' or top == '>=' or top == '<=' or top == '/=' or top == '==':
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
            print('Error de tipo en una comparacion')
            sys.exit()  
#######################################################
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
      print('Error de tipo en una operación.')
      sys.exit()
    

def p_another_termino(p):
  '''another_termino : '*' termino
                     | '/' termino 
                     | '%' termino
                     | empty '''
  if len(p) > 2:
      add_pOper(p[1])                   
 

def p_factor(p): 
    '''factor : '(' mega_exp ')'
              | func_call
              | value '''

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