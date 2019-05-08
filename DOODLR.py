import ply.lex as lex
import ply.yacc as yacc
import sys

# Librerias necesarias para el analalisis estadistico
import matplotlib.pyplot as plt
import numpy as np
import statistics as st
import matplotlib
import matplotlib.colors

# Inicializacion de diccionarios,variables y listas necesarias para el compilador
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
pArr = []
contQuads = 0
contParam = 0
funcToCall = ''
currentQuad = 0
memFunc = 30000
Dim = 0
R = 1
toDim = ''
axuDim = 0

# Inicilizacion del scope global
actual_scope = 'global'

# Inicializacion del directorio de funciones vacio
dir_func[actual_scope] = {'type': 'VOID', 'scope': {}, 'numParams': 0, 'quadStart': -1}

# Declaracion de direcciones para variables globales y temporales
nextAvailable = {'gInt': 1000, 'gFloat': 5000, 'gBool': 10000,
                 'tInt': 15000, 'tFloat': 20000, 'tBool': 25000}

# Inicializacion de la memoria vacia
memoria = {}

# Funcion que en base a un tipo de resultado regresa el siguiente valor de memoria para Temp disponible
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


# Funcion que en base a un tipo de resultado regresa el siguiente valor de memoria para Global disponible
def nextGlobal(result_type):
    global actual_scope
    if actual_scope == 'global':
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
        print('Es una funcion')


# Funciones para agregar valores a las pilas
def add_pArr(id):
    pArr.append(id)

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


# funciones para sacar el ultimo elemento de las pilas
def pop_pArr():
    if (len(pArr) > 0):
        return pArr.pop()

def pop_pFunc():
    if (len(pFunc) > 0):
        return pFunc.pop()

def pop_pVar():
    if (len(pVar) > 0):
        return pVar.pop()

def pop_pilaReturn():
    if (len(pReturnTo) > 0):
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

# Funciones para regresar el tope de las pilas
def top_pArr():
    if (len(pArr) > 0):
        temp = pop_pArr()
        add_pArr(temp)
        return temp
    else:
        return -1

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

# Funcion que agrega el cuadruplo al diccionario de cuadruplos
def add_quad(operator, leftOperand, rightOperand, result):
    quad.append({'operator': operator, 'leftOperand': leftOperand, 'rightOperand': rightOperand, 'result': result})
    global contQuads
    contQuads = contQuads + 1


add_quad('GOTO', '', '', '')

# Funcion que actualiza las casillas pendientes de los cuádruplos
def updateQuad(i, llave, val):
    (quad[i])[llave] = val

# Funcion que checa que las operaciones existan en el cubo semántico
def semantic_check(lOP_type, rOP_type, oper):
    if lOP_type in sem_cube:
        if rOP_type in sem_cube[lOP_type]:
            if oper in sem_cube[lOP_type][rOP_type]:
                return sem_cube[lOP_type][rOP_type][oper]
    return 'error'

# Funcion de utilidad que revisa si el paraametro es un numero
def is_number(s):
    try:
        float(s)
        return True
    except ValueError:
        return False


# Declaracion del cubo semantico
sem_cube = {'INT': {'INT': {'+': 'INT',
                            '-': 'INT',
                            '/': 'FLOAT',
                            '*': 'INT',
                            '%': 'INT',
                            '<': 'BOOL',
                            '>': 'BOOL',
                            '<=': 'BOOL',
                            '>=': 'BOOL',
                            '!=': 'BOOL',
                            '==': 'BOOL',
                            '=': 'INT'},
                    'FLOAT': {'+': 'FLOAT',
                             '-': 'FLOAT',
                             '/': 'FLOAT',
                             '*': 'FLOAT',
                             '<': 'BOOL',
                             '>': 'BOOL',
                             '<=': 'BOOL',
                             '>=': 'BOOL',
                             '!=': 'BOOL',
                             '==': 'BOOL',
                             '=': 'INT'}},
            'FLOAT': {'INT': {'+': 'FLOAT',
                             '-': 'FLOAT',
                             '/': 'FLOAT',
                             '*': 'FLOAT',
                             '<': 'BOOL',
                             '>': 'BOOL',
                             '<=': 'BOOL',
                             '>=': 'BOOL',
                             '!=': 'BOOL',
                             '==': 'BOOL',
                             '=': 'FLOAT'},
                     'FLOAT': {'+': 'FLOAT',
                              '-': 'FLOAT',
                              '/': 'FLOAT',
                              '*': 'FLOAT',
                              '<': 'BOOL',
                              '>': 'BOOL',
                              '<=': 'BOOL',
                              '>=': 'BOOL',
                              '!=': 'BOOL',
                              '==': 'BOOL',
                              '=': 'FLOAT'}},
            'BOOL': {'BOOL': {'AND': 'BOOL',
                              'OR': 'BOOL',
                              '=': 'BOOL'}}}

# Lista de las palabras reservadas del lenguaje
reserved = {
    'PROGRAM': 'PR_program',
    'VAR': 'PR_var',
    'FUNC': 'PR_function',
    'MAIN': 'PR_main',


    'calculaRegresion': 'PR_calculaRegresion',
    'calculaModa': 'PR_calculaModa',
    'calculaMediana': 'PR_calculaMediana',
    'calculaMedia': 'PR_calculaMedia',
    'calculaPoisson': 'PR_calculaPoisson',
    'calculaBinomial': 'PR_calculaBinomial',
    'calculaNormal': 'PR_calculaNormal',


    'ARR': 'PR_arreglo',
    'IF': 'PR_if',
    'ELSE': 'PR_else',
    'LOOP': 'PR_loop',
    'TRUE': 'PR_true',
    'FALSE': 'PR_false',
    'NOT': 'PR_negacion',
    'AND': 'PR_interseccion',
    'OR': 'PR_union',
    'INT': 'PR_int',
    'FLOAT': 'PR_float',
    'BOOL': 'PR_bool',
    'VOID': 'PR_void',
    'RET': 'PR_return',
    'END': 'PR_end',
    'PRINT': 'PR_print',
}

# Diccionario de tokens
tokens = [
    'OP_MAS', 'OP_MENOS', 'OP_MULT', 'OP_DIV', 'OP_RESID',
    'OP_DOBLEIGUAL', 'OP_IGUAL', 'OP_DIFDE', 'OP_MENORQUE', 'OP_MENOROIGUAL',
    'OP_MAYORQUE', 'OP_MAYOROIGUAL',
    'TO_PARABRE', 'TO_PARCIERRA', 'TO_LLAABRE', 'TO_LLACIERRA',
    'TO_CORABRE', 'TO_CORCIERRA',
    'TO_INT', 'TO_FLOAT', 'ID', 'TO_COMA', 'TO_DOSPTOS'
]

# Expresiones regulares de los tokens
t_OP_MAS = r'\+'
t_OP_MENOS = r'\-'
t_OP_MULT = r'\*'
t_OP_DIV = r'\/'
t_OP_RESID = r'\%'
t_OP_DOBLEIGUAL = r'\=\='
t_OP_IGUAL = r'\='
t_OP_DIFDE = r'\!\='
t_OP_MENORQUE = r'\<'
t_OP_MENOROIGUAL = r'\<\='
t_OP_MAYORQUE = r'\>'
t_OP_MAYOROIGUAL = r'\>\='
t_TO_PARABRE = r'\('
t_TO_PARCIERRA = r'\)'
t_TO_LLAABRE = r'\{'
t_TO_LLACIERRA = r'\}'
t_TO_CORABRE = r'\['
t_TO_CORCIERRA = r'\]'
t_TO_INT = r'[0-9]+'
t_TO_FLOAT = r'[0-9]+\.[0-9]+'
t_TO_COMA = r'\,'
t_TO_DOSPTOS = r'\:'

tokens = tokens + list(reserved.values())

# Expresion regular de ID
def t_ID(t):
    r'[a-zA-Z][a-zA-Z0-9]*'
    t.type = reserved.get(t.value, 'ID')
    return t

# Caracteres ignorados
t_ignore = ' \t\n'

# Revisa caracteres ilegales en la sintaxis
def t_error(t):
    global aprobado
    aprobado = False
    print("Caracter ilegal '%s'" % t.value[0])
    t.lexer.skip(1)

# Construye el lexer
lexer = lex.lex()

# Inicio de programa
def p_prog(p):
    'prog : PR_program TO_LLAABRE declare mainBlock TO_LLACIERRA'
    a = 0
    # for q in quad:
    #     print(a)
    #     print(q)
    #     a = a + 1

# Definicion de regla de valor
# En caso de que lo que se lea sea un arreglo, valida que exista la variable dimensionada, de ser asi
# Si existe, se agrega el arreglo al directorio de funciones junto con su tipo y pilas
def p_val(p):
    '''val :  TO_INT
            | TO_FLOAT
            | PR_true
            | PR_false
            | ID
            | PR_arreglo firstIndex moreDimIndex TO_CORCIERRA'''
    if len(p) > 2:
        arreglo = pop_pArr()
        varscope = ''
        try:
            dimensiones = dir_func[actual_scope]['scope'][arreglo.get('name')]['dim']
            varscope = actual_scope
        except KeyError:
            dimensiones = dir_func['global']['scope'][arreglo.get('name')]['dim']
            varscope = 'global'
        else:
            print("Error la variable  no existe")
            print(arreglo)
            sys.exit()
        if arreglo.get('currentDim') != len(dimensiones) and len(dimensiones) != 1:
            print('Error, faltan dimensiones en el arreglo')
            sys.exit()
        nextT = nextTemp('INT')
        memoria[nextT] = 0
        temp1 = '(' + str(nextT) + ')'
        aux = pop_pilaO()
        rand = pop_pType()
        add_quad('+', aux, dimensiones[len(dimensiones) - 1].get('Val'), temp1)
        nextT = nextTemp('INT')
        memoria[nextT] = 0
        temp2 = '[' + str(nextT) + ']'
        myDat = varscope + '/' + arreglo.get('name')
        add_quad('DIRBASE', temp1, myDat, temp2)
        add_pilaO(temp2)
        add_pType(dir_func[varscope]['scope'][arreglo.get('name')].get('type'))
    elif p[1] == 'TRUE':
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

def p_declare(p):
    'declare : decVar decFunc'

def p_decVar(p):
    ''' decVar : var decVar
                | empty'''

def p_decFunc(p):
    ''' decFunc : func decFunc
                | empty'''

def p_var(p):
    'var : var1 arrayCreate'
    if actual_scope == 'global':
        varAddress = nextGlobal(dir_func[actual_scope]['scope'][p[1]].get('type'))
        dir_func[actual_scope]['scope'][p[1]]['address'] = varAddress
        memoria[varAddress] = 0
        if p[2] == 1:
            cant = 1
            for i in dir_func[actual_scope]['scope'][p[1]]['dim']:
                cant = cant * i.get('Lim')
            for i in range(cant - 1):
                varAddress = nextGlobal(dir_func[actual_scope]['scope'][p[1]].get('type'))
                memoria[varAddress] = 0

# Declaración de variable, si esta ya existe en el dir de func, muestra error
def p_var1(p):
    'var1 :  PR_var tipo ID'
    if not p[3] in dir_func[actual_scope]['scope']:
        varAddress = 0
        dir_func[actual_scope]['scope'][p[3]] = {'type': p[2], 'address': 123, 'dim': []}
        p[0] = p[3]
        global toDim
        toDim = p[3]
    else:
        print('Variable ' + p[3] + ' ya declarada')
        sys.exit()

# Regla para crear arreglos con n dimensiones
def p_arrayCreate(p):
    '''arrayCreate : firstCreate moreDimCreate TO_CORCIERRA
                   | empty'''
    if len(p) > 2:
        mDim = 0
        Suma = 0
        global R
        for i in range(0, len(dir_func[actual_scope]['scope'][toDim]['dim'])):
            mDim = R / (dir_func[actual_scope]['scope'][toDim]['dim'][i].get('Lim'))
            R = mDim
            Suma = Suma + mDim
            if i < len(dir_func[actual_scope]['scope'][toDim]['dim']) - 1:
                dir_func[actual_scope]['scope'][toDim]['dim'][i]['Val'] = mDim
            else:
                dir_func[actual_scope]['scope'][toDim]['dim'][i]['Val'] = Suma * -1
        p[0] = 1

    else:
        p[0] = 0


# Agrega arreglo al dir junto con sus dimensiones
def p_firstCreate(p):
    'firstCreate : TO_CORABRE TO_INT'
    dicAux = {'Lim': int(p[2]), 'Val': 0}
    dir_func[actual_scope]['scope'][toDim]['dim'].append(dicAux)
    global R
    R = R * int(p[2])

def p_moreDimCreate(p):
    '''moreDimCreate : unaDimCreate moreDimCreate
                     | empty'''

def p_unaDimCreate(p):
    'unaDimCreate : TO_COMA TO_INT'
    if len(p) > 2:
        dicAux = {'Lim': int(p[2]), 'Val': 0}
        dir_func[actual_scope]['scope'][toDim]['dim'].append(dicAux)
        global R
        R = R * int(p[2])

def p_tipo(p):
    '''tipo : PR_int
            | PR_float
            | PR_bool '''
    p[0] = p[1]

# Revisa el valor
def p_assign(p):
    'assign : assignTo OP_IGUAL megaExp'
    varia = p[1]
    rightOperand = pop_pilaO()
    rOP_type = pop_pType()
    if varia[0] == '[':
        arreglo = pop_pArr()
        try:
            varscope = dir_func[actual_scope]['scope'][arreglo.get('name')]
            try:
                dimensiones = dir_func[actual_scope]['scope'][arreglo.get('name')]['dim']
                varscope = actual_scope
            except KeyError:
                dimensiones = dir_func['global']['scope'][arreglo.get('name')]['dim']
                varscope = 'global'
            else:
                print("Error la variable no existe")
                sys.exit()

            if arreglo.get('currentDim') != len(dimensiones) and len(dimensiones) != 1:
                print('Error, faltan dimensiones en el arreglo')
                sys.exit()

            result_check = semantic_check(varscope.get('type'), rOP_type, '=')
            if result_check != 'error':
                add_quad('=', '', rightOperand, varia)
            else:
                print("Error de tipos al asignar")
                sys.exit()
        except KeyError:
            varscope = dir_func['global']['scope'][arreglo.get('name')]
            result_check = semantic_check(varscope.get('type'), rOP_type, '=')
            if result_check != 'error':
                add_quad('=', '', rightOperand, varia)
            else:
                print("Error de tipos al asignar")
                sys.exit()
        else:
            print('Error, la variable no existe en el scope')
            sys.exit()
    else:
        try:
            varscope = dir_func[actual_scope]['scope'][varia]
        except KeyError:
            varscope = dir_func['global']['scope'][varia]
            result_check = semantic_check(varscope.get('type'), rOP_type, '=')
            if result_check != 'error':
                add_quad('=', '', rightOperand, varia)
            else:
                print("Error de tipos al asignar")
                sys.exit()
        else:
            result_check = semantic_check(varscope.get('type'), rOP_type, '=')
            if result_check != 'error':
                add_quad('=', '', rightOperand, varia)
            else:
                print("Error de tipos al asignar")
                sys.exit()


# Asegnacion de arreglos. Generar el cuadruplo de la dirbase
def p_assignTo(p):
    '''assignTo : ID
                | PR_arreglo firstIndex moreDimIndex TO_CORCIERRA'''
    if len(p) > 2:
        arreglo = top_pArr()
        varscope = ''
        try:
            dimensiones = dir_func[actual_scope]['scope'][arreglo.get('name')]['dim']
            varscope = actual_scope
        except KeyError:
            dimensiones = dir_func['global']['scope'][arreglo.get('name')]['dim']
            varscope = 'global'
        else:
            print("Error la variable no existe")
            sys.exit()
        nextT = nextTemp('INT')
        memoria[nextT] = 0
        temp1 = '(' + str(nextT) + ')'
        aux = pop_pilaO()
        rand = pop_pType()
        add_quad('+', aux, dimensiones[len(dimensiones) - 1].get('Val'), temp1)
        nextT = nextTemp('INT')
        memoria[nextT] = 0
        temp2 = '[' + str(nextT) + ']'
        myDat = varscope + '/' + arreglo.get('name')
        add_quad('DIRBASE', temp1, myDat, temp2)
        add_pilaO(temp2)
        add_pType(dir_func[varscope]['scope'][arreglo.get('name')].get('type'))
        p[0] = temp2
    else:
        p[0] = p[1]

def p_firstIndex(p):
    'firstIndex : ID TO_CORABRE exp'

    varscope = ''

    try:
        dimensiones = dir_func[actual_scope]['scope'][p[1]]['dim']
        varscope = actual_scope
    except KeyError:
        dimensiones = dir_func['global']['scope'][p[1]]['dim']
        varscope = 'global'
    else:
        print("Error la variable no existe")
        sys.exit()

    if len(dimensiones) > 0:
        add_pArr({'name': p[1], 'currentDim': 1})

        index = pop_pilaO()
        indexType = pop_pType()
        result_type = semantic_check(indexType, 'INT', '=')

        if result_type != 'error':
            add_quad('VER', index, dimensiones[0].get('Lim'), '')

            if len(dimensiones) > 1:
                nextT = nextTemp('INT')
                memoria[nextT] = 0
                temp1 = '(' + str(nextT) + ')'
                add_quad('*', index, dimensiones[0].get('Val'), temp1)
                add_pilaO(temp1)
                add_pType('INT')
            else:
                add_pType(indexType)
                add_pilaO(index)

        else:
            print('Error, usa un INT para el indice de un arreglo')
            sys.exit()
    else:
        print('Error, la variable ' + p[1] + ' no es dimensionada')
        sys.exit()


def p_moreDimIndex(p):
    '''moreDimIndex : unaDim moreDimIndex
                     | empty'''


# Regla para mas de una dimension en arreglo. Valida semantica de tipos
def p_unaDim(p):
    'unaDim : TO_COMA exp'
    if len(p) > 2:
        varscope = ''
        arreglo = top_pArr()
        try:
            dimensiones = dir_func[actual_scope]['scope'][arreglo.get('name')]['dim']
            varscope = actual_scope
        except KeyError:
            dimensiones = dir_func['global']['scope'][arreglo.get('name')]['dim']
            varscope = 'global'
        else:
            print("Error la variable no existe")
            sys.exit()
        index = pop_pilaO()
        indexType = pop_pType()
        result_type = semantic_check(indexType, 'INT', '=')
        if result_type != 'error':
            add_quad('VER', index, dimensiones[arreglo.get('currentDim')].get('Lim'), '')
            if arreglo.get('currentDim') < len(dimensiones) - 1:
                nextT = nextTemp('INT')
                memoria[nextT] = 0
                temp1 = '(' + str(nextT) + ')'
                add_quad('*', index, dimensiones[arreglo.get('currentDim')].get('Val'), temp1)
                add_pilaO(temp1)
                add_pType('INT')
            else:
                add_pilaO(index)
                add_pType(indexType)
            nextT = nextTemp('INT')
            memoria[nextT] = 0
            temp1 = '(' + str(nextT) + ')'
            aux1 = pop_pilaO()
            aux2 = pop_pilaO()
            random = pop_pType()
            random = pop_pType()
            add_quad('+', aux1, aux2, temp1)
            add_pilaO(temp1)
            add_pType('INT')
            auxArreglo = pop_pArr()
            auxArreglo['currentDim'] = auxArreglo.get('currentDim') + 1
            add_pArr(auxArreglo)
        else:
            print('Error, usa un INT para el indice de un arreglo')
            sys.exit()

def p_func(p):
    'func : func1 func2'

def p_func1(p):
    'func1 : func11 func12'

# Declaracion de funciones. Valida que esta no exista en el dir func.
def p_func11(p):
    'func11 : PR_function decideType ID TO_PARABRE'
    if not p[3] in dir_func:
        global actual_scope
        if p[2] != 'VOID':
            varAddress = nextGlobal(p[2])
            dir_func['global']['scope'][p[3]] = {'type': p[2], 'address': varAddress}
            memoria[varAddress] = 0
        actual_scope = p[3]
        dir_func[p[3]] = {'type': p[2], 'scope': {}, 'numParams': 0, 'quadStart': contQuads}
    else:
        print("Funcion " + p[3] + " ya declarada")
        sys.exit()


def p_func12(p):
    'func12 : params TO_PARCIERRA TO_LLAABRE'


def p_func2(p):
    'func2 : decVar bloque TO_LLACIERRA'
    add_quad('ENDPROC', '', '', '')


def p_decideType(p):
    '''decideType : tipo
                  | PR_void'''
    p[0] = p[1]

def p_params(p):
    '''params : tipo ID moreParams
              | empty'''
    if len(p) > 2:
        dir_func[actual_scope]['scope'][p[2]] = {'type': p[1], 'dim': []}
        dir_func[actual_scope]['numParams'] = dir_func[actual_scope]['numParams'] + 1

# Parametros de funciones ya declaradas
def p_moreParams(p):
    '''moreParams : TO_COMA tipo ID moreParams
              | empty'''
    if len(p) > 2:
        dir_func[actual_scope]['scope'][p[3]] = {'type': p[2], 'dim': []}
        dir_func[actual_scope]['numParams'] = dir_func[actual_scope]['numParams'] + 1


def p_mainBlock(p):
    'mainBlock : mainBlock1 bloque TO_LLACIERRA'


# Agrega al dir de funciones la funcion main
def p_mainBlock1(p):
    'mainBlock1 : PR_main TO_LLAABRE'
    global actual_scope
    actual_scope = p[1]
    dir_func[p[1]] = {'type': 'VOID', 'scope': {}}
    updateQuad(0, 'result', contQuads)


def p_opLogico(p):
    '''opLogico : PR_interseccion
                | PR_union'''
    if len(p) > 1:
        add_pOper(p[1])

# print(pOper)


# Realiza operaciones correspondientes a los loops
def p_loop(p):
    'loop : loop1 loop2 loop3'
    fin = pop_pJumps()
    inicio = pop_pJumps()
    iterator = pop_pIterator()
    add_quad('+', iterator, 1, iterator)
    add_quad('GOTO', '', '', inicio)
    global contQuads
    updateQuad(fin, 'result', contQuads)
    add_quad('=', '', 1, iterator)


def p_loop1(p):
    'loop1 : PR_loop'
    add_pJumps(contQuads)
    nextT = nextTemp('INT')
    add_pIterator('(' + str(nextT) + ')')
    memoria[nextT] = 1


def p_loop2(p):
    'loop2 : TO_PARABRE exp TO_PARCIERRA'
    exp_type = pop_pType()
    if exp_type == 'INT':
        resultado = pop_pilaO()
        nextT = nextTemp('BOOL')
        memoria[nextT] = False
        iterator = top_pIterator()
        add_quad('<=', iterator, resultado, '(' + str(nextT) + ')')
        add_quad('GOTOF', '(' + str(nextT) + ')', '', '')
        global contQuads
        add_pJumps(contQuads - 1)
    else:
        print('Error de tipo en LOOP')
        sys.exit()


def p_loop3(p):
    'loop3 : TO_LLAABRE bloque TO_LLACIERRA'


def p_opRelacional(p):
    '''opRelacional : OP_DOBLEIGUAL
                    | OP_DIFDE
                    | OP_MENORQUE
                    | OP_MENOROIGUAL
                    | OP_MAYORQUE
                    | OP_MAYOROIGUAL'''

    if len(p) > 1:
        add_pOper(p[1])


def p_bloque(p):
    '''bloque : estructura bloque
              | PR_end'''


def p_estructura(p):
    '''estructura : assign
                  | loop
                  | comparacion
                  | return
                  | funcCall
                  | decVar
                  | write '''

# Genera los cuadrupos de las funciones predeterminadas
def p_funcCall(p):
    '''funcCall : funcCall1 funcCall2
                | PR_calculaRegresion TO_PARABRE ID TO_PARCIERRA
                | PR_calculaModa TO_PARABRE ID TO_PARCIERRA
                | PR_calculaMediana TO_PARABRE ID TO_PARCIERRA
                | PR_calculaMedia TO_PARABRE ID TO_PARCIERRA
                | PR_calculaPoisson TO_PARABRE ID TO_PARCIERRA
                | PR_calculaBinomial TO_PARABRE ID TO_PARCIERRA
                | PR_calculaNormal TO_PARABRE ID TO_PARCIERRA '''
    if (p[1] == 'calculaRegresion' or p[1] == 'calculaModa' or p[1] == 'calculaMediana' or p[1] == 'calculaMedia'
            or p[1] == 'calculaPoisson' or p[1] == 'calculaBinomial' or p[1] == 'calculaNormal'):
        add_quad(p[1], '', '', p[3])

# Regla de print
def p_write(p):
    '''write : PR_print TO_PARABRE superExp action TO_PARCIERRA '''

# Cuadruplo de write
def p_action(p):
    '''action : empty'''
    rightOperand = pop_pilaO()
    add_quad('PRINT', rightOperand,'','')

# crea el ERA de la funcion correspondiente
def p_funcCall1(p):
    'funcCall1 : ID TO_PARABRE'
    if p[1] in dir_func:
        add_quad('ERA', '', p[1], '')
        global funcToCall
        funcToCall = p[1]
    else:
        print('Error la funcion ' + p[1] + ' no existe')
        sys.exit()

# Crea el gosub de la funcion correspondientes asi como los parametros
def p_funcCall2(p):
    'funcCall2 : paramVals TO_PARCIERRA'
    global contParam
    if contParam == dir_func[funcToCall].get('numParams'):
        add_quad('GOSUB', funcToCall, '', '')
        if dir_func[funcToCall].get('type') != 'VOID':
            nextT = nextTemp(dir_func[funcToCall].get('type'))
            add_quad('=', '', funcToCall, '(' + str(nextT) + ')')
            memoria[nextT] = 0
            add_pilaO('(' + str(nextT) + ')')
            add_pType(dir_func[funcToCall].get('type'))
        contParam = 0
    else:
        print('Error en el numero de parametros de ' + funcToCall)
        sys.exit()

def p_paramVals(p):
    '''paramVals : unParam moreParamVals
                 | empty'''


def p_moreParamVals(p):
    '''moreParamVals : TO_COMA unParam moreParamVals
                     | empty'''


def p_unParam(p):
    'unParam : ID TO_DOSPTOS megaExp'
    global funcToCall
    val = pop_pilaO()
    valType = pop_pType()
    funcTable = dir_func[funcToCall]
    try:
        result = semantic_check(funcTable['scope'][p[1]].get('type'), valType, '=')
    except KeyError:
        print('Error parametro ' + p[1] + ' no existe para la funcion ' + funcToCall)
        sys.exit()
    if result != 'error':
        global contParam
        contParam = contParam + 1
        # print('Aqui es memoria')

        add_quad('PARAM', val, '', funcToCall + ':' + p[1])
    else:
        print('Error de tipo al enviar parametro ' + p[1])
        sys.exit()


def p_return(p):
    '''return : PR_return megaExp'''
    rightOperand = pop_pilaO()
    rOP_type = pop_pType()
    result_type = semantic_check(dir_func[actual_scope].get('type'), rOP_type, '=')
    if result_type != 'error':
        add_quad('RET', '', rightOperand, '')
    else:
        print('Error de tipo al retornar en la funcion ' + actual_scope)
        sys.exit()


def p_comparacion(p):
    'comparacion : compara1 compara2'


def p_compara1(p):
    'compara1 : PR_if TO_PARABRE megaExp TO_PARCIERRA TO_LLAABRE'
    exp_type = pop_pType()
    if exp_type == 'BOOL':
        global contQuads
        resultado = pop_pilaO()
        add_quad('GOTOF', resultado, '', '')
        add_pJumps(contQuads - 1)
    else:
        print('Error de tipo en IF')
        sys.exit()


def p_compara2(p):
    'compara2 : bloque TO_LLACIERRA maybeElse'
    fin = pop_pJumps()
    global contQuads
    updateQuad(fin, 'result', contQuads)


def p_maybeElse(p):
    '''maybeElse : checkElse doElse
                 | empty'''


def p_checkElse(p):
    'checkElse : PR_else TO_LLAABRE'
    add_quad('GOTO', '', '', '')
    falso = pop_pJumps()
    global contQuads
    add_pJumps(contQuads - 1)
    updateQuad(falso, 'result', contQuads)


def p_doElse(p):
    'doElse : bloque TO_LLACIERRA'


def p_megaExp(p):
    'megaExp : maybeNot superExp anotherMega'
    top = top_pOper()
    if top == 'OR' or top == 'AND' or top == 'NOT':
        rightOperand = pop_pilaO()
        rOP_type = pop_pType()
        operator = pop_pOper()
        if operator == 'NOT':
            if rOP_type == 'BOOL':
                nextT = nextTemp(rOP_type)
                add_quad(operator, '', rightOperand, '(' + str(nextT) + ')')
                memoria[nextT] = 0
                add_pilaO('(' + str(nextT) + ')')
                add_pType('BOOL')
            else:
                print('Error de tipo en negacion')
                sys.exit()
        else:
            leftOperand = pop_pilaO()
            lOP_type = pop_pType()
            result_type = semantic_check(lOP_type, rOP_type, operator)
            if result_type != 'error':
                nextT = nextTemp(result_type)
                add_quad(operator, leftOperand, rightOperand, '(' + str(nextT) + ')')
                memoria[nextT] = 0
                add_pilaO('(' + str(nextT) + ')')
                add_pType(result_type)
            # for q in quad: print q
            # print(pType)
            else:
                print('Error de tipo en una comparacion')
                sys.exit()


def p_maybeNot(p):
    '''maybeNot : PR_negacion
                | empty'''
    if p[1] == 'NOT':
        add_pOper(p[1])


# print(pOper)

def p_anotherMega(p):
    '''anotherMega : opLogico megaExp
                   | empty'''


def p_superExp(p):
    'superExp : exp maybeRel'


# Regla de agregar operadores relacionales
def p_maybeRel(p):
    '''maybeRel : opRelacional exp
                | empty'''
    top = top_pOper()
    if top == '>' or top == '<' or top == '>=' or top == '<=' or top == '!=' or top == '==':
        rightOperand = pop_pilaO()
        rOP_type = pop_pType()
        leftOperand = pop_pilaO()
        lOP_type = pop_pType()
        operator = pop_pOper()
        result_type = semantic_check(lOP_type, rOP_type, operator)
        if result_type != 'error':
            nextT = nextTemp(result_type)
            add_quad(operator, leftOperand, rightOperand, '(' + str(nextT) + ')')
            memoria[nextT] = 0
            add_pilaO('(' + str(nextT) + ')')
            add_pType(result_type)
        # for q in quad: print q
        # print(pType)
        else:
            print('Error de tipo en una comparacion')
            sys.exit()


# Regla de agregar operadores de + y -
def p_exp(p):
    'exp : term anotherExp'
    top = top_pOper()
    if top == '+' or top == '-':
        rightOperand = pop_pilaO()
        rOP_type = pop_pType()
        leftOperand = pop_pilaO()
        lOP_type = pop_pType()
        operator = pop_pOper()
        result_type = semantic_check(lOP_type, rOP_type, operator)
        if result_type != 'error':
            nextT = nextTemp(result_type)
            add_quad(operator, leftOperand, rightOperand, '(' + str(nextT) + ')')
            memoria[nextT] = 0
            add_pilaO('(' + str(nextT) + ')')
            add_pType(result_type)
        # for q in quad: print q
        # print(pType)
        else:
            print('Error de tipo en una suma o resta')
            sys.exit()


def p_anotherExp(p):
    '''anotherExp : OP_MAS exp
                  | OP_MENOS exp
                  | empty'''
    if len(p) > 2:
        add_pOper(p[1])


# Regla de agregar operadores relacionales * / %
def p_term(p):
    'term : fact anotherTerm'
    top = top_pOper()
    if top == '*' or top == '/' or top == '%':
        rightOperand = pop_pilaO()
        rOP_type = pop_pType()
        leftOperand = pop_pilaO()
        lOP_type = pop_pType()
        operator = pop_pOper()

        result_type = semantic_check(lOP_type, rOP_type, operator)

        if result_type != 'error':
            nextT = nextTemp(result_type)
            # cont de termporales
            add_quad(operator, leftOperand, rightOperand, '(' + str(nextT) + ')')
            memoria[nextT] = 0
            add_pilaO('(' + str(nextT) + ')')
            add_pType(result_type)
        # for q in quad: print q
        # print(pType)
        else:
            print('Error de tipo en una multiplicacion, division o modulo')
            sys.exit()


def p_anotherTerm(p):
    '''anotherTerm : OP_MULT term
                   | OP_DIV term
                   | OP_RESID term
                   | empty'''
    if len(p) > 2:
        add_pOper(p[1])


def p_fact(p):
    '''fact : TO_PARABRE megaExp TO_PARCIERRA
            | funcCall
            | val'''


def p_empty(p):
    'empty :'


def p_error(p):
    global aprobado
    aprobado = False
    print("Error de sintaxis en '%s'" % p.value)
    sys.exit()


# Funcion que regresa el valor que guarda una dirección de memoria
def retrieveValueAt(address):
    if not isinstance(address, str):
        return address
    if address[0] == '(':
        address = int(address[1:len(address) - 1])
    elif address[0] == '[':
        address = retrieveValueAt((address.replace('[', '(')).replace(']', ')'))
    else:
        for func in dir_func:
            if address in dir_func.get(func).get('scope').keys():
                address = dir_func.get(func).get('scope').get(address).get('address')
    if not address in memoria.keys():
        print(str(address) + ' ' + str(currentQuad))
        print('Variable no inicializada')
        sys.exit()
    return memoria.get(address)


# Funcion de utilidad que transforma un string (1800)
# en un numero 1800 para que pueda ser accesado el valor correspondiente
def translateString(address):
    if not isinstance(address, str):
        return address
    if address[0] == '(':
        address = int(address[1:len(address) - 1])
    elif address[0] == '[':
        address = retrieveValueAt((address.replace('[', '(')).replace(']', ')'))
    else:
        for func in dir_func:
            if address in dir_func.get(func).get('scope').keys():
                address = dir_func.get(func).get('scope').get(address).get('address')
    if not address in memoria.keys():
        for r in memoria:
            print(str(r) + ':' + str(memoria.get(r)))
        print(address)
        print('Variable no inicializada')
        sys.exit()
    return address

# Máquina virtual
# Ejecuta los códigos de operación.
def maqVirtual():
    global currentQuad
    while currentQuad < contQuads:
        executeQuad = quad[currentQuad]
        operation = executeQuad.get('operator')
        if operation == 'GOTO':
            if currentQuad == 0:
                global memFunc
                dicTemp = {}
                ogMem = memFunc
                for var in dir_func['MAIN']['scope']:
                    dir_func['MAIN']['scope'][var]['address'] = memFunc
                    dicTemp[var] = memFunc
                    memoria[memFunc] = 0
                    memFunc = memFunc + 1
                    if len(dir_func['MAIN']['scope'][var]['dim']) > 0:
                        cant = 1
                        for i in dir_func['MAIN']['scope'][var]['dim']:
                            cant = cant * i.get('Lim')
                        for i in range(cant - 1):
                            memoria[memFunc] = 0
                            memFunc = memFunc + 1
                memFunc = ogMem + 1000
                add_pFunc('MAIN')
                add_pVar(dicTemp)
            currentQuad = executeQuad.get('result')
        elif operation == 'GOTOF':
            mem = executeQuad.get('leftOperand')
            val = retrieveValueAt(mem)
            if not val:
                currentQuad = executeQuad.get('result')
            else:
                currentQuad = currentQuad + 1
        elif operation == 'GOSUB':
            func = executeQuad.get('leftOperand')
            dicVars = top_pVar()
            for var in dicVars:
                dir_func[func]['scope'][var]['address'] = dicVars.get(var)
            add_pilaReturn(currentQuad + 1)
            currentQuad = dir_func[func].get('quadStart')
        elif operation == 'ERA':
            right = executeQuad.get('rightOperand')
            dicTemp = {}
            ogMem = memFunc
            for var in dir_func[right]['scope']:
                dicTemp[var] = memFunc
                memoria[memFunc] = 0
                memFunc = memFunc + 1
                if len(dir_func[right]['scope'][var]['dim']) > 0:
                    cant = 1
                    for i in dir_func[right]['scope'][var]['dim']:
                        cant = cant * i.get('Lim')
                    for i in range(cant - 1):
                        memoria[memFunc] = 0
                        memFunc = memFunc + 1
            memFunc = ogMem + 1000
            add_pFunc(right)
            add_pVar(dicTemp)
            currentQuad = currentQuad + 1
        elif operation == 'PARAM':
            left = retrieveValueAt(executeQuad.get('leftOperand'))
            func, var = executeQuad.get('result').split(":")
            dicVars = top_pVar()
            memoria[dicVars.get(var)] = left
            currentQuad = currentQuad + 1
        elif operation == 'ENDPROC':
            pop_pVar()
            pop_pFunc()
            dicVars = top_pVar()
            func = top_pFunc()
            if func != 'MAIN':
                for var in dicVars:
                    dir_func[func]['scope'][var]['address'] = dicVars.get(var)
            currentQuad = pop_pilaReturn()
        elif operation == 'RET':
            right = retrieveValueAt(executeQuad.get('rightOperand'))
            memoria[dir_func['global']['scope'][top_pFunc()].get('address')] = right
            currentQuad = currentQuad + 1
        elif operation == 'VER':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            rightval = retrieveValueAt(right)
            if not (leftval >= 1 and leftval <= rightval):
                print(currentQuad)
                for r in memoria:
                    print(str(r) + ':' + str(memoria.get(r)))
                print('Error el indice se sale del limite')
                sys.exit()
            currentQuad = currentQuad + 1
        elif operation == 'DIRBASE':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            cosas = right.split('/')
            result = executeQuad.get('result')
            result = result.replace('[', '(')
            result = result.replace(']', ')')
            result = translateString(result)
            memoria[result] = leftval + dir_func[cosas[0]]['scope'][cosas[1]].get('address')
            currentQuad = currentQuad + 1
        elif operation == 'calculaRegresion':
            right = executeQuad.get('result')
            # Codigo correspondiente

            currentQuad = currentQuad + 1
        elif operation == 'calculaModa':
            right = executeQuad.get('result')
            f = open(right + ".txt", "r")
            arr = f.read().split(',')
            moda = st.mode(arr)
            print("La moda es igual a " + str(moda))
            f.close()
            currentQuad = currentQuad + 1
        elif operation == 'calculaMediana':
            right = executeQuad.get('result')
            f = open(right + ".txt", "r")
            arr = f.read().split(',')
            mediana = st.median(map(float, arr))
            print("La mediana es igual a " + str(mediana))
            f.close()
            currentQuad = currentQuad + 1
        elif operation == 'calculaMedia':
            right = executeQuad.get('result')
            f = open(right + ".txt", "r")
            arr = f.read().split(',')
            media = st.mean(map(float, arr))
            print("La media es igual a " + str(media))
            f.close()
            currentQuad = currentQuad + 1
        elif operation == 'calculaPoisson':
            right = executeQuad.get('result')
            f = open(right + ".txt", "r")
            par1 = f.readline()
            par2 = f.readline()
            s = np.random.poisson(int(par1), int(par2))
            count, bins, ignored = plt.hist(s, 14, density=True)
            plt.show()
            f.close()
            print("llega")
            currentQuad = currentQuad + 1
        elif operation == 'calculaBinomial':
            right = executeQuad.get('result')
            f = open(right + ".txt", "r")
            par1 = f.readline()
            par2 = f.readline()
            par3 = f.readline()
            par4 = f.readline()
            s = np.random.binomial(int(par1), float(par2), int(par3))
            count, bins, ignored = plt.hist(s, 14, density=True, color='m')
            plt.title(par4)
            plt.show()
            currentQuad = currentQuad + 1
        elif operation == 'calculaNormal':
            right = executeQuad.get('result')
            f = open(right + ".txt", "r")
            par1 = f.readline()  # mu
            par2 = f.readline()  # desv est
            par3 = f.readline()  # tamaño
            par4 = f.readline()  # titulo
            s = np.random.normal(float(par1), float(par2), int(par3))
            # Verificae la media y la varianza:
            bInt = abs(float(par1) - np.mean(s)) < 0.01
            bInt2 = abs(float(par2) - np.std(s, ddof=1)) < 0.01
            if bInt:
                if bInt2:
                    count, bins, ignored = plt.hist(s, 20, normed=True)
                    plt.plot(bins, 1 / (float(par2) * np.sqrt(2 * np.pi)) * np.exp(
                        - (bins - float(par1)) ** 2 / (2 * float(par2) ** 2)), linewidth=2, color='r')
                    plt.title(par4)
                    plt.show()
            else:
                print("Media y la varianza mayores a 0.01")
            print("llegue normal")
            currentQuad = currentQuad + 1
        elif operation == 'PRINT':
            left = executeQuad.get('leftOperand')
            print("Console prints: " + str(retrieveValueAt(left)))
            currentQuad = currentQuad + 1
        elif operation == '+':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = leftval + rightval
            currentQuad = currentQuad + 1
        elif operation == '-':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = leftval - rightval
            currentQuad = currentQuad + 1
        elif operation == '*':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = leftval * rightval
            currentQuad = currentQuad + 1
        elif operation == '/':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = leftval / rightval
            currentQuad = currentQuad + 1
        elif operation == '%':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = leftval % rightval
            currentQuad = currentQuad + 1
        elif operation == '=':
            right = executeQuad.get('rightOperand')
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = rightval
            currentQuad = currentQuad + 1
        elif operation == '<':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = leftval < rightval
            currentQuad = currentQuad + 1
        elif operation == '<=':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = leftval <= rightval
            currentQuad = currentQuad + 1
        elif operation == '>':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = leftval > rightval
            currentQuad = currentQuad + 1
        elif operation == '>=':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = leftval >= rightval
            currentQuad = currentQuad + 1
        elif operation == '==':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = leftval == rightval
            currentQuad = currentQuad + 1
        elif operation == 'AND':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = leftval and rightval
            currentQuad = currentQuad + 1
        elif operation == 'OR':
            left = executeQuad.get('leftOperand')
            right = executeQuad.get('rightOperand')
            leftval = retrieveValueAt(left)
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = leftval or rightval
            currentQuad = currentQuad + 1
        elif operation == 'NOT':
            right = executeQuad.get('rightOperand')
            rightval = retrieveValueAt(right)
            result = translateString(executeQuad.get('result'))
            memoria[result] = not rightval
            currentQuad = currentQuad + 1


parser = yacc.yacc()

#fName = "fact.txt"
#fName = "fact_rec.txt"

#fName = "fibbo.txt"
#fName = "fibbo_rec.txt"

#fName = "binsearch.txt"
#fName = "find.txt"

#fName = "sort.txt"

#fName = "multmat.txt"

fName = "funcPred.txt"


with open(fName, 'r') as myfile:
	s = myfile.read().replace('\n', '')

parser.parse(s)
maqVirtual()

# print de memoria
# for r in memoria:
#    print(str(r) + ':' + str(memoria.get(r)))

# print de directorio de funciones
#print(dir_func)

# Code to display all found tokens ######
# lexer.input(s)
# print("List of Tokens: ")
# while True:
#    tok = lexer.token()
#    if not tok:
#        break
#    print(tok)

if aprobado == True:
    print("Archivo aprobado")
    sys.exit()
else:
    print("Archivo no aprobado")
    sys.exit()



