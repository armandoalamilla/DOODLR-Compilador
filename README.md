# DOODLR-Compilador
MANUAL DE USUARIO 

-Antes de correr el compilador es necesario tener instalado Python 3 y las librerias de SciPy
-Correr este comando ***python -m pip install --user numpy scipy matplotlib ipython jupyter pandas sympy nose***
-Ejecutar los programas modificando el fName.

***¿Como hacer un programa?***

-Asi es la declaración:

PROGRAM {
	variables aqui

	MAIN {
		codigo aqui

		END -- marca el fin de la función
	}
}

***¿Como declarar las variables?***

-Las variables se declaran en el formato VAR TIPO ID.
-Los arreglos se declarana asi VAR TIPO ID [] y  VAR TIPO ID [][].

***¿Como declarar funciones?***

FUNC TIPO ID(parametros...)
{
	codigo aqui...
	END
}

una llamada se ve asi:

ejemplo = algo(x:30,c:5,...	)

***¿Como se hacen los if?***
-Los if son parecidos a los de C/C++

IF (A==B OR A<=B)
{
	codigo
}
ELSE {
	codigo
	END
}

***¿Como se hacen los ciclos?***

LOOP(numero)
{
	codigo
	END
}

***¿Como se gráfica y/o hace los calculos estadisticos?***
Se editan los archivos (parametros) segun la función a usar y se pone cualquiera de estas funciones:
calculaGamma(gamma)
calculaMedia(media)
calculaPoisson(pruebapois)
calculaNormal(normal)
calculaBinomial(binomial)
calculaModa(moda)
calculaMediana(mediana)




