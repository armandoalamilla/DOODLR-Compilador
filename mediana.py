import statistics as st 


archivo = open("mediana.txt", "r")
arr1 = archivo.read().split(',')



mediana1 = st.median(map(float, arr1))

print("La mediana es igual a " + str(mediana1))

archivo.close()
