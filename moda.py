import statistics as st 


archivo = open("arch.txt", "r")
arr1 = archivo.read().split(',')


moda1 = st.mode(arr1)

print("La moda es igual a " + str(moda1))

archivo.close()
