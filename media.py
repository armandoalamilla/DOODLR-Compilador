import statistics as st 


archivo = open("media.txt", "r")
arr1 = archivo.read().split(',')



media1 = st.mean(map(float, arr1))

print("La media es igual a " + str(media1))

archivo.close()
