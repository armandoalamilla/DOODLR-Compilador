import matplotlib.pyplot as plt
import numpy as np


f = open("normal.txt", "r")
par1 = f.readline() #mu
par2 = f.readline() #desv est
par3 = f.readline() #tamaño
par4 = f.readline() #titulo

#mu, sigma = 0, 0.2 # mean and standard deviation
s = np.random.normal(float(par1), float(par2) , int(par3))

#Verificae la media y la varianza:

bInt = abs(float(par1) - np.mean(s)) < 0.01
bInt2 = abs(float(par2)- np.std(s, ddof=1)) < 0.01



if bInt:

	if bInt2:
		count, bins, ignored = plt.hist(s, 20, normed=True)
		plt.plot(bins, 1/(float(par2)* np.sqrt(2 * np.pi)) * np.exp( - (bins - float(par1))**2 / (2 * float(par2)**2) ),linewidth=2, color='r')
		plt.title(par4)
		plt.show()
	
	
else:
	print("Media y la varianza mayores a 0.01")



