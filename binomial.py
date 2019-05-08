import matplotlib
import matplotlib.colors
import matplotlib.pyplot as plt
import numpy as np

f = open("binomial.txt", "r")
par1 = f.readline()
par2 = f.readline()
par3 = f.readline()
par4 = f.readline()
s = np.random.binomial(int(par1), float(par2),int(par3))
count, bins, ignored = plt.hist(s, 14, density=True, color='m')


plt.title(par4)

plt.show()