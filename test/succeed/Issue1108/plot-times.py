#!/usr/bin/env python3
from agdatime import *
import matplotlib.pyplot as plt

data = read_times("times/")

case = sys.argv[1]

d = data[case]

plt.title(case)
plt.subplot(111)
plt.subplots_adjust(right=0.7)
for module, profile in sorted(d.items(), 
                              key = lambda x: 
                                -max([ v for v in x[1].values()])):
    r = sorted(profile.items())
    n = [n for n,_ in r]
    v = [1+v for _,v in r]

    plt.plot(n, v, label = module)

plt.legend(bbox_to_anchor=(1.05, 1), loc=2, borderaxespad=0.)
plt.show()




