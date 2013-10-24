#! /usr/bin/env python3

import sys

l = float(sys.argv[1])
s = float(sys.argv[2])

e1 = 6.7   * l +  3.0 * s
e2 = 8.8   * l +  5.0 * s
e3 = 11.0  * l +  7.0 * s

e4 = 69.2  * l +  4.7 * s
e5 = 148.5 * l + 10.4 * s
e6 = 230.4 * l + 18.3 * s

print("%result expect   diff")

print("%7.1f %7.1f %7.1f" % (e1,  837, e1- 837))
print("%7.1f %7.1f %7.1f" % (e2, 1858, e2-1858))
print("%7.1f %7.1f %7.1f" % (e3, 3232, e3-3232))

print("%7.1f %7.1f %7.1f" % (e4, 1139, e4-1139))
print("%7.1f %7.1f %7.1f" % (e5, 2479, e5-2479))
print("%7.1f %7.1f %7.1f" % (e6, 4225, e6-4225))



