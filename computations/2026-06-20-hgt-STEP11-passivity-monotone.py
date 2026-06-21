import numpy as np


def quartet(a, t=14.1):
    return [0.5 - a + 1j * t, 0.5 + a - 1j * t, 0.5 + a + 1j * t, 0.5 - a - 1j * t]


def fe_symmetric(zeros, tol=1e-9):
    unused = list(zeros)
    while unused:
        z = unused.pop()
        target = 1.0 - z
        found = None
        for i, w in enumerate(unused):
            if abs(w - target) <= tol:
                found = i
                break
        if found is None:
            return False
        unused.pop(found)
    return True


print("STEP11 passivity-vs-detailed-balance monotone")
print("Method #13: find a monotone quantity.")
print("FE balance is held fixed; horizontal off-line displacement a controls the passivity/ergotropy proxy.")
print("a       FE_balance  off_line_count  ergotropy_proxy")
for a in np.linspace(0.0, 0.25, 11):
    zeros = quartet(float(a))
    off = sum(abs(z.real - 0.5) > 1e-12 for z in zeros)
    proxy = sum((z.real - 0.5) ** 2 for z in zeros)
    print(f"{a:0.3f}   {str(fe_symmetric(zeros)):10s} {off:14d} {proxy:15.8f}")
