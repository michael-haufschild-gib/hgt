#!/usr/bin/env python3
# MACHINE STEP11 wild experiment (no predictable outcome). Metaphor: Fisher nondegeneracy = identifiability
# = NO flat direction; Gamma's Bohr-Mollerup constraint = log-convexity = POSITIVE Fisher metric (logGamma)''=psi'.
# The "Fisher-degeneracy / non-identifiable locus" of the logGamma statistical geometry = ZEROS of trigamma psi'(z).
# psi'(z)=sum 1/(z+k)^2 > 0 for all real z (Gamma log-convex on reals) => locus is PURELY COMPLEX. Where is it?
# Method#4 (change viewpoint / reflect): also view the locus under z -> 1-z and compare to digamma's zeros.
import mpmath as mp
mp.mp.dps = 25

def find_zeros(f, box_re, box_im, nre=14, nim=12):
    roots=[]
    for i in range(nre):
        for j in range(nim):
            re = box_re[0] + (box_re[1]-box_re[0])*i/(nre-1)
            im = box_im[0] + (box_im[1]-box_im[0])*j/(nim-1)
            if abs(im)<1e-6: continue
            try:
                z = mp.findroot(f, mp.mpc(re,im))
            except Exception:
                continue
            if box_re[0]-1 < z.real < box_re[1]+1 and abs(z.imag) < box_im[1]+1:
                if all(abs(z-r)>1e-6 for r in roots):
                    if abs(f(z))<1e-12:
                        roots.append(z)
    return sorted(roots, key=lambda z:(round(float(z.real),4), round(float(z.imag),4)))

trig = lambda z: mp.polygamma(1,z)     # psi'(z) = Fisher metric of logGamma-as-potential
dig  = lambda z: mp.polygamma(0,z)     # psi(z)  = digamma (the dual coordinate); its zeros = stationary pts of logGamma

print("=== STEP11: Fisher-degeneracy locus = zeros of trigamma psi'(z) (logGamma info-geometry) ===")
zt = find_zeros(trig, (-5,2), (0.01,4))
zt = [z for z in zt if z.imag>0]   # conjugate pairs; list upper half
print(f"  trigamma psi'(z) zeros (upper half-plane), {len(zt)} found:")
for z in zt[:12]:
    print(f"    z = {mp.nstr(z,8)}   |psi'(z)|={mp.nstr(abs(trig(z)),3)}")

print("\n=== method#4 (change viewpoint): digamma psi(z) zeros (stationary pts of logGamma) for comparison ===")
zd = find_zeros(dig, (-6,3), (0.01,4))
zd=[z for z in zd if z.imag>0]
print(f"  digamma psi(z) complex zeros (upper half), {len(zd)} found:")
for z in zd[:8]:
    print(f"    z = {mp.nstr(z,8)}")
# the known real digamma zero (psi(x0)=0 at x0~1.4616, the Gamma minimum)
x0 = mp.findroot(lambda x: mp.polygamma(0,x), 1.46)
print(f"  (real digamma zero = Gamma's minimum: x0 = {mp.nstr(x0,8)})")

print("\n=== interpret: structure of the degeneracy locus? (method#4: reflect z->1-z) ===")
for z in zt[:6]:
    print(f"    trigamma zero z={mp.nstr(z,6)} ; reflection 1-z={mp.nstr(1-z,6)} ; |psi'(1-z)|={mp.nstr(abs(trig(1-z)),3)}")
