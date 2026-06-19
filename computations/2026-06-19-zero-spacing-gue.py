#!/usr/bin/env python3
# Spacing-ratio test (Atas et al 2013, parameter-free) of the Riemann zeros.
# r_n = min(s_n,s_{n+1})/max(s_n,s_{n+1}), s_n = gamma_{n+1}-gamma_n.
# GUE (chaotic): <r>=0.60266 ; Poisson (integrable): <r>=0.38629. Local, no runpod.
import mpmath as mp
mp.mp.dps = 25
N = 160
g = [mp.im(mp.zetazero(n)) for n in range(1, N + 1)]
sp = [g[i+1] - g[i] for i in range(len(g) - 1)]
r = [min(sp[i], sp[i+1]) / max(sp[i], sp[i+1]) for i in range(len(sp) - 1)]
mean_r = sum(r) / len(r)
print("N=%d  <r>=%s  (GUE 0.60266 / Poisson 0.38629)" % (N, mp.nstr(mean_r, 6)))
print("verdict: %s" % ("GUE/chaotic" if abs(mean_r-mp.mpf('0.60266')) < abs(mean_r-mp.mpf('0.38629')) else "Poisson"))
