import time, mpmath as mp, importlib.util
spec=importlib.util.spec_from_file_location("hb","2026-06-22-hurwitz-batch.py"); hb=importlib.util.module_from_spec(spec); spec.loader.exec_module(hb)
mp.mp.dps=500; a=mp.mpf(2)/5; s0=mp.mpf('0.5'); M=250
t=time.time(); h=hb.hurwitz_taylor(a,s0,M); tb=time.time()-t
print(f"batched: all {M+1} coeffs at dps=500 in {tb:.1f}s")
# mpmath per-order cost at a few high n (extrapolate)
t=time.time(); _=mp.zeta(s0,a,200)/mp.factorial(200); t1=time.time()-t
print(f"mpmath single high derivative (n=200) at dps=500: {t1:.2f}s  => all {M+1} ~ {t1*(M+1):.0f}s (per-order method)")
# accuracy spot-check at high n
ref=mp.zeta(s0,a,200)/mp.factorial(200); print(f"accuracy n=200: rel={mp.nstr(abs(h[200]-ref)/abs(ref),3)}")
