"""Runpod-only independent ordinary-prefix checks at increased precision."""
import os
for name in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import concurrent.futures
import json
import time
import mpmath as mp


def verify(spec):
    sigma_text, n, ratio_text = spec
    digits = 130 + int(mp.ceil(mp.mpf(sigma_text))) * len(str(n))
    mp.mp.dps = digits
    sigma, ratio = mp.mpf(sigma_text), mp.mpf(ratio_text)
    t = 2*mp.pi*n*ratio
    s = mp.mpc(sigma, t)
    x = mp.mpf(n)
    prefix = mp.fsum(mp.mpf(j)**(-s) for j in range(1,n+1))
    r = prefix - mp.zeta(s) - x**(1-s)/(1-s) - x**(-s)/2
    direct = x**(mp.conj(s)+2)*mp.conj(r)/(mp.conj(s)*(mp.conj(s)+1))
    with mp.workdps(digits+40):
        sigma, ratio = mp.mpf(sigma_text), mp.mpf(ratio_text)
        u = mp.mpc(sigma, -2*mp.pi*n*ratio)
        hurwitz = x*x*(-x**u*mp.zeta(u,n+1)-x/(1-u)-mp.mpf("0.5"))/(u*(u+1))
    return {"sigma":sigma_text, "n":n, "ratio":ratio_text, "digits_direct":digits,
            "scaled_im":mp.nstr(mp.im(direct),75),
            "method_difference":mp.nstr(abs(direct-hurwitz),15)}


if __name__ == "__main__":
    started = time.time()
    initial = json.load(open("initial-fixed-precision-results.json"))
    specs = [(r["sigma"],r["n"],r["ratio_t_over_2pi_n"])
             for r in initial["rows"] if r["inside_R"] and r["positive"]]
    specs += [("0.001",512,"0.9999"),("0.5",128,"0.99"),
              ("0.5",4,"1.3"),("2",1,"0.001")]
    with concurrent.futures.ProcessPoolExecutor(max_workers=6) as pool:
        rows = list(pool.map(verify,specs))
    out = {"warning":"Numerical stability checks, not interval certificates or Lean proof inputs.",
           "methods":["ordinary finite prefix minus Riemann zeta", "Hurwitz tail at +40 digits"],
           "seconds":time.time()-started,"rows":rows}
    with open("verification.json","w") as handle:
        json.dump(out,handle,indent=2)
    print(json.dumps(out,indent=2),flush=True)
