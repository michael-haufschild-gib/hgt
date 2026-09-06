"""Runpod-only scan of the frozen successor-cell phase threshold conjecture."""
import os
for name in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import concurrent.futures
import json
import platform
import time
import mpmath as mp


def evaluate(spec):
    sigma_text, n, ratio_text = spec
    # Hurwitz evaluation can stop at an absolute tolerance. Protect tiny n^(-sigma)
    # tails before multiplying back to unit scale.
    mp.mp.dps = 85 + int(mp.ceil(mp.mpf(sigma_text))) * len(str(n))
    sigma = mp.mpf(sigma_text)
    ratio = mp.mpf(ratio_text)
    t = 2 * mp.pi * n * ratio
    s = mp.mpc(sigma, t)
    u = mp.conj(s)
    x = mp.mpf(n)
    scaled = x*x * (-x**u * mp.zeta(u, n + 1) - x/(1-u) - mp.mpf("0.5")) / (u*(u+1))
    return {"sigma": sigma_text, "n": n, "ratio_t_over_2pi_n": ratio_text,
            "t": mp.nstr(t, 45), "scaled_re": mp.nstr(mp.re(scaled), 45),
            "scaled_im": mp.nstr(mp.im(scaled), 45),
            "inside_R": ratio < 1, "positive": mp.im(scaled) > 0}


if __name__ == "__main__":
    started = time.time()
    sigmas = ["0.001", "0.05", "0.5", "1", "2", "8", "32"]
    cutoffs = [1, 2, 4, 8, 16, 32, 64, 128, 512]
    ratios = ["0.001", "0.05", "0.15", "0.3", "0.5", "0.7", "0.9", "0.99",
              "0.9999", "1", "1.0001", "1.01", "1.1", "1.3", "1.6", "2.1"]
    specs = [(sigma, n, ratio) for sigma in sigmas for n in cutoffs for ratio in ratios]
    rows = []
    print(json.dumps({"tasks": len(specs), "workers": 8}), flush=True)
    with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:
        for row in pool.map(evaluate, specs, chunksize=1):
            rows.append(row)
            if len(rows) % 100 == 0:
                print(json.dumps({"completed": len(rows)}), flush=True)
    violations = [r for r in rows if r["inside_R"] and r["positive"]]
    outside_positive = [r for r in rows if not r["inside_R"] and r["positive"]]
    summary = {"violations": len(violations), "outside_positive": len(outside_positive),
               "examples": violations[:8], "outside_examples": outside_positive[:8]}
    output = {"warning": "Exploratory numerical data, not a proof or an interval certificate.",
              "digits": "85 + ceil(sigma) * decimal_digits(n)", "workers": 8, "python": platform.python_version(),
              "mpmath": mp.__version__, "seconds": time.time()-started,
              "summary": summary, "rows": rows}
    with open("results.json", "w") as handle:
        json.dump(output, handle, indent=2)
    print(json.dumps(summary, indent=2), flush=True)
