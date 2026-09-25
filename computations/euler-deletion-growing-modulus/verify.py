"""Runpod-only independent high-precision tail representation check."""
import os
for name in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import concurrent.futures
import json
import mpmath as mp

def packed(value):
    return [str(mp.re(value)), str(mp.im(value))]

def w_value(s, p, head, order):
    t = mp.conj(s)
    a = 2 * mp.re(s)
    c = mp.power(p, 1 - s)
    total = 0
    for n in range(1, head + 1):
        x = mp.mpf(p * n)
        remainder = -mp.zeta(t, x + 1) - mp.power(x, 1 - t) / (1 - t) - mp.power(x, -t) / 2
        total += mp.power(n, -s) * remainder
    total *= c
    for k in range(1, order + 1):
        coefficient = -mp.bernoulli(2 * k) * mp.rf(t, 2 * k - 1) / mp.factorial(2 * k)
        total += coefficient * mp.power(p, 2 - a - 2 * k) * mp.zeta(a + 2 * k - 1, head + 1)
    return total

def task(row):
    mp.mp.dps = 65
    s = mp.mpc(row["spec"]["sigma"], row["height_65_digits"])
    sigma = mp.re(s)
    a = 2 - 2 * sigma
    zs = mp.zeta(s)
    K = mp.zeta(2 * sigma - 1) / (1 - mp.conj(s))
    w1a = w_value(s, 1, 128, 8)
    w1 = w_value(s, 1, 128, 12)
    identity_error = mp.re(w1) + abs(zs) ** 2 / 2 + mp.re(K)
    comparisons = []
    for item in row["rows"]:
        p = item["p"]
        if p not in (16, 32, 1024, 8192):
            continue
        wp = w_value(s, p, 8, 12)
        B = -mp.log(p) / 2 if sigma == mp.mpf("0.5") else mp.zeta(2 * sigma) * mp.expm1((1 - 2 * sigma) * mp.log(p)) / 2
        predicted = abs(zs) ** 2 * (mp.power(p, 1 - s) - 1) + K * (mp.power(p, a) - 1) + B + wp - w1
        observed = mp.mpc(*item["observations"][-1]["estimate"])
        wp_leading = -mp.conj(s) * mp.zeta(2 * sigma + 1) / (12 * mp.power(p, 2 * sigma))
        comparisons.append({"p": p, "predicted": packed(predicted), "observed": packed(observed),
                            "discrepancy": str(abs(predicted - observed)), "W_p": packed(wp),
                            "W_p_minus_first_term": packed(wp - wp_leading)})
    answer = {"label": row["spec"]["label"], "W1": packed(w1),
              "tail_order_8_vs_12_drift": str(abs(w1 - w1a)),
              "real_W1_identity_error": str(identity_error), "comparisons": comparisons}
    print(answer["label"], "Re W1 identity error", answer["real_W1_identity_error"], flush=True)
    return answer

if __name__ == "__main__":
    with open("results.json") as source:
        data = json.load(source)
    with concurrent.futures.ProcessPoolExecutor(max_workers=4) as pool:
        output = list(pool.map(task, data["results"]))
    with open("verification.json", "w") as out:
        json.dump({"digits": 65, "workers": 4, "head_W1": 128, "orders": [8, 12],
                   "note": "High-precision checks with asymptotic tails, not rigorous intervals", "results": output}, out, indent=2)
