#!/usr/bin/env python3.13
"""MWM winding engine (campaign R1/R2, docs/drafts/rh-monodromy-weight-mismatch/03).

Rectangle-contour winding counts via adaptive argument tracking (no derivatives).
Self-checks: xi(2)=pi/6, xi FE residual, D-H banked-zero residual, before any claim.

Subcommands:
  validate                 R1: zeta boxes [-1,2]x[T,T+5] vs mp.nzeros counts + xi sanity
  dh-banked                R2a step 1: banked D-H zero residual + winding on a tight box
  dh-sweep T1 T2 [CHUNK]   R2a step 2: seed sweep, boxes sigma in [0.55,1.2], height 2
Output: JSON lines. Archive stdout under computations/mwm/.
"""
import sys, json
from mpmath import mp, mpc, mpf, pi, gamma, zeta, arg, sqrt, power, fabs

mp.dps = 30

# ---------- objects ----------

def kappa():
    return (sqrt(10 - 2*sqrt(5)) - 2) / (sqrt(5) - 1)

# chi mod 5 with chi(2)=i (2 is a primitive root: 2,4,3,1)
CHI = {1: mpc(1, 0), 2: mpc(0, 1), 3: mpc(0, -1), 4: mpc(-1, 0)}

def L_chi(s, conjugate=False):
    tot = mpc(0)
    for a in (1, 2, 3, 4):
        c = CHI[a].conjugate() if conjugate else CHI[a]
        tot += c * zeta(s, mpf(a) / 5)
    return power(5, -s) * tot

def f_dh(s):
    k = kappa()
    return (1 - 1j * k) / 2 * L_chi(s) + (1 + 1j * k) / 2 * L_chi(s, True)

def f_zeta(s):
    return zeta(s)

def f_xi(s):
    return s * (s - 1) / 2 * power(pi, -s / 2) * gamma(s / 2) * zeta(s)

# ---------- winding via adaptive argument tracking ----------

class ContourZero(Exception):
    pass

def _dphi(f, p0, v0, p1, v1, depth, stats):
    if fabs(v0) < mpf(10) ** (-mp.dps + 5) or fabs(v1) < mpf(10) ** (-mp.dps + 5):
        raise ContourZero
    d = arg(v1 / v0)
    if fabs(d) < mp.pi / 2:
        return d
    if depth <= 0:
        stats["unresolved"] += 1
        return d
    pm = (p0 + p1) / 2
    vm = f(pm)
    stats["evals"] += 1
    return _dphi(f, p0, v0, pm, vm, depth - 1, stats) + _dphi(f, pm, vm, p1, v1, depth - 1, stats)

def winding(f, s1, s2, t1, t2, per_edge=16, max_depth=16, nudge=mpf("1e-3"), tries=3):
    """Winding number of f around rectangle [s1,s2]x[t1,t2], counterclockwise.
    Retries with a slightly nudged box if the contour hits a (near-)zero."""
    for attempt in range(tries):
        stats = {"evals": 0, "unresolved": 0}
        corners = [mpc(s1, t1), mpc(s2, t1), mpc(s2, t2), mpc(s1, t2), mpc(s1, t1)]
        try:
            total = mpf(0)
            for c0, c1 in zip(corners, corners[1:]):
                pts = [c0 + (c1 - c0) * mpf(i) / per_edge for i in range(per_edge + 1)]
                vals = [f(p) for p in pts]
                stats["evals"] += len(vals)
                for i in range(per_edge):
                    total += _dphi(f, pts[i], vals[i], pts[i + 1], vals[i + 1], max_depth, stats)
            w = total / (2 * mp.pi)
            wr = int(mp.nint(w))
            ok = fabs(w - wr) < mpf("1e-6") and stats["unresolved"] == 0
            return {"w": wr, "raw": float(w), "ok": bool(ok), **stats,
                    "box": [float(s1), float(s2), float(t1), float(t2)]}
        except ContourZero:
            t1, t2 = t1 + nudge, t2 + nudge
            continue
    return {"w": None, "ok": False, "reason": "contour-zero after retries",
            "box": [float(s1), float(s2), float(t1), float(t2)]}

# ---------- self-checks ----------

def selfcheck_xi():
    out = {}
    out["xi2_vs_pi_over_6"] = float(fabs(f_xi(mpc(2)) - pi / 6))
    res = mpf(0)
    for s in (mpc("0.3", "7.2"), mpc("1.7", "-3.1"), mpc("0.51", "14.1")):
        res = max(res, fabs(f_xi(s) - f_xi(1 - s)))
    out["xi_fe_residual"] = float(res)
    out["pass"] = out["xi2_vs_pi_over_6"] < 1e-25 and out["xi_fe_residual"] < 1e-22
    return out

BANKED_DH_ZERO = mpc("0.808517182456637386", "85.6993484853775922")

def selfcheck_dh():
    out = {"kappa": float(kappa())}
    out["banked_zero_residual"] = float(fabs(f_dh(BANKED_DH_ZERO)))
    # 18-digit zero => |f| <~ |f'| * 1e-18; accept 1e-14 margin
    out["pass"] = out["banked_zero_residual"] < 1e-14
    return out

# ---------- runs ----------

def run_validate():
    print(json.dumps({"selfcheck_xi": selfcheck_xi()}), flush=True)
    for T in (10, 50, 100, 500):
        w = winding(f_zeta, -1, 2, T, T + 5, per_edge=24)
        try:
            from mpmath import nzeros
            expected = int(nzeros(T + 5)) - int(nzeros(T))
        except Exception as e:
            expected = None
        print(json.dumps({"run": "validate", "T": T, "winding": w,
                          "expected_nzeros": expected,
                          "match": (expected is not None and w["ok"] and w["w"] == expected)}),
              flush=True)

def run_dh_banked():
    print(json.dumps({"selfcheck_dh": selfcheck_dh()}), flush=True)
    z = BANKED_DH_ZERO
    d = mpf("0.02")
    w = winding(f_dh, z.real - d, z.real + d, z.imag - d, z.imag + d, per_edge=20)
    print(json.dumps({"run": "dh-banked", "zero": [float(z.real), float(z.imag)],
                      "winding": w, "parity_odd": (w["w"] is not None and w["w"] % 2 == 1)}),
          flush=True)

def run_dh_sweep(t1, t2, chunk=25):
    H = mpf(2)
    T = mpf(t1)
    n = 0
    while T < mpf(t2) and n < chunk:
        w = winding(f_dh, mpf("0.55"), mpf("1.2"), T, T + H, per_edge=20)
        if w["w"] not in (0, None):
            print(json.dumps({"run": "dh-sweep", "DEFECT": True, "winding": w}), flush=True)
        else:
            print(json.dumps({"run": "dh-sweep", "T": float(T), "w": w["w"], "ok": w["ok"]}),
                  flush=True)
        T += H
        n += 1
    print(json.dumps({"run": "dh-sweep", "done_upto": float(T)}), flush=True)

if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "validate"
    if cmd == "validate":
        run_validate()
    elif cmd == "dh-banked":
        run_dh_banked()
    elif cmd == "dh-sweep":
        run_dh_sweep(sys.argv[2], sys.argv[3], int(sys.argv[4]) if len(sys.argv) > 4 else 25)
    else:
        print(json.dumps({"error": "unknown subcommand", "cmd": cmd}))
        sys.exit(1)
