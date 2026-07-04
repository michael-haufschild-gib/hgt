#!/usr/bin/env python3
"""
Certified window reader (doc 76 SS4 next-object (b)) — rigorous ball arithmetic
via python-flint/ARB (acb). Run with the scratchpad venv python (python-flint
installed there); archive output as certified_reader.out + certificate JSON.

Produces MACHINE CERTIFICATES (rigorous, outward-rounded ball bounds — not
floating-point estimates) for the hypotheses of the Lean capstone
`anneal_mod_two_window_relation_of_domination` (AnnealWindowRelation.lean) on
the #136-run windows. All certificates at RAW carrier level (zeta vs g5); the
machine-checked `completed_domination_iff` bridges raw domination to the
completed-level hdom pointwise, and empty zero sets make the peeling data
trivial (empty product; h := the carrier itself, nonvanishing by C1/C2).

CERTIFICATES (window B, a = 1/2 + 220.0i, r0 = 0.15, R = 0.30):
  C1: zeta has NO zeros in the closed ball(a, R)      [box covering, |ball| > 0]
  C2: g5 has NO zeros in the closed ball(a, R)        [box covering, |ball| > 0]
  C3: |zeta - g5| < |g5| on the closed annulus r0 <= |z-a| <= R  [box covering,
      strict ball inequality per box]  — superset of chartRA ∪ chartLA.
  => every hypothesis of the Lean capstone holds for t1 = t2 = ∅ with hL = (0≡0):
     the zero-free window instance is CERTIFIED end to end.

CERTIFICATE (window A, the #136 pair — the t2/m2 datum):
  C4: interval-Newton box around rho = 0.6094...+221.0788...i: the Newton
      operator N(X) = x0 - g5(x0)/g5'(X) maps the box strictly into itself
      => exactly one zero of g5 in X, and it is SIMPLE (g5' ball on X excludes 0)
      => certified configuration entry (box, multiplicity 1).
  C5: domination FAILURE witness at one chart point of window A:
      |zeta - g5| > |g5| certified at z = a + 0.16 (ball comparison).

Boxes are acb midpoints with radii; bounds are arb upper/lower bounds (rigorous
by ARB semantics). JSON manifest: certified_window_cert.json.
"""
import json
import math
from flint import acb, arb, ctx

ctx.dps = 40

T0_PAIR_RE = "0.609410680660665122128188900795"
T0_PAIR_IM = "221.078884111315925862344356455"
NTR = 5


def cball(re_mid, re_rad, im_mid, im_rad):
    return acb(arb(re_mid, re_rad), arb(im_mid, im_rad))


def chi(s):
    return acb.pi() ** (s - acb('0.5')) * (( (1 - s) / 2).gamma()) / ((s / 2).gamma())


def g5(s):
    tot = acb(0)
    for n in range(1, NTR + 1):
        tot += acb(n) ** (-s)
    tail = acb(0)
    for n in range(1, NTR + 1):
        tail += acb(n) ** (s - 1)
    return tot + chi(s) * tail


def g5prime(s):
    # d/ds [n^{-s}] = -log n * n^{-s};  chi' = chi * (log pi - psi((1-s)/2)/2 - psi(s/2)/2)
    d1 = acb(0)
    for n in range(1, NTR + 1):
        d1 += -acb(n).log() * acb(n) ** (-s)
    tail = acb(0)
    dtail = acb(0)
    for n in range(1, NTR + 1):
        tail += acb(n) ** (s - 1)
        dtail += acb(n).log() * acb(n) ** (s - 1)
    logchi_d = acb.pi().log() - ((1 - s) / 2).digamma() / 2 - (s / 2).digamma() / 2
    return d1 + chi(s) * (logchi_d * tail + dtail)


def lower_abs(ball):
    """rigorous lower bound of |ball| (arb lower of .abs_lower)."""
    return ball.abs_lower()


def upper_abs(ball):
    return ball.abs_upper()


def cover_disk(a_re, a_im, R, delta):
    """closed disk |z-a|<=R covered by square boxes of half-side delta."""
    boxes = []
    n = int(math.ceil(R / (2 * delta))) + 1
    for i in range(-n, n + 1):
        for j in range(-n, n + 1):
            cx, cy = a_re + 2 * delta * i, a_im + 2 * delta * j
            # keep box if it intersects the disk: dist(center, a) <= R + sqrt2*delta
            if math.hypot(cx - a_re, cy - a_im) <= R + 1.5 * delta:
                boxes.append((cx, cy, delta))
    return boxes


def cover_annulus(a_re, a_im, r0, R, delta):
    boxes = []
    n = int(math.ceil(R / (2 * delta))) + 1
    for i in range(-n, n + 1):
        for j in range(-n, n + 1):
            cx, cy = a_re + 2 * delta * i, a_im + 2 * delta * j
            d = math.hypot(cx - a_re, cy - a_im)
            if r0 - 1.5 * delta <= d <= R + 1.5 * delta:
                boxes.append((cx, cy, delta))
    return boxes


def certify_no_zeros(f, boxes, name):
    bad = []
    minlo = None
    for (cx, cy, d) in boxes:
        v = f(cball(cx, d, cy, d))
        lo = lower_abs(v)
        if not (lo > arb(0)):
            bad.append((cx, cy, d))
        minlo = lo if minlo is None else min(minlo, lo)
    ok = not bad
    print(f"{name}: {len(boxes)} boxes, certified |f|>0 on all: {ok}"
          f" (min lower bound {minlo})" + ("" if ok else f"  FAILED on {len(bad)}"))
    return ok, str(minlo), [list(b) for b in bad]


def certify_domination(boxes, name, max_depth=6):
    """Adaptive: ARB's zeta enclosure radius ~ 33x the box half-side at t~220,
    so wide boxes fail spuriously; bisect failing boxes up to max_depth."""
    bad = []
    margin = None
    nchecked = 0
    stack = [(cx, cy, d, 0) for (cx, cy, d) in boxes]
    while stack:
        cx, cy, d, depth = stack.pop()
        nchecked += 1
        z = cball(cx, d, cy, d)
        gz = g5(z)
        diff = z.zeta() - gz
        up, lo = upper_abs(diff), lower_abs(gz)
        if up < lo:
            m = lo - up
            margin = m if margin is None else min(margin, m)
        elif depth < max_depth:
            h = d / 2
            for sx in (-h, h):
                for sy in (-h, h):
                    stack.append((cx + sx, cy + sy, h, depth + 1))
        else:
            bad.append((cx, cy, d))
    ok = not bad
    print(f"{name}: {nchecked} boxes checked (adaptive), certified |zeta-g5|<|g5|: {ok}"
          f" (min margin over certified {margin})"
          + ("" if ok else f"  FAILED on {len(bad)} at max depth"))
    return ok, str(margin), [list(b) for b in bad]


cert = {"backend": "python-flint/ARB", "dps": 40, "raw_level_note":
        "raw-level certificates; completed_domination_iff (Lean) bridges to hdom"}

# ---------- WINDOW B ----------
print("=== WINDOW B: a = 1/2 + 220.0i, r0 = 0.15, R = 0.30 ===")
okC1, m1, bad1 = certify_no_zeros(lambda z: z.zeta(),
                                  cover_disk(0.5, 220.0, 0.30, 0.01), "C1 (zeta no-zero)")
okC2, m2, bad2 = certify_no_zeros(g5, cover_disk(0.5, 220.0, 0.30, 0.01),
                                  "C2 (g5 no-zero)")
okC3, m3, bad3 = certify_domination(cover_annulus(0.5, 220.0, 0.15, 0.30, 0.01),
                                    "C3 (domination on annulus)")
cert["windowB"] = {"a": [0.5, 220.0], "r0": 0.15, "R": 0.30,
                  "C1_zeta_no_zero": {"ok": okC1, "min_lower": m1, "failed_boxes": bad1},
                  "C2_g5_no_zero": {"ok": okC2, "min_lower": m2, "failed_boxes": bad2},
                  "C3_domination": {"ok": okC3, "min_margin": m3, "failed_boxes": bad3},
                  "lean_reading": "t1=t2=∅, m trivial, hL: 0≡0 [MOD 4]; "
                                  "all hypotheses of "
                                  "anneal_mod_two_window_relation_of_domination hold"}

# ---------- WINDOW A pair (C4) ----------
print("\n=== WINDOW A pair: interval Newton certificate ===")
x0 = acb(T0_PAIR_RE, T0_PAIR_IM)
RADX = 1e-8
X = cball(float(arb(T0_PAIR_RE)), RADX, float(arb(T0_PAIR_IM)), RADX)
fx0 = g5(x0)
fpX = g5prime(X)
NX = x0 - fx0 / fpX
# strict containment of N(X) in X: |mid offsets| + rad(NX) < RADX componentwise
dre = (NX.real - arb(T0_PAIR_RE)).abs_upper()
dim = (NX.imag - arb(T0_PAIR_IM)).abs_upper()
contained = (dre < arb(RADX)) and (dim < arb(RADX))
simple = lower_abs(fpX) > arb(0)
print(f"N(X) offsets: re {dre}, im {dim}  (box rad {RADX})")
print(f"C4: contained={contained}, g5' nonzero on X (simple)={simple}")
cert["windowA_pair"] = {"box_center": [T0_PAIR_RE, T0_PAIR_IM], "box_rad": RADX,
                        "newton_contained": bool(contained), "simple": bool(simple),
                        "lean_reading": "certified t2 entry (box, multiplicity 1) + "
                                        "mirror 1-conj(rho); m2 = 1"}

# ---------- WINDOW A domination-failure witness (C5) ----------
zA = acb('0.66', T0_PAIR_IM)  # a + 0.16 in the theta=0 direction
gzA = g5(zA)
lo_diff = lower_abs(zA.zeta() - gzA)
up_g = upper_abs(gzA)
fail_cert = lo_diff > up_g
print(f"\nC5: |zeta-g5| > |g5| at a+0.16: {fail_cert}"
      f"  (lower diff {lo_diff} vs upper |g5| {up_g})")
cert["windowA_domination_failure"] = {"point": ["0.66", T0_PAIR_IM],
                                      "ok": bool(fail_cert),
                                      "lower_diff": str(lo_diff),
                                      "upper_g5": str(up_g)}

with open("certified_window_cert.json", "w") as f:
    json.dump(cert, f, indent=1)
print("\ncertificate written: certified_window_cert.json")
print("ALL CERTIFIED:", all([okC1, okC2, okC3, bool(contained), bool(simple),
                             bool(fail_cert)]))
