#!/usr/bin/env python3
"""
R33: discount parallel transport -> faithful-index transport normalization gate.

NODE side: discounting is parallel transport; closed-loop discount products
are gauge-invariant while edge prices are gauge-dependent.

HGT side: a faithful index must be transported by congruence, which preserves
inertia. Non-covariant damping/coarse-graining can erase a sparse negative
square even when the source matrix still looks close in measured norms.
"""

import math
import random
from typing import Dict, List, Sequence, Tuple


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def jacobi_eigenvalues(a: List[List[float]], tol: float = 1e-12, max_iter: int = 20000) -> List[float]:
    n = len(a)
    mat = [row[:] for row in a]
    for _ in range(max_iter):
        p, q = 0, 1
        max_off = 0.0
        for i in range(n):
            for j in range(i + 1, n):
                if abs(mat[i][j]) > max_off:
                    max_off = abs(mat[i][j])
                    p, q = i, j
        if max_off < tol:
            break
        app, aqq, apq = mat[p][p], mat[q][q], mat[p][q]
        tau = (aqq - app) / (2.0 * apq)
        t = math.copysign(1.0 / (abs(tau) + math.sqrt(1.0 + tau * tau)), tau)
        c = 1.0 / math.sqrt(1.0 + t * t)
        s = t * c
        for k in range(n):
            if k != p and k != q:
                mkp = mat[k][p]
                mkq = mat[k][q]
                mat[k][p] = mat[p][k] = c * mkp - s * mkq
                mat[k][q] = mat[q][k] = s * mkp + c * mkq
        mat[p][p] = app - t * apq
        mat[q][q] = aqq + t * apq
        mat[p][q] = mat[q][p] = 0.0
    return sorted(mat[i][i] for i in range(n))


def inertia(a: List[List[float]], eps: float = 1e-8) -> Tuple[int, int, int, float]:
    vals = jacobi_eigenvalues(a)
    neg = sum(1 for x in vals if x < -eps)
    zero = sum(1 for x in vals if abs(x) <= eps)
    pos = sum(1 for x in vals if x > eps)
    return neg, zero, pos, vals[0]


def matmul_diag_congruence(d: Sequence[float], h: List[List[float]]) -> List[List[float]]:
    n = len(h)
    return [[d[i] * h[i][j] * d[j] for j in range(n)] for i in range(n)]


def hadamard_damp(h: List[List[float]], lam: float) -> List[List[float]]:
    n = len(h)
    return [[math.exp(-lam * abs(i - j)) * h[i][j] for j in range(n)] for i in range(n)]


def frob_norm(a: List[List[float]], b: List[List[float]]) -> float:
    return math.sqrt(sum((a[i][j] - b[i][j]) ** 2 for i in range(len(a)) for j in range(len(a))))


def node_discount_test() -> Dict[str, object]:
    # Edge log-discounts on triangle A->B->C and direct A->C.
    log_d_ab = -0.021
    log_d_bc = -0.019
    log_d_ac = -0.037
    loop = log_d_ab + log_d_bc - log_d_ac
    # Gauge/numeraire potentials at nodes.
    phi = {"A": 0.13, "B": -0.04, "C": 0.08}

    def gauge(edge_log: float, src: str, dst: str) -> float:
        return edge_log + phi[dst] - phi[src]

    g_ab = gauge(log_d_ab, "A", "B")
    g_bc = gauge(log_d_bc, "B", "C")
    g_ac = gauge(log_d_ac, "A", "C")
    g_loop = g_ab + g_bc - g_ac
    flat_ac = log_d_ab + log_d_bc
    flat_loop = log_d_ab + log_d_bc - flat_ac
    return {
        "loop_log_curvature": loop,
        "gauge_loop_log_curvature": g_loop,
        "flat_loop_log_curvature": flat_loop,
        "edge_change_max": max(abs(g_ab - log_d_ab), abs(g_bc - log_d_bc), abs(g_ac - log_d_ac)),
        "arbitrage_return": math.exp(loop) - 1.0,
    }


def build_sparse_negative_carrier(n: int = 12) -> List[List[float]]:
    # Positive background plus a sparse alternating source vector that creates
    # one small negative square.
    h = [[0.0 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        h[i][i] = 1.0
    u = [1.0 / math.sqrt(n) for _ in range(n)]
    v = [0.0 for _ in range(n)]
    for idx, sign in [(1, 1.0), (4, -1.0), (7, 1.0), (10, -1.0)]:
        v[idx] = sign / 2.0
    # Orthogonalize v against u so the negative mode is not a mean/trace mode.
    dot = sum(ui * vi for ui, vi in zip(u, v))
    v = [vi - dot * ui for ui, vi in zip(u, v)]
    norm = math.sqrt(sum(vi * vi for vi in v))
    v = [vi / norm for vi in v]
    alpha = 1.08
    beta = 0.10
    for i in range(n):
        for j in range(n):
            h[i][j] += beta * u[i] * u[j] - alpha * v[i] * v[j]
    return h


def transfer_choice() -> Dict[str, object]:
    base = """
for each path edge:
    transport=edge_discount
loop_curvature=sum_logs_around_closed_loop
test: node gauge changes edges but preserves loop curvature
"""
    attempts = {
        "A_index_congruence_transport": """
for a source carrier H:
    transported = D H D
invariant = inertia(transported)
test: proper discount transport preserves kappa, noncovariant damping can erase it
""",
        "B_trace_discount_measure": """
for a source carrier H:
    measured_trace=sum_i w_i H_ii
test: discount weights change measured positivity and can hide dust
""",
        "C_contour_discount_integral": """
for rectangles R:
    weighted_charge = integral w(s) xi'/xi ds
test: nonconstant discount weights break contour charge invariance
""",
    }
    distances = {name: levenshtein(base, text) for name, text in attempts.items()}
    return {"distances": distances, "chosen": min(distances, key=distances.get)}


def hgt_transfer_test() -> Dict[str, object]:
    h = build_sparse_negative_carrier()
    base_inertia = inertia(h)
    n = len(h)
    d = [math.exp(-0.05 * i) for i in range(n)]
    transported = matmul_diag_congruence(d, h)
    transported_inertia = inertia(transported)
    trace_rows = []
    for lam in [-0.30, -0.10, 0.0, 0.10, 0.30, 0.60]:
        weights = [math.exp(-lam * i) for i in range(n)]
        measured_trace = sum(weights[i] * h[i][i] for i in range(n)) / sum(weights)
        trace_rows.append((lam, measured_trace))
    lam_rows = []
    for lam in [0.0, 0.02, 0.05, 0.10, 0.20, 0.40, 0.80, 1.20]:
        damped = hadamard_damp(h, lam)
        lam_rows.append((lam, inertia(damped), frob_norm(h, damped)))
    return {
        "base_inertia": base_inertia,
        "transported_inertia": transported_inertia,
        "trace_rows": trace_rows,
        "lam_rows": lam_rows,
    }


def step12_followup(trials: int = 24) -> Dict[str, object]:
    rng = random.Random(33002)
    h = build_sparse_negative_carrier()
    congruence_failures = 0
    damping_thresholds = []
    for _ in range(trials):
        d = [math.exp(rng.uniform(-1.2, 1.2)) for _ in range(len(h))]
        if inertia(matmul_diag_congruence(d, h))[0] != inertia(h)[0]:
            congruence_failures += 1
        # Randomly damp by increasing lambda; record first loss of negative square.
        first_loss = None
        for k in range(81):
            lam = k * 0.02
            if inertia(hadamard_damp(h, lam))[0] == 0:
                first_loss = lam
                break
        damping_thresholds.append(first_loss)
    return {
        "congruence_failures": congruence_failures,
        "damping_threshold_min": min(x for x in damping_thresholds if x is not None),
        "damping_threshold_max": max(x for x in damping_thresholds if x is not None),
        "trials": trials,
    }


def main() -> None:
    node = node_discount_test()
    choice = transfer_choice()
    hgt = hgt_transfer_test()
    follow = step12_followup()

    print("R33 DISCOUNT_FAITHFUL_INDEX")
    print("NODE_RESULT")
    for key, value in node.items():
        print(f"  {key}={value}")

    print("STEP8_LEVENSHTEIN")
    for name, dist in sorted(choice["distances"].items(), key=lambda kv: kv[1]):
        print(f"  {name}: {dist}")
    print(f"  chosen={choice['chosen']}")

    print("HGT_TRANSFER_RESULT")
    print(f"  base_inertia_neg_zero_pos_min={hgt['base_inertia']}")
    print(f"  congruence_transported_inertia={hgt['transported_inertia']}")
    print("  discount_weighted_trace lam measured_trace")
    for lam, measured_trace in hgt["trace_rows"]:
        print(f"  trace_lambda={lam:.2f} measured_trace={measured_trace:.9f}")
    print("  lambda damping_inertia frob_distance")
    for lam, iner, dist in hgt["lam_rows"]:
        print(f"  lambda={lam:.2f} inertia={iner} frob={dist:.9f}")

    print("STEP9_METHOD_RESULT")
    print("  method=12 find an invariant")
    print("  invariant=closed-loop discount curvature on NODE; inertia/kappa under congruence on HGT")
    print("  chosen_transfer=trace discount measure; congruence is the invariant contrast")

    print("STEP12_FOLLOWUP")
    print(f"  congruence_failures={follow['congruence_failures']}/{follow['trials']}")
    print(f"  damping_threshold_min={follow['damping_threshold_min']}")
    print(f"  damping_threshold_max={follow['damping_threshold_max']}")

    print("INTERPRETATION")
    print(
        "  The chosen trace-discount transfer is measured, not faithful: all tested weighted traces "
        "stay positive while the carrier has one negative square. Proper discount transport is "
        "gauge/congruence data and preserves the faithful index; non-covariant damping can erase it. "
        "A source-built kappa pipeline needs a transport-normalization passport."
    )


if __name__ == "__main__":
    main()
