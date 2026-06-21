#!/usr/bin/env python3
"""THE-MACHINE tick: spectral-triple domain invariance -> corank shadow.

NODE:
  Domain issues for an unbounded D are not cosmetic: invariance of dense
  domains under algebra actions often matters.

Consolidated target:
  The corank infinity-minus-one -- the seam as one number.

STEP 9 method:
  4. Change the viewpoint.
"""

from __future__ import annotations

import math

import numpy as np


NODE = (
    "domain issues for the unbounded operator D are not cosmetic invariance "
    "of dense domains under algebra actions often matters"
)

TRANSFER_ATTEMPTS = [
    "finite corank windows are not cosmetic invariance under prime log algebra actions matters",
    "corank one number shadow must preserve the domain under prime multiplication",
    "finite prime log relation domains can look closed but leak under the unbounded seam action",
]


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[j - 1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


def node_operator_rows() -> list[str]:
    lines = ["STEP 6 NODE TEST: bounded action vs domain-breaking action"]
    lines.append(
        "Hilbert model: D e_n = n e_n. A good shift S maps Dom(D) to itself "
        "and has bounded commutator. A bounded sparse map B e_n = e_{n^2}/sqrt(n) "
        "has bounded operator norm but its commutator grows with cutoff, "
        "signaling domain failure."
    )
    lines.append("N norm_S comm_S norm_B comm_B test_Dx test_DBx")
    for n in [16, 32, 64, 128, 256]:
        # Exact cutoff norms. For S e_k=e_{k+1}, ||S||=1 and
        # ||[D,S]||=1. For B e_k=e_{k^2}/sqrt(k), ||B||=1 and
        # ||[D,B]|| = max_k (k^2-k)/sqrt(k).
        norm_s = 1.0
        norm_comm_s = 1.0
        norm_b = 1.0
        norm_comm_b = max((k * k - k) / math.sqrt(k) for k in range(1, n + 1))

        # Test vector x_k = 1/(k^(3/2) log(k+1)). Then x is in Dom(D)
        # in the infinite model, but D B x has partial norm
        # sqrt(sum 1/log(k+1)^2), which diverges.
        test_dx = math.sqrt(
            sum(1.0 / (k * math.log(k + 1) ** 2) for k in range(1, n + 1))
        )
        test_dbx = math.sqrt(
            sum(1.0 / (math.log(k + 1) ** 2) for k in range(1, n + 1))
        )
        lines.append(
            f"{n:03d} {norm_s:.3f} {norm_comm_s:.3f} "
            f"{norm_b:.3f} {norm_comm_b:.3f} {test_dx:.4f} {test_dbx:.4f}"
        )
    lines.append(
        "NODE verdict: finite cutoffs can hide the issue if one only checks "
        "boundedness of the action. The growing commutator/domain image is the "
        "real constraint."
    )
    return lines


def monomial_dim(n_primes: int, degree: int) -> int:
    return math.comb(n_primes + degree, degree)


def internal_fraction_same_primes(n_primes: int, degree: int) -> float:
    # Domain: all monomials of total degree <= degree in n_primes variables.
    # Multiplication by one of the existing prime-log variables stays inside
    # iff the monomial had degree <= degree-1. Count ratio is T/(N+T).
    if degree == 0:
        return 0.0
    return math.comb(n_primes + degree - 1, degree - 1) / math.comb(n_primes + degree, degree)


def transfer_rows() -> list[str]:
    lines = ["\nSTEP 7 FORMULA CHECK"]
    lines.append(
        "The NODE domain-invariance test does not apply unchanged to corank: "
        "the transfer must use the prime-log relation/monomial domain, not a "
        "generic operator cutoff."
    )
    lines.append("\nSTEP 8 LEVENSHTEIN TRANSFER CANDIDATES")
    scored = []
    for i, attempt in enumerate(TRANSFER_ATTEMPTS, 1):
        d = levenshtein(NODE, attempt)
        scored.append((d, i, attempt))
        lines.append(f"{i}. distance={d} normalized={d / max(len(NODE), len(attempt)):.4f}: {attempt}")
    d, i, chosen = min(scored)
    lines.append(f"chosen={i}: {chosen}")

    lines.append("\nSTEP 9 METHOD 4: CHANGE THE VIEWPOINT")
    lines.append(
        "Old viewpoint: finite graded corank window reports a rank/corank "
        "inside a box of N prime logs and degree <= T. New viewpoint: treat "
        "that box as a domain and ask whether multiplication by prime-log "
        "generators leaves it invariant."
    )
    lines.append(
        "N T dim_window internal_existing_prime leak_existing_prime "
        "leak_new_prime boundary_regime"
    )
    for n in [2, 3, 5, 10, 20, 50, 100]:
        for t in [1, 2, 3, 5, 10]:
            dim = monomial_dim(n, t)
            internal = internal_fraction_same_primes(n, t)
            leak = 1.0 - internal
            # Multiplying by a prime outside the cutoff always leaves the
            # finite N-prime domain.
            leak_new = 1.0
            regime = "prime-first-boundary" if leak > 0.5 else "degree-rich"
            lines.append(
                f"{n:03d} {t:02d} {dim:10d} {internal:.6f} "
                f"{leak:.6f} {leak_new:.1f} {regime}"
            )
    lines.append(
        "\nTransfer verdict before Step 11: for fixed degree T, the internal "
        "fraction under existing-prime multiplication is T/(N+T), so the leak "
        "tends to 1 as N grows. Finite graded corank windows are therefore "
        "boundary-dominated domains unless degree grows with prime cutoff."
    )
    return lines


def main() -> None:
    out: list[str] = []
    out.append("THE-MACHINE tick: domain invariance -> corank infinity-minus-one")
    out.append(f"NODE: {NODE}")
    out.append("Standing-order target: 4/32 corank infinity-minus-one")
    out.extend(node_operator_rows())
    out.extend(transfer_rows())
    print("\n".join(out))


if __name__ == "__main__":
    main()
