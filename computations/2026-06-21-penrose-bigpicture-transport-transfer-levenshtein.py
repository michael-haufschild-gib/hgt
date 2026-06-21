#!/usr/bin/env python3


def levenshtein(a, b):
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


original = (
    "Flat U(1) circle connections have zero curvature; local coefficients change "
    "under gauge shifts, but holonomy is the transport invariant."
)

attempts = {
    "A_affine_weld_holonomy": (
        "The affine weld connection has universal curvature; local A and P coefficients "
        "change under gauge/passport shifts, but holonomy is the transport invariant."
    ),
    "B_phase_delta_projection": (
        "The scalar phase defect Delta changes as a projected local coefficient; "
        "source holonomy is the invariant transport object."
    ),
    "C_kappa_index_transport": (
        "The completed carrier has local logarithmic coefficients, but the faithful "
        "negative index is the transport invariant."
    ),
}


def main():
    print("Step 8 transfer attempts scored by Levenshtein distance")
    print("Original NODE test:")
    print(original)
    print()
    rows = sorted((levenshtein(original, text), name, text) for name, text in attempts.items())
    for dist, name, text in rows:
        print(f"{name}: distance={dist}")
        print(text)
        print()
    print(f"Chosen transfer by minimum distance: {rows[0][1]}")


if __name__ == "__main__":
    main()
