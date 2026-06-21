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
    "Same projected branch value, different sheet-level monodromy cycle data; "
    "base projection count is blind to ramified preimage count and cycle type."
)

attempts = {
    "A_scalar_delta_source_lift": (
        "Same projected scalar Delta event, different source-level carrier data; "
        "scalar projection is blind to source multiplicity and holonomy type."
    ),
    "B_cross_sigma_lanes": (
        "Same finite-Euler amplitude lane, different cross-sigma association graph; "
        "amplitude projection is blind to coupled-lane transport."
    ),
    "C_krein_index_blocks": (
        "Same measured zero density, different Krein carrier blocks; "
        "density projection is blind to negative-index multiplicity."
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
