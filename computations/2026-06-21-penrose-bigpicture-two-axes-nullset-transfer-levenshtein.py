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
    "Null-set modification leaves measure-algebra dynamics unchanged, "
    "but changes the named exceptional orbit completely."
)

attempts = {
    "A_realization_vs_faithful_index": (
        "Realization-axis data can remain unchanged, but the faithful positivity index "
        "changes on a density-zero exceptional zero."
    ),
    "B_carrier_source_defect": (
        "Average carrier data can remain unchanged, but a source-carrying defect changes "
        "the exceptional contour count."
    ),
    "C_value_axis_exception": (
        "Geometric divisor data can remain unchanged, but an arithmetic relation changes "
        "the exceptional value-axis type."
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
