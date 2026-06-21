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
    "Brownian paths have no tangent flow; local oscillation and quadratic variation "
    "are the replacement measurable objects."
)

attempts = {
    "A_source_variation": (
        "The completed object has no generative differential flow; source-current "
        "variation of log transport is the replacement measurable object."
    ),
    "B_value_coefficient_variation": (
        "The value axis has no finite recurrence flow; coefficient-relation variation "
        "of Stieltjes data is the replacement arithmetic object."
    ),
    "C_completion_correction": (
        "Smooth approximations miss correction terms; Gamma completion is the correction "
        "that makes the constrained object measurable."
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
