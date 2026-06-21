#!/usr/bin/env python3


def levenshtein(a, b):
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


original = (
    "Continue a log germ around a closed chain by overlapping power series; "
    "valid overlaps recover the integer monodromy, invalid jumps diverge, "
    "and the same endpoint may carry a different germ."
)

attempts = {
    "A_contour_winding": (
        "Continue d log xi around a closed contour; valid contours recover "
        "an integer winding/off-line count, invalid zero-crossing jumps break "
        "the certificate, and the same endpoint may carry different holonomy."
    ),
    "B_matrix_cover": (
        "Glue a cover of local finite carrier matrices; require Sylvester "
        "negative inertia to agree on overlaps, then read a global kappa index "
        "instead of a trace."
    ),
    "C_density_defect": (
        "Scan density windows with one rare inserted defect; compare averaged "
        "density with an integer defect counter and test whether the density "
        "misses the defect."
    ),
}


def main():
    print("Step 8 transfer attempts scored by Levenshtein distance")
    print("Original NODE test:")
    print(original)
    print()
    rows = []
    for name, text in attempts.items():
        rows.append((levenshtein(original, text), name, text))
    for dist, name, text in sorted(rows):
        print(f"{name}: distance={dist}")
        print(text)
        print()
    best = min(rows)
    print(f"Chosen transfer by minimum distance: {best[1]}")


if __name__ == "__main__":
    main()
