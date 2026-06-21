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
    "Position multiplicity is constrained by orbit-stabilizer: generic points "
    "have full orbit, special positions have larger stabilizer and smaller multiplicity."
)

attempts = {
    "A_relation_stabilizer": (
        "Divisor arithmetic is constrained by relation-stabilizer: generic values "
        "have full algebraic orbit, special value tuples have larger relation stabilizer."
    ),
    "B_fe_orbit_multiplicity": (
        "Zero geometry is constrained by FE orbit multiplicity: generic off-line zeros "
        "have full quartet orbit, seam zeros have folded multiplicity."
    ),
    "C_corank_trdeg_collapse": (
        "Value arithmetic is constrained by corank-trdeg collapse: generic multiplier logs "
        "have trdeg equal corank, special arithmetic logs have algebraic stabilizers."
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
