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
    "Gibbs rare states have invariant probability p, recurrence time about 1/p, "
    "and finite trajectories miss them with probability (1-p)^N."
)

attempts = {
    "A_sparse_resonance_sampling": (
        "Sparse positivity resonances have effective weight p, detection scale about 1/p, "
        "and finite grids miss them without a lower-bound guard."
    ),
    "B_source_measure_average": (
        "The zero source measure has rare charged regions; ensemble averages exist, "
        "but time averages cannot replace a source-built positivity transfer."
    ),
    "C_adaptive_event_contours": (
        "Rare defects require adaptive event-certified contours; fixed samples miss them "
        "even when the all-scale index is nonzero."
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
