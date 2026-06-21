#!/usr/bin/env python3


def cycles(perm):
    seen = [False] * len(perm)
    out = []
    for i in range(len(perm)):
        if seen[i]:
            continue
        cyc = []
        j = i
        while not seen[j]:
            seen[j] = True
            cyc.append(j + 1)
            j = perm[j] - 1
        out.append(tuple(cyc))
    return out


def stats(perm):
    cyc = cycles(perm)
    nontrivial = [c for c in cyc if len(c) > 1]
    defect = sum(len(c) - 1 for c in nontrivial)
    moved = sum(len(c) for c in nontrivial)
    return {
        "cycles": cyc,
        "ramified_preimages": len(nontrivial),
        "moved_sheets": moved,
        "total_ramification_defect": defect,
    }


def main():
    cases = {
        "one_transposition": [2, 1, 3, 4],
        "two_transpositions_same_projection": [2, 1, 4, 3],
        "one_three_cycle_same_projection": [2, 3, 1, 4],
        "one_four_cycle_same_projection": [2, 3, 4, 1],
    }

    print("NODE test: same base branch value, different sheet-level monodromy")
    print("degree=4 covers; projected branch-value count is 1 in every row")
    print()
    for name, perm in cases.items():
        s = stats(perm)
        print(name)
        print(f"  permutation={perm}")
        print(f"  cycle_decomposition={s['cycles']}")
        print("  base_projection_count=1")
        print(f"  ramified_preimages_over_that_value={s['ramified_preimages']}")
        print(f"  moved_sheets={s['moved_sheets']}")
        print(f"  total_ramification_defect=sum(e-1)={s['total_ramification_defect']}")
        print()

    print("comparison")
    print("  one base branch value does not determine the number of ramified preimages.")
    print("  total defect 2 can mean two simple ramification points or one 3-cycle.")


if __name__ == "__main__":
    main()
