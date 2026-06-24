#!/usr/bin/env python3
"""
echolocation x immune-system x clock-sync, method=strengthen (seed 797825051725134353).
Costas arrays = permutations whose displacement vectors are all distinct (sonar/radar
ranging codes). STRENGTHEN: among Costas arrays, count those with extra DIHEDRAL symmetry
(the 8-element symmetry group of the square: rotations/reflections that fix the Costas set).

Instrument check: total Costas counts must match OEIS A008404 (n=1..: 1,2,4,12,40,116,200,444,...).
Then report the symmetry-class breakdown and look for a clean pattern (conjecture-from-data).
"""
import sys

def costas_count_and_symmetry(n):
    # backtracking enumeration; per-gap sets of row-differences (difference-triangle rows distinct)
    perm = [0]*n
    used = [False]*(n+1)
    arrays = []
    # gap_seen[g] = set of differences p_{i+g}-p_i already used for that gap
    def bt(col, gap_seen):
        if col == n:
            arrays.append(tuple(perm))
            return
        for r in range(1, n+1):
            if used[r]:
                continue
            ok = True
            newdiffs = []
            for g in range(1, col+1):
                d = r - perm[col-g]
                if d in gap_seen[g]:
                    ok = False; break
                newdiffs.append((g, d))
            if ok:
                for (g, d) in newdiffs:
                    gap_seen[g].add(d)
                perm[col] = r; used[r] = True
                bt(col+1, gap_seen)
                used[r] = False
                for (g, d) in newdiffs:
                    gap_seen[g].discard(d)
    bt(0, [set() for _ in range(n+1)])

    # symmetry: a Costas array as a set of points {(i, perm[i])}, i=0..n-1 (0-indexed grid n x n)
    # dihedral group D4 acting on the grid [0,n-1]^2. Count arrays fixed by >1 symmetry.
    def as_set(p):
        return frozenset((i, p[i]) for i in range(n))
    def apply_sym(pts, k):
        m = n-1
        out = []
        for (x, y) in pts:
            if k == 0: nx, ny = x, y                 # id
            elif k == 1: nx, ny = m-x, y             # vertical flip
            elif k == 2: nx, ny = x, m-y             # horizontal flip
            elif k == 3: nx, ny = m-x, m-y           # 180
            elif k == 4: nx, ny = y, x               # transpose
            elif k == 5: nx, ny = m-y, x             # rot90
            elif k == 6: nx, ny = y, m-x             # rot270
            elif k == 7: nx, ny = m-y, m-x           # anti-transpose
            out.append((nx, ny))
        return frozenset(out)
    total = len(arrays)
    sets = [as_set(p) for p in arrays]
    setpool = set(sets)
    sym_counts = {}  # number of D4 elements fixing the array -> how many arrays
    nontrivial = 0
    for s in sets:
        fix = sum(1 for k in range(8) if apply_sym(s, k) == s)
        sym_counts[fix] = sym_counts.get(fix, 0) + 1
        if fix > 1:
            nontrivial += 1
    return total, nontrivial, sym_counts

print(f"{'n':>2} {'Costas':>8} {'symmetric':>10}  sym-class-breakdown(|stab|:count)")
known = {1:1,2:2,3:4,4:12,5:40,6:116,7:200,8:444,9:995,10:2160,11:4368,12:17828}
for n in range(1, 13):
    total, nontriv, sc = costas_count_and_symmetry(n)
    flag = "" if known.get(n) == total else f"  <-- MISMATCH known={known.get(n)}"
    print(f"{n:>2} {total:>8} {nontriv:>10}  {dict(sorted(sc.items()))}{flag}")
    sys.stdout.flush()
print("\nInstrument check: totals vs OEIS A008404 (flagged if mismatch).")
print("Strengthen result: the symmetric-Costas counts per n -- pattern? known sequence?")
