#!/usr/bin/env python3


def partitions(n, max_part=None):
    if max_part is None or max_part > n:
        max_part = n
    if n == 0:
        yield []
        return
    for first in range(min(max_part, n), 0, -1):
        for rest in partitions(n - first, first):
            yield [first] + rest


def scalar_passport(cycle_type):
    fixed = sum(1 for c in cycle_type if c == 1)
    nontrivial = sum(1 for c in cycle_type if c > 1)
    moved = sum(c for c in cycle_type if c > 1)
    defect = sum(c - 1 for c in cycle_type if c > 1)
    return (fixed, nontrivial, moved, defect)


def main():
    print("Step 9 method 2: attack projection-blindness as false")
    print("Try scalar passports richer than base branch-value count.")
    print("passport=(fixed sheets, nontrivial cycles, moved sheets, total defect)")
    print()
    for n in range(2, 11):
        buckets = {}
        for part in partitions(n):
            key = scalar_passport(part)
            buckets.setdefault(key, []).append(tuple(part))
        collisions = [(key, vals) for key, vals in buckets.items() if len(vals) > 1]
        if collisions:
            print(f"degree={n}: scalar passport collisions found")
            for key, vals in collisions[:4]:
                print(f"  passport={key}: cycle_types={vals}")
            print()
            break
    else:
        print("No collisions found up to degree 10.")

    print("degree-6 explicit collision:")
    for part in [(4, 2), (3, 3)]:
        print(f"  cycle_type={part}, passport={scalar_passport(part)}")


if __name__ == "__main__":
    main()
