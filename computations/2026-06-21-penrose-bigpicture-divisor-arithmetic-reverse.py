#!/usr/bin/env python3


def monomials_total_degree(d):
    return [(a, b) for a in range(d + 1) for b in range(d + 1 - a)]


def free_normal_form(m):
    return m


def dependent_normal_form(m):
    a, b = m
    return a + 2 * b  # Y = X^2, so X^a Y^b -> X^(a+2b)


def rank_under_normal_form(monomials, normal_form):
    return len({normal_form(m) for m in monomials})


def main():
    print("Step 9 method 3: reverse orbit-stabilizer")
    print("Test whether absence of relations gives full monomial multiplicity,")
    print("while a relation creates a special-position collapse.")
    print()
    print("degree  free_rank  dependent_rank(Y=X^2)  collapse")
    for d in range(1, 8):
        mons = monomials_total_degree(d)
        free_rank = rank_under_normal_form(mons, free_normal_form)
        dep_rank = rank_under_normal_form(mons, dependent_normal_form)
        print(f"{d:6d}  {free_rank:9d}  {dep_rank:22d}  {free_rank - dep_rank:8d}")
    print()
    print("degree 3 dependent collisions:")
    buckets = {}
    for m in monomials_total_degree(3):
        buckets.setdefault(dependent_normal_form(m), []).append(m)
    for key, vals in sorted(buckets.items()):
        if len(vals) > 1:
            print(f"  X^{key}: {vals}")


if __name__ == "__main__":
    main()
