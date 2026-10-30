# Rigidity at the minimum Adams multiplicity support

- **ID:** AHA-EQUALITY
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Statement:** For `d,r≥1`, an arithmetic auxiliary supported on `1≤n≤2^(dr)` with full multiplicity at least `r` on the order-`d` prime torsion locus is a scalar multiple of `(χ(2)^d−1)^r`.

The boundary polynomial has top coefficient one. Subtracting the top
coefficient times this polynomial would leave an auxiliary below `2^(dr)`
with the same multiplicity constraints. The strict support theorem should
then force the remainder to vanish. The required formal interface transports
point-ideal powers between the coordinate sets before and after removing
the endpoint; `dr=1` also removes the prime-two coordinate.

For integer coefficients this classification would fix the coefficient
height at minimum support. It makes no assertion about height after enlarging
support, where multiplication can change cancellation and coefficient norms.
No novelty claim is made for the subtraction principle. The precise arithmetic
extremizer classification and its Lean proof remain to be audited.
