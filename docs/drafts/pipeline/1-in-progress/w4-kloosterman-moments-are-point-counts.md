# W4 — Kloosterman moments are differences of point counts

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** For `b ≠ 0`, primitive `ψ`, and `q = #F`, the degree-`m` Kloosterman moment satisfies `(q−1)M_m = q²A_m−qB_m`, where `B_m` counts nonzero tuples with coordinate sum zero and `A_m` also imposes reciprocal sum zero.

## Proof

Scaling the summation variable gives `K(a,b)=K(ab,1)`, so `Σ_a K(a,b)^m` is independent of nonzero `b`. Summing over both parameters and applying orthogonality gives `q²A_m`. The parameter `b=0` contributes `qB_m` by the one-constraint moment identity. The other `q−1` parameters give the claimed equality.

For `m>0`, simultaneous scalar multiplication acts freely on both tuple sets. Normalizing the first coordinate to one gives counts `A'_m,B'_m` with `A_m=(q−1)A'_m`, `B_m=(q−1)B'_m`; hence `M_m=q(qA'_m−B'_m)`.

## Open arithmetic content

The identities construct explicit counting varieties for the global moments. They do not bound the difference of their point counts, construct their cohomology, or supply the corresponding ζ family.
