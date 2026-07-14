# Semilocal projection geometry splits into constraint and orientation sectors

- **ID:** `semilocal-projection-constraint-orientation-splitting`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[VALUE-RELATION INTERFACE]`, `[TOP-DOWN GAP CORRECTION]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/SemilocalProjectionConstraintOrientation.lean`
- **Parents:** `semilocal-projection-mixed-curvature-coboundary.md`;
  `sonin-prime-seam-exterior-factorization.md`;
  `sonin-place-transition-cutoff-dichotomy.md`
- **Statement:** A self-adjoint projection family has independent symmetric constraint and
  antisymmetric orientation sectors. The latter is its compressed connection commutator and is
  exactly the skew normal Gram. Actual Sonin prime normals are necessarily Calkin-visible, so they
  cannot arise from a compact-relative projection chart.

## Exact identities

Let `P` be a self-adjoint idempotent and let `D_s,D_t` be self-adjoint tangents,

```text
D_s P + P D_s = D_s,
D_t P + P D_t = D_t.
```

Put

```text
N_s = (1-P) D_s P,
N_t = (1-P) D_t P.
```

The mixed-Hessian module already proves

```text
P D_st P = -(N_t^* N_s + N_s^* N_t).                    (1)
```

The new module defines the compressed connection curvature

```text
Omega_P(D_s,D_t) = P(D_t D_s - D_s D_t)P                (2)
```

and proves

```text
Omega_P(D_s,D_t) = N_t^* N_s - N_s^* N_t.               (3)
```

Consequently one oriented product is recovered by the exact constraint--orientation split

```text
N_t^* N_s = (1/2)(-P D_st P + Omega_P(D_s,D_t)).         (4)
```

Equation `(1)` is the symmetric constraint sector. Equation `(3)` is the skew orientation sector.
A mixed derivative alone cannot recover the sign-sensitive prime-seam coboundary.

## Actual Sonin specialization

Lean identifies the projection normal corner with the existing cutoff-cross-boundary operator:

```text
projectionNormalCorner P D = crossBoundary P D.          (5)
```

For the central Sonin projection and the prime dilation sum this is the actual prime corner
`B_p`. Hence, whenever two abstract tangent normals are identified with actual `p`- and `q`-Sonin
corners, `(3)` becomes

```text
Omega_P(D_q,D_p) = B_p^* B_q - B_q^* B_p
                  = Q_pq - Q_qp.                         (6)
```

This is the operator shape required by the antisymmetric source-divisor formula in
`sonin-prime-seam-exterior-factorization.md`; it is not produced by the symmetric Hessian.

The ambient Sonin corner has the exact principal--residual decomposition

```text
B_p = P_p + R_p,
R_p in the concrete time-band ideal.                       (6a)
```

The new module expands both cross-prime products and proves the stronger ideal-valued identity

```text
(B_p^*B_q-B_q^*B_p)-(P_p^*P_q-P_q^*P_p)
  lies in the concrete time-band ideal, hence is compact.  (6b)
```

Thus the full and formal-principal skew Grams have the same Calkin class. The residual passage in
the finite-pair route is now formally discharged; the remaining value relation may use whichever
representative is exposed by the completed prime--Gamma formula.

## Essential transversality

Suppose a norm-differentiable operator family `F(t)` satisfies

```text
F(t)-F(0) compact for every t.                            (7)
```

Then its derivative is compact, so every projection normal corner of that derivative is compact.
But the actual Sonin prime corner `B_p` is unconditionally noncompact. Lean therefore proves:

```text
projectionNormalCorner P (F'(0)) = B_p
  -> exists t, F(t)-F(0) is noncompact.                   (8)
```

It also proves the two-parameter diagonal obstruction:

```text
N_s = N_t = B_p
  -> D_st is noncompact.                                  (9)
```

The positive content is that actual prime directions are essentially transverse: a source chart
realizing them must move nontrivially in the Calkin algebra at first order. Compactness can only
appear after an arithmetic combination of different directions.

## Corrected top-down chain

The viable chain is now sharply isolated:

```text
[OPEN VALUE RELATION]
completed prime--Gamma zero-fibre connection curvature
  = charge-difference-weighted finite Sonin skew Gram modulo compacts
+ completed antisymmetric curvature is compact
-> replace full skew Gram by its principal skew Gram, or conversely, using (6b)
-> finite Sonin Gram coefficient matrix is zero
   by the existing finite Calkin injectivity theorem
-> every pair of Xi prime-seam charges is equal
-> the common charge vanishes by the formalized cofinal prime decay
-> RH.                                                     (10)
```

This chain does not require a compact-relative raw projection family. It asks for compactness of
the completed, charge-weighted antisymmetric curvature only.

## Exact open problem

Use the explicit source-defined Euler chart and its arithmetic connection contraction from
`semilocal-dual-pair-euler-connection-source-law.md`, extend it by the archimedean conductor on the
analytically continued prime--Gamma fibre, and prove the operator value relation

```text
completed Omega_pq
  = sum_{r,s in finite support}
      ((a_r(rho)-a_s(rho))/sqrt(r s)) L_r^* L_s
    modulo compact operators.                             (11)
```

The finite prime connection coefficients are now fixed as `-L_p'/L_p`; they are not an open input.
The coefficients in `(11)` must still come from the actual zero-fibre reflection formula. Freely
prescribing tangent normals, or assuming the desired seam-charge equality, is circular. The hard
step is the cutoff/resolvent prime--Gamma/reflection identification and the cancellation making its
completed skew combination compact.

## Scope and falsifiers

- No Xi zero location, real-rootedness, anti-Herglotz positivity, limiting divisor measure, or RH
  equivalent sign assumption is used.
- The module does not prove compactness of `completed Omega_pq` or the value relation `(11)`.
- It does not claim a raw Sonin prime corner is compact; it proves the opposite obstruction.
- Symmetric mixed curvature cannot substitute for `(11)`, because it erases the orientation sign.
- A chart that is compact relative to its base is ruled out if its normal is an actual Sonin prime
  corner.
- The principal--residual replacement is proved only modulo the concrete time-band ideal; it does
  not manufacture the source-defined completed curvature.

## Literature boundary

The algebra of tangent projections and compressed connection curvature belongs to the classical
geometry of projection/Grassmann connections; Kato's
[*Perturbation Theory for Linear Operators*](https://doi.org/10.1007/978-3-642-66282-9) is a
standard operator-theoretic reference. Connes--Consani's
[*Quasi-inner functions and local factors*](https://arxiv.org/abs/2008.10974) supplies the relevant
completed local-factor compactness setting, but does not identify a raw Sonin prime normal as a
compact-relative derivative. No novelty claim is made for `(1)`--`(4)`.

## Gates

- [x] identify projection normal corner with cutoff cross-boundary
- [x] prove connection curvature equals the skew normal Gram
- [x] prove the constraint--orientation reconstruction formula
- [x] specialize the skew curvature to actual Sonin prime quadratic corners
- [x] prove full and formal-principal cross-prime skew Grams have the same Calkin class
- [x] prove actual Sonin prime normals force Calkin-visible variation
- [x] prove the same-prime mixed derivative obstruction
- [x] import the Lean module through the `RHTower` umbrella
- [ ] construct the completed source-defined antisymmetric connection curvature
- [ ] prove the prime--Gamma zero-fibre value relation `(11)`
- [ ] deduce seam-charge coherence and close RH
