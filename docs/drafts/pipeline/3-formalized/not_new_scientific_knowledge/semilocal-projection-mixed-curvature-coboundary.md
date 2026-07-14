# Semilocal projection mixed curvature is a negative polarized normal Gram

- **ID:** `semilocal-projection-mixed-curvature-coboundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[VALUE-RELATION INTERFACE]`, `[TOP-DOWN GAP REDUCTION]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/SemilocalProjectionMixedCurvature.lean`
- **Parents:** `cofinite-euler-connection-reader-rigidity.md`;
  `semilocal-euler-kernel-chart-differentiability.md`;
  `sonin-prime-seam-exterior-factorization.md`
- **Statement:** For a norm-differentiable two-parameter family of self-adjoint idempotents, the
  diagonal compression of the mixed derivative is exactly the negative polarized Gram of the two
  normal first derivatives. Consequently, compact mixed curvature, and in particular a compact
  relative projection family, forces the finite two-direction normal Gram to be compact.

## Exact theorem

Let `P(s,t)` be a two-parameter family of idempotents near `(0,0)`. Write

```text
P = P(0,0),
D_s = partial_s P(0,0),
D_t = partial_t P(0,0),
D_st = partial_s partial_t P(0,0).
```

Differentiating `P(s,t)^2=P(s,t)` once gives

```text
D_s P + P D_s = D_s,
D_t P + P D_t = D_t,
P D_s P = P D_t P = 0.                                  (1)
```

Differentiating twice and compressing gives the unconditional algebraic identity

```text
P D_st P = -(P D_t D_s P + P D_s D_t P).                (2)
```

If `P`, `D_s`, and `D_t` are self-adjoint, define their normal corners

```text
N_s = (1-P) D_s P,
N_t = (1-P) D_t P.
```

The tangent equations in `(1)` identify each cross term with a normal Gram term:

```text
P D_t D_s P = N_t^* N_s,
P D_s D_t P = N_s^* N_t.                                (3)
```

Therefore Lean proves the exact mixed-curvature value relation

```text
P D_st P = -(N_t^* N_s + N_s^* N_t).                    (4)
```

This is an identity, not a sign assumption and not an RH reformulation.

## Compactness discharge

Equation `(4)` immediately gives

```text
D_st compact
  -> N_t^* N_s + N_s^* N_t compact.                      (5)
```

The module also closes the derivative input without requiring the base projection to be compact.
If the full family varies compactly relative to its base point,

```text
P(s,t) - P(0,0) compact for every s,t,                    (6)
```

then the existing norm-derivative theorem makes `D_st` compact, and `(5)` makes the polarized
normal Gram compact. Thus finite relative compactness, mixed differentiation, and normal-curvature
extraction are now one formal chain.

## Top-down consequence

The cofinite Euler connection-reader theorem reduces the semilocal source problem to compactness
on finite prime-tangent pairs. This theorem identifies the symmetric constraint sector, but a
subsequent formal calculation shows that this sector cannot carry the required orientation by
itself:

```text
mixed Hessian = -(N_t^* N_s + N_s^* N_t),
connection curvature = N_t^* N_s - N_s^* N_t.            (7)
```

The first line is a constraint. The second is the orientation-sensitive object needed by the
prime-seam exterior-factorization route. See
`semilocal-projection-constraint-orientation-splitting.md` for the formal split and its Sonin
specialization.

## Retired instantiation and corrected remaining problem

The formerly proposed compact-relative realization

```text
P_pq(s,t)-P_pq(0,0) compact,
normal derivatives = actual Sonin prime corners           (8)
```

is impossible. Norm differentiation of the first line makes each first derivative compact, hence
makes each projection normal compact, while the corpus proves every actual Sonin prime corner is
noncompact. The corrected source object must therefore vary nontrivially in the Calkin algebra at
first order.

The remaining problem is orientation-sensitive: construct a completed prime--Gamma source chart
whose compressed connection commutator has an exact zero-fibre value relation to the
charge-difference-weighted antisymmetric Sonin Gram, and prove compactness only for that completed
antisymmetric combination. This avoids requiring compactness of either raw prime normal.

## Scope and falsifiers

- The theorem does not construct `P_pq` or prove the identification in `(8)`.
- It does not assert compactness of a one-prime Euler metric corner; the corpus proves that corner
  is noncompact.
- A compact-relative chart cannot have an actual Sonin prime normal; this proposed bridge is
  formally retired rather than left as an open construction problem.
- It does not infer RH from abstract projection geometry. The arithmetic source identification is
  indispensable.
- The theorem uses no Xi zero locations, RH-equivalent positivity, limiting measure, or divisor
  selection.
- A projection family chosen only to realize prescribed normal vectors, without an exact
  prime--Gamma value formula, does not close `(8)`.

## Literature boundary

The differential identities are standard geometry of smooth projection families, within Kato's
[*Perturbation Theory for Linear Operators*](https://doi.org/10.1007/978-3-642-66282-9).
Compact relative perturbations and the induced Fredholm/essential geometry are also classical.
Connes--Consani's [*Quasi-inner functions and local factors*](https://arxiv.org/abs/2008.10974)
is the relevant source for the finite completed local-factor compactness input. The contribution
here is the precise formal interface with the existing semilocal Euler connection chain; no
novelty claim is made for the projection identity itself.

## Gates

- [x] first derivative of an idempotent has zero diagonal compression
- [x] mixed compressed derivative equals the negative symmetrized tangent product
- [x] tangent cross products equal normal Gram corners in the self-adjoint case
- [x] exact negative polarized normal-Gram identity
- [x] compact mixed derivative implies compact polarized normal Gram
- [x] compact relative family implies compact polarized normal Gram
- [x] Lean module imported by the `RHTower` umbrella
- [x] retire the impossible compact-relative actual-Sonin-normal instantiation
- [ ] construct a Calkin-varying completed prime--Gamma source chart
- [ ] prove its antisymmetric connection-curvature/source-divisor value relation
- [ ] propagate through the cofinite reader and close the RH chain
