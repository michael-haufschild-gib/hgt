# Continuous-aperture tangent Loewner closure

- **ID:** `continuous-aperture-tangent-loewner-closure`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (Lean) / SOURCE-GEOMETRY GAP CLOSURE
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/XiMobiusContinuousApertureTangentLoewnerLimit.lean`
- **Parent:**
  `../needs-audit/xi-mobius-continuous-aperture-szego-metric.md`
- **Statement:** Every normalized positive-mesh Möbius aperture Gram lies below its exact Cauchy
  tangent Gram in Loewner order.  This composes the already formalized one-step dyadic innovation
  positivity with the already formalized all-prime tangent limit and closes the global matrix form
  of equation `(23)` on every finite positive aperture packet.

## Law

For a positive mesh width `h`, a positive finite aperture packet `a_i`, and

```text
M_h(i,j)=K(h a_i,h a_j)/h,
T(i,j)=C_M a_i a_j/(a_i+a_j),
```

the target is

```text
T-M_h >= 0                                               (1)
```

in positive-semidefinite matrix order.

## Proof

The formalized dyadic innovation theorem gives

```text
M_(u/2)-M_u >= 0                                        (2)
```

for every `u>0`.  Induction and addition of positive-semidefinite matrices therefore give

```text
M_(h 2^(-n))-M_h >= 0                                   (3)
```

for every natural `n`.

Since `h 2^(-n)` tends to zero through positive values, the formalized all-prime Cauchy tangent
law gives entrywise convergence

```text
M_(h 2^(-n))(i,j) -> T(i,j).                            (4)
```

For every finite vector `x`, finite summation transports `(4)` to convergence of quadratic forms.
The quadratic forms in `(3)` are nonnegative, and the nonnegative real cone is closed, so their
limit is the quadratic form of `T-M_h` and is nonnegative.  Both kernels are symmetric, hence
`T-M_h` is Hermitian.  This proves `(1)`.

The proof is unconditional and uses no numerical computation.  It does not prove the missing
source-to-Xi contraction; it identifies the exact positive source-side projection defect which
such a contraction would have to respect.

## Gates

- [x] paper identity and dependency chain audited
- [x] one-step dyadic Loewner theorem exists in Lean
- [x] all-prime Cauchy tangent limit exists in Lean
- [x] formalize iterated dyadic Loewner positivity
- [x] formalize the limiting tangent-minus-mesh positive-semidefinite law
- [x] exact target build and axiom audit

## Log

- 2026-07-19 — extracted by composing the live dyadic innovation and all-prime tangent theorems;
  the parent card stated the endpoint inequality but had not closed it in Lean.
- 2026-07-19 — formalized kernel symmetry, arbitrary finite dyadic refinement positivity,
  entrywise convergence along every positive dyadic mesh ray, and the limiting all-prime Loewner
  law.  The exact target build passes; `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
