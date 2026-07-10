# Finite Euler corners are Calkin-independent

- **ID:** finite-euler-calkin-independence
- **Stage:** 3-formalized
- **Type:** `[BRIDGE / FORMALIZATION; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean endpoint:** `formal/GaloisForLFunctions/RHTower/FiniteEulerCalkinIndependence.lean`
- **Parents:** `../new_scientific_knowledge/even-sonin-euler-corner-noncompact.md`,
  `one-prime-euler-fredholm-seam.md`

## Statement

Fix a Sonin cutoff `a>0`, distinct scales `r_1,...,r_m>1`, and complex coefficients
`c_1,...,c_m`, not all zero. Let `Q_a` be the orthogonal projection onto the common physical and
Fourier Sonin kernel and let

```text
D_r = U_r + U_r*
```

be the symmetric normalized dilation. Then

```text
(1-Q_a) (sum_j c_j D_(r_j)) Q_a
```

is not compact.

The same conclusion holds after restriction to the actual even carrier `L²(R)^ev`. Since the
positive Euler metric at scale `r` has lower corner

```text
-r^(-1/2) (1-Q_a) D_r Q_a,
```

the distinct positive Euler metric corners are linearly independent in the Calkin quotient.

Under the concrete dual Hardy--Titchmarsh unitary, this becomes the literal source theorem: for the
weighted critical-line Euler metrics

```text
w_r(s) = |1-r^(-1/2-is)|²,
```

every nonzero finite linear combination of their lower corners across the archimedean boundary
carrier is noncompact. Prime scales are an immediate specialization.

## Proof mechanism

Select the least scale `r_k` with nonzero coefficient. Choose `b>a` sufficiently close to `a`
that

```text
b r_k < a r_j
```

for every other active scale. The inward images of the even shell `a<|x|<b` under the distinct
dilations are then separated.

Let `g_n` be the orthonormal sequence of normalized indicators of shrinking symmetric cells in
that shell. The existing finite time-band compactness theorem implies

```text
Q_a g_n - g_n -> 0.
```

Observe the image through the physical cutoff onto the inward `r_k`-scaled shell. Exactly, for
every `n`,

```text
A_k (sum_j c_j D_(r_j)) g_n = c_k U_(r_k) g_n,
||A_k (sum_j c_j D_(r_j)) g_n|| = |c_k| > 0.
```

The observer kills `Q_a`, is contractive, and the correction `Q_a g_n-g_n` is norm-null. Thus the
lower corner maps a bounded weakly-null sequence to vectors whose norms stay bounded away from
zero, which is impossible for a compact operator.

For the even-carrier theorem, the proof does not infer noncompactness from an unrelated odd sector.
It extends a hypothetical compact even restriction through the ambient even projection and
contradicts the same explicitly even shell certificate. Unitary transport then gives the concrete
Hardy--Titchmarsh source statement.

## Formal surface

The endpoint exports, among its supporting geometry:

- `scaledEvenShellBand_disjoint`
- `exists_finiteSupport_separatingShellUpper`
- `centralSoninCorner_not_isCompactOperator_of_scaledShell_norm`
- `finiteDilationCorners_calkinIndependent`
- `finitePositiveEulerCorners_calkinIndependent`
- `finiteEvenDilationCorners_calkinIndependent`
- `finiteEvenPositiveEulerCorners_calkinIndependent`
- `finiteArchimedeanPrimeEulerCorners_eq_unitaryPush`
- `finiteArchimedeanPrimeEulerCorners_calkinIndependent`

## Exact scope

`[PROVED]` No nonzero finite **linear combination of positive Euler metric corners** is compact.

`[PROVED]` Consequently these corners span an infinite-dimensional linear subspace of the Calkin
quotient.

`[IMPORTANT CORRECTION]` This theorem does not say that every finite-place repair is impossible.
Connes--Consani prove that the product of the archimedean local-factor ratio with finitely many
non-archimedean ratios is quasi-inner, although each individual non-archimedean ratio is not. Their
operator is a multiplicative phase-ratio construction across a Hardy projection. The present
operator is the additive span of positive Gram metrics across the actual Sonin boundary carrier.
Thus nonlinear/product archimedean compensation is outside this theorem and remains available.

`[BRIDGE]` The theorem supplies no zero localization and does not increase the
Platt--Trudgian verified range. It constrains the architecture of a future source index: cancellation
cannot come from a finite additive counterterm in the positive Euler-metric span.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The separating-shell argument gives a useful exact theorem and a
verified source-specific Lean API, but its parent mechanism is standard localization / limit-operator
reasoning: isolate the least active dilation on a separated shell and test it on a weakly-null
sequence. The literal Sonin and Hardy--Titchmarsh transports do not turn that established mechanism
into a new scientific principle.

The result remains valuable as a bridge. It records that finite additive Euler-metric cancellation
is unavailable in this model and isolates the nonlinear or infinite renormalization problem. That is
project architecture and formalization value, not a claim of novelty in the scientific literature.

## Literature boundary

- Alain Connes and Caterina Consani, *Quasi-inner functions and local factors*,
  arXiv:2008.10974 / J. Number Theory 226 (2021), 139--167.
- Alain Connes, Caterina Consani, and Henri Moscovici, *Zeta zeros and prolate wave operators:
  semilocal adelic operators*, arXiv:2310.18423.
- The one-prime metric setup and source transport are recorded in
  `../../2-fully-proven/new/sonin-euler-metric-corner-noncompact.md` and
  `even-sonin-euler-corner-noncompact.md`.

## Verification

- Direct Lean compilation passes.
- The endpoint module build passes.
- The complete `GaloisForLFunctions.RHTower` umbrella build passes.
- `#print axioms` for all five independence endpoints reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The formal lint and generated-index gates are required before publication promotion.

## Gates

- [x] 0 -> 1: concrete finite-scale statement and actual Sonin carrier fixed.
- [x] 1 -> 2: separating-shell proof completed.
- [x] 2 -> 3: ambient, even-carrier, and concrete Hardy--Titchmarsh source theorems formalized.
- [ ] 3 -> 4: requires independent expert novelty review and a standalone paper exposition.
