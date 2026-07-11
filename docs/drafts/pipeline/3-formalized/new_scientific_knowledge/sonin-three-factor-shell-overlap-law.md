# The three-factor shell-overlap law for Sonin Euler Gram chains

- **ID:** sonin-three-factor-shell-overlap-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-11
- **Status banner:** `[NOVELTY UNVERIFIED]` The law is proved and formalized unconditionally on
  the actual even Sonin carrier. It resolves the multiplication question left open by both
  parents: chains of three mixed Gram factors. The mechanism, once the pair law is known, is
  windowed interval algebra of Wiener--Hopf type; scientific priority of the actual-Sonin law
  requires the same external audit as the parents.
- **Parents:**
  `sonin-mixed-calkin-partial-isometry-law.md`;
  `sonin-two-scale-quadratic-corner-noncompact.md`
- **Lean endpoint:** `formal/GaloisForLFunctions/RHTower/SoninEulerTripleShellOverlap.lean`
- **Statement:** For the even Sonin corners `L_r=(1-Q_a)(U_r+U_r^{-1})Q_a` and Gram entries
  `G(p,q)=L_p^†L_q`, the chain `G(p,q)G(q,r)` through a middle scale `q` is, modulo compact
  operators, an explicit three-scale shell translation. The middle factor cancels exactly when
  `min(p,r) <= q` and never otherwise. The chain is always a Calkin partial isometry; the
  multiplicative thickness of its initial and final shells is `min(p,q,r)`. Chains therefore
  compose as a groupoid above the minimum scale and carry a permanent tropical memory — the
  minimum scale visited — below it.

## Theorem `[PROVED IN LEAN]`

Fix `a>0` and `p,q,r>1`. Write `T(p,q)` for the mixed shell translation
(the compact-quotient normal form of `G(p,q)`), `Sigma(s,t)` for the two-polarization shell,
and `m2 = max(a,(p/q)a)`.

1. **Chain law.** Within each polarization the chain product is exact:

   ```text
   (A_{pa}-A_a)U_{q/p}(1-A_a) . (A_{qa}-A_a)U_{r/q}(1-A_a)
     = (A_{pa}-A_{m2}) U_{r/p} (1-A_a),
   ```

   and identically on the Fourier side. Consequently

   ```text
   G(p,q)G(q,r) =_K T3(p,q,r),
   ```

   where `T3(p,q,r)` is the `(p,r)` shell translation with inner floor raised to `m2`.

2. **Absorption dichotomy.** `T3(p,q,r) = T(p,r)` exactly when `min(p,r) <= q`, and

   ```text
   G(p,q)G(q,r) =_K G(p,r)   iff   min(p,r) <= q.
   ```

   The forward implication is rigid: for `q < min(p,r)` the difference stays at positive
   distance from the compact ideal, because a nondegenerate two-polarization shell is not
   compact.

3. **Polar data.** Every chain `W=G(p,q)G(q,r)` is a partial isometry in the Calkin algebra,
   with

   ```text
   W^†W  =_K Sigma(max(a,(r/q)a,(r/p)a), ra),
   W W^† =_K Sigma(max(a,(p/q)a,(p/r)a), pa).
   ```

4. **Tropical thickness law.** The shells in (3) satisfy exactly

   ```text
   max(a,(r/q)a,(r/p)a) . min(p,q,r) = ra .
   ```

   The multiplicative thickness of every chain shell is `min(p,q,r)`; in logarithmic units the
   chain transports a shell of thickness `log min(p,q,r)`.

## Mechanism

One windowed lemma per polarization carries the whole law. For floors `b <= pa`, `a <= c <= qa`:

```text
(A_{pa}-A_b)U_{q/p}(1-A_a) . (A_{qa}-A_c)U_{r/q}(1-A_a)
  = (A_{pa}-A_{max(b,(p/q)c)}) U_{r/p} (1-A_a).
```

The trailing central complement absorbs into the middle shell, dilation covariance transports
the middle shell to the `p` scale, co-anchored shells multiply by taking the larger floor, and
the dilations compose. Reversed products, initial/final projections, absorption, and the
general-order pair law (no order relation between the two scales) are all instances of this one
identity followed by a unit-scale collapse. Cross-polarization products are compact by a
windowed generalization of the finite time--band block argument, with arbitrary shell endpoints
and dilation scales.

The strictness half multiplies a hypothetical absorption congruence by the reversed pair entry;
the initial shells of the two sides then differ by the two-polarization shell over
`(max(a,(r/p)a), (r/q)a]`, which fixes an orthonormal symmetric shell sequence and is therefore
not compact.

## Consequences

1. The Gram system of the Sonin Euler corners is not closed under multiplication in the Calkin
   algebra: it is a partial-isometry calculus whose composable part is exactly the
   `min(p,r) <= q` region. Pairwise data does not determine triple data; the missing gluing
   datum is one number, the minimum scale visited.
2. Chain thickness is a tropical (min-plus) invariant: any chain of Gram entries through a
   small scale is permanently pinched, and no later large scale restores it. For prime scales,
   every chain through `2` has thickness `log 2` regardless of length or route.
3. On the Euler-metric normalization `C_r=-r^{-1/2}L_r`, amplitudes multiply while supports
   take minima: the chain `C_p^†C_q C_q^†C_r` has amplitude `q^{-1}(pr)^{-1/2}` on a shell of
   thickness `log min(p,q,r)`. Arithmetic decay and geometric memory decouple.

## Lean surface

Shell algebra and windowed calculus:

- `evenIndicatorCutoff_shellProduct`, `evenFourierCutoff_shellProduct`
- `evenIndicatorCutoff_shellComplementProduct`, `evenFourierCutoff_shellComplementProduct`
- `evenIndicatorCutoff_complement_shellProduct`, `evenFourierCutoff_complement_shellProduct`
- `physicalWindowedShellTranslation_chain_mul`, `fourierWindowedShellTranslation_chain_mul`
- `physicalWindowedShellTranslation_scaleOne`, `fourierWindowedShellTranslation_scaleOne`
- `physicalWindowedShellTranslation_normalForm`, `fourierWindowedShellTranslation_normalForm`
- `isCompactOperator_physicalWindow_mul_fourierWindow`
- `isCompactOperator_fourierWindow_mul_physicalWindow`

The three-scale object and the law:

- `evenPhysicalTripleShellTranslation`, `evenFourierTripleShellTranslation`,
  `evenSoninTripleShellTranslation`
- `physicalShellTranslation_chain_mul`, `fourierShellTranslation_chain_mul` (exact)
- `evenSoninMixedShellTranslation_chain_compactEq_triple`
- `evenCentralSoninQuadraticCorner_chain_compactEq_triple`
- `evenSoninTripleShellTranslation_eq_pair_of_absorb` (exact operator equality)
- `evenCentralSoninQuadraticCorner_chain_absorb`
- `physicalTripleShellTranslation_mul_rev`, `fourierTripleShellTranslation_mul_rev` (exact)
- `evenSoninTripleShellTranslation_mul_rev_compactEq_shell`
- `adjoint_evenCentralSoninChainCorner`
- `evenCentralSoninChainCorner_adjoint_mul_compactEq_shell`
- `evenCentralSoninChainCorner_mul_adjoint_compactEq_shell`
- `evenCentralSoninChainCorner_isCalkinPartialIsometry`
- `tripleShellFloor_mul_min`
- `evenSoninMixedShellTranslation_mul_pair_compactEq_shell` (general order, no `p <= q`)
- `evenSoninMixedShellTranslation_mul_triple_compactEq_shell`

Strictness:

- `indicatorCutoff_normalizedIndicator_of_subset`, `indicatorCutoff_normalizedIndicator_of_disjoint`
- `evenIndicatorCutoff_evenShellVectorEven_of_le`, `evenIndicatorCutoff_evenShellVectorEven_eq_zero`
- `not_isCompactOperator_evenIndicatorShellDiff`
- `not_isCompactOperator_evenTwoPolarizationShell`
- `evenSoninTripleShellTranslation_not_compactEq_pair_of_pinch`
- `evenCentralSoninChainCorner_absorb_iff`

## Verification

- `lake build GaloisForLFunctions.RHTower.SoninEulerTripleShellOverlap` — PASS.
- `scripts/formal_tools.py lint --check-generated` — PASS.
- `#print axioms` on all nine endpoint theorems reports only `propext`, `Classical.choice`,
  `Quot.sound`.
- The module contains no `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration.

## Attack and exact scope

- `[PROVED]` The law holds for every real triple of scales above one; no primality or
  arithmetic independence is used. The absorption boundary `min(p,r) = q` is included in the
  absorbing region.
- `[PROVED]` Strictness needs both strict inequalities `q < p` and `q < r`; either failure
  restores exact absorption.
- `[PROVED]` The general-order pair law removes the `p <= q` hypotheses of the parent
  initial/final projection theorems.
- `[PARENT-THEORY WARNING]` After logarithmic coordinates the windowed calculus is
  translation-by-`log` interval algebra of Wiener--Hopf type. The candidate scientific content
  is the actual-Sonin realization — the two-constraint carrier, the two-polarization structure,
  and the compact cross terms — and the resolved dichotomy, not the interval bookkeeping.
- `[OPEN]` Chains with non-matching middle scales `G(p,q)G(r,s)`, `q != r`, involve displaced
  shell overlaps and are not computed here.
- `[OPEN]` The `n`-fold chain law — thickness equals the logarithm of the minimum of all
  visited scales — follows on paper by iterating the windowed lemma; only the three-factor case
  is formal.
- `[OPEN]` The essential norm of a pinched chain (equal to one, by the polar data and the
  nonzero shells) is not yet connected to the in-tree `essentialNorm` reader.

## Dual gate

- **NOVEL:** Both parents record the multiplication law for three or more mixed Gram factors as
  their open core; this card closes it with an exact dichotomy and a new invariant. The
  composable region is characterized, and the obstruction to composability is a single tropical
  datum. Priority remains subject to the same Wiener--Hopf/Toeplitz/prolate audit as the
  parents.
- **SIGNIFICANT:** The result determines how pairwise Gram data glues on triples: compatibly
  above the minimum scale, with an explicit pinch defect below it. This is the operator-side
  compatibility law needed before any all-prime aggregation of the Gram system, and it shows
  the Calkin image of the corner system is a min-plus calculus rather than a groupoid.

## Gates

- [x] 0 -> 1: chain operator, windowed mechanism, and dichotomy conjecture isolated
- [x] 1 -> 2: exact one-polarization chain law, absorption, polar data, tropical law, and
  strictness proved on paper
- [x] 2 -> 3: all of the above formalized unconditionally on the actual even Sonin carrier;
  build green, axioms clean, lint passed
- [ ] 3 -> 4: independent operator-algebra priority audit and standalone exposition

## Log

- 2026-07-11 — Derived the windowed chain law and recognized every product statement as one of
  its instances; proved absorption iff `min(p,r) <= q` with tropical thickness `min(p,q,r)`.
- 2026-07-11 — Formalized the full law, the general-order pair projections, shell
  noncompactness, and the strict dichotomy in `SoninEulerTripleShellOverlap.lean`; registered
  the module and regenerated indexes.
