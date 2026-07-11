# Mixed Sonin Calkin Gram entries are shell partial isometries

- **ID:** mixed-sonin-calkin-gram-partial-isometry
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status banner:** `[NOVELTY UNVERIFIED]` The theorem is formally proved. A primary-source audit
  found adjacent Sonin scaling non-invariance and quasi-inner partial-isometry results, but not the
  exact positive-metric two-polarization shell law. Priority still requires a broader
  Wiener--Hopf, Toeplitz--Hankel, and prolate operator-algebra audit.
- **Paper source:** `../../2-fully-proven/new_scientific_knowledge/sonin-mixed-calkin-partial-isometry-law.md`
- **Lean endpoint:** `formal/GaloisForLFunctions/RHTower/SoninEulerCalkinPartialIsometry.lean`

## Statement

Let `Q_a` be the orthogonal projection in `L²(R)^ev` onto the simultaneous kernel of the
physical and Fourier cutoffs at radius `a > 0`. For `r > 1`, let

`L_r = (1-Q_a)(U_r+U_r⁻¹)Q_a`

and let

`G(p,q) = L_p† L_q`.

For `m=min(p,q)` and the two-polarization shell operator

`Sigma(s,t) = (A_t-A_s) + (R_t-R_s)`,

the actual even-Sonin operators satisfy the compact-congruence identities

`G(p,q)† G(p,q) =_K Sigma((q*m⁻¹)*a,q*a)`,

`G(p,q) G(p,q)† =_K Sigma((p*m⁻¹)*a,p*a)`.

Each shell is self-adjoint exactly and idempotent modulo compact operators. Consequently every
mixed Gram entry `G(p,q)` is a partial isometry in the Calkin algebra. For `p <= q`, it transports
the two-polarization shell `[(q/p)*a,q*a]` to `[a,p*a]`; the reverse order is obtained by swapping
`p` and `q`. The logarithmic thickness of both shells is `log(min(p,q))`.

## Formal surface

The endpoint proves, without introducing a quotient type:

- `evenCentralSoninQuadraticCorner_compactEq_shellTranslation`
- `evenSoninMixedShellTranslation_adjointProduct_compactEq_shell_of_le`
- `evenSoninMixedShellTranslation_product_compactEq_shell_of_le`
- `adjoint_evenCentralSoninQuadraticCorner`
- `evenCentralSoninQuadraticCorner_adjoint_mul_compactEq_shell`
- `evenCentralSoninQuadraticCorner_mul_adjoint_compactEq_shell`
- `adjoint_evenTwoPolarizationShell`
- `evenTwoPolarizationShell_mul_compactEq_self`
- `evenTwoPolarizationShell_isCalkinProjection`
- `evenCentralSoninQuadraticCorner_isCalkinPartialIsometry`

Here `S =_K T` abbreviates `IsCompactOperator (S-T)`. The final predicate says that both
`(G†G)² =_K G†G` and `(GG†)² =_K GG†`.

## Proof architecture

1. Prove the normalized Fourier--dilation covariance on the actual `L²` model and restrict it to
   the even carrier.
2. Replace `Q_a` modulo compact operators by `1-A_a-R_a`, using the unconditional projection
   complement theorem in `SoninProjectionCalkin.lean`.
3. Delete the four support-forbidden branches exactly and express the surviving physical and
   Fourier branches as shell translations.
4. Multiply the shell translations in both orders. For `p <= q`, the physical products are
   exactly `A_(q*a)-A_((q/p)*a)` and `A_(p*a)-A_a`; the Fourier products obey the identical laws.
5. Factor every cross-polarization product through a finite time--frequency block, hence through a
   compact operator.
6. Combine the two polarizations, prove the min-formulas by the two possible orderings of `p,q`,
   and prove the resulting shells are Calkin projections.

This is a constraint-side multiplication law. No infinitesimal generator, carrier propagation,
or limiting flow is used.

## Verification

- The exact endpoint module passes a targeted Lean check and targeted module build.
- `#print axioms` for the two min-formulas, the shell Calkin-projection theorem, and the final
  partial-isometry theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.
- The endpoint contains no `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration.
- No full project build or project-wide lint is part of this card's verification.

## Exact boundary

The theorem determines the initial and final Calkin projections of every two-scale even-Sonin
Euler Gram entry. It does not yet provide a Lean essential-norm reader from compact congruence, so
the corollaries `||G(p,q)||_ess=1` and the corresponding positive Euler coefficient remain
paper-level consequences. The multiplication law for chains of three mixed entries through a
common middle scale is now formalized in `sonin-three-factor-shell-overlap-law.md`
(`SoninEulerTripleShellOverlap.lean`): absorption holds exactly on `min(p,r) <= q`, and the
pinched chain transports a shell of thickness `log min(p,q,r)`. Chains with non-matching middle
scales remain open.

## Dual gate

- **NOVEL:** Scaling non-invariance only asserts a nonzero boundary crossing. This theorem
  identifies the complete initial/final Calkin projection pair for every ordered pair of scales.
- **SIGNIFICANT:** The result gives the polar geometry of the entire two-place Sonin Euler Gram
  matrix and proves that the unsmoothed metric interaction transports an infinite-dimensional
  shell rather than becoming compact.

## Gates

- [x] 0 -> 1: exact source operator and shell endpoints isolated.
- [x] 1 -> 2: both multiplication laws proved on paper.
- [x] 2 -> 3: compact-congruence laws and Calkin partial-isometry endpoint formalized in Lean.
- [ ] 3 -> 4: requires an independent priority audit and standalone exposition.
