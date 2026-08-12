# Marked Mellin normalization, exchange, and phase-response law — Lean certificate

- **ID:** `cmr-marked-mellin-normalization-exchange-response-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `marked-mellin-normalization-exchange-response-law.md` (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean module

`formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/MarkedMellinExchange.lean`,
namespace `HTGeometry.ConstraintMotiveRelativity`, imported by `GaloisForLFunctions.HTGeometry`.

The Cauchy–Schwarz step reuses the corpus lemma
`ContinuousLinearMap.tsum_mul_le_sqrt_mul_sqrt` of `HTGeometry/HilbertSchmidtOperator.lean` rather
than re-deriving an `ℓ²` pairing bound.

## Formal statement chain

### §1 — atomic probes and the dense source nerve

1. `mellinWeight`, `totalMass` — `(MER.5)`, `(MER.9)`: the atomic Mellin weight `c_n n^{-σ}` and
   the marked total mass `Z_c`.
2. **`atomic_density`** — Theorem 1.1: for a nonnegative comparison stream, positive rational
   atomic probes separate coefficient streams, i.e. `(∀ n q, 0 < q → q ≤ c n → q ≤ d n) ↔ c ≤ d`.
   Nonnegativity of the comparison stream is necessary and is the card's own standing `(MER.1)`.
3. **`coeff_eq_sSup`** — the coefficient is the supremum of the probes that it passes, so the
   atomic nerve is fully faithful.

### §2 — the marked pair and radial invariance

4. `normWeight` — `(MER.6)`: the normalized weight `P_c`.
5. **`coeff_of_normWeight`** — `(MER.7)`: the marked pair `(Z_c, P_c)` is coefficient faithful,
   `c_n = Z_c n^{σ} P_c(n)`.
6. **`totalMass_smul`**, **`normWeight_smul`** — the mass is homogeneous of degree one and the
   normalized state is invariant under positive radial rescaling.

### §3 — the exchange differential

7. `exchangeSeed` — `(MER.10)`: the centered exchange tangent `Z_c^{-1}(μ_h − H₀(h) P_c)`.
8. **`hasDerivAt_normWeight`** — the seed is the coordinatewise derivative of `ε ↦ P_{c+εh}` at
   `ε = 0` along an additive mass direction.
9. **`tsum_normWeight`**, **`tsum_exchangeSeed`** — the state has mass one and the tangent has mass
   zero.
10. **`exchangeSeed_eq_zero_iff`** — `(MER.11)`: the kernel of the exchange differential is exactly
    the radial line `h = (H₀(h)/Z_c) c`, so normalization has one-dimensional kernel.

### §4 — the phase reporter and the response law

11. `logAtom`, `atomChar`, **`norm_atomChar`** — the atom `log n` and the unimodular character
    `e^{-it log n}`.
12. `phaseCorr`, `phaseResponse` — `(MER.6)`, `(MER.13)`: the phase correlation `C_c(t)` and the
    centered response `DC_c[h](t)`.
13. **`phaseCorr_smul`** — `(MER.19)`: the phase reporter is radial-scale invariant.
14. **`phaseResponse_smul`** — `(MER.20)`: the same absolute intervention has response scaled by
    `λ^{-1}`, so the unmarked reporters cannot predict the absolute response.  Together with
    item 13 this is the exact non-identifiability of §6.
15. **`phaseResponse_atom`** — `(MER.15)`: the response to a multiplicative atom intervention is
    the marked weight times the centered character.
16. `expect`, `expect_const`, **`phaseCorr_eq_expect`** — the correlation is the `P_c`-expectation
    of the character.
17. **`phaseResponse_covariance`** — `(MER.14)`: for a multiplicative score `h = cr` the response is
    the bilinear covariance `E_{P_c}(r χ_t) − E_{P_c}(r) C_c(t)`.

### §5 — the Fisher-cost bound

18. `IsMarkedState` — the standing marked hypotheses `(MER.1)`–`(MER.2)` packaged as one predicate:
    the normalized weights are nonnegative, summable and of total mass one.  Its consequences
    `totalMass_ne_zero`, `summable_complex`, `total_complex`, `summable_mul_of_bounded`,
    `summable_atomChar`, `expect_atomChar`, `tsum_normWeight_mul_atomChar`,
    `summable_centered_atomChar` are proved, not assumed.
19. **`tsum_centered_atomChar`** — the centered character has zero `P_c`-mean.
20. `mean`, `fisherVar` — `(MER.16)`: the quotient Fisher form `g_c(r,r) = Var_{P_c}(r)`;
    `hermVar` — the Hermitian variance of a complex observable; `fisherVar_nonneg`,
    `hermVar_nonneg`.
21. **`hermVar_atomChar`** — `(MER.17)`, the exact character variance
    `Var^H_{P_c}(e^{-itx}) = 1 − |C_c(t)|²`, from `‖χ_t‖ = 1` and `E_{P_c}χ_t = C_c(t)`.
    `hermVarianceChar_eq` records the same identity in the algebraic `expect` formulation.
22. **`phaseResponse_centered`** — the response equals the tsum of the centered score against the
    centered character, for *every* centering constant; this is the step that makes Cauchy–Schwarz
    applicable.
23. **`phaseResponse_normSq_le`** — `(MER.17)`, the sharp bound
    `|DC_c[cr](t)|² ≤ Var_{P_c}(r)·(1 − |C_c(t)|²)`.  Weighted Cauchy–Schwarz on the vectors
    `√P_c |r − E r|` and `√P_c ‖χ_t − C_c(t)‖`.
24. **`phaseResponse_normSq_le_fisherVar`** — `(MER.17)`, the coarse bound
    `|DC_c[cr](t)|² ≤ Var_{P_c}(r)`.
25. **`fisherVar_eq_zero_iff`** — `(MER.17)`, the kernel: the quotient Fisher seminorm vanishes
    exactly on scores constant on the active support of `P_c`, which under `h = cr` is the radial
    source direction.

### §5 — time jets

26. `weightMoment` — the `k`-th log moment `∫ x^k e^{-itx} dμ` of the character against a weight
    sequence; `weightMoment_div_totalMass` identifies its normalization with `E_{P_c}(x^k χ_t)`.
27. **`hasDerivAt_atomChar`** — `∂_t e^{-it log n} = −i (log n) e^{-it log n}`.
28. **`hasDerivAt_weightMoment`** — differentiation under the sum: `∂_t` raises the moment order
    and multiplies by `−i`.  The dominating summable majorant is the absolute log moment
    `|w_n| |log n|^{k+1}` of `(MER.2)`, which is exactly the card's "dominated convergence uses the
    available absolute log moments".
29. **`iteratedDeriv_weightMoment_comb`** — every time jet of a linear combination of two log
    moments is the corresponding higher moment scaled by `(−i)^k`.
30. **`iteratedDeriv_phaseCorr`** — `(MER.18)`:
    `∂_t^k C_c(t) = (−i)^k E_{P_c}(x^k e^{-itx})`.
31. **`iteratedDeriv_phaseResponse`** — `(MER.18a)`:
    `∂_t^k DC_c[h](t) = ((−i)^k/Z_c)(∫ x^k e^{-itx} dμ_h − H₀(h) E_{P_c}(x^k e^{-itx}))`,
    i.e. the jet of the response is the response of the jet.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/MarkedMellinExchange.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.MarkedMellinExchange
```

Green with no warnings.  `#print axioms` on `coeff_of_normWeight`, `hasDerivAt_normWeight`,
`tsum_exchangeSeed`, `exchangeSeed_eq_zero_iff`, `phaseCorr_smul`, `phaseResponse_smul`,
`phaseResponse_atom`, `atomic_density`, `coeff_eq_sSup`, `phaseResponse_covariance`,
`hermVarianceChar_eq`, `IsMarkedState.totalMass_ne_zero`, `tsum_centered_atomChar`,
`hermVar_atomChar`, `phaseResponse_centered`, `phaseResponse_normSq_le`,
`phaseResponse_normSq_le_fisherVar`, `fisherVar_eq_zero_iff`, `hasDerivAt_atomChar`,
`hasDerivAt_weightMoment`, `iteratedDeriv_weightMoment_comb`, `iteratedDeriv_phaseCorr` and
`iteratedDeriv_phaseResponse` reports only `propext`, `Classical.choice`, `Quot.sound`.

## Scope notes

The card's standing hypotheses `(MER.1)`–`(MER.2)` — nonnegativity and finiteness of every
absolute logarithmic moment — appear in the Lean statements as `IsMarkedState` and as the
summability side conditions `Summable (fun n => |w n| * |log n|^k)`.  They are the card's own
setup, not added assumptions: without them the tsums that define `Z_c`, `P_c`, `C_c` and the jets
do not converge and the statements are vacuous.  Everything derivable from them inside the module
(nonvanishing of `Z_c`, complex summability, boundedness of the character, the moment splittings)
is proved rather than assumed.

`(MER.12)`'s identification of the tangent as an element of the signed-measure space and
`(MER.8)`'s Mellin series are recorded through their coefficient formulas — `exchangeSeed` and
`mellinWeight` — since every statement the card derives from them is a statement about those
coefficients.

§7's specialization to Euler shells is a remark about instantiating `c` at a shell stream and
introduces no further theorem; the card itself states that no indexed PCDG multicell is
constructed.
