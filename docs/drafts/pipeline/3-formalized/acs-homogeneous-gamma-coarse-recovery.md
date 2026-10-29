# Homogeneous Gamma recovery of complete-cell averages

- **ID:** acs-homogeneous-gamma-coarse-recovery
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** One constant, independent of horizon and coefficients, bounds the Gamma energy of both actual pair averages and balanced details by the Gamma energy of their complete source.

## Goal

Remove the unpaid coarse square-mass term from `CompleteCellGammaRecovery`.
For `F = g + h`, where `g = averageSectionProfile q X` and
`h = haarSectionProfile d X`, prove

`Γ(g) + Γ(h) ≤ C Γ(F)`.

This addresses an analytic loss in ACS source descent. It does not by itself
pay the first-prime source, coarse odd higher powers, finite detail heads,
or the true polar and archimedean mass terms.

## Gates

- [x] 0 → 1: exact source, horizon-independent assertion, identified proof mechanism.
- [x] 1 → 2: dependency-closed paper proof below.
- [x] 2 → 3: direct Lean check; umbrella imports.

## Approach

1. Existing exact interval-to-exterior Gamma formula gives indicator energy
   at most `w (2 gammaTailMass(w) + exp(1/2))` for `0 < w ≤ 1`.
2. Split the tail at one; `ω(t) ≤ exp(1/2)/(2t)` on `(0,1]` gives
   `gammaTailMass(w) ≤ gammaTailMass(1) + exp(1/2)/2 * log(1/w)`.
3. Adjacent logarithmic widths are uniformly comparable. Each balanced
   two-cell atom therefore has energy at most a fixed multiple of
   `cellGammaWeight(a) * haarMass(a)`.
4. Disjoint pair supports give energy of an arbitrary signed detail sum
   at most twice the sum of its atom energies.
5. Existing exact variance payment bounds the weighted detail mass by
   `Γ(F)`. The quadratic inequality `Γ(F-h) ≤ 2Γ(F)+2Γ(h)` concludes.

## Paper proof [PROVED HERE]

Write `ω(t)=exp(-t/2)/(1-exp(-2t))`, `E=exp(1/2)`,
`T=∫₁∞ω(t)dt`, `w_a=log((a+1)/a)`, `κ_a=log(1/w_a)`.
The existing positive-tail integrability theorem makes `T` finite and
nonnegative. Existing width and weight lemmas give `0<w_a<1`,
`κ_a≥κ_1>0`, and `1/(a+1)≤w_a≤1/a` for `a≥1`.

For `0<w≤1`, split the integral at one and apply the existing density bound
`ω(t)≤E/(2t)` on `(0,1]`. Thus

`gammaTailMass(w) ≤ T + (E/2) log(1/w)`.

For an interval `I` of width `w≤1`, symmetry of the double difference
integral gives `Γ(1_I)=∫_I∫_{Iᶜ}ω(|x-y|)dy dx`. Endpoints have measure zero.
The existing exact interval-exterior formula and boundary-moment bound give

`Γ(1_I) ≤ w [E log(1/w) + 2T + E]`.

For a finite family of functions with disjoint supports, at every `(x,y)`
at most two summands of `f_i(x)-f_i(y)` are nonzero. Cauchy–Schwarz gives

`(Σ_i(f_i(x)-f_i(y)))² ≤ 2 Σ_i(f_i(x)-f_i(y))²`.

Multiplication by the nonnegative kernel and integration gives
`Γ(Σ_i f_i)≤2Σ_i Γ(f_i)`. All functions used below are compact BV;
the corpus proves their Gamma energies finite, so finite sums and integral
identities used here are valid.

For `n=2a` or `2a+1`, `w_a/4≤w_n`: indeed
`w_a≤1/a≤4/(2a+2)≤4/(n+1)≤4w_n`.
Consequently `log(1/w_n)≤κ_a+log 4`. Set

`B = E + (E log 4 + 2T + E)/κ_1 > 0`.

Then `Γ(rawCell n)≤B κ_a w_n`. The balanced atom is
`H_a=l_a rawCell(2a)-r_a rawCell(2a+1)`, with disjoint halves and
`l_a² w_(2a)+r_a² w_(2a+1)=M_a=haarMass(a)`.
The disjoint-sum inequality (or its two-term square bound) yields
`Γ(H_a)≤2Bκ_a M_a`. Different `H_a` have disjoint pair supports, so

`Γ(h)≤4B Σ_a κ_a M_a d_a²`.

The exact variance of `F=g+h` on pair `a` is `M_a d_a²`. The existing
`sum_cellGammaWeight_variance_le_gamma` therefore gives
`Σ_a κ_a M_a d_a²≤Γ(F)` without any condition on `q` or `d`.
Hence `Γ(h)≤4BΓ(F)`. Finally `g=F-h` and the pointwise two-term
square inequality give `Γ(g)≤2Γ(F)+2Γ(h)`. Therefore

`Γ(g)+Γ(h) ≤ (2+12B) Γ(F)`.

Every constant depends only on the Gamma kernel and the first cell width.
There is no horizon, coefficient, mean, pole, or spectral premise.

Writing `D=Σ_a κ_a M_a d_a²`, the same proof gives the two-sided energy
comparison

`Γ(g)+D ≤ (3+12B)Γ(F)`, and `Γ(F)≤2Γ(g)+8BD`.

The first follows by adding `D≤Γ(F)` and dropping nonnegative `Γ(h)`;
the second is the quadratic triangle bound and `Γ(h)≤4BD`. Thus complete
source Gamma energy is equivalent to coarse Gamma energy plus diagonal
weighted detail mass. Constants are multiplicative: this is not a
coefficient-one reserve or a full-Weil positivity statement.

## Arithmetic reserve retained after payment [PROVED HERE]

The corpus square-source theorem supplies `δ>0` such that

`Γ(F)-S₂(F)+(∫F)²/2 ≥ δΓ(F)+(γ_E/2)∫F²`.

The formalized odd higher-power joint-tail theorem supplies one fixed head
`A` after which `|P_odd(F)-P_odd(g)|≤(δ/2)Γ(F)`. Here the coarse source
is retained exactly; this is the mixed term plus the detail diagonal.
Let `K=3+12B` and `η=δ/(2K)>0`. The new homogeneous comparison gives

`Γ(F)-S₂(F)-[P_odd(F)-P_odd(g)]+(∫F)²/2`
`≥ η(Γ(g)+D)+(γ_E/2)∫F²`

whenever `d_a=0` for `a<A`, uniformly in all coarse coefficients and horizon.
This removes the additive coarse-mass error from the already-paid arithmetic
form while retaining a positive coarse Gamma and weighted-detail reserve.
First prime powers, pure coarse odd higher powers, finite detail heads, and
the actual polar/archimedean terms still require joint signed control.

## Lean implementation and validation

- `ArithmeticCastelnuovoSeveri/DisjointStepsHaveLogarithmicGammaCost.lean`:
  `levyEnergy_disjoint_sum_le`, `levyEnergy_sub_le_two_bv`,
  `gammaTailMass_le_log`, `rawCell_gamma_eq_exterior`,
  `rawCell_levyEnergy_le_log`.
- `ArithmeticIndexDescent/CompleteCellAveragesAreBoundedInGammaEnergy.lean`:
  `haarSectionProfile_gamma_le_weighted_mass`,
  `completePairProfile_gamma_pays_coarse_and_detail`,
  `exists_uniform_homogeneous_gamma_coarse_detail_bound`,
  `completePairProfile_gamma_equivalent_coarse_weighted_detail`,
  `exists_squareOddHigherRefinement_coarse_detail_reserve`.
- Helper file passed direct Lean check. Its required olean and the odd-source
  dependency olean were built individually, without diagnostics.
- Final check passed, exit 0, no diagnostics:
  `lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/CompleteCellAveragesAreBoundedInGammaEnergy.lean`.
- Both new modules are imported by their programme umbrellas. Umbrellas were
  not compiled. No final-module olean was created because no downstream file
  being written requires it.
- No web search, novelty checks, numerical experiments, or axiom checks.

## Log

- 2026-10-29 — Candidate recorded after corpus searches and inspection of
  `GammaIntervalRemainder`, `GammaMeanZeroEnergy`, `HaarCellProfiles`,
  `TranslatedDetailsAreUniformlySmallInGammaEnergy`, and existing coarse recovery.
- 2026-10-29 — Homogeneous recovery, two-sided energy comparison, and retained
  higher-power arithmetic reserve formalized; direct Lean check passed.
