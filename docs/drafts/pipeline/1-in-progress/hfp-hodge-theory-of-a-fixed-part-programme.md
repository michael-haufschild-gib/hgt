# Hodge theory of a fixed part (HFP)

- **ID:** hfp-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), programme card
- **Source:** `docs/reports/review-1011/obstacles-summary.md` §2.9
- **Statement:** Positivity and index theorems for the pairing of the degree points of the
  arithmetic square: contacts, jets, comb counterterm; effective classes; defects.

## Goal

Develop the field of §2.9: answer Q1–Q5, build tools T1–T6, decide criteria K1–K7, prove
milestones M2–M4. Folder `formal/GaloisForLFunctions/HodgeTheoryOfAFixedPart/`, umbrella
`HodgeTheoryOfAFixedPart.lean`, README in the folder.

## Normal form

Coordinates `c_n = f_n/√n` (packet `f` sampled at scale `N`, `f_n = f(log(n/N))`).

- `jet m n = ½(1/|m−n| + 1/(m+n))` (= AGZ `jetKernel`).
- contact `Λ(n/m)` for `m ∣ n`, `m < n`.
- counterterm `log(n/2π)`.
- `D·D = Σ_{m≠n} c_m c_n jet + 2 Σ_{m∣n,m<n} Λ(n/m) c_m c_n − Σ c_n² log(n/2π)`.
- degrees `d₁ = Σ c_n/n`, `d₂ = Σ c_n`; pole `2 d₁ d₂ = Σ c_m c_n (1/m + 1/n)`.
- AGZ: `degreeForm f L N + 2·degreeContact f L N` is `D·D` of the sampled packet on the window
  `Ioc N (N + L·N)`.

## Theorems (paper proofs)

**H1 (Lévy–Khintchine / Zariski on a comb).** For a symmetric kernel `k ≥ 0` off the diagonal on
a finite set `S`: `Σ_{m≠n} c_m c_n k = Σ_n c_n² row(n) − ½ Σ_{m≠n} k (c_m − c_n)²`. Hence
`D·D ≤ Σ c_n² (row_jets(n) + row_contacts(n) − log(n/2π))`.

**H2 (finite-scale Hodge index on short windows).** For `S ⊂ Ioc N (N+M)` with `M ≤ N/6`,
`N ≥ ...`, every real `c`: `D·D ≤ 2 d₁ d₂`. Proof: no contacts in a window of ratio `< 2`.
Row of the jets at `n`: `Σ_{m∈S, m≠n} ½/|m−n| ≤ H_{⌈(M−1)/2⌉}`-type bound `≤ 1 + log(M/2)`...,
`Σ ½/(m+n) ≤ M/(4N)`. Pole: `2 d₁ d₂ ≥ −(L³/2) Σ c_n²` on a window of ratio `1 + L`
(`d₁ = d₂/N − Σ c_n (n−N)/(nN)`). Counterterm `≥ log(N/2π)`.

**H3 (flat tail).** `Σ_{m ≤ A} ψ(B/m) = log ⌊B⌋!` for `A ≤ B < 2(A+1)`; contact energy of the
first `N` degree points is `log N!` (gluing index). Comb form of the flat tail `[1, N]`:
`2N·H_N − (N+½)H_{2N} + (5/4)H_N + N − log N! − N log 2π`, positive for every `N`, `/N → 2λ₁ =
2 + γ − log 4π`. In the limit the flat tail is `e^{u/2}` on `u ≤ 0`, `f̂(γ) = 1/ρ`,
`Z = Σ 1/(ρ(1−ρ)) = 2λ₁`.

**H4 (carry cocycle).** `E(N) = log N!` contact energy; `E(M+N) − E(M) − E(N) = log C(M+N, M)`
`= Σ_k Λ(k)·[carry]` (AGZ `log_choose_eq_sum_carry`). Counterterm of the block `(M, M+N]` =
counterterm of `[1, N]` + carry cocycle. Cross contacts of tail `[1,N]` with octave `(N, 2N]`:
`log((2N)!/N!)`; the single graph `Γ_1` contributes the window count, the others the carries.

**H5 (Riemann–Roch on the tower).** Sections of level `M`, `b` digits in `[0, A]`: count
`(A+1)^{bτ(M)}` (AGZ `card_image_orbitLatticeMap` for `[−A, A]`). Values on `Γ_1..Γ_K` lie in
the gluing lattice; with `|x_n| ≤ B_n` at most `Π_{n≤K}(2B_n/n + 1)` value vectors (necklace
coordinates are triangular with diagonal `n`). Pigeonhole: a nonzero section with digits in
`[−A, A]` vanishing on `Γ_1..Γ_K` exists once `(A+1)^{bτ} > Π (2B_n/n+1)`. The gluing index
`K!` is the quadratic term. Bézout: a section vanishing on all `Γ_d`, `d ∣ m`, `d < m`, has
`m ∣ x_m`.

**H6 (second axiom).** Reverse Cauchy–Schwarz on an open cone ⇔ index ≤ 1; Brunn–Minkowski for
`√vol` ⇒ reverse Cauchy–Schwarz. The count form of the tower at level `M` is a sum of `τ(M)`
hyperbolic planes: index `τ(M)`. Zero divisors `e_p(e_p − p) = 0`.

## Lean status

Folder `formal/GaloisForLFunctions/HodgeTheoryOfAFixedPart/`. Each module checked with
`lake --old env lean`, empty output.

| Module | Content | Status |
|---|---|---|
| `TheNormalFormOfThePairingOfTheDegreePoints` | `contact`, `pairKernel`, `counterterm`, `combPairing`, `degOne`, `degTwo`, `combForm`, `combPotential`, `combDirichlet`, `sampleCoord`; Zariski `combPairing_eq_potential_sub_dirichlet`; `combPotential_eq_of_properDivisors_subset`; bridge `combPairing_sample`; limits `tendsto_combPairing_sample`, `tendsto_degOne_mul_degTwo_sample`, `tendsto_combForm_sample` | checked, olean built |
| `TheHodgeIndexHoldsAtEveryScaleOnShortWindows` | `contact_eq_zero_of_window`, `sum_jetKernel_erase_le`, `log_nine_div_pi_ge`, `combPotential_le_of_short`, `combPairing_le_of_short` (≤ −1/40 Σc²), `neg_le_two_mul_degOne_mul_degTwo`, `combForm_ge_of_short` (≥ 1/50 Σc², `18 M ≤ N`), `combPairing_le_degrees_of_short` | checked, olean built |
| `WeilsFormInTheGaugeOfTheFlatTail` | `combBilin`, `formBilin`, `tailPotential`, `formBilin_one`, `combForm_eq_gauge`, `chebyshev`, `sum_contact_erase_Icc`, `combPotential_Icc`, `tailRow`, `tailPotential_Icc`, `formBilin_flatTail`, `sum_sum_contact_Icc`, `sum_chebyshev_div`, `combForm_flatTail`, `tendsto_combForm_flatTail_div` (→ 2+γ−log 4π), `tendsto_tailRow_mul`, `carryCocycle`, `sum_log_Ioc`, `sum_counterterm_Ioc`, `sum_contact_Icc_of_octave`, `sum_chebyshev_octave`, `sum_chebyshev_octave_lines` | checked, olean built |
| `RiemannRochOnTheTowerHasTheGluingIndex` | `natCast_dvd_ghostComponent_of_vanish`, `exists_first_graph`, `exists_fiber_of_triangular`, `exists_orbitLatticeMap_vanishing`, `exists_orbitLatticeMap_first_graph` | checked |
| `TheCombOfUnitMassesFixesTheContacts` | `sum_divisors_eq_log_iff`, `multiplicity_eq_one_iff`, `contactW`, `combPairingW`, `combFormW`, `combFormW_flatTail`, `tendsto_combFormW_flatTail_div`, `eventually_combFormW_flatTail_neg`, `eventually_combFormW_doubleTwo_neg` | checked |

| `TheIndexOfAWindowIsFiniteAtEveryScale` | `blockIndex`, `blockKernel`, `sum_mul_mul_blockKernel_eq_zero`, `abs_inv_sub_blockKernel_le`, `sum_dist_le`, `distMajorant`, `sum_contact_erase_le`, `sum_abs_pairKernel_sub_blockKernel_le`, `sum_mul_mul_le_abs_row` (Schur), `combForm_nonneg_of_blockSum_eq_zero`, `blockIndex_lt`, `exists_blockSize_combForm_nonneg` | checked |
| `ASeparatedCombIsOneOrbitOfTheFrobeniusMonoid` | `FrobeniusStable`, `Separated`, `frobeniusOrbit`, `exists_near_collision`, `exists_ratio_of_separated`, `den_le_of_separated`, `exists_orbit_of_separated`, `eq_orbit_of_generator_mem` (imports Mathlib only) | checked |
| `WhatTheSectionsOfTheSquareCertify` | `sum_contact_properDivisors_le_log_abs`, `prime_dvd_ghostComponent_of_vanish`, `sum_contact_primes_le_log_abs`, `primePointSection` (`p − e_p`), `primePointSection_spec`, `log_abs_primePointSection_lt` | checked |
| `TheInequalityAtFiniteScaleDecidesTheLimit` | `tendsto_sum_sq_sampleCoord`, `zeroSum_nonneg_of_frequently`, `riemannHypothesis_of_frequently_combForm_ge`, `exists_window_combForm_neg_of_not_riemannHypothesis` | checked |
| `OneInequalityPerPrimeOnTheComb` | `spline`, `twoBumpPacket`, `twoBumpWindow`, `zeroSum_twoBumpPacket`, `tendsto_combForm_twoBumpPacket`, `riemannHypothesis_iff_twoBump_windows_off_finset` | checked |

Umbrella `HodgeTheoryOfAFixedPart.lean` written with ten modules and imported by `MainTheorems`.
Oleans built for modules 1–4 and for the dependency
`SurfaceOfSpecZ/ScaleLocality/ExceptionalLogarithmicWindows`. README: first draft (needs the
results).

## Plan (remaining)

- Q1 canonical comb: a uniformly separated set stable under multiplication by `ℕ` lies in one
  orbit `δℕ` (Dirichlet approximation + Bézout coefficients; denominators `≤ α/σ`).
- Q3/T3: comb surface as `ArithmeticCastelnuovoSeveri.PolarSurface` (needs symmetric bilinear
  `combBilin`), Hodge index on short windows, Cauchy–Schwarz for the defect; Zariski index bound
  `ind₊ ≤ #{n : (P h)_n > 0}` for a positive gauge `h`.
- Q2: second axiom = smallness (Arakelov effectivity): Bézout for a section vanishing on `S` and
  `Γ_m` in the comb pairing is the bound `log|x_m| ≤ h(m) − Σ jets`; tower pairing between graphs
  on a line is `log|q^m − q^n|`; count form has one pole plane per line.
- K1–K7 readings; M3 = ACS `CurveDatum.spanDefect_eq_toeplitz`; M4: finite scale ratio 19/18
  (Lean), limit width 181/250 (AGZ).
- T4 (windows with exceptions), T6 (ordered approximations): corpus + normal-form statements.

## Traps met

- Each check of a module importing the AGZ chain takes 4–6 min (imports); the tower module 1.5.
- `Nat.add_choose_mul_factorial_mul_factorial i j` has `(i + j).choose j` (use
  `Nat.choose_symm_add`).
- `positivity` cannot prove `0 < (n : ℝ)` for a cast of an unknown natural: pass `mul_pos`.
- `set S := … with hS` blocks `rw` with lemmas stated on the explicit set: state helper lemmas
  on the explicit `Ioc N (N + L * N)`.
- `first | (field_simp; done) | …` triggers unreachable-tactic warnings: plain `field_simp`.

## Open

Q1 (canonical comb), Q3 at finite scale beyond short windows, K1–K7 readings, M2–M4.

## Log
- 2026-11-10 — created; README first draft; five modules checked.
