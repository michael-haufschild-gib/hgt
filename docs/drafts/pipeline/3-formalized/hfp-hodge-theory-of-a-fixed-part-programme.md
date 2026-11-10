# Hodge theory of a fixed part (HFP)

- **ID:** hfp-programme
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), programme card
- **Source:** `docs/reports/review-1011/obstacles-summary.md` §2.9
- **Statement:** Positivity and index theorems at finite scale for the pairing of the degree
  points of the arithmetic square, in its normal form: jets `½(1/|m−n| + 1/(m+n))`, contacts
  `Λ(n/m)`, diagonal `−log(n/2π)`, pole `1/m + 1/n`.

## Goal

Develop the field of §2.9: answer Q1–Q5, build tools T1–T6, read criteria K1–K7, prove M2 and M4.
Folder `formal/GaloisForLFunctions/HodgeTheoryOfAFixedPart/` (13 modules, README), umbrella
`HodgeTheoryOfAFixedPart.lean`, imported by `MainTheorems`. M5 is the Riemann hypothesis: open.

## Normal form

Coordinates `c_n = f_n/√n`, `f_n = f(log(n/N))`. `D·D = Σ_{m≠n} c_m c_n (jet + contact) −
Σ c_n² log(n/2π)`; `d₁ = Σ c_n/n`, `d₂ = Σ c_n`; Weil's form on the comb `𝔚 = 2 d₁ d₂ − D·D`.

## Theorems and paper proofs

**H1 Normal form** (`combPairing_sample`, `tendsto_combForm_sample`). `c_m c_n jet = f_m f_n
levyKernel`; a pair `(m, mk)` in the window has `2 ≤ k ≤ L`, and `c_m c_{mk} Λ(k) =
(Λ(k)/√k) f_m f_{mk}/m`; pairs counted from both ends give `2·degreeContact`. Degrees:
`√N d₁`, `d₂/√N` are Riemann sums of `∫ f e^{∓u/2}`. Limit from AGZ
`tendsto_degreePairing_degrees_sub_zeroSum`.

**H2 Zariski** (`combPairing_eq_potential_sub_dirichlet`). `c_m c_n = ½(c_m² + c_n²) −
½(c_m − c_n)²` for the nonnegative symmetric kernel `jet + contact`. Balance:
`Σ_{d ∣ n, d < n} Λ(n/d) = log n` (`combPotential_eq_of_properDivisors_subset`).

**H3 Short windows** (`combForm_ge_of_short`, `18M ≤ N`). No contacts in a window of ratio `≤ 2`.
Row of the jets `≤ H_M + M/(4N)` (distinct distances on each side), `H_M ≤ 1 + log M`,
counterterm `≥ log(N/2π)`, and `log(9/π) ≥ 1 + 1/72 + 1/40` (`e < 2.7183`, `e^x ≤ 1/(1−x)`,
`π < 3.15`): `V ≤ −1/40`. Pole: `d₁ = d₂/N − e`, `e² ≤ (M³/N⁴)Σc²` by Cauchy–Schwarz,
`2x²/N − 2xe ≥ −Ne²/2`: `2 d₁ d₂ ≥ −(M³/2N³)Σc² ≥ −Σc²/200`.

**H4 Finite index** (`combForm_nonneg_of_blockSum_eq_zero`, `exists_blockSize_combForm_nonneg`).
Blocks of `B` points; `K̃(m,n) = 1/(2B|i−j|)` for blocks at distance `≥ 2`, else `0`; it is a
function of the blocks, so its form vanishes on divisors with zero block sums. For blocks at
distance `k ≥ 2`: `(k−1)B < |m−n| < (k+1)B`, hence `|1/(2x) − 1/(2Bk)| ≤ 1/(2xk) ≤ B/x²`. Row of
`|1/(2|m−n|) − K̃|`: near pairs `|m−n| < 2B` give `≤ H_{2B}`, far pairs `Σ_{d>B} 2B/d² ≤ 2`.
Regular part `≤ M/(4N)`, contacts `≤ 2ψ(Q)` (quotients `≤ Q`, injective). Schur for a signed
symmetric kernel via Lévy–Khintchine applied to `|c|`, `|K|`. On zero block sums `d₂ = 0`.
`B = ⌊N/R⌋`, `R = ⌈4π e^{3 + Q/4 + 2ψ(Q)}⌉`; fewer than `2QR` blocks.

**H5 Finite scale and the limit** (`riemannHypothesis_of_frequently_combForm_ge`,
`exists_window_combForm_neg_of_not_riemannHypothesis`). `Σ c_n² → ∫ f²`; `Z(f) + η∫f² ≥ 0` for
all `η` gives `Z(f) ≥ 0`; AGZ `riemannHypothesis_iff_degreePairing_le_degrees`.

**H6 Flat gauge** (`combForm_eq_gauge`, `tailPotential_Icc`, `tendsto_tailRow_mul`). Pole in
Lévy–Khintchine form with rows `Σ_m (1/m + 1/n) = H_N + N/n`; contacts of `Γ_n` with the tail
`log n + ψ(N/n)` (multiples `nk ≤ N`); jets row `½(H_{N−n} + H_{N+n}) − 3/(4n)` (AGZ). Along
`N = kn`: `H_{kn} − ½(H_{(k−1)n} + H_{(k+1)n}) → −½ log(1 − k⁻²)`.

**H7 Chebyshev, carries** (`sum_chebyshev_div`, `sum_counterterm_Ioc`, `sum_chebyshev_octave`,
`combForm_flatTail`, `tendsto_combForm_flatTail_div`). Contacts among `[1,N]` counted from below:
`Σ log n = log N!`; from rows: `Σ (log n + ψ(N/n))`. `Σ_{n∈(M,M+N]} log n = log N! +
log C(M+N,M)`. For `N < n ≤ 2N+1` all proper divisors of `n` are `≤ N`. Flat tail:
`2N·H_N − jetEnergy N − log N! − N log 2π`, per point `→ 2γ + 2 − (log 4π + γ)`.

**H8 Hardy** (`hasSum_jetLevel`, `sum_mul_mul_jetLevel_nonneg`, `combForm_sub_combFormJets`).
`b/(b²−a²) = Σ_j a^{2j}/b^{2j+1}`; remainder after `J` terms `(a/b)^{2J}` times the sum.
`k_j(m,n) = (mn)^{2j}/max^{4j+1}`; for `g` nonincreasing, by induction
`g(N)(Σ_{n≤N} x_n)² ≤ Σ x_m x_n g(max)`. Ordered approximations: same potential, Dirichlet form
with `J` weights; error `½Σ(min/max)^{2J} jet (c_m−c_n)²`, `min/max ≤ 1 − 1/N` on `[1,N]`.

**H9 Tower** (`exists_fiber_of_triangular`, `exists_orbitLatticeMap_vanishing`,
`exists_orbitLatticeMap_first_graph`). If `x`, `y` agree on `Γ_d`, `d ∣ n` proper, then
`n ∣ x_n − y_n` (necklace coordinates); a residue class modulo `n` has `≤ ⌊2B/n⌋ + 1` points in
`[−B, B]`; induction on `K`, pigeonhole on the quotient `⌊(v + B)/n⌋`. Sections with digits in
`[0, A]`: `(A+1)^{bτ}`; difference of two with equal values.

**H10 Certified contacts** (`sum_contact_properDivisors_le_log_abs`,
`sum_contact_primes_le_log_abs`, `log_abs_primePointSection_lt`). `n ∣ x_n`; Dwork:
`p ∣ x_{pm} − x_m`, distinct primes multiply; `p − e_p` has components `p·[p ∤ n]`.

**H11 Unit masses** (`sum_divisors_eq_log_iff`, `multiplicity_eq_one_iff`,
`combFormW_flatTail`, `eventually_combFormW_flatTail_neg`). Strong induction on `n`; pairs
`(m, mk)`, `mk ≤ N`: `⌊N/k⌋`; `⌊N/k⌋/N → 1/k`.

**H12 One orbit** (`exists_orbit_of_separated`). Irrational ratio: Dirichlet,
`|kθ − j| ≤ 1/(n+1)`, `j ≥ 1`. Rational `a/b`: `a(m+b) = b·j + 1`, distance `α/b ≥ σ`;
`δ = α/⌊α/σ⌋!`.

**H13 Window criterion** (`riemannHypothesis_iff_twoBump_windows_off_finset`). SRT `W_twoBump`,
`conj_lagStructure_neg`: `Z(B + τ_v B) = 2 Re S(0) + 2 Re S(v)`; SOSZ
`riemannHypothesis_iff_prime_logarithmic_windows_off_finset`.

**H14 Index and defect** (`hermNegIndex_zeroGram_le_of_hermiteBiehler`,
`hermNegIndex_zeroGram_le_one_of_constantTerm`). ACS `negIndex_zeroGram_le_of_tempered` and IRP
`hermiteBiehler_index`, `constantTerm_zero_subsingleton`, `exists_exceptionalParameter_iff`.

**H15 Calibration** (`combFormW_ge_of_short`). No contact in a window of ratio `≤ 2`.

## Lean status

Each module checked with `lake --old env lean`, empty output.

| Module | Main declarations |
|---|---|
| `TheNormalFormOfThePairingOfTheDegreePoints` | `contact`, `pairKernel`, `counterterm`, `combPairing`, `degOne`, `degTwo`, `combForm`, `combPotential`, `combDirichlet`, `sampleCoord`, `combPairing_eq_potential_sub_dirichlet`, `combPotential_eq_of_properDivisors_subset`, `combPairing_sample`, `tendsto_combForm_sample` |
| `TheHodgeIndexHoldsAtEveryScaleOnShortWindows` | `contact_eq_zero_of_window`, `sum_jetKernel_erase_le`, `log_nine_div_pi_ge`, `combPotential_le_of_short`, `combPairing_le_of_short`, `neg_le_two_mul_degOne_mul_degTwo`, `combForm_ge_of_short` |
| `WeilsFormInTheGaugeOfTheFlatTail` | `combBilin`, `formBilin`, `tailPotential`, `combForm_eq_gauge`, `chebyshev`, `tailRow`, `tailPotential_Icc`, `sum_chebyshev_div`, `combForm_flatTail`, `tendsto_combForm_flatTail_div`, `tendsto_tailRow_mul`, `carryCocycle`, `sum_counterterm_Ioc`, `sum_chebyshev_octave`, `sum_chebyshev_octave_lines` |
| `RiemannRochOnTheTowerHasTheGluingIndex` | `natCast_dvd_ghostComponent_of_vanish`, `exists_first_graph`, `exists_fiber_of_triangular`, `exists_orbitLatticeMap_vanishing`, `exists_orbitLatticeMap_first_graph` |
| `TheCombOfUnitMassesFixesTheContacts` | `sum_divisors_eq_log_iff`, `multiplicity_eq_one_iff`, `contactW`, `combFormW`, `combFormW_flatTail`, `tendsto_combFormW_flatTail_div`, `eventually_combFormW_flatTail_neg`, `eventually_combFormW_doubleTwo_neg` |
| `TheIndexOfAWindowIsFiniteAtEveryScale` | `blockIndex`, `blockKernel`, `sum_mul_mul_blockKernel_eq_zero`, `abs_inv_sub_blockKernel_le`, `sum_abs_pairKernel_sub_blockKernel_le`, `sum_mul_mul_le_abs_row`, `combForm_nonneg_of_blockSum_eq_zero`, `blockIndex_lt`, `exists_blockSize_combForm_nonneg` |
| `ASeparatedCombIsOneOrbitOfTheFrobeniusMonoid` | `FrobeniusStable`, `Separated`, `frobeniusOrbit`, `exists_near_collision`, `den_le_of_separated`, `exists_orbit_of_separated`, `eq_orbit_of_generator_mem` |
| `WhatTheSectionsOfTheSquareCertify` | `sum_contact_properDivisors_le_log_abs`, `sum_contact_primes_le_log_abs`, `primePointSection`, `log_abs_primePointSection_lt` |
| `TheInequalityAtFiniteScaleDecidesTheLimit` | `tendsto_sum_sq_sampleCoord`, `riemannHypothesis_of_frequently_combForm_ge`, `exists_window_combForm_neg_of_not_riemannHypothesis` |
| `OneInequalityPerPrimeOnTheComb` | `spline`, `twoBumpPacket`, `zeroSum_twoBumpPacket`, `tendsto_combForm_twoBumpPacket`, `riemannHypothesis_iff_twoBump_windows_off_finset` |
| `TheJetsAreASumOfHardySquares` | `jetLevel`, `hasSum_jetLevel`, `jetKernel_sub_sum_jetLevel`, `le_sum_mul_mul_antitone_max`, `sum_mul_mul_jetLevel_nonneg`, `neg_le_sum_sum_jetLevel`, `combFormJets`, `combForm_sub_combFormJets`, `combForm_sub_combFormJets_le`, `tendsto_combFormJets` |
| `TheIndexOfThePairingIsAtMostTheDefectOfASplitting` | `hermNegIndex_zeroGram_le_of_rightZeros_subset`, `hermNegIndex_zeroGram_le_of_hermiteBiehler`, `hermNegIndex_zeroGram_zeta_le_of_hermiteBiehler`, `hermNegIndex_zeroGram_le_one_of_constantTerm`, `hermNegIndex_zeroGram_eq_zero_of_constantTerm` |
| `ShortWindowsDoNotSeeTheContacts` | `combFormW_eq_combForm_of_window`, `combFormW_ge_of_short` |

## Open

The topics of README §11: the inequality at finite scale under RH (all real divisors); the exact
index at finite scale; the first contact at finite scale; a count of small sections; the prime
powers above a graph; the flat-tail cone; a splitting with a bounded defect. M5.

## Compile practice and traps

- A check of a module importing the AGZ chain takes 3–6 min (11 under load); foreground only.
- Oleans built: modules 1–5 of the folder, and the dependencies
  `SurfaceOfSpecZ/ScaleLocality/ExceptionalLogarithmicWindows`,
  `InfiniteRankPurityTheory/ADefectOfDegreeKappaHasAtMostKappaExceptionalPoints`,
  `InfiniteRankPurityTheory/TheExceptionalParameterIsBornAtFourPiExpMinusGamma`.
- `Nat.add_choose_mul_factorial_mul_factorial i j` has `(i + j).choose j`.
- `add_le_add_right h c` adds on the left in this Mathlib: use `add_le_add h le_rfl`.
- `field_simp` on `(m/n)^2` loses the hypothesis `1 − (m/n)² ≠ 0`: abstract the ratio first.
- `positivity` does not prove `0 < (n : ℝ)` for an unknown natural.
- `Nat.exists_mul_mod_eq_one_of_coprime` (not `emod`); `Set.encard_le_encard`.
- `rw [← Nat.cast_natAbs]` needs `← Int.cast_abs` first.

## Log
- 2026-11-10 — created; README; thirteen modules checked; umbrella wired into `MainTheorems`.
