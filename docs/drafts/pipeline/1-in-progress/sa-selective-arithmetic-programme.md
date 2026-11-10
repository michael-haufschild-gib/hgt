# Selective Arithmetic (SA) programme

- **ID:** sa-programme
- **Stage:** 1-in-progress
- **Type:** PROGRAMME
- **Source:** docs/reports/review-1011/obstacles-summary.md §2.9 (with §3, §2.1 A93/A96/A98/A100, §2.3 F20–F22)
- **Statement:** theory of producers: prices, fakes and trivial apertures of the sign, by aspect.

## Goal
Develop the field of §2.9: folder `formal/GaloisForLFunctions/SelectiveArithmetic/`, umbrella
`SelectiveArithmetic.lean`, README (foundational, first draft written). Answer Q1–Q5 of the
README; build the tools (contact operator/Schur test, polar packets, conductor ladder, calibration
on fakes, feasible sets, slack map/exchange atlas).

## Mathematics fixed so far (paper)
System form on a packet `f ⊂ [-a,a]`:
`𝔚_{w,q}(f) = (1/2π)∫|f̂|²(S_∞ + log q) − Σ_{2≤n≤e^{2a}} w(n) n^{-1/2}·2(f⋆f̃)(log n)`.
For `w = Λ Re χ`, `q` = conductor: `= Z_χ(f)` (+ `placeEnergy ≥ 0` for odd χ)
(`AbsoluteGeometryOfSpecZ.integral_weilAtomSymbol_twist_packet`).

1. **Schur price of sizes.** `|w| ≤ Λ` ⇒ `|contact form| ≤ (K e^{a} + B + (1+2a)²)∫f²` whenever
   `ψ(x) ≤ Kx + B`. Proof: Schur test with polar weight `cosh`; row sums are
   `BiScaleUncertainty.polar_schur_le` (window `(−a, a)`, `L = 2a`). PNT: `K = 1+ε`
   (`BiScaleUncertainty.exists_psi_le_linear`).
2. **Trivial aperture.** `Z_χ(f) ≥ (log q − A₀ − (1+ε)e^{a} − B_ε − (1+2a)²)∫f²`,
   `A₀ = γ + 3 log 2 + π/2 + log π`. So the dominated box is feasible to `log log q − o(1)`.
   The report's `log log q − log 4` came from the pointwise bound `4e^{a}` of the symbol.
3. **Fakes.** Odd polar test `o·cutoff`, `o(t) = e^{−(L−t)/2} − e^{−t/2}` on `(0,L)`, `L = 2a`.
   With `p` the even profile: `o(t)o(s) + p(t)p(s) = 2(e^{−L+(t+s)/2} + e^{−(t+s)/2})`, hence
   `A_odd(y) + A_even(y) ≤ 4e^{−y/2}`, `logValue_odd(n) ≤ 8/n − logValue_even(n)`; prime side of
   the odd test `≤ 8(1+L)² − primeSide_even`, and `primeSide_even ≥ (1−η)e^{L/2}·…`
   (`BiScaleUncertainty.primeSide_polarTest_ge`). Mass of odd ≤ mass of even ≤ `2 + 2Le^{−L/2}`.
   Needs an upper bound of the archimedean energy of the smooth test (to find in corpus).
   Fakes: `w = −Λ`; Liouville `w(p^k) = (−1)^k log p` (= `−Λ` + 2·squares, squares cost
   `≤ 2(1+L)²` mass); `w = +Λ` without pole plane on the even test.
   Conclusion: negative square at `e^{a} ≥ (1+ε)(log q + C)`: ladder has no gap.
4. **One square.** `2⟨f,e₊⟩⟨f,e₋⟩` on `L²[−a,a]`, `e± = e^{±du}`: eigenvalues
   `2a ± sinh(2da)/d`.
5. **Ladder chart.** aperture `κ log(mass)`: isolated zero of depth `d` visible iff `2dκ > 1`.
6. **Height aspect.** Packets `f(u)e^{itu}`: same Schur bound; archimedean symbol `≈ log(t/2π)`.
7. **First selective window (A96).** For `a > ½ log 2` the feasible interval of `w(2)` is
   bounded; half-length `≍ log(1/(a − ½ log 2))`.

## Corpus facts already established (do not redo)
- `RHTower.riemannHypothesis_iff_forall_level_exists_weilPositiveFullUpTo` (A98 done).
- `BiScaleUncertainty.tendsto_windowCeiling_div_exp` (ceiling of the prime side for `Λ`).
- `CriticalHardyTheoryOfTheWindowCone.TheMarginLawOfTheWindowCone` (`𝒜(c)` and best margin).
- `DimensionZeroGeometryOfSpecZ.TheArchimedeanPlaceAloneIsNotWeilPositive`
  (convexity of the finite-level cone, `w = 0` fails for ζ).
- `AbsoluteGeometryOfSpecZ.twistedZeroSum_nonneg_of_level` (packets shorter than `log 2`).
- `ExceptionalLayerTheory.exists_deuring_heilbronn_repulsion`.

## Modules (folder `SelectiveArithmetic/`)
| Module | Content | State |
|---|---|---|
| `TheMassOfAConductorPaysEveryDominatedContact` | `Dominated`, `contactForm`, `systemForm`, `Feasible`, Schur price `abs_contactForm_le_of_psi`, `systemForm_ge_of_dominated`, `exists_systemForm_margin`, `twistedZeroSum_eq_systemForm`, `exists_trivialAperture_margin` | clean, olean built |
| `ThePolarPacketsOfAWindow` | `cutoff`, `evenPolar`, `oddPolar`, masses, derivative energies, `packetAutocorr_evenPolar_ge`, `packetAutocorr_oddPolar_le`, `abs_packetAutocorr_le` | clean, olean built |
| `TheLiouvilleTwistFailsBeyondTheTrivialAperture` | `systemForm_le_of_packet`, `liouvilleWeight`, `exists_systemForm_polar_neg`, `exists_not_feasible`, `trivialAperture`, `tendsto_trivialAperture_sub_log`, `eventually_cubic_lt_exp` | clean, olean built |
| `TheHeightOfAPacketIsAMass` | `integral_arch_modulated_ge`, `systemForm_modulated_ge`, `abs_re_weilPoleTerm_modulated_le`, `re_weilFullFunctional_modulated_ge`, `exists_height_margin`, `contDiff_two_deriv` | clean, olean built |
| `CancellationInTheContactsBuysTheLadder` | `HasCancellation`, Abel summation, `abs_sum_contact_cos_le`, `systemForm_ge_of_cancellation`, `exists_cancellation_margin` | clean |
| `AnIsolatedPairShowsAtTheRungOfItsDepth` | `isolatedPair_nonneg_of_rung`, `isolatedPair_neg_of_rung`, `exists_companion_of_rung`, `zeta_companion_of_rung` | clean |
| `TheFeasibleSetsOfAConductor` | `feasible_congr`, `Feasible.anti`, `Feasible.mono_conductor`, `convex_feasible`, `feasible_mul_exp_iff`, `exists_not_floor`, `bddAbove_feasibleApertures`, `feasible_of_lt_trivialAperture`, `exists_not_feasible_of_trivialAperture_lt` | clean |
| `TheZerosOfADirichletLFunctionOnTheLadder` | `dirichletZeros_local_count`, `dirichlet_companion_of_rung` | clean |
| `TheSignIsSquareRootCancellationOfTheRieszMean` | `systemForm_le_of_packet_scaled`, `packetAutocorr_cutoff_ge/le`, `packetAutocorr_evenPolar_sub_oddPolar`, `contactForm_le_of_systemForm_nonneg`, `riesz_bound_algebra`, `exists_riesz_le_of_polar_nonneg`, `exists_riesz_le_of_feasible`, `exists_not_feasible_of_riesz_ge`, `exists_riesz_twist_le_of_nonneg` | clean |
| `EveryVisibleWeightIsBoundedByTheMass` | `twoBump`, `packetAutocorr_twoBump`, `exists_abs_weight_le_of_feasible` (free width `r`), `abs_contactForm_le_sum_abs`, `feasible_of_sum_abs_le`, `feasible_iff_of_lt_half_log_two` | clean, olean built |
| `TheFirstSelectiveWindowOfZeta` | `PoleFeasible`, `poleFeasible_iff_of_lt_half_log_two`, `poleFeasible_of_abs_sub_le`, `poleFeasible_vonMangoldt`, `abs_re_weilPoleTerm_twoBump_le`, `exists_abs_weight_le_of_poleFeasible` | clean |
| `APoleAtTheHeightFailsBeyondTheTrivialAperture` | `weilTest_modulatedTest`, `contactForm_modulatedTest`, `alignedWeight`, `integral_cos_mul_sq_ge`, `exists_height_sum_cos_sq_ge`, `integral_arch_modulated_le`, `re_weilFullFunctional_modulated_le`, `exists_aligned_height_neg`, `exists_dominated_height_neg` | clean, olean built |
| `AHeightIsAConductorOfTheTwistedContacts` | `twistedWeight`, `archimedeanWeilSymbol_add_le`, `systemForm_modulatedTest_le/ge` (height transfer), `exists_twisted_riesz_le_of_feasible`, `exists_height_cancellation_margin`, `feasible_of_symbol_nonneg`, `feasible_of_twisted_cancellation` | clean, olean built |
| `InTheMeanOverTheHeightsTheContactsCancel` | `integral_sq_sum_cos_le`, `contactPoly`/`contactMass`/`contactEnergy`/`contactSlope`, `integral_contactPoly_sq_le`, `integral_contactPoly_window_sq_le`, sizes on a window, `exists_height_of_means`, `exists_height_contactPoly_small`, `abs_contactPoly_le_of_grid` | clean, olean built |
| `BoundedShapesDoNotDecideFeasibility` | `two_mul_sum_twisted_aligned`, `systemForm_aligned_ge`, `riesz_window_eq`, `grid_budget`, `receiver_budget`, `aligned_shape_positive_not_feasible_of`, `exists_shape_positive_not_feasible` | clean |

Umbrella `SelectiveArithmetic.lean` imports all fifteen; `MainTheorems.lean` imports the umbrella.
README rewritten around the proved pillars (ladder, rungs, exchange rate `2δκ = 1`, height transfer).

## Paper mathematics of modules 11–13
- **First window of ζ.** `Re W_w = Re W_Λ − contactForm(w − Λ)`; for `2a < log 2` no contact;
  two-bump pole term `≤ 12 Φ₀`; margin of Weil's form at width `181/250` gives the interior of `Λ`.
- **Height fake.** `(F_t ⋆ F̃_t)(x) = e^{−itx}(f ⋆ f̃)(x)`; aligned weight `Λ cos(t log n)` is seen
  with `cos²`; `∫_T^{2T} cos²(tx) dt ≥ T/2 − 1` (`x ≥ ½`); maximum ≥ mean; balance with
  `2 log T ≤ e^{−η} e^{a}`.
- **Height transfer.** `S_∞(τ+t) ≤ S_∞(τ) + log(2+|t|) + A₂`; translation of the frequency
  integral; contact form of `w` on `e^{−itu}f` = contact form of `w cos(t log ·)` on `f`.
  Receiver at height `t` = module 9 applied to the twisted system at conductor `q(2+|t|)e^{A₂}`.

## Separation theorem: bounded shapes do not decide feasibility (paper proof)
**Statement.** For every `η > 0` and every conductor with `x = log q` large, with
`a = log x + log 2 + η`: there is a dominated system `w` with
`𝔚_{w,q}(f) ≥ (x/2)(∫f² − ∫f'²)` for every `C³` packet `f` vanishing off `(−a, a)`, and
`¬ Feasible q a w`.

**Proof.** `E = e^{a} = 2e^{η}x`, `s = 2 + 2a`, `N = ⌊e^{2a}⌋`, `T = E⁸`, `ε = (1 − e^{−η/4})/4`,
`D = contactPoly N`, `P, Q, L` its mass, energy, slope: `P ≤ Es²`, `Q ≤ 2as²`, `L ≤ 2aEs²`.
1. *Height.* `4NP² ≤ 4E⁴s⁴ ≤ E⁸ = T` since `2s ≤ E`. Riesz weights `r(n) = Λ(n)(2a − log n) ≥ 0`,
   `R = Σ r(n) ≥ e^{−η/4}E²` (prime number theorem). Grid: `L̄ = 2aEs² + 1`, `h = x/(16L̄)`,
   `τ₁ = 4e^{η/2}s`, `M = ⌈16τ₁L̄/x⌉`, so `Mh ≥ τ₁` and `Lh ≤ x/16`. Module 14 gives
   `t₀ ∈ [T, 2T]` with `Σ r(n)cos²(t₀ log n) ≥ (½ − 1/T − ε)R ≥ ½e^{−η/4}R` and
   `D(t₀ + (k−M)h)² ≤ 2(2M+1)(Q+1)/ε` on the grid.
2. *Budget.* `L̄ ≤ s³E`, `16τ₁L̄/x ≤ 128e^{3η/2}s⁴`, `Q + 1 ≤ s³`; hence
   `2(2M+1)(Q+1)/ε ≤ 518 e^{3η/2} s⁷/ε ≤ (x/16)²` once `4345298944·e^{5η/2}a¹² ≤ Eε`
   (`s ≤ 4a`, `x² ≥ x`). So `|D| ≤ x/16` on the grid and `|D(t₀+σ)| ≤ x/8` for `|σ| ≤ τ₁`.
3. *Symbol.* `w = Λ(n)cos(t₀ log n)`. Product formula:
   `2Σ w(n)cos(τ log n)/√n = D(t₀−τ) + D(t₀+τ)`. For `|τ| ≤ τ₁` it is `≤ x/4`; for `|τ| > τ₁` it
   is `≤ 2P ≤ 2Es² = (x/4)τ₁² ≤ (x/4)τ²`. So the symbol plus `x` is
   `≥ (x − A₀ − x/4) − (x/4)τ²`, and with `A₀ ≤ x/4` the form is `≥ (x/2)(∫f² − ∫f'²)`.
4. *Infeasible.* If `w` were feasible, the receiver at the height `t₀` (module 13) gives
   `Σ r(n)cos²(t₀ log n) ≤ (x + log(2+t₀))(E+2a) + C(1+a)³E`, `log(2+t₀) ≤ log 4 + 8a`. The left
   side is `≥ ½e^{−η/2}E²`; the right side is `½e^{−η}E² + O((1+a)³E)` because `xE = ½e^{−η}E²`.
   Contradiction once `(31+8C)a¹² < ½(e^{−η/2} − e^{−η})E`.
5. *Sizes.* All conditions follow from `K a¹² < e^{a}` for one constant `K(η)`, hence hold for
   `log q ≥ M₀(η)`.

Lean: `SelectiveArithmetic/BoundedShapesDoNotDecideFeasibility.lean`, `exists_shape_positive_not_feasible`
(formalized, compiled clean).

## Open mathematics of the field (README §8)
- Sign of a true object at `log log q + C` (Landau–Siegel on the comb); a rung `κ > 1`.
- The separation on a whole rung: sign on bounded shapes at `κ log log q`, infeasible at
  `log log q + log 2 + η`. Same proof with a common height for the two windows; second moments
  reach `κ < 7/3` (budget `(log q)^{3(κ−1)/2} ≲ (log q)²`), higher rungs need higher moments.
- Rung law for an exceptional zero with Deuring–Heilbronn isolation: peer AGZ module has the raw
  inequality.

## Peers (do not duplicate)
- `AbsoluteGeometryOfSpecZ/TheTrivialApertureAndTheExceptionalSquare.lean` (peer, card
  `assemblies-of-proved-pieces.md`, A100/A101): pointwise trivial aperture `log log q − log 4`,
  half-window improvement `− log 2`, one-square law, Deuring–Heilbronn isolation inequality on the
  twisted comb with the raw size condition, `exists_dirichletZeros_local_count`,
  `grh_dirichlet_iff_forall_twistedZeroSum_nonneg`. SA supersedes its constant (Schur: `− o(1)`)
  and adds the fakes; SA does not redo the one-square law or DH.
- Corpus one-square law: `SquareRootThreshold.IsolatedOffLinePairVisibilityLaw` (`pairEnergy`,
  `isolatedPairConfig_weil_nonneg_iff`: nonneg iff `sinh(2δa)/δ ≤ 2L + 2a`).
- Peer owns A93, A96 as assembly rows (open there).

## Compile practice
- Each check takes 3–10 min (machine shared). Write complete modules, then compile.
- `set` variables: rewrite later hypotheses with `← hdef` before `linarith` (compound bodies are
  not identified).
- Long proofs with many hypotheses: `nlinarith` times out; split into small lemmas (a budget
  lemma and a pure-algebra lemma) and close with `linarith` on prepared products.
- `rw [e] at h` rewrites every occurrence, also under floors and `psi`; state the rewritten fact
  separately.
- With `Finset` and `Set` both open use `Set.Icc` / `Finset.Icc` explicitly.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Log
- 2026-11-10 — card created; README first draft; fifteen modules compiled clean and wired; README rewritten around the proved pillars.
