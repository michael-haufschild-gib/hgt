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
| `TheHeightOfAPacketIsAMass` | `integral_arch_modulated_ge`, `systemForm_modulated_ge`, `re_weilPoleTerm_modulated_ge`, `re_weilFullFunctional_modulated_ge`, `exists_height_margin`, `contDiff_two_deriv` | clean, olean built |
| `CancellationInTheContactsBuysTheLadder` | `HasCancellation`, Abel summation, `abs_sum_contact_cos_le`, `systemForm_ge_of_cancellation`, `exists_cancellation_margin` | clean |
| `AnIsolatedPairShowsAtTheRungOfItsDepth` | `isolatedPair_nonneg_of_rung`, `isolatedPair_neg_of_rung`, `exists_companion_of_rung`, `zeta_companion_of_rung` | clean |
| `TheFeasibleSetsOfAConductor` | `feasible_congr`, `Feasible.anti`, `Feasible.mono_conductor`, `convex_feasible`, `feasible_mul_exp_iff`, `exists_not_floor`, `bddAbove_feasibleApertures`, `feasible_of_lt_trivialAperture`, `exists_not_feasible_of_trivialAperture_lt` | clean |
| `TheZerosOfADirichletLFunctionOnTheLadder` | `dirichletZeros_local_count`, `dirichlet_companion_of_rung` | clean |
| `TheSignIsSquareRootCancellationOfTheRieszMean` | `systemForm_le_of_packet_scaled`, `packetAutocorr_cutoff_ge/le`, `packetAutocorr_evenPolar_sub_oddPolar`, `contactForm_le_of_systemForm_nonneg`, `riesz_bound_algebra`, `exists_riesz_le_of_polar_nonneg`, `exists_riesz_le_of_feasible`, `exists_not_feasible_of_riesz_ge`, `exists_riesz_twist_le_of_nonneg` | clean |

Umbrella `SelectiveArithmetic.lean` imports all nine; `MainTheorems.lean` imports the umbrella.
README rewritten around the proved pillars (ladder, rungs, exchange rate `2δκ = 1`).

## Not done (candidates)
- Fake for the height aspect in the dominated class (block-aligned phases).
- Rung law for an exceptional zero with Deuring–Heilbronn isolation (peer AGZ module has the raw
  inequality; `dirichletZeros_local_count` here duplicates the peer's local count because that
  module had no olean).
- Exchange rate without shape condition (uniform in `τ`); first-contact interval (peer A96).

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
- 2026-11-10 — card created; README first draft; three modules compiled.
