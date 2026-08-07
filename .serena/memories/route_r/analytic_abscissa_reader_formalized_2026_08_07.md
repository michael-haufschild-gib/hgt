# Analytic abscissa reader — FORMALIZED, both domains (2026-08-07)

Supersedes `mem:route_r/analytic_abscissa_reader_paper_proved_2026_08_06`.
Module `RHTower/HarmonicResidueAbscissaReader.lean`, `lake build` green (3178 jobs), axioms
`[propext, Classical.choice, Quot.sound]`, in the RHTower umbrella. Imports ONLY
`RHTower/PrimeZetaLogAsymptotic` and `HTGeometry/CofinalUnitProfileResidue` — keeping the general law
off the heavy Route R cone is what made it buildable while full-area rebuilds held that cone.

## The law

`primeAbscissaSeries a s = ∑' p, a p * p^(-(s-1))`, `abscissaLog s = -log(s-1)`.

- `tendsto_primeAbscissaSeries_div_abscissaLog` — for `HasReferenceResidue primeHarmonicWeight a c`,
  `A(s)/(-log(s-1)) → c` on `𝓝[>]1`.
- `tendsto_primeAbscissaSeries_div_abscissaLog_of_negligible` — negligible (`o(1/p)`, possibly
  NON-summable) fields vanish. Pointwise `‖b p‖p^{-(s-1)} ≤ ε p^{-s} + 1_{s₀}(p)‖b p‖`, hence
  `‖B(s)‖ ≤ ε·P(s) + C`; the ε is absorbed by the *normalised* `P(s)/L(s) → 1`.
- `tendsto_primeAbscissaSeries_div_abscissaLog_mod` — the reader law on `ℓ¹ + negligible`, i.e. the
  same enlarged domain as the profile reader. The two readers now agree on exactly one class.

Supporting: `primeHarmonicWeight_mul_abscissaShift` (`p⁻¹·p^(-(s-1)) = p^(-s)`),
`norm_primeAbscissaRemainder_le` (remainder bounded UNIFORMLY for `s ≥ 1` since `p^(-(s-1)) ≤ 1`),
`primeAbscissaSeries_eq`, `tendsto_primeZeta_div_abscissaLog`,
`summable_primeAbscissaTermOfResidue`, `summable_primeAbscissaTermOfNegligible`,
`norm_primeAbscissaSeries_negligible_le`.

## Lean notes

- `tendsto_abscissaLog_atTop` proved directly via `tendsto_atTop.mpr`, `Iio_mem_nhds`,
  `nhdsWithin_le_nhds`, `Real.log_le_log` — no named "log → atBot at 0⁺" lemma needed.
- `Complex.summable_ofReal` did NOT work as `.mpr` here (elaborated with head `Function`); use
  `Complex.hasSum_ofReal.mpr h |> ... |>.summable` instead.
- `mul_lt_mul_left` is not an iff in this mathlib; use `mul_lt_mul_of_pos_left`.
- Dot-notation trap once more: `hres.norm` fails for `hres : HasReferenceResidue …`; write
  `Summable.norm hres`.
- `Set.indicator` is classical, so it can appear in statements without `DecidableEq`; its tsum need
  not be identified with a finite sum — leaving it as `C := ∑' p, indicator …` is enough.

## Blocked, honestly

The Route R specialization (analytic three-value law + analytic RH characterization) and the two
fifth-pass theorems `primeHarmonicResidueMod_unique`,
`riemannHypothesis_of_frequently_negligible_producer` all need the
`RouteRHarmonicQuantumGapCriterion` cone. Missing oleans in that cone went 9 → 8 → 6 → **19** as two
further sessions launched fresh full-area `lake build GaloisForLFunctions.RHTower` runs. A targeted
`lake build` of the gap module reached 10233/10788 jobs once, then a later attempt made zero progress
(lock contention). Do not keep retrying; wait for the tree to settle.
