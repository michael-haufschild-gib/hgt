# Clock probes for a potential of finite regularity

- **ID:** finite-regularity-clock-probes
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** child of `two-species-conformal-clock-scale-law`, "Missing 1" (the last open input of
  the programme)
- **Statement:** In every dimension, a spacetime potential of class `C^k` with an explicit finite
  `k = k(d)` admits clock probes at every event — the `C^∞` hypothesis of
  `regularOpenProbes_of_smooth_spacetime` is not needed.

## Goal

The parent card's open input is local solvability of `□u + Vu = 0` near every event. The state of
the corpus is:

- dimension two: solved for every `C¹` potential (Goursat);
- every dimension, potentials analytic in the transverse directions: solved (Ovsyannikov scale);
- every dimension, `C^∞` potentials: solved (`regularOpenProbes_of_smooth_spacetime`);
- every dimension, potentials of finite regularity: **open**.

Smoothness enters the third item at exactly one point. The probe is built by Fourier synthesis
against a *Wiener density* — a spatial Fourier density integrable against the weight `⟨η⟩^N` — and
the corpus realizes a potential as such a density by cutting it off and using mathlib's Schwartz
Fourier isomorphism. Schwartz is far more than the construction needs: the interface actually
consumed is `WienerFamily.ofWeightedBounds`, which asks only for the pointwise bound
`‖a t η‖ ≤ ⟨η⟩^{-(N+m)}M` and its Lipschitz analogue. A compactly supported `C^n` function already
satisfies it, with `n` finite.

## Approach

1. **Decay from finitely many derivatives.** For `f : E → ℂ` compactly supported and `C^n`, every
   `iteratedFDeriv ℝ i f` (`i ≤ n`) is continuous with compact support, hence integrable, so
   mathlib's `Real.fourier_iteratedFDeriv` applies:
   `𝓕(iteratedFDeriv ℝ n f) w = fourierPowSMulRight (-innerSL ℝ) (𝓕 f) w n`.
   Evaluating that multilinear map at `n` copies of `w/‖w‖` and using `le_opNorm` gives the *lower*
   bound `(2π‖w‖)^n ‖𝓕 f w‖ ≤ ‖𝓕(iteratedFDeriv ℝ n f) w‖ ≤ ∫‖iteratedFDeriv ℝ n f‖`.
2. **The weight.** `⟨w⟩^{2j} = (1+‖w‖²)^j ≤ 2^j(1 + ‖w‖^{2j})`, so
   `⟨w⟩^{2j}‖𝓕 f w‖ ≤ 2^j(∫‖f‖ + (2π)^{-2j}∫‖iteratedFDeriv ℝ (2j) f‖)`.
   Two functionals of `f`, both finite-order — no Schwartz seminorms.
3. **The curve.** A `C^k` spacetime potential cut off in space and time is a curve of compactly
   supported `C^k` functions; the two functionals are bounded uniformly in time and Lipschitz in
   time by compactness, using one further derivative in time.
4. **Assembly.** `WienerFamily.ofWeightedBounds` then produces the family, Fourier inversion
   (`Continuous.fourierInv_fourier_eq`) identifies its synthesis with the potential near the event,
   and `regularOpenProbes_of_locally_kgChartPotential` finishes.

## Gates

- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized — six modules, `FiniteRegularityFourierDecay.lean` …
      `FiniteRegularityConformalProbe.lean`; every theorem below depends only on
      `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready

## Numbered statements, as built

| # | statement | Lean name |
|---|---|---|
| 1 | derivatives of a compactly supported `C^n` function are integrable | `integrable_iteratedFDeriv_of_hasCompactSupport` |
| 2 | `(2π‖w‖)^n‖𝓕f w‖ ≤ ∫‖D^n f‖` | `norm_pow_mul_norm_fourier_le` |
| 3 | the weighted bound from two functionals | `kgFreq_pow_mul_norm_fourier_le`, `contDiffDecay` |
| 4 | admissible family from a curve of compactly supported `C^{2j}` functions | `WienerFamily.ofContDiffCurve` |
| 5 | Fourier inversion for such a curve | `kgPotential_fourier_of_contDiff` |
| 6 | the derivative of a time slice, and its two bounds | `iteratedFDeriv_slice`, `norm_iteratedFDeriv_slice_le`, `exists_lipschitz_time`, `exists_contDiffDecay_bounds` |
| 7 | local realization of a `C^{2j+1}` potential | `exists_locally_kgChartPotential_of_contDiff_spacetime` |
| 8 | **clock probes for a `C^{2j+1}` potential, every dimension** | `regularOpenProbes_of_contDiff_spacetime` |
| 9 | the explicit order `C^{2d+5}` | `regularOpenProbes_of_contDiff_spacetime_explicit`, `regularOpenProbes_of_contDiff_chart_explicit` |
| 10 | the same on every conformal rescaling of the flat chart | `regularOpenProbes_conformalRescale_kgChart_contDiff(_explicit)` |

## What is gained, and what is still open

The threshold is explicit and finite: with `N = d+3`, `m = d+1`, `j = d+2` the construction needs
`2j+1 = 2d+5` derivatives, so in `1+d` dimensions a `C^{2d+5}` potential carries probes at every
event — in the physical case `d = 3`, class `C^{11}`. The conformal factor is unaffected: it enters
only through smooth terms of the pullback potential, so it may remain an arbitrary smooth function.

What is *not* reached is a potential of class `C^k` with `k < 2d+5`, in particular a `C¹` potential
in dimension `≥ 3`. That is not an artefact of the cut-off: the Fourier route needs the density to
be integrable against `⟨η⟩^{N}` with `N > d+2`, and a `C^k` function only supplies decay of order
`k`. Below the threshold the construction has to be replaced by a Cauchy problem on a spacelike
hypersurface — hyperbolic energy estimates, which mathlib does not have. In dimension two the
`C¹` case is already closed by the Goursat construction, which is why no threshold appears there.

## Log
- 2026-08-04 — created in 1-in-progress; mathlib inputs verified present
  (`Real.fourier_iteratedFDeriv`, `Continuous.fourierInv_fourier_eq`, `integrable_one_add_norm`).
- 2026-08-04 — formalized end to end in six modules and moved to 3-formalized. The Schwartz
  hypothesis of the earlier construction is replaced by the explicit finite order `C^{2d+5}`.
