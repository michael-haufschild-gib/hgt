# ULF-FRM-4 — Lean certification record

Card: `cofinal-capital-density-selection-and-gaussian-rate-region-law.md`
Promoted to Stage 3 on 2026-08-30.

## Modules (all new)

| Module | Card sections |
|---|---|
| `GaloisForLFunctions.HTGeometry.CofinalCapitalDensitySelection` | §1, §2, §5 |
| `GaloisForLFunctions.HTGeometry.GaussianFormationRateRegion` | §3 |
| `GaloisForLFunctions.HTGeometry.GaussianPacketTestingLaw` | §4 and the relative-entropy form of §2 |

All three are imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`, which
`GaloisForLFunctions.HTGeometry` imports.

## Card result → Lean declaration

| Card | Lean |
|---|---|
| `(CDS.1)`, `(CDS.2)` finite binary experiments | `FiniteExperiment` |
| `(CDS.3)`, `(CDS.4)` exact formation array | `ExactFormation` |
| `(CDS.5)` Rényi overlap and extended capital | `renyiOverlap`, `renyiCapital`, `FiniteExperiment.capital` |
| `(CDS.6)` source capital density | `FiniteExperiment.capitalDensity` |
| **Thm 2.1**, `(CDS.7)` | `ExactFormation.capital_le`, `ExactFormation.capital_le_density`; ingredients `sum_rpow_mul_rpow_le` (Hölder), `renyiOverlap_markovDataProcessing`, `renyiOverlap_tensorPower`, `renyiCapital_tensorPower` |
| `(CDS.7)` for additive KL / Jeffreys capital | `klDiv_comp_pi_le`, `jeffreys_comp_pi_le` (built on the new randomized DPI `klDiv_comp_le`) |
| **Thm 2.2**, `(CDS.8)`, `(CDS.9)` | `tendsto_capital_of_tendsto_density` |
| `(CDS.10)` strict Hölder/AM–GM equality | `renyiOverlap_eq_one_iff`, `FiniteExperiment.capital_eq_zero_iff` |
| `(CDS.11)`, `(CDS.12)` coercivity conversion | `coercivity_displacement_bound` |
| `(CDS.13)`, `(CDS.14)` Gaussian shift/genesis packet | `GaussianFormation`, `garblingOp`, `gaussianGarbling` |
| **Thm 3.1**, `(CDS.15)` | `nonempty_gaussianFormation_iff`; packet form `nonempty_gaussianFormation_packetPow_iff`, density form `nonempty_gaussianFormation_packetPow_iff_le_density` |
| the `d`-fold independent product identification | `stdGaussian_piLp`, `stdGaussian_piLp_shift`, `norm_sq_packetPow` |
| `(CDS.16)`, `(CDS.17)` | `tendsto_signal_of_tendsto_density` |
| `(CDS.18)`, `(CDS.19)` | `displacement_le_of_gap` |
| **Thm 4.1**, `(CDS.20)` | `bayesRisk`, `bayesError`, `stdGaussianCDF`, `bayesRisk_stdGaussian_shift`, `bayesError_stdGaussian_shift`, `bayesError_ge_of_rate` |
| **Cor 4.1**, `(CDS.21)` | `tendsto_stdGaussianCDF_half` |
| **Thm 5.1**, `(CDS.22)` | `capital_eq_of_blackwellEquivalent` |
| **Cor 5.2**, `(CDS.23)`, `(CDS.24)` | `FiniteExperiment.capital_tensorPow` |

## Infrastructure built here that mathlib lacks

* `klDiv_comp_le` — randomized data processing for `klDiv`.  Mathlib has only the chain rule and
  `klDiv_compProd_left`; the corpus had only the deterministic `klDiv_map_le`.
* `klDiv_gaussianReal_shift` — the one-dimensional Cameron–Martin divergence `c²/2`.
* `klDiv_stdGaussian_shift` — its coordinate-free form `‖m‖²/2`, by orthonormal-basis reduction.
* `garblingOp`, `gaussianGarbling`, `nonempty_gaussianFormation_iff` — the exact Gaussian
  Blackwell classification, with the sufficiency half given by an explicit garbling kernel and
  verified through characteristic functions.
* `stdGaussian_piLp` — the standard Gaussian on an `ℓ²` power *is* the independent product.
* `bayesRisk`, `bayesRisk_prod_right`, `bayesRisk_gaussianReal`, `bayesRisk_stdGaussian_shift` —
  the Gaussian testing law.  The optimality half needs **no** Neyman–Pearson machinery: a common
  independent side channel is testing-neutral by Fubini, and the one-dimensional bound is
  `∫ min(φ₀, φ_c)`.

## Verification

* All three modules elaborate with 0 errors and build
  (`lake build GaloisForLFunctions.HTGeometry.{CofinalCapitalDensitySelection,GaussianFormationRateRegion,GaussianPacketTestingLaw}`).
* `#print axioms` over every public theorem of the three modules (69 declarations) reports only
  `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration; no hypothesis interface stands in
  for card content.  The only hypotheses carried are the card's own data conditions
  (`0 < α < 1`, probability packets, `0 < b`, `0 < d`).
