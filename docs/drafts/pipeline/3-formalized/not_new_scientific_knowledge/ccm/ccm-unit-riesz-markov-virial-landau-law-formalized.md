# Formalization certificate — `ccm-unit-riesz-markov-virial-landau-law`

- **Card:** `ccm-unit-riesz-markov-virial-landau-law.md`
- **Stage:** 3-formalized / not-new
- **Lean modules:**
  - `formal/GaloisForLFunctions/RHTower/CCMUnitRieszMarkovDensity.lean` — cell positivity/gluing
  - `formal/GaloisForLFunctions/RHTower/CCMUnitRieszMobiusCausalVirial.lean` — finite virial algebra
  - `formal/GaloisForLFunctions/RHTower/CCMUnitRieszProfileLimit.lean` — `(4)`, `(5)`
  - `formal/GaloisForLFunctions/RHTower/CCMUnitRieszMarkovTransform.lean` — `(6)`, `(7)`,
    `(14)`–`(17)`
  - `formal/GaloisForLFunctions/RHTower/CCMUnitRieszVirialConnector.lean` — `(9)`, `(11)` split,
    `(13)` polar part, `(18)`–`(21)`
- **Umbrella:** all wired from `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` throughout
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(3)`–`(5)` profile, prefix bound, limit | `CCMUnitRieszProfileLimit` (+ `CCMUnitRieszQuadratureDefect`) |
| `(6)`, `(7)` zeta Laplace transform | `unitRieszLaplace_eq`, `unitRieszMarkovTransform_eq_mul` |
| `(9)` wavelet kernel | `hasDerivAt_movingWavelet` |
| `(11)` convolution split | `wavelet_coefficient_split` |
| `(13)` polar part of the virial | `integral_exp_neg_window`, `virial_exp_part` |
| `(14)`–`(17)` coefficient transform and residue | `CCMUnitRieszMarkovTransform` |
| `(18)`–`(21)` Landau bookkeeping | `landau_shift_nonneg_iff`, `landau_exponent_lt`, `landau_bracket` |

## Deliberately outside the Lean statement

- causal-convolution associativity `w = 1 ⋆ d`;
- Landau's first-singularity theorem;
- the Möbius floor identity `(12)`.

The card's remaining open gates (prove the Markov–virial lower bound `(23)`; RH) are route gates,
not statements of this card.
