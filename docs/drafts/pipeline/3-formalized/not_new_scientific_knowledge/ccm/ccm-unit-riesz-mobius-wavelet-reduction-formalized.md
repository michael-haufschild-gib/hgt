# Formalization certificate — `ccm-unit-riesz-mobius-wavelet-reduction`

- **Card:** `ccm-unit-riesz-mobius-wavelet-reduction.md`
- **Stage:** 3-formalized / not-new
- **Lean modules:**
  - `formal/GaloisForLFunctions/RHTower/CCMCriticalMellinRieszMobiusRenewal.lean` — `(1)`, `(2)`,
    `(9)`, `(13)`
  - `formal/GaloisForLFunctions/RHTower/CCMUnitRieszQuadratureDefect.lean` — `(4)`, `(5)`, `(6)`,
    `(11)` sharp form
  - `formal/GaloisForLFunctions/RHTower/CCMUnitRieszWaveletFrontier.lean` — `(7)`, `(10)`, `(15)`,
    `(18)`, `(20)`–`(23)`, `(25)`
- **Umbrella:** all wired from `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` throughout
- **Hypotheses:** only the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(1)`, `(2)`, `(9)`, `(13)` | `CCMCriticalMellinRieszMobiusRenewal` |
| `(4)`–`(6)`, `(11)` | `CCMUnitRieszQuadratureDefect` |
| `(7)` progression mass | `progressionMass_eq` |
| `(10)` Möbius compensation | `mobius_compensation` |
| `(15)` renewal normalization | `riesz_normalization_eq` |
| `(18)` zero-mean wavelet | `integral_kernel_zero_mean` |
| `(20)`–`(22)` pole-channel margin | `integral_u_exp_neg`, `one_sub_poleChannel_le` |
| `(23)` frontier identity | `frontier_identity` |
| `(25)` frontier equivalence | `frontier_equivalence` |

## Deliberately outside the Lean statement

- the Möbius divisor law `∑_{q|n} μ(q) log q = −Λ(n)`;
- the Stieltjes partial summation producing `(18)`;
- the corpus causal graph identity `(19)`.

The card's remaining open gates (prove the causal-complement coefficient bound `(25)`; the one-sided
Landau connector; RH) are route gates, not statements of this card.
