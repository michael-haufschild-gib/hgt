# Shift-covariant pole-to-divisor capacity — formalized closure

- **ID:** `ccm-shift-covariant-pole-divisor-capacity-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-shift-covariant-pole-divisor-capacity-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.RHTower.CCMShiftCovariantPoleDivisorCapacity`

Standing on `CCMQuartetPaleyWiener` (half-line exponential Laplace integral) and
`RHTower/FractionalPartZeta` (no real zeta zero in `(0,1)`).

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(2)`, `(4)`, `(7)` | `polePacketProfile`, `divisorPacketProfile`, `divisorPacketMultiplicity`, `poleDivisorMultiplier` | the incoming Euler pole profile `2e^{-t/2}`, the divisor profile `2∑ m_j e^{-λ_j t}`, the total multiplicity `κ(D)`, and the rational symbol `φ_D(z) = (z+1/2)∑ m_j/(z+λ_j)` |
| `(9)` | `laplace_polePacketProfile`, `laplace_divisorPacketProfile` | both Laplace transforms on `Re z > 0`, from the half-line exponential integral `integral_Ioi_cexp_neg_mul` |
| `(5)`, `(7)` | `poleDivisorMultiplier_mul_pole` | the rational symbol carries the pole transform onto the divisor transform, which is what forces `(7)` once the commutant theorem supplies *some* multiplier |
| `(10)` | `tendsto_inv_add_atTop`, `tendsto_ratio_one`, `tendsto_poleDivisorMultiplier_atTop` | along the positive real axis the symbol tends to `κ(D)`, because each factor `(x+1/2)/(x+λ_j)` tends to one |
| `(6)` | `divisorPacketMultiplicity_le_of_bound` | every uniform bound for the symbol on the right half-plane is at least the total multiplicity. Stated so that no supremum is formed and no `H^∞` norm theory is needed |
| `(11)` | `two_le_divisorPacketMultiplicity` | a nonempty packet closed under conjugation with no real point has total multiplicity at least two. No injectivity of `λ` is needed: a fixed point of the conjugation involution would have zero imaginary part |
| `(12)` | `not_contractive_poleDivisorMultiplier` | no contractive shift-covariant symbol carries a nonempty conjugation-closed divisor packet |
| section 3 arithmetic | `riemannZeta_zero_im_ne_zero` | a zeta zero in the open critical strip is not real, from `RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo` |

## Axioms

`#print axioms` on all ten theorems returns exactly `[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

The commutant theorem `(8)` — bounded translation-covariant operators on `L²(0,∞)` are exactly the
`H^∞` multipliers of the right half-plane — which the card cites as a parent. The Lean statements
work directly with the symbol, so that theorem is used only to know a symbol exists; the cost
computation `(6)`, `(10)` and the exclusion `(12)` are proved about the symbol itself.

Also outside: the cutoff seam density `(14)` and the source-selected cutoff transfer, which are the
card's open gates.

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCMShiftCovariantPoleDivisorCapacity`: success.
- `#print axioms` on every theorem: clean.
- Umbrella import added.
