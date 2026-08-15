# Transverse index trace-slope coercivity — formalized closure

- **ID:** `ccm-transverse-index-trace-slope-coercivity-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-transverse-index-trace-slope-coercivity-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCMTransverseIndexTraceSlopeCoercivity` (new)
- `GaloisForLFunctions.RHTower.CCMShiftCovariantPoleDivisorCapacity` — the divisor profile `(3)`,
  the pole profile `(9)`, the total multiplicity `(2)`, and the half-line exponential integral.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(2)`, `(3)`, `(9)` | `divisorPacketMultiplicity`, `divisorPacketProfile`, `polePacketProfile` | the quantized charge, the anti-causal residue profile, and the incoming pole profile |
| `(5)`, right side | `divisorPacketEnergy` | `E(D) = ‖ℓ_D‖₂²`, the `L²(0,∞)` energy |
| Cauchy weight | `cauchyWeight`, `cauchyWeight_pos`, `cauchyWeight_self`, `re_div_add_conj` | the positive weight `(a_j+a_k)/((a_j+a_k)²+(γ_j−γ_k)²)` and its identification with the real part of the resolvent pairing |
| `(7)`, first half | `ofReal_divisorPacketEnergy`, `divisorPacketEnergy_eq` | the energy is the exact positive Cauchy form `4∑_{j,k} m_j m_k (a_j+a_k)/((a_j+a_k)²+(γ_j−γ_k)²)`, by expanding `\|ℓ_D\|² = ℓ_D conj ℓ_D` into a double exponential sum and integrating each term |
| `(7)`, second half | `diagonal_le_divisorPacketEnergy` | every Cauchy term is positive, so the energy dominates its own diagonal `2∑_j m_j²/a_j` |
| `(6)`, `(8)` | `four_mul_multiplicity_lt_divisorPacketEnergy` | for a nonempty packet with `0 < a_j < 1/2` and `m_j ≥ 1`, `E(D) > 4κ(D)` |
| `(11)` | `polePacketEnergy`, `polePacketEnergy_eq_four` | the incoming pole at depth `1/2` has energy exactly `4` |
| `(13)` | `divisorPacket_isEmpty_of_energy_le_pole` | a nonexpansive pole-to-divisor transfer admits no divisor unit at all |

## Axioms

`#print axioms` on all ten declarations returns exactly `[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The trace-slope identity `(5)` itself — the identification of `−F_D'(0+)` with `‖ℓ_D‖₂²` — which is
  the content of `ccm-hankel-gap-trace-slope-rh-criterion.md`. The Lean module works with the `L²`
  energy directly, so the coercivity `(6)` and the exclusion `(13)` are unconditional statements
  about that energy.
- The three equivalent realizations of the quantized charge (inner-denominator degree, Hardy leakage
  rank, prime-zeta monodromy) listed in section 1.
- The source budget `(12)` and the endpoint trace-slope theorem `(17)`, which the card names as its
  sole remaining RH-bearing obligation.

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCMTransverseIndexTraceSlopeCoercivity`: success.
- `#print axioms` on every theorem: clean.
- Umbrella import added.
