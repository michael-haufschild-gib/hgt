# Hankel gap-trace slope criterion — formalized closure

- **ID:** `ccm-hankel-gap-trace-slope-rh-criterion-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-hankel-gap-trace-slope-rh-criterion.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCM.CCMHankelGapTraceSlope` (new)
- `GaloisForLFunctions.RHTower.CCM.CCMTransverseIndexTraceSlopeCoercivity` — the Cauchy energy form and
  the coercivity bound.
- `GaloisForLFunctions.RHTower.CCM.CCMShiftCovariantPoleDivisorCapacity` — the divisor and pole profiles.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(1)` | `LeakProfile` | the admissible class: measurable on the half-line with finite first leakage moment |
| `(4)` | `hankelGapProfile`, `hankelGapProfile_eq_shift` | the two forms `∫_u^∞ (t−u)\|ℓ\|²` and `∫_0^∞ r\|ℓ(u+r)\|²`, related by the measure-preserving translation of the half-line |
| `(7)`, exact form | `hankelGapProfile_sub` | `F(u) − F(k) = (k−u)T(k) + ∫_{(u,k]} (t−u)\|ℓ\|²` |
| remainder bounds | `tailLeakEnergy_sub`, `remainder_nonneg`, `remainder_le` | `0 ≤ remainder ≤ (k−u)(T(u) − T(k))` |
| `(5)`–`(6)`, mechanism | `tailLeakEnergy_le_diff_quotient` | the sandwich `T(k) ≤ (F(u)−F(k))/(k−u) ≤ T(u)`, replacing the card's two-term limit argument by an exact two-sided inequality |
| absolute continuity | `tendsto_tailLeakEnergy_right` | right continuity of the tail energy |
| `(5)`–`(6)` | `tendsto_diff_quotient_hankelGapProfile`, `tendsto_initial_slope` | the one-sided derivative is minus the tail energy, and `−F'(0+) = ‖ℓ‖₂²`. No boundary value `ℓ(0)` and no derivative of `ℓ` is used |
| `(4)`, monotonicity | `hankelGapProfile_antitone` | the gap profile is decreasing |
| `(1)` for the two profiles | `exists_uniform_re_bound`, `integrableOn_one_add_mul_exp_neg`, `norm_divisorPacketProfile_le`, `leakProfile_divisorPacket`, `leakProfile_polePacket` | the divisor packet and the incoming pole are admissible |
| `(8)`, `(12)`, `(9)` | `ofReal_leakDensity_divisorPacket`, `integrableOn_sub_mul_cexp_neg_mul`, `tendsto_linear_mul_exp_neg`, `integral_Ioi_sub_mul_cexp_neg_mul`, `hankelGapProfile_divisorPacket` | the exact first-moment Laplace integral `∫_u^∞ (t−u)e^{-bt} dt = e^{-bu}/b²` for `Re b > 0`, by the fundamental theorem of calculus with antiderivative `((u−s)/b − 1/b²)e^{-bs}`; and the closed form of the gap profile of a finite divisor packet |
| `(10)`, `(11)` | `tendsto_initial_slope_divisorPacket`, and `divisorPacketEnergy_eq`, `diagonal_le_divisorPacketEnergy` of the coercivity module | the initial trace slope of a packet is its residue energy, with the exact Cauchy form and the diagonal bound |
| `(14)` | `tailLeakEnergy_polePacket_zero`, `tendsto_initial_slope_polePacket` | the incoming pole has initial trace slope exactly `−4` |
| `(16)`–`(17)` | `divisorPacketEnergy_le_four_iff` | a right-half packet has initial trace loss at most the pole value exactly when it is empty |

## Axioms

`#print axioms` on all 30 declarations returns exactly `[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The Hilbert–Schmidt norm formula identifying `Tr(H_u^* H_u)` of the shifted Hankel operator `(2)`
  with the first-moment tail `(4)` — the card's cited parent.
- The identification of the Xi divisor with the packet data, which is what upgrades the packet
  criterion `(16)`–`(17)` to the RH equivalence.
- The source-side obligation `(18)`–`(20b)`, the card's own open gate.

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCM.CCMHankelGapTraceSlope`: success.
- `#print axioms` on every theorem: clean.
- Umbrella import added.
