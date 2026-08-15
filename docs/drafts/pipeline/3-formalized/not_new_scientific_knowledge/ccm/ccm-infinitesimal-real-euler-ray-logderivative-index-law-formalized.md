# The infinitesimal real Euler ray has exact off-line log-derivative index — formalized closure

- **ID:** `ccm-infinitesimal-real-euler-ray-logderivative-index-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-infinitesimal-real-euler-ray-logderivative-index-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

`GaloisForLFunctions.RHTower.CCMEulerRayLogDerivativeIndex` (new), over
`CCMDiagonalFockLift` and `CCMHalfUnitCauchySeam`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(7)` | `qPacket_eq` | `1/(z−λ) + 1/(z+λ) = 2z/(z²−λ²)` |
| `(8)` | `packet_contribution` | the packet's contribution to `J` |
| `(9)` | `imagPacketKernel_eq`, `posSemidef_imagPacketMatrix` | a critical-line packet is a sum of two rank-one Gram kernels, hence PSD |
| `(10)` | `realPacketKernel_eq` | an off-line packet is a difference of two rank-one Gram kernels |
| `(10)`, sign | `det_realPacket_two_point`, `det_realPacket_two_point_neg`, `not_posSemidef_realPacketMatrix` | the exact minor `−4a²(x−y)²/(…)²` and its strict negativity: one genuine negative square per off-line packet |
| quartet congruence | `quartet_polarization` | `f·conj g + g·conj f = \|u⟩⟨u\| − \|v⟩⟨v\|` |
| `(17)` | `euler_kernel_diagonal` | `J(x,x) = Q(x)/x` |
| `(11)`, `(12)` | `hasDerivAt_shiftedQuotient` | `d/dω[X(x−ω)/X(x+ω)]` at `ω = 0` is `−2Q(x)` |
| `(13)` | `hasDerivAt_loewnerKernel` | the shifted Cauchy–Loewner kernel has derivative `2J(x,y)` at `ω = 0` |
| rank-one building block | `posSemidef_rankOneMatrix` | a rank-one Gram kernel is PSD |

## Axioms

`#print axioms` on all thirteen declarations returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The Hadamard divisor representation `(6)`. The tree already owns
  `XiC_eq_constant_mul_canonicalProduct` and `logDeriv_XiC_eq_relativeResolventTrace`; what is
  cited is the *summed* form with locally uniform symmetric summation.
- The Krein–Langer generalized-Nevanlinna minimal-factorization theorem, which converts the
  packetwise sign count into the exact negative index `(3)`, and the uniqueness-set restriction
  preserving that index.
- The Euler-region evaluation `(14)`–`(15)`.
- The card's own open gates: `J ⪰ 0` from the Euler–Gamma source, and RH.

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCMEulerRayLogDerivativeIndex`: success.
- `#print axioms` on every declaration: clean.
- Umbrella import added.
