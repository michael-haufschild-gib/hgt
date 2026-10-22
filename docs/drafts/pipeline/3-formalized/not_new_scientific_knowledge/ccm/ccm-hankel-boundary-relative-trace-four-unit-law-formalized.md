# The four-unit CCM target is a boundary relative-trace density — formalized closure

- **ID:** `ccm-hankel-boundary-relative-trace-four-unit-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-hankel-boundary-relative-trace-four-unit-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [RH-EQUIVALENT TARGET]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCM.CCMBoundaryRelativeTrace` (new)
- `GaloisForLFunctions.RHTower.CCM.CCMHankelGapTraceSlope` — pre-existing carrier of `leakDensity`,
  `tailLeakEnergy`, `hankelGapProfile`, `LeakProfile`, the pole and divisor packets, and the Cauchy
  energy criterion. One theorem (`leakDensity_polePacketProfile`) was exported from an inline `have`
  so that this module can reuse it.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(1)`–`(2)` | `leakDensity`, `LeakProfile` (pre-existing) | the kernel and the sole `L²`-type hypothesis; no trace-class assumption anywhere |
| `(5a)` | `boundaryBlockEnergy` | the one-sided output-boundary block energy, `ℝ≥0∞`-valued, defined unconditionally |
| `(5a)`–`(6)`, `(8)` | `boundaryBlockEnergy_eq_lintegral` | the geometric core: translating the inner half-line, Tonelli, and `vol (Ioo 0 u ∩ Iio t) = min (t, u)` give the exact `min (t, u)` relative-trace kernel |
| `(6)`, finiteness | `boundaryBlockEnergy_eq`, `integrableOn_min_mul` | the block energy is finite and equals the real relative trace, from `min (t,u) ≤ u` alone |
| `(7)`, `(8a)` | `boundaryRelativeTrace_eq` | corner plus cutoff-interface splitting; `crossTrace` is the projection-commutator energy |
| `(8b)` | `cornerTrace` | the local corner block |
| `(8c)` | `cornerTrace_div_le` | proved in the sharper exact form `corner/u ≤ ∫₀ᵘ |ℓ|²`, whose right side tends to `0` |
| `(8d)` | `tendsto_crossTrace_div` | the whole first-order charge crosses the interface: the commutator density is `‖ℓ‖₂²` |
| `(9)` | `boundaryRelativeTrace_div` | the `min (t/u, 1)`-weighted form of the difference quotient |
| `(10)` | `tendsto_boundaryRelativeTrace_div` | the relative-trace density at the origin is the residue energy |
| `(11)` | `boundaryRelativeTrace_eq_gap_sub` | `Δ_ℓ(u) = F_ℓ(0) − F_ℓ(u)` |
| `(12)`–`(13)` | `hankelGapProfile_polePacket`, `boundaryRelativeTrace_polePacket` | the incoming Euler pole has `Δ_pole(u) = 4(1 − e^{−u})` exactly, via the shifted first-moment Laplace integral |
| `(14)` | `tendsto_boundaryRelativeTrace_div_polePacket` | the four-unit budget is an initial boundary-layer density |
| `(15)`–`(16)` | `tendsto_boundaryRelativeTrace_div_divisorPacket` | the density of a finite right-half divisor packet is its Cauchy residue energy |
| `(17)`, ratio form | `tendsto_boundaryRelativeTrace_ratio`, `boundaryRelativeTrace_ratio_le_one_iff` | the completed-to-pole ratio tends to `E/4`, and `E/4 ≤ 1 ↔ the packet is empty` |
| `(17)`, density form | `boundaryRelativeTrace_density_le_four_iff` | every limit of `Δ_E(u)/u` is `≤ 4` if and only if the off-line divisor packet is empty |

## Axioms

`#print axioms` on all nineteen theorems of the module returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The operator-side reading of `(3)`–`(5)`: that `Q_a H_ℓ Q_a`, `Q_a H_ℓ P_a`, `P_a H_ℓ Q_a` are
  Hilbert–Schmidt with the stated kernel-integral norms and that their total is `‖Q_u H_ℓ‖²`. This
  is Hilbert–Schmidt kernel calculus, a cited parent; the Lean module works throughout with the
  kernel-side energies those norms are equal to, which is where the card's own mathematics lives.
- The extended Hilbert–Schmidt norm `(17a)` for a densely defined operator, and with it the
  source-side statements `(18)`, `(19)`, `(19a)`.
- The rational-gauge non-uniformity of section 6, and RH itself.

These are exactly the card's unticked gates.

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCM.CCMBoundaryRelativeTrace`: success.
- `lake build GaloisForLFunctions.RHTower.CCM.CCMHankelGapTraceSlope`: success (after the export).
- `#print axioms` on every theorem: clean.
- Umbrella import added.
