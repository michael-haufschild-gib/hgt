# Suzuki arithmetic tangent and inverse-moment holography, formalized

- **ID:** `suzuki-arithmetic-tangent-inverse-moment-holography`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-arithmetic-tangent-inverse-moment-holography.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiArithmeticTangentHolography.lean`
  - determinacy input: `formal/GaloisForLFunctions/HTGeometry/CompactMomentDeterminacy.lean`
  - `(15)`'s convergence half: `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiStrongResolventLimit.lean`
  - Cayley layer: `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiDonoghueHerglotzTransform.lean`,
    `SuzukiFiniteApertureHermiteBiehler.lean`

## Formal content

| Card | Lean |
|---|---|
| `(13)` Cauchy-transform derivatives | `hasDerivAt_suzukiCauchyPow`, `iteratedDeriv_suzukiCauchyPow` (dominated differentiation on the half-gap disc) |
| `(5)` odd central jets | `iteratedDeriv_suzukiDonoghueTransform_odd_zero` (via the Leibniz ladder `iteratedDeriv_succ_succ_suzukiDonoghueTransform`) |
| `(6)` moment reconstruction | `suzukiInverseMomentReconstruction_eq` |
| `(7)` pushforward moments | `suzukiInverseMoment_pushforward` |
| Theorem A determinacy | `suzukiInverseMoment_determinacy` = `map_invSq_eq_of_suzukiInverseMoments` (compact moment determinacy on `[0, δ⁻²]`) + `ext_of_even_of_map_invSq_eq` (even recovery) |
| `(8)`–`(9)` projective shape | `suzukiInverseEvenMoment_dilation`, `suzukiProjectiveMomentShape_geometricScale` |
| `(17)`/`(25)` Livšic tangent | `hasDerivAt_suzukiFourierLivsic_freeBoundary` |
| `(18)` Herglotz tangent | `hasDerivAt_suzukiUpperCayleyInv_parameter`, `hasDerivAt_suzukiHerglotz_freeBoundary` |
| `(15)` convergence half | `tendsto_neumannShiftFamily_id` (pre-existing) |

## What the card actually closes

Theorem A is complete: the odd Taylor jet of the Donoghue transform at the origin reads off every
inverse even moment (`m^{(2n+1)}(0)/(2n+1)! = q_n + q_{n+1}`), the moments are the moments of the
compactly supported pushforward under `t ↦ (t²)⁻¹`, compact moment determinacy identifies the
pushforward, and evenness splits each absolute value into two reflected copies of equal mass —
so **an even finite measure with a spectral gap is determined by its inverse even moments**
(`suzukiInverseMoment_determinacy`), with the scale-free shape `κ_n = q_n/q_1^n` invariant under
every dilation.  The `(16)`–`(18)` block's derivative laws are theorems about arbitrary
characteristic families with the stated nonvanishing side conditions, which is the exact form the
free-boundary expansion consumes.

## Hypotheses

Object data only: the measure is a probability (or finite) measure, even where evenness is used,
with an a.e. spectral gap `δ ≤ |t|`; the derivative laws carry their natural nonvanishing side
conditions (`F(±z) ≠ 0`, `Θ ≠ 1`).  No RH, no numerical certificate, no `sorry`, `axiom`,
`opaque`, or `unsafe`.  Every theorem named above audits to
`[propext, Classical.choice, Quot.sound]`.

## Open boundary

The concrete operator expansion `(15)` and Theorem B's identification with Suzuki's operator stay
paper-level, exactly as Section 9 prescribes: the convergence half is already the corpus theorem
`tendsto_neumannShiftFamily_id`, and what remains is the domain fact `e^x ∈ Dom(A_a)` and the
identification of the family with Suzuki's restricted-Weil operator — the folder's shared
open-research core, deliberately not replaced by an axiom or a wrapper.  The open gates are
research: the source nonvanishing/persistence theorem, the intrinsic cofinal intermediate shift,
the Xi divisor weld, specialist novelty review, and RH.
