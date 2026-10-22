# The mollified mean square has a floor at one

- **ID:** MMS-FLOOR-001
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** the common-terminus diagnosis; `ZetaGateFromDyadicMeanSquare`, `ZetaOffLineFirstMomentMollifierCredit`
- **Statement:** a detector Dirichlet polynomial with leading coefficient `1` has normalized window mean square at least `1 − ε`.

## Goal

Three corpus lanes (criterion positivity, grid density, Levinson proportion) terminate at the sharp
constant of the mollified second moment. The question this card settles is what that constant can
possibly be worth: whether pushing it down can ever make the off-line displacement chain certify
RH, or only improve a density constant.

## What is proved

Module [`MollifiedMeanSquareFloor`](../../../../../../formal/GaloisForLFunctions/RHTower/MollifiedMeanSquareFloor.lean):

- `RHTower.one_le_coeff_energy` — a normalized coefficient family has energy at least `1`.
- `RHTower.dirPoly_meanSquare_floor` —
  `(T₂−T₁) − 8N(1+log N) ≤ ∫_{T₁}^{T₂} ‖dirPoly N a t‖² dt` whenever `a ⟨0,_⟩ = 1` and `T₁ ≤ T₂`.
  The mean value theorem gives `∫ ≥ ((T₂−T₁) − 8N(1+log N))·S` with `S ≥ 1`; when the bracket is
  negative the claim follows from nonnegativity of the integral instead.
- `RHTower.one_sub_mul_le_dirPoly_meanSquare` — `(1−ε)(T₂−T₁) ≤ Msq` once
  `8N(1+log N) ≤ ε(T₂−T₁)`.
- `RHTower.log_one_sub_le_log_dirPoly_meanSquare_div` — `log(1−ε) ≤ log(Msq/(T₂−T₁))`.

Axiom-clean; wired into `GaloisForLFunctions.RHTower`.

## Consequence for the lane

`exists_zetaOffLineFirstMoment_add_mollifierLogMean_le_of_mollified_meanSquare` reads

```text
2π Σ_ρ m_ρ (β − 1/2) + ∫ log‖Ψ(1/2+it)‖ ≤ (T₂−T₁)/2 · log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb).
```

The mean square appears only inside the logarithm, and the floor bounds that logarithm below by
`log(1−ε)`. So the first term on the right is bounded below by `(T₂−T₁)/2 · log(1−ε)`, which tends
to `0⁻`: it is never a useful negative quantity. Driving the mollified mean-square constant to its
optimum `1` makes that term vanish, and no further. Whatever RH-strength the chain has must come
from `−∫ log‖Ψ(1/2+it)‖ dt`.

Recorded as CANNOT-322.

## Scope, honestly

The floor is proved for the detector Dirichlet polynomial — the object the high-block law and
`ZetaDyadicMeanSquareLaw` actually bound. `ζΨ` itself is not a Dirichlet polynomial, so the same
statement for `∫‖ζΨ(σ₀+it)‖² dt` is not proved here; it should follow from the approximate
functional equation, and that is the open successor.

## Open successor

1. Transport the floor from the detector to `∫‖ζΨ(σ₀+it)‖² dt` through the approximate functional
   equation.
2. Decide the remaining term: is `∫_T^{2T} log‖Ψ(1/2+it)‖ dt` capable of supplying a negative
   quantity of size `≍ T`, or is it also floored? Littlewood's lemma applied to `ζ` alone makes
   `∫ log‖ζ(1/2+it)‖ dt` equal to `2π Σ(β − 1/2)` up to `O(log T)`, which suggests the two sides of
   the chain measure the same quantity; making that precise would decide whether the lane is
   circular at leading order.

## Log
- 2026-09-24 — created; floor, normalized floor and logarithmic floor proved in Lean.
