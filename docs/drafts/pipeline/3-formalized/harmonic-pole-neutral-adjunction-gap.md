# Harmonic pole-neutral adjunction gap

- **ID:** critical-rigidity-harmonic-pole-adjunction-gap
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Control coefficient mass and the literal prime residual by adjunction energy on the actual finite-horizon pole hyperplane.

## Exact setting

Let `v_m(N)` be the corpus's normalized physical Ramanujan horizon vectors, `Q≥2`, `Q²≤N`, and `18(1+log Q)≤log N`. Suppose `u=Σ_(m≤Q)a_m v_m(N)` satisfies `〈u,v_1(N)〉=0`. This is the actual harmonic pole hyperplane, not the condition `a_1=0`.

## Proof

Write `M=Σa_m²`, `L=Σ(log m+tameDifferent m)a_m²`, and `δ=9(1+log Q)/log N≤1/2`. The proved polarized harmonic Gram estimate, paired against the coefficient unit vector at conductor one, gives

`|a_1|≤δ sqrt M`, hence `a_1²≤M/4`.

The exact first excitation is `2 log 2`, so

`L≥2 log 2 · (M−a_1²)≥(3/2)log 2 · M`.

Insert this into the source-relative prime residual estimate. Since `1+log Q≤(1+log Q)²`, an absolute constant gives

`||R_a||²/log N ≤ C (1+log Q)²/log N · L`.

All constants are uniform over the stated conductor and horizon range. The only hyperplane condition is literal orthogonality to `v_1(N)`.

## Scope

This closes the projection distinction in the relative residual estimate. It is a quantitative approximation tool. Direct prime-dilation squares in the corpus already give stronger prime-form coercivity; no new complete-Weil positivity range is claimed.

## Lean

`CriticalScaleArithmeticRigidity/HarmonicPoleAdjunctionGap.lean`, using the public polarized Gram estimate from `CompletedArithmeticForms.PrimePacketCoercivity` and the exact excitation gap from `SelectiveMultiscaleArithmeticPositivity`.

Declarations: `coefficient_mass_le_harmonic_neutral_adjunction_gap` and `exists_primeResidual_harmonic_neutral_relative_sq_le`. Direct audit passed; only `propext`, `Classical.choice`, `Quot.sound`.
