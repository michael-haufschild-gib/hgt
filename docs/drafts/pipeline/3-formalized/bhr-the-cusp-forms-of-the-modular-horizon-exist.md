# BHR — the cusp forms of the modular horizon exist

- **ID:** bhr-cusp-forms-exist
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** gap of `modular-horizon-general-data-cusp-spin-two.md`: `CuspEigenIndex 0` not proved nonempty.
- **Statement:** The mirror-odd sector of `L²(SL₂(ℤ)\ℍ)` is cuspidal and infinite-dimensional; the
  level-one cuspidal eigenbasis is infinite, with infinitely many distinct eigenvalues `λ ≥ ¼`. Maass cusp
  forms for `SL₂(ℤ)` exist, and the modular black hole has infinitely many undamped tones.

## Goal
Make the cusp channel of the modular black hole non-vacuous without a Weyl law. Not an RH route.

## Paper proof
1. **Mirror.** `ι z = -z̄`. For `g = (a b; c d)`, `ι(gz) = g'(ιz)` with `g' = (a −b; −c d) ∈ SL₂(ℤ)`.
2. **Odd ⇒ cuspidal.** If `f` is `SL₂(ℤ)`-invariant and `f∘ι = −f`, then `x ↦ f(x+iy)` is `1`-periodic
   and odd, so `∫₀¹ f(x+iy)dx = ∫_{−1}^0 f = −∫₀¹ f`, hence `0`, for every `y > 0`.
3. **Heights.** If `c ≠ 0`, `Im gz = y/|cz+d|² ≤ y/(cy)² ≤ 1/y`. So `Im w > ½` and `Im gw > ½` force both
   heights below `2` when `c ≠ 0`; when `c = 0`, `g` is a translation.
4. **Field.** `ψ_k` a smooth bump supported in `(2+2k, 3+2k)`, `G_k(w) = ψ_k(Im w) sin(2π Re w)`, which is
   `1`-periodic and odd. `F_k(z) = G_k(γz)` for any `γ` with `Im γz > ½` is well defined by 3, invariant,
   and odd. Near every point it is `G_k ∘ (Möbius)`, hence `C¹`; on the cell it equals `G_k`, so value and
   both weighted derivatives are bounded there. So `F_k` lies in the cusp-zero form pre-domain.
5. **Nonzero, orthogonal.** `F_k = 1` at `¼ + i(5/2+2k)`, an interior point of the cell, so its class is
   nonzero (open sets have positive hyperbolic volume). On the cell `F_j F_k = 0` for `j ≠ k`.
6. **Conclusion.** A finite Hilbert basis would make `CuspidalL2 0` finite-dimensional, contradicting the
   independent family `F_k`. Each eigenvalue space is finite-dimensional (corpus), so infinitely many
   distinct eigenvalues occur; each basis vector is a nonzero cusp eigenfunction with `λ ≥ ¼` (corpus).

## Lean certificate
Module `formal/GaloisForLFunctions/BlackHoleRingdown/TheCuspFormsExist.lean`, wired into
`BlackHoleRingdown.lean`; checked with `lake --old env lean`, no messages; axioms of
`exists_maassCuspForm`, `infinite_undamped_tones`: `propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems |
|---|---|
| Mirror normalizes `SL₂(ℤ)` | `OddCusp.mirror_smul` |
| Odd sector is cuspidal | `OddCusp.horocycle_mean_eq_zero_of_odd`, `OddCusp.levelCuspZero_oddVec` |
| Heights above `½` | `OddCusp.im_smul_le_inv`, `OddCusp.oddProfile_smul_eq` |
| Odd cusp field in the form domain | `OddCusp.oddPre`, `OddCusp.oddCusp`, `OddCusp.isChartC1_oddVec` |
| Nonzero, orthogonal | `OddCusp.oddL2_ne_zero`, `OddCusp.inner_oddL2` |
| Infinite basis, eigenvalues | `infinite_cuspEigenIndex`, `infinite_cuspEigenvalues` |
| Existence; undamped tones | `exists_maassCuspForm`, `infinite_undamped_tones` |

## Reading
The zeros of `ξ` live in the mirror-even sector only: the odd sector is cuspidal, carries no resonance,
and rings undamped. The arithmetic of the zeros enters only through the single even Eisenstein channel.

## Not formalized
- A Weyl law (counting), and the parity of the eigenfunctions obtained.

## Log
- 2026-11-07 — created and formalized.
