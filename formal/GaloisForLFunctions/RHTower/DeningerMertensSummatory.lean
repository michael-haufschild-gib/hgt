import GaloisForLFunctions.RHTower.Sieve.MoebiusSharpKappaTwo
import GaloisForLFunctions.RHTower.Sieve.MoebiusMaximalWindow

/-!
# The unconditional Möbius saving in summatory form

The Möbius summatory function `M(N) = ∑_{n ≤ N} μ(n)` carries the only arithmetic input of the
Möbius--Fourier calculus of the ray: the unconditional zero-free-region estimate

`|M(N)| ≤ B N exp(-(log N)^{1/3}/108)`.

This is PNT-strength cancellation, not the RH-equivalent square-root bound.  The corpus proves it
as a contour estimate at real arguments; here it is transported to the integer summatory function
`Sieve.mertensM` and divided by `N²`, which is the shape Abel summation on the ray consumes.

* `deningerMertensSaving` : the saving factor `exp(-(log N)^{1/3}/108)`.
* `deningerMertensM_rate` : **the unconditional saving, at integer arguments.**
* `deningerMertensM_div_sq_le` : the shape used by Abel summation on the ray.
-/

namespace RHTower

open ArithmeticFunction Filter

noncomputable section

/-- The saving factor of the unconditional Möbius estimate. -/
def deningerMertensSaving (N : ℝ) : ℝ := Real.exp (-((Real.log N) ^ ((1 : ℝ) / 3) / 108))

theorem deningerMertensSaving_pos (N : ℝ) : 0 < deningerMertensSaving N := Real.exp_pos _

/-- **The unconditional Möbius saving at integer arguments.**  This is the corpus's sharp
`κ = 2` contour estimate, restricted to the integer summatory function `Sieve.mertensM`. -/
theorem deningerMertensM_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |Sieve.mertensM N| ≤ B * (N : ℝ) * deningerMertensSaving (N : ℝ) := by
  obtain ⟨B, hB, hrate⟩ := Sieve.exists_norm_sum_moebius_kappa_two_rate
  refine ⟨B, hB, ?_⟩
  have hcomp : ∀ᶠ N : ℕ in atTop,
      ‖∑ n ∈ Finset.range (⌊(N : ℝ)⌋₊ + 1), ((moebius n : ℤ) : ℂ)‖
        ≤ B * (N : ℝ) * Real.exp (-((Real.log (N : ℝ)) ^ ((1 : ℝ) / 3) / 108)) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hrate
  filter_upwards [hcomp] with N hN
  have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
  rw [hfloor] at hN
  have hcast : ‖∑ n ∈ Finset.range (N + 1), ((moebius n : ℤ) : ℂ)‖ = |Sieve.mertensM N| := by
    rw [Sieve.mertensM, show (∑ n ∈ Finset.range (N + 1), ((moebius n : ℤ) : ℂ))
        = (((∑ n ∈ Finset.range (N + 1), ((moebius n : ℤ) : ℝ) : ℝ)) : ℂ) from by
          push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hcast] at hN
  exact hN

/-- The shape the Abel summation on the ray consumes: after dividing by `N²` the saving is
`exp(-(log N)^{1/3}/108)/N`. -/
theorem deningerMertensM_div_sq_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |Sieve.mertensM N| / (N : ℝ) ^ 2
        ≤ B * (deningerMertensSaving (N : ℝ) / (N : ℝ)) := by
  obtain ⟨B, hB, hrate⟩ := deningerMertensM_rate
  refine ⟨B, hB, ?_⟩
  filter_upwards [hrate, eventually_gt_atTop 0] with N hN hNpos
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  rw [div_le_iff₀ (by positivity)]
  have hstep : B * ((N : ℝ) * deningerMertensSaving (N : ℝ))
      = (B * (deningerMertensSaving (N : ℝ) / (N : ℝ))) * (N : ℝ) ^ 2 := by
    field_simp
  calc |Sieve.mertensM N| ≤ B * (N : ℝ) * deningerMertensSaving (N : ℝ) := hN
    _ = B * ((N : ℝ) * deningerMertensSaving (N : ℝ)) := by ring
    _ = (B * (deningerMertensSaving (N : ℝ) / (N : ℝ))) * (N : ℝ) ^ 2 := hstep

end

end RHTower
