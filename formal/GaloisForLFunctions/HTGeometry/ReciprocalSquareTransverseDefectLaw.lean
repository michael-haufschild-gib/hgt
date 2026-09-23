import GaloisForLFunctions.HTGeometry.ConfocalAbelDefectFlow

/-!
# Reciprocal-square transverse-defect law

Reflection-centered reciprocal-square inversion transports horizontal displacement by an exact
universal law.  If `w` is a nonzero spectral coordinate and `lambda = -w⁻²`, then

`|lambda| - Re lambda = 2 (Re w)² / |w|⁴`.

Thus horizontal displacement is charged quadratically and suppressed quartically by radial
height.  A horizontal corridor and a vertical floor give a uniform source-envelope theorem, while
the radical is exactly the reflection axis `Re w = 0`.
-/

open Complex

namespace HTGeometry

noncomputable section

/-- Reflection-centered reciprocal-square coordinate. -/
def reflectedReciprocalSquare (w : ℂ) : ℂ :=
  -(w⁻¹) ^ (2 : ℕ)

/-- Norm of the reflected reciprocal-square coordinate. -/
theorem norm_reflectedReciprocalSquare (w : ℂ) :
    ‖reflectedReciprocalSquare w‖ = (Complex.normSq w)⁻¹ := by
  rw [reflectedReciprocalSquare, norm_neg, norm_pow, norm_inv, inv_pow,
    Complex.sq_norm]

/-- Real part of the reflected reciprocal-square coordinate. -/
theorem reflectedReciprocalSquare_re {w : ℂ} (hw : w ≠ 0) :
    (reflectedReciprocalSquare w).re =
      (w.im ^ (2 : ℕ) - w.re ^ (2 : ℕ)) / (Complex.normSq w) ^ (2 : ℕ) := by
  rw [reflectedReciprocalSquare, Complex.neg_re, pow_two, Complex.mul_re,
    Complex.inv_re, Complex.inv_im]
  have hnormSq : Complex.normSq w ≠ 0 := (Complex.normSq_pos.mpr hw).ne'
  field_simp [hnormSq]
  ring

/-- **Universal reciprocal-square transverse-charge law.**  Horizontal displacement is charged
quadratically and divided by the fourth power of radial distance. -/
theorem transverseDefect_reflectedReciprocalSquare {w : ℂ} (hw : w ≠ 0) :
    transverseDefect (reflectedReciprocalSquare w) =
      2 * w.re ^ (2 : ℕ) / (Complex.normSq w) ^ (2 : ℕ) := by
  rw [transverseDefect, norm_reflectedReciprocalSquare,
    reflectedReciprocalSquare_re hw]
  have hnormSq : Complex.normSq w ≠ 0 := (Complex.normSq_pos.mpr hw).ne'
  field_simp [hnormSq]
  rw [Complex.normSq_apply]
  ring

/-- The radical of reciprocal-square transverse charge is exactly the reflection axis. -/
theorem transverseDefect_reflectedReciprocalSquare_eq_zero_iff
    {w : ℂ} (hw : w ≠ 0) :
    transverseDefect (reflectedReciprocalSquare w) = 0 ↔ w.re = 0 := by
  rw [transverseDefect_reflectedReciprocalSquare hw]
  have hden : (Complex.normSq w) ^ (2 : ℕ) ≠ 0 :=
    pow_ne_zero 2 (Complex.normSq_pos.mpr hw).ne'
  constructor
  · intro h
    have hnum : 2 * w.re ^ (2 : ℕ) = 0 :=
      (div_eq_zero_iff.mp h).resolve_right hden
    exact (mul_eq_zero.mp hnum).resolve_left (by norm_num) |>
      sq_eq_zero_iff.mp
  · intro h
    apply div_eq_zero_iff.mpr
    left
    simp [h]

/-- A horizontal square bound and a vertical square floor give a universal reciprocal-square
defect bound. -/
theorem transverseDefect_reflectedReciprocalSquare_le
    {w : ℂ} {A H : ℝ}
    (hA : 0 ≤ A) (hH : 0 < H)
    (hre : w.re ^ (2 : ℕ) ≤ A) (him : H ≤ w.im ^ (2 : ℕ)) :
    transverseDefect (reflectedReciprocalSquare w) ≤ 2 * A / H ^ (2 : ℕ) := by
  have hw : w ≠ 0 := by
    intro hw
    subst w
    norm_num at him
    linarith
  rw [transverseDefect_reflectedReciprocalSquare hw]
  let D : ℝ := Complex.normSq w
  have hD : D = w.re ^ (2 : ℕ) + w.im ^ (2 : ℕ) := by
    dsimp only [D]
    rw [Complex.normSq_apply]
    ring
  have hHD : H ≤ D := by rw [hD]; nlinarith [sq_nonneg w.re]
  have hDpos : 0 < D := hH.trans_le hHD
  have hsq : H ^ (2 : ℕ) ≤ D ^ (2 : ℕ) := pow_le_pow_left₀ hH.le hHD 2
  have hleft : 2 * w.re ^ (2 : ℕ) * H ^ (2 : ℕ) ≤ 2 * A * D ^ (2 : ℕ) := by
    calc
      2 * w.re ^ (2 : ℕ) * H ^ (2 : ℕ) ≤ 2 * A * H ^ (2 : ℕ) := by
        gcongr
      _ ≤ 2 * A * D ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num) hA)
  rw [show Complex.normSq w = D by rfl]
  exact (div_le_div_iff₀ (sq_pos_of_pos hDpos) (sq_pos_of_pos hH)).2 hleft

/-- Exact source-envelope form of the universal law. -/
theorem transverseDefectEnvelope_reflectedReciprocalSquare_image
    (W : Set ℂ) (hzero : 0 ∉ W) :
    transverseDefectEnvelope (reflectedReciprocalSquare '' W) =
      sSup ((fun w : ℂ =>
        2 * w.re ^ (2 : ℕ) / (Complex.normSq w) ^ (2 : ℕ)) '' W) := by
  rw [transverseDefectEnvelope]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨w, hwW, rfl⟩, rfl⟩
    have hw0 : w ≠ 0 := fun hw => hzero (hw ▸ hwW)
    exact ⟨w, hwW, (transverseDefect_reflectedReciprocalSquare hw0).symm⟩
  · rintro ⟨w, hwW, rfl⟩
    have hw0 : w ≠ 0 := fun hw => hzero (hw ▸ hwW)
    exact ⟨reflectedReciprocalSquare w, ⟨w, hwW, rfl⟩,
      transverseDefect_reflectedReciprocalSquare hw0⟩

/-- **Universal reciprocal-square source bound.**  Every source in a horizontal square corridor
and above a vertical square floor has reciprocal-square transverse envelope at most `2A/H²`. -/
theorem transverseDefectEnvelope_reflectedReciprocalSquare_le
    {W : Set ℂ} (hne : W.Nonempty) {A H : ℝ}
    (hA : 0 ≤ A) (hH : 0 < H)
    (hre : ∀ w ∈ W, w.re ^ (2 : ℕ) ≤ A)
    (him : ∀ w ∈ W, H ≤ w.im ^ (2 : ℕ)) :
    transverseDefectEnvelope (reflectedReciprocalSquare '' W) ≤ 2 * A / H ^ (2 : ℕ) := by
  rw [transverseDefectEnvelope]
  apply csSup_le ((hne.image reflectedReciprocalSquare).image transverseDefect)
  rintro y ⟨z, ⟨w, hw, rfl⟩, rfl⟩
  exact transverseDefect_reflectedReciprocalSquare_le hA hH (hre w hw) (him w hw)

end

end HTGeometry
