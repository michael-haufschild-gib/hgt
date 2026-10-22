import GaloisForLFunctions.RHTower.Deninger.DeningerStrictLineBounds

/-!
# Polynomial bounds from the Poisson side

Mellin inversion on the line `Re s = m + 2` gives decay of order `x^{-m-2}` at infinity, and
inversion on the line `Re s = −1` gives a factor `x` at the origin.  Together they bound every
polynomially weighted supremum of a member of Meyer's space by two line norms of its Poisson sum,
hence — through the seminorm bound for the line norms — by finitely many Schwartz seminorms of two
logarithmic weights of the Poisson sum.

This is the direction opposite to the continuity of the Poisson operator: the topology of Meyer's
space is recovered from the radial data, for the seminorms of order zero.

* `abs_pow_mul_norm_le` : the pointwise polynomial bound.
* `seminorm_zero_le_lineNorm` : the same for the seminorms `p_{m,0}`.
* `exists_bound_seminorm_zero` : **`p_{m,0}(f)` is bounded by finitely many Schwartz seminorms of
  the weights `Z_{m+2}f` and `Z_{-1}f`.**
-/

open scoped Real SchwartzMap FourierTransform ContDiff NNReal
open Complex MeasureTheory GaloisForLFunctions

noncomputable section

namespace RHTower

/-- **The pointwise polynomial bound**: at every polynomial weight, a member of Meyer's space is
bounded by the two line norms of its Poisson sum. -/
theorem abs_pow_mul_norm_le (m : ℕ) (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap) (x : ℝ) :
    |x| ^ m * ‖f x‖
      ≤ 4 / (2 * π) * deningerLineNorm ((((m : ℤ) + 2 : ℤ) : ℝ)) (deningerPoissonValue f)
        + 8 * π ^ 2 / (2 * π) * deningerLineNorm (-1) (deningerPoissonValue f) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  obtain ⟨he, h0, _⟩ := (deningerMeyerCap_mem_iff f).mp hf
  set L₁ : ℝ := deningerLineNorm ((((m : ℤ) + 2 : ℤ) : ℝ)) (deningerPoissonValue f) with hL₁
  set L₂ : ℝ := deningerLineNorm (-1) (deningerPoissonValue f) with hL₂
  have hL₁nn : 0 ≤ L₁ := deningerLineNorm_nonneg _ _
  have hL₂nn : 0 ≤ L₂ := deningerLineNorm_nonneg _ _
  have hfirst : 0 ≤ 4 / (2 * π) * L₁ := by positivity
  have hsecond : 0 ≤ 8 * π ^ 2 / (2 * π) * L₂ := by positivity
  have hkey : ∀ y : ℝ, 0 < y →
      y ^ m * ‖f y‖ ≤ 4 / (2 * π) * L₁ + 8 * π ^ 2 / (2 * π) * L₂ := by
    intro y hy
    rcases le_or_gt y 1 with hle | hgt
    · have hb := norm_le_of_poisson_left f hf hy
      rw [← hL₂] at hb
      have hym : y ^ m ≤ 1 := pow_le_one₀ hy.le hle
      have hstep : y ^ m * ‖f y‖ ≤ ‖f y‖ := by
        nlinarith [norm_nonneg (f y)]
      have hsmall : ‖f y‖ ≤ 8 * π ^ 2 / (2 * π) * L₂ := by
        calc ‖f y‖ ≤ 8 * π ^ 2 / (2 * π) * y * L₂ := hb
          _ ≤ 8 * π ^ 2 / (2 * π) * 1 * L₂ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hle (by positivity)) hL₂nn
          _ = 8 * π ^ 2 / (2 * π) * L₂ := by ring
      linarith
    · have hs : (2 : ℤ) ≤ (m : ℤ) + 2 := by omega
      have hb := norm_le_of_poisson_right ((m : ℤ) + 2) hs f hf hy
      rw [← hL₁] at hb
      have hcast : (((((m : ℤ) + 2 : ℤ)) : ℝ)) = (m : ℝ) + 2 := by push_cast; ring
      rw [hcast] at hb
      have hpow : y ^ m * y ^ (-((m : ℝ) + 2)) = y ^ (-2 : ℝ) := by
        rw [← Real.rpow_natCast y m, ← Real.rpow_add hy]
        congr 1
        ring
      have hle2 : y ^ (-2 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hgt.le (by norm_num)
      have hlarge : y ^ m * ‖f y‖ ≤ 4 / (2 * π) * L₁ := by
        calc y ^ m * ‖f y‖
            ≤ y ^ m * (4 / (2 * π) * y ^ (-((m : ℝ) + 2)) * L₁) :=
              mul_le_mul_of_nonneg_left hb (pow_nonneg hy.le m)
          _ = 4 / (2 * π) * (y ^ m * y ^ (-((m : ℝ) + 2))) * L₁ := by ring
          _ = 4 / (2 * π) * y ^ (-2 : ℝ) * L₁ := by rw [hpow]
          _ ≤ 4 / (2 * π) * 1 * L₁ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hle2 (by positivity)) hL₁nn
          _ = 4 / (2 * π) * L₁ := by ring
      linarith
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have hy : 0 < -x := by linarith
    have hval : f x = f (-x) := (he x).symm
    rw [abs_of_neg hneg, hval]
    exact hkey (-x) hy
  · subst hzero
    rw [h0]
    simp only [norm_zero, mul_zero]
    linarith
  · rw [abs_of_pos hpos]
    exact hkey x hpos

/-- **Every polynomially weighted supremum seminorm of a member of Meyer's space is bounded by the
two line norms of its Poisson sum.** -/
theorem seminorm_zero_le_lineNorm (m : ℕ) (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap) :
    SchwartzMap.seminorm ℂ m 0 f
      ≤ 4 / (2 * π) * deningerLineNorm ((((m : ℤ) + 2 : ℤ) : ℝ)) (deningerPoissonValue f)
        + 8 * π ^ 2 / (2 * π) * deningerLineNorm (-1) (deningerPoissonValue f) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h1 := deningerLineNorm_nonneg ((((m : ℤ) + 2 : ℤ) : ℝ)) (deningerPoissonValue f)
  have h2 := deningerLineNorm_nonneg (-1 : ℝ) (deningerPoissonValue f)
  refine SchwartzMap.seminorm_le_bound' ℂ m 0 f
    (add_nonneg (mul_nonneg (by positivity) h1) (mul_nonneg (by positivity) h2)) fun x => ?_
  rw [iteratedDeriv_zero]
  exact abs_pow_mul_norm_le m f hf x

/-- **The supremum seminorms of a member of Meyer's space are bounded by finitely many Schwartz
seminorms of two logarithmic weights of its Poisson sum.** -/
theorem exists_bound_seminorm_zero (m : ℕ) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap),
      SchwartzMap.seminorm ℂ m 0 f
        ≤ C * ((K.sup (schwartzSeminormFamily ℂ ℝ ℂ))
              (deningerPoissonSchwartz ((m : ℤ) + 2) f hf)
            + (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (deningerPoissonSchwartz (-1) f hf)) := by
  classical
  have hpi : (0 : ℝ) < π := Real.pi_pos
  obtain ⟨K₁, C₁, hC₁, hb₁⟩ := exists_bound_deningerLineNorm ((m : ℤ) + 2)
  obtain ⟨K₂, C₂, hC₂, hb₂⟩ := exists_bound_deningerLineNorm (-1)
  have hle₁ : K₁.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ≤ (K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
    Finset.sup_mono Finset.subset_union_left
  have hle₂ : K₂.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ≤ (K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
    Finset.sup_mono Finset.subset_union_right
  refine ⟨K₁ ∪ K₂, max (4 / (2 * π) * C₁) (8 * π ^ 2 / (2 * π) * C₂), ?_, fun f hf => ?_⟩
  · exact le_max_of_le_left (by positivity)
  set S₁ : ℝ := ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ))
    (deningerPoissonSchwartz ((m : ℤ) + 2) f hf) with hS₁
  set S₂ : ℝ := ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ))
    (deningerPoissonSchwartz (-1) f hf) with hS₂
  have hS₁nn : 0 ≤ S₁ := apply_nonneg _ _
  have hS₂nn : 0 ≤ S₂ := apply_nonneg _ _
  have hL₁ : deningerLineNorm ((((m : ℤ) + 2 : ℤ) : ℝ)) (deningerPoissonValue f) ≤ C₁ * S₁ :=
    (hb₁ f hf).trans (mul_le_mul_of_nonneg_left
      (hle₁ (deningerPoissonSchwartz ((m : ℤ) + 2) f hf)) hC₁)
  have hL₂ : deningerLineNorm (((-1 : ℤ) : ℝ)) (deningerPoissonValue f) ≤ C₂ * S₂ :=
    (hb₂ f hf).trans (mul_le_mul_of_nonneg_left
      (hle₂ (deningerPoissonSchwartz (-1) f hf)) hC₂)
  have hcast : (((-1 : ℤ) : ℝ)) = (-1 : ℝ) := by norm_num
  rw [hcast] at hL₂
  have hmax₁ : 4 / (2 * π) * C₁ ≤ max (4 / (2 * π) * C₁) (8 * π ^ 2 / (2 * π) * C₂) :=
    le_max_left _ _
  have hmax₂ : 8 * π ^ 2 / (2 * π) * C₂ ≤ max (4 / (2 * π) * C₁) (8 * π ^ 2 / (2 * π) * C₂) :=
    le_max_right _ _
  calc SchwartzMap.seminorm ℂ m 0 f
      ≤ 4 / (2 * π) * deningerLineNorm ((((m : ℤ) + 2 : ℤ) : ℝ)) (deningerPoissonValue f)
        + 8 * π ^ 2 / (2 * π) * deningerLineNorm (-1) (deningerPoissonValue f) :=
        seminorm_zero_le_lineNorm m f hf
    _ ≤ 4 / (2 * π) * (C₁ * S₁) + 8 * π ^ 2 / (2 * π) * (C₂ * S₂) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hL₁ (by positivity))
          (mul_le_mul_of_nonneg_left hL₂ (by positivity))
    _ = (4 / (2 * π) * C₁) * S₁ + (8 * π ^ 2 / (2 * π) * C₂) * S₂ := by ring
    _ ≤ max (4 / (2 * π) * C₁) (8 * π ^ 2 / (2 * π) * C₂) * S₁
        + max (4 / (2 * π) * C₁) (8 * π ^ 2 / (2 * π) * C₂) * S₂ :=
        add_le_add (mul_le_mul_of_nonneg_right hmax₁ hS₁nn)
          (mul_le_mul_of_nonneg_right hmax₂ hS₂nn)
    _ = max (4 / (2 * π) * C₁) (8 * π ^ 2 / (2 * π) * C₂) * (S₁ + S₂) := by ring

end RHTower

end
