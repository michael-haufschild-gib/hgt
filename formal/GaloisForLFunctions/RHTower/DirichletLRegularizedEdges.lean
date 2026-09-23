import GaloisForLFunctions.RHTower.DirichletLStripGrowth

/-!
# Uniform edge bounds for the regularized L-function

Phragmén–Lindelöf compares a function against a *single* constant on both edges of the strip, but
the two edge bounds available are of different strength: bounded on `Re s = 3` and `O(|t|³)` on
`Re s = -2`.  Dividing by `(s-4)³` equalizes them.  On `Re s = 3` the divisor has modulus at least
`1`, so nothing is lost; on `Re s = -2` it has modulus at least `|t|`, which absorbs the cubic.

Near the real axis, where the polynomial edge bound is silent, continuity of the entire L-function
on a compact segment supplies a bound.
-/

open Complex

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- The L-function of a nontrivial character is bounded on any compact segment of a vertical
line. -/
theorem exists_bound_LFunction_segment {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (a T : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, |t| ≤ T →
      ‖DirichletCharacter.LFunction χ ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B := by
  rcases le_or_gt 0 T with hT | hT
  · have hcont : ContinuousOn
        (fun t : ℝ => ‖DirichletCharacter.LFunction χ ((a : ℂ) + (t : ℂ) * Complex.I)‖)
        (Set.Icc (-T) T) := by
      refine Continuous.continuousOn ?_
      refine continuous_norm.comp ?_
      refine (DirichletCharacter.differentiable_LFunction hχ).continuous.comp ?_
      fun_prop
    obtain ⟨t₀, _, hmax⟩ :=
      isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (by linarith)) hcont
    refine ⟨max ‖DirichletCharacter.LFunction χ ((a : ℂ) + (t₀ : ℂ) * Complex.I)‖ 1,
      lt_of_lt_of_le one_pos (le_max_right _ _), fun t ht => ?_⟩
    have hmem : t ∈ Set.Icc (-T) T := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    exact le_trans (hmax hmem) (le_max_left _ _)
  · exact ⟨1, one_pos, fun t ht => absurd (le_trans (abs_nonneg t) ht) (not_le.mpr hT)⟩

/-- **Uniform edge bounds for the regularized function.**  One constant bounds
`L(s,χ)/(s-4)³` on both edges of the strip. -/
theorem exists_bound_regularized_edges {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧
      (∀ z : ℂ, z.re = 3 →
        ‖DirichletCharacter.LFunction χ z / (z - 4) ^ (3 : ℕ)‖ ≤ C) ∧
      (∀ z : ℂ, z.re = -2 →
        ‖DirichletCharacter.LFunction χ z / (z - 4) ^ (3 : ℕ)‖ ≤ C) := by
  obtain ⟨C₁, hC₁, hright⟩ := exists_bound_LFunction_of_two_le_re χ
  obtain ⟨A, hA, hleft⟩ := exists_bound_LFunction_left_edge hprim
  obtain ⟨Bseg, hBseg, hseg⟩ := exists_bound_LFunction_segment hχ (-2 : ℝ) 2
  refine ⟨max C₁ (max A Bseg), lt_of_lt_of_le hC₁ (le_max_left _ _), ?_, ?_⟩
  · intro z hz
    have hre4 : |(z - 4).re| = 1 := by
      rw [Complex.sub_re, hz]
      norm_num
    have hge : (1 : ℝ) ≤ ‖z - 4‖ := by
      have h := Complex.abs_re_le_norm (z - 4)
      rw [hre4] at h
      exact h
    have hpow : (1 : ℝ) ≤ ‖z - 4‖ ^ (3 : ℕ) := one_le_pow₀ hge
    have hLb : ‖DirichletCharacter.LFunction χ z‖ ≤ C₁ := hright z (by rw [hz]; norm_num)
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ C₁ := hLb
      _ ≤ max C₁ (max A Bseg) := le_max_left _ _
      _ = max C₁ (max A Bseg) * 1 := by ring
      _ ≤ max C₁ (max A Bseg) * ‖z - 4‖ ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_left hpow (le_trans hC₁.le (le_max_left _ _))
  · intro z hz
    have hzeq : z = (-2 : ℂ) + (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hz]
    have hzeq2 : z = (((-2 : ℝ)) : ℂ) + (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hz]
    have him4 : |(z - 4).im| = |z.im| := by rw [Complex.sub_im]; norm_num
    have hgeim : |z.im| ≤ ‖z - 4‖ := by
      have h := Complex.abs_im_le_norm (z - 4)
      rwa [him4] at h
    have hre4 : |(z - 4).re| = 6 := by
      rw [Complex.sub_re, hz]
      norm_num
    have hge6 : (6 : ℝ) ≤ ‖z - 4‖ := by
      have h := Complex.abs_re_le_norm (z - 4)
      rw [hre4] at h
      exact h
    have hpow1 : (1 : ℝ) ≤ ‖z - 4‖ ^ (3 : ℕ) := one_le_pow₀ (by linarith)
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
    rcases le_or_gt 2 |z.im| with hbig | hsmall
    · have hLb : ‖DirichletCharacter.LFunction χ z‖ ≤ A * |z.im| ^ (3 : ℕ) := by
        have h := hleft z.im hbig
        rwa [← hzeq] at h
      have hcube : A * |z.im| ^ (3 : ℕ) ≤ max C₁ (max A Bseg) * ‖z - 4‖ ^ (3 : ℕ) := by
        have h1 : |z.im| ^ (3 : ℕ) ≤ ‖z - 4‖ ^ (3 : ℕ) :=
          pow_le_pow_left₀ (abs_nonneg _) hgeim 3
        have h2 : A ≤ max C₁ (max A Bseg) :=
          le_trans (le_max_left A Bseg) (le_max_right _ _)
        have h3 : (0 : ℝ) ≤ ‖z - 4‖ ^ (3 : ℕ) := by positivity
        nlinarith [h1, h2, h3, hA.le, abs_nonneg z.im]
      exact le_trans hLb hcube
    · have hLb : ‖DirichletCharacter.LFunction χ z‖ ≤ Bseg := by
        have h := hseg z.im hsmall.le
        rwa [← hzeq2] at h
      have h2 : Bseg ≤ max C₁ (max A Bseg) :=
        le_trans (le_max_right A Bseg) (le_max_right _ _)
      calc ‖DirichletCharacter.LFunction χ z‖ ≤ Bseg := hLb
        _ ≤ max C₁ (max A Bseg) := h2
        _ = max C₁ (max A Bseg) * 1 := by ring
        _ ≤ max C₁ (max A Bseg) * ‖z - 4‖ ^ (3 : ℕ) :=
            mul_le_mul_of_nonneg_left hpow1 (le_trans hC₁.le (le_max_left _ _))

end RHTower
