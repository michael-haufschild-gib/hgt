import GaloisForLFunctions.RHTower.DirichletLLogStrip
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Unconditional zero-free strips for actual Dirichlet L-functions

The logarithmic growth estimate for every character gives a Cauchy derivative estimate
on a slightly smaller strip. The exact character 3-4-1 product then excludes zeros
at large heights, with one positive width for all characters of a fixed modulus.
The squared character remains literal, including when it is principal.

For each nonprincipal character, compactness and actual nonvanishing on Re(s)=1
supply the bounded-height part. The final strip uses log(3+|t|), covers every height,
and requires no primitive-character or unproved arithmetic input. Its width may depend
on the character. This supplies a missing BAG rational-major-arc prerequisite; it does
not assert a quantitative AP prime theorem, full cubic cancellation, or RH.
-/

noncomputable section
open Filter Topology Finset Complex
namespace RHTower
variable {Q : ℕ} [NeZero Q]

open Set Metric

/-- Cauchy control of the actual character derivative in the shrinking strip. -/
theorem norm_deriv_LFunction_le_sq_log (χ : DirichletCharacter ℂ Q) {σ t : ℝ} (ht : 9 ≤ |t|)
    (hσ1 : 1 - 1 / (4 * Real.log |t|) ≤ σ) (hσ2 : σ ≤ 3 / 2) :
    ‖deriv (DirichletCharacter.LFunction χ) (↑σ + ↑t * Complex.I)‖
      ≤ 8 * characterLogStripConstant Q * Real.log |t| ^ (2 : ℕ) := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have ht1 : (1 : ℝ) ≤ |t| := by linarith
  -- `log|t| > 2` as in the growth bound
  have hexp2 := exp_two_lt_eight
  have hlogt2 : 2 < Real.log |t| := by
    have h1 : Real.log (Real.exp 2) < Real.log |t| :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hr0 : (0 : ℝ) < 1 / (4 * Real.log |t|) := by positivity
  have hr8 : 1 / (4 * Real.log |t|) ≤ 1 / 8 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  -- facts about points of the closed disc
  have hdisc : ∀ w : ℂ,
      w ∈ closedBall (↑σ + ↑t * Complex.I) (1 / (4 * Real.log |t|)) →
      8 ≤ |w.im| ∧ 1 - 1 / Real.log |w.im| ≤ w.re ∧ w.re ≤ 2
        ∧ Real.log |w.im| ≤ 2 * Real.log |t| := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have hre : (↑σ + ↑t * Complex.I).re = σ := by
      simp [Complex.add_re, Complex.mul_re]
    have him : (↑σ + ↑t * Complex.I).im = t := by
      simp [Complex.add_im, Complex.mul_im]
    have hwre : |w.re - σ| ≤ 1 / (4 * Real.log |t|) := by
      have h1 := Complex.abs_re_le_norm (w - (↑σ + ↑t * Complex.I))
      rw [Complex.sub_re, hre] at h1
      linarith
    have hwim : |w.im - t| ≤ 1 / (4 * Real.log |t|) := by
      have h1 := Complex.abs_im_le_norm (w - (↑σ + ↑t * Complex.I))
      rw [Complex.sub_im, him] at h1
      linarith
    have hwre' := abs_le.1 hwre
    have hwim' := abs_le.1 hwim
    -- `|w.im| ∈ [|t| − 1/8, |t| + 1/8]`
    have habs1 : |t| - 1 / 8 ≤ |w.im| := by
      have h1 : |t| - |w.im| ≤ |t - w.im| := by
        calc |t| - |w.im| ≤ |(|t| - |w.im|)| := le_abs_self _
          _ ≤ |t - w.im| := abs_abs_sub_abs_le_abs_sub _ _
      have h2 : |t - w.im| ≤ 1 / (4 * Real.log |t|) := by
        rw [abs_sub_comm]
        exact hwim
      linarith [hr8]
    have habs2 : |w.im| ≤ |t| + 1 / 8 := by
      have h1 : |w.im| - |t| ≤ |w.im - t| := by
        calc |w.im| - |t| ≤ |(|w.im| - |t|)| := le_abs_self _
          _ ≤ |w.im - t| := abs_abs_sub_abs_le_abs_sub _ _
      linarith [hr8, hwim]
    have h8 : (8 : ℝ) ≤ |w.im| := by linarith
    have hwim0 : (0 : ℝ) < |w.im| := by linarith
    -- `log|w.im| ≤ 2 log|t|` since `|w.im| ≤ |t|²`
    have hsq : |w.im| ≤ |t| ^ (2 : ℕ) := by
      nlinarith
    have hlog2L : Real.log |w.im| ≤ 2 * Real.log |t| := by
      have h1 : Real.log |w.im| ≤ Real.log (|t| ^ (2 : ℕ)) :=
        Real.log_le_log hwim0 hsq
      rwa [Real.log_pow, Nat.cast_ofNat] at h1
    have hlogw0 : (0 : ℝ) < Real.log |w.im| := by
      have h1 : Real.log 8 ≤ Real.log |w.im| :=
        Real.log_le_log (by norm_num) h8
      have h2 : (0 : ℝ) < Real.log 8 :=
        Real.log_pos (by norm_num)
      linarith
    refine ⟨h8, ?_, by linarith [hwre'.2], hlog2L⟩
    -- `1 − 1/log|w.im| ≤ w.re`
    have h1 : 1 / (2 * Real.log |t|) ≤ 1 / Real.log |w.im| := by
      apply div_le_div_of_nonneg_left (by norm_num) hlogw0 hlog2L
    have h2 : σ - 1 / (4 * Real.log |t|) ≤ w.re := by linarith [hwre'.1]
    have h3 : 1 - 1 / (2 * Real.log |t|)
        ≤ σ - 1 / (4 * Real.log |t|) := by
      have : 1 / (2 * Real.log |t|) = 1 / (4 * Real.log |t|)
          + 1 / (4 * Real.log |t|) := by
        field_simp
        ring
      linarith
    linarith
  -- differentiability on the closed disc
  have hdiff : DiffContOnCl ℂ (DirichletCharacter.LFunction χ)
      (ball (↑σ + ↑t * Complex.I) (1 / (4 * Real.log |t|))) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (ne_of_gt hr0)]
    intro w hw
    obtain ⟨h8, _, _, _⟩ := hdisc w hw
    have hne1 : w ≠ 1 := by
      intro h
      rw [h] at h8
      simp at h8
      linarith
    exact (χ.differentiableAt_LFunction w (Or.inl hne1)).differentiableWithinAt
  -- the sphere bound
  have hsphere : ∀ w ∈ sphere (↑σ + ↑t * Complex.I)
      (1 / (4 * Real.log |t|)),
      ‖(DirichletCharacter.LFunction χ) w‖ ≤ 2 * characterLogStripConstant Q * Real.log |t| := by
    intro w hw
    obtain ⟨h8, hσ1', hσ2', hlog2L⟩ :=
      hdisc w (sphere_subset_closedBall hw)
    have h1 : ‖(DirichletCharacter.LFunction χ) (↑w.re + ↑w.im * Complex.I)‖
        ≤ characterLogStripConstant Q * Real.log |w.im| :=
      norm_LFunction_le_log χ h8 hσ1' hσ2'
    rw [Complex.re_add_im] at h1
    have hK := one_le_characterLogStripConstant Q
    nlinarith
  -- Cauchy's estimate at order one
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    1 hr0 hdiff hsphere
  rw [iteratedDeriv_one] at hcauchy
  refine le_trans hcauchy ?_
  simp only [Nat.factorial_one, Nat.cast_one, pow_one, one_mul]
  have hid : 2 * characterLogStripConstant Q * Real.log |t| / (1 / (4 * Real.log |t|))
      = 8 * characterLogStripConstant Q * Real.log |t| ^ (2 : ℕ) := by
    field_simp
    ring
  linarith [hid]

/-- The actual horizontal variation, retaining both endpoint values. -/
theorem norm_LFunction_sub_le_segment (χ : DirichletCharacter ℂ Q) {β σ' t : ℝ} (ht : 9 ≤ |t|)
    (hβ1 : 1 - 1 / (4 * Real.log |t|) ≤ β) (hβσ : β ≤ σ')
    (hσ2 : σ' ≤ 3 / 2) :
    ‖DirichletCharacter.LFunction χ (↑σ' + ↑t * Complex.I) -
        DirichletCharacter.LFunction χ (↑β + ↑t * Complex.I)‖
      ≤ 8 * characterLogStripConstant Q * Real.log |t| ^ (2 : ℕ) * (σ' - β) := by
  rcases hβσ.eq_or_lt with rfl | hβσ
  · simp
  have ht0 : (0 : ℝ) < |t| := by linarith
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp at ht
    linarith
  -- pointwise differentiability of the horizontal restriction
  have hf : ∀ u : ℝ, HasDerivAt (fun v : ℝ => (DirichletCharacter.LFunction χ) (↑v + ↑t * Complex.I))
      (deriv (DirichletCharacter.LFunction χ) (↑u + ↑t * Complex.I)) u := by
    intro u
    have hne : (↑u + ↑t * Complex.I) ≠ 1 := by
      intro h
      have h2 := congrArg Complex.im h
      simp [Complex.add_im, Complex.mul_im] at h2
      exact htne h2
    have h1 : HasDerivAt (fun z : ℂ => z + ↑t * Complex.I) 1 ↑u :=
      (hasDerivAt_id _).add_const _
    have h2 : HasDerivAt (DirichletCharacter.LFunction χ)
        (deriv (DirichletCharacter.LFunction χ) (↑u + ↑t * Complex.I))
        (↑u + ↑t * Complex.I) :=
      (χ.differentiableAt_LFunction _ (Or.inl hne)).hasDerivAt
    have h3 := (h2.comp (↑u : ℂ) h1)
    simp only [mul_one] at h3
    exact h3.comp_ofReal
  have hdiff : DifferentiableOn ℝ
      (fun v : ℝ => (DirichletCharacter.LFunction χ) (↑v + ↑t * Complex.I)) (Set.Icc β σ') :=
    fun u _ => (hf u).differentiableAt.differentiableWithinAt
  have hbound : ∀ u ∈ Set.Ico β σ',
      ‖derivWithin (fun v : ℝ => (DirichletCharacter.LFunction χ) (↑v + ↑t * Complex.I))
        (Set.Icc β σ') u‖ ≤ 8 * characterLogStripConstant Q * Real.log |t| ^ (2 : ℕ) := by
    intro u hu
    rw [(hf u).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hβσ) u (Set.mem_Icc_of_Ico hu))]
    apply norm_deriv_LFunction_le_sq_log χ ht
    · linarith [hu.1]
    · linarith [hu.2]
  have hkey := norm_image_sub_le_of_norm_deriv_le_segment hdiff hbound σ'
    (Set.right_mem_Icc.2 hβσ.le)
  exact hkey

private theorem norm_character_LFunction_le_of_zero (χ : DirichletCharacter ℂ Q)
    {β σ' t : ℝ} (ht : 9 ≤ |t|)
    (hβ1 : 1 - 1 / (4 * Real.log |t|) ≤ β) (hβσ : β < σ')
    (hσ2 : σ' ≤ 3 / 2)
    (hzero : DirichletCharacter.LFunction χ (↑β + ↑t * Complex.I) = 0) :
    ‖DirichletCharacter.LFunction χ (↑σ' + ↑t * Complex.I)‖
      ≤ 8 * characterLogStripConstant Q * Real.log |t| ^ (2 : ℕ) * (σ' - β) := by
  simpa only [hzero, sub_zero] using
    norm_LFunction_sub_le_segment χ ht hβ1 hβσ.le hσ2

/-- Every character of a fixed positive modulus has an unconditional high-height
zero-free strip. The same width handles principal and imprimitive characters. -/
theorem exists_character_zero_free_log_strip (Q : ℕ) [NeZero Q] :
    ∃ c : ℝ, 0 < c ∧ ∀ (χ : DirichletCharacter ℂ Q) (β t : ℝ),
      9 ≤ |t| → 1 - c / Real.log |t| ^ (9 : ℕ) < β →
        DirichletCharacter.LFunction χ (β + t * I) ≠ 0 := by
  let K := characterLogStripConstant Q
  have hK1 : 1 ≤ K := one_le_characterLogStripConstant Q
  have hK : 0 < K := by linarith
  let c : ℝ := 1 / (4 * 16 ^ (4 : ℕ) * K ^ (8 : ℕ))
  have hc : 0 < c := by dsimp [c]; positivity
  have hchalf : c ≤ 1 / 2 := by
    have hK8 : (1 : ℝ) ≤ K ^ (8 : ℕ) := one_le_pow₀ hK1
    dsimp only [c]
    apply (div_le_iff₀ (by positivity : 0 < 4 * 16 ^ (4 : ℕ) * K ^ (8 : ℕ))).mpr
    nlinarith
  refine ⟨c, hc, fun χ β t ht hβ hzero => ?_⟩
  have ht0 : 0 < |t| := by linarith
  have hL2 : 2 < Real.log |t| := by
    have h := Real.log_lt_log (Real.exp_pos 2)
      (lt_of_lt_of_le exp_two_lt_eight (by linarith : 8 ≤ |t|))
    rwa [Real.log_exp] at h
  let L := Real.log |t|
  have hL : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hL9 : 0 < L ^ (9 : ℕ) := by positivity
  have htne : t ≠ 0 := by intro h; simp [h] at ht; linarith
  have hne : (β + t * I : ℂ) ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact htne hi
  have hβ1 : β < 1 := by
    by_contra! hb
    exact χ.LFunction_ne_zero_of_one_le_re (.inr hne) (by simpa using hb) hzero
  let x := c / L ^ (9 : ℕ)
  have hx : 0 < x := div_pos hc hL9
  have hxhalf : x ≤ 1 / 2 := by
    have hLpow : (1 : ℝ) ≤ L ^ (9 : ℕ) := one_le_pow₀ hL1
    exact (div_le_self hc.le hLpow).trans hchalf
  have hxfloor : x ≤ 1 / (4 * L) := by
    dsimp only [x]
    rw [div_le_div_iff₀ hL9 (by positivity)]
    have hL8 : (2 : ℝ) ^ (8 : ℕ) ≤ L ^ (8 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hL2.le 8
    have hpow : L ^ (9 : ℕ) = L ^ (8 : ℕ) * L := by ring
    have hcL : c * (4 * L) ≤ 2 * L := by nlinarith
    nlinarith
  have hβfloor : 1 - 1 / (4 * Real.log |t|) ≤ β := by
    change 1 - x < β at hβ
    change 1 - 1 / (4 * L) ≤ β
    linarith
  have hmid : ‖DirichletCharacter.LFunction χ (((1 + x : ℝ) : ℂ) + t * I)‖ ≤
      16 * K * x * L ^ (2 : ℕ) := by
    have h := norm_character_LFunction_le_of_zero χ ht hβfloor
      (show β < 1 + x by linarith) (show 1 + x ≤ 3 / 2 by linarith) hzero
    change ‖DirichletCharacter.LFunction χ (((1 + x : ℝ) : ℂ) + t * I)‖ ≤
      8 * K * L ^ (2 : ℕ) * (1 + x - β) at h
    change 1 - x < β at hβ
    have hscale : 0 ≤ 8 * K * L ^ (2 : ℕ) := by positivity
    nlinarith
  have hpole : ‖DirichletCharacter.LFunctionTrivChar Q (1 + (x : ℂ))‖ ≤ K / x :=
    norm_LFunctionTrivChar_one_add_le hx (by linarith)
  have hhigh : ‖DirichletCharacter.LFunction (χ ^ 2)
      (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ≤ 2 * K * L := by
    have h2t : 8 ≤ |2 * t| := by rw [abs_mul, abs_two]; linarith
    have hlog2 : 0 < Real.log |2 * t| := Real.log_pos (by rw [abs_mul, abs_two]; linarith)
    have h := norm_LFunction_le_log (χ ^ 2) h2t
      (show 1 - 1 / Real.log |2 * t| ≤ 1 + x by
        have hinv : 0 < 1 / Real.log |2 * t| := by positivity
        linarith)
      (show 1 + x ≤ 2 by linarith)
    have hlog : Real.log |2 * t| ≤ 2 * L := by
      have hsq : |2 * t| ≤ |t| ^ (2 : ℕ) := by rw [abs_mul, abs_two]; nlinarith
      have he := Real.log_le_log (by rw [abs_mul, abs_two]; positivity : 0 < |2 * t|) hsq
      simpa only [Real.log_pow, Nat.cast_ofNat] using he
    change _ ≤ K * Real.log |2 * t| at h
    nlinarith
  have hprod := χ.norm_LFunction_product_ge_one hx t
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at hprod
  have harg2 : (1 : ℂ) + x + I * t = ((1 + x : ℝ) : ℂ) + t * I := by push_cast; ring
  have harg3 : (1 : ℂ) + x + 2 * I * t = ((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [harg2, harg3] at hprod
  have hchain : ‖DirichletCharacter.LFunctionTrivChar Q (1 + (x : ℂ))‖ ^ (3 : ℕ) *
      ‖DirichletCharacter.LFunction χ (((1 + x : ℝ) : ℂ) + t * I)‖ ^ (4 : ℕ) *
      ‖DirichletCharacter.LFunction (χ ^ 2) (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ≤
      (K / x) ^ (3 : ℕ) * (16 * K * x * L ^ (2 : ℕ)) ^ (4 : ℕ) * (2 * K * L) := by
    exact mul_le_mul
      (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hpole 3)
        (pow_le_pow_left₀ (norm_nonneg _) hmid 4) (by positivity) (by positivity))
      hhigh (norm_nonneg _) (by positivity)
  have hcollapse : (K / x) ^ (3 : ℕ) * (16 * K * x * L ^ (2 : ℕ)) ^ (4 : ℕ) *
      (2 * K * L) = 1 / 2 := by
    dsimp only [x, c]
    field_simp [hK.ne', hL.ne']
    ring
  rw [hcollapse] at hchain
  linarith

private theorem exists_character_zero_free_bounded_height
    {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ β t : ℝ, |t| ≤ 9 → 1 - δ < β →
      DirichletCharacter.LFunction χ (β + t * I) ≠ 0 := by
  let S : Set ℂ := (fun t : ℝ => (1 : ℂ) + t * I) '' Set.Icc (-9) 9
  let U : Set ℂ := {s | DirichletCharacter.LFunction χ s ≠ 0}
  have hS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hU : IsOpen U := isOpen_ne_fun (DirichletCharacter.differentiable_LFunction hχ).continuous
    continuous_const
  have hSU : S ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by simp)
  obtain ⟨δ, hδ, hsub⟩ := hS.exists_thickening_subset_open hU hSU
  refine ⟨δ, hδ, fun β t ht hβ => ?_⟩
  by_cases hb : 1 ≤ β
  · exact χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by simpa using hb)
  · apply hsub
    apply Metric.mem_thickening_iff.mpr
    refine ⟨1 + t * I, ⟨t, abs_le.mp ht, rfl⟩, ?_⟩
    have heq : (β + t * I : ℂ) - (1 + t * I) = ((β - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [dist_eq_norm, heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith : β - 1 < 0)]
    linarith

/-- A complete-height zero-free region for every actual nonprincipal character. The
width is positive and fixed for the character; no zero-free or prime-distribution input
is left as an assumption. -/
theorem exists_nonprincipal_character_zero_free_log_strip
    {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ β t : ℝ,
      1 - c / Real.log (3 + |t|) ^ (9 : ℕ) < β →
      DirichletCharacter.LFunction χ (β + t * I) ≠ 0 := by
  obtain ⟨c, hc, hhigh⟩ := exists_character_zero_free_log_strip Q
  obtain ⟨δ, hδ, hlow⟩ := exists_character_zero_free_bounded_height hχ
  let A : ℝ := Real.log 3 ^ (9 : ℕ)
  have hA : 0 < A := by dsimp [A]; exact pow_pos (Real.log_pos (by norm_num)) _
  let d := min c (δ * A)
  have hd : 0 < d := lt_min hc (mul_pos hδ hA)
  refine ⟨d, hd, fun β t hβ => ?_⟩
  have hlog3 : Real.log 3 ≤ Real.log (3 + |t|) :=
    Real.log_le_log (by norm_num) (le_add_of_nonneg_right (abs_nonneg t))
  have hlog0 : 0 < Real.log (3 + |t|) := Real.log_pos (by linarith [abs_nonneg t])
  have hden : 0 < Real.log (3 + |t|) ^ (9 : ℕ) := by positivity
  by_cases ht : 9 ≤ |t|
  · apply hhigh χ β t ht
    have hsmall : 0 < Real.log |t| := Real.log_pos (by linarith)
    have hlogs : Real.log |t| ≤ Real.log (3 + |t|) :=
      Real.log_le_log (by linarith) (by linarith)
    have hpow := pow_le_pow_left₀ hsmall.le hlogs 9
    have hratio : d / Real.log (3 + |t|) ^ (9 : ℕ) ≤ c / Real.log |t| ^ (9 : ℕ) := by
      exact (div_le_div_of_nonneg_right (min_le_left _ _) hden.le).trans
        (div_le_div_of_nonneg_left hc.le (by positivity) hpow)
    linarith
  · apply hlow β t (by linarith)
    have hApow : A ≤ Real.log (3 + |t|) ^ (9 : ℕ) :=
      pow_le_pow_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le hlog3 9
    have hratio : d / Real.log (3 + |t|) ^ (9 : ℕ) ≤ δ := by
      apply (div_le_iff₀ hden).mpr
      exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left hApow hδ.le)
    linarith

end RHTower
