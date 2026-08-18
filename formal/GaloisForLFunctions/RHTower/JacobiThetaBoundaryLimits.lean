import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Boundary limits of the Jacobi theta function at the rational points `1` and `2`

The one-variable theta function is holomorphic on the upper half-plane and has period `2`.  At a
boundary point that is an *even* integer it blows up at the exact rate `‖w‖^{-1/2}`, while at an
*odd* integer it vanishes faster than any power, because the alternating theta series is the
difference of two rapidly convergent transforms.

Both facts follow from the `S`-transformation together with the elementary even/odd split
`θ(1+w) = 2θ(4w) - θ(w)` and mathlib's explicit bound for `‖θ(τ) - 1‖`.

These are the two boundary inputs of Hardy's theorem: the vanishing point produces a finite
half-plane trace, the blow-up point produces the unboundedness that contradicts it.
-/

namespace RHTower

open Complex Filter Topology

open scoped Real

noncomputable section

/-! ## The `S`-transformation in inverse form -/

theorem im_neg_inv (w : ℂ) : (-w⁻¹).im = w.im / Complex.normSq w := by
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]

theorem ne_zero_of_im_pos {w : ℂ} (hw : 0 < w.im) : w ≠ 0 := by
  intro h
  rw [h] at hw
  simp at hw

theorem im_neg_inv_pos {w : ℂ} (hw : 0 < w.im) : 0 < (-w⁻¹).im := by
  rw [im_neg_inv]
  exact div_pos hw (Complex.normSq_pos.2 (ne_zero_of_im_pos hw))

/-- **The `S`-transformation, inverse form.**  `θ(w) = (I/w)^{1/2} θ(-1/w)`. -/
theorem jacobiTheta_eq_cpow_mul {w : ℂ} (hw : 0 < w.im) :
    jacobiTheta w = ((I / w) ^ (1 / 2 : ℂ)) * jacobiTheta (-w⁻¹) := by
  have hne : w ≠ 0 := ne_zero_of_im_pos hw
  have hinv : 0 < (-w⁻¹).im := im_neg_inv_pos hw
  set τ : UpperHalfPlane := ⟨-w⁻¹, hinv⟩ with hτ
  have hS := jacobiTheta_S_smul τ
  have hcoe : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = w := by
    rw [UpperHalfPlane.modular_S_smul]
    show (-(-w⁻¹))⁻¹ = w
    rw [neg_neg, inv_inv]
  have harg : (-I * (τ : ℂ)) = I / w := by
    show (-I * (-w⁻¹)) = I / w
    field_simp
  rw [hcoe, harg] at hS
  exact hS

theorem norm_jacobiTheta_eq {w : ℂ} (hw : 0 < w.im) :
    ‖jacobiTheta w‖ = ‖w‖ ^ (-(1 / 2) : ℝ) * ‖jacobiTheta (-w⁻¹)‖ := by
  have hne : w ≠ 0 := ne_zero_of_im_pos hw
  have hIw : I / w ≠ 0 := div_ne_zero I_ne_zero hne
  have hnormpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hne
  rw [jacobiTheta_eq_cpow_mul hw, norm_mul, Complex.norm_cpow_of_ne_zero hIw]
  have hre : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have him : ((1 : ℂ) / 2).im = 0 := by norm_num
  rw [hre, him, mul_zero, Real.exp_zero, div_one, norm_div, Complex.norm_I]
  congr 1
  rw [one_div ‖w‖, ← Real.rpow_neg_one ‖w‖, ← Real.rpow_mul hnormpos.le]
  norm_num

/-! ## The even/odd split -/

private theorem summable_jacobiTheta_term {w : ℂ} (hw : 0 < w.im) :
    Summable (fun n : ℤ => cexp (↑π * I * (n : ℂ) ^ 2 * w)) := by
  have h := hasSum_jacobiTheta₂_term 0 hw
  have hcongr : (fun n : ℤ => jacobiTheta₂_term n 0 w)
      = fun n : ℤ => cexp (↑π * I * (n : ℂ) ^ 2 * w) := by
    funext n
    simp [jacobiTheta₂_term]
  rw [hcongr] at h
  exact h.summable

private theorem exp_pi_I_sq (n : ℤ) : cexp (↑π * I * (n : ℂ) ^ 2) = (-1 : ℂ) ^ n := by
  have hz : (π : ℂ) * I * (n : ℂ) ^ 2 = ((n ^ 2 : ℤ) : ℂ) * ((π : ℂ) * I) := by
    push_cast
    ring
  rw [hz, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rcases Int.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    have h2 : Even (n ^ 2) := ⟨2 * k ^ 2, by rw [hk]; ring⟩
    rw [Even.neg_one_zpow h2, Even.neg_one_zpow ⟨k, hk⟩]
  · rw [Odd.neg_one_zpow ho.pow, Odd.neg_one_zpow ho]

/-- **The even/odd split.**  `θ(1+w) = 2 θ(4w) - θ(w)`. -/
theorem jacobiTheta_one_add {w : ℂ} (hw : 0 < w.im) :
    jacobiTheta (1 + w) = 2 * jacobiTheta (4 * w) - jacobiTheta w := by
  have hw4 : 0 < ((4 : ℂ) * w).im := by
    rw [Complex.mul_im]
    norm_num
    linarith
  set a : ℤ → ℂ := fun n => cexp (↑π * I * (n : ℂ) ^ 2 * w) with ha
  have hsum : Summable a := summable_jacobiTheta_term hw
  have hshift : jacobiTheta (1 + w) = ∑' n : ℤ, (-1 : ℂ) ^ n * a n := by
    rw [jacobiTheta]
    refine tsum_congr fun n => ?_
    rw [show (↑π : ℂ) * I * (n : ℂ) ^ 2 * (1 + w)
        = (↑π * I * (n : ℂ) ^ 2) + (↑π * I * (n : ℂ) ^ 2 * w) by ring,
      Complex.exp_add, exp_pi_I_sq]
  have halt : Summable (fun n : ℤ => (-1 : ℂ) ^ n * a n) := by
    refine Summable.of_norm ?_
    refine (hsum.norm).congr fun n => ?_
    rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
  have hsummable2 : Summable (fun n : ℤ => ((1 : ℂ) + (-1 : ℂ) ^ n) * a n) := by
    refine (hsum.add halt).congr fun n => ?_
    ring
  have hdouble : HasSum (fun m : ℤ => (2 : ℂ) * a (2 * m))
      (∑' n : ℤ, ((1 : ℂ) + (-1 : ℂ) ^ n) * a n) := by
    have hinj : Function.Injective (fun m : ℤ => 2 * m) := by
      intro x y hxy
      simpa using hxy
    have hzero : ∀ n : ℤ, n ∉ Set.range (fun m : ℤ => 2 * m) →
        ((1 : ℂ) + (-1 : ℂ) ^ n) * a n = 0 := by
      intro n hn
      have hodd : Odd n := by
        rcases Int.even_or_odd n with he | ho
        · obtain ⟨k, hk⟩ := he
          exact absurd (⟨k, by show 2 * k = n; omega⟩ :
            n ∈ Set.range (fun m : ℤ => 2 * m)) hn
        · exact ho
      rw [Odd.neg_one_zpow hodd]
      ring
    have hfun : (fun n : ℤ => ((1 : ℂ) + (-1 : ℂ) ^ n) * a n) ∘ (fun m : ℤ => 2 * m)
        = fun m : ℤ => (2 : ℂ) * a (2 * m) := by
      funext m
      have heven : Even (2 * m) := ⟨m, by ring⟩
      show ((1 : ℂ) + (-1 : ℂ) ^ (2 * m)) * a (2 * m) = 2 * a (2 * m)
      rw [Even.neg_one_zpow heven]
      ring
    rw [← hfun]
    exact (hinj.hasSum_iff hzero).2 hsummable2.hasSum
  have heven4 : ∀ m : ℤ, a (2 * m) = cexp (↑π * I * (m : ℂ) ^ 2 * (4 * w)) := by
    intro m
    show cexp (↑π * I * ((2 * m : ℤ) : ℂ) ^ 2 * w) = cexp (↑π * I * (m : ℂ) ^ 2 * (4 * w))
    congr 1
    push_cast
    ring
  have hthetafour : ∑' m : ℤ, (2 : ℂ) * a (2 * m) = 2 * jacobiTheta (4 * w) := by
    rw [tsum_mul_left, jacobiTheta]
    congr 1
    exact tsum_congr fun m => heven4 m
  have hsplit : ∑' n : ℤ, ((1 : ℂ) + (-1 : ℂ) ^ n) * a n
      = jacobiTheta w + ∑' n : ℤ, (-1 : ℂ) ^ n * a n := by
    rw [jacobiTheta, ← hsum.tsum_add halt]
    refine tsum_congr fun n => ?_
    ring
  have hfinal : (2 : ℂ) * jacobiTheta (4 * w)
      = jacobiTheta w + ∑' n : ℤ, (-1 : ℂ) ^ n * a n := by
    rw [← hthetafour, hdouble.tsum_eq, hsplit]
  rw [hshift]
  linear_combination -hfinal

/-! ## The quarter-scaling of the transformation factor -/

theorem cpow_half_div_four {z : ℂ} (hz : z ≠ 0) :
    (z / 4) ^ (1 / 2 : ℂ) = z ^ (1 / 2 : ℂ) / 2 := by
  have hz4 : z / 4 ≠ 0 := by simp [hz]
  rw [Complex.cpow_def_of_ne_zero hz4, Complex.cpow_def_of_ne_zero hz]
  have hlog : Complex.log (z / 4) = Complex.log z - (Real.log 4 : ℂ) := by
    rw [show z / 4 = ((1 / 4 : ℝ) : ℂ) * z by push_cast; ring,
      Complex.log_ofReal_mul (by norm_num) hz, Real.log_div (by norm_num) (by norm_num)]
    push_cast
    simp
    ring
  rw [hlog, show (Complex.log z - (Real.log 4 : ℂ)) * (1 / 2)
      = Complex.log z * (1 / 2) - (Real.log 4 : ℂ) / 2 by ring, Complex.exp_sub]
  congr 1
  rw [show ((Real.log 4 : ℝ) : ℂ) / 2 = ((Real.log 2 : ℝ) : ℂ) by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring]
  rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]
  norm_num

/-! ## Boundary bounds -/

/-- The universal constant in mathlib's theta tail bound at height at least one. -/
def jacobiThetaTailConstant : ℝ := 2 / (1 - Real.exp (-π))

theorem jacobiThetaTailConstant_pos : 0 < jacobiThetaTailConstant := by
  have hlt : Real.exp (-π) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith [Real.pi_pos]
  rw [jacobiThetaTailConstant]
  have : 0 < 1 - Real.exp (-π) := by linarith
  positivity

/-- Mathlib's tail bound, uniformized above height one. -/
theorem norm_jacobiTheta_sub_one_le' {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta τ - 1‖ ≤ jacobiThetaTailConstant * Real.exp (-π * τ.im) := by
  have hpos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have h := norm_jacobiTheta_sub_one_le hpos
  refine h.trans ?_
  have hmono : Real.exp (-π * τ.im) ≤ Real.exp (-π) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  have hlt : Real.exp (-π) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith [Real.pi_pos]
  have hden : 0 < 1 - Real.exp (-π * τ.im) := by
    have : Real.exp (-π * τ.im) ≤ Real.exp (-π) := hmono
    linarith
  have hden' : 0 < 1 - Real.exp (-π) := by linarith
  rw [jacobiThetaTailConstant]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rw [div_le_div_iff₀ hden hden']
  nlinarith [hmono, Real.exp_pos (-π * τ.im)]

/-- **Blow-up at an even boundary point.**  If the transformed height is large enough that the
theta tail is small, the theta value is at least half the reciprocal square root. -/
theorem le_norm_jacobiTheta {w : ℂ} (hw : 0 < w.im)
    (hsmall : ‖jacobiTheta (-w⁻¹) - 1‖ ≤ 1 / 2) :
    1 / 2 * ‖w‖ ^ (-(1 / 2) : ℝ) ≤ ‖jacobiTheta w‖ := by
  have hlower : (1 : ℝ) / 2 ≤ ‖jacobiTheta (-w⁻¹)‖ := by
    have htri : (1 : ℝ) ≤ ‖jacobiTheta (-w⁻¹)‖ + ‖jacobiTheta (-w⁻¹) - 1‖ := by
      have h := norm_sub_le (jacobiTheta (-w⁻¹)) (jacobiTheta (-w⁻¹) - 1)
      rw [sub_sub_cancel, norm_one] at h
      exact h
    linarith
  rw [norm_jacobiTheta_eq hw]
  have hpow : (0 : ℝ) < ‖w‖ ^ (-(1 / 2) : ℝ) :=
    Real.rpow_pos_of_pos (norm_pos_iff.2 (ne_zero_of_im_pos hw)) _
  nlinarith [hlower, hpow]

/-- **Vanishing at an odd boundary point.**  The alternating theta series at `1 + w` is the
difference of two exponentially small transforms. -/
theorem norm_jacobiTheta_one_add_le {w : ℂ} (hw : 0 < w.im)
    (hM : 4 ≤ w.im / Complex.normSq w) :
    ‖jacobiTheta (1 + w)‖
      ≤ ‖w‖ ^ (-(1 / 2) : ℝ) *
        (2 * jacobiThetaTailConstant * Real.exp (-π * (w.im / Complex.normSq w) / 4)) := by
  have hne : w ≠ 0 := ne_zero_of_im_pos hw
  have hnormsq : 0 < Complex.normSq w := Complex.normSq_pos.2 hne
  set M : ℝ := w.im / Complex.normSq w with hMdef
  have hMim : (-w⁻¹).im = M := im_neg_inv w
  have hw4 : 0 < ((4 : ℂ) * w).im := by
    rw [Complex.mul_im]
    norm_num
    linarith
  have hne4 : (4 : ℂ) * w ≠ 0 := by
    intro h
    exact hne (by simpa using h)
  have hM4 : (-((4 : ℂ) * w)⁻¹).im = M / 4 := by
    rw [im_neg_inv, Complex.mul_im, Complex.normSq_mul]
    norm_num
    rw [hMdef]
    field_simp
    ring
  -- the two transformed values
  have hIw : I / w ≠ 0 := div_ne_zero I_ne_zero hne
  have hfactor : (I / ((4 : ℂ) * w)) ^ (1 / 2 : ℂ) = (I / w) ^ (1 / 2 : ℂ) / 2 := by
    rw [show I / ((4 : ℂ) * w) = (I / w) / 4 by field_simp]
    exact cpow_half_div_four hIw
  have hsplit := jacobiTheta_one_add hw
  rw [jacobiTheta_eq_cpow_mul hw4, jacobiTheta_eq_cpow_mul hw, hfactor] at hsplit
  have hform : jacobiTheta (1 + w)
      = (I / w) ^ (1 / 2 : ℂ) *
        ((jacobiTheta (-((4 : ℂ) * w)⁻¹) - 1) - (jacobiTheta (-w⁻¹) - 1)) := by
    rw [hsplit]
    ring
  have hnormfactor : ‖(I / w) ^ (1 / 2 : ℂ)‖ = ‖w‖ ^ (-(1 / 2) : ℝ) := by
    rw [Complex.norm_cpow_of_ne_zero hIw]
    have hre : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
    have him : ((1 : ℂ) / 2).im = 0 := by norm_num
    rw [hre, him, mul_zero, Real.exp_zero, div_one, norm_div, Complex.norm_I]
    rw [one_div ‖w‖, ← Real.rpow_neg_one ‖w‖,
      ← Real.rpow_mul (norm_pos_iff.2 hne).le]
    norm_num
  have hb1 : ‖jacobiTheta (-((4 : ℂ) * w)⁻¹) - 1‖
      ≤ jacobiThetaTailConstant * Real.exp (-π * (M / 4)) := by
    have h := norm_jacobiTheta_sub_one_le' (τ := -((4 : ℂ) * w)⁻¹) (by rw [hM4]; linarith)
    rwa [hM4] at h
  have hb2 : ‖jacobiTheta (-w⁻¹) - 1‖
      ≤ jacobiThetaTailConstant * Real.exp (-π * (M / 4)) := by
    have h := norm_jacobiTheta_sub_one_le' (τ := -w⁻¹) (by rw [hMim]; linarith)
    rw [hMim] at h
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ jacobiThetaTailConstant_pos.le
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  rw [hform, norm_mul, hnormfactor]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (norm_nonneg w) _)
  refine le_trans (norm_sub_le _ _) ?_
  have harith : -π * M / 4 = -π * (M / 4) := by ring
  rw [harith]
  linarith [hb1, hb2]

end

end RHTower
