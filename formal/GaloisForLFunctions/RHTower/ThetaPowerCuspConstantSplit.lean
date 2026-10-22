import GaloisForLFunctions.RHTower.ThetaPowerOffLineParameterSet
import GaloisForLFunctions.RHTower.ThetaGroupFormCuspBounds
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeWindowLaw

/-!
# The cusp constant of the theta-power transform

`F_a(iy) = 2^a e^{-Ey}(1 + O(e^{-πy/2}))`, `E = πa/4`, uniformly in `a ∈ [0, 1/2]`.  Folding the Mellin integral of
`Λ_a = thetaPowerXiC a` with the inversion law and splitting off the cusp constant gives, with `z = (1/2 - iw)/2`,

  `Λ_a(w) = 2^{a-2} [(1/E)^z Γ(z) + (1/E)^{1/2-z} Γ(1/2-z)] + β_a(w)`,

where `β_a` is bounded on every strip `|Im w| ≤ ρ < 1/2` uniformly in `a ∈ (0, 1/2]`.  As `a → 0⁺` the Gamma pair grows
like `(πa/4)^{-1/4}`, so `Λ_a` does not converge to the transform of `θ₃`.
-/

open Complex Real Filter Topology MeasureTheory Set Metric

namespace RHTower

noncomputable section

open Bottcher

variable {a : ℝ}

/-- Three factors within `ε ≤ 1/1000` of `1` keep `u⁴v⁴/w⁸` within `23ε` of `1`. -/
theorem norm_quot_sub_one_le_mul {u v w : ℂ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000)
    (hu : ‖u - 1‖ ≤ ε) (hv : ‖v - 1‖ ≤ ε) (hw : ‖w - 1‖ ≤ ε) :
    ‖u ^ 4 * v ^ 4 / w ^ 8 - 1‖ ≤ 23 * ε := by
  have hvn : ‖v‖ ≤ 1 + ε := by
    calc ‖v‖ = ‖(v - 1) + 1‖ := by ring_nf
      _ ≤ ‖v - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + ε := by rw [norm_one]; linarith
  have huv : ‖u * v - 1‖ ≤ 3 * ε := by
    calc ‖u * v - 1‖ = ‖(u - 1) * v + (v - 1)‖ := by ring_nf
      _ ≤ ‖u - 1‖ * ‖v‖ + ‖v - 1‖ := by refine le_trans (norm_add_le _ _) ?_; rw [norm_mul]
      _ ≤ ε * (1 + ε) + ε := by gcongr
      _ ≤ 3 * ε := by nlinarith
  have h4 := norm_pow_sub_one_le huv 4
  have h8 := norm_pow_sub_one_le hw 8
  have e2 : ε ^ 2 ≤ ε / 1000 := by nlinarith
  have e3 : ε ^ 3 ≤ ε / 1000 := by nlinarith [pow_le_pow_left₀ hε0 hε 2]
  have e4 : ε ^ 4 ≤ ε / 1000 := by nlinarith [pow_le_pow_left₀ hε0 hε 3]
  have e5 : ε ^ 5 ≤ ε / 1000 := by nlinarith [pow_le_pow_left₀ hε0 hε 4]
  have e6 : ε ^ 6 ≤ ε / 1000 := by nlinarith [pow_le_pow_left₀ hε0 hε 5]
  have e7 : ε ^ 7 ≤ ε / 1000 := by nlinarith [pow_le_pow_left₀ hε0 hε 6]
  have e8 : ε ^ 8 ≤ ε / 1000 := by nlinarith [pow_le_pow_left₀ hε0 hε 7]
  have h4' : (1 + 3 * ε) ^ 4 - 1 ≤ 13 * ε := by
    have : (1 + 3 * ε) ^ 4 - 1 = 12 * ε + 54 * ε ^ 2 + 108 * ε ^ 3 + 81 * ε ^ 4 := by ring
    rw [this]; linarith
  have h8' : (1 + ε) ^ 8 - 1 ≤ 9 * ε := by
    have : (1 + ε) ^ 8 - 1 = 8 * ε + 28 * ε ^ 2 + 56 * ε ^ 3 + 70 * ε ^ 4 + 56 * ε ^ 5 + 28 * ε ^ 6 +
        8 * ε ^ 7 + ε ^ 8 := by ring
    rw [this]; linarith
  have hw8 : 991 / 1000 ≤ ‖w ^ 8‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - w ^ 8)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
    linarith
  have hw8pos : 0 < ‖w ^ 8‖ := by linarith
  have hw8ne : w ^ 8 ≠ 0 := norm_pos_iff.mp hw8pos
  have heq : u ^ 4 * v ^ 4 / w ^ 8 - 1 = (((u * v) ^ 4 - 1) - (w ^ 8 - 1)) / w ^ 8 := by
    rw [eq_div_iff hw8ne, sub_mul, div_mul_cancel₀ _ hw8ne]; ring
  rw [heq, norm_div, div_le_iff₀ hw8pos]
  calc ‖((u * v) ^ 4 - 1) - (w ^ 8 - 1)‖ ≤ ‖(u * v) ^ 4 - 1‖ + ‖w ^ 8 - 1‖ := norm_sub_le _ _
    _ ≤ 23 * ε * ‖w ^ 8‖ := by nlinarith

/-- **Exponential approach of `Q = h/(16e^{πiτ})` to `1`.** -/
theorem norm_cuspInfQuot_sub_one_le_exp {τ : ℂ} (hτ : 6 ≤ τ.im) :
    ‖cuspInfQuot τ - 1‖ ≤ 69 * Real.exp (-(π / 2 * τ.im)) := by
  rw [cuspInfQuot_eq]
  have hτ1 : 1 ≤ τ.im := by linarith
  have hT := jacobiThetaTailConstant_le_three
  have hJ := norm_jacobiTheta₂_half_sub_two_le_exp (τ := τ) (by linarith)
  have hJ' : Real.exp (-(π / 2 * τ.im)) ≤ (1 / 20) ^ 3 := by
    have h := exp_neg_pi_lt_twentieth
    have h3 : Real.exp (-(π / 2 * τ.im)) ≤ Real.exp (-π) ^ 3 := by
      rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
      have := Real.pi_pos; push_cast; nlinarith
    exact h3.trans (pow_le_pow_left₀ (Real.exp_pos _).le h.le 3)
  have hpi : Real.exp (-π * τ.im) ≤ Real.exp (-(π / 2 * τ.im)) :=
    Real.exp_le_exp.mpr (by have := Real.pi_pos; nlinarith)
  have hC0 := jacobiThetaTailConstant_pos
  set ε : ℝ := 3 * Real.exp (-(π / 2 * τ.im)) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 / 1000 := by rw [hε]; norm_num at hJ' ⊢; linarith
  have h := norm_quot_sub_one_le_mul (u := jacobiTheta₂ (τ / 2) τ / 2) (v := thetaFour τ)
    (w := thetaThree τ) hε0 hε1 ?_ ?_ ?_
  · rw [hε] at h; linarith
  · have : jacobiTheta₂ (τ / 2) τ / 2 - 1 = (jacobiTheta₂ (τ / 2) τ - 2) / 2 := by ring
    rw [this, norm_div, Complex.norm_two, hε]
    have := Real.exp_pos (-(π / 2 * τ.im))
    linarith
  · have h4 := norm_thetaFour_sub_one_le hτ1
    rw [hε]
    nlinarith [mul_le_mul hT hpi (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 3)]
  · have h3 := norm_thetaThree_sub_one_le hτ1
    rw [hε]
    nlinarith [mul_le_mul hT hpi (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 3)]

/-- `x^s ≤ 1 + x^{1/8}` for `x ≥ 0`, `0 ≤ s ≤ 1/8`. -/
theorem rpow_le_one_add_rpow_eighth {x s : ℝ} (hx : 0 ≤ x) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 8) :
    x ^ s ≤ 1 + x ^ (1 / 8 : ℝ) := by
  rcases le_total x 1 with h | h
  · linarith [Real.rpow_le_one hx h hs0, Real.rpow_nonneg hx (1 / 8 : ℝ)]
  · linarith [Real.rpow_le_rpow_of_exponent_le h hs]

/-- **Uniform cusp remainder.** `|F_a(iy) - 2^a e^{-πay/4}| ≤ C e^{-πy/2}` for `y ≥ 1`, `0 ≤ a ≤ 1/2`. -/
theorem exists_norm_thetaPowerForm_sub_cusp_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 / 2 → ∀ y : ℝ, 1 ≤ y →
      ‖thetaPowerForm a (I * (y : ℂ)) - ((2 : ℝ) ^ a * Real.exp (-(π * (a / 4) * y)) : ℝ)‖ ≤
        C * Real.exp (-(π / 2 * y)) := by
  -- the compact piece `1 ≤ y ≤ 6`
  have hcont : ContinuousOn (fun y : ℝ => ‖thetaThree (I * (y : ℂ))‖ +
      ‖thetaPowerForm (1 / 2) (I * (y : ℂ))‖) (Icc 1 6) := by
    have hmap : ∀ y ∈ Icc (1 : ℝ) 6, I * (y : ℂ) ∈ modUpperSet := fun y hy => by
      show 0 < (I * (y : ℂ)).im; simp; linarith [hy.1]
    have h1 : ContinuousOn (fun y : ℝ => I * (y : ℂ)) (Icc 1 6) := by fun_prop
    refine (ContinuousOn.norm ?_).add (ContinuousOn.norm ?_)
    · refine ContinuousOn.comp (g := thetaThree) (fun τ hτ => ?_) h1 hmap
      exact (differentiableAt_thetaThree hτ).continuousAt.continuousWithinAt
    · exact (differentiableOn_thetaPowerForm (1 / 2)).continuousOn.comp h1 hmap
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max 64 ((max M 0 + 2) * Real.exp (3 * π)), by positivity, fun a ha0 ha1 y hy => ?_⟩
  have hy0 : 0 < (I * (y : ℂ)).im := by simp; linarith
  have h2a : (2 : ℝ) ^ a ≤ 2 := by
    calc (2 : ℝ) ^ a ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hE1 : Real.exp (-(π * (a / 4) * y)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ π * (a / 4) * y := mul_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (by linarith)
    linarith
  rcases le_or_gt y 6 with hy6 | hy6
  · -- compact range
    have hF : ‖thetaPowerForm a (I * (y : ℂ))‖ ≤ max M 0 := by
      rw [norm_thetaPowerForm hy0]
      have hb := rpow_le_one_add_rpow_eighth (norm_nonneg (thetaGroupHauptmodul (I * (y : ℂ))))
        (show 0 ≤ a / 4 by linarith) (show a / 4 ≤ 1 / 8 by linarith)
      have hhalf : ‖thetaPowerForm (1 / 2) (I * (y : ℂ))‖ =
          ‖thetaThree (I * (y : ℂ))‖ * ‖thetaGroupHauptmodul (I * (y : ℂ))‖ ^ (1 / 8 : ℝ) := by
        rw [norm_thetaPowerForm hy0]; norm_num
      have hMy := hM y ⟨hy, hy6⟩
      rw [Real.norm_of_nonneg (by positivity), hhalf] at hMy
      calc ‖thetaThree (I * (y : ℂ))‖ * ‖thetaGroupHauptmodul (I * (y : ℂ))‖ ^ (a / 4)
          ≤ ‖thetaThree (I * (y : ℂ))‖ * (1 + ‖thetaGroupHauptmodul (I * (y : ℂ))‖ ^ (1 / 8 : ℝ)) :=
            mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ ≤ M := by linarith
        _ ≤ max M 0 := le_max_left _ _
    have hc : ‖(((2 : ℝ) ^ a * Real.exp (-(π * (a / 4) * y)) : ℝ) : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      nlinarith [Real.exp_pos (-(π * (a / 4) * y)), Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) a]
    have hexp : 1 ≤ Real.exp (3 * π) * Real.exp (-(π / 2 * y)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by have := Real.pi_pos; nlinarith)
    calc _ ≤ ‖thetaPowerForm a (I * (y : ℂ))‖ + ‖(((2 : ℝ) ^ a * Real.exp (-(π * (a / 4) * y)) : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ max M 0 + 2 := add_le_add hF hc
      _ ≤ (max M 0 + 2) * (Real.exp (3 * π) * Real.exp (-(π / 2 * y))) := by
          have : 0 ≤ max M 0 + 2 := by positivity
          nlinarith
      _ = (max M 0 + 2) * Real.exp (3 * π) * Real.exp (-(π / 2 * y)) := by ring
      _ ≤ max 64 ((max M 0 + 2) * Real.exp (3 * π)) * Real.exp (-(π / 2 * y)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · -- near `i∞`
    have him : (I * (y : ℂ)).im = y := by simp
    have hτ6 : 6 < (I * (y : ℂ)).im := by rw [him]; exact hy6
    have hQ := norm_cuspInfQuot_sub_one_le_exp hτ6.le
    rw [him] at hQ
    have hE8 : Real.exp (-(π / 2 * y)) ≤ (1 / 20) ^ 3 := by
      have h := exp_neg_pi_lt_twentieth
      have h3 : Real.exp (-(π / 2 * y)) ≤ Real.exp (-π) ^ 3 := by
        rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
        have := Real.pi_pos; push_cast; nlinarith
      exact h3.trans (pow_le_pow_left₀ (Real.exp_pos _).le h.le 3)
    have hQh : ‖cuspInfQuot (I * (y : ℂ)) - 1‖ ≤ 1 / 2 := by
      have := Real.exp_pos (-(π / 2 * y)); norm_num at hE8; nlinarith
    have hlog : ‖Complex.log (cuspInfQuot (I * (y : ℂ)))‖ ≤ 3 / 2 * ‖cuspInfQuot (I * (y : ℂ)) - 1‖ := by
      have := Complex.norm_log_one_add_half_le_self hQh
      rwa [add_sub_cancel] at this
    set X : ℂ := Complex.exp (((a / 4 : ℝ) : ℂ) * Complex.log (cuspInfQuot (I * (y : ℂ)))) with hX
    have hXarg : ‖((a / 4 : ℝ) : ℂ) * Complex.log (cuspInfQuot (I * (y : ℂ)))‖ ≤
        3 / 16 * ‖cuspInfQuot (I * (y : ℂ)) - 1‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      calc a / 4 * ‖Complex.log (cuspInfQuot (I * (y : ℂ)))‖
          ≤ 1 / 8 * (3 / 2 * ‖cuspInfQuot (I * (y : ℂ)) - 1‖) :=
            mul_le_mul (by linarith) hlog (norm_nonneg _) (by norm_num)
        _ = 3 / 16 * ‖cuspInfQuot (I * (y : ℂ)) - 1‖ := by ring
    have hX1 : ‖X - 1‖ ≤ 3 / 8 * ‖cuspInfQuot (I * (y : ℂ)) - 1‖ := by
      have hle : ‖((a / 4 : ℝ) : ℂ) * Complex.log (cuspInfQuot (I * (y : ℂ)))‖ ≤ 1 := by linarith
      have := Complex.norm_exp_sub_one_le hle
      rw [← hX] at this; linarith
    have hXn : ‖X‖ ≤ 2 := by
      calc ‖X‖ = ‖(X - 1) + 1‖ := by ring_nf
        _ ≤ ‖X - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    have h3 := norm_thetaThree_sub_one_le (τ := I * (y : ℂ)) (by rw [him]; linarith)
    rw [him] at h3
    have hT := jacobiThetaTailConstant_le_three
    have hpi : Real.exp (-π * y) ≤ Real.exp (-(π / 2 * y)) :=
      Real.exp_le_exp.mpr (by have := Real.pi_pos; nlinarith)
    have h3' : ‖thetaThree (I * (y : ℂ)) - 1‖ ≤ 3 * Real.exp (-(π / 2 * y)) := by
      nlinarith [mul_le_mul hT hpi (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 3),
        jacobiThetaTailConstant_pos]
    have hkey : ‖thetaThree (I * (y : ℂ)) * X - 1‖ ≤ 32 * Real.exp (-(π / 2 * y)) := by
      calc ‖thetaThree (I * (y : ℂ)) * X - 1‖ = ‖(thetaThree (I * (y : ℂ)) - 1) * X + (X - 1)‖ := by
            ring_nf
        _ ≤ ‖thetaThree (I * (y : ℂ)) - 1‖ * ‖X‖ + ‖X - 1‖ := by
            refine le_trans (norm_add_le _ _) ?_; rw [norm_mul]
        _ ≤ 3 * Real.exp (-(π / 2 * y)) * 2 + 3 / 8 * (69 * Real.exp (-(π / 2 * y))) := by
            gcongr; linarith
        _ ≤ 32 * Real.exp (-(π / 2 * y)) := by nlinarith [Real.exp_pos (-(π / 2 * y))]
    have hform := thetaPowerForm_eq_cuspInf a hτ6
    have hcusp : (2 : ℂ) ^ (a : ℂ) * Complex.exp (π * I * (a / 4 : ℝ) * (I * (y : ℂ))) =
        (((2 : ℝ) ^ a * Real.exp (-(π * (a / 4) * y)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_exp]
      push_cast
      congr 2
      linear_combination ((π : ℂ) * ((a : ℂ) / 4) * (y : ℂ)) * I_sq
    rw [hform, ← hX, ← mul_assoc, hcusp, show ((((2 : ℝ) ^ a * Real.exp (-(π * (a / 4) * y)) : ℝ) : ℂ) *
        thetaThree (I * (y : ℂ)) * X - (((2 : ℝ) ^ a * Real.exp (-(π * (a / 4) * y)) : ℝ) : ℂ)) =
        (((2 : ℝ) ^ a * Real.exp (-(π * (a / 4) * y)) : ℝ) : ℂ) * (thetaThree (I * (y : ℂ)) * X - 1) by ring,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc (2 : ℝ) ^ a * Real.exp (-(π * (a / 4) * y)) * ‖thetaThree (I * (y : ℂ)) * X - 1‖
        ≤ 2 * 1 * (32 * Real.exp (-(π / 2 * y))) :=
          mul_le_mul (mul_le_mul h2a hE1 (Real.exp_pos _).le (by norm_num)) hkey (norm_nonneg _)
            (by norm_num)
      _ = 64 * Real.exp (-(π / 2 * y)) := by ring
      _ ≤ max 64 ((max M 0 + 2) * Real.exp (3 * π)) * Real.exp (-(π / 2 * y)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- **Folding by the inversion law.** `Λ_a(w)` is the sum of the half-line transforms at `w` and `-w`. -/
theorem thetaPowerXiC_eq_Ioi_add (ha : 0 < a) (w : ℂ) :
    thetaPowerXiC a w =
      (∫ x in Ioi (0 : ℝ), Complex.exp (-I * w * x) * modTail (thetaPowerForm a) 0 x) +
      ∫ x in Ioi (0 : ℝ), Complex.exp (-I * (-w) * x) * modTail (thetaPowerForm a) 0 x := by
  have hint := integrable_thetaPowerXiC_integrand ha w
  unfold thetaPowerXiC
  rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn hint.integrableOn,
    add_comm]
  congr 1
  have h := integral_comp_neg_Iic (0 : ℝ)
    (fun x => Complex.exp (-I * (-w) * x) * modTail (thetaPowerForm a) 0 x)
  rw [neg_zero] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Iic (fun x _ => ?_)
  show Complex.exp (-I * w * x) * modTail (thetaPowerForm a) 0 x =
    Complex.exp (-I * (-w) * ((-x : ℝ) : ℂ)) * modTail (thetaPowerForm a) 0 (-x)
  rw [modTail_thetaPowerForm_neg, Complex.ofReal_neg]
  ring_nf

/-- **Half-line transform as a truncated Mellin integral.** -/
theorem integral_Ioi_modTail_eq (a : ℝ) (w : ℂ) :
    ∫ x in Ioi (0 : ℝ), Complex.exp (-I * w * x) * modTail (thetaPowerForm a) 0 x =
      (1 / 4) * ∫ y in Ioi (1 : ℝ), (y : ℂ) ^ ((1 / 2 - I * w) / 2 - 1) *
        thetaPowerForm a (I * (y : ℂ)) := by
  set z : ℂ := (1 / 2 - I * w) / 2 with hz
  set g : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun y => thetaPowerForm a (I * (y : ℂ))) with hg
  have h := integral_cexp_mul_comp_exp_two g z
  have hL : (fun x : ℝ => Complex.exp (2 * z * x) * g (Real.exp (2 * x))) =
      (Ioi (0 : ℝ)).indicator
        (fun x => 2 * (Complex.exp (-I * w * x) * modTail (thetaPowerForm a) 0 x)) := by
    funext x
    by_cases hx : 0 < x
    · have h1 : Real.exp (2 * x) ∈ Ioi (1 : ℝ) := by show 1 < Real.exp (2 * x); rw [Real.one_lt_exp_iff]; linarith
      rw [hg, Set.indicator_of_mem h1, Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
      unfold modTail modAxisPoint
      rw [sub_zero, Complex.ofReal_exp]
      have e : Complex.exp (2 * z * x) = Complex.exp (-I * w * x) * Complex.exp ((x : ℂ) / 2) := by
        rw [← Complex.exp_add, hz]; ring_nf
      rw [e]
      push_cast
      ring
    · have h1 : Real.exp (2 * x) ∉ Ioi (1 : ℝ) := by
        simp only [mem_Ioi, not_lt]; exact Real.exp_le_one_iff.mpr (by linarith)
      rw [hg, Set.indicator_of_notMem h1, Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx),
        mul_zero]
  have hR : mellin g z = ∫ y in Ioi (1 : ℝ), (y : ℂ) ^ (z - 1) * thetaPowerForm a (I * (y : ℂ)) := by
    unfold mellin
    have hfun : (fun t : ℝ => (t : ℂ) ^ (z - 1) • g t) =
        (Ioi (1 : ℝ)).indicator (fun t => (t : ℂ) ^ (z - 1) * thetaPowerForm a (I * (t : ℂ))) := by
      funext t
      by_cases ht : t ∈ Ioi (1 : ℝ)
      · rw [hg, Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul]
      · rw [hg, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
    rw [hfun, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  rw [hL, integral_indicator measurableSet_Ioi, integral_const_mul, hR] at h
  linear_combination h / 2

theorem norm_cpow_sub_one_le_rpow {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖(y : ℂ) ^ (s - 1)‖ = y ^ (s.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.sub_re, Complex.one_re]

theorem continuousOn_cpow_sub_one (s : ℂ) :
    ContinuousOn (fun y : ℝ => (y : ℂ) ^ (s - 1)) (Ioi 0) := fun y hy =>
  ((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
    (Or.inl (by simpa using (show (0 : ℝ) < y from hy)))).continuousWithinAt

theorem integrableOn_Ioc_cpow_mul_exp {s : ℂ} (hs : 0 < s.re) (E : ℝ) (hE : 0 ≤ E) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1) * Complex.exp (-((E : ℂ) * y))) (Ioc 0 1) := by
  have hint : IntegrableOn (fun y : ℝ => y ^ (s.re - 1)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  refine hint.mono' ?_ ?_
  · exact ((continuousOn_cpow_sub_one s).mono Ioc_subset_Ioi_self |>.mul
      (by fun_prop : Continuous fun y : ℝ => Complex.exp (-((E : ℂ) * y))).continuousOn).aestronglyMeasurable
      measurableSet_Ioc
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun y hy => ?_)
    rw [norm_mul, norm_cpow_sub_one_le_rpow hy.1]
    have : ‖Complex.exp (-((E : ℂ) * y))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact Real.exp_le_one_iff.mpr (by nlinarith [hy.1])
    calc y ^ (s.re - 1) * ‖Complex.exp (-((E : ℂ) * y))‖ ≤ y ^ (s.re - 1) * 1 :=
          mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hy.1.le _)
      _ = y ^ (s.re - 1) := mul_one _

theorem norm_integral_Ioc_cpow_mul_exp_le {s : ℂ} (hs : 0 < s.re) (E : ℝ) (hE : 0 ≤ E) :
    ‖∫ y in Ioc (0 : ℝ) 1, (y : ℂ) ^ (s - 1) * Complex.exp (-((E : ℂ) * y))‖ ≤ 1 / s.re := by
  have hint : IntegrableOn (fun y : ℝ => y ^ (s.re - 1)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioc).mpr
    (Eventually.of_forall fun y hy => ?_))).trans (le_of_eq ?_)
  · rw [norm_mul, norm_cpow_sub_one_le_rpow hy.1]
    have : ‖Complex.exp (-((E : ℂ) * y))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact Real.exp_le_one_iff.mpr (by nlinarith [hy.1])
    calc y ^ (s.re - 1) * ‖Complex.exp (-((E : ℂ) * y))‖ ≤ y ^ (s.re - 1) * 1 :=
          mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hy.1.le _)
      _ = y ^ (s.re - 1) := mul_one _
  · rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith))]
    simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hs.ne']
    ring

theorem integrableOn_Ioi_cpow_mul_exp {s : ℂ} (hs1 : s.re ≤ 1) {E : ℝ} (hE : 0 < E) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1) * Complex.exp (-((E : ℂ) * y))) (Ioi 1) := by
  refine (exp_neg_integrableOn_Ioi 1 hE).mono' ?_ ?_
  · exact ((continuousOn_cpow_sub_one s).mono (Ioi_subset_Ioi zero_le_one) |>.mul
      (by fun_prop : Continuous fun y : ℝ => Complex.exp (-((E : ℂ) * y))).continuousOn).aestronglyMeasurable
      measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans zero_lt_one hy
    rw [norm_mul, norm_cpow_sub_one_le_rpow hy0, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have : y ^ (s.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy.le (by linarith)
    rw [show -E * y = -(E * y) by ring]
    exact mul_le_of_le_one_left (Real.exp_pos _).le this

/-- `∫_1^∞ y^{s-1} e^{-Ey} dy = (1/E)^s Γ(s) - ∫_0^1 y^{s-1} e^{-Ey} dy`. -/
theorem integral_Ioi_one_cpow_mul_exp {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∫ y in Ioi (1 : ℝ), (y : ℂ) ^ (s - 1) * Complex.exp (-((E : ℂ) * y)) =
      (1 / (E : ℂ)) ^ s * Complex.Gamma s -
        ∫ y in Ioc (0 : ℝ) 1, (y : ℂ) ^ (s - 1) * Complex.exp (-((E : ℂ) * y)) := by
  have hfull := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hE
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (integrableOn_Ioc_cpow_mul_exp hs E hE.le) (integrableOn_Ioi_cpow_mul_exp hs1 hE)] at hfull
  rw [← hfull]
  ring

/-- The Gamma factor `(1/E)^{z} Γ(z)`, `z = (1/2 - iw)/2`, `E = πa/4`. -/
def thetaPowerCuspGamma (a : ℝ) (w : ℂ) : ℂ :=
  (1 / ((π * (a / 4) : ℝ) : ℂ)) ^ ((1 / 2 - I * w) / 2) * Complex.Gamma ((1 / 2 - I * w) / 2)

/-- The cusp-constant main term `2^{a-2}[(1/E)^z Γ(z) + (1/E)^{1/2-z} Γ(1/2-z)]`. -/
def thetaPowerCuspMain (a : ℝ) (w : ℂ) : ℂ :=
  (((2 : ℝ) ^ a / 4 : ℝ) : ℂ) * (thetaPowerCuspGamma a w + thetaPowerCuspGamma a (-w))

theorem re_half_sub_I_mul_div_two (w : ℂ) : ((1 / 2 - I * w) / 2).re = 1 / 4 + w.im / 2 := by
  simp; ring

/-- **The Gamma pair carries the transform.** On `|Im w| ≤ ρ < 1/2`, `Λ_a - main` is bounded uniformly in
`a ∈ (0, 1/2]`. -/
theorem exists_norm_thetaPowerXiC_sub_cuspMain_le {ρ : ℝ} (hρ : ρ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → ∀ w : ℂ, |w.im| ≤ ρ →
      ‖thetaPowerXiC a w - thetaPowerCuspMain a w‖ ≤ C := by
  obtain ⟨CR, hCR0, hCR⟩ := exists_norm_thetaPowerForm_sub_cusp_le
  refine ⟨(2 * (2 * (1 / (1 / 4 - ρ / 2))) + 2 * CR) / 4, by
    have : 0 < 1 / 4 - ρ / 2 := by linarith
    positivity, fun a ha0 ha1 w hw => ?_⟩
  set E : ℝ := π * (a / 4) with hE
  have hE0 : 0 < E := by positivity
  -- one half-line piece
  have hpiece : ∀ v : ℂ, |v.im| ≤ ρ →
      ∃ ε : ℂ, ‖ε‖ ≤ 2 * (1 / (1 / 4 - ρ / 2)) + CR ∧
        ∫ y in Ioi (1 : ℝ), (y : ℂ) ^ ((1 / 2 - I * v) / 2 - 1) * thetaPowerForm a (I * (y : ℂ)) =
          (((2 : ℝ) ^ a : ℝ) : ℂ) * thetaPowerCuspGamma a v + ε := by
    intro v hv
    set s : ℂ := (1 / 2 - I * v) / 2 with hs
    have hsre : s.re = 1 / 4 + v.im / 2 := re_half_sub_I_mul_div_two v
    have hvb := abs_le.mp hv
    have hs0 : 1 / 4 - ρ / 2 ≤ s.re := by rw [hsre]; linarith
    have hs0' : 0 < s.re := by linarith
    have hs1 : s.re ≤ 1 := by rw [hsre]; linarith
    set R : ℝ → ℂ := fun y => thetaPowerForm a (I * (y : ℂ)) -
      (((2 : ℝ) ^ a * Real.exp (-(π * (a / 4) * y)) : ℝ) : ℂ) with hRdef
    have hRb : ∀ y : ℝ, 1 ≤ y → ‖R y‖ ≤ CR * Real.exp (-(π / 2 * y)) := fun y hy =>
      hCR a ha0.le ha1 y hy
    have hFc : ContinuousOn (fun y : ℝ => thetaPowerForm a (I * (y : ℂ))) (Ioi 1) := by
      have h1 : ContinuousOn (fun y : ℝ => I * (y : ℂ)) (Ioi 1) := by fun_prop
      exact (differentiableOn_thetaPowerForm a).continuousOn.comp h1
        (fun y hy => by show 0 < (I * (y : ℂ)).im; simp; linarith [show (1 : ℝ) < y from hy])
    have hRint : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1) * R y) (Ioi 1) := by
      refine ((exp_neg_integrableOn_Ioi 1 (show 0 < π / 2 by positivity)).const_mul CR).mono' ?_ ?_
      · refine ((continuousOn_cpow_sub_one s).mono (Ioi_subset_Ioi zero_le_one) |>.mul
          (hFc.sub ?_)).aestronglyMeasurable measurableSet_Ioi
        exact (by fun_prop : Continuous fun y : ℝ =>
          (((2 : ℝ) ^ a * Real.exp (-(π * (a / 4) * y)) : ℝ) : ℂ)).continuousOn
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
        have hy0 : (0 : ℝ) < y := lt_trans zero_lt_one hy
        rw [norm_mul, norm_cpow_sub_one_le_rpow hy0]
        have hp : y ^ (s.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hy) (by linarith)
        calc y ^ (s.re - 1) * ‖R y‖ ≤ 1 * (CR * Real.exp (-(π / 2 * y))) :=
              mul_le_mul hp (hRb y (le_of_lt hy)) (norm_nonneg _) zero_le_one
          _ = CR * Real.exp (-(π / 2) * y) := by ring_nf
    have hcint := integrableOn_Ioi_cpow_mul_exp hs1 hE0
    have hsplit : (fun y : ℝ => (y : ℂ) ^ (s - 1) * thetaPowerForm a (I * (y : ℂ))) =
        fun y : ℝ => (((2 : ℝ) ^ a : ℝ) : ℂ) * ((y : ℂ) ^ (s - 1) * Complex.exp (-((E : ℂ) * y))) +
          (y : ℂ) ^ (s - 1) * R y := by
      funext y
      simp only [hRdef, hE]
      push_cast
      ring
    rw [hsplit, integral_add (hcint.const_mul _) hRint, integral_const_mul,
      integral_Ioi_one_cpow_mul_exp hs0' hs1 hE0]
    refine ⟨-(((2 : ℝ) ^ a : ℝ) : ℂ) * (∫ y in Ioc (0 : ℝ) 1, (y : ℂ) ^ (s - 1) *
        Complex.exp (-((E : ℂ) * y))) + ∫ y in Ioi (1 : ℝ), (y : ℂ) ^ (s - 1) * R y, ?_, ?_⟩
    · have hJ := norm_integral_Ioc_cpow_mul_exp_le hs0' E hE0.le
      have h2a : ‖(((2 : ℝ) ^ a : ℝ) : ℂ)‖ ≤ 2 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        calc (2 : ℝ) ^ a ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have hJ' : 1 / s.re ≤ 1 / (1 / 4 - ρ / 2) := one_div_le_one_div_of_le (by linarith) hs0
      have hRI : ‖∫ y in Ioi (1 : ℝ), (y : ℂ) ^ (s - 1) * R y‖ ≤ CR := by
        refine (norm_integral_le_of_norm_le (((exp_neg_integrableOn_Ioi 1
          (show 0 < π / 2 by positivity)).const_mul CR)) ((ae_restrict_iff' measurableSet_Ioi).mpr
            (Eventually.of_forall fun y hy => ?_))).trans ?_
        · have hy0 : (0 : ℝ) < y := lt_trans zero_lt_one hy
          rw [norm_mul, norm_cpow_sub_one_le_rpow hy0]
          have hp : y ^ (s.re - 1) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hy) (by linarith)
          calc y ^ (s.re - 1) * ‖R y‖ ≤ 1 * (CR * Real.exp (-(π / 2 * y))) :=
                mul_le_mul hp (hRb y (le_of_lt hy)) (norm_nonneg _) zero_le_one
            _ = CR * Real.exp (-(π / 2) * y) := by ring_nf
        · rw [integral_const_mul, show (fun x : ℝ => Real.exp (-(π / 2) * x)) =
              fun x => Real.exp ((-(π / 2)) * x) from rfl, integral_exp_mul_Ioi (by
              have := Real.pi_pos; linarith) 1]
          have h1 : Real.exp (-(π / 2) * 1) ≤ 1 := Real.exp_le_one_iff.mpr (by
            have := Real.pi_pos; linarith)
          have h2 : 1 ≤ π / 2 := by have := Real.pi_gt_three; linarith
          rw [show -Real.exp (-(π / 2) * 1) / -(π / 2) = Real.exp (-(π / 2) * 1) / (π / 2) by ring]
          have : Real.exp (-(π / 2) * 1) / (π / 2) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith
      calc ‖-(((2 : ℝ) ^ a : ℝ) : ℂ) * (∫ y in Ioc (0 : ℝ) 1, (y : ℂ) ^ (s - 1) *
            Complex.exp (-((E : ℂ) * y))) + ∫ y in Ioi (1 : ℝ), (y : ℂ) ^ (s - 1) * R y‖
          ≤ ‖-(((2 : ℝ) ^ a : ℝ) : ℂ) * (∫ y in Ioc (0 : ℝ) 1, (y : ℂ) ^ (s - 1) *
              Complex.exp (-((E : ℂ) * y)))‖ + ‖∫ y in Ioi (1 : ℝ), (y : ℂ) ^ (s - 1) * R y‖ :=
            norm_add_le _ _
        _ = ‖(((2 : ℝ) ^ a : ℝ) : ℂ)‖ * ‖∫ y in Ioc (0 : ℝ) 1, (y : ℂ) ^ (s - 1) *
              Complex.exp (-((E : ℂ) * y))‖ + ‖∫ y in Ioi (1 : ℝ), (y : ℂ) ^ (s - 1) * R y‖ := by
            rw [norm_mul, norm_neg]
        _ ≤ 2 * (1 / (1 / 4 - ρ / 2)) + CR := by
            gcongr
            exact hJ.trans hJ'
    · unfold thetaPowerCuspGamma
      rw [← hs, hE]
      ring
  obtain ⟨ε₁, hε₁, h₁⟩ := hpiece w hw
  obtain ⟨ε₂, hε₂, h₂⟩ := hpiece (-w) (by rwa [Complex.neg_im, abs_neg])
  rw [thetaPowerXiC_eq_Ioi_add ha0 w, integral_Ioi_modTail_eq, integral_Ioi_modTail_eq, h₁, h₂]
  unfold thetaPowerCuspMain
  have heq : 1 / 4 * ((((2 : ℝ) ^ a : ℝ) : ℂ) * thetaPowerCuspGamma a w + ε₁) +
      1 / 4 * ((((2 : ℝ) ^ a : ℝ) : ℂ) * thetaPowerCuspGamma a (-w) + ε₂) -
      (((2 : ℝ) ^ a / 4 : ℝ) : ℂ) * (thetaPowerCuspGamma a w + thetaPowerCuspGamma a (-w)) =
      (ε₁ + ε₂) / 4 := by push_cast; ring
  rw [heq, norm_div, show ‖(4 : ℂ)‖ = 4 by norm_num]
  have := norm_add_le ε₁ ε₂
  have h4 : (0 : ℝ) < 4 := by norm_num
  rw [div_le_div_iff_of_pos_right h4]
  linarith

end

end RHTower
