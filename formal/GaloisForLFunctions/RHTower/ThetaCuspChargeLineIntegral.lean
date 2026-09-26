import GaloisForLFunctions.RHTower.ThetaCuspChargeSaddleWindow
import GaloisForLFunctions.RHTower.ThetaCuspChargeFarField

open Complex MeasureTheory Set
open scoped Real

namespace RHTower

noncomputable section

theorem integral_exp_neg_mul_abs_eq {c : ℝ} (hc : 0 < c) :
    ∫ x : ℝ, Real.exp (-(c * |x|)) = 2 / c := by
  have h := integral_comp_abs (f := fun y : ℝ => Real.exp (-(c * y)))
  rw [h]
  have h2 := integral_exp_mul_Ioi (a := -c) (by linarith) 0
  have e : (fun x : ℝ => Real.exp (-(c * x))) = fun x => Real.exp (-c * x) := by
    funext x; ring_nf
  rw [e, h2]; simp; field_simp

section Integration

variable {t : ℝ}

theorem continuous_chLine (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) : Continuous (chLine t) := by
  have hβ := chBeta_lt ht (by linarith)
  have hβ0 := chBeta_nonneg ht2
  have hc := continuousOn_chargeTailC (differentiableOn_thetaGroupBasis 1) hβ
  have h1 : Continuous (fun s : ℝ => (s : ℂ) - (chBeta t : ℂ) * Complex.I) := by fun_prop
  have h2 := hc.comp_continuous h1 (fun s => by simp [abs_of_nonneg hβ0])
  unfold chLine
  exact (by fun_prop : Continuous fun s : ℝ => Complex.exp (-Complex.I * chU t * s)).mul h2

theorem integrable_chLine (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) : Integrable (chLine t) := by
  have hβ := chBeta_lt ht (by linarith)
  have hβ0 := chBeta_nonneg ht2
  obtain ⟨M, hM⟩ := exists_thetaGroupBasis_one_cusp
  obtain ⟨C, hC, hbd⟩ := exists_norm_chargeTailC_le (differentiableOn_thetaGroupBasis 1)
    (fun τ hτ => thetaGroupBasis_S 1 hτ) hM hβ0 hβ
  refine MeasureTheory.Integrable.mono' ((integrable_exp_neg_mul_abs' one_pos).const_mul C)
    (continuous_chLine ht ht2).aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  have hz : |((s : ℂ) - (chBeta t : ℂ) * Complex.I).im| ≤ chBeta t := by
    simp [abs_of_nonneg hβ0]
  have h := hbd _ hz
  have hre : ((s : ℂ) - (chBeta t : ℂ) * Complex.I).re = s := by simp
  rw [hre] at h
  unfold chLine
  rw [norm_mul, Complex.norm_exp]
  have : (-Complex.I * (chU t : ℂ) * (s : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero, one_mul]
  simpa using h

/-- The full shifted-line integral. -/
def chLineInt (t : ℝ) : ℂ := ∫ s : ℝ, chLine t s

/-- **Main lower bound for the shifted-line integral.** -/
theorem re_chLineInt_ge (ht : 0 < t) (ht0 : t ≤ 1 / 1000000000) {M : ℝ}
    (hM : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis 1 τ‖ ≤ M * Real.exp (-π * τ.im)) :
    chG0 t * t ^ 3 / 16 - 2 * chBfar t M ≤ (chLineInt t).re := by
  have ht1 : t ≤ 1 := by linarith
  have ht2 : t ^ 2 ≤ 1 / 160 := by nlinarith
  have ht2' : t ^ 2 ≤ 1 / 2 := by linarith
  have ht4 : t ^ 4 ≤ 1 / 6 := by nlinarith [pow_pos ht 2]
  have ht4' : t ^ 4 ≤ 1 := by linarith
  have hG : 0 < chG0 t := by unfold chG0; have := chP0_pos (t := t); positivity
  have hint := integrable_chLine ht ht2'
  have hre_int : Integrable (fun s => (chLine t s).re) := hint.re
  set inner : Set ℝ := Icc (-(t ^ 3 / 4)) (t ^ 3 / 4) with hinner
  set k : ℝ := 36 / t ^ 3 with hk
  have hk0 : 0 < k := by positivity
  set lam : ℝ → ℝ := fun s =>
    9 / 8 * chG0 t * Real.exp (-(k * |s|)) + chBfar t M * Real.exp (-(1 * |s|)) with hlam
  have hκ := chKap_pos ht (by nlinarith)
  have hBf : 0 ≤ chBfar t M := by
    refine le_trans ?_ (le_max_left _ _)
    have hκ' := inv_nonneg.mpr hκ.le
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hκ' 3))
      (Real.exp_pos _).le) (by norm_num)
  have hlam_int : Integrable lam :=
    ((integrable_exp_neg_mul_abs' hk0).const_mul _).add
      ((integrable_exp_neg_mul_abs' one_pos).const_mul _)
  have hlam_val : ∫ s, lam s = chG0 t * t ^ 3 / 16 + 2 * chBfar t M := by
    rw [hlam, integral_add ((integrable_exp_neg_mul_abs' hk0).const_mul _)
      ((integrable_exp_neg_mul_abs' one_pos).const_mul _), integral_const_mul, integral_const_mul,
      integral_exp_neg_mul_abs_eq hk0, integral_exp_neg_mul_abs_eq one_pos, hk]
    field_simp; ring
  -- pointwise bounds
  have hcore : ∀ s, |s| ≤ 144 * t ^ 3 → 0 ≤ (chLine t s).re := by
    intro s hs
    have h := half_le_re_chLine_core ht ht0 hs
    have : 0 ≤ chG0 t * Real.exp ((chPsi t s).re - chR0 t) / 2 := by positivity
    linarith
  have hinner_lb : ∀ s ∈ inner, chG0 t / 4 ≤ (chLine t s).re := by
    intro s hs
    have hs' : |s| ≤ t ^ 3 / 4 := abs_le.mpr ⟨hs.1, hs.2⟩
    have hs144 : |s| ≤ 144 * t ^ 3 := by nlinarith [pow_pos ht 3]
    have h := half_le_re_chLine_core ht ht0 hs144
    have hd := chR0_sub_psi_re_le_inner ht ht1 hs'
    have he : 1 / 2 ≤ Real.exp ((chPsi t s).re - chR0 t) := by
      have := Real.add_one_le_exp ((chPsi t s).re - chR0 t); linarith
    nlinarith
  have hout : ∀ s, -lam s ≤ (chLine t s).re := by
    intro s
    have hl1 : 0 ≤ 9 / 8 * chG0 t * Real.exp (-(k * |s|)) := by positivity
    have hl2 : 0 ≤ chBfar t M * Real.exp (-(1 * |s|)) := by positivity
    have hneg : -‖chLine t s‖ ≤ (chLine t s).re := by
      have := Complex.abs_re_le_norm (chLine t s); have := neg_abs_le (chLine t s).re; linarith
    rcases le_or_gt |s| (144 * t ^ 3) with h1 | h1
    · have := hcore s h1; simp only [hlam]; linarith
    rcases le_or_gt |s| (2 * t ^ 2) with h2 | h2
    · have hw := norm_chLine_le_window ht ht2 h2
      have hmid := chR0_sub_psi_re_ge_mid ht (by linarith) h2
      have hexp : Real.exp ((chPsi t s).re - chR0 t) ≤ Real.exp (-(k * |s|)) := by
        apply Real.exp_le_exp.mpr
        have hsq : 144 * t ^ 3 * |s| ≤ s ^ 2 := by
          rw [← sq_abs s]; nlinarith [abs_nonneg s]
        have : k * |s| ≤ s ^ 2 / (4 * t ^ 6) := by
          rw [hk, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [pow_pos ht 3, abs_nonneg s]
        linarith
      have : ‖chLine t s‖ ≤ 9 / 8 * chG0 t * Real.exp (-(k * |s|)) := by
        refine le_trans hw ?_
        have := mul_le_mul_of_nonneg_left hexp hG.le
        nlinarith
      simp only [hlam]; linarith
    · have hf := norm_chLine_far ht ht4 hM h2.le
      simp only [hlam, one_mul]; linarith
  -- assemble
  have hsplit := integral_add_compl (μ := volume) measurableSet_Icc hre_int (s := inner)
  unfold chLineInt
  have hre_eq : (∫ s, chLine t s).re = ∫ s, (chLine t s).re := (integral_re hint).symm
  rw [hre_eq, ← hsplit]
  have hA : chG0 t / 4 * (t ^ 3 / 2) ≤ ∫ s in inner, (chLine t s).re := by
    have hc : ∫ s in inner, (chG0 t / 4 : ℝ) = chG0 t / 4 * (t ^ 3 / 2) := by
      rw [setIntegral_const, smul_eq_mul, hinner, Real.volume_real_Icc_of_le (by
        have := pow_pos ht 3; linarith)]
      ring
    rw [← hc]
    exact setIntegral_mono_on (integrableOn_const (by simp [hinner, Real.volume_Icc]))
      hre_int.integrableOn measurableSet_Icc hinner_lb
  have hB : -(∫ s, lam s) ≤ ∫ s in innerᶜ, (chLine t s).re := by
    have h1 : ∫ s in innerᶜ, -lam s ≤ ∫ s in innerᶜ, (chLine t s).re :=
      setIntegral_mono_on hlam_int.neg.integrableOn hre_int.integrableOn
        measurableSet_Icc.compl (fun s _ => hout s)
    have h2 : ∫ s in innerᶜ, lam s ≤ ∫ s, lam s :=
      setIntegral_le_integral hlam_int (Filter.Eventually.of_forall fun s => by
        simp only [hlam]; positivity)
    rw [integral_neg] at h1
    linarith
  rw [hlam_val] at hB
  linarith

end Integration

end

end RHTower
