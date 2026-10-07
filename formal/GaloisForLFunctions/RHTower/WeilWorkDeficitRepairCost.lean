import GaloisForLFunctions.RHTower.WeilWorkPBAPNullRepair
import GaloisForLFunctions.RHTower.WeilWorkPBAPPacketFourier
import GaloisForLFunctions.RHTower.WeilPositivityRegularPerturbationRigidity
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure

/-!
# Polynomial cost of the actual isolated-atom repair

The repair bumps are exact dilates of one fixed smooth bump. Their Fourier
scaling separates the shrinking support from the logarithmic translation.
This is the repair-cost component of WP06's finite-cancellation route.
-/

open Complex MeasureTheory Set Zeta23
open scoped ComplexConjugate
noncomputable section

namespace RHTower.WeilWorkPBAP

open WeilOneSided WeilSpectral

/-- All actual repair bumps are rescalings of the index-zero bump. -/
theorem narrowBump_eq_scaled_zero (n : ℕ) (u : ℝ) :
    narrowBump n u = narrowBump 0 (((n : ℝ) + 1) * u) := by
  have hs : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [ContDiffBump.apply, narrowBump, Nat.cast_zero, zero_add, mul_one,
    sub_zero, smul_eq_mul]
  congr 1 <;> field_simp

private theorem narrowBumpC_eq_scaled_zero (n : ℕ) (u : ℝ) :
    narrowBumpC n u = narrowBumpC 0 (((n : ℝ) + 1) * u) := by
  exact congrArg Complex.ofReal (narrowBump_eq_scaled_zero n u)

/-- Exact Fourier scaling, including nonreal frequencies. -/
theorem paperFT_narrowBump_scale (n : ℕ) (z : ℂ) :
    paperFT (narrowBumpC n) z = (((n : ℝ) + 1)⁻¹ : ℝ) *
      paperFT (narrowBumpC 0) ((((n : ℝ) + 1)⁻¹ : ℝ) * z) := by
  have hs : 0 < (n : ℝ) + 1 := by positivity
  have h := Measure.integral_comp_mul_left
    (fun u : ℝ => narrowBumpC 0 u *
      Complex.exp (I * ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * z * u)) ((n : ℝ) + 1)
  rw [abs_inv, abs_of_pos hs, Complex.real_smul] at h
  unfold paperFT
  convert h using 1
  · congr 1 with u
    rw [narrowBumpC_eq_scaled_zero]
    congr 1
    congr 1
    push_cast
    field_simp
  · congr 1
    congr 1 with u
    congr 1
    congr 1
    ring

/-- Exact scaling of the physical squared mass used by `atomWeight`. -/
theorem integral_narrowBump_sq_scale (n : ℕ) :
    (∫ u, (narrowBump n u) ^ 2) =
      ((n : ℝ) + 1)⁻¹ * ∫ u, (narrowBump 0 u) ^ 2 := by
  simp_rw [narrowBump_eq_scaled_zero n]
  change (∫ u, (fun v : ℝ => (narrowBump 0 v) ^ 2) (((n : ℝ) + 1) * u)) = _
  rw [Measure.integral_comp_mul_left (fun v : ℝ => (narrowBump 0 v) ^ 2), smul_eq_mul, abs_inv,
    abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]

private theorem integral_narrowBump_scale (n : ℕ) :
    (∫ u, narrowBump n u) = ((n : ℝ) + 1)⁻¹ * ∫ u, narrowBump 0 u := by
  simp_rw [narrowBump_eq_scaled_zero n]
  rw [Measure.integral_comp_mul_left, smul_eq_mul, abs_inv,
    abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]

private theorem paperFT_pairTest (n : ℕ) (σ : ℝ) (z : ℂ) :
    paperFT (pairTest n σ) z =
      (1 + (σ : ℂ) * Complex.exp (I * z * Real.log n)) * paperFT (narrowBumpC n) z := by
  rw [pairTest_eq_sum, paperFT_finset_sum (Finset.range 2)
    (fun m => if m = 0 then (1 : ℂ) else (σ : ℂ))
    (f := fun m u => narrowBumpC n (u - if m = 0 then 0 else Real.log n))
    (fun _ => (contDiff_narrowBumpC n).continuous.comp
      (continuous_id.sub continuous_const))
    (fun _ => (hasCompactSupport_narrowBumpC n).comp_homeomorph (Homeomorph.subRight _))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_true,
    one_ne_zero, if_false, paperFT_translate', Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    one_mul]
  ring

private theorem norm_paperFT_pairTest_real_le (n : ℕ) (σ : ℝ) (hσ : |σ| ≤ 1) (r : ℝ) :
    ‖paperFT (pairTest n σ) r‖ ≤ 2 * ‖paperFT (narrowBumpC n) r‖ := by
  rw [paperFT_pairTest, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc ‖(1 : ℂ) + (σ : ℂ) * Complex.exp (I * (r : ℂ) * Real.log n)‖
      ≤ 1 + |σ| := by
        convert norm_add_le (1 : ℂ) ((σ : ℂ) * Complex.exp (I * (r : ℂ) * Real.log n)) using 1
        simp only [norm_mul, norm_one, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_exp, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
            one_mul, Real.exp_zero, mul_one]
    _ ≤ 2 := by linarith

private def repairGammaConst : ℝ :=
  |digammaVerticalGrowthConst (1 / 4) + Real.log Real.pi + 1| + 1

private theorem repairGammaConst_pos : 0 < repairGammaConst := by
  unfold repairGammaConst
  positivity

private def repairGammaMajorant (r : ℝ) : ℝ :=
  ‖paperFT (narrowBumpC 0) r‖ ^ 2 * (repairGammaConst + |r|)

private theorem integrable_repairGammaMajorant : Integrable repairGammaMajorant := by
  obtain ⟨a, ha⟩ := exists_abs_bound_of_hasCompactSupport (hasCompactSupport_narrowBumpC 0)
  have hs : tsupport (narrowBumpC 0) ⊆ Icc (-a) a := by
    apply closure_minimal _ isClosed_Icc
    intro u hu
    exact abs_le.mp (ha u hu)
  apply integrable_normSq_paperFT_mul_of_linear
    ((contDiff_narrowBumpC 0).of_le (by norm_cast)) hs
    (continuous_const.add continuous_abs) (Mp := repairGammaConst + 1)
  intro r
  change |repairGammaConst + (|r|)| ≤ _
  rw [abs_of_nonneg (add_nonneg repairGammaConst_pos.le (abs_nonneg r))]
  nlinarith [repairGammaConst_pos, abs_nonneg r,
    mul_nonneg repairGammaConst_pos.le (abs_nonneg r)]

private theorem pairTest_gamma_majorant (n : ℕ) (σ : ℝ) (hσ : |σ| ≤ 1) (r : ℝ) :
    ‖paperFT (pairTest n σ) r‖ ^ 2 * |EF.gammaBracket r| ≤
      4 * ((n : ℝ) + 1)⁻¹ * repairGammaMajorant (((n : ℝ) + 1)⁻¹ * r) := by
  let d : ℝ := ((n : ℝ) + 1)⁻¹
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := by
    dsimp [d]
    exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hf := norm_paperFT_pairTest_real_le n σ hσ r
  rw [paperFT_narrowBump_scale, norm_mul, Complex.norm_real, Real.norm_of_nonneg hd.le] at hf
  have hcast : ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * (r : ℂ) = ((d * r : ℝ) : ℂ) := by
    simp [d]
  rw [hcast] at hf
  have hg : |EF.gammaBracket r| ≤ repairGammaConst + |r| :=
    (abs_gammaBracket_le r).trans (by
      unfold repairGammaConst
      linarith [le_abs_self (digammaVerticalGrowthConst (1 / 4) + Real.log Real.pi + 1)])
  have hf2 := pow_le_pow_left₀ (norm_nonneg _) hf 2
  calc ‖paperFT (pairTest n σ) r‖ ^ 2 * |EF.gammaBracket r|
      ≤ (2 * (d * ‖paperFT (narrowBumpC 0) ((d * r : ℝ) : ℂ)‖)) ^ 2 *
        (repairGammaConst + |r|) :=
          mul_le_mul hf2 hg (abs_nonneg _) (by positivity)
    _ ≤ 4 * d * repairGammaMajorant (d * r) := by
      unfold repairGammaMajorant
      rw [abs_mul, abs_of_pos hd]
      have h := mul_nonneg
        (mul_nonneg (sq_nonneg ‖paperFT (narrowBumpC 0) ((d * r : ℝ) : ℂ)‖)
          repairGammaConst_pos.le) (mul_nonneg hd.le (sub_nonneg.mpr hd1))
      nlinarith

private theorem integral_pairTest_gamma_norm_le (n : ℕ) (σ : ℝ) (hσ : |σ| ≤ 1) :
    ‖∫ r : ℝ, paperFT (EF.weilTest (pairTest n σ) (pairTest n σ)) r *
      (EF.gammaBracket r : ℂ)‖ ≤ 4 * ∫ r, repairGammaMajorant r := by
  have hs : 0 < (n : ℝ) + 1 := by positivity
  have hm : Integrable (fun r : ℝ =>
      4 * ((n : ℝ) + 1)⁻¹ * repairGammaMajorant (((n : ℝ) + 1)⁻¹ * r)) :=
    (integrable_repairGammaMajorant.comp_mul_left' (inv_ne_zero hs.ne')).const_mul _
  calc ‖∫ r : ℝ, paperFT (EF.weilTest (pairTest n σ) (pairTest n σ)) r *
        (EF.gammaBracket r : ℂ)‖
      ≤ ∫ r : ℝ, ‖paperFT (EF.weilTest (pairTest n σ) (pairTest n σ)) r *
        (EF.gammaBracket r : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r : ℝ, 4 * ((n : ℝ) + 1)⁻¹ *
        repairGammaMajorant (((n : ℝ) + 1)⁻¹ * r) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hm
      apply Filter.Eventually.of_forall
      intro r
      dsimp only
      rw [EF.paperFT_weilTest (contDiff_pairTest n σ).continuous
        (contDiff_pairTest n σ).continuous (hasCompactSupport_pairTest n σ)
        (hasCompactSupport_pairTest n σ), Complex.conj_ofReal, norm_mul, norm_mul,
        Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, ← sq]
      exact pairTest_gamma_majorant n σ hσ r
    _ = 4 * ∫ r, repairGammaMajorant r := by
      rw [integral_const_mul, Measure.integral_comp_mul_left, inv_inv,
        abs_of_pos hs, smul_eq_mul]
      field_simp

private theorem norm_paperFT_pairTest_strip_le (n : ℕ) (hn : 2 ≤ n)
    (σ : ℝ) (hσ : |σ| ≤ 1) (z : ℂ) (hz : |z.im| ≤ 1) :
    ‖paperFT (pairTest n σ) z‖ ≤ Real.exp 1 * ∫ u, narrowBump 0 u := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs : 0 < (n : ℝ) + 1 := by positivity
  have hJ : 0 ≤ ∫ u, narrowBump 0 u := integral_nonneg (fun _ => (narrowBump 0).nonneg)
  have hb := norm_paperFT_narrowBumpC_le n 1 z
  simp only [mul_one, packetL1] at hb
  rw [integral_narrowBump_scale] at hb
  have hrad : 1 / (4 * ((n : ℝ) + 1)) ≤ 1 := by
    apply (div_le_one (show 0 < 4 * ((n : ℝ) + 1) by positivity)).mpr
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hb' : ‖paperFT (narrowBumpC n) z‖ ≤
      Real.exp 1 * (((n : ℝ) + 1)⁻¹ * ∫ u, narrowBump 0 u) := by
    refine hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity))
    exact (mul_le_mul_of_nonneg_left hz (by positivity)).trans (by simpa using hrad)
  have hp : ‖Complex.exp (I * z * Real.log n)‖ ≤ (n : ℝ) := by
    calc ‖Complex.exp (I * z * Real.log n)‖
        ≤ Real.exp (Real.log n * |z.im|) :=
          WeilDeletion.norm_exp_I_mul_le (le_of_eq (abs_of_nonneg (Real.log_nonneg hn1)))
      _ ≤ Real.exp (Real.log n) := by
        apply Real.exp_le_exp.mpr
        simpa using mul_le_mul_of_nonneg_left hz (Real.log_nonneg hn1)
      _ = n := Real.exp_log hn0
  rw [paperFT_pairTest, norm_mul]
  have hfactor : ‖(1 : ℂ) + (σ : ℂ) * Complex.exp (I * z * Real.log n)‖ ≤ 1 + (n : ℝ) := by
    calc ‖(1 : ℂ) + (σ : ℂ) * Complex.exp (I * z * Real.log n)‖
        ≤ ‖(1 : ℂ)‖ + ‖(σ : ℂ) * Complex.exp (I * z * Real.log n)‖ := norm_add_le _ _
      _ ≤ 1 + (n : ℝ) := by
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact add_le_add le_rfl ((mul_le_mul hσ hp (norm_nonneg _) (by norm_num)).trans_eq
          (one_mul _))
  calc ‖(1 : ℂ) + (σ : ℂ) * Complex.exp (I * z * Real.log n)‖ * ‖paperFT (narrowBumpC n) z‖
      ≤ (1 + (n : ℝ)) * (Real.exp 1 * (((n : ℝ) + 1)⁻¹ * ∫ u, narrowBump 0 u)) :=
        mul_le_mul hfactor hb' (norm_nonneg _) (by positivity)
    _ = Real.exp 1 * ∫ u, narrowBump 0 u := by field_simp; ring

private theorem pairTest_arch_uniform_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ), 2 ≤ n → ∀ σ : ℝ, |σ| ≤ 1 →
      |weilArchRe (EF.weilTest (pairTest n σ) (pairTest n σ))| ≤ B := by
  let P := Real.exp 1 * ∫ u, narrowBump 0 u
  let Q := 4 * ∫ r, repairGammaMajorant r
  have hP : 0 ≤ P := mul_nonneg (Real.exp_pos 1).le
    (integral_nonneg (fun _ => (narrowBump 0).nonneg))
  have hQ : 0 ≤ Q := by
    apply mul_nonneg (by norm_num)
    exact integral_nonneg fun r => mul_nonneg (sq_nonneg _)
      (add_nonneg repairGammaConst_pos.le (abs_nonneg r))
  refine ⟨2 * P ^ 2 + (1 / (2 * Real.pi)) * Q, by positivity, ?_⟩
  intro n hn σ hσ
  have hpole (z : ℂ) (hz : |z.im| ≤ 1) :
      ‖paperFT (EF.weilTest (pairTest n σ) (pairTest n σ)) z‖ ≤ P ^ 2 := by
    rw [EF.paperFT_weilTest (contDiff_pairTest n σ).continuous
      (contDiff_pairTest n σ).continuous (hasCompactSupport_pairTest n σ)
      (hasCompactSupport_pairTest n σ), norm_mul, Complex.norm_conj]
    have hconj : |(conj z).im| ≤ 1 := by simpa using hz
    simpa only [sq] using mul_le_mul (norm_paperFT_pairTest_strip_le n hn σ hσ z hz)
      (norm_paperFT_pairTest_strip_le n hn σ hσ (conj z) hconj) (norm_nonneg _) hP
  have hp := hpole (I / 2) (by norm_num)
  have hm := hpole (-I / 2) (by norm_num)
  have hγ := integral_pairTest_gamma_norm_le n σ hσ
  have hfac : ‖(1 / (2 * (Real.pi : ℂ)) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  unfold weilArchRe
  refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
  rw [norm_mul, hfac]
  have hsum := (norm_add_le _ _).trans (add_le_add hp hm)
  have hg := mul_le_mul_of_nonneg_left hγ (by positivity : 0 ≤ 1 / (2 * Real.pi))
  dsimp [Q] at *
  nlinarith

/-- The exact PBAP isolated-atom repair costs at most a fixed polynomial in its index. -/
theorem atomCost_le_polynomial :
    ∃ C : ℝ, 0 < C ∧ ∀ j : LogIndex,
      atomCost j ≤ C * ((j : ℕ) + 1 : ℝ) * Real.sqrt (j : ℕ) := by
  obtain ⟨B, hB, hbound⟩ := pairTest_arch_uniform_bound
  let J := ∫ u, (narrowBump 0 u) ^ 2
  have hJ : 0 < J := integral_narrowBump_sq_pos 0
  refine ⟨(B + 1) / (2 * J), by positivity, ?_⟩
  intro j
  have hs : 0 < ((j : ℕ) : ℝ) + 1 := by positivity
  have hj : 0 < ((j : ℕ) : ℝ) := by exact_mod_cast (show 0 < (j : ℕ) by omega)
  have hroot := Real.sqrt_pos.mpr hj
  have hw : atomWeight j = 2 * (((j : ℕ) : ℝ) + 1)⁻¹ * J / Real.sqrt (j : ℕ) := by
    rw [atomWeight, integral_narrowBump_sq_scale]
    dsimp [J]
    ring
  have hb : max |weilArchRe (EF.weilTest (pairTest j 1) (pairTest j 1))|
      |weilArchRe (EF.weilTest (pairTest j (-1)) (pairTest j (-1)))| ≤ B :=
    max_le (hbound j j.2 1 (by norm_num)) (hbound j j.2 (-1) (by norm_num))
  calc atomCost j ≤ B / atomWeight j := div_le_div_of_nonneg_right hb (atomWeight_pos j).le
    _ ≤ (B + 1) / atomWeight j := div_le_div_of_nonneg_right (by linarith) (atomWeight_pos j).le
    _ = (B + 1) / (2 * J) * (((j : ℕ) : ℝ) + 1) * Real.sqrt (j : ℕ) := by
      rw [hw]
      field_simp

end RHTower.WeilWorkPBAP
