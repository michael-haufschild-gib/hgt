import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicCutoffLimits
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicNegativePartContinuity

/-!
# Unit trial recovery for the closed logarithmic form

Normalize expanding compact cutoffs. Their physical and positive Fourier
energies converge, while bounded first moments control the negative
logarithmic tails. Thus the full signed trial energies recover the closed form.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri


private theorem mass_of_real_L2_representative {F : ℝ → ℝ} {v : SoninL2}
    (hv : (v : ℝ → ℂ) =ᵐ[volume] cx F) : (∫ u, F u ^ 2) = ‖v‖ ^ 2 := by
  rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq volume]
  apply integral_congr_ae
  filter_upwards [hv] with u hu
  rw [hu]
  change F u ^ 2 = ‖(F u : ℂ)‖ ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem firstMoment_of_real_L2_representative {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) {v : SoninL2}
    (hv : (v : ℝ → ℂ) =ᵐ[volume] cx F) :
    (∫ u : ℝ, |u| * ‖v u‖ ^ 2) = criticalHalfLineFirstMoment F := by
  calc
    _ = ∫ u : ℝ, |u| * ‖cx F u‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hv] with u hu
      exact congrArg (fun z : ℂ => |u| * ‖z‖ ^ 2) hu
    _ = _ := hF.integral_absMoment

/-- Normalized compact cutoffs recover both a unit profile and its full signed energy.
Physical domination, positive jump-form convergence, and uniform negative
Fourier tails control the three terms separately. -/
theorem exists_softLogarithmic_unit_recovery {v : SoninL2}
    (hv : ClosedSoftLogarithmicHalfLineDomain v) (hn : ‖v‖ = 1) :
    ∃ (F : ℕ → ℝ → ℝ) (hF : ∀ n, SoftLogarithmicHalfLineDomain (F n)),
      (∀ n, (∫ u, F n u ^ 2) = 1) ∧
      Tendsto (fun n => (hF n).memLp_complex.toLp (cx (F n))) atTop (𝓝 v) ∧
      Tendsto (fun n => softLogarithmicHalfLineEnergy (F n)) atTop
        (𝓝 (closedSoftLogarithmicHalfLineEnergy v)) := by
  have hnorm : Tendsto (fun n => ‖softLogarithmicCutoffVector n v‖) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hn] using (tendsto_softLogarithmicCutoffVector v).norm
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hnorm.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  let p : ℕ → ℝ → ℝ := fun n => softLogarithmicCutoffProfile (n + N) v
  let g : ℕ → SoninL2 := fun n => softLogarithmicCutoffVector (n + N) v
  let c : ℕ → ℝ := fun n => ‖g n‖⁻¹
  let F : ℕ → ℝ → ℝ := fun n u => c n * p n u
  let U : ℕ → SoninL2 := fun n => (c n : ℂ) • g n
  have hgpos (n : ℕ) : 0 < ‖g n‖ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans (hN (n + N) (by omega))
  have hc0 (n : ℕ) : 0 ≤ c n := inv_nonneg.mpr (norm_nonneg (g n))
  have hc2 (n : ℕ) : c n ^ 2 ≤ 4 := by
    have hb : c n ≤ 2 := by
      change ‖g n‖⁻¹ ≤ 2
      rw [← one_div]
      apply (div_le_iff₀ (hgpos n)).mpr
      linarith only [hN (n + N) (by omega)]
    nlinarith only [hc0 n, hb]
  have hgp : Tendsto g atTop (𝓝 v) :=
    (tendsto_softLogarithmicCutoffVector v).comp (tendsto_add_atTop_nat N)
  have hgn : Tendsto (fun n => ‖g n‖) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hn] using hgp.norm
  have hcp : Tendsto c atTop (𝓝 (1 : ℝ)) := by
    simpa only [inv_one] using hgn.inv₀ one_ne_zero
  have hcsp : Tendsto (fun n => c n ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_pow] using hcp.pow 2
  have hcc : Tendsto (fun n => (c n : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using (Complex.continuous_ofReal.tendsto 1).comp hcp
  have hUp : Tendsto U atTop (𝓝 v) := by
    simpa only [one_smul] using hcc.smul hgp
  have hp (n : ℕ) : SoftLogarithmicHalfLineDomain (p n) := hv.cutoff_trial (n + N)
  have hpr (n : ℕ) : (g n : ℝ → ℂ) =ᵐ[volume] cx (p n) :=
    hv.cutoff_representative (n + N)
  have hF (n : ℕ) : SoftLogarithmicHalfLineDomain (F n) := (hp n).const_mul (c n)
  have hUr (n : ℕ) : (U n : ℝ → ℂ) =ᵐ[volume] cx (F n) := by
    filter_upwards [Lp.coeFn_smul (c n : ℂ) (g n), hpr n] with u hu hr
    change U n u = ((c n : ℂ) • (g n : ℝ → ℂ)) u at hu
    rw [hu]
    dsimp only [Pi.smul_apply, smul_eq_mul]
    rw [hr]
    change (c n : ℂ) * (p n u : ℂ) = ((c n * p n u : ℝ) : ℂ)
    exact (Complex.ofReal_mul _ _).symm
  have hUnorm (n : ℕ) : ‖U n‖ = 1 := by
    change ‖(c n : ℂ) • g n‖ = 1
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 n)]
    exact inv_mul_cancel₀ (hgpos n).ne'
  have hm (n : ℕ) : (∫ u, F n u ^ 2) = 1 := by
    rw [mass_of_real_L2_representative (hUr n), hUnorm n, one_pow]
  have hMraw (n : ℕ) : criticalHalfLineFirstMoment (p n) =
      ∫ u : ℝ, |u| * ‖g n u‖ ^ 2 :=
    (firstMoment_of_real_L2_representative (hp n) (hpr n)).symm
  have hMscaled (n : ℕ) : criticalHalfLineFirstMoment (F n) =
      c n ^ 2 * ∫ u : ℝ, |u| * ‖g n u‖ ^ 2 := by
    change criticalHalfLineFirstMoment (fun u => c n * p n u) = _
    rw [criticalHalfLineFirstMoment_const_mul, hMraw n]
  have hMbound (n : ℕ) : criticalHalfLineFirstMoment (F n) ≤
      4 * ∫ u : ℝ, |u| * ‖v u‖ ^ 2 := by
    rw [hMscaled n]
    exact (mul_le_mul_of_nonneg_right (hc2 n)
      (integral_nonneg fun u => mul_nonneg (abs_nonneg u) (sq_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (hv.cutoff_firstMoment_le (n + N)) (by norm_num))
  have hMp : Tendsto (fun n => criticalHalfLineFirstMoment (F n)) atTop
      (𝓝 (∫ u : ℝ, |u| * ‖v u‖ ^ 2)) := by
    have h := hcsp.mul (hv.cutoff_firstMoment_tendsto.comp (tendsto_add_atTop_nat N))
    simpa only [hMscaled, one_mul] using h
  have hPscaled (n : ℕ) : (∫ ξ : ℝ, max (Real.log |ξ|) 0 * ‖fourierUnitary (U n) ξ‖ ^ 2) =
      c n ^ 2 * ∫ ξ : ℝ, max (Real.log |ξ|) 0 * ‖fourierUnitary (g n) ξ‖ ^ 2 := by
    have he : fourierUnitary (U n) = (c n : ℂ) • fourierUnitary (g n) := by
      change fourierUnitary ((c n : ℂ) • g n) = _
      rw [map_smul]
    have hcoe := Lp.coeFn_smul (c n : ℂ) (fourierUnitary (g n))
    rw [← he] at hcoe
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hcoe] with ξ hξ
    rw [hξ]
    dsimp only [Pi.smul_apply, smul_eq_mul]
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hPp : Tendsto (fun n => ∫ ξ : ℝ, max (Real.log |ξ|) 0 *
      ‖fourierUnitary (U n) ξ‖ ^ 2) atTop
      (𝓝 (∫ ξ : ℝ, max (Real.log |ξ|) 0 * ‖fourierUnitary v ξ‖ ^ 2)) := by
    have h := hcsp.mul (hv.cutoff_positiveEnergy_tendsto.comp (tendsto_add_atTop_nat N))
    simpa only [hPscaled, one_mul] using h
  have hNp := (negativeLog_integral_tendsto_of_softLogarithmic_trials hF hm hUr hUp hMbound).2
  have hE (n : ℕ) : softLogarithmicHalfLineEnergy (F n) =
      8 * criticalHalfLineFirstMoment (F n) +
      (∫ ξ : ℝ, max (Real.log |ξ|) 0 * ‖fourierUnitary (U n) ξ‖ ^ 2) -
        ∫ ξ : ℝ, max (-Real.log |ξ|) 0 * ‖fourierUnitary (U n) ξ‖ ^ 2 := by
    have h := ((hF n).toClosed (hUr n)).energy_eq_parts
    rw [(hF n).closedEnergy_eq (hUr n), firstMoment_of_real_L2_representative (hF n) (hUr n)] at h
    exact h
  have henergy : Tendsto (fun n => softLogarithmicHalfLineEnergy (F n)) atTop
      (𝓝 (closedSoftLogarithmicHalfLineEnergy v)) := by
    rw [hv.energy_eq_parts]
    simpa only [hE] using ((hMp.const_mul 8).add hPp).sub hNp
  have hLp (n : ℕ) : (hF n).memLp_complex.toLp (cx (F n)) = U n :=
    Lp.ext ((hF n).memLp_complex.coeFn_toLp.trans (hUr n).symm)
  refine ⟨F, hF, hm, ?_, henergy⟩
  simpa only [hLp] using hUp

#print axioms exists_softLogarithmic_unit_recovery
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

