import GaloisForLFunctions.HTGeometry.PermutohedralScheduleConservation
import GaloisForLFunctions.HTGeometry.CausalRationalKernel
import GaloisForLFunctions.HTGeometry.LaplaceAtomicRigidity

/-!
# Stable causal exactification of the schedule alternant

When the formation numerator `P_r(z;λ)` has positive degree and no zero in `Re z ≥ 0`, the causal
kernel `g` of `1/P_r` (Laplace transform `1/P_r`) inverts `P_r(∂_t)` on the exact alternant range:
for distinct grades `H_r = W_r g ∗ Δ_r⁻¹ F_r` on `[0, ∞)`.  Both sides have Laplace transform
`M_r/(z D_r(z))`; after an exponential damping the difference is integrable with vanishing Laplace
transform on `(0, ∞)`, hence zero, and continuity upgrades almost-everywhere to everywhere.
-/

open MeasureTheory Set Filter Topology Equiv Polynomial
open MvPolynomial (aeval)

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

open Permutohedral

variable {r : ℕ}

/-- `P_r(z;λ)` as a complex polynomial in `z`. -/
def formPolyC (lam : Fin r → ℝ) : ℂ[X] := (formPoly lam).map Complex.ofRealHom

theorem eval_formPolyC (lam : Fin r → ℝ) (z : ℂ) :
    (formPolyC lam).eval z = aeval (point z (lamC lam)) (formNumer r) :=
  eval_map_formPoly lam z

/-- The causal Green kernel of `P_r(∂_t)`: the quasi-polynomial with transform `1/P_r`. -/
def formKernel (lam : Fin r → ℝ) : QuasiPolynomial := QuasiPolynomial.ratKernel (formPolyC lam)

theorem formKernel_stable {lam : Fin r → ℝ}
    (hstab : ∀ z : ℂ, 0 ≤ z.re → (formPolyC lam).eval z ≠ 0) :
    ∀ μ ∈ (formKernel lam).support, μ.re < 0 := fun μ hμ => by
  have h := QuasiPolynomial.support_ratKernel _ hμ
  rw [Multiset.mem_toFinset] at h
  by_contra hre
  exact hstab μ (not_lt.1 hre) ((mem_roots'.1 h).2)

theorem roots_formPolyC_re_neg {lam : Fin r → ℝ}
    (hstab : ∀ z : ℂ, 0 ≤ z.re → (formPolyC lam).eval z ≠ 0) :
    ∀ μ ∈ (formPolyC lam).roots, μ.re < 0 := fun μ h => by
  by_contra hre
  exact hstab μ (not_lt.1 hre) ((mem_roots'.1 h).2)

theorem causalConv_const_mul (k f : ℝ → ℂ) (c : ℂ) (t : ℝ) :
    causalConv k (fun s => c * f s) t = c * causalConv k f t := by
  rw [causalConv, causalConv, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun s _ => by ring

/-- The damped Laplace identity behind the exactification: for real `σ > 0` the difference
`H_r - W_r Δ_r⁻¹ g ∗ F_r` has integrable damped values with vanishing transform. -/
theorem laplace_exactification_zero {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i)
    (hΔ : delta lam ≠ 0) (hdeg : 0 < (formPolyC lam).natDegree)
    (hstab : ∀ z : ℂ, 0 ≤ z.re → (formPolyC lam).eval z ≠ 0) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t => ((hypoQP (subsetRates lam)).eval t -
        ((subsetIncidence lam : ℝ) : ℂ) * (((delta lam : ℝ) : ℂ)⁻¹ *
          causalConv (formKernel lam).eval (scheduleQP lam).eval t)) *
            Complex.exp (-(σ * t))) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), ((hypoQP (subsetRates lam)).eval t -
        ((subsetIncidence lam : ℝ) : ℂ) * (((delta lam : ℝ) : ℂ)⁻¹ *
          causalConv (formKernel lam).eval (scheduleQP lam).eval t)) *
            Complex.exp (-(σ * t)) = 0 := by
  have hq : 0 < ((σ : ℂ)).re := by simpa using hσ
  have hstabK := formKernel_stable hstab
  obtain ⟨δ, hδ, Cg, hCg0, hCg⟩ := QuasiPolynomial.exists_decay hstabK
  have hFsupp : ∀ μ ∈ (scheduleQP lam).support, μ.re < σ / 2 := fun μ hμ =>
    (re_le_of_mem_support_scheduleQP hlam μ hμ).trans_lt (by linarith)
  obtain ⟨CF, hCF0, hCF⟩ := (scheduleQP lam).exists_norm_eval_le hFsupp
  have hgb : ∀ t, 0 ≤ t → ‖(formKernel lam).eval t‖ ≤ Cg * Real.exp (σ / 2 * t) := fun t ht =>
    (hCg t ht).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hCg0)
  obtain ⟨hconvInt, hconvEq⟩ := laplace_causalConv (formKernel lam).continuous_eval
    (scheduleQP lam).continuous_eval hgb hCF (by linarith : σ / 2 < σ)
  have hHsupp : ∀ μ ∈ (hypoQP (subsetRates lam)).support, μ.re < ((σ : ℂ)).re := fun μ hμ =>
    (re_le_of_mem_support_hypoQP (subsetRates_pos hlam) μ hμ).trans_lt hq
  obtain ⟨hHint, hHeq⟩ := QuasiPolynomial.integral_eval_mul_cexp _ hHsupp
  have hgsupp : ∀ μ ∈ (formKernel lam).support, μ.re < ((σ : ℂ)).re := fun μ hμ =>
    (hstabK μ hμ).trans hq
  have hgeq := (QuasiPolynomial.integral_eval_mul_cexp _ hgsupp).2
  have hFsupp' : ∀ μ ∈ (scheduleQP lam).support, μ.re < ((σ : ℂ)).re := fun μ hμ =>
    (re_le_of_mem_support_scheduleQP hlam μ hμ).trans_lt hq
  have hFeq := (QuasiPolynomial.integral_eval_mul_cexp _ hFsupp').2
  have hpt : ∀ t : ℝ, ((hypoQP (subsetRates lam)).eval t -
      ((subsetIncidence lam : ℝ) : ℂ) * (((delta lam : ℝ) : ℂ)⁻¹ *
        causalConv (formKernel lam).eval (scheduleQP lam).eval t)) * Complex.exp (-(σ * t)) =
      (hypoQP (subsetRates lam)).eval t * Complex.exp (-(σ * t)) -
        (((subsetIncidence lam : ℝ) : ℂ) * ((delta lam : ℝ) : ℂ)⁻¹) *
          (causalConv (formKernel lam).eval (scheduleQP lam).eval t * Complex.exp (-(σ * t))) :=
    fun t => by ring
  have hint : IntegrableOn (fun t => (hypoQP (subsetRates lam)).eval t * Complex.exp (-(σ * t)) -
      (((subsetIncidence lam : ℝ) : ℂ) * ((delta lam : ℝ) : ℂ)⁻¹) *
        (causalConv (formKernel lam).eval (scheduleQP lam).eval t * Complex.exp (-(σ * t))))
      (Ioi 0) := hHint.sub (hconvInt.const_mul _)
  refine ⟨hint.congr_fun (fun t _ => (hpt t).symm) measurableSet_Ioi, ?_⟩
  simp_rw [hpt]
  have hgL : (formKernel lam).laplace (σ : ℂ) = ((formPolyC lam).eval (σ : ℂ))⁻¹ :=
    QuasiPolynomial.laplace_ratKernel hdeg fun μ hμ => (roots_formPolyC_re_neg hstab μ hμ).trans hq
  rw [integral_sub hHint (hconvInt.const_mul _), integral_const_mul, hconvEq, hgeq, hFeq, hHeq, hgL,
    laplace_scheduleQP hlam hq, laplace_subsetQP hlam hq, alternant_eq _ _ (phases_ne_zero hlam hq),
    eval_formPolyC, subsetGradeProd_eq]
  have hD := aeval_denom_ne_zero (σ : ℂ) (lamC lam) (phases_ne_zero hlam hq)
  have hP : aeval (point (σ : ℂ) (lamC lam)) (formNumer r) ≠ 0 := by
    rw [← eval_formPolyC]; exact hstab _ hq.le
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hΔC : ((delta lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hΔ
  have hdelta : delta (lamC lam) = ((delta lam : ℝ) : ℂ) := by simp [delta, lamC]
  rw [hdelta]
  push_cast
  field_simp
  ring

/-- **Stable causal exactification** `H_r = W_r g ∗ Δ_r⁻¹ F_r` on `[0, ∞)`, where `g` is the causal
kernel with Laplace transform `1/P_r`. -/
theorem subsetCDF_eq_formKernel_conv {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i)
    (hΔ : delta lam ≠ 0) (hdeg : 0 < (formPolyC lam).natDegree)
    (hstab : ∀ z : ℂ, 0 ≤ z.re → (formPolyC lam).eval z ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (subsetCDF lam t : ℂ) = ((subsetIncidence lam : ℝ) : ℂ) *
      causalConv (formKernel lam).eval
        (fun s => ((delta lam : ℝ) : ℂ)⁻¹ * scheduleAlternant lam s) t := by
  set u : ℝ → ℂ := fun t => (hypoQP (subsetRates lam)).eval t -
    ((subsetIncidence lam : ℝ) : ℂ) * (((delta lam : ℝ) : ℂ)⁻¹ *
      causalConv (formKernel lam).eval (scheduleQP lam).eval t)
  have hcont : Continuous u :=
    (hypoQP (subsetRates lam)).continuous_eval.sub (continuous_const.mul (continuous_const.mul
      (continuous_causalConv (formKernel lam).continuous_eval (scheduleQP lam).continuous_eval)))
  set v : ℝ → ℂ := fun r => u r * Complex.exp (-((1 : ℝ) * r))
  have hvint : IntegrableOn v (Ioi 0) := (laplace_exactification_zero hlam hΔ hdeg hstab one_pos).1
  have hvlap : ∀ᵐ τ ∂(volume.restrict (Ioi (0 : ℝ))),
      ∫ r in Ioi 0, v r * (Real.exp (-τ * r) : ℂ) = 0 := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_
    have h := (laplace_exactification_zero hlam hΔ hdeg hstab
      (by linarith [mem_Ioi.1 hτ] : (0 : ℝ) < 1 + τ)).2
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [v, u]
    rw [mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hv0 := ae_eq_zero_of_laplace_ae_eq_zero hvint hvlap
  have hu0 : u =ᵐ[volume.restrict (Ioi 0)] 0 := by
    filter_upwards [hv0] with r hr
    simp only [v, Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero, or_false] at hr
    exact hr
  have heq : EqOn u 0 (Ioi 0) := Measure.eqOn_of_ae_eq hu0 hcont.continuousOn
    continuousOn_const (by rw [interior_Ioi, closure_Ioi]; exact Ioi_subset_Ici_self)
  have hr1 : 1 ≤ r := by
    by_contra h
    have h0 : r = 0 := by omega
    subst h0
    have := natDegree_formPoly_le lam
    rw [formPolyC, natDegree_map_eq_of_injective Complex.ofReal_injective] at hdeg
    simp at this
    omega
  have hu : u t = 0 := by
    rcases eq_or_lt_of_le ht with rfl | htpos
    · have hne : subsetRates lam ≠ [] := by
        intro h
        have := length_subsetRates lam
        rw [h] at this
        have : 2 ≤ 2 ^ r := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr1
        simp at *
        omega
      obtain ⟨ρ, ρs, hρ⟩ := List.exists_cons_of_ne_nil hne
      simp only [u, causalConv, intervalIntegral.integral_same, mul_zero, sub_zero]
      rw [← hypoCDFList_eq_eval, hρ, hypoCDFList, expKernelConv_zero, Complex.ofReal_zero]
    · exact heq htpos
  have hF : causalConv (formKernel lam).eval
      (fun s => ((delta lam : ℝ) : ℂ)⁻¹ * scheduleAlternant lam s) t =
        ((delta lam : ℝ) : ℂ)⁻¹ * causalConv (formKernel lam).eval (scheduleQP lam).eval t := by
    rw [← causalConv_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    simp only
    rw [scheduleAlternant_eq_eval hlam hs.1]
  rw [hF, subsetCDF, hypoCDFList_eq_eval]
  exact sub_eq_zero.1 hu

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
