import GaloisForLFunctions.HTGeometry.ChronologicalTensor.FusionHeat
import GaloisForLFunctions.RHTower.SalemFermiModeIntegral

/-!
# Zeta zeros of the capacity-generated fusion response

The regularized fusion heat kernel has an ordinary convergent Mellin integral
on the open strip. Its transform is minus the product of the capacity scale,
Gamma, and zeta. Hence its zero locus there is exactly zeta's zero locus.

Only the classical Fermi Mellin identity and a nonvanishing elementary factor
are imported from SalemFermiModeIntegral. No RH criterion or RH assertion is used.
The connection to Euler signs of geometric joins is a separate obligation.
-/

open Complex Set Filter MeasureTheory Asymptotics
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section


def fusionMellinStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}
def fusionBoseKernel (t : ℝ) : ℂ := (fusionBoseDefect t : ℝ)

theorem fusionBoseKernel_norm (t : ℝ) :
    ‖fusionBoseKernel t‖ = fusionBoseDefect t := by
  rw [fusionBoseKernel,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (fusionBoseDefect_bounds t).1]

theorem fusionBoseKernel_continuousOn :
    ContinuousOn fusionBoseKernel (Ioi 0) := by
  have h1 : ContinuousOn (fun t : ℝ => 1/t) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt ht)
  have h2 : ContinuousOn (fun t : ℝ => 1/(Real.exp t-1)) (Ioi 0) :=
    continuousOn_const.div (Real.continuous_exp.continuousOn.sub continuousOn_const)
      (fun t ht => ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)))
  refine (Complex.continuous_ofReal.comp_continuousOn (h1.sub h2)).congr ?_
  intro t ht
  change 0 < t at ht
  simp only [fusionBoseKernel,fusionBoseDefect,if_pos ht]
  rfl

theorem fusionBoseKernel_isBigO_atTop :
    fusionBoseKernel =O[atTop] (fun t : ℝ => t^(-(1 : ℝ))) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1,?_⟩
  filter_upwards [] with t
  simpa only [fusionBoseKernel_norm,one_mul,Real.rpow_neg_one,
    Real.norm_eq_abs,abs_inv,one_div] using (fusionBoseDefect_bounds t).2.2

theorem fusionBoseKernel_isBigO_atZero :
    fusionBoseKernel =O[𝓝[>] 0] (fun t : ℝ => t^(-(0 : ℝ))) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1,?_⟩
  filter_upwards [] with t
  simpa only [fusionBoseKernel_norm,neg_zero,Real.rpow_zero,norm_one,one_mul]
    using (fusionBoseDefect_bounds t).2.1

theorem fusionBoseKernel_converges :
    ∀ s ∈ fusionMellinStrip, MellinConvergent fusionBoseKernel s := by
  intro s hs
  exact mellinConvergent_of_isBigO_rpow
    (fusionBoseKernel_continuousOn.locallyIntegrableOn measurableSet_Ioi)
    fusionBoseKernel_isBigO_atTop hs.2 fusionBoseKernel_isBigO_atZero hs.1

theorem fusionBoseKernel_dyadic :
    Set.EqOn (fun t => (2 : ℂ) • fusionBoseKernel (2*t)-fusionBoseKernel t)
      RHTower.salemFermiKernel (Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have h := congrArg Complex.ofReal (fusionBoseDefect_dyadic t)
  rw [if_pos ht] at h
  simpa [fusionBoseKernel,RHTower.salemFermiKernel,one_div,smul_eq_mul] using h

theorem fusionBoseKernel_mellin :
    Set.EqOn (mellin fusionBoseKernel)
      (fun s => -Complex.Gamma s * riemannZeta s) fusionMellinStrip := by
  intro s hs
  have hc := fusionBoseKernel_converges s hs
  have hc2 : MellinConvergent (fun t => fusionBoseKernel (2*t)) s :=
    (MellinConvergent.comp_mul_left (by positivity : (0 : ℝ) < 2)).mpr hc
  have hsub := (hasMellin_sub (hc2.const_smul (2 : ℂ)) hc).2
  have hleft :
      mellin (fun t => (2 : ℂ) • fusionBoseKernel (2*t)-fusionBoseKernel t) s =
        mellin RHTower.salemFermiKernel s := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact congrArg (fun z : ℂ => (t : ℂ)^(s-1) • z)
      (fusionBoseKernel_dyadic ht)
  rw [hleft,mellin_const_smul,
    mellin_comp_mul_left fusionBoseKernel s (by positivity : (0 : ℝ) < 2)] at hsub
  have hs1 : s ≠ 1 := by
    intro h
    have hh := hs.2
    rw [h,Complex.one_re] at hh
    exact lt_irrefl _ hh
  rw [RHTower.mellin_salemFermiKernel_eq_closedForm hs.1 hs1] at hsub
  have hpow : (2 : ℂ)*(2 : ℂ)^(-s)=(2 : ℂ)^(1-s) := by
    rw [sub_eq_add_neg,Complex.cpow_add _ _ (by exact_mod_cast
      (ne_of_gt (show (0 : ℝ) < 2 by positivity))),Complex.cpow_one]
  have hcoef : 1-(2 : ℂ)^(1-s) ≠ 0 := by
    simpa only [RHTower.salemSpectralParameter_re_im] using
      (RHTower.salemDyadicFactor_ne_zero (gamma := s.im) hs.2)
  simp only [smul_eq_mul,Complex.ofReal_ofNat] at hsub
  have hproduct :
      (1-(2 : ℂ)^(1-s))*mellin fusionBoseKernel s =
        (1-(2 : ℂ)^(1-s))*(-Complex.Gamma s*riemannZeta s) := by
    rw [← hpow] at hsub ⊢
    linear_combination hsub
  exact mul_left_cancel₀ hcoef hproduct

theorem fusionRegularizedKernel_converges :
    ∀ s ∈ fusionMellinStrip, MellinConvergent fusionRegularizedKernel s := by
  intro s hs
  exact (MellinConvergent.comp_mul_left fusionSpacing_pos).mpr
    (fusionBoseKernel_converges s hs)

theorem fusionRegularizedKernel_mellin :
    Set.EqOn (mellin fusionRegularizedKernel)
      (fun s => -(fusionSpacing : ℂ)^(-s)*Complex.Gamma s*riemannZeta s)
      fusionMellinStrip := by
  intro s hs
  change mellin (fun t => fusionBoseKernel (fusionSpacing*t)) s = _
  rw [mellin_comp_mul_left fusionBoseKernel s fusionSpacing_pos,
    fusionBoseKernel_mellin hs,smul_eq_mul]
  ring

theorem fusionRegularizedKernel_zeroLocus :
    {s ∈ fusionMellinStrip | mellin fusionRegularizedKernel s=0} =
      {s ∈ fusionMellinStrip | riemannZeta s=0} := by
  ext s
  constructor
  · rintro ⟨hs,hzero⟩
    refine ⟨hs,?_⟩
    rw [fusionRegularizedKernel_mellin hs] at hzero
    have hpow : (fusionSpacing : ℂ)^(-s) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
        (ne_of_gt fusionSpacing_pos)))
    have hfactor := mul_ne_zero (neg_ne_zero.mpr hpow)
      (Complex.Gamma_ne_zero_of_re_pos hs.1)
    exact (mul_eq_zero.mp hzero).resolve_left hfactor
  · rintro ⟨hs,hzero⟩
    exact ⟨hs,by
      rw [fusionRegularizedKernel_mellin hs]
      simp only [hzero,mul_zero]⟩

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
