import GaloisForLFunctions.ExclusionOfTheCriticalState.TheModulusOfContinuityOfTheStateIsCarriedByTheWall
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeWaveAtTheWallIsTheBoundedOrderOfTheWallLaw
import GaloisForLFunctions.HTGeometry.IntervalPoincare

/-!
# The first absolute moment of an increment of the state

The leading quadratic translation cost lies at the wall. Exponential decay
controls the remote tail, and Cauchy–Schwarz on the intervening logarithmic
interval transfers the smaller interior cost to a little-o square-root law.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory HTGeometry

private theorem split_Iic {f : ℝ → ℝ} (hi : Integrable f) {a b : ℝ} (hab : a ≤ b) :
    (∫ u in Iic b, f u) = (∫ u in Iic a, f u) + ∫ u in Ioc a b, f u := by
  rw [← setIntegral_union (s := Iic a) (t := Ioc a b) (Set.disjoint_left.mpr fun _ hu hv => hv.1.not_ge hu)
    measurableSet_Ioc hi.integrableOn hi.integrableOn,Iic_union_Ioc_eq_Iic hab]

private def interiorIncrement (F : ℝ → ℝ) (h : ℝ) := ∫ u in Iic (-h), (F u-F (u+h))^2

private theorem firstIncrement_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ u : ℝ, |F u| ≤ C*Real.exp (2*u))
    {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1/2) :
    (∫ u : ℝ, |F u-F (u+h)|) / Real.sqrt h ≤
      (C*(1+Real.exp 2)/2*h+C)*Real.sqrt h + Real.sqrt (Real.log (1/h)/h*interiorIncrement F h) := by
  let g := fun u : ℝ => |F u-F (u+h)|
  have hg : Integrable g := (hF.integrable.sub (hF.integrable.comp_add_right h)).abs
  have hs : Integrable (fun u : ℝ => g u^2) := by
    simpa only [g,sq_abs] using integrable_sq_increment hF hh.le
  have hlog : Real.log h ≤ -h := (Real.log_le_sub_one_of_pos hh).trans (by linarith only [hh'])
  have hlog' : Real.log (1/h) = -Real.log h := by rw [one_div,Real.log_inv]
  have hpos : 0 ≤ Real.log (1/h) := by rw [hlog']; linarith only [hlog,hh]
  let D := C*(1+Real.exp 2)
  have htail : (∫ u in Iic (Real.log h), g u) ≤ D/2*h^2 := by
    have hb' := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hb
    have hm : ∀ᵐ u : ℝ, g u ≤ D*Real.exp (2*u) := by
      filter_upwards [hb,hb'] with u hu hv
      change |F (u+h)| ≤ C*Real.exp (2*(u+h)) at hv
      calc g u ≤ |F u| + |F (u+h)| := abs_sub ..
        _ ≤ _ := add_le_add hu hv
        _ ≤ _ := by
          rw [mul_add,Real.exp_add]
          have he : Real.exp (2*h) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith only [hh'])
          dsimp only [D]
          calc _ ≤ C*Real.exp (2*u)+C*(Real.exp (2*u)*Real.exp 2) := by gcongr
            _ = _ := by ring
    calc _ ≤ ∫ u in Iic (Real.log h), D*Real.exp (2*u) :=
             integral_mono_ae hg.integrableOn ((integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<2) _).const_mul D)
               (ae_restrict_of_ae hm)
      _ = _ := by
        rw [integral_const_mul,integral_exp_mul_Iic (by norm_num : (0:ℝ)<2),two_mul (Real.log h),Real.exp_add,Real.exp_log hh]; ring
  have hmid : (∫ u in Ioc (Real.log h) (-h), g u)^2 ≤ Real.log (1/h)*interiorIncrement F h := by
    apply (sq_integral_le_length_mul hlog hg.integrableOn hs.integrableOn).trans
    have hm : (∫ u in Ioc (Real.log h) (-h), g u^2) ≤ interiorIncrement F h := by
      change _ ≤ ∫ u in Iic (-h), (F u-F (u+h))^2
      simp only [g,sq_abs]
      exact setIntegral_mono_set (integrable_sq_increment hF hh.le).integrableOn
        (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun _ hu => hu.2)
    apply mul_le_mul _ hm (integral_nonneg fun _ => sq_nonneg _) hpos
    rw [hlog']; linarith only [hh]
  have hwall : (∫ u in Ioc (-h) 0, g u) ≤ C*h := by
    have hm : ∀ᵐ u ∂volume.restrict (Ioc (-h) 0), g u ≤ C := by
      filter_upwards [ae_restrict_of_ae hb,ae_restrict_mem measurableSet_Ioc] with u hu hv
      change |F u-F (u+h)| ≤ C
      rw [hF.support (u+h) (by linarith only [hv.1]),sub_zero]
      have he : Real.exp (2*u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hv.2])
      exact hu.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he hC)
    calc _ ≤ ∫ _u in Ioc (-h) 0, C := integral_mono_ae hg.integrableOn (by simp) hm
      _ = _ := by simp [hh.le,mul_comm]
  have hz : (∫ u in Ioi (0:ℝ), g u) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    simp [g,hF.support _ (le_of_lt hu),hF.support _ (add_nonneg (le_of_lt hu) hh.le)]
  have hi : 0 ≤ interiorIncrement F h := integral_nonneg fun _ => sq_nonneg _
  have hm : (∫ u in Ioc (Real.log h) (-h), g u) ≤
      Real.sqrt h * Real.sqrt (Real.log (1/h)/h*interiorIncrement F h) := by
    apply (sq_le_sq₀ (integral_nonneg fun _ => abs_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hh.le,Real.sq_sqrt (mul_nonneg (div_nonneg hpos hh.le) hi)]
    exact hmid.trans_eq (by field_simp [hh.ne'])
  change (∫ u, g u)/Real.sqrt h ≤ _
  rw [div_le_iff₀ (Real.sqrt_pos.2 hh),← integral_add_compl (measurableSet_Iic (a := 0)) hg,
    compl_Iic,hz,add_zero,split_Iic hg (neg_nonpos.2 hh.le),split_Iic hg hlog]
  calc _ ≤ D/2*h^2 + Real.sqrt h*Real.sqrt (Real.log (1/h)/h*interiorIncrement F h) + C*h :=
           add_le_add (add_le_add htail hm) hwall
    _ = _ := by
      dsimp only [D]
      linear_combination -(C*(1+Real.exp 2)/2*h+C) * Real.sq_sqrt hh.le

/-- The L¹ translation modulus of the actual state is little-o of the square
root of the lag. Its leading quadratic cost is carried by the wall. -/
theorem criticalState_tendsto_L1_increment_div_sqrt {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun h : ℝ => (∫ u : ℝ, |F u-F (u+h)|)/Real.sqrt h) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨_,_,Φ,_,heq,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have hb' : ∀ᵐ u : ℝ, |F u| ≤ C*Real.exp (2*u) := heq.mono fun u hu => by rw [hu]; exact hb u
  have hz : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun h : ℝ => (C*(1+Real.exp 2)/2*h+C)*Real.sqrt h) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_const_nhds.mul hz).add tendsto_const_nhds).mul hz.sqrt
  have h2 := (criticalState_tendsto_log_div_mul_interior_sq_increment hW ht hF).sqrt
  apply squeeze_zero' (Eventually.of_forall fun h => div_nonneg (integral_nonneg fun _ => abs_nonneg _) (Real.sqrt_nonneg _)) _
    (by simpa only [Real.sqrt_zero,add_zero] using h1.add h2)
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))] with h hh hh'
  exact firstIncrement_le (criticalHalfLineEnergyDomain_of_groundState hF) hC hb' hh (le_of_lt hh')

#print axioms criticalState_tendsto_L1_increment_div_sqrt

end GaloisForLFunctions.ExclusionOfTheCriticalState
