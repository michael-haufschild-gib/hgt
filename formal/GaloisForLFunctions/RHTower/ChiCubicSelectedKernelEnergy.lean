import GaloisForLFunctions.RHTower.ChiCubicCoupledStripEnergy
import GaloisForLFunctions.RHTower.ChiCubicKernelFrequencyDecay

/-!
# Global weighted energy of the actual selected reciprocal kernel

The actual order-twelve max-frequency estimate has an integrable separated
majorant on every complementary frequency tail. For the literal selection
`delta = N^(-3/4)`, `h = 1/log N`, and curvature `tau/N`, its cutoff loss is
absorbed beyond `N/(4*tau)`. Combining this with the admitted curved-strip
estimate gives globally uniform weighted L2 energy at every order below 3/2.
No assumed energy budget or cancellation estimate enters either theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private theorem tail_energy_majorant (e a b R z D : ℝ)
    (he : 0≤e) (he20 : e≤20) (hR : 1≤R) (hRM : R ≤ max |a| |b|)
    (hz : 0≤z) (hdec : (max |a| |b|)^12*z≤D) :
    (1+|a|+|b|)^e*z^2≤
      16*(3 : ℝ)^e*D^2*R^(e-20)/((1+|a|)^2*(1+|b|)^2) := by
  let M := max |a| |b|
  have hM : 0<M := lt_of_lt_of_le zero_lt_one (hR.trans hRM)
  have hMp : 1≤M := hR.trans hRM
  have ha : |a|≤M := le_max_left _ _
  have hb : |b|≤M := le_max_right _ _
  have hT : 1+|a|+|b|≤3*M := by linarith
  have hA : 1+|a|≤2*M := by linarith
  have hB : 1+|b|≤2*M := by linarith
  have hweight : (1+|a|+|b|)^e≤(3 : ℝ)^e*M^e := by
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ)≤3) hM.le] using
      Real.rpow_le_rpow (by positivity : (0 : ℝ)≤1+|a|+|b|) hT he
  have hsq : z^2≤D^2/M^24 := by
    have hh : z≤D/M^12 := (le_div_iff₀ (pow_pos hM 12)).mpr (by simpa only [mul_comm] using hdec)
    have hhh := pow_le_pow_left₀ hz hh 2
    simpa only [div_pow,←pow_mul] using hhh
  have hprod : (1+|a|)^2*(1+|b|)^2≤16*M^4 := by
    calc (1+|a|)^2*(1+|b|)^2≤(2*M)^2*(2*M)^2 := by gcongr
      _ = _ := by ring
  have hfrac : 1/M^4≤16/((1+|a|)^2*(1+|b|)^2) := by
    apply (div_le_div_iff₀ (pow_pos hM 4) (by positivity)).mpr
    simpa only [one_mul] using hprod
  have htail : M^(e-20)≤R^(e-20) :=
    Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hR) hRM (by linarith)
  calc (1+|a|+|b|)^e*z^2
      ≤ ((3 : ℝ)^e*M^e)*(D^2/M^24) :=
        mul_le_mul hweight hsq (sq_nonneg _) (by positivity)
    _ = ((3 : ℝ)^e*D^2)*M^(e-20)*(1/M^4) := by
      rw [Real.rpow_sub hM]
      norm_num only [Real.rpow_ofNat]
      field_simp
    _ ≤ ((3 : ℝ)^e*D^2)*R^(e-20)*(16/((1+|a|)^2*(1+|b|)^2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left htail (by positivity)) hfrac (by positivity) (by positivity)
    _ = _ := by ring

private def inverseSquare (x : ℝ) : ℝ := 1/(1+|x|)^2

private theorem inverse_square_integrable : Integrable inverseSquare := by
  have hh := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  convert hh using 1
  funext x
  rw [Real.norm_eq_abs,Real.rpow_neg (by positivity : (0 : ℝ)≤1+|x|),Real.rpow_two]
  simp only [inverseSquare,one_div]

private def tailDensity (ab : ℝ×ℝ) : ℝ := inverseSquare ab.1*inverseSquare ab.2

private theorem tail_density_integrable : Integrable tailDensity :=
  inverse_square_integrable.mul_prod inverse_square_integrable

private theorem tail_density_nonneg (ab : ℝ×ℝ) : 0≤tailDensity ab := by
  dsimp only [tailDensity,inverseSquare]
  positivity

private theorem reciprocal_kernel_measurable
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (lam : ℝ) :
    Measurable (fun ab : ℝ×ℝ => bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)) := by
  let F := bagCubicNormalizedSlice δ.1 h.1
  let f : (((ℝ×ℝ)×ℝ)×ℝ)×ℝ→ℂ := fun z =>
    F z.2*F z.1.2*star (F z.1.1.2)/(z.1.1.2 : ℂ)^2*
      (bagPhysicalHeightWindow (z.2*z.1.2/z.1.1.2) : ℂ)*
      bourgainOscillation (-(z.2*z.1.1.1.2+z.1.2*z.1.1.1.1+lam*z.1.1.1.1*z.1.1.1.2)/z.1.1.2)
  have hF : Measurable F := (bagCubicNormalizedSlice_properties δ h).1.continuous.measurable
  have hW : Measurable (bagPhysicalHeightWindow : ℝ→ℝ) := (show ContDiff ℝ ∞ (bagPhysicalHeightWindow : ℝ→ℝ) from bagPhysicalHeightWindow.contDiff).continuous.measurable
  have hf : Measurable f := by
    dsimp only [f]
    unfold bourgainOscillation
    fun_prop
  exact hf.stronglyMeasurable.integral_prod_right'.integral_prod_right'.integral_prod_right'.measurable

/-- Uniform admitted complementary tail energy of the full actual reciprocal kernel. -/
theorem bagCubicReciprocalKernel_tail_energy (s : {r : ℝ // r∈Ico (0 : ℝ) (3/2)}) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀lam : ℝ, ∀R : {r : ℝ // 1≤r},
      IntegrableOn (fun ab : ℝ×ℝ => (1+|ab.1|+|ab.2|)^(2*s.1)*
        ‖bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)‖^2)
        {ab : ℝ×ℝ | R.1 ≤ max |ab.1| |ab.2|} ∧
      (∫ab : ℝ×ℝ in {ab : ℝ×ℝ | R.1 ≤ max |ab.1| |ab.2|},
        (1+|ab.1|+|ab.2|)^(2*s.1)*‖bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)‖^2)
        ≤C/δ.1^22*R.1^(2*s.1-20) := by
  obtain ⟨K,hK,hKb⟩ := bagCubicReciprocalKernel_frequency_decay ⟨12,by omega⟩
  let mass := ∫ab : ℝ×ℝ, tailDensity ab
  have hmass : 0 ≤ mass := integral_nonneg tail_density_nonneg
  refine ⟨16*(3 : ℝ)^(2*s.1)*K^2*(mass+1),by positivity,fun δ h lam R => ?_⟩
  let T := {ab : ℝ×ℝ | R.1 ≤ max |ab.1| |ab.2|}
  let J : ℝ×ℝ→ℝ := fun ab => (1+|ab.1|+|ab.2|)^(2*s.1)*
    ‖bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)‖^2
  let D := K/δ.1^11
  let L := 16*(3 : ℝ)^(2*s.1)*D^2*R.1^(2*s.1-20)
  have hRpos : 0<R.1 := lt_of_lt_of_le zero_lt_one R.2
  have hL : 0≤L := by dsimp only [L]; positivity
  have hT : MeasurableSet T := measurableSet_le measurable_const (measurable_fst.abs.max measurable_snd.abs)
  have hKm := reciprocal_kernel_measurable δ h lam
  have hJm : Measurable J := by dsimp only [J]; fun_prop
  have hJn (ab : ℝ×ℝ) : 0≤J ab := by dsimp only [J]; positivity
  have hpw (ab : ℝ×ℝ) (hab : ab∈T) : J ab≤L*tailDensity ab := by
    have hd : (max |ab.1| |ab.2|)^12*
        ‖bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)‖≤D :=
      hKb δ h ab.1 ab.2 (lam*ab.1*ab.2)
    have hh := tail_energy_majorant (2*s.1) ab.1 ab.2 R.1
      ‖bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)‖ D
      (by linarith [s.2.1]) (by linarith [s.2.2]) R.2 hab (norm_nonneg _) hd
    exact hh.trans_eq (by
      dsimp only [L,tailDensity,inverseSquare]
      simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
      ring)
  have hJi : IntegrableOn J T := by
    apply (tail_density_integrable.integrableOn.const_mul L).mono' hJm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hT] with ab hab
    rw [Real.norm_eq_abs,abs_of_nonneg (hJn ab)]
    exact hpw ab hab
  refine ⟨hJi,?_⟩
  calc (∫ab : ℝ×ℝ in T, J ab)
      ≤ ∫ab : ℝ×ℝ in T, L*tailDensity ab :=
        setIntegral_mono_on hJi (tail_density_integrable.integrableOn.const_mul L) hT hpw
    _ = L*(∫ab : ℝ×ℝ in T, tailDensity ab) := integral_const_mul _ _
    _ ≤ L*mass := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral tail_density_integrable (Eventually.of_forall tail_density_nonneg)) hL
    _ ≤ L*(mass+1) := mul_le_mul_of_nonneg_left (by linarith) hL
    _ = _ := by
      dsimp only [L,D]
      simp only [div_pow,←pow_mul]
      ring

private theorem selected_tail_scale {N tau : ℝ} (hN : 0<N) (htau : 0<tau) (s : ℝ) :
    (1/(N^(-(3/4 : ℝ)))^22)*(N/(4*tau))^(2*s-20)=
      (4*tau)^(20-2*s)*N^(2*s-7/2) := by
  have hpow : (N^(-(3/4 : ℝ)))^22=N^(-(33/2 : ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    congr 1
    ring
  have hleft : 1/(N^(-(3/4 : ℝ)))^22=N^(33/2 : ℝ) := by
    rw [hpow,Real.rpow_neg hN.le,one_div,inv_inv]
  have hright : (N/(4*tau))^(2*s-20)=N^(2*s-20)*(4*tau)^(20-2*s) := by
    rw [Real.div_rpow hN.le (by positivity),div_eq_mul_inv,←Real.rpow_neg (by positivity : 0≤4*tau)]
    congr 2
    ring
  rw [hleft,hright]
  calc N^(33/2 : ℝ)*(N^(2*s-20)*(4*tau)^(20-2*s))
      = (4*tau)^(20-2*s)*(N^(33/2 : ℝ)*N^(2*s-20)) := by ring
    _ = _ := by
      rw [←Real.rpow_add hN,show (33/2 : ℝ)+(2*s-20)=2*s-7/2 by ring]

private theorem selected_parameters_eventually (tau : {r : ℝ // 0<r}) :
    ∀ᶠ N : ℝ in atTop,
      1<N ∧ N^(-(3/4 : ℝ))∈Ioo (0 : ℝ) (1/2) ∧
      1/Real.log N∈Icc (0 : ℝ) 1 ∧ 1≤N/(4*tau.1) := by
  have hd := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<3/4)
  filter_upwards [eventually_ge_atTop (Real.exp 1),eventually_ge_atTop (4*tau.1),
    hd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with N hN hNt hdN
  have hN1 : 1<N := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) hN
  have hN0 : 0<N := zero_lt_one.trans hN1
  have hL : 1≤Real.log N := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hN
  refine ⟨hN1,⟨Real.rpow_pos_of_pos hN0 _,hdN⟩,?_,?_⟩
  · exact ⟨div_nonneg zero_le_one (by linarith),
      (div_le_iff₀ (Real.log_pos hN1)).mpr (by simpa using hL)⟩
  · exact (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ)<4) tau.2)).mpr (by simpa using hNt)

/-- Global weighted energy for the literal selected shrinking-cutoff family. -/
theorem bagCubicReciprocalKernel_selected_uniform_energy
    (s : {r : ℝ // r∈Ico (0 : ℝ) (3/2)}) (tau : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop,
      Integrable (fun ab : ℝ×ℝ => (1+|ab.1|+|ab.2|)^(2*s.1)*
        ‖bagCubicReciprocalKernel (N^(-(3/4 : ℝ))) (1/Real.log N)
          ab.1 ab.2 ((tau.1/N)*ab.1*ab.2)‖^2) ∧
      (∫ab : ℝ×ℝ, (1+|ab.1|+|ab.2|)^(2*s.1)*
        ‖bagCubicReciprocalKernel (N^(-(3/4 : ℝ))) (1/Real.log N)
          ab.1 ab.2 ((tau.1/N)*ab.1*ab.2)‖^2)≤C := by
  obtain ⟨B,hB,hBb⟩ := bagCubicReciprocalKernel_uniform_strip_energy s
  obtain ⟨C,hC,hCb⟩ := bagCubicReciprocalKernel_tail_energy s
  have htau := tau.2
  refine ⟨B+C*(4*tau.1)^(20-2*s.1),by positivity,?_⟩
  filter_upwards [selected_parameters_eventually tau] with N hpars
  have hN1 := hpars.1
  have hN : 0<N := zero_lt_one.trans hN1
  let δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)} := ⟨N^(-(3/4 : ℝ)),hpars.2.1⟩
  let h : {r : ℝ // r∈Icc (0 : ℝ) 1} := ⟨1/Real.log N,hpars.2.2.1⟩
  let R : {r : ℝ // 1≤r} := ⟨N/(4*tau.1),hpars.2.2.2⟩
  let lam := tau.1/N
  let S := {ab : ℝ×ℝ | |lam*ab.1|≤1/4}
  let T := {ab : ℝ×ℝ | R.1 ≤ max |ab.1| |ab.2|}
  let J : ℝ×ℝ→ℝ := fun ab => (1+|ab.1|+|ab.2|)^(2*s.1)*
    ‖bagCubicReciprocalKernel δ.1 h.1 ab.1 ab.2 (lam*ab.1*ab.2)‖^2
  have hJ (ab : ℝ×ℝ) : 0≤J ab := by dsimp only [J]; positivity
  have hS : MeasurableSet S := measurableSet_le (measurable_const.mul measurable_fst).abs measurable_const
  have hScT : Sᶜ⊆T := by
    intro ab hab
    have hh : (1/4 : ℝ) < |lam*ab.1| := lt_of_not_ge hab
    rw [abs_mul,abs_of_pos (div_pos tau.2 hN)] at hh
    have he : (tau.1/N)*|ab.1|=(tau.1*|ab.1|)/N := by ring
    change 1/4<(tau.1/N)*|ab.1| at hh
    rw [he] at hh
    have hh' := (lt_div_iff₀ hN).mp hh
    have ha : N/(4*tau.1)≤|ab.1| := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ)<4*tau.1)).mpr
      nlinarith only [hh']
    exact ha.trans (le_max_left _ _)
  have hstrip := hBb δ h lam
  have htail := hCb δ h lam R
  have hSi : IntegrableOn J S := hstrip.1
  have hTi : IntegrableOn J T := htail.1
  have hSci : IntegrableOn J Sᶜ := hTi.mono_set hScT
  have hi : Integrable J := by
    have hh := hSi.union hSci
    simpa only [union_compl_self,integrableOn_univ] using hh
  have htailb : (∫ab : ℝ×ℝ in T, J ab)≤C*(4*tau.1)^(20-2*s.1) := by
    refine htail.2.trans ?_
    have hscale := selected_tail_scale hN tau.2 s.1
    have hpow : N^(2*s.1-7/2)≤1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1.le (by linarith [s.2.2])
    calc C/δ.1^22*R.1^(2*s.1-20)
        = C*((1/(N^(-(3/4 : ℝ)))^22)*(N/(4*tau.1))^(2*s.1-20)) := by dsimp only [δ,R]; ring
      _ = C*((4*tau.1)^(20-2*s.1)*N^(2*s.1-7/2)) := by rw [hscale]
      _ ≤ C*((4*tau.1)^(20-2*s.1)*1) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) hC.le
      _ = _ := by ring
  refine ⟨hi,?_⟩
  change (∫ab : ℝ×ℝ, J ab)≤_
  rw [←integral_add_compl hS hi]
  exact add_le_add hstrip.2 ((setIntegral_mono_set hTi (Eventually.of_forall hJ)
    (Eventually.of_forall hScT)).trans htailb)

end RHTower.BAGTrace
