import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeSlabBounds
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPositiveHaarPrefix
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Boundary moments for the actual power-damped Möbius source

The boundary is `s = 1 - ε`. These moments concern the literal source;
canonical square integrability is not an input.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
namespace RHTower

private theorem pmb_reciprocal_source_bound {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) :
    ‖pmPowerDampedFermiSource ε (1/x)‖ ≤ 2*x := by
  rw [pmPowerDampedFermiSource_eq_divisor_counts ε (by positivity), one_div_one_div,
    show 1/(2*(1/x)) = x/2 by field_simp]
  calc
    _ ≤ ‖(pmPowerDampedDivisorSum ε x : ℂ)‖ +
        ‖2*(pmPowerDampedDivisorSum ε (x/2) : ℂ)‖ := norm_sub_le _ _
    _ ≤ x+2*(x/2) := by
      simp only [norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pmPowerDampedDivisorSum_nonneg hε _)]
      exact add_le_add (pmPowerDampedDivisorSum_le hε hx.le)
        (mul_le_mul_of_nonneg_left (pmPowerDampedDivisorSum_le hε (by positivity))
          (by norm_num))
    _ = _ := by ring

/-- The unconditional remainder saving holds at every sufficiently large real
reciprocal argument, including the moving prime cofactors. -/
theorem pmPowerDampedFermiSource_reciprocal_eventually_log_four {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      ‖pmPowerDampedFermiSource ε (1/x)‖ ≤ C*x^(1-ε)/Real.log x^4 := by
  obtain ⟨A,D,hA,hD,he⟩ := pmPowerDampedFermiSource_prime_slab_bound hε hεhalf
  obtain ⟨K,hK⟩ := eventually_atTop.mp he
  have hs := (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
    (by linarith : 0 < 1-ε)).bound (c := 1) (by norm_num)
  refine ⟨A+16*D,by positivity,?_⟩
  filter_upwards [hs,eventually_ge_atTop (3*((K : ℝ)+1)),eventually_ge_atTop 16]
    with x hsx hxK hx16
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  let P : ℕ := ⌊2*x/3⌋₊
  have hPf : (P : ℝ) ≤ 2*x/3 := Nat.floor_le (by positivity)
  have hfP : 2*x/3 < (P : ℝ)+1 := Nat.lt_floor_add_one _
  have hPK : K ≤ P := by
    apply Nat.le_floor
    linarith
  have hPx : x/2 ≤ (P : ℝ) := by linarith
  have hP0 : (0 : ℝ) < P := by linarith
  have hPs : x ≤ (P : ℝ)^2 := by nlinarith
  have hlogP : Real.log x/2 ≤ Real.log (P : ℝ) := by
    have h := Real.log_le_log hx0 hPs
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hb := hK P hPK x (by linarith) (by linarith)
  have hm : D*(P : ℝ)^(1-ε)/Real.log (P : ℝ)^4 ≤
      16*D*x^(1-ε)/Real.log x^4 := by
    calc
      _ ≤ D*x^(1-ε)/(Real.log x/2)^4 := by
        apply div_le_div₀ (by positivity) _ (by positivity)
          (pow_le_pow_left₀ (by positivity) hlogP 4)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hP0.le (by linarith) (by linarith)) hD
      _ = _ := by ring
  have hp : Real.log x^4 ≤ x^(1-ε) := by
    simpa only [show (4 : ℝ) = (4 : ℕ) by norm_num,Real.rpow_natCast,
      Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hlx.le 4),
      abs_of_nonneg (Real.rpow_nonneg hx0.le (1-ε)),one_mul] using hsx
  have hAb : A ≤ A*x^(1-ε)/Real.log x^4 := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact mul_le_mul_of_nonneg_left hp hA
  calc
    _ ≤ A+D*(P : ℝ)^(1-ε)/Real.log (P : ℝ)^4 := hb
    _ ≤ A*x^(1-ε)/Real.log x^4 + 16*D*x^(1-ε)/Real.log x^4 := add_le_add hAb hm
    _ = _ := by ring

private def pmb_boundaryMajorant (ε x : ℝ) : ℝ :=
  ‖pmPowerDampedFermiSource ε (1/x)‖ * x^(ε-2) * (1+Real.log x^2)

private theorem pmb_boundaryMajorant_measurable (ε : ℝ) :
    Measurable (pmb_boundaryMajorant ε) := by
  exact (((measurable_pmPowerDampedFermiSource ε).comp
    (measurable_const.div measurable_id)).norm.mul (measurable_id.pow_const _)).mul
      (measurable_const.add (Real.measurable_log.pow_const 2))

/-- Absolute second logarithmic moment at the actual source's Mellin boundary. -/
theorem integrableOn_pmPowerDampedFermiSource_boundary_log_sq {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    IntegrableOn (fun x : ℝ => ‖pmPowerDampedFermiSource ε (1/x)‖ *
      x^(ε-2)*(1+Real.log x^2)) (Ioi (1 : ℝ)) := by
  obtain ⟨C,hC,he⟩ := pmPowerDampedFermiSource_reciprocal_eventually_log_four hε hεhalf
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp he
  let R : ℝ := max R₀ (Real.exp 1)
  have hRe : Real.exp 1 ≤ R := le_max_right _ _
  have hR1 : 1 < R := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hRe
  have hm := pmb_boundaryMajorant_measurable ε
  have hhead : IntegrableOn (pmb_boundaryMajorant ε) (Icc 1 R) := by
    apply IntegrableOn.of_bound (by simp) hm.aestronglyMeasurable.restrict
      (2*R*(1+Real.log R^2))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx.1
    have hp : x^(ε-2) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
        hx.1 (by linarith : ε-2 ≤ 0)
    have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx.1
    have hl : Real.log x ≤ Real.log R := Real.log_le_log hx0 hx.2
    have hs := pmb_reciprocal_source_bound hε.le hx0
    change ‖‖pmPowerDampedFermiSource ε (1/x)‖ * x^(ε-2) * (1+Real.log x^2)‖ ≤ _
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (2*R)*1*(1+Real.log R^2) := by
        apply mul_le_mul _ (by nlinarith) (by positivity) (by positivity)
        exact mul_le_mul (hs.trans (by linarith [hx.2])) hp (by positivity) (by positivity)
      _ = _ := by ring
  have htail : IntegrableOn (pmb_boundaryMajorant ε) (Ioi R) := by
    apply ((integrableOn_inv_div_log_sq_Ioi hR1).const_mul (2*C)).mono'
      hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hR1.trans hx
    have hx0 : 0 < x := zero_lt_one.trans hx1
    have hl : 1 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) (hRe.trans hx.le)
      simpa only [Real.log_exp] using h
    have hl0 : 0 < Real.log x := zero_lt_one.trans_le hl
    have hb := hR₀ x ((le_max_left _ _).trans hx.le)
    have hp : x^(1-ε)*x^(ε-2) = x⁻¹ := by
      rw [← Real.rpow_add hx0, show 1-ε+(ε-2)=(-1 : ℝ) by ring,Real.rpow_neg_one]
    have hs : 1+Real.log x^2 ≤ 2*Real.log x^2 := by nlinarith
    change ‖‖pmPowerDampedFermiSource ε (1/x)‖ * x^(ε-2) *
      (1+Real.log x^2)‖ ≤ 2*C*(x⁻¹/Real.log x^2)
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (C*x^(1-ε)/Real.log x^4)*x^(ε-2)*(2*Real.log x^2) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hb (by positivity)) hs
          (by positivity) (by positivity)
      _ = (C*(x^(1-ε)*x^(ε-2)))*(2*Real.log x^2)/Real.log x^4 := by ring
      _ = _ := by rw [hp]; field_simp
  have hu := hhead.union htail
  exact hu.mono_set (fun x hx => by
    by_cases hxr : x ≤ R
    · exact Or.inl ⟨hx.le,hxr⟩
    · exact Or.inr (lt_of_not_ge hxr))

/-- The actual reciprocal source with its boundary Mellin weight. -/
def pmPowerDampedBoundaryWeight (ε x : ℝ) : ℂ :=
  (x^(ε-2) : ℝ)*pmPowerDampedFermiSource ε (1/x)

private theorem pmb_weight_measurable (ε : ℝ) : Measurable (pmPowerDampedBoundaryWeight ε) :=
  ((measurable_id.pow_const _).complex_ofReal).mul
    ((measurable_pmPowerDampedFermiSource ε).comp (measurable_const.div measurable_id))

private theorem pmb_weight_bound {ε x : ℝ} (hx : 1 < x) {b : ℂ}
    (hb : ‖b‖ ≤ 1+Real.log x^2) :
    ‖pmPowerDampedBoundaryWeight ε x*b‖ ≤ pmb_boundaryMajorant ε x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [norm_mul,pmPowerDampedBoundaryWeight,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  calc
    _ ≤ (x^(ε-2)*‖pmPowerDampedFermiSource ε (1/x)‖)*(1+Real.log x^2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by dsimp [pmb_boundaryMajorant]; ring

private def pmb_transform (ε δ : ℝ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), pmPowerDampedBoundaryWeight ε x * (Real.exp (-δ*Real.log x) : ℂ)

private theorem pmb_exp_integrable {ε δ : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2)
    (hδ : 0 ≤ δ) :
    IntegrableOn (fun x => pmPowerDampedBoundaryWeight ε x *
      (Real.exp (-δ*Real.log x) : ℂ)) (Ioi (1 : ℝ)) := by
  apply (integrableOn_pmPowerDampedFermiSource_boundary_log_sq hε hεhalf).mono'
    (((pmb_weight_measurable ε).mul
      ((measurable_const.mul Real.measurable_log).exp.complex_ofReal)).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  apply pmb_weight_bound hx
  rw [Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  dsimp only [Pi.mul_apply]
  have h := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) (Real.log_nonneg hx.le))
  nlinarith [sq_nonneg (Real.log x)]

private theorem pmb_exp_slope_bound {δ x : ℝ} (hδ : 0 < δ) (hx : 1 < x) :
    |(Real.exp (-δ*Real.log x)-1)/δ| ≤ 1+Real.log x^2 := by
  have hl := Real.log_nonneg hx.le
  have he : Real.exp (-δ*Real.log x) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) hl)
  have hs : |(Real.exp (-δ*Real.log x)-1)/δ| ≤ Real.log x := by
    rw [abs_div,abs_of_pos hδ,abs_of_nonpos (sub_nonpos.mpr he)]
    apply (div_le_iff₀ hδ).mpr
    nlinarith [Real.add_one_le_exp (-δ*Real.log x)]
  exact hs.trans (by nlinarith [sq_nonneg (Real.log x-1)])

theorem integrableOn_pmPowerDampedBoundaryWeight {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    IntegrableOn (pmPowerDampedBoundaryWeight ε) (Ioi (1 : ℝ)) := by
  simpa only [neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,mul_one] using
    pmb_exp_integrable hε hεhalf (δ := 0) le_rfl

theorem integrableOn_pmPowerDampedBoundaryWeight_log {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    IntegrableOn (fun x => pmPowerDampedBoundaryWeight ε x*(Real.log x : ℂ))
      (Ioi (1 : ℝ)) := by
  apply (integrableOn_pmPowerDampedFermiSource_boundary_log_sq hε hεhalf).mono'
    (((pmb_weight_measurable ε).mul Real.measurable_log.complex_ofReal).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  apply pmb_weight_bound hx
  rw [Complex.norm_real,Real.norm_of_nonneg (Real.log_nonneg hx.le)]
  nlinarith [sq_nonneg (Real.log x-1)]

private theorem pmb_exp_slope (x : ℝ) :
    Tendsto (fun δ : ℝ => (Real.exp (-δ*Real.log x)-1)/δ)
      (𝓝[>] 0) (𝓝 (-Real.log x)) := by
  have h := (((hasDerivAt_id (0 : ℝ)).neg.mul_const (Real.log x)).exp).tendsto_slope_zero_right
  simpa only [Pi.neg_apply,id_eq,zero_add,neg_zero,zero_mul,Real.exp_zero,
    one_mul,neg_mul,smul_eq_mul,div_eq_mul_inv,mul_comm] using h

private theorem pmb_boundary_right_slope {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    Tendsto (fun δ : ℝ => (pmb_transform ε δ-pmb_transform ε 0)/(δ : ℂ))
      (𝓝[>] 0) (𝓝 (-(∫ x in Ioi (1 : ℝ),
        pmPowerDampedBoundaryWeight ε x*(Real.log x : ℂ)))) := by
  let F : ℝ → ℝ → ℂ := fun δ x => pmPowerDampedBoundaryWeight ε x *
    (((Real.exp (-δ*Real.log x)-1)/δ : ℝ) : ℂ)
  have hm (δ : ℝ) : Measurable (F δ) :=
    (pmb_weight_measurable ε).mul
      (((((measurable_const.mul Real.measurable_log).exp).sub measurable_const).div
        measurable_const).complex_ofReal)
  have hb : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)),
      ‖F δ x‖ ≤ pmb_boundaryMajorant ε x := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply pmb_weight_bound hx
    simpa only [Complex.norm_real,Real.norm_eq_abs] using pmb_exp_slope_bound hδ hx
  have hl : ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)),
      Tendsto (fun δ => F δ x) (𝓝[>] 0)
        (𝓝 (-(pmPowerDampedBoundaryWeight ε x*(Real.log x : ℂ)))) := by
    filter_upwards with x
    have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (pmb_exp_slope x)).const_mul (pmPowerDampedBoundaryWeight ε x)
    simpa only [F,Function.comp_def,Complex.ofReal_neg,mul_neg] using h
  have ht := tendsto_integral_filter_of_dominated_convergence (pmb_boundaryMajorant ε)
    (Eventually.of_forall fun δ => (hm δ).aestronglyMeasurable.restrict)
    hb (integrableOn_pmPowerDampedFermiSource_boundary_log_sq hε hεhalf) hl
  rw [integral_neg] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [pmb_transform,pmb_transform,
    ← integral_sub (pmb_exp_integrable hε hεhalf hδ.le)
      (pmb_exp_integrable hε hεhalf le_rfl),← integral_div]
  apply integral_congr_ae
  filter_upwards with x
  simp only [F,neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,mul_one]
  push_cast
  ring

private theorem pmb_transform_eq_mellin (ε δ : ℝ) :
    pmb_transform ε δ = mellin (pmPowerDampedFermiSource ε) ((1-ε+δ : ℝ) : ℂ) := by
  let s : ℂ := ((ε-1-δ : ℝ) : ℂ)
  have hi := mellin_comp_inv (pmPowerDampedFermiSource ε) s
  have hs : -s = ((1-ε+δ : ℝ) : ℂ) := by dsimp [s]; push_cast; ring
  rw [hs] at hi
  rw [← hi,mellin]
  have hcut : (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1) • pmPowerDampedFermiSource ε x⁻¹) =
      ∫ x in Ici (1 : ℝ), (x : ℂ)^(s-1) • pmPowerDampedFermiSource ε x⁻¹ := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => zero_lt_one.trans_le hx)
    intro x hx
    have hx1 : x < 1 := lt_of_not_ge hx.2
    have hxi : 1 < x⁻¹ := by
      rw [← one_div]
      exact (lt_div_iff₀ hx.1).mpr (by simpa using hx1)
    rw [pmPowerDampedFermiSource_eq_zero_of_one_lt ε hxi,smul_zero]
  rw [hcut,integral_Ici_eq_integral_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have he : s-1 = ((ε-2-δ : ℝ) : ℂ) := by dsimp [s]; push_cast; ring
  have hp : x^(ε-2-δ) = x^(ε-2)*Real.exp (-δ*Real.log x) := by
    rw [Real.rpow_def_of_pos hx0,Real.rpow_def_of_pos hx0,← Real.exp_add]
    congr 1
    ring
  change pmPowerDampedBoundaryWeight ε x*(Real.exp (-δ*Real.log x) : ℂ) =
    (x : ℂ)^(s-1)*pmPowerDampedFermiSource ε x⁻¹
  rw [he,← Complex.ofReal_cpow hx0.le,hp,Complex.ofReal_mul]
  simp only [pmPowerDampedBoundaryWeight,one_div]
  ring

/-- The residue determining the first logarithmic source moment. -/
def pmPowerDampedBoundaryJet (ε : ℝ) : ℂ :=
  (1-(2 : ℂ)^(ε : ℂ))*riemannZeta ((1-ε : ℝ) : ℂ)/((1-ε : ℝ) : ℂ)

private theorem pmb_boundary_simple_jet {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    Tendsto (fun δ : ℝ => pmb_transform ε δ/(δ : ℂ))
      (𝓝[>] 0) (𝓝 (pmPowerDampedBoundaryJet ε)) := by
  have hd : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun δ : ℝ => ((1-ε+δ : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((1-ε : ℝ) : ℂ)) := by
    simpa only [Function.comp_def,add_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp (hd.const_add (1-ε))
  have ht : Tendsto (fun δ : ℝ => ((ε-δ : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (ε : ℂ)) := by
    simpa only [Function.comp_def,sub_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.sub hd)
  have h1 : Tendsto (fun δ : ℝ => ((1+δ : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def,add_zero,Complex.ofReal_one] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp (hd.const_add 1)
  have ha0 : ((1-ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : 1-ε ≠ 0)
  have ha1 : ((1-ε : ℝ) : ℂ) ≠ 1 := by exact_mod_cast (by linarith : 1-ε ≠ 1)
  have hz := (differentiableAt_riemannZeta ha1).continuousAt.tendsto.comp hs
  have hu : Tendsto (fun δ : ℝ => zetaResidueUnit ((1+δ : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def,zetaResidueUnit_one] using
      (analyticAt_zetaResidueUnit 1).continuousAt.tendsto.comp h1
  have hp := ht.const_cpow (a := (2 : ℂ)) (Or.inl (by norm_num))
  have hk := (((tendsto_const_nhds (x := (1 : ℂ))).sub hp).mul hz).div (hs.mul hu)
    (by simpa only [mul_one] using ha0)
  simp only [Function.comp_def,mul_one] at hk
  apply hk.congr'
  filter_upwards [self_mem_nhdsWithin,hd.eventually (eventually_lt_nhds hε)] with δ hδ hδε
  change 0 < δ at hδ
  dsimp only [Pi.div_apply,Pi.mul_apply,Function.comp_def]
  rw [pmb_transform_eq_mellin,
    (hasMellin_pmPowerDampedFermiSource ε (s := ((1-ε+δ : ℝ) : ℂ))
      (by simp only [Complex.ofReal_re]; linarith)
      (by simp only [Complex.ofReal_re]; linarith)
      (by simp only [Complex.ofReal_re]; linarith)).2]
  have hshift : ((1-ε+δ : ℝ) : ℂ)+(ε : ℂ) = ((1+δ : ℝ) : ℂ) := by push_cast; ring
  have hpower : 1-((1-ε+δ : ℝ) : ℂ) = ((ε-δ : ℝ) : ℂ) := by push_cast; ring
  have hne : ((1+δ : ℝ) : ℂ) ≠ 1 := by exact_mod_cast (by linarith : 1+δ ≠ 1)
  rw [hshift,hpower,zetaResidueUnit,Function.update_of_ne hne]
  have hid : ((1+δ : ℝ) : ℂ)-1 = (δ : ℂ) := by push_cast; ring
  rw [hid]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The actual boundary moment vanishes, without a square-integrability input. -/
theorem pmPowerDampedBoundaryWeight_integral {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    (∫ x in Ioi (1 : ℝ), pmPowerDampedBoundaryWeight ε x) = 0 := by
  have hd : Tendsto (fun δ : ℝ => (δ : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (pmb_transform ε) (𝓝[>] 0) (𝓝 0) := by
    have h := (pmb_boundary_simple_jet hε hεhalf).mul hd
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact div_mul_cancel₀ _ (by exact_mod_cast hδ.ne')
  have hc : Tendsto (pmb_transform ε) (𝓝[>] 0) (𝓝 (pmb_transform ε 0)) := by
    have h := ((pmb_boundary_right_slope hε hεhalf).mul hd).add_const (pmb_transform ε 0)
    simp only [mul_zero,zero_add] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [div_mul_cancel₀ _ (by exact_mod_cast hδ.ne')]
    ring
  have he := tendsto_nhds_unique hc hz
  simpa only [pmb_transform,neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,mul_one] using he

/-- The first signed logarithmic moment is fixed by the pole of zeta at one. -/
theorem pmPowerDampedBoundaryWeight_log_integral {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    (∫ x in Ioi (1 : ℝ), pmPowerDampedBoundaryWeight ε x*(Real.log x : ℂ)) =
      -pmPowerDampedBoundaryJet ε := by
  have hz : pmb_transform ε 0 = 0 := by
    simpa only [pmb_transform,neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,mul_one]
      using pmPowerDampedBoundaryWeight_integral hε hεhalf
  have h := pmb_boundary_right_slope hε hεhalf
  simp only [hz,sub_zero] at h
  have he := tendsto_nhds_unique h (pmb_boundary_simple_jet hε hεhalf)
  exact neg_eq_iff_eq_neg.mp he

/-- The boundary jet tends to the nonzero Haar value as damping vanishes. -/
theorem tendsto_pmPowerDampedBoundaryJet_zero :
    Tendsto pmPowerDampedBoundaryJet (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2 : ℂ)) := by
  have hd : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun ε : ℝ => ((Real.exp (ε*Real.log 2)-1)/ε : ℝ))
      (𝓝[>] 0) (𝓝 (Real.log 2)) := by
    have h := (((hasDerivAt_id (0 : ℝ)).mul_const (Real.log 2)).exp).tendsto_slope_zero_right
    simpa only [id_eq,zero_add,zero_mul,Real.exp_zero,one_mul,smul_eq_mul,
      div_eq_mul_inv,mul_comm] using h
  have ha : Tendsto (fun ε : ℝ => ((1-ε : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    have hc : Continuous (fun ε : ℝ => ((1-ε : ℝ) : ℂ)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun ε : ℝ => zetaResidueUnit ((1-ε : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def,zetaResidueUnit_one] using
      (analyticAt_zetaResidueUnit 1).continuousAt.tendsto.comp ha
  have ht := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hs).mul hu).div ha
    (by norm_num : (1 : ℂ) ≠ 0)
  simp only [Function.comp_def,mul_one,div_one] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,hd.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with ε hε hε1
  change 0 < ε at hε
  dsimp only [Pi.div_apply,Pi.mul_apply,Function.comp_def]
  have he0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have ha0 : ((1-ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : 1-ε ≠ 0)
  have hane : ((1-ε : ℝ) : ℂ) ≠ 1 := by exact_mod_cast (by linarith : 1-ε ≠ 1)
  have hunit : zetaResidueUnit ((1-ε : ℝ) : ℂ) =
      -(ε : ℂ)*riemannZeta ((1-ε : ℝ) : ℂ) := by
    rw [zetaResidueUnit,Function.update_of_ne hane]
    push_cast
    ring
  have hpow : (2 : ℂ)^(ε : ℂ) = (Real.exp (ε*Real.log 2) : ℂ) := by
    have h := Complex.ofReal_cpow (y := ε) (by norm_num : (0 : ℝ) ≤ 2)
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),mul_comm (Real.log 2) ε] at h
    simpa only [Complex.ofReal_ofNat] using h.symm
  rw [hunit,pmPowerDampedBoundaryJet,hpow]
  push_cast
  field_simp
  ring

end RHTower
