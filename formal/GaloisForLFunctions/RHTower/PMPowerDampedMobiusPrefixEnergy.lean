import GaloisForLFunctions.RHTower.PMPowerDampedMobiusSource
import GaloisForLFunctions.RHTower.EulerDeletionMobiusGlobalLogSaving
import GaloisForLFunctions.RHTower.ArchimedeanMellinFourier

/-!
# Unconditional logarithmic savings for the literal Möbius Fermi prefixes

Reciprocal half-density identifies the physical modular source with the existing
Báez-Duarte carrier, preserving its full square integral. Its dyadic difference,
minus the exact harmonic correction, is the literal raw Möbius Fermi prefix.

The full prefix energy is bounded by twelve times the modular carrier energy
plus eighteen times the squared harmonic partial sum. Existing unconditional
Mertens cancellation therefore gives every fixed logarithmic saving relative to
N. This is preparation for endpoint power damping; it does not prove canonical
admission at arbitrarily small positive dampings or RH.
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.NymanMellin
open scoped InnerProductSpace
noncomputable section
namespace RHTower


-- Exact integral realization of an admitted function's L² norm.
theorem pm_integral_norm_sq_toLp {μ : Measure ℝ} {f : ℝ → ℂ} (hf : MemLp f 2 μ) :
    (∫ t, ‖f t‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  apply Complex.ofReal_injective
  calc
    ((∫ t, ‖f t‖ ^ 2 ∂μ : ℝ) : ℂ) = ∫ t, ((‖f t‖ ^ 2 : ℝ) : ℂ) ∂μ := by
      exact integral_complex_ofReal.symm
    _ = inner ℂ (hf.toLp f) (hf.toLp f) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with t ht
      rw [ht, inner_self_eq_norm_sq_to_K]
      norm_cast
    _ = ((‖hf.toLp f‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast

-- Modular prefix in the physical coordinate.
def pmMobiusModularSource (N : ℕ) (t : ℝ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
    (nymanGen (d : ℝ) t - ((d : ℂ)⁻¹) * nymanGen 1 t))

theorem pmMobiusModularSource_reciprocal (N : ℕ) (u : ℝ) :
    pmMobiusModularSource N u⁻¹ * (u : ℂ)⁻¹ =
      ∑ d ∈ Finset.Icc 1 N, (-(ArithmeticFunction.moebius d : ℂ)) *
        bdGenFun (1 / (d : ℝ)) u := by
  unfold pmMobiusModularSource bdGenFun nymanGen
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have harg : 1 / ((d : ℝ) * u⁻¹) = (1 / (d : ℝ)) * u := by simp [div_eq_mul_inv, mul_comm]
  rw [harg]
  simp only [one_mul, one_div, inv_inv, Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

theorem pmMobiusModularSource_eq_zero_of_one_lt (N : ℕ) {t : ℝ} (ht : 1 < t) :
    pmMobiusModularSource N t = 0 := by
  unfold pmMobiusModularSource
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro d hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hdt : 1 < (d : ℝ) * t := lt_of_lt_of_le ht
    (le_mul_of_one_le_left (by linarith) hd1)
  have ht0 : 0 < t := by linarith
  have hd0 : 0 < (d : ℝ) := by linarith
  rw [nymanGen, nymanGen, one_mul,
    Int.fract_eq_self.mpr ⟨by positivity, (div_lt_one (by positivity)).mpr hdt⟩,
    Int.fract_eq_self.mpr ⟨by positivity, (div_lt_one ht0).mpr ht⟩]
  push_cast
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

theorem pm_integrable_sq_reciprocal_iff (f : ℝ → ℂ) :
    IntegrableOn (fun u : ℝ => ‖f u⁻¹ * (u : ℂ)⁻¹‖ ^ 2) (Ioi 0) ↔
      IntegrableOn (fun t : ℝ => ‖f t‖ ^ 2) (Ioi 0) := by
  have h := integrableOn_Ioi_comp_rpow_iff (fun t : ℝ => ‖f t‖ ^ 2)
    (p := (-1 : ℝ)) (by norm_num)
  have heq : ∀ u ∈ Ioi (0 : ℝ),
      (|(-1 : ℝ)| * u ^ ((-1 : ℝ) - 1)) • ‖f (u ^ (-1 : ℝ))‖ ^ 2 =
        ‖f u⁻¹ * (u : ℂ)⁻¹‖ ^ 2 := by
    intro u hu
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, show |u| = u from abs_of_pos hu]
    norm_num [Real.rpow_neg_one, Real.rpow_neg hu.le, Real.rpow_two, mul_pow]
    ring
  exact (integrableOn_congr_fun heq measurableSet_Ioi).symm.trans h

theorem measurable_pmMobiusModularSource (N : ℕ) :
    Measurable (pmMobiusModularSource N) := by
  unfold pmMobiusModularSource
  exact (Finset.measurable_sum (Finset.Icc 1 N) fun (d : ℕ) _ =>
    (measurable_const (a := (ArithmeticFunction.moebius d : ℂ))).mul
      ((measurable_nymanGen (d : ℝ)).sub
        ((measurable_const (a := (d : ℂ)⁻¹)).mul (measurable_nymanGen 1)))).neg

theorem pmMobiusModularSource_carrier_ae (N : ℕ) :
    (fun u : ℝ => pmMobiusModularSource N u⁻¹ * (u : ℂ)⁻¹) =ᵐ[bdMeasure]
      (bdMobiusModularApproximantVec N : ℝ → ℂ) := by
  rw [bdMobiusModularApproximantVec_eq_generatorCombination]
  let c : ℕ → ℂ := fun d => -(ArithmeticFunction.moebius d : ℂ)
  have hsum : ∀ (S : Finset ℕ),
      (fun u : ℝ => ∑ d ∈ S, c d * bdGenFun (1 / (d : ℝ)) u) =ᵐ[bdMeasure]
        ((∑ d ∈ S, c d • bdGen (1 / (d : ℝ)) : BDCarrier) : ℝ → ℂ) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      filter_upwards [Lp.coeFn_zero ℂ 2 bdMeasure] with u hu
      simpa only [Finset.sum_empty, Pi.zero_apply] using hu.symm
    | @insert d S hd ih =>
      filter_upwards [ih, (memLp_bdGenFun (1 / (d : ℝ))).coeFn_toLp,
        Lp.coeFn_smul (c d) (bdGen (1 / (d : ℝ))),
        Lp.coeFn_add (c d • bdGen (1 / (d : ℝ))) (∑ k ∈ S, c k • bdGen (1 / (k : ℝ)))]
        with u hu hgen hsmul hadd
      rw [Finset.sum_insert hd, Finset.sum_insert hd, hadd, Pi.add_apply, hsmul,
        Pi.smul_apply, smul_eq_mul, bdGen, hgen, hu]
  filter_upwards [hsum (Finset.Icc 1 N)] with u hu
  rw [pmMobiusModularSource_reciprocal]
  change (∑ d ∈ Finset.Icc 1 N, c d * bdGenFun (1 / (d : ℝ)) u) = _
  rw [hu]
  simp only [bdMobiusGeneratorCombination, c, Complex.ofReal_neg, Complex.ofReal_intCast]

theorem pmMobiusModularSource_reciprocal_sq_integrable (N : ℕ) :
    IntegrableOn (fun u : ℝ => ‖pmMobiusModularSource N u⁻¹ * (u : ℂ)⁻¹‖ ^ 2) (Ioi 0) := by
  have htail : IntegrableOn (fun u : ℝ =>
      ‖pmMobiusModularSource N u⁻¹ * (u : ℂ)⁻¹‖ ^ 2) (Ioi 1) := by
    refine ((Lp.memLp (bdMobiusModularApproximantVec N)).norm.integrable_sq).congr ?_
    filter_upwards [pmMobiusModularSource_carrier_ae N] with u hu
    rw [hu]
  have hhead : IntegrableOn (fun u : ℝ =>
      ‖pmMobiusModularSource N u⁻¹ * (u : ℂ)⁻¹‖ ^ 2) (Ioo 0 1) := by
    refine (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioo 0 1)).congr_fun
      (fun u hu => ?_) measurableSet_Ioo
    rw [pmMobiusModularSource_eq_zero_of_one_lt N (one_lt_inv_iff₀.mpr hu)]
    simp
  rw [← Ioo_union_Ici_eq_Ioi (by norm_num : (0 : ℝ) < 1)]
  exact hhead.union ((integrableOn_Ici_iff_integrableOn_Ioi).mpr htail)

theorem memLp_pmMobiusModularSource (N : ℕ) :
    MemLp (pmMobiusModularSource N) 2 (volume.restrict (Ioi 0)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_pmMobiusModularSource N).aestronglyMeasurable).mpr
  exact (pm_integrable_sq_reciprocal_iff _).mp
    (pmMobiusModularSource_reciprocal_sq_integrable N)

theorem pmMobiusModularSource_norm_sq (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖pmMobiusModularSource N t‖ ^ 2) =
      ‖bdMobiusModularApproximantVec N‖ ^ 2 := by
  have hrecip : (∫ t in Ioi (0 : ℝ), ‖pmMobiusModularSource N t‖ ^ 2) =
      ∫ u in Ioi (0 : ℝ), ‖pmMobiusModularSource N u⁻¹ * (u : ℂ)⁻¹‖ ^ 2 := by
    rw [integral_Ioi_comp_inv]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change (u ^ 2)⁻¹ * ‖pmMobiusModularSource N u⁻¹‖ ^ 2 =
      ‖pmMobiusModularSource N u⁻¹ * (u : ℂ)⁻¹‖ ^ 2
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    simp only [mul_pow, inv_pow]
    ring
  rw [hrecip]
  have hcut : (∫ u in Ioi (0 : ℝ), ‖pmMobiusModularSource N u⁻¹ * (u : ℂ)⁻¹‖ ^ 2) =
      ∫ u in Ici (1 : ℝ), ‖pmMobiusModularSource N u⁻¹ * (u : ℂ)⁻¹‖ ^ 2 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (show Ici (1 : ℝ) ⊆ Ioi 0 from fun u hu => lt_of_lt_of_le (show (0 : ℝ) < 1 from zero_lt_one) hu)
    intro u hu
    have hlu : u < 1 := lt_of_not_ge hu.2
    rw [pmMobiusModularSource_eq_zero_of_one_lt N (one_lt_inv_iff₀.mpr ⟨hu.1, hlu⟩)]
    simp
  rw [hcut, integral_Ici_eq_integral_Ioi]
  have hae := pmMobiusModularSource_carrier_ae N
  calc
    _ = ∫ u in Ioi (1 : ℝ), ‖(bdMobiusModularApproximantVec N : ℝ → ℂ) u‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hae] with u hu
      rw [hu]
    _ = ‖bdMobiusModularApproximantVec N‖ ^ 2 := by
      have h := pm_integral_norm_sq_toLp (Lp.memLp (bdMobiusModularApproximantVec N))
      have hv : (Lp.memLp (bdMobiusModularApproximantVec N)).toLp
          (bdMobiusModularApproximantVec N : ℝ → ℂ) = bdMobiusModularApproximantVec N := by
        apply Lp.ext
        exact (Lp.memLp (bdMobiusModularApproximantVec N)).coeFn_toLp
      rw [hv] at h
      exact h

theorem rawMobiusFermiApprox_eq_modular_difference (N : ℕ) (t : ℝ) :
    rawMobiusFermiApprox N t =
      fermiDilationDifference (pmMobiusModularSource N) t -
        (deningerHarmonicPartial N : ℂ) * fermiNymanGen 1 t := by
  have hgen : ∀ d : ℝ, nymanGen d (2 * t) = nymanGen (2 * d) t := by
    intro d
    unfold nymanGen
    rw [show d * (2 * t) = 2 * d * t by ring]
  have hsum : (∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℂ) * (d : ℂ)⁻¹) =
        (deningerHarmonicPartial N : ℂ) := by
    rw [deningerHarmonicPartial_eq_sum_Icc]
    push_cast
    simp only [div_eq_mul_inv]
  unfold rawMobiusFermiApprox fermiDilationDifference pmMobiusModularSource
  simp_rw [fermiNymanGen, hgen, mul_sub]
  simp only [Finset.sum_sub_distrib]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
  have htwo : (∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℂ) * 2 * nymanGen (2 * (d : ℝ)) t) =
        2 * ∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℂ) * nymanGen (2 * (d : ℝ)) t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [htwo]
  ring

theorem pm_integral_normSq_fermiDilationDifference_le {f : ℝ → ℂ}
    (hm : Measurable f) (hf : MemLp f 2 (volume.restrict (Ioi 0))) :
    (∫ t in Ioi (0 : ℝ), ‖fermiDilationDifference f t‖ ^ 2) ≤
      6 * ∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2 := by
  have hi : IntegrableOn (fun t : ℝ => ‖f t‖ ^ 2) (Ioi (0 : ℝ)) := hf.norm.integrable_sq
  have hg : IntegrableOn (fun t : ℝ => ‖f (2 * t)‖ ^ 2) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => ‖f t‖ ^ 2) 0
      (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [mul_zero] using hi
  have hd := integrableOn_normSq_fermiDilationDifference hm hi
  have hpoint : ∀ t : ℝ, ‖fermiDilationDifference f t‖ ^ 2 ≤
      2 * ‖f t‖ ^ 2 + 8 * ‖f (2 * t)‖ ^ 2 := by
    intro t
    have h := norm_sub_le (f t) ((2 : ℂ) * f (2 * t))
    rw [norm_mul] at h
    norm_num at h
    change ‖f t - 2 * f (2 * t)‖ ^ 2 ≤ _
    nlinarith [norm_nonneg (f t), norm_nonneg (f (2 * t)),
      norm_nonneg (f t - 2 * f (2 * t)), sq_nonneg (‖f t‖ - 2 * ‖f (2 * t)‖)]
  have h := setIntegral_mono_on hd ((hi.const_mul 2).add (hg.const_mul 8))
    measurableSet_Ioi (fun t _ => hpoint t)
  simp only [Pi.add_apply] at h
  rw [integral_add (hi.const_mul 2) (hg.const_mul 8), integral_const_mul,
    integral_const_mul, integral_comp_mul_left_Ioi (fun t : ℝ => ‖f t‖ ^ 2) 0
      (by norm_num : (0 : ℝ) < 2)] at h
  norm_num [smul_eq_mul] at h
  linarith

theorem memLp_pm_fermiNymanGen {a : ℝ} (ha : 0 < a) :
    MemLp (fermiNymanGen a) 2 (volume.restrict (Ioi 0)) :=
  ⟨(measurable_fermiNymanGen a).aestronglyMeasurable,
    (pm_eLpNorm_fermiNymanGen_le ha).trans_lt ENNReal.ofReal_lt_top⟩

theorem pm_integral_normSq_fermiNymanGen_one_le :
    (∫ t in Ioi (0 : ℝ), ‖fermiNymanGen 1 t‖ ^ 2) ≤ 9 := by
  have hm := memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1)
  have hn : ‖hm.toLp (fermiNymanGen 1)‖ ≤ 3 := by
    rw [Lp.norm_toLp]
    apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
    simpa using pm_eLpNorm_fermiNymanGen_le (by norm_num : (0 : ℝ) < 1)
  rw [pm_integral_norm_sq_toLp hm]
  nlinarith [norm_nonneg (hm.toLp (fermiNymanGen 1))]

theorem memLp_rawMobiusFermiApprox (N : ℕ) :
    MemLp (rawMobiusFermiApprox N) 2 (volume.restrict (Ioi 0)) := by
  have heq : rawMobiusFermiApprox N = fun t =>
      fermiDilationDifference (pmMobiusModularSource N) t -
        (deningerHarmonicPartial N : ℂ) * fermiNymanGen 1 t :=
    funext (rawMobiusFermiApprox_eq_modular_difference N)
  rw [heq]
  have hm : Measurable (fermiDilationDifference (pmMobiusModularSource N)) :=
    (measurable_pmMobiusModularSource N).sub (measurable_const.mul
      ((measurable_pmMobiusModularSource N).comp (measurable_const.mul measurable_id)))
  have hd : MemLp (fermiDilationDifference (pmMobiusModularSource N)) 2
      (volume.restrict (Ioi 0)) :=
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
      (integrableOn_normSq_fermiDilationDifference (measurable_pmMobiusModularSource N)
        (memLp_pmMobiusModularSource N).norm.integrable_sq)
  exact hd.sub ((memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1)).const_mul _)

theorem pm_rawMobiusFermiApprox_energy_le (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖rawMobiusFermiApprox N t‖ ^ 2) ≤
      12 * ‖bdMobiusModularApproximantVec N‖ ^ 2 +
        18 * deningerHarmonicPartial N ^ 2 := by
  let B := pmMobiusModularSource N
  let H := deningerHarmonicPartial N
  have hD := integrableOn_normSq_fermiDilationDifference (measurable_pmMobiusModularSource N)
    (memLp_pmMobiusModularSource N).norm.integrable_sq
  have hG := (memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1)).norm.integrable_sq
  have hpoint : ∀ t : ℝ, ‖rawMobiusFermiApprox N t‖ ^ 2 ≤
      2 * ‖fermiDilationDifference B t‖ ^ 2 + 2 * H ^ 2 * ‖fermiNymanGen 1 t‖ ^ 2 := by
    intro t
    rw [rawMobiusFermiApprox_eq_modular_difference]
    have h := norm_sub_le (fermiDilationDifference B t) ((H : ℂ) * fermiNymanGen 1 t)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
    change ‖fermiDilationDifference B t - (H : ℂ) * fermiNymanGen 1 t‖ ^ 2 ≤ _
    have habs : |H| ^ 2 = H ^ 2 := sq_abs H
    nlinarith [norm_nonneg (fermiDilationDifference B t), norm_nonneg (fermiNymanGen 1 t),
      norm_nonneg (fermiDilationDifference B t - (H : ℂ) * fermiNymanGen 1 t),
      sq_nonneg (‖fermiDilationDifference B t‖ - |H| * ‖fermiNymanGen 1 t‖)]
  have h := setIntegral_mono_on (memLp_rawMobiusFermiApprox N).norm.integrable_sq
    ((hD.const_mul 2).add (hG.const_mul (2 * H ^ 2))) measurableSet_Ioi (fun t _ => hpoint t)
  simp only [Pi.add_apply] at h
  rw [integral_add (hD.const_mul 2) (hG.const_mul (2 * H ^ 2)),
    integral_const_mul, integral_const_mul] at h
  have hDB := pm_integral_normSq_fermiDilationDifference_le
    (measurable_pmMobiusModularSource N) (memLp_pmMobiusModularSource N)
  rw [pmMobiusModularSource_norm_sq] at hDB
  have hGle := mul_le_mul_of_nonneg_left pm_integral_normSq_fermiNymanGen_one_le
    (show 0 ≤ 2 * H ^ 2 by positivity)
  dsimp only [B, H] at h hGle
  linarith

theorem pm_rawMobiusFermiApprox_energy_log_saving (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      (∫ t in Ioi (0 : ℝ), ‖rawMobiusFermiApprox N t‖ ^ 2) ≤
        C * (N : ℝ) / Real.log (N : ℝ) ^ (q + 1) := by
  obtain ⟨B, hB, hrate⟩ := DeletionMobiusGlobal.modular_norm_log_saving q
  obtain ⟨D, hD⟩ := deningerHarmonicPartial_bounded
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpower : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ (q + 1) ≤ (N : ℝ) := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (burnolEventually_log_pow_le_rpow (δ := 1) (by norm_num) (q + 1))
    simpa only [Real.rpow_one] using h
  refine ⟨12 * B + 18 * D ^ 2, by positivity, ?_⟩
  filter_upwards [hrate, hpower, hlog.eventually_ge_atTop 1] with N hN hPN hLN
  have hlog0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hLN
  have hden : 0 < Real.log (N : ℝ) ^ (q + 1) := pow_pos hlog0 _
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD N)
  have hH : deningerHarmonicPartial N ^ 2 ≤ D ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (hD N) 2
    simpa only [sq_abs] using h
  have hconst : D ^ 2 ≤ D ^ 2 * (N : ℝ) / Real.log (N : ℝ) ^ (q + 1) := by
    apply (le_div_iff₀ hden).mpr
    exact mul_le_mul_of_nonneg_left hPN (sq_nonneg D)
  calc
    _ ≤ 12 * ‖bdMobiusModularApproximantVec N‖ ^ 2 +
        18 * deningerHarmonicPartial N ^ 2 := pm_rawMobiusFermiApprox_energy_le N
    _ ≤ 12 * (B * (N : ℝ) / Real.log (N : ℝ) ^ (q + 1)) +
        18 * (D ^ 2 * (N : ℝ) / Real.log (N : ℝ) ^ (q + 1)) := by
      gcongr
      exact hH.trans hconst
    _ = _ := by ring

end RHTower
