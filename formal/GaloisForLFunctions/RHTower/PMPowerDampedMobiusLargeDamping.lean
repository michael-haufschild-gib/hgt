import GaloisForLFunctions.RHTower.PMPowerDampedMobiusGramDiagonal
import Mathlib.Analysis.Normed.Group.Tannery

/-! The literal power-damped Fermi source has first-prime canonical asymptotic
`A_ε = −φ_1 + 2^(−ε)φ_2 + o_L²(2^(−ε))` as damping tends to infinity.
The positive overlap of the first two generators makes the leading energy
correction strictly negative. Energies approach `log 2` from below, so actual
source norms cannot be eventually nonincreasing under additional damping.
Every large-damping source used here is already canonically admitted. -/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower


def pmFirstPrimeTailMajorant (ε : ℝ) (d : ℕ) : ℝ :=
  if 3 ≤ d then 3 * (2 / (d : ℝ)) ^ ε else 0

theorem pmFirstPrimeTailMajorant_nonneg (ε : ℝ) (d : ℕ) :
    0 ≤ pmFirstPrimeTailMajorant ε d := by
  unfold pmFirstPrimeTailMajorant
  split <;> positivity

theorem pmFirstPrimeTailMajorant_le {ε : ℝ} (hε : 2 ≤ ε) (d : ℕ) :
    pmFirstPrimeTailMajorant ε d ≤ 12 * (d : ℝ) ^ (-(2 : ℝ)) := by
  unfold pmFirstPrimeTailMajorant
  split_ifs with hd
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (by omega : 2 ≤ d)
    calc
      3 * (2 / (d : ℝ)) ^ ε ≤ 3 * (2 / (d : ℝ)) ^ (2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge (by positivity)
            ((div_le_one hd0).mpr hd2) hε) (by norm_num)
      _ = 12 * (d : ℝ) ^ (-(2 : ℝ)) := by
        rw [Real.div_rpow (by norm_num) hd0.le, Real.rpow_neg hd0.le]
        norm_num [div_eq_mul_inv]
        ring
  · positivity

theorem summable_pmFirstPrimeTailMajorant {ε : ℝ} (hε : 2 ≤ ε) :
    Summable (pmFirstPrimeTailMajorant ε) := by
  exact Summable.of_nonneg_of_le (pmFirstPrimeTailMajorant_nonneg ε)
    (pmFirstPrimeTailMajorant_le hε)
    ((Real.summable_nat_rpow.mpr (by norm_num : -(2 : ℝ) < -1)).mul_left 12)

theorem tendsto_pmFirstPrimeTailMajorant_tsum :
    Tendsto (fun ε : ℝ => ∑' d, pmFirstPrimeTailMajorant ε d) atTop (𝓝 0) := by
  have hb : Summable (fun d : ℕ => 12 * (d : ℝ) ^ (-(2 : ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(2 : ℝ) < -1)).mul_left 12
  have hlim (d : ℕ) : Tendsto (fun ε : ℝ => pmFirstPrimeTailMajorant ε d) atTop (𝓝 0) := by
    by_cases hd : 3 ≤ d
    · have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hd2 : (2 : ℝ) < d := by exact_mod_cast hd
      simpa [pmFirstPrimeTailMajorant, hd] using
        (tendsto_rpow_atTop_of_base_lt_one (2 / (d : ℝ))
          (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (by positivity))
          ((div_lt_one hd0).mpr hd2)).const_mul 3
    · simp only [pmFirstPrimeTailMajorant, if_neg hd]
      exact tendsto_const_nhds
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hb hlim (by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with ε hε d
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pmFirstPrimeTailMajorant_nonneg ε d)] using
      pmFirstPrimeTailMajorant_le hε d)

theorem pmPowerDampedFermiPrefix_sub_two (ε : ℝ) {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    pmPowerDampedFermiPrefix ε N t - pmPowerDampedFermiPrefix ε 2 t =
      -(∑ d ∈ Finset.Ioc 2 N, (ArithmeticFunction.moebius d : ℂ) *
        (((d : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t) := by
  have heq (K : ℕ) : Finset.Icc 1 K = Finset.Ioc 0 K := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsum := Finset.sum_Ioc_consecutive (fun d => (ArithmeticFunction.moebius d : ℂ) *
    (((d : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t) (by omega : 0 ≤ 2) hN
  simp only [pmPowerDampedFermiPrefix, heq]
  linear_combination hsum

theorem pmPowerDampedFermiPrefix_two (ε t : ℝ) :
    pmPowerDampedFermiPrefix ε 2 t =
      -fermiNymanGen 1 t + (((2 : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen 2 t := by
  rw [pmPowerDampedFermiPrefix, show (2 : ℕ) = 1 + 1 from rfl,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ 1 + 1)]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two, add_comm]

theorem pm_scaled_fermi_term_norm_le (ε : ℝ) {d : ℕ} (hd : 3 ≤ d) :
    eLpNorm (fun t => (ArithmeticFunction.moebius d : ℂ) *
      (((2 / (d : ℝ)) ^ ε : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t)
      2 (volume.restrict (Ioi (0 : ℝ))) ≤ ENNReal.ofReal (pmFirstPrimeTailMajorant ε d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hr : 0 ≤ (2 / (d : ℝ)) ^ ε := Real.rpow_nonneg (by positivity) _
  have hc : ‖(ArithmeticFunction.moebius d : ℂ) * (((2 / (d : ℝ)) ^ ε : ℝ) : ℂ)‖ ≤
      (2 / (d : ℝ)) ^ ε := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    apply mul_le_of_le_one_left hr
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  have hg : eLpNorm (fermiNymanGen (d : ℝ)) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      ENNReal.ofReal 3 := by
    apply (pm_eLpNorm_fermiNymanGen_le hd0).trans
    apply ENNReal.ofReal_le_ofReal
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos (x := (d : ℝ))
      (by exact_mod_cast (by omega : 1 ≤ d)) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    linarith
  change eLpNorm (((ArithmeticFunction.moebius d : ℂ) *
    (((2 / (d : ℝ)) ^ ε : ℝ) : ℂ)) • fermiNymanGen (d : ℝ)) 2 _ ≤ _
  rw [eLpNorm_const_smul, ← ofReal_norm]
  calc
    _ ≤ ENNReal.ofReal ((2 / (d : ℝ)) ^ ε) * ENNReal.ofReal 3 :=
      mul_le_mul (ENNReal.ofReal_le_ofReal hc) hg bot_le bot_le
    _ = _ := by rw [← ENNReal.ofReal_mul hr, pmFirstPrimeTailMajorant, if_pos hd, mul_comm]

def pmScaledFirstPrimeTail (ε t : ℝ) : ℂ :=
  (((2 : ℝ) ^ ε : ℝ) : ℂ) *
    (pmPowerDampedFermiSource ε t - pmPowerDampedFermiPrefix ε 2 t)

theorem pmScaledFirstPrimeTail_eq_sum (ε : ℝ) {t : ℝ} (ht : 0 < t)
    {N : ℕ} (hN : 2 ≤ N) (hcut : ⌊1 / t⌋₊ ≤ N) :
    pmScaledFirstPrimeTail ε t =
      -(∑ d ∈ Finset.Ioc 2 N, (ArithmeticFunction.moebius d : ℂ) *
        (((2 / (d : ℝ)) ^ ε : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t) := by
  have heq : pmPowerDampedFermiSource ε t = pmPowerDampedFermiPrefix ε N t := by
    simpa only [pmPowerDampedFermiPrefix, Complex.ofReal_mul, Complex.ofReal_intCast] using
      pmPowerDampedFermiSource_eq_sum ε ht hcut
  rw [pmScaledFirstPrimeTail, heq, pmPowerDampedFermiPrefix_sub_two ε hN t,
    mul_neg, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  have hp : (2 : ℝ) ^ ε * (d : ℝ) ^ (-ε) = (2 / (d : ℝ)) ^ ε := by
    rw [Real.div_rpow (by norm_num) hd0, Real.rpow_neg hd0, div_eq_mul_inv]
  calc
    _ = (ArithmeticFunction.moebius d : ℂ) *
        ((((2 : ℝ) ^ ε : ℝ) : ℂ) * (((d : ℝ) ^ (-ε) : ℝ) : ℂ)) *
          fermiNymanGen (d : ℝ) t := by ring
    _ = _ := by rw [← Complex.ofReal_mul, hp]

theorem pmScaledFirstPrimeTail_norm_le {ε : ℝ} (hε : 2 ≤ ε) :
    eLpNorm (pmScaledFirstPrimeTail ε) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      ENNReal.ofReal (∑' d, pmFirstPrimeTailMajorant ε d) := by
  let g : ℕ → ℝ → ℂ := fun d t => (ArithmeticFunction.moebius d : ℂ) *
    (((2 / (d : ℝ)) ^ ε : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t
  let f : ℕ → ℝ → ℂ := fun N t => -(∑ d ∈ Finset.Ioc 2 (N + 2), g d t)
  have hgm (d : ℕ) : AEStronglyMeasurable (g d) (volume.restrict (Ioi (0 : ℝ))) :=
    (measurable_const.mul (measurable_fermiNymanGen (d : ℝ))).aestronglyMeasurable
  have hf_eq (N : ℕ) : f N = -(∑ d ∈ Finset.Ioc 2 (N + 2), g d) := by
    funext t
    simp only [f, Finset.sum_apply, Pi.neg_apply]
  have hfm (N : ℕ) : AEStronglyMeasurable (f N) (volume.restrict (Ioi (0 : ℝ))) := by
    rw [hf_eq]
    exact (Finset.aestronglyMeasurable_sum _ (fun d _ => hgm d)).neg
  have hbound (N : ℕ) : eLpNorm (f N) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      ENNReal.ofReal (∑' d, pmFirstPrimeTailMajorant ε d) := by
    rw [hf_eq, eLpNorm_neg]
    apply (eLpNorm_sum_le (f := g) (s := Finset.Ioc 2 (N + 2)) (fun d _ => hgm d)
      (by norm_num : (1 : ENNReal) ≤ 2)).trans
    rw [ENNReal.ofReal_tsum_of_nonneg (pmFirstPrimeTailMajorant_nonneg ε)
      (summable_pmFirstPrimeTailMajorant hε)]
    apply (Finset.sum_le_sum (fun d hd => pm_scaled_fermi_term_norm_le ε
      (by have := (Finset.mem_Ioc.mp hd).1; omega))).trans
    exact ENNReal.sum_le_tsum (Finset.Ioc 2 (N + 2))
  have hlim : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun N => f N t) atTop (𝓝 (pmScaledFirstPrimeTail ε t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ⌊1 / t⌋₊] with N hN
    exact pmScaledFirstPrimeTail_eq_sum ε ht (by omega) (by omega)
  exact Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hbound) hfm hlim

theorem tendsto_pmScaledFirstPrimeTail_eLpNorm :
    Tendsto (fun ε : ℝ => eLpNorm (pmScaledFirstPrimeTail ε) 2
      (volume.restrict (Ioi (0 : ℝ)))) atTop (𝓝 0) := by
  have hupper := ENNReal.tendsto_ofReal tendsto_pmFirstPrimeTailMajorant_tsum
  simp only [ENNReal.ofReal_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with ε hε
  exact pmScaledFirstPrimeTail_norm_le hε

def pmFermiFirstPrimeOverlap : ℝ :=
  ∫ t in Ioi (0 : ℝ), (fermiNymanGen 1 t).re * (fermiNymanGen 2 t).re

theorem pm_fermi_first_prime_overlap_integrable :
    Integrable (fun t => (fermiNymanGen 1 t).re * (fermiNymanGen 2 t).re)
      (volume.restrict (Ioi (0 : ℝ))) := by
  let h1 := memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1)
  let h2 := memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 2)
  have hi := (MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
    (h1.toLp (fermiNymanGen 1)) (h2.toLp (fermiNymanGen 2))).re
  apply hi.congr
  filter_upwards [h1.coeFn_toLp, h2.coeFn_toLp] with t ht1 ht2
  rw [ht1, ht2]
  rcases pm_fermiNymanGen_eq_zero_or_neg_one 1 t with h | h <;>
    rcases pm_fermiNymanGen_eq_zero_or_neg_one 2 t with h' | h' <;> simp [h, h']

theorem pm_fermi_first_prime_inner_re :
    (inner ℂ ((memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1)).toLp (fermiNymanGen 1))
      ((memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 2)).toLp (fermiNymanGen 2))).re =
      pmFermiFirstPrimeOverlap := by
  let h1 := memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1)
  let h2 := memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 2)
  calc
    _ = (∫ t in Ioi (0 : ℝ), inner ℂ (h1.toLp (fermiNymanGen 1) t)
        (h2.toLp (fermiNymanGen 2) t)).re := rfl
    _ = ∫ t in Ioi (0 : ℝ), (inner ℂ (h1.toLp (fermiNymanGen 1) t)
        (h2.toLp (fermiNymanGen 2) t)).re :=
      (integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (h1.toLp _) (h2.toLp _))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [h1.coeFn_toLp, h2.coeFn_toLp] with t ht1 ht2
      rw [ht1, ht2]
      rcases pm_fermiNymanGen_eq_zero_or_neg_one 1 t with h | h <;>
        rcases pm_fermiNymanGen_eq_zero_or_neg_one 2 t with h' | h' <;> simp [h, h']

theorem pm_fermi_first_prime_overlap_band {t : ℝ} (ht : t ∈ Ioc (1 / 4 : ℝ) (1 / 3)) :
    fermiNymanGen 1 t = -1 ∧ fermiNymanGen 2 t = -1 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hf1 : ⌊1 / t⌋ = (3 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    norm_num only
    constructor
    · apply (le_div_iff₀ ht0).mpr
      nlinarith [ht.2]
    · apply (div_lt_iff₀ ht0).mpr
      nlinarith [ht.1]
  have hf2 : ⌊1 / (2 * t)⌋ = (1 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    norm_num only
    constructor
    · apply (le_div_iff₀ (by positivity : 0 < 2 * t)).mpr
      nlinarith [ht.2]
    · apply (div_lt_iff₀ (by positivity : 0 < 2 * t)).mpr
      nlinarith [ht.1]
  constructor
  · rw [fermiNymanGen_eq_floor_difference]
    simp only [div_one, hf1, hf2]
    norm_num
  · exact pm_fermiNymanGen_first_band (by norm_num) ht0 (by nlinarith [ht.1])
      (by nlinarith [ht.2])

theorem pmFermiFirstPrimeOverlap_lower : 1 / 12 ≤ pmFermiFirstPrimeOverlap := by
  have hnonneg (t : ℝ) : 0 ≤ (fermiNymanGen 1 t).re * (fermiNymanGen 2 t).re := by
    rcases pm_fermiNymanGen_eq_zero_or_neg_one 1 t with h | h <;>
      rcases pm_fermiNymanGen_eq_zero_or_neg_one 2 t with h' | h' <;> simp [h, h']
  have hband : (∫ t in Ioc (1 / 4 : ℝ) (1 / 3),
      (fermiNymanGen 1 t).re * (fermiNymanGen 2 t).re) = 1 / 12 := by
    calc
      _ = ∫ _t in Ioc (1 / 4 : ℝ) (1 / 3), (1 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        obtain ⟨h1, h2⟩ := pm_fermi_first_prime_overlap_band ht
        simp [h1, h2]
      _ = _ := by norm_num
  rw [← hband, pmFermiFirstPrimeOverlap]
  exact setIntegral_mono_set pm_fermi_first_prime_overlap_integrable
    (Eventually.of_forall (fun t => hnonneg t))
    (Eventually.of_forall (fun t ht => by
      have h := ht.1
      change (0 : ℝ) < t
      linarith))

theorem pm_hilbert_energy_first_order {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {v : ℝ → E} {f g : E} {r : ℝ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (hr0 : ∀ᶠ ε in atTop, r ε ≠ 0)
    (hq : Tendsto (fun ε => (((r ε)⁻¹ : ℝ) : ℂ) • (v ε - f)) atTop (𝓝 g)) :
    Tendsto (fun ε => (‖v ε‖ ^ 2 - ‖f‖ ^ 2) / r ε) atTop
      (𝓝 (2 * (inner ℂ f g).re)) := by
  let q : ℝ → E := fun ε => (((r ε)⁻¹ : ℝ) : ℂ) • (v ε - f)
  have hinner : Tendsto (fun ε => (inner ℂ f (q ε)).re) atTop
      (𝓝 ((inner ℂ f g).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp (tendsto_const_nhds.inner hq)
  have h := (hinner.const_mul 2).add (hr.mul (hq.norm.pow 2))
  simp only [zero_mul, add_zero] at h
  apply h.congr'
  filter_upwards [hr0] with ε hε
  change 2 * (inner ℂ f (q ε)).re + r ε * ‖q ε‖ ^ 2 =
    (‖v ε‖ ^ 2 - ‖f‖ ^ 2) / r ε
  have hv : v ε = f + (r ε : ℂ) • q ε := by
    dsimp only [q]
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hε, Complex.ofReal_one, one_smul]
    abel
  conv_rhs => rw [hv, norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
  change 2 * (inner ℂ f (q ε)).re + r ε * ‖q ε‖ ^ 2 =
    (‖f‖ ^ 2 + 2 * ((r ε : ℂ) * inner ℂ f (q ε)).re +
      (‖(r ε : ℂ)‖ * ‖q ε‖) ^ 2 - ‖f‖ ^ 2) / r ε
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp [hε]
  ring

theorem tendsto_pmPowerDampedFermiSource_first_energy_correction :
    Tendsto (fun ε : ℝ => (2 : ℝ) ^ ε *
      ((eLpNorm (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))).toReal ^ 2 -
        Real.log 2)) atTop (𝓝 (-2 * pmFermiFirstPrimeOverlap)) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let h1 := memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1)
  let h2 := memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 2)
  let f := h1.toLp (fermiNymanGen 1)
  let g := h2.toLp (fermiNymanGen 2)
  let v (ε : ℝ) : Lp ℂ 2 μ :=
    if hε : 1 / 2 < ε then (memLp_pmPowerDampedFermiSource hε).toLp
      (pmPowerDampedFermiSource ε) else 0
  let q (ε : ℝ) := (((2 : ℝ) ^ ε : ℝ) : ℂ) • (v ε + f)
  have hq : Tendsto q atTop (𝓝 g) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp tendsto_pmScaledFirstPrimeTail_eLpNorm
    simp only [ENNReal.toReal_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with ε hε
    have hs : 1 / 2 < ε := by linarith
    let hf := memLp_pmPowerDampedFermiSource hs
    let hp := memLp_pmPowerDampedFermiPrefix ε 2
    let ht := (hf.sub hp).const_smul ((((2 : ℝ) ^ ε : ℝ) : ℂ))
    have hprefix : hp.toLp (pmPowerDampedFermiPrefix ε 2) =
        -f + ((((2 : ℝ) ^ (-ε) : ℝ) : ℂ)) • g := by
      calc
        _ = (h1.neg.add (h2.const_smul ((((2 : ℝ) ^ (-ε) : ℝ) : ℂ)))).toLp
            (-fermiNymanGen 1 + ((((2 : ℝ) ^ (-ε) : ℝ) : ℂ)) • fermiNymanGen 2) := by
          apply MemLp.toLp_congr
          exact Eventually.of_forall (fun t => pmPowerDampedFermiPrefix_two ε t)
        _ = _ := rfl
    have hpowers : (2 : ℝ) ^ ε * (2 : ℝ) ^ (-ε) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
    have hvec : ht.toLp (pmScaledFirstPrimeTail ε) = q ε - g := by
      change ((((2 : ℝ) ^ ε : ℝ) : ℂ)) •
        (hf.toLp (pmPowerDampedFermiSource ε) - hp.toLp (pmPowerDampedFermiPrefix ε 2)) = _
      rw [hprefix, sub_add_eq_sub_sub, sub_neg_eq_add, smul_sub, smul_smul,
        ← Complex.ofReal_mul, hpowers, Complex.ofReal_one, one_smul]
      simp only [q, v, dif_pos hs]
    rw [← hvec, Lp.norm_toLp]
    rfl
  have hr : Tendsto (fun ε : ℝ => (2 : ℝ) ^ (-ε)) atTop (𝓝 0) := by
    apply (tendsto_rpow_atTop_of_base_lt_one (1 / 2 : ℝ) (by norm_num) (by norm_num)).congr'
    exact Eventually.of_forall (fun ε => by
      dsimp only
      rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2),
        Real.one_rpow, one_div, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)])
  have hq' : Tendsto (fun ε : ℝ => ((((2 : ℝ) ^ (-ε))⁻¹ : ℝ) : ℂ) • (v ε - (-f)))
      atTop (𝓝 g) := by
    simpa only [sub_neg_eq_add, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv] using hq
  have h := pm_hilbert_energy_first_order hr
    (Eventually.of_forall (fun ε : ℝ => (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-ε)).ne')) hq'
  have hseed : ‖f‖ ^ 2 = Real.log 2 := by
    rw [← pm_integral_norm_sq_toLp h1, pm_integral_normSq_fermiNymanGen_one]
  have hinner : 2 * (inner ℂ (-f) g).re = -2 * pmFermiFirstPrimeOverlap := by
    rw [inner_neg_left, Complex.neg_re]
    change 2 * (-(inner ℂ (h1.toLp _) (h2.toLp _)).re) = _
    rw [pm_fermi_first_prime_inner_re]
    ring
  rw [hinner] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with ε hε
  have hs : 1 / 2 < ε := by linarith
  have hvnorm : ‖v ε‖ =
      (eLpNorm (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))).toReal := by
    dsimp only [v]
    split_ifs
    exact Lp.norm_toLp _ _
  rw [hvnorm, norm_neg, hseed,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, inv_inv]
  ring

theorem tendsto_pmPowerDampedFermiSource_energy_atTop :
    Tendsto (fun ε : ℝ =>
      (eLpNorm (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))).toReal ^ 2)
      atTop (𝓝 (Real.log 2)) := by
  have hr : Tendsto (fun ε : ℝ => (2 : ℝ) ^ (-ε)) atTop (𝓝 0) := by
    apply (tendsto_rpow_atTop_of_base_lt_one (1 / 2 : ℝ) (by norm_num) (by norm_num)).congr'
    exact Eventually.of_forall (fun ε => by
      dsimp only
      rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2),
        Real.one_rpow, one_div, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)])
  have h := hr.mul tendsto_pmPowerDampedFermiSource_first_energy_correction
  simp only [zero_mul] at h
  have hdiff : Tendsto (fun ε : ℝ =>
      (eLpNorm (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))).toReal ^ 2 -
        Real.log 2) atTop (𝓝 0) := by
    apply h.congr'
    exact Eventually.of_forall (fun ε => by
      dsimp only
      rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        neg_add_cancel, Real.rpow_zero, one_mul])
  simpa only [sub_add_cancel, zero_add] using hdiff.add_const (Real.log 2)

theorem pmPowerDampedFermiSource_energy_eventually_lt_seed :
    ∀ᶠ ε : ℝ in atTop,
      (eLpNorm (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))).toReal ^ 2 <
        Real.log 2 := by
  have hneg : -2 * pmFermiFirstPrimeOverlap < 0 := by
    nlinarith [pmFermiFirstPrimeOverlap_lower]
  have h := tendsto_pmPowerDampedFermiSource_first_energy_correction.eventually
    (Iio_mem_nhds hneg)
  filter_upwards [h] with ε hε
  change (2 : ℝ) ^ ε * (_ - Real.log 2) < 0 at hε
  by_contra hn
  have hnonneg := mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ε)
    (sub_nonneg.mpr (le_of_not_gt hn))
  exact not_le_of_gt hε hnonneg

/-- Norm-increasing parameter pairs occur beyond every threshold, inside the admitted range. -/
theorem pmPowerDampedFermiSource_exists_large_norm_growth (b : ℝ) :
    ∃ ε η : ℝ, b ≤ ε ∧ 2 ≤ ε ∧ ε ≤ η ∧
      (eLpNorm (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))).toReal <
        (eLpNorm (pmPowerDampedFermiSource η) 2 (volume.restrict (Ioi (0 : ℝ)))).toReal := by
  obtain ⟨ε, hε, hε2, hεb⟩ :=
    (pmPowerDampedFermiSource_energy_eventually_lt_seed.and
      ((eventually_ge_atTop (2 : ℝ)).and (eventually_ge_atTop b))).exists
  have h := tendsto_pmPowerDampedFermiSource_energy_atTop.eventually (Ioi_mem_nhds hε)
  obtain ⟨η, hη, hηε⟩ := (h.and (eventually_ge_atTop ε)).exists
  refine ⟨ε, η, hεb, hε2, hηε, ?_⟩
  change _ ^ 2 < _ ^ 2 at hη
  by_contra hn
  exact not_le_of_gt hη (pow_le_pow_left₀ ENNReal.toReal_nonneg (le_of_not_gt hn) 2)

end RHTower
