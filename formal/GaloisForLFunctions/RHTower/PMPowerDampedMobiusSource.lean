import GaloisForLFunctions.RHTower.FermiNymanLogMobiusHead
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.PSeries

/-!
# Literal power-damped Möbius Fermi sources

The generator support makes the arithmetic source a finite sum at each positive
time. Zero damping gives the dyadic Haar target, with pointwise convergence and
an exact Chebyshev first derivative in the damping parameter. Absolute generator
norms and Fatou give canonical `L²(dt)` admission for damping greater than one half.

No admission for arbitrarily small positive damping, canonical norm convergence,
or unconditional Riemann hypothesis is asserted here.
-/

open MeasureTheory Set Filter Topology
open ArithmeticFunction
open scoped ENNReal
noncomputable section
namespace RHTower

def pmPowerDampedFermiSource (ε t : ℝ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 ⌊1 / t⌋₊,
    ((((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ε) : ℝ) : ℂ) *
      fermiNymanGen (d : ℝ) t)

theorem pmPowerDampedFermiSource_zero_parameter (t : ℝ) :
    pmPowerDampedFermiSource 0 t = rawMobiusFermiApprox ⌊1 / t⌋₊ t := by
  simp only [pmPowerDampedFermiSource, neg_zero, Real.rpow_zero, mul_one,
    Complex.ofReal_intCast, rawMobiusFermiApprox]

theorem pmPowerDampedFermiSource_zero_eq_haar {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    pmPowerDampedFermiSource 0 t = dyadicHaar t := by
  rw [pmPowerDampedFermiSource_zero_parameter]
  apply rawMobiusFermiApprox_eq_dyadicHaar _ _ ht.2
  have hN : (0 : ℝ) < (⌊1 / t⌋₊ : ℝ) + 1 := by positivity
  apply (div_lt_iff₀ hN).mpr
  have h := (div_lt_iff₀ ht.1).mp (Nat.lt_floor_add_one (1 / t))
  nlinarith

theorem continuous_pmPowerDampedFermiSource_parameter (t : ℝ) :
    Continuous (fun ε : ℝ => pmPowerDampedFermiSource ε t) := by
  unfold pmPowerDampedFermiSource
  apply Continuous.neg
  apply continuous_finsetSum
  intro d hd
  have hd0 : (0 : ℝ) < d := by
    exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hp : Continuous (fun ε : ℝ => (d : ℝ) ^ (-ε)) :=
    (Real.continuous_const_rpow hd0.ne').comp continuous_neg
  exact (Complex.continuous_ofReal.comp (continuous_const.mul hp)).mul continuous_const

theorem tendsto_pmPowerDampedFermiSource_zero {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    Tendsto (fun ε : ℝ => pmPowerDampedFermiSource ε t) (𝓝[>] 0) (𝓝 (dyadicHaar t)) := by
  rw [← pmPowerDampedFermiSource_zero_eq_haar ht]
  exact (continuous_pmPowerDampedFermiSource_parameter t).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds

theorem pmPowerDampedFermiSource_eq_sum (ε : ℝ) {t : ℝ} (ht : 0 < t)
    {N : ℕ} (hN : ⌊1 / t⌋₊ ≤ N) :
    pmPowerDampedFermiSource ε t =
      -(∑ d ∈ Finset.Icc 1 N,
        ((((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ε) : ℝ) : ℂ) *
          fermiNymanGen (d : ℝ) t) := by
  unfold pmPowerDampedFermiSource
  congr 1
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hN)
  intro d hd hnot
  have hd1 := (Finset.mem_Icc.mp hd).1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hdgt : ⌊1 / t⌋₊ < d := by
    by_contra h
    exact hnot (Finset.mem_Icc.mpr ⟨hd1, le_of_not_gt h⟩)
  have hxd : 1 / t < (d : ℝ) :=
    (Nat.lt_floor_add_one (1 / t)).trans_le (by exact_mod_cast hdgt)
  have hinv : 1 / (d : ℝ) < t := by
    apply (div_lt_iff₀ hd0).mpr
    have h := (div_lt_iff₀ ht).mp hxd
    nlinarith
  rw [fermiNymanGen_eq_zero_of_inv_lt hd0 hinv, mul_zero]

theorem pm_moebius_log_fermi_sum {t : ℝ} (ht : 0 < t) :
    (∑ d ∈ Finset.Icc 1 ⌊1 / t⌋₊,
      ((moebius d : ℤ) : ℂ) * (Real.log (d : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t) =
        ((Chebyshev.psi (1 / t) - 2 * Chebyshev.psi (1 / (2 * t)) : ℝ) : ℂ) := by
  have hhalf : ⌊1 / (2 * t)⌋₊ ≤ ⌊1 / t⌋₊ :=
    Nat.floor_mono (one_div_le_one_div_of_le ht (by linarith))
  have hF := sum_moebius_log_mul_floor ⌊1 / t⌋₊ (by positivity : 0 ≤ 1 / t) le_rfl
  have hH := sum_moebius_log_mul_floor ⌊1 / t⌋₊ (by positivity : 0 ≤ 1 / (2 * t)) hhalf
  have hreal : (∑ d ∈ Finset.Icc 1 ⌊1 / t⌋₊,
      ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) *
        (2 * (⌊(1 / (2 * t)) / d⌋ : ℝ) - (⌊(1 / t) / d⌋ : ℝ))) =
      Chebyshev.psi (1 / t) - 2 * Chebyshev.psi (1 / (2 * t)) := by
    calc
      _ = 2 * (∑ d ∈ Finset.Icc 1 ⌊1 / t⌋₊,
          ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * (⌊(1 / (2 * t)) / d⌋ : ℝ)) -
        (∑ d ∈ Finset.Icc 1 ⌊1 / t⌋₊,
          ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ) * (⌊(1 / t) / d⌋ : ℝ)) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro d hd
            ring
      _ = _ := by rw [hF, hH]; ring
  simp_rw [fermiNymanGen_eq_floor_difference]
  exact_mod_cast hreal

theorem hasDerivAt_pmPowerDampedFermiSource_zero {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun ε : ℝ => pmPowerDampedFermiSource ε t)
      ((Chebyshev.psi (1 / t) - 2 * Chebyshev.psi (1 / (2 * t)) : ℝ) : ℂ) 0 := by
  have hterm : ∀ d ∈ Finset.Icc 1 ⌊1 / t⌋₊,
      HasDerivAt (fun ε : ℝ =>
        ((((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t)
        (((((moebius d : ℤ) : ℝ) * (-Real.log (d : ℝ)) : ℝ) : ℂ) *
          fermiNymanGen (d : ℝ) t) 0 := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hr : HasDerivAt (fun ε : ℝ => (d : ℝ) ^ (-ε)) (-Real.log (d : ℝ)) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).neg.const_rpow hd0
    exact ((hr.const_mul ((moebius d : ℤ) : ℝ)).ofReal_comp).mul_const _
  have h := (HasDerivAt.fun_sum hterm).neg
  have heq : -(∑ d ∈ Finset.Icc 1 ⌊1 / t⌋₊,
      (((((moebius d : ℤ) : ℝ) * (-Real.log (d : ℝ)) : ℝ) : ℂ) *
        fermiNymanGen (d : ℝ) t)) =
      ((Chebyshev.psi (1 / t) - 2 * Chebyshev.psi (1 / (2 * t)) : ℝ) : ℂ) := by
    rw [← pm_moebius_log_fermi_sum ht, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    push_cast
    ring
  rw [heq] at h
  exact h

private theorem pm_measurable_nat_choice {f : ℕ → ℝ → ℂ}
    (hf : ∀ N, Measurable (f N)) {n : ℝ → ℕ} (hn : Measurable n) :
    Measurable (fun t => f (n t) t) :=
  (measurable_from_prod_countable_right (f := fun p : ℕ × ℝ => f p.1 p.2) hf).comp
    (hn.prodMk measurable_id)

theorem measurable_pmPowerDampedFermiSource (ε : ℝ) :
    Measurable (pmPowerDampedFermiSource ε) := by
  apply pm_measurable_nat_choice (f := fun N t =>
    -(∑ d ∈ Finset.Icc 1 N,
      ((((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t))
  · intro N
    apply Measurable.neg
    exact Finset.measurable_sum (Finset.Icc 1 N) (fun d _ =>
      (measurable_const : Measurable (fun _ : ℝ =>
        ((((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ε) : ℝ) : ℂ))).mul
          (measurable_fermiNymanGen (d : ℝ)))
  · exact ((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).div measurable_id).nat_floor

theorem pmPowerDampedFermiSource_eq_zero_of_one_lt (ε : ℝ) {t : ℝ} (ht : 1 < t) :
    pmPowerDampedFermiSource ε t = 0 := by
  have h : ⌊1 / t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by
    exact (div_lt_one (by linarith)).mpr ht)
  unfold pmPowerDampedFermiSource
  rw [h]
  simp

theorem pm_eLpNorm_fermiNymanGen_le {a : ℝ} (ha : 0 < a) :
    eLpNorm (fermiNymanGen a) 2 (volume.restrict (Ioi 0)) ≤
      ENNReal.ofReal (3 * a ^ (-(1 / 2 : ℝ))) := by
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ‖fermiNymanGen a t‖ ≤ ‖(Ioc (0 : ℝ) (1 / a)).indicator (fun _ => (3 : ℝ)) t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    by_cases hta : t ≤ 1 / a
    · simp only [Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) (1 / a) from ⟨ht, hta⟩)]
      simpa using norm_fermiNymanGen_le a t
    · rw [fermiNymanGen_eq_zero_of_inv_lt ha (lt_of_not_ge hta)]
      simp only [norm_zero]
      exact norm_nonneg _
  refine (eLpNorm_mono_ae hbound).trans_eq ?_
  rw [eLpNorm_indicator_const measurableSet_Ioc (by norm_num) (by norm_num),
    Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc (0 : ℝ) (1 / a) ⊆ Ioi 0 from fun _ h => h.1),
    Real.volume_Ioc]
  norm_num only [sub_zero, ENNReal.toReal_ofNat]
  rw [ENNReal.ofReal_rpow_of_pos (by positivity : 0 < 1 / a)]
  have h3 : ‖(3 : ℝ)‖ₑ = ENNReal.ofReal 3 := by rw [← ofReal_norm]; norm_num
  rw [h3,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  rw [one_div, Real.inv_rpow ha.le, Real.rpow_neg ha.le]

theorem pm_eLpNorm_power_damped_term_le (ε : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    eLpNorm (fun t =>
        ((((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t)
      2 (volume.restrict (Ioi 0)) ≤
        ENNReal.ofReal (3 * (d : ℝ) ^ (-ε - 1 / 2)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : ‖((((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ε) : ℝ) : ℂ)‖ ≤
      (d : ℝ) ^ (-ε) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hd0.le _)]
    apply mul_le_of_le_one_left (Real.rpow_nonneg hd0.le _)
    exact_mod_cast (abs_moebius_le_one (n := d))
  let c : ℝ := ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ε)
  change eLpNorm ((c : ℂ) • fermiNymanGen (d : ℝ)) 2 (volume.restrict (Ioi 0)) ≤ _
  rw [eLpNorm_const_smul, ← ofReal_norm]
  calc
    _ ≤ ENNReal.ofReal ((d : ℝ) ^ (-ε)) *
        ENNReal.ofReal (3 * (d : ℝ) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul (ENNReal.ofReal_le_ofReal hc) (pm_eLpNorm_fermiNymanGen_le hd0)
        bot_le bot_le
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd0.le _)]
      congr 1
      rw [mul_left_comm, ← Real.rpow_add hd0]
      congr 2

theorem memLp_pmPowerDampedFermiSource {ε : ℝ} (hε : 1 / 2 < ε) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi 0)) := by
  let g : ℕ → ℝ → ℂ := fun d t =>
    ((((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t
  let f : ℕ → ℝ → ℂ := fun N t => -(∑ d ∈ Finset.Icc 1 N, g d t)
  let B : ℕ → ℝ := fun d => 3 * (d : ℝ) ^ (-ε - 1 / 2)
  have hB : Summable B :=
    (Real.summable_nat_rpow.mpr (by linarith : -ε - 1 / 2 < -1)).mul_left 3
  have hB0 (d : ℕ) : 0 ≤ B d := by dsimp [B]; positivity
  have hgm (d : ℕ) : AEStronglyMeasurable (g d) (volume.restrict (Ioi 0)) :=
    (measurable_const.mul (measurable_fermiNymanGen (d : ℝ))).aestronglyMeasurable
  have hf_eq (N : ℕ) : f N = -(∑ d ∈ Finset.Icc 1 N, g d) := by
    funext t
    simp only [f, Finset.sum_apply, Pi.neg_apply]
  have hm (N : ℕ) : AEStronglyMeasurable (f N) (volume.restrict (Ioi 0)) := by
    rw [hf_eq]
    exact (Finset.aestronglyMeasurable_sum (Finset.Icc 1 N) (fun d _ => hgm d)).neg
  have hbound (N : ℕ) : eLpNorm (f N) 2 (volume.restrict (Ioi 0)) ≤
      ∑' d, ENNReal.ofReal (B d) := by
    rw [hf_eq, eLpNorm_neg]
    refine (eLpNorm_sum_le (f := g) (s := Finset.Icc 1 N) (fun d _ => hgm d)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans ?_
    exact (Finset.sum_le_sum (fun d hd =>
      pm_eLpNorm_power_damped_term_le ε (Finset.mem_Icc.mp hd).1)).trans
        (ENNReal.sum_le_tsum (Finset.Icc 1 N))
  have hlim : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun N => f N t) atTop (𝓝 (pmPowerDampedFermiSource ε t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ⌊1 / t⌋₊] with N hN
    exact pmPowerDampedFermiSource_eq_sum ε ht hN
  refine ⟨(measurable_pmPowerDampedFermiSource ε).aestronglyMeasurable, ?_⟩
  apply lt_of_le_of_lt (Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbound) hm hlim)
  rw [← ENNReal.ofReal_tsum_of_nonneg hB0 hB]
  exact ENNReal.ofReal_lt_top

end RHTower
