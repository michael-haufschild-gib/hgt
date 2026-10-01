import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrefixEnergy
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Unconditional canonical admission for the literal power-damped Möbius Fermi source
at and above damping one half. Finite Abel summation uses arbitrary logarithmic
savings for raw-prefix energy; Fatou transfers the uniform prefix bound to the
literal source. Admission at arbitrarily small positive damping remains open. -/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

-- This norm is real-valued only after the explicit admission theorem has been established.
theorem pm_rawMobiusFermiApprox_lpNorm_sq (N : ℕ) :
    lpNorm (rawMobiusFermiApprox N) 2 (volume.restrict (Ioi 0)) ^ 2 =
      ∫ t in Ioi (0 : ℝ), ‖rawMobiusFermiApprox N t‖ ^ 2 := by
  rw [pm_integral_norm_sq_toLp (memLp_rawMobiusFermiApprox N), Lp.norm_toLp,
    toReal_eLpNorm (memLp_rawMobiusFermiApprox N).aestronglyMeasurable]

theorem pm_rawMobiusFermiApprox_normalized_norm_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      lpNorm (rawMobiusFermiApprox N) 2 (volume.restrict (Ioi 0)) / Real.sqrt (N : ℝ) ≤
        C / Real.log (N : ℝ) ^ 2 := by
  obtain ⟨B, hB, hrate⟩ := pm_rawMobiusFermiApprox_energy_log_saving 3
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hrate, hlog.eventually_ge_atTop 1, eventually_ge_atTop 1] with N hN hLN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hL : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hLN
  have hN' : lpNorm (rawMobiusFermiApprox N) 2 (volume.restrict (Ioi 0)) ^ 2 ≤
      B * (N : ℝ) / Real.log (N : ℝ) ^ 4 := by
    rw [pm_rawMobiusFermiApprox_lpNorm_sq]
    exact hN
  have hb := Real.sq_sqrt hB
  have hn := Real.sq_sqrt hN0.le
  have hsbound : (lpNorm (rawMobiusFermiApprox N) 2 (volume.restrict (Ioi 0)) /
      Real.sqrt (N : ℝ)) ^ 2 ≤ (Real.sqrt B / Real.log (N : ℝ) ^ 2) ^ 2 := by
    rw [div_pow, div_pow, hb, hn]
    have h := div_le_div_of_nonneg_right hN' hN0.le
    calc
      _ ≤ (B * (N : ℝ) / Real.log (N : ℝ) ^ 4) / (N : ℝ) := h
      _ = _ := by field_simp [hN0.ne']
  have hleft : 0 ≤ lpNorm (rawMobiusFermiApprox N) 2 (volume.restrict (Ioi 0)) /
      Real.sqrt (N : ℝ) := div_nonneg lpNorm_nonneg hsN.le
  have hright : 0 ≤ Real.sqrt B / Real.log (N : ℝ) ^ 2 := by positivity
  nlinarith

def pmPowerDampedFermiPrefix (ε : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
    (((d : ℝ) ^ (-ε) : ℝ) : ℂ) * fermiNymanGen (d : ℝ) t)

theorem pmPowerDampedFermiPrefix_abel (ε : ℝ) (N : ℕ) (t : ℝ) :
    pmPowerDampedFermiPrefix ε (N + 1) t =
      ((((N + 1 : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) * rawMobiusFermiApprox (N + 1) t +
        ∑ n ∈ Finset.Icc 1 N,
          (((((n : ℝ) ^ (-ε) - ((n + 1 : ℕ) : ℝ) ^ (-ε)) : ℝ) : ℂ)) *
            rawMobiusFermiApprox n t := by
  have hraw (n : ℕ) : rawMobiusFermiApprox (n + 1) t =
      rawMobiusFermiApprox n t - (ArithmeticFunction.moebius (n + 1) : ℂ) *
        fermiNymanGen ((n + 1 : ℕ) : ℝ) t := by
    rw [rawMobiusFermiApprox, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    unfold rawMobiusFermiApprox
    ring
  have hprefix (n : ℕ) : pmPowerDampedFermiPrefix ε (n + 1) t =
      pmPowerDampedFermiPrefix ε n t - (ArithmeticFunction.moebius (n + 1) : ℂ) *
        (((((n + 1 : ℕ) : ℝ) ^ (-ε)) : ℝ) : ℂ) *
          fermiNymanGen ((n + 1 : ℕ) : ℝ) t := by
    rw [pmPowerDampedFermiPrefix, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    unfold pmPowerDampedFermiPrefix
    ring
  induction N with
  | zero => simp [pmPowerDampedFermiPrefix, rawMobiusFermiApprox]
  | succ N ih =>
    rw [hprefix (N + 1), ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1),
      hraw (N + 1)]
    push_cast
    ring

theorem tendsto_pm_rawMobiusFermiApprox_normalized_norm_zero :
    Tendsto (fun N : ℕ => lpNorm (rawMobiusFermiApprox N) 2 (volume.restrict (Ioi 0)) /
      Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := pm_rawMobiusFermiApprox_normalized_norm_log_bound
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => 1 / Real.log (N : ℝ)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div_atTop hlog)
  have hmajor : Tendsto (fun N : ℕ => C / Real.log (N : ℝ) ^ 2) atTop (𝓝 0) := by
    convert (hinv.pow 2).const_mul C using 1 <;> simp [div_eq_mul_inv, pow_two]
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg lpNorm_nonneg (Real.sqrt_nonneg _)) hbound hmajor

theorem pm_summable_reciprocal_log_sq :
    Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2)) := by
  let K : ℕ := ⌈Real.exp 1⌉₊
  have hK : Real.exp 1 ≤ (K : ℝ) := Nat.le_ceil _
  have h := GaloisForLFunctions.HTGeometry.summable_one_div_mul_log_pow_succ
    (p := 1) (by norm_num) hK
  apply (summable_nat_add_iff (K + 1)).mp
  have heq : (fun n : ℕ => 1 / (((n + (K + 1) : ℕ) : ℝ) *
      Real.log ((n + (K + 1) : ℕ) : ℝ) ^ 2)) =
      (fun i : ℕ => 1 / (((K : ℝ) + (i + 1)) *
        Real.log ((K : ℝ) + (i + 1)) ^ (1 + 1))) := by
    funext n
    have harg : ((n + (K + 1) : ℕ) : ℝ) = (K : ℝ) + ((n : ℝ) + 1) := by
      push_cast
      ring
    rw [harg]
  rw [heq]
  exact h

theorem pm_half_damping_gap_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) - ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  apply sub_nonneg.mpr
  apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn)
  · exact_mod_cast Nat.le_succ n
  · norm_num

theorem pm_half_damping_gap_norm_summable :
    Summable (fun n : ℕ =>
      ((n : ℝ) ^ (-(1 / 2 : ℝ)) - ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
        lpNorm (rawMobiusFermiApprox n) 2 (volume.restrict (Ioi 0))) := by
  obtain ⟨C, hC, hbound⟩ := pm_rawMobiusFermiApprox_normalized_norm_log_bound
  apply (pm_summable_reciprocal_log_sq.mul_left (C / 2)).of_norm_bounded_eventually_nat
  filter_upwards [hbound, eventually_ge_atTop 1] with n hnBound hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hgap := pm_half_damping_gap_nonneg hn
  have hdiff : (n : ℝ) ^ (-(1 / 2 : ℝ)) - ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ) - 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      GaloisForLFunctions.RHTower.rpow_sub_rpow_succ_le (by norm_num : (0 : ℝ) < 1 / 2) hn0
  have hpow : (n : ℝ) ^ (-(1 / 2 : ℝ) - 1) * Real.sqrt (n : ℝ) = 1 / (n : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
    norm_num [Real.rpow_neg_one]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgap lpNorm_nonneg)]
  calc
    _ ≤ ((1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ) - 1)) *
        lpNorm (rawMobiusFermiApprox n) 2 (volume.restrict (Ioi 0)) :=
      mul_le_mul_of_nonneg_right hdiff lpNorm_nonneg
    _ = (1 / (2 * (n : ℝ))) *
        (lpNorm (rawMobiusFermiApprox n) 2 (volume.restrict (Ioi 0)) / Real.sqrt (n : ℝ)) := by
      have hp := (eq_div_iff hsqrt.ne').mpr hpow
      rw [hp]
      ring
    _ ≤ (1 / (2 * (n : ℝ))) * (C / Real.log (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hnBound (by positivity)
    _ = _ := by ring

theorem memLp_pmPowerDampedFermiPrefix (ε : ℝ) (N : ℕ) :
    MemLp (pmPowerDampedFermiPrefix ε N) 2 (volume.restrict (Ioi 0)) := by
  let c : ℕ → ℂ := fun d => (ArithmeticFunction.moebius d : ℂ) *
    (((d : ℝ) ^ (-ε) : ℝ) : ℂ)
  have h := memLp_finsetSum (Finset.Icc 1 N) (f := fun d =>
    fun t : ℝ => c d * fermiNymanGen (d : ℝ) t) (fun d hd =>
      (memLp_pm_fermiNymanGen (by exact_mod_cast (Finset.mem_Icc.mp hd).1)).const_mul (c d))
  exact h.neg

theorem pm_half_damping_prefix_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      eLpNorm (pmPowerDampedFermiPrefix (1 / 2) (N + 1)) 2
        (volume.restrict (Ioi 0)) ≤ ENNReal.ofReal C := by
  let w : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))
  let g : ℕ → ℝ := fun n => (w n - w (n + 1)) *
    lpNorm (rawMobiusFermiApprox n) 2 (volume.restrict (Ioi 0))
  have hg : Summable g := pm_half_damping_gap_norm_summable
  have hg0 (n : ℕ) : 0 ≤ g n := by
    cases n with
    | zero =>
      have hz : rawMobiusFermiApprox 0 = (0 : ℝ → ℂ) := by
        funext t
        simp [rawMobiusFermiApprox]
      dsimp only [g]
      rw [hz, lpNorm_zero, mul_zero]
    | succ n => exact mul_nonneg (pm_half_damping_gap_nonneg (by omega)) lpNorm_nonneg
  obtain ⟨B, hB⟩ := deningerBounded_of_tendsto tendsto_pm_rawMobiusFermiApprox_normalized_norm_zero
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine ⟨B + ∑' n, g n, add_nonneg hB0 (tsum_nonneg hg0), ?_⟩
  intro N
  let F : ℕ → ℝ → ℂ := fun n => ((w n - w (n + 1) : ℝ) : ℂ) • rawMobiusFermiApprox n
  have hF (n : ℕ) : MemLp (F n) 2 (volume.restrict (Ioi 0)) :=
    (memLp_rawMobiusFermiApprox n).const_smul _
  have heq : pmPowerDampedFermiPrefix (1 / 2) (N + 1) =
      (w (N + 1) : ℂ) • rawMobiusFermiApprox (N + 1) + ∑ n ∈ Finset.Icc 1 N, F n := by
    funext t
    simpa [F, w, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      pmPowerDampedFermiPrefix_abel (1 / 2) N t
  rw [← ofReal_lpNorm (memLp_pmPowerDampedFermiPrefix (1 / 2) (N + 1))]
  apply ENNReal.ofReal_le_ofReal
  rw [heq]
  have htri := lpNorm_add_le
    ((memLp_rawMobiusFermiApprox (N + 1)).const_smul (w (N + 1) : ℂ))
      (g := ∑ n ∈ Finset.Icc 1 N, F n) (by norm_num : (1 : ENNReal) ≤ 2)
  have hsum := lpNorm_sum_le (f := F) (s := Finset.Icc 1 N) (fun n _ => hF n)
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hnorm (n : ℕ) (hn : 1 ≤ n) :
      lpNorm (F n) 2 (volume.restrict (Ioi 0)) = g n := by
    dsimp only [F, g]
    rw [lpNorm_const_smul]
    simp only [coe_nnnorm, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (pm_half_damping_gap_nonneg hn)]
  have hsum' : lpNorm (∑ n ∈ Finset.Icc 1 N, F n) 2 (volume.restrict (Ioi 0)) ≤ ∑' n, g n := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N, lpNorm (F n) 2 (volume.restrict (Ioi 0)) := hsum
      _ = ∑ n ∈ Finset.Icc 1 N, g n := Finset.sum_congr rfl fun n hn => hnorm n (Finset.mem_Icc.mp hn).1
      _ ≤ _ := hg.sum_le_tsum _ (fun n _ => hg0 n)
  have hfirst : lpNorm ((w (N + 1) : ℂ) • rawMobiusFermiApprox (N + 1)) 2
      (volume.restrict (Ioi 0)) ≤ B := by
    rw [lpNorm_const_smul]
    simp only [coe_nnnorm, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    have hw : w (N + 1) = (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ := by
      dsimp only [w]
      rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow]
    dsimp only [w] at hw
    rw [hw]
    have hb := hB (N + 1)
    rw [abs_of_nonneg (div_nonneg lpNorm_nonneg (Real.sqrt_nonneg _))] at hb
    simpa only [div_eq_mul_inv, mul_comm] using hb
  exact htri.trans (add_le_add hfirst hsum')

theorem memLp_pmPowerDampedFermiSource_half :
    MemLp (pmPowerDampedFermiSource (1 / 2)) 2 (volume.restrict (Ioi 0)) := by
  obtain ⟨C, hC, hbound⟩ := pm_half_damping_prefix_uniform_bound
  refine ⟨(measurable_pmPowerDampedFermiSource (1 / 2)).aestronglyMeasurable, ?_⟩
  have hlim : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun N : ℕ => pmPowerDampedFermiPrefix (1 / 2) (N + 1) t) atTop
        (𝓝 (pmPowerDampedFermiSource (1 / 2) t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ⌊1 / t⌋₊] with N hN
    simpa only [pmPowerDampedFermiPrefix, Complex.ofReal_mul, Complex.ofReal_intCast] using
      pmPowerDampedFermiSource_eq_sum (1 / 2) ht (hN.trans (Nat.le_succ N))
  have hnorm := Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hbound)
    (fun N => (memLp_pmPowerDampedFermiPrefix (1 / 2) (N + 1)).aestronglyMeasurable) hlim
  exact hnorm.trans_lt ENNReal.ofReal_lt_top

theorem memLp_pmPowerDampedFermiSource_of_half_le {ε : ℝ} (hε : 1 / 2 ≤ ε) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi 0)) := by
  rcases eq_or_lt_of_le hε with h | h
  · rw [← h]
    exact memLp_pmPowerDampedFermiSource_half
  · exact memLp_pmPowerDampedFermiSource h

end RHTower
