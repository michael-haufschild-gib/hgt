import GaloisForLFunctions.RHTower.ChronologicalHeatMellin

/-!
# Harmonic tail charge and exact normalization of heat repair

A bounded finite coefficient array has an algebraic `1/t` tail plus a uniformly
bounded exponential remainder. Integration over a unit interval bounds the tail
charge in terms of the actual full L² error, independently of the cutoff.
Consequently every bounded successful array has vanishing charge.

Adjusting the first coefficient removes that charge exactly. The residual change
is the charge times the Bose defect. For every positive budget increment, a
successful array therefore admits an exactly zero-charge successful normalization
within the enlarged fixed budget.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RHTower
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- The coefficient of the algebraic tail of a finite heat residual. -/
def chronologicalHarmonicCharge (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 N, a k / (k:ℝ)

/-- The exponentially decaying part of the finite Lambert response. -/
def chronologicalBoseSum (a : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 N, a k / (Real.exp ((k:ℝ)*t)-1)

/-- Exact separation of the algebraic tail and the exponential response. -/
theorem chronologicalHeatError_charge_decomposition (a : ℕ → ℝ) (N : ℕ)
    {t : ℝ} (ht : 0 < t) :
    chronologicalHeatError a N t = chronologicalHarmonicCharge a N / t +
      Real.exp (-t) - chronologicalBoseSum a N t := by
  have he : ∑ k ∈ Finset.Ioc 0 N, a k * fusionBoseDefect ((k:ℝ)*t) =
      ∑ k ∈ Finset.Ioc 0 N, (a k/(k:ℝ)/t - a k/(Real.exp ((k:ℝ)*t)-1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : (0:ℝ)<k := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
    rw [fusionBoseDefect, if_pos (mul_pos hk0 ht)]
    simp only [mul_sub, mul_one_div, div_div]
  rw [chronologicalHeatError, he, Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [chronologicalHarmonicCharge, chronologicalBoseSum]
  ring

private theorem geometric_positive_sum_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (N : ℕ) :
    (∑ k ∈ Finset.Ioc 0 N, q^k) ≤ 2*q := by
  have he : (1-q)*(∑ k ∈ Finset.Ioc 0 N, q^k) = q-q^(N+1) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), mul_add, ih, pow_succ]
      ring
  have hp : 0 ≤ ∑ k ∈ Finset.Ioc 0 N, q^k :=
    Finset.sum_nonneg (fun k _ => pow_nonneg hq0 k)
  have hpow := pow_nonneg hq0 (N+1)
  nlinarith

private theorem chronological_exp_neg_le_half {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-t) ≤ 1/2 := by
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0:ℝ)<2)
    (show 2 ≤ Real.exp t by linarith [Real.add_one_le_exp t])

/-- Uniform exponential bound; the constant does not depend on the cutoff. -/
theorem chronologicalBoseSum_uniform_bound (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C)
    {t : ℝ} (ht : 1 ≤ t) :
    |chronologicalBoseSum a N t| ≤ 4*C*Real.exp (-t) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.Ioc 0 N) :
      |a k/(Real.exp ((k:ℝ)*t)-1)| ≤ 2*C*(Real.exp (-t))^k := by
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
    have hkt : 1 ≤ (k:ℝ)*t := by nlinarith
    have he : 2 ≤ Real.exp ((k:ℝ)*t) := by linarith [Real.add_one_le_exp ((k:ℝ)*t)]
    have hden : 0 < Real.exp ((k:ℝ)*t)-1 := by linarith
    have hb : 1/(Real.exp ((k:ℝ)*t)-1) ≤ 2/Real.exp ((k:ℝ)*t) := by
      apply (div_le_div_iff₀ hden (Real.exp_pos _)).mpr
      linarith
    rw [abs_div, abs_of_pos hden]
    calc
      _ ≤ C/(Real.exp ((k:ℝ)*t)-1) := div_le_div_of_nonneg_right (ha k hk) hden.le
      _ ≤ C*(2/Real.exp ((k:ℝ)*t)) := by
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hb hC
      _ = _ := by
        rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_nat_mul]
        rw [show (k:ℝ)*(-t) = -((k:ℝ)*t) by ring]
        ring
  calc
    _ ≤ ∑ k ∈ Finset.Ioc 0 N, |a k/(Real.exp ((k:ℝ)*t)-1)| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ k ∈ Finset.Ioc 0 N, 2*C*(Real.exp (-t))^k := Finset.sum_le_sum hterm
    _ = 2*C*(∑ k ∈ Finset.Ioc 0 N, (Real.exp (-t))^k) := by rw [Finset.mul_sum]
    _ ≤ 2*C*(2*Real.exp (-t)) := mul_le_mul_of_nonneg_left
      (geometric_positive_sum_le (Real.exp_pos _).le (chronological_exp_neg_le_half ht) N) (by positivity)
    _ = _ := by ring

private theorem chronological_unit_interval_abs_integral_le {f : ℝ → ℝ}
    (hf : MemLp f 2 chronologicalPositiveVolume) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Ioc T (T+1), |f t|) ≤ chronologicalL2Norm f := by
  have hsub : Ioc T (T+1) ⊆ Ioi 0 := fun t ht => lt_of_le_of_lt hT ht.1
  have hfm : MemLp f 2 (volume.restrict (Ioc T (T+1))) :=
    hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hg : MemLp (fun _t : ℝ => (1:ℝ)) 2 (volume.restrict (Ioc T (T+1))) := memLp_const 1
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hfm) (by simpa using hg)
  have hc : (∫ t in Ioc T (T+1), |f t|) ≤ Real.sqrt (∫ t in Ioc T (T+1), f t^2) := by
    rw [Real.sqrt_eq_rpow]
    simpa [Real.norm_eq_abs, Real.rpow_two, sq_abs] using hcs
  have hsq : (∫ t in Ioc T (T+1), f t^2) ≤ ∫ t in Ioi (0:ℝ), f t^2 :=
    integral_mono_measure (Measure.restrict_mono hsub le_rfl)
      (Eventually.of_forall (fun t => sq_nonneg _)) hf.integrable_sq
  rw [chronologicalL2Norm_eq_sqrt hf.1]
  exact hc.trans (Real.sqrt_le_sqrt hsq)

/-- A unit-interval measurement bounds the algebraic tail charge, uniformly in N. -/
theorem chronologicalHarmonicCharge_L2_bound (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C)
    {T : ℝ} (hT : 1 ≤ T) :
    |chronologicalHarmonicCharge a N| ≤ (T+1) *
      (chronologicalL2Norm (chronologicalHeatError a N) + (1+4*C)*Real.exp (-T)) := by
  let r := chronologicalHeatError a N
  have hT0 : 0 < T := by linarith
  have hp (t : ℝ) (ht : t ∈ Ioc T (T+1)) :
      |chronologicalHarmonicCharge a N| ≤ (T+1) * (|r t|+(1+4*C)*Real.exp (-T)) := by
    have ht1 : 1 ≤ t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    have hs : chronologicalHarmonicCharge a N =
        t*(r t - Real.exp (-t) + chronologicalBoseSum a N t) := by
      dsimp [r]
      rw [chronologicalHeatError_charge_decomposition a N ht0]
      field_simp
      ring
    have hb := chronologicalBoseSum_uniform_bound a N C hC ha ht1
    have he : Real.exp (-t) ≤ Real.exp (-T) := Real.exp_le_exp.mpr (by linarith [ht.1])
    rw [hs, abs_mul, abs_of_pos ht0]
    have hh := (abs_add_le (r t-Real.exp (-t)) (chronologicalBoseSum a N t)).trans
      (add_le_add (abs_sub (r t) (Real.exp (-t))) le_rfl)
    rw [abs_of_pos (Real.exp_pos _)] at hh
    calc
      _ ≤ t*(|r t|+Real.exp (-t)+|chronologicalBoseSum a N t|) :=
        mul_le_mul_of_nonneg_left hh ht0.le
      _ ≤ (T+1)*(|r t|+(1+4*C)*Real.exp (-T)) := by
        have hh2 : |r t|+Real.exp (-t)+|chronologicalBoseSum a N t| ≤
            |r t|+(1+4*C)*Real.exp (-T) := by nlinarith
        exact (mul_le_mul_of_nonneg_left hh2 ht0.le).trans
          (mul_le_mul_of_nonneg_right ht.2 (by positivity))
  have hr : IntegrableOn (fun t => |r t|) (Ioc T (T+1)) := by
    have hfm := (chronologicalHeatError_memLp a N).mono_measure
      (Measure.restrict_mono (show Ioc T (T+1) ⊆ Ioi 0 from fun t ht => lt_trans hT0 ht.1) le_rfl)
    exact (hfm.integrable (by simp : (1:ENNReal) ≤ 2)).abs
  have hi := setIntegral_mono_on
    (integrableOn_const (C := |chronologicalHarmonicCharge a N|) (hs := measure_Ioc_lt_top.ne))
    ((hr.add (integrableOn_const (C := (1+4*C)*Real.exp (-T)) (hs := measure_Ioc_lt_top.ne))).const_mul (T+1))
    measurableSet_Ioc hp
  have hir : (∫ t in Ioc T (T+1), (T+1)*(|r t|+(1+4*C)*Real.exp (-T))) =
      (T+1)*((∫ t in Ioc T (T+1), |r t|)+(1+4*C)*Real.exp (-T)) := by
    rw [integral_const_mul]
    rw [integral_add hr (integrableOn_const
      (C := (1+4*C)*Real.exp (-T)) (hs := measure_Ioc_lt_top.ne))]
    simp
  change (∫ _t in Ioc T (T+1), |chronologicalHarmonicCharge a N|) ≤
    ∫ t in Ioc T (T+1), (T+1)*(|r t|+(1+4*C)*Real.exp (-T)) at hi
  rw [hir] at hi
  simp at hi
  have hu := chronological_unit_interval_abs_integral_le (chronologicalHeatError_memLp a N) hT0.le
  exact hi.trans (mul_le_mul_of_nonneg_left (add_le_add hu le_rfl) (by linarith))

/-- Every bounded successful heat repair has vanishing harmonic tail charge. -/
theorem chronologicalHarmonicCharge_tendsto_zero (a : ℕ → ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ N k, k ∈ Finset.Ioc 0 N → |a N k| ≤ C)
    (hE : Tendsto (fun N => chronologicalL2Norm (chronologicalHeatError (a N) N))
      atTop (𝓝 0)) :
    Tendsto (fun N => chronologicalHarmonicCharge (a N) N) atTop (𝓝 0) := by
  have hd' : Tendsto (fun T : ℝ => (T*Real.exp (-T)+Real.exp (-T))*(1+4*C))
      atTop (𝓝 0) := by
    simpa only [pow_one, zero_add, zero_mul] using
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).add
        Real.tendsto_exp_neg_atTop_nhds_zero).mul_const (1+4*C)
  have hd : Tendsto (fun T : ℝ => (T+1)*(1+4*C)*Real.exp (-T)) atTop (𝓝 0) := by
    convert hd' using 1
    funext T
    ring
  rw [Metric.tendsto_atTop] at hd hE ⊢
  intro η hη
  obtain ⟨T₀,hT₀⟩ := hd (η/2) (by linarith)
  let T := max 1 T₀
  have hT : 1 ≤ T := le_max_left _ _
  have hTp : 0 < T+1 := by linarith
  have hsmall := hT₀ T (le_max_right _ _)
  rw [Real.dist_eq, sub_zero] at hsmall
  have hs : (T+1)*(1+4*C)*Real.exp (-T) < η/2 :=
    lt_of_le_of_lt (le_abs_self _) hsmall
  obtain ⟨N₀,hN₀⟩ := hE (η/(2*(T+1))) (by positivity)
  refine ⟨N₀, ?_⟩
  intro N hN
  have he := hN₀ N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (chronologicalL2Norm_nonneg _)] at he
  have he' := (lt_div_iff₀ (show 0 < 2*(T+1) by positivity)).mp he
  have hb := chronologicalHarmonicCharge_L2_bound (a N) N C hC (ha N) hT
  rw [Real.dist_eq, sub_zero]
  nlinarith

/-- Remove the algebraic tail by adjusting the first coefficient. -/
def chronologicalZeroChargeRepair (a : ℕ → ℝ) (N k : ℕ) : ℝ :=
  a k - if k=1 then chronologicalHarmonicCharge a N else 0

/-- The normalized finite array has exactly zero harmonic charge. -/
theorem chronologicalZeroChargeRepair_charge (a : ℕ → ℝ) (N : ℕ) :
    chronologicalHarmonicCharge (chronologicalZeroChargeRepair a N) N = 0 := by
  by_cases hN : N=0
  · subst N
    simp [chronologicalHarmonicCharge]
  · have h1 : 1 ∈ Finset.Ioc 0 N := by simp; omega
    simp [chronologicalHarmonicCharge, chronologicalZeroChargeRepair,
      sub_div, Finset.sum_sub_distrib, ite_div, h1]

/-- Exact residual change produced by harmonic normalization. -/
theorem chronologicalZeroChargeRepair_error (a : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    chronologicalHeatError (chronologicalZeroChargeRepair a N) N t =
      chronologicalHeatError a N t - chronologicalHarmonicCharge a N * fusionBoseDefect t := by
  by_cases hN : N=0
  · subst N
    simp [chronologicalHeatError, chronologicalHarmonicCharge]
  · have h1 : 1 ∈ Finset.Ioc 0 N := by simp; omega
    simp [chronologicalHeatError, chronologicalZeroChargeRepair,
      sub_mul, Finset.sum_sub_distrib, ite_mul, h1]
    ring

/-- Exact charge normalization changes the full norm by at most its charge cost. -/
theorem chronologicalZeroChargeRepair_norm_bound (a : ℕ → ℝ) (N : ℕ) :
    chronologicalL2Norm (chronologicalHeatError (chronologicalZeroChargeRepair a N) N) ≤
      chronologicalL2Norm (chronologicalHeatError a N) +
        |chronologicalHarmonicCharge a N| * chronologicalL2Norm fusionBoseDefect := by
  have he : chronologicalHeatError (chronologicalZeroChargeRepair a N) N =
      fun t => chronologicalHeatError a N t - chronologicalHarmonicCharge a N * fusionBoseDefect t := by
    funext t
    exact chronologicalZeroChargeRepair_error a N t
  rw [he]
  have h := lpNorm_sub_le (chronologicalHeatError_memLp a N) (by simp : (1:ENNReal) ≤ 2)
    (g := fun t => chronologicalHarmonicCharge a N * fusionBoseDefect t)
  change chronologicalL2Norm (fun t => chronologicalHeatError a N t -
    chronologicalHarmonicCharge a N * fusionBoseDefect t) ≤
      chronologicalL2Norm (chronologicalHeatError a N) +
        chronologicalL2Norm (fun t => chronologicalHarmonicCharge a N * fusionBoseDefect t) at h
  have hs : chronologicalL2Norm (fun t => chronologicalHarmonicCharge a N * fusionBoseDefect t) =
      |chronologicalHarmonicCharge a N| * chronologicalL2Norm fusionBoseDefect := by
    change lpNorm ((chronologicalHarmonicCharge a N) • fusionBoseDefect) 2 chronologicalPositiveVolume = _
    rw [lpNorm_const_smul]
    simp [Real.norm_eq_abs, chronologicalL2Norm]
  rwa [hs] at h

/-- Harmonic normalization preserves successful bounded-array approximation. -/
theorem chronologicalZeroChargeRepair_tendsto (a : ℕ → ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ N k, k ∈ Finset.Ioc 0 N → |a N k| ≤ C)
    (hE : Tendsto (fun N => chronologicalL2Norm (chronologicalHeatError (a N) N))
      atTop (𝓝 0)) :
    Tendsto (fun N => chronologicalL2Norm
      (chronologicalHeatError (chronologicalZeroChargeRepair (a N) N) N)) atTop (𝓝 0) := by
  have hS := chronologicalHarmonicCharge_tendsto_zero a C hC ha hE
  have hs : Tendsto (fun N => |chronologicalHarmonicCharge (a N) N| *
      chronologicalL2Norm fusionBoseDefect) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, norm_zero, zero_mul] using
      hS.norm.mul_const (chronologicalL2Norm fusionBoseDefect)
  have hh : Tendsto (fun N => chronologicalL2Norm (chronologicalHeatError (a N) N) +
      |chronologicalHarmonicCharge (a N) N| * chronologicalL2Norm fusionBoseDefect)
      atTop (𝓝 0) := by simpa only [zero_add] using hE.add hs
  exact squeeze_zero (fun N => chronologicalL2Norm_nonneg _)
    (fun N => chronologicalZeroChargeRepair_norm_bound (a N) N) hh

/-- Every successful array with budget C admits an exactly zero-charge successful
array with budget C+η for any η>0. The finitely many initial rows can be chosen zero. -/
theorem chronologicalSuccessfulRepair_zeroCharge_normalization
    (a : ℕ → ℕ → ℝ) (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η)
    (ha : ∀ N k, k ∈ Finset.Ioc 0 N → |a N k| ≤ C)
    (hE : Tendsto (fun N => chronologicalL2Norm (chronologicalHeatError (a N) N))
      atTop (𝓝 0)) :
    ∃ b : ℕ → ℕ → ℝ,
      (∀ N k, k ∈ Finset.Ioc 0 N → |b N k| ≤ C+η) ∧
      (∀ N, chronologicalHarmonicCharge (b N) N = 0) ∧
      Tendsto (fun N => chronologicalL2Norm (chronologicalHeatError (b N) N)) atTop (𝓝 0) := by
  have hS := chronologicalHarmonicCharge_tendsto_zero a C hC ha hE
  obtain ⟨N₀,hN₀⟩ := (Metric.tendsto_atTop.mp hS) η hη
  let b : ℕ → ℕ → ℝ := fun N => if N₀ ≤ N then chronologicalZeroChargeRepair (a N) N else fun _ => 0
  refine ⟨b, ?_, ?_, ?_⟩
  · intro N k hk
    by_cases hN : N₀ ≤ N
    · have hs := hN₀ N hN
      rw [Real.dist_eq, sub_zero] at hs
      simp only [b, if_pos hN, chronologicalZeroChargeRepair]
      by_cases hk1 : k=1
      · rw [if_pos hk1]
        have hh := abs_sub (a N k) (chronologicalHarmonicCharge (a N) N)
        have hb := ha N k hk
        linarith
      · rw [if_neg hk1, sub_zero]
        exact (ha N k hk).trans (by linarith)
    · simp only [b, if_neg hN, abs_zero]
      linarith
  · intro N
    dsimp [b]
    split_ifs
    · exact chronologicalZeroChargeRepair_charge _ _
    · simp [chronologicalHarmonicCharge]
  · apply (chronologicalZeroChargeRepair_tendsto a C hC ha hE).congr'
    filter_upwards [eventually_ge_atTop N₀] with N hN
    simp only [b, if_pos hN]

end RHTower
