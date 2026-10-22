import GaloisForLFunctions.RHTower.Suzuki.SuzukiOriginRemainderRegularity
import GaloisForLFunctions.HTGeometry.BanachIntervalIntegralAbsoluteContinuity
import GaloisForLFunctions.HTGeometry.LogKernelExteriorL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

theorem lipschitzOnWith_absolutelyContinuousOnInterval
    {f : ℝ → ℝ} {K : NNReal} {a b : ℝ}
    (hfK : LipschitzOnWith K f (uIcc a b)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨ε / (K + 1), by positivity, fun (n, I) hnI₁ hnI₂ ↦ ?_⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n, K * dist (I i).1 (I i).2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := hfK (hnI₁.left i hi).left (hnI₁.left i hi).right
      apply ENNReal.toReal_mono (Ne.symm (not_eq_of_beq_eq_false rfl)) at h
      rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist] at h
    _ = K * ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 := by
      symm
      exact Finset.mul_sum _ _ _
    _ ≤ K * (ε / (K + 1)) := by gcongr
    _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
    _ = ε := by field

theorem absolutelyContinuousOnInterval_congr_on
    {f g : ℝ → ℝ} {a b : ℝ}
    (hfg : Set.EqOn f g (uIcc a b))
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [AbsolutelyContinuousOnInterval] at hg ⊢
  apply hg.congr'
  have hevent : ∀ᶠ E : ℕ × (ℕ → ℝ × ℝ) in
      AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hevent] with E hE
  obtain ⟨hpoints, -⟩ := hE
  apply Finset.sum_congr rfl
  intro i hi
  have hp := hpoints i hi
  rw [hfg hp.1, hfg hp.2]

/-- The weak first derivative of the universal logarithmic cusp `|t| log |t|`. -/
def logarithmicCuspDerivative (t : ℝ) : ℝ :=
  (SignType.sign t : ℝ) * (Real.log t + 1)

@[simp] theorem logarithmicCuspDerivative_zero :
    logarithmicCuspDerivative 0 = 0 := by
  simp [logarithmicCuspDerivative]

theorem logarithmicCuspDerivative_neg (t : ℝ) :
    logarithmicCuspDerivative (-t) = -logarithmicCuspDerivative t := by
  simp only [logarithmicCuspDerivative, Real.log_neg_eq_log, Left.sign_neg, SignType.coe_neg]
  ring

theorem intervalIntegrable_logarithmicCuspDerivative (a b : ℝ) :
    IntervalIntegrable logarithmicCuspDerivative volume a b := by
  have hbase : IntervalIntegrable (fun t : ℝ => Real.log t + 1) volume a b :=
    (intervalIntegral.intervalIntegrable_log' (a := a) (b := b)).add intervalIntegrable_const
  apply hbase.mono_fun
  · have hsign : Measurable (fun t : ℝ => (SignType.sign t : ℝ)) := by
      have h : Measurable (fun t : ℝ =>
          if 0 < t then (1 : ℝ) else if t < 0 then (-1 : ℝ) else 0) :=
        Measurable.ite measurableSet_Ioi measurable_const
          (Measurable.ite measurableSet_Iio measurable_const measurable_const)
      convert h using 1
      funext t
      rw [sign_apply]
      split_ifs <;> simp
    exact (hsign.mul (Real.measurable_log.add measurable_const)).aestronglyMeasurable.restrict
  · filter_upwards with t
    rw [logarithmicCuspDerivative, norm_mul]
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · rw [sign_neg ht, SignType.coe_neg_one]
      norm_num
    · simp
    · rw [sign_pos ht, SignType.coe_one]
      norm_num

theorem integral_logarithmicCuspDerivative_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, logarithmicCuspDerivative s) = t * Real.log t := by
  calc
    (∫ s in (0 : ℝ)..t, logarithmicCuspDerivative s) =
        ∫ s in (0 : ℝ)..t, (Real.log s + 1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with s
      intro hs
      rw [uIoc_of_le ht] at hs
      have hspos : 0 < s := hs.1
      rw [logarithmicCuspDerivative, sign_pos hspos, SignType.coe_one]
      simp
    _ = (∫ s in (0 : ℝ)..t, Real.log s) + ∫ _ in (0 : ℝ)..t, (1 : ℝ) := by
      rw [intervalIntegral.integral_add
        (intervalIntegral.intervalIntegrable_log' (a := 0) (b := t))
        intervalIntegrable_const]
    _ = t * Real.log t := by
      rw [integral_log, integral_one]
      simp

theorem integral_logarithmicCuspDerivative (t : ℝ) :
    (∫ s in (0 : ℝ)..t, logarithmicCuspDerivative s) = |t| * Real.log |t| := by
  rcases le_total 0 t with ht | ht
  · rw [integral_logarithmicCuspDerivative_of_nonneg ht, abs_of_nonneg ht]
  · have hnt : 0 ≤ -t := neg_nonneg.mpr ht
    calc
      (∫ s in (0 : ℝ)..t, logarithmicCuspDerivative s) =
          -(∫ s in t..(0 : ℝ), logarithmicCuspDerivative s) := by
        rw [intervalIntegral.integral_symm]
      _ = -(∫ s in (0 : ℝ)..(-t), logarithmicCuspDerivative (-s)) := by
        rw [intervalIntegral.integral_comp_neg]
        simp
      _ = ∫ s in (0 : ℝ)..(-t), logarithmicCuspDerivative s := by
        rw [show (fun s : ℝ => logarithmicCuspDerivative (-s)) =
            fun s => -logarithmicCuspDerivative s by
          funext s
          exact logarithmicCuspDerivative_neg s]
        rw [intervalIntegral.integral_neg]
        ring
      _ = (-t) * Real.log (-t) :=
        integral_logarithmicCuspDerivative_of_nonneg hnt
      _ = |t| * Real.log |t| := by
        rw [abs_of_nonpos ht]

theorem absolutelyContinuousOnInterval_logarithmicCusp (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => |t| * Real.log |t|) a b := by
  let F : ℝ → ℝ := fun t => |a| * Real.log |a| +
    ∫ s in a..t, logarithmicCuspDerivative s
  have hconst : LipschitzOnWith 0 (fun _ : ℝ => |a| * Real.log |a|) (uIcc a b) :=
    (LipschitzWith.const (|a| * Real.log |a|)).lipschitzOnWith
  have hF : AbsolutelyContinuousOnInterval F a b :=
    (lipschitzOnWith_absolutelyContinuousOnInterval hconst).add
      (IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normed
        (intervalIntegrable_logarithmicCuspDerivative a b) left_mem_uIcc)
  apply absolutelyContinuousOnInterval_congr_on (g := F) (hg := hF)
  intro t ht
  dsimp only [F]
  rw [← integral_logarithmicCuspDerivative a,
    ← integral_logarithmicCuspDerivative t]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_logarithmicCuspDerivative 0 a)
    (intervalIntegrable_logarithmicCuspDerivative a t)).symm

theorem contDiffOn_one_absolutelyContinuousOnInterval
    {f : ℝ → ℝ} {a b : ℝ} (hf : ContDiffOn ℝ 1 f (uIcc a b)) :
    AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by norm_num)
    (by simpa [uIcc] using convex_Icc (min a b) (max a b))
    (by simpa [uIcc] using isCompact_Icc : IsCompact (uIcc a b))
  exact lipschitzOnWith_absolutelyContinuousOnInterval hK

theorem absolutelyContinuousOnInterval_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun x => ∑ i ∈ s, f i x) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero : LipschitzOnWith 0 (fun _ : ℝ => (0 : ℝ)) (uIcc a b) :=
        (LipschitzWith.const (0 : ℝ)).lipschitzOnWith
      simpa using lipschitzOnWith_absolutelyContinuousOnInterval hzero
  | @insert i s hi ih =>
      have hiAC : AbsolutelyContinuousOnInterval (f i) a b :=
        hf i (Finset.mem_insert_self i s)
      have hsAC : AbsolutelyContinuousOnInterval (fun x => ∑ j ∈ s, f j x) a b :=
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      apply absolutelyContinuousOnInterval_congr_on
        (g := fun x => f i x + ∑ j ∈ s, f j x)
      · intro x hx
        simp [Finset.sum_insert hi]
      · exact hiAC.add hsAC

theorem lipschitzWith_logarithmicHinge (c : ℝ) :
    LipschitzWith 1 (fun t : ℝ => max 0 (|t| - c)) := by
  have habs : LipschitzWith 1 (fun t : ℝ => |t|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using
      abs_abs_sub_abs_le_abs_sub x y
  have hmax : LipschitzWith 1 (fun t : ℝ => max c |t|) := habs.const_max c
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hmax.dist_le_mul x y
  calc
    dist (max 0 (|x| - c)) (max 0 (|y| - c)) =
        dist (max c |x| - c) (max c |y| - c) := by
      rw [← max_sub_sub_right c |x| c, ← max_sub_sub_right c |y| c]
      simp
    _ = dist (max c |x|) (max c |y|) :=
      dist_sub_right (max c |x|) (max c |y|) c
    _ ≤ (1 : NNReal) * dist x y := h

theorem absolutelyContinuousOnInterval_screwPrimeSum_abs (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => screwPrimeSum |t|) a b := by
  classical
  let T : ℝ := max |a| |b|
  let N : ℕ := ⌊Real.exp T⌋₊
  let P : ℝ → ℝ := fun t =>
    ∑ n ∈ Finset.Icc 2 N,
      screwPrimeWeight n * max 0 (|t| - Real.log n)
  have hP : AbsolutelyContinuousOnInterval P a b := by
    dsimp only [P]
    apply absolutelyContinuousOnInterval_finset_sum
    intro n hn
    exact (lipschitzOnWith_absolutelyContinuousOnInterval
      (lipschitzWith_logarithmicHinge (Real.log n)).lipschitzOnWith).const_mul
        (screwPrimeWeight n)
  apply absolutelyContinuousOnInterval_congr_on (g := P) (hg := hP)
  intro t ht
  dsimp only [P]
  rw [screwPrimeSum_eq_sum_max]
  dsimp only [N, T]
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at ht
    exact abs_le_max_abs_abs ht.1 ht.2
  · rw [uIcc_of_ge hba] at ht
    simpa only [max_comm] using abs_le_max_abs_abs ht.1 ht.2

/-- Suzuki's exact arithmetic screw function is locally absolutely continuous on every compact
interval.  This includes its logarithmic origin cusp and all prime-power derivative jumps. -/
theorem absolutelyContinuousOnInterval_suzukiSourceScrew (a b : ℝ) :
    AbsolutelyContinuousOnInterval suzukiSourceScrew a b := by
  have hcusp := absolutelyContinuousOnInterval_logarithmicCusp a b
  have habs : AbsolutelyContinuousOnInterval (fun t : ℝ => |t|) a b :=
    lipschitzOnWith_absolutelyContinuousOnInterval
      (show LipschitzOnWith 1 (fun t : ℝ => |t|) (uIcc a b) from by
        apply LipschitzWith.lipschitzOnWith
        apply LipschitzWith.of_dist_le_mul
        intro x y
        simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using
          abs_abs_sub_abs_le_abs_sub x y)
  have hprime := absolutelyContinuousOnInterval_screwPrimeSum_abs a b
  have hrem : AbsolutelyContinuousOnInterval suzukiOriginRemainder a b :=
    contDiffOn_one_absolutelyContinuousOnInterval
      ((contDiff_two_suzukiOriginRemainder.of_le (by norm_num)).contDiffOn)
  have hsum : AbsolutelyContinuousOnInterval
      (fun t : ℝ =>
        (1 / 2 : ℝ) * (|t| * Real.log |t|) +
          suzukiOriginLinearCoeff * |t| + screwPrimeSum |t| +
            suzukiOriginRemainder t) a b :=
    (((hcusp.const_mul (1 / 2 : ℝ)).add
      (habs.const_mul suzukiOriginLinearCoeff)).add hprime).add hrem
  apply absolutelyContinuousOnInterval_congr_on (g := fun t : ℝ =>
      (1 / 2 : ℝ) * (|t| * Real.log |t|) +
        suzukiOriginLinearCoeff * |t| + screwPrimeSum |t| +
          suzukiOriginRemainder t) (hg := hsum)
  intro t ht
  simpa only [mul_assoc] using suzuki_equation_two_two t

theorem integrableOn_log_sq_Ioc_zero_one :
    IntegrableOn (fun t : ℝ => Real.log t ^ 2) (Ioc (0 : ℝ) 1) := by
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (Ioc (0 : ℝ) 1) := by
    have h := intervalIntegral.intervalIntegrable_rpow'
      (a := (0 : ℝ)) (b := (1 : ℝ)) (r := (-(1 : ℝ) / 2)) (by norm_num)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
  have hmajor : IntegrableOn (fun t : ℝ => 16 * t ^ (-(1 : ℝ) / 2))
      (Ioc (0 : ℝ) 1) := hpow.const_mul 16
  refine hmajor.mono' ?_ ?_
  · exact (Real.measurable_log.pow_const 2).aestronglyMeasurable.restrict
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    have htpos : 0 < t := ht.1
    have htone : t ≤ 1 := ht.2
    have hlognonpos : Real.log t ≤ 0 := Real.log_nonpos htpos.le htone
    have hlog := GaloisForLFunctions.HTGeometry.log_inv_le_rpow htpos
    have hlog' : -Real.log t ≤ 4 * t ^ (-(1 : ℝ) / 4) := by
      simpa only [one_div, Real.log_inv] using hlog
    have hsq := pow_le_pow_left₀ (neg_nonneg.mpr hlognonpos) hlog' 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      Real.log t ^ 2 = (-Real.log t) ^ 2 := by ring
      _ ≤ (4 * t ^ (-(1 : ℝ) / 4)) ^ 2 := hsq
      _ = 16 * t ^ (-(1 : ℝ) / 2) := by
        rw [mul_pow]
        norm_num
        rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
        norm_num

theorem intervalIntegrable_log_sq (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log t ^ 2) volume a b := by
  apply intervalIntegrable_of_even (ha := by finiteness) (hb := by finiteness)
  · intro t
    rw [Real.log_neg_eq_log]
  · intro t ht
    have h01 : IntervalIntegrable (fun s : ℝ => Real.log s ^ 2) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
      exact integrableOn_log_sq_Ioc_zero_one
    rcases le_total t 1 with ht1 | h1t
    · apply h01.mono_set
      rw [uIcc_of_le ht.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc_right ht1
    · exact h01.trans (ContinuousOn.intervalIntegrable
        ((Real.continuousOn_log.mono (by
          intro s hs
          rw [uIcc_of_le h1t] at hs
          exact mem_compl_singleton_iff.mpr (by linarith [hs.1]))).pow 2))

theorem lipschitzWith_const_mul_real {f : ℝ → ℝ} {K : NNReal}
    (c : ℝ) (hf : LipschitzWith K f) :
    LipschitzWith (‖c‖₊ * K) (fun x => c * f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← mul_sub, abs_mul]
  calc
    |c| * |f x - f y| ≤ |c| * (K * dist x y) := by
      gcongr
      simpa only [Real.dist_eq] using hf.dist_le_mul x y
    _ = ((‖c‖₊ * K : NNReal) : ℝ) * dist x y := by
      simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
      ring

theorem exists_lipschitzWith_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, ∃ K : NNReal, LipschitzWith K (f i)) :
    ∃ K : NNReal, LipschitzWith K (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp only [Finset.sum_empty]
      exact (LipschitzWith.const (0 : ℝ) :
        LipschitzWith 0 (fun _ : ℝ => (0 : ℝ)))
  | @insert i s hi ih =>
      obtain ⟨Ki, hiLip⟩ := hf i (Finset.mem_insert_self i s)
      obtain ⟨Ks, hsLip⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      refine ⟨Ki + Ks, ?_⟩
      simpa [Finset.sum_insert hi] using hiLip.add hsLip

theorem hasDerivAt_logarithmicCusp_of_ne {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => |s| * Real.log |s|)
      (logarithmicCuspDerivative t) t := by
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t := hasDerivAt_neg t
    have hlog := (Real.hasDerivAt_log (neg_ne_zero.mpr ht)).comp t hneg
    have hmul := hneg.mul hlog
    have hderiv : -1 * Real.log (-t) + (-t) * ((-t)⁻¹ * -1) =
        logarithmicCuspDerivative t := by
      unfold logarithmicCuspDerivative
      rw [sign_neg htneg, SignType.coe_neg_one, Real.log_neg_eq_log]
      field_simp [ht]
      ring
    have hraw := hmul.congr_deriv hderiv
    apply hraw.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds htneg] with s hs
    rw [abs_of_neg hs]
    rfl
  · have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have hlog := Real.hasDerivAt_log ht
    have hmul := hid.mul hlog
    have hderiv : 1 * Real.log t + t * t⁻¹ = logarithmicCuspDerivative t := by
      unfold logarithmicCuspDerivative
      rw [sign_pos htpos, SignType.coe_one]
      field_simp [ht]
    have hraw := hmul.congr_deriv hderiv
    apply hraw.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds htpos] with s hs
    rw [abs_of_pos hs]
    rfl

/-- The first derivative of Suzuki's exact source screw is square-integrable on every compact
interval.  This is the analytic regularity used in Suzuki's `Gₐ(L²₀) ⊆ H¹` argument. -/
theorem intervalIntegrable_deriv_suzukiSourceScrew_sq (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => deriv suzukiSourceScrew t ^ 2) volume a b := by
  classical
  let lo : ℝ := min a b - 1
  let hi : ℝ := max a b + 1
  let T : ℝ := max |lo| |hi|
  let N : ℕ := ⌊Real.exp T⌋₊
  let P : ℝ → ℝ := fun t =>
    ∑ n ∈ Finset.Icc 2 N,
      screwPrimeWeight n * max 0 (|t| - Real.log n)
  let R : ℝ → ℝ := fun t =>
    suzukiOriginLinearCoeff * |t| + P t + suzukiOriginRemainder t
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    have h : min a b ≤ max a b := min_le_max
    linarith
  have habsLip : LipschitzWith 1 (fun t : ℝ => |t|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using
      abs_abs_sub_abs_le_abs_sub x y
  obtain ⟨KP, hPLip⟩ : ∃ K : NNReal, LipschitzWith K P := by
    dsimp only [P]
    apply exists_lipschitzWith_finset_sum
    intro n hn
    refine ⟨‖screwPrimeWeight n‖₊, ?_⟩
    simpa using lipschitzWith_const_mul_real (screwPrimeWeight n)
      (lipschitzWith_logarithmicHinge (Real.log n))
  have hremCD : ContDiffOn ℝ 1 suzukiOriginRemainder (uIcc lo hi) :=
    (contDiff_two_suzukiOriginRemainder.of_le (by norm_num)).contDiffOn
  obtain ⟨Kr, hremLip⟩ := hremCD.exists_lipschitzOnWith (by norm_num)
        (by rw [uIcc_of_le hlohi]; exact convex_Icc lo hi)
        (by rw [uIcc_of_le hlohi]; exact isCompact_Icc)
  have hRLip : LipschitzOnWith
      (‖suzukiOriginLinearCoeff‖₊ * 1 + KP + Kr) R (uIcc lo hi) := by
    dsimp only [R]
    have hglobal :=
      (lipschitzWith_const_mul_real suzukiOriginLinearCoeff habsLip).add hPLip
    exact hglobal.lipschitzOnWith.add hremLip
  have hReq : Set.EqOn
      (fun t => suzukiOriginLinearCoeff * |t| + screwPrimeSum |t| +
        suzukiOriginRemainder t) R (uIcc lo hi) := by
    intro t ht
    dsimp only [R, P]
    congr 2
    rw [screwPrimeSum_eq_sum_max]
    dsimp only [N, T]
    apply Nat.floor_mono
    apply Real.exp_le_exp.mpr
    rw [uIcc_of_le hlohi] at ht
    exact abs_le_max_abs_abs ht.1 ht.2
  have hRAC : AbsolutelyContinuousOnInterval R lo hi :=
    lipschitzOnWith_absolutelyContinuousOnInterval hRLip
  let K : ℝ := ((‖suzukiOriginLinearCoeff‖₊ * 1 + KP + Kr : NNReal) : ℝ)
  let C : ℝ := 2 * (1 + K) ^ 2
  have hmajor : IntervalIntegrable
      (fun t : ℝ => 2 * Real.log t ^ 2 + C) volume a b :=
    (intervalIntegrable_log_sq a b).const_mul 2 |>.add intervalIntegrable_const
  apply hmajor.mono_fun
  · have hderivInt :=
      (absolutelyContinuousOnInterval_suzukiSourceScrew a b).intervalIntegrable_deriv
    exact hderivInt.aestronglyMeasurable_restrict_uIoc.pow 2
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_uIoc,
      ae_restrict_of_ae hRAC.ae_differentiableAt,
      (volume.restrict (uIoc a b)).ae_ne 0] with t ht htR ht0
    have htab : min a b ≤ t ∧ t ≤ max a b := by
      rcases le_total a b with hab | hba
      · rw [uIoc_of_le hab] at ht
        rw [min_eq_left hab, max_eq_right hab]
        exact ⟨ht.1.le, ht.2⟩
      · rw [uIoc_of_ge hba] at ht
        rw [min_eq_right hba, max_eq_left hba]
        exact ⟨ht.1.le, ht.2⟩
    have htlo : lo < t := by dsimp [lo]; linarith [htab.1]
    have hthi : t < hi := by dsimp [hi]; linarith [htab.2]
    have htOuter : t ∈ uIcc lo hi := by
      rw [uIcc_of_le hlohi]
      exact ⟨htlo.le, hthi.le⟩
    have hOuterNhds : uIcc lo hi ∈ 𝓝 t := by
      apply mem_of_superset (Ioo_mem_nhds htlo hthi)
      rw [uIcc_of_le hlohi]
      exact Ioo_subset_Icc_self
    have hlocal : suzukiSourceScrew =ᶠ[𝓝 t]
        (fun s => (1 / 2 : ℝ) * (|s| * Real.log |s|) + R s) := by
      filter_upwards [hOuterNhds] with s hs
      calc
        suzukiSourceScrew s =
            (1 / 2 : ℝ) * (|s| * Real.log |s|) +
              (suzukiOriginLinearCoeff * |s| + screwPrimeSum |s| +
                suzukiOriginRemainder s) := by
          rw [suzuki_equation_two_two]
          ring
        _ = (1 / 2 : ℝ) * (|s| * Real.log |s|) + R s := by
          exact congrArg (fun x => (1 / 2 : ℝ) * (|s| * Real.log |s|) + x)
            (hReq hs)
    have hcusp := hasDerivAt_logarithmicCusp_of_ne ht0
    have hRdiff : DifferentiableAt ℝ R t := htR htOuter
    have hsum := (hcusp.const_mul (1 / 2 : ℝ)).add hRdiff.hasDerivAt
    have hderiv : deriv suzukiSourceScrew t =
        (1 / 2 : ℝ) * logarithmicCuspDerivative t + deriv R t := by
      rw [hlocal.deriv_eq]
      have hfun : (fun s => (1 / 2 : ℝ) * (|s| * Real.log |s|) + R s) =
          ((fun y => (1 / 2 : ℝ) * (|y| * Real.log |y|)) + R) := by
        funext s
        rfl
      rw [hfun]
      exact hsum.deriv
    have hRbound : ‖deriv R t‖ ≤ K := by
      exact norm_deriv_le_of_lipschitzOn hOuterNhds hRLip
    have hcuspNorm : ‖logarithmicCuspDerivative t‖ = |Real.log t + 1| := by
      rw [logarithmicCuspDerivative, norm_mul]
      rcases lt_or_gt_of_ne ht0 with htneg | htpos
      · rw [sign_neg htneg, SignType.coe_neg_one]
        norm_num
      · rw [sign_pos htpos, SignType.coe_one]
        norm_num
    have hnorm : ‖deriv suzukiSourceScrew t‖ ≤
        (1 / 2 : ℝ) * |Real.log t + 1| + K := by
      rw [hderiv]
      calc
        ‖(1 / 2 : ℝ) * logarithmicCuspDerivative t + deriv R t‖ ≤
            ‖(1 / 2 : ℝ) * logarithmicCuspDerivative t‖ + ‖deriv R t‖ :=
          norm_add_le _ _
        _ ≤ (1 / 2 : ℝ) * |Real.log t + 1| + K := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num), hcuspNorm]
          gcongr
    have hlogAbs : |Real.log t + 1| ≤ |Real.log t| + 1 := by
      simpa using abs_add_le (Real.log t) 1
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hD : 0 ≤ ‖deriv suzukiSourceScrew t‖ := norm_nonneg _
    have hL : 0 ≤ |Real.log t| := abs_nonneg _
    have hupper : ‖deriv suzukiSourceScrew t‖ ≤ |Real.log t| + (1 + K) := by
      calc
        ‖deriv suzukiSourceScrew t‖ ≤
            (1 / 2 : ℝ) * |Real.log t + 1| + K := hnorm
        _ ≤ |Real.log t| + (1 + K) := by nlinarith
    have hsq : ‖deriv suzukiSourceScrew t‖ ^ 2 ≤
        2 * Real.log t ^ 2 + C := by
      dsimp only [C]
      have hsquare := sq_nonneg (|Real.log t| - (1 + K))
      have habsq : |Real.log t| ^ 2 = Real.log t ^ 2 := sq_abs (Real.log t)
      rw [← habsq]
      nlinarith [sq_nonneg ‖deriv suzukiSourceScrew t‖]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (by dsimp [C]; positivity)]
    simpa only [Real.norm_eq_abs, sq_abs] using hsq

end GaloisForLFunctions.RHTower

end
