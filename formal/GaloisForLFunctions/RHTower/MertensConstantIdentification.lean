import GaloisForLFunctions.RHTower.MertensSecondRealVariable
import GaloisForLFunctions.RHTower.LogLogIntegralAsymptotic
import GaloisForLFunctions.RHTower.PrimeZetaAbelRepresentation

/-!
# Identification of the Mertens constant

Splitting the Abel representation of the prime zeta function by
`∑_{p ≤ t} 1/p = log log t + M + ε(t)` and comparing with the Euler-product asymptotic identifies

```text
M = γ + ∑_p (log(1 - 1/p) + 1/p).
```
-/

open Filter Topology MeasureTheory Set Asymptotics
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The real-variable Mertens error -/

/-- The Mertens error in the real variable. -/
def mertensErrorTail (t : ℝ) : ℝ :=
  primeRecipSum ⌊t⌋₊ - Real.log (Real.log t) - mertensSecondConstant

theorem tendsto_mertensErrorTail : Tendsto mertensErrorTail atTop (nhds 0) := by
  have h := tendsto_primeRecipSum_floor_sub_logLog.sub_const mertensSecondConstant
  rw [sub_self] at h
  exact h

/-- Slope of the linear-logarithmic bound on the Mertens error. -/
def mertensErrorSlope : ℝ := 1 / Real.log 2 + 1

/-- Intercept of the linear-logarithmic bound on the Mertens error. -/
def mertensErrorIntercept : ℝ :=
  mertensPrimeWindowBound / Real.log 2 + |Real.log (Real.log 2)| + |mertensSecondConstant|

theorem mertensErrorSlope_pos : 0 < mertensErrorSlope := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [mertensErrorSlope]
  positivity

theorem mertensErrorIntercept_nonneg : 0 ≤ mertensErrorIntercept := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 ≤ mertensPrimeWindowBound := mertensPrimeWindowBound_nonneg
  rw [mertensErrorIntercept]
  positivity

theorem abs_mertensErrorTail_le {t : ℝ} (ht : 2 ≤ t) :
    |mertensErrorTail t| ≤ mertensErrorIntercept + mertensErrorSlope * Real.log t := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht0 : (0 : ℝ) < t := by linarith
  have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr (by linarith)
  have hfloorpos : (0 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hfloor1
  have hfloorle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
  have hA0 : 0 ≤ primeRecipSum ⌊t⌋₊ := primeRecipSum_nonneg _
  have hAle : primeRecipSum ⌊t⌋₊ ≤ (Real.log t + mertensPrimeWindowBound) / Real.log 2 := by
    refine (primeRecipSum_le_log hfloor1).trans ?_
    gcongr
  have hlogloglt := abs_logLog_le ht
  have hM : |mertensSecondConstant| ≤ |mertensSecondConstant| := le_rfl
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have habs : |mertensErrorTail t| ≤
      primeRecipSum ⌊t⌋₊ + |Real.log (Real.log t)| + |mertensSecondConstant| := by
    rw [mertensErrorTail]
    calc |primeRecipSum ⌊t⌋₊ - Real.log (Real.log t) - mertensSecondConstant|
        ≤ |primeRecipSum ⌊t⌋₊ - Real.log (Real.log t)| + |mertensSecondConstant| :=
          abs_sub _ _
      _ ≤ (|primeRecipSum ⌊t⌋₊| + |Real.log (Real.log t)|) + |mertensSecondConstant| := by
          gcongr
          exact abs_sub _ _
      _ = primeRecipSum ⌊t⌋₊ + |Real.log (Real.log t)| + |mertensSecondConstant| := by
          rw [abs_of_nonneg hA0]
  refine habs.trans ?_
  rw [mertensErrorIntercept, mertensErrorSlope]
  have hdiv : (Real.log t + mertensPrimeWindowBound) / Real.log 2 =
      Real.log t / Real.log 2 + mertensPrimeWindowBound / Real.log 2 := by
    rw [add_div]
  have hkey : Real.log t / Real.log 2 = 1 / Real.log 2 * Real.log t := by
    rw [one_div, div_eq_inv_mul]
  rw [hdiv, hkey] at hAle
  linarith

/-! ## Integrability against the Abel weight -/

theorem integrableOn_rpow_neg {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ (-δ - 1)) (Ioi (2 : ℝ)) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)

theorem integrableOn_rpow_mul_log {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * Real.log t) (Ioi (2 : ℝ)) := by
  have hmajorInt : IntegrableAtFilter (fun t : ℝ => t ^ (-1 - δ / 2)) atTop :=
    ⟨Ioi (1 : ℝ), Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by linarith) one_pos⟩
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-δ - 1) * Real.log t) (Ici (2 : ℝ)) := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    exact ((Real.continuousAt_rpow_const t (-δ - 1) (Or.inl ht0.ne')).mul
      (Real.continuousAt_log ht0.ne')).continuousWithinAt
  have hloc : LocallyIntegrableOn (fun t : ℝ => t ^ (-δ - 1) * Real.log t) (Ici (2 : ℝ)) :=
    hcont.locallyIntegrableOn measurableSet_Ici
  have hbigO : (fun t : ℝ => t ^ (-δ - 1) * Real.log t) =O[atTop]
      (fun t : ℝ => t ^ (-1 - δ / 2)) := by
    have hmul := (isBigO_refl (fun t : ℝ => t ^ (-δ - 1)) atTop).mul
      ((isLittleO_log_rpow_atTop (by positivity : (0 : ℝ) < δ / 2)).isBigO)
    refine hmul.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← Real.rpow_add ht, show -δ - 1 + δ / 2 = -1 - δ / 2 by ring, one_mul]
  exact (hloc.integrableOn_of_isBigO_atTop hbigO hmajorInt).mono_set Ioi_subset_Ici_self

private theorem measurable_mertensErrorTail : Measurable mertensErrorTail := by
  have h1 : Measurable (fun t : ℝ => primeRecipSum ⌊t⌋₊) :=
    (measurable_from_top (f := primeRecipSum)).comp Nat.measurable_floor
  exact (h1.sub (Real.measurable_log.comp Real.measurable_log)).sub measurable_const

theorem integrableOn_rpow_mul_mertensErrorTail {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * mertensErrorTail t) (Ioi (2 : ℝ)) := by
  have hmajor : IntegrableOn (fun t : ℝ =>
      mertensErrorIntercept * t ^ (-δ - 1) + mertensErrorSlope * (t ^ (-δ - 1) * Real.log t))
      (Ioi (2 : ℝ)) :=
    ((integrableOn_rpow_neg hδ).const_mul _).add ((integrableOn_rpow_mul_log hδ).const_mul _)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (-δ - 1) * mertensErrorTail t)
      (volume.restrict (Ioi (2 : ℝ))) := by
    have : Measurable (fun t : ℝ => t ^ (-δ - 1) * mertensErrorTail t) :=
      (measurable_id.pow_const (-δ - 1)).mul measurable_mertensErrorTail
    exact this.aestronglyMeasurable
  refine Integrable.mono hmajor hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht2 : (2 : ℝ) < t := ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hbd := abs_mertensErrorTail_le ht2.le
  have hnn : (0 : ℝ) ≤ mertensErrorIntercept * t ^ (-δ - 1) +
      mertensErrorSlope * (t ^ (-δ - 1) * Real.log t) := by
    have h1 := mertensErrorIntercept_nonneg
    have h2 := mertensErrorSlope_pos.le
    positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpow, Real.norm_eq_abs, abs_of_nonneg hnn]
  calc t ^ (-δ - 1) * |mertensErrorTail t|
      ≤ t ^ (-δ - 1) * (mertensErrorIntercept + mertensErrorSlope * Real.log t) :=
        mul_le_mul_of_nonneg_left hbd hpow.le
    _ = mertensErrorIntercept * t ^ (-δ - 1) +
        mertensErrorSlope * (t ^ (-δ - 1) * Real.log t) := by ring

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set Asymptotics
open scoped BigOperators

/-! ## Splitting the Abel integral -/

theorem rpow_neg_le_half {δ t : ℝ} (hδ : 0 < δ) (ht : 2 ≤ t) : t ^ (-δ - 1) ≤ 1 / 2 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hstep : t ^ (-δ - 1) ≤ (2 : ℝ) ^ (-δ - 1) := by
    rw [Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    nlinarith
  refine hstep.trans ?_
  rw [show (-δ - 1 : ℝ) = -δ + (-1) by ring, Real.rpow_add (by norm_num : (0:ℝ) < 2),
    Real.rpow_neg_one]
  have h1 : (2 : ℝ) ^ (-δ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by norm_num) _
  norm_num
  linarith

theorem integral_rpow_neg_Ioi {δ : ℝ} (hδ : 0 < δ) (c : ℝ) (hc : 0 < c) :
    (∫ t in Ioi c, t ^ (-δ - 1)) = c ^ (-δ) / δ := by
  rw [integral_Ioi_rpow_of_lt (by linarith) hc]
  rw [show (-δ - 1 + 1 : ℝ) = -δ by ring]
  field_simp

theorem primeRecipSum_one : primeRecipSum 1 = 0 := by
  rw [primeRecipSum, show Finset.Icc 0 1 = ({0, 1} : Finset ℕ) by decide]
  norm_num [primeRecipWeight]

theorem integral_abelWeight_Ioc_one_two {δ : ℝ} :
    (∫ t in Ioc (1 : ℝ) 2, t ^ (-δ - 1) * primeRecipSum ⌊t⌋₊) = 0 := by
  rw [← MeasureTheory.setIntegral_congr_set (Ioo_ae_eq_Ioc (a := (1 : ℝ)) (b := 2))]
  refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
  have h1 : (1 : ℝ) < t := ht.1
  have h2 : t < 2 := ht.2
  have hfloor : ⌊t⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    refine ⟨by exact_mod_cast h1.le, ?_⟩
    push_cast
    linarith
  rw [hfloor, primeRecipSum_one, mul_zero]

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set Asymptotics
open scoped BigOperators

/-! ## The vanishing of the error contribution -/

theorem tendsto_delta_mul_errorIntegral :
    Tendsto (fun δ : ℝ => δ * ∫ t in Ioi (2 : ℝ), t ^ (-δ - 1) * mertensErrorTail t)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro η hη
  obtain ⟨T, hT2, hT⟩ : ∃ T : ℝ, 2 ≤ T ∧ ∀ t, T ≤ t → |mertensErrorTail t| ≤ η / 2 := by
    have h := tendsto_mertensErrorTail
    rw [NormedAddGroup.tendsto_nhds_zero] at h
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (h (η / 2) (by positivity))
    refine ⟨max T₀ 2, le_max_right _ _, fun t ht => ?_⟩
    have hle := hT₀ t (le_trans (le_max_left _ _) ht)
    rw [Real.norm_eq_abs] at hle
    exact hle.le
  set B : ℝ := mertensErrorIntercept + mertensErrorSlope * Real.log T with hB
  have hB0 : 0 ≤ B := by
    have h1 := mertensErrorIntercept_nonneg
    have h2 := mertensErrorSlope_pos.le
    have h3 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    rw [hB]
    positivity
  have hsmall : ∀ᶠ δ : ℝ in nhdsWithin 0 (Ioi 0), δ * (B * (T - 2) / 2) < η / 2 := by
    have hlim : Tendsto (fun δ : ℝ => δ * (B * (T - 2) / 2)) (nhdsWithin 0 (Ioi 0))
        (nhds 0) := by
      have h : Tendsto (fun δ : ℝ => δ * (B * (T - 2) / 2)) (nhds 0)
          (nhds (0 * (B * (T - 2) / 2))) := (continuous_id.mul continuous_const).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    exact hlim.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < η / 2))
  filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδs
  have hδ0 : (0 : ℝ) < δ := hδ
  have hint2 := integrableOn_rpow_mul_mertensErrorTail hδ0
  have hintIoc : IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * mertensErrorTail t)
      (Ioc (2 : ℝ) T) := hint2.mono_set Ioc_subset_Ioi_self
  have hintIoiT : IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * mertensErrorTail t) (Ioi T) :=
    hint2.mono_set (Ioi_subset_Ioi hT2)
  have hdisj : Disjoint (Ioc (2 : ℝ) T) (Ioi T) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    exact absurd hy.2 (not_le.mpr hy')
  have hsplit : (∫ t in Ioi (2 : ℝ), t ^ (-δ - 1) * mertensErrorTail t) =
      (∫ t in Ioc (2 : ℝ) T, t ^ (-δ - 1) * mertensErrorTail t) +
        ∫ t in Ioi T, t ^ (-δ - 1) * mertensErrorTail t := by
    rw [← Ioc_union_Ioi_eq_Ioi hT2, setIntegral_union hdisj measurableSet_Ioi hintIoc hintIoiT]
  have hb1 : |∫ t in Ioc (2 : ℝ) T, t ^ (-δ - 1) * mertensErrorTail t| ≤
      B * (T - 2) / 2 := by
    have hle : ∀ t ∈ Ioc (2 : ℝ) T, ‖t ^ (-δ - 1) * mertensErrorTail t‖ ≤ B / 2 := by
      intro t ht
      have ht2 : (2 : ℝ) < t := ht.1
      have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos (by linarith) _
      have hhalf := rpow_neg_le_half hδ0 ht2.le
      have hbd : |mertensErrorTail t| ≤ B := by
        refine (abs_mertensErrorTail_le ht2.le).trans ?_
        rw [hB]
        have := mertensErrorSlope_pos.le
        have hlog : Real.log t ≤ Real.log T := Real.log_le_log (by linarith) ht.2
        nlinarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpow]
      calc t ^ (-δ - 1) * |mertensErrorTail t| ≤ (1 / 2) * B := by
            exact mul_le_mul hhalf hbd (abs_nonneg _) (by norm_num)
        _ = B / 2 := by ring
    have hconst : IntegrableOn (fun _ : ℝ => B / 2) (Ioc (2 : ℝ) T) :=
      continuous_const.integrableOn_Ioc
    calc |∫ t in Ioc (2 : ℝ) T, t ^ (-δ - 1) * mertensErrorTail t|
        ≤ ∫ t in Ioc (2 : ℝ) T, ‖t ^ (-δ - 1) * mertensErrorTail t‖ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _t in Ioc (2 : ℝ) T, B / 2 :=
          setIntegral_mono_on hintIoc.norm hconst measurableSet_Ioc hle
      _ = B * (T - 2) / 2 := by
          rw [setIntegral_const, smul_eq_mul]
          have hvol : MeasureTheory.volume.real (Ioc (2 : ℝ) T) = T - 2 := by
            simp [MeasureTheory.measureReal_def, Real.volume_Ioc,
              ENNReal.toReal_ofReal, (by linarith : (0 : ℝ) ≤ T - 2)]
          rw [hvol]
          ring
  have hb2 : |∫ t in Ioi T, t ^ (-δ - 1) * mertensErrorTail t| ≤
      η / 2 * (T ^ (-δ) / δ) := by
    have hle : ∀ t ∈ Ioi T, ‖t ^ (-δ - 1) * mertensErrorTail t‖ ≤ η / 2 * t ^ (-δ - 1) := by
      intro t ht
      have htT : T < t := ht
      have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos (by linarith) _
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpow]
      calc t ^ (-δ - 1) * |mertensErrorTail t| ≤ t ^ (-δ - 1) * (η / 2) :=
            mul_le_mul_of_nonneg_left (hT t htT.le) hpow.le
        _ = η / 2 * t ^ (-δ - 1) := by ring
    have hmajor : IntegrableOn (fun t : ℝ => η / 2 * t ^ (-δ - 1)) (Ioi T) :=
      ((integrableOn_rpow_neg hδ0).mono_set (Ioi_subset_Ioi hT2)).const_mul _
    calc |∫ t in Ioi T, t ^ (-δ - 1) * mertensErrorTail t|
        ≤ ∫ t in Ioi T, ‖t ^ (-δ - 1) * mertensErrorTail t‖ := abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioi T, η / 2 * t ^ (-δ - 1) :=
          setIntegral_mono_on hintIoiT.norm hmajor measurableSet_Ioi hle
      _ = η / 2 * (T ^ (-δ) / δ) := by
          rw [MeasureTheory.integral_const_mul, integral_rpow_neg_Ioi hδ0 T (by linarith)]
  have hTpow : T ^ (-δ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hTpow0 : (0 : ℝ) < T ^ (-δ) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.norm_eq_abs, hsplit, abs_mul, abs_of_pos hδ0]
  have hfin : |(∫ t in Ioc (2 : ℝ) T, t ^ (-δ - 1) * mertensErrorTail t) +
      ∫ t in Ioi T, t ^ (-δ - 1) * mertensErrorTail t| ≤
      B * (T - 2) / 2 + η / 2 * (T ^ (-δ) / δ) :=
    le_trans (abs_add_le _ _) (add_le_add hb1 hb2)
  have hstep : δ * |(∫ t in Ioc (2 : ℝ) T, t ^ (-δ - 1) * mertensErrorTail t) +
      ∫ t in Ioi T, t ^ (-δ - 1) * mertensErrorTail t| ≤
      δ * (B * (T - 2) / 2) + η / 2 * T ^ (-δ) := by
    have := mul_le_mul_of_nonneg_left hfin hδ0.le
    have heq : δ * (B * (T - 2) / 2 + η / 2 * (T ^ (-δ) / δ)) =
        δ * (B * (T - 2) / 2) + η / 2 * T ^ (-δ) := by
      field_simp
    linarith [heq ▸ this]
  have hlast : η / 2 * T ^ (-δ) ≤ η / 2 := by
    nlinarith [hTpow, hη.le]
  linarith

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set Asymptotics
open scoped BigOperators

/-! ## The Abelian limit and the constant -/

theorem integral_abelWeight_Ioi_one_eq_Ioi_two {δ : ℝ} :
    (∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * primeRecipSum ⌊t⌋₊) =
      ∫ t in Ioi (2 : ℝ), t ^ (-δ - 1) * primeRecipSum ⌊t⌋₊ := by
  have hne : ∀ᵐ t : ℝ, t ≠ 2 := by
    have h : (volume : Measure ℝ) {(2 : ℝ)} = 0 := Real.volume_singleton
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr h] with t ht
    simpa using ht
  have hindic : (Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-δ - 1) * primeRecipSum ⌊t⌋₊)
      =ᵐ[volume] (Ioi (2 : ℝ)).indicator (fun t : ℝ => t ^ (-δ - 1) * primeRecipSum ⌊t⌋₊) := by
    filter_upwards [hne] with t ht
    by_cases h1 : (1 : ℝ) < t
    · by_cases h2 : (2 : ℝ) < t
      · rw [indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h1),
          indicator_of_mem (show t ∈ Ioi (2 : ℝ) from h2)]
      · have hlt : t < 2 := lt_of_le_of_ne (not_lt.mp h2) ht
        have hfloor : ⌊t⌋₊ = 1 := by
          rw [Nat.floor_eq_iff (by linarith)]
          refine ⟨by exact_mod_cast h1.le, ?_⟩
          push_cast
          linarith
        rw [indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h1),
          indicator_of_notMem (by simpa using not_lt.mp h2), hfloor, primeRecipSum_one, mul_zero]
    · have h2 : ¬(2 : ℝ) < t := fun hc => h1 (by linarith)
      rw [indicator_of_notMem (by simpa using not_lt.mp h1),
        indicator_of_notMem (by simpa using not_lt.mp h2)]
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  exact integral_congr_ae hindic

theorem primeZeta_split {δ : ℝ} (hδ : 0 < δ) :
    primeZeta (1 + δ) =
      δ * (∫ t in Ioi (2 : ℝ), t ^ (-δ - 1) * Real.log (Real.log t))
        + mertensSecondConstant * (2 : ℝ) ^ (-δ)
        + δ * ∫ t in Ioi (2 : ℝ), t ^ (-δ - 1) * mertensErrorTail t := by
  have hA := integrableOn_rpow_mul_logLog hδ
  have hBint := (integrableOn_rpow_neg hδ).const_mul mertensSecondConstant
  have hC := integrableOn_rpow_mul_mertensErrorTail hδ
  have hthree : (∫ t in Ioi (2 : ℝ), t ^ (-δ - 1) * primeRecipSum ⌊t⌋₊) =
      (∫ t in Ioi (2 : ℝ), t ^ (-δ - 1) * Real.log (Real.log t)) +
        (∫ t in Ioi (2 : ℝ), mertensSecondConstant * t ^ (-δ - 1)) +
        ∫ t in Ioi (2 : ℝ), t ^ (-δ - 1) * mertensErrorTail t := by
    have hpt : ∀ t ∈ Ioi (2 : ℝ), t ^ (-δ - 1) * primeRecipSum ⌊t⌋₊ =
        (t ^ (-δ - 1) * Real.log (Real.log t) + mertensSecondConstant * t ^ (-δ - 1)) +
          t ^ (-δ - 1) * mertensErrorTail t := by
      intro t _
      rw [mertensErrorTail]
      ring
    have hAB : IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * Real.log (Real.log t) +
        mertensSecondConstant * t ^ (-δ - 1)) (Ioi (2 : ℝ)) := hA.add hBint
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      MeasureTheory.integral_add hAB hC,
      MeasureTheory.integral_add hA hBint]
  have hconst : (∫ t in Ioi (2 : ℝ), mertensSecondConstant * t ^ (-δ - 1)) =
      mertensSecondConstant * ((2 : ℝ) ^ (-δ) / δ) := by
    rw [MeasureTheory.integral_const_mul, integral_rpow_neg_Ioi hδ 2 (by norm_num)]
  rw [primeZeta_eq_abel_integral hδ, integral_abelWeight_Ioi_one_eq_Ioi_two, hthree, hconst]
  field_simp

/-- **The Abelian limit of the prime zeta function.** -/
theorem tendsto_primeZeta_add_log_abelian :
    Tendsto (fun δ : ℝ => primeZeta (1 + δ) + Real.log δ) (nhdsWithin 0 (Ioi 0))
      (nhds (mertensSecondConstant - Real.eulerMascheroniConstant)) := by
  have hlogLog := tendsto_logLog_integral_add_log
  have hpow : Tendsto (fun δ : ℝ => mertensSecondConstant * (2 : ℝ) ^ (-δ))
      (nhdsWithin 0 (Ioi 0)) (nhds mertensSecondConstant) := by
    have hc : Continuous (fun δ : ℝ => mertensSecondConstant * (2 : ℝ) ^ (-δ)) := by
      have : Continuous (fun δ : ℝ => Real.exp (Real.log 2 * -δ)) := by fun_prop
      refine continuous_const.mul ?_
      refine this.congr fun δ => ?_
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := hc.tendsto (0 : ℝ)
    simp only [neg_zero, Real.rpow_zero, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have herr := tendsto_delta_mul_errorIntegral
  have hsum := (hlogLog.add hpow).add herr
  rw [add_zero] at hsum
  have hval : -Real.eulerMascheroniConstant + mertensSecondConstant =
      mertensSecondConstant - Real.eulerMascheroniConstant := by ring
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [primeZeta_split hδ]
  ring

/-- **The Mertens constant.**  `M = γ + ∑_p (log(1 - 1/p) + 1/p)`. -/
theorem mertensSecondConstant_eq :
    mertensSecondConstant = Real.eulerMascheroniConstant - primeLogDefect 1 := by
  have hshift : Tendsto (fun δ : ℝ => 1 + δ) (nhdsWithin 0 (Ioi 0))
      (nhdsWithin 1 (Ioi 1)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun δ : ℝ => 1 + δ) (nhds 0) (nhds (1 + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      simpa using hδ
  have hzeta := tendsto_primeZeta_add_log_sub.comp hshift
  have hcongr : Tendsto (fun δ : ℝ => primeZeta (1 + δ) + Real.log δ)
      (nhdsWithin 0 (Ioi 0)) (nhds (-primeLogDefect 1)) := by
    refine hzeta.congr fun δ => ?_
    simp only [Function.comp_apply]
    congr 2
    ring
  have := tendsto_nhds_unique tendsto_primeZeta_add_log_abelian hcongr
  linarith [this]

end

end RHTower
