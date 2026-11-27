import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.UnitRMS
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitTails

/-! # Sixth moments and high-confidence deadlines for normalized first excursions -/
open Set Filter MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
open PrescribedTimes WeakBonds
noncomputable section

/-- The minimum of the onset and subsequent first wait, both before
and after fixing unit RMS, has infinite sixth moment even on samples
with every physical Pauli strength in the positive interval [1/20,4]. -/
theorem positive_sixth_moment :
    ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let P := nearHilbertContinuousCircuitBudget (n+2)
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let R := sqrt (Fintype.card (PrefixIndex n):ℝ)
      let S := {x : PrefixIndex n→ℝ | ∀ i, x i∈Icc (1/20:ℝ) 4}
      ∀ j ≤ P/2, let J := fun x => min (crossingOrigin n P (9/80) x) (crossingWait n P j x)
        ¬ Integrable (fun x => |S.indicator (fun y => min (J y) (J (atRadius R y))) x|^6) μ := by
  obtain ⟨C,hC,hsector⟩ := positive_rms_tail
  filter_upwards [hsector] with k hk
  intro n P μ R S j hj J
  have hm : Measurable J := (measurable_crossingOrigin ..).min (measurable_crossingWait ..)
  have hn : Measurable (coefficientNorm (n:=n)) := (continuous_norm.comp (PiLp.continuous_toLp 2 _)).measurable
  have hrad : Measurable (atRadius (n:=n) R) := (measurable_const.div hn).smul measurable_id
  have hS : MeasurableSet S := by
    simp only [S,setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_Icc.preimage (measurable_pi_apply i)
  let c := exp (-C*((n+2:ℕ):ℝ)^2)
  have hc : 0<c/(20:ℝ)^6 := div_pos (exp_pos _) (by norm_num)
  let f := S.indicator (fun x => min (J x) (J (atRadius R x)))
  have hf : Measurable f := (hm.min (hm.comp hrad)).indicator hS
  apply not_integrable_boundary_moment μ f hf 6 (B:=1) zero_lt_one (half_pos hc)
  intro T hT
  have h := hk T hT
  rw [mul_pow,mul_assoc] at h
  apply (half_lt_self hc).trans_le
  apply ((div_le_iff₀ (by norm_num : (0:ℝ)<20^6)).mpr (h.trans_eq (mul_comm ..))).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hT) _)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx
  change T*1 < S.indicator _ x
  rw [mul_one,indicator_of_mem (show x∈S from hx.1)]
  have hraw : 20*T < J x := lt_min hx.2.2.1.1 (hx.2.2.1.2 j hj)
  exact lt_min ((by linarith only [hT] : T≤20*T).trans_lt hraw)
    (lt_min hx.2.2.2.1 (hx.2.2.2.2 j hj))

/-- A deadline for the unit-RMS wait at failure probability exp(−aD)
obeys a doubly exponential lower bound from the original crossing. -/
theorem normalized_confidence_deadline :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let R := sqrt (Fintype.card (PrefixIndex n):ℝ)
      ∀ s ≤ P/2, ∀ a : ℝ, ∀ T ≥ (1:ℝ),
        μ.real {x | T < crossingWait n P s (atRadius R x)} ≤ exp (-a*2^K) →
          a*2^K-C*(K:ℝ)^2 ≤ 6*log (20*T) := by
  obtain ⟨C,hC,hsector⟩ := positive_rms_tail
  refine ⟨C,hC,?_⟩
  filter_upwards [hsector] with k hk
  intro n K P μ R s hs a T hT htail
  have hpos : 0<20*T := mul_pos (by norm_num) (zero_lt_one.trans_le hT)
  have h := hk T hT
  have hh : exp (-C*(K:ℝ)^2) ≤ (20*T)^6*exp (-a*2^K) := by
    apply h.trans (mul_le_mul_of_nonneg_left _ (pow_nonneg hpos.le 6))
    apply le_trans _ htail
    exact measureReal_mono (fun x hx => hx.2.2.2.2 s hs) (measure_ne_top μ _)
  have hlog := log_le_log (exp_pos _) hh
  rw [log_exp,log_mul (pow_pos hpos 6).ne' (exp_pos _).ne',log_pow,log_exp] at hlog
  change -C*(K:ℝ)^2 ≤ (6:ℝ)*log (20*T)+ -a*2^K at hlog
  linarith only [hlog]

#print axioms positive_sixth_moment
#print axioms normalized_confidence_deadline
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
