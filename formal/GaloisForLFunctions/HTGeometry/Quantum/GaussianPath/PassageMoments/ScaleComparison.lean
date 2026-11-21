import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.CutoffClock
import Mathlib.Analysis.Real.Pi.Bounds

/-! # A scale-free upper comparison of first return and onset -/
open Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PassageMoments
noncomputable section
open PrescribedTimes

/-- Every origin A≥0 admits an s-gate visit in [A,63^(D−1)A].
The integer clock applies to the generator multiplied by A. -/
theorem affordable_by_origin_multiple (n s : ℕ) (x : PrefixIndex n → ℝ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ t ∈ Icc A (A*(63:ℝ)^(2^(n+2)-1)), pathGateDistance n s x t ≤ 1/10 := by
  let N := n+2
  let d := 2^N-1
  let e := (qubitConfigFin N).trans (finCongr (show 2^N=d+1 by
    dsimp [d]
    exact (Nat.sub_add_cancel (Nat.one_le_two_pow)).symm))
  let H := prefixGenerator n (A • x)
  obtain ⟨v,hv,c,hc,C,hC,herr⟩ := projective_operator_zero_gate_return_after e H 0 62
  have hd : pathGateDistance n s (A • x) v ≤ (1/10:ℝ) :=
    (hasProjectiveCircuitApproximation_iff_infDist _ s _).mp
      ⟨c,hc,C,hC.trans (Nat.zero_le _),herr.trans (by norm_num; linarith only [Real.pi_lt_d2])⟩
  have hv' : v ∈ Icc 1 ((63:ℝ)^d) := by norm_num at hv ⊢; exact hv
  refine ⟨A*v,⟨?_,mul_le_mul_of_nonneg_left hv'.2 hA⟩,?_⟩
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hv'.1 hA
  · rwa [←distance_dilate n s A x v]

/-- For every coefficient vector and both gate budgets, the actual wait
is bounded by the first crossing multiplied by a dimension-only factor. -/
theorem first_wait_le_scaled_onset (n j s : ℕ) (x : PrefixIndex n → ℝ) :
    crossingWait n j s x ≤ ((63:ℝ)^(2^(n+2)-1)-1)*crossingOrigin n j (9/80) x := by
  let a := crossingOrigin n j (9/80) x
  have ha : 0 ≤ a := Real.sInf_nonneg (fun _ h => h.1)
  obtain ⟨t,ht,h⟩ := affordable_by_origin_multiple n s x ha
  apply (crossingWait_le_iff _ _ _ _ _).mpr
  exact ⟨t,⟨ht.1,ht.2.trans_eq (by change a*_ = a+(_-1)*a; ring)⟩,h⟩

/-- Under any disorder law, adding the actual first wait to the onset by
taking their maximum preserves exactly the finite positive moment orders. -/
theorem passage_moment_iff_onset (k s : ℕ) (μ : Measure (PrefixIndex (k+1) → ℝ)) {p : ℝ} (hp : 0 < p) :
    let a := crossingOrigin (k+1) (nearHilbertContinuousCircuitBudget (k+3)) (9/80)
    Integrable (fun x => (passageMax k s x)^p) μ ↔ Integrable (fun x => (a x)^p) μ := by
  intro a
  let M := (63:ℝ)^(2^(k+3)-1)
  have hM : 1 ≤ M := one_le_pow₀ (by norm_num)
  have ha (x) : 0 ≤ a x := Real.sInf_nonneg (fun _ h => h.1)
  have below (x) : a x ≤ passageMax k s x := le_max_left ..
  have habove (x) : passageMax k s x ≤ M*a x := by
    apply max_le
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hM (ha x)
    · exact (first_wait_le_scaled_onset _ _ s x).trans (mul_le_mul_of_nonneg_right
        (sub_le_self M zero_le_one) (ha x))
  constructor
  · intro h
    apply h.mono' ((measurable_crossingOrigin _ _ _).pow_const p).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (ha x) p)]
    exact Real.rpow_le_rpow (ha x) (below x) hp.le
  · intro h
    apply (h.const_mul (M^p)).mono' ((measurable_passageMax _ _).pow_const p).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (passageMax_nonneg _ _ _) p),
      ←Real.mul_rpow (zero_le_one.trans hM) (ha x)]
    exact Real.rpow_le_rpow (passageMax_nonneg _ _ _) (habove x) hp.le

#print axioms first_wait_le_scaled_onset
#print axioms passage_moment_iff_onset
end
end GaloisForLFunctions.HTGeometry.PassageMoments
