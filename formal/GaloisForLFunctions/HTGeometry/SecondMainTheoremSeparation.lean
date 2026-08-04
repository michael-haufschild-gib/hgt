import Mathlib

/-!
# Separating the proximity to several values

At any point, a value can be close to at most one of a family of pairwise separated targets.  The sum
of the proximities to all of them is therefore controlled by the proximity of the single sum
`∑ (w - a_j)⁻¹`, at a cost depending only on the number of targets and their separation.

This is the pointwise step behind the reduction of the second main theorem to estimates for the
logarithmic derivative: it converts a sum of proximity terms into one proximity term, which is what
allows the logarithmic-derivative bound to be applied only once.
-/

open Finset ValueDistribution Metric

namespace GaloisForLFunctions.HTGeometry

/-- **At most one target is close.**  Pairwise separated targets cannot both be within half the
separation of a common point. -/
theorem eq_of_both_close {q : ℕ} {A : Fin q → ℂ} {δ : ℝ}
    (hsep : ∀ i j : Fin q, i ≠ j → δ ≤ ‖A i - A j‖) {w : ℂ} {i j : Fin q}
    (hi : ‖w - A i‖ < δ / 2) (hj : ‖w - A j‖ < δ / 2) : i = j := by
  by_contra hne
  have hsij := hsep i j hne
  have htri : ‖A i - A j‖ ≤ ‖w - A j‖ + ‖w - A i‖ := by
    calc ‖A i - A j‖ = ‖(w - A j) - (w - A i)‖ := by ring_nf
      _ ≤ ‖w - A j‖ + ‖w - A i‖ := norm_sub_le _ _
  linarith

/-- A point far from a target has small proximity to it. -/
theorem posLog_inv_le_of_far {δ : ℝ} (hδ : 0 < δ) {w a : ℂ} (h : δ / 2 ≤ ‖w - a‖) :
    Real.posLog ‖w - a‖⁻¹ ≤ Real.posLog (2 / δ) := by
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  have hpos : 0 < ‖w - a‖ := lt_of_lt_of_le hhalf h
  have hle : ‖w - a‖⁻¹ ≤ 2 / δ := by
    have h1 : (1 : ℝ) / ‖w - a‖ ≤ 1 / (δ / 2) := one_div_le_one_div_of_le hhalf h
    have h2 : (1 : ℝ) / (δ / 2) = 2 / δ := by field_simp
    rw [inv_eq_one_div]
    linarith [h1, h2.le, h2.ge]
  exact Real.posLog_le_posLog (by positivity) hle

/-- **The separation estimate.**  The total proximity to a family of pairwise separated targets is
bounded by the proximity of the sum of the reciprocals, plus a constant depending only on the number
of targets and their separation. -/
theorem sum_posLog_inv_le {q : ℕ} (A : Fin q → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Fin q, i ≠ j → δ ≤ ‖A i - A j‖) (w : ℂ) :
    ∑ j, Real.posLog ‖w - A j‖⁻¹
      ≤ Real.posLog ‖∑ j, (w - A j)⁻¹‖
        + (q : ℝ) * Real.posLog (2 / δ)
        + Real.posLog ((q : ℝ) * (2 / δ)) + Real.log 2 := by
  classical
  have hδ2 : (0 : ℝ) < 2 / δ := by positivity
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hFnn : (0 : ℝ) ≤ Real.posLog ‖∑ j, (w - A j)⁻¹‖ := Real.posLog_nonneg
  have hCnn : (0 : ℝ) ≤ Real.posLog ((q : ℝ) * (2 / δ)) := Real.posLog_nonneg
  by_cases hex : ∃ j₀ : Fin q, ‖w - A j₀‖ < δ / 2
  · obtain ⟨j₀, hj₀⟩ := hex
    have hfar : ∀ j ∈ Finset.univ.erase j₀, δ / 2 ≤ ‖w - A j‖ := by
      intro j hj
      have hne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
      by_contra hcon
      exact hne (eq_of_both_close hsep (not_le.mp hcon) hj₀)
    -- the far targets
    have hrest : ∑ j ∈ Finset.univ.erase j₀, Real.posLog ‖w - A j‖⁻¹
        ≤ (q : ℝ) * Real.posLog (2 / δ) := by
      have hbd : ∀ j ∈ Finset.univ.erase j₀,
          Real.posLog ‖w - A j‖⁻¹ ≤ Real.posLog (2 / δ) :=
        fun j hj => posLog_inv_le_of_far hδ (hfar j hj)
      have h := Finset.sum_le_card_nsmul _ _ _ hbd
      rw [nsmul_eq_mul] at h
      refine le_trans h ?_
      have hcard : ((Finset.univ.erase j₀).card : ℝ) ≤ (q : ℝ) := by
        have := Finset.card_erase_le (s := (Finset.univ : Finset (Fin q))) (a := j₀)
        have hle : (Finset.univ.erase j₀).card ≤ q := by
          simp only [Finset.card_univ, Fintype.card_fin] at this
          exact this
        exact_mod_cast hle
      exact mul_le_mul_of_nonneg_right hcard Real.posLog_nonneg
    -- the close target
    have hnormrest : ∑ j ∈ Finset.univ.erase j₀, ‖(w - A j)⁻¹‖ ≤ (q : ℝ) * (2 / δ) := by
      have hbd : ∀ j ∈ Finset.univ.erase j₀, ‖(w - A j)⁻¹‖ ≤ 2 / δ := by
        intro j hj
        rw [norm_inv]
        have hhalf : (0 : ℝ) < δ / 2 := by linarith
        have hpos : 0 < ‖w - A j‖ := lt_of_lt_of_le hhalf (hfar j hj)
        have h1 : (1 : ℝ) / ‖w - A j‖ ≤ 1 / (δ / 2) :=
          one_div_le_one_div_of_le hhalf (hfar j hj)
        have h2 : (1 : ℝ) / (δ / 2) = 2 / δ := by field_simp
        rw [inv_eq_one_div]
        linarith [h1, h2.le, h2.ge]
      have h := Finset.sum_le_card_nsmul _ _ _ hbd
      rw [nsmul_eq_mul] at h
      refine le_trans h ?_
      have hcard : ((Finset.univ.erase j₀).card : ℝ) ≤ (q : ℝ) := by
        have hcerase := Finset.card_erase_le (s := (Finset.univ : Finset (Fin q))) (a := j₀)
        have hle : (Finset.univ.erase j₀).card ≤ q := by
          simp only [Finset.card_univ, Fintype.card_fin] at hcerase
          exact hcerase
        exact_mod_cast hle
      exact mul_le_mul_of_nonneg_right hcard (le_of_lt hδ2)
    have hsplit : (w - A j₀)⁻¹
        = (∑ j, (w - A j)⁻¹) - ∑ j ∈ Finset.univ.erase j₀, (w - A j)⁻¹ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
      ring
    have hnormj₀ : ‖w - A j₀‖⁻¹ ≤ ‖∑ j, (w - A j)⁻¹‖ + (q : ℝ) * (2 / δ) := by
      rw [← norm_inv]
      rw [hsplit]
      calc ‖(∑ j, (w - A j)⁻¹) - ∑ j ∈ Finset.univ.erase j₀, (w - A j)⁻¹‖
          ≤ ‖∑ j, (w - A j)⁻¹‖ + ‖∑ j ∈ Finset.univ.erase j₀, (w - A j)⁻¹‖ := norm_sub_le _ _
        _ ≤ ‖∑ j, (w - A j)⁻¹‖ + ∑ j ∈ Finset.univ.erase j₀, ‖(w - A j)⁻¹‖ := by
            have hns := norm_sum_le (Finset.univ.erase j₀) (fun j => (w - A j)⁻¹)
            linarith
        _ ≤ ‖∑ j, (w - A j)⁻¹‖ + (q : ℝ) * (2 / δ) := by linarith
    have hclose : Real.posLog ‖w - A j₀‖⁻¹
        ≤ Real.log 2 + Real.posLog ‖∑ j, (w - A j)⁻¹‖
          + Real.posLog ((q : ℝ) * (2 / δ)) := by
      refine le_trans (Real.posLog_le_posLog (by positivity) hnormj₀) ?_
      exact Real.posLog_add
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
    linarith
  · have hfar : ∀ j : Fin q, δ / 2 ≤ ‖w - A j‖ := by
      intro j
      by_contra hcon
      exact hex ⟨j, not_le.mp hcon⟩
    have hbd : ∀ j ∈ (Finset.univ : Finset (Fin q)),
        Real.posLog ‖w - A j‖⁻¹ ≤ Real.posLog (2 / δ) :=
      fun j _ => posLog_inv_le_of_far hδ (hfar j)
    have h := Finset.sum_le_card_nsmul _ _ _ hbd
    rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at h
    linarith

/-! ## The integrated form -/

/-- **The separation estimate, integrated.**  The total proximity of `f` to a family of pairwise
separated values is bounded by the proximity of `∑ (f - a_j)⁻¹` at infinity, plus a constant
depending only on the number of values and their separation.

This is the step that lets the logarithmic-derivative estimate be applied once rather than once per
value.  The integrability hypotheses are the ones a meromorphic `f` supplies through
`MeromorphicOn.circleIntegrable_posLog_norm`. -/
theorem sum_proximity_le {f : ℂ → ℂ} {q : ℕ} (A : Fin q → ℂ) {δ r : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Fin q, i ≠ j → δ ≤ ‖A i - A j‖)
    (hint : ∀ j : Fin q, CircleIntegrable (fun z => Real.posLog ‖f z - A j‖⁻¹) 0 r)
    (hintF : CircleIntegrable (fun z => Real.posLog ‖∑ j, (f z - A j)⁻¹‖) 0 r) :
    ∑ j, proximity f (A j : WithTop ℂ) r
      ≤ proximity (fun z => ∑ j, (f z - A j)⁻¹) ⊤ r
        + ((q : ℝ) * Real.posLog (2 / δ) + Real.posLog ((q : ℝ) * (2 / δ)) + Real.log 2) := by
  classical
  set C : ℝ :=
    (q : ℝ) * Real.posLog (2 / δ) + Real.posLog ((q : ℝ) * (2 / δ)) + Real.log 2 with hC
  have hfun : ∀ j ∈ (Finset.univ : Finset (Fin q)),
      CircleIntegrable (fun z => Real.posLog ‖f z - A j‖⁻¹) 0 r := fun j _ => hint j
  have hconstint : CircleIntegrable (fun _ : ℂ => C) 0 r :=
    ContinuousOn.circleIntegrable' continuousOn_const
  have hsum : ∑ j, proximity f (A j : WithTop ℂ) r
      = Real.circleAverage (fun z => ∑ j, Real.posLog ‖f z - A j‖⁻¹) 0 r := by
    rw [Real.circleAverage_fun_sum hfun]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [proximity_coe]
  have hmono : Real.circleAverage (fun z => ∑ j, Real.posLog ‖f z - A j‖⁻¹) 0 r
      ≤ Real.circleAverage (fun z => Real.posLog ‖∑ j, (f z - A j)⁻¹‖ + C) 0 r := by
    refine Real.circleAverage_mono (CircleIntegrable.fun_sum _ hfun) (hintF.add hconstint) ?_
    intro z _
    have := sum_posLog_inv_le A hδ hsep (f z)
    rw [hC]
    linarith
  have hconst : Real.circleAverage (fun z => Real.posLog ‖∑ j, (f z - A j)⁻¹‖ + C) 0 r
      = Real.circleAverage (fun z => Real.posLog ‖∑ j, (f z - A j)⁻¹‖) 0 r + C := by
    have hfeq : (fun z : ℂ => Real.posLog ‖∑ j, (f z - A j)⁻¹‖ + C)
        = (fun z : ℂ => Real.posLog ‖∑ j, (f z - A j)⁻¹‖) + (fun _ : ℂ => C) := rfl
    rw [hfeq, Real.circleAverage_add hintF hconstint, Real.circleAverage_const]
  rw [hsum, proximity_top]
  rw [hconst] at hmono
  exact hmono

/-- Circle integrability of the proximity integrand, from meromorphy of the reciprocal. -/
theorem circleIntegrable_posLog_inv_sub_const {f : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (hf : MeromorphicOn (fun z => (f z - a)⁻¹) (sphere (0 : ℂ) |r|)) :
    CircleIntegrable (fun z => Real.posLog ‖f z - a‖⁻¹) 0 r := by
  have h := hf.circleIntegrable_posLog_norm
  simpa [norm_inv] using h

/-- **The separation estimate for a meromorphic function.**  The integrability side conditions are
discharged from meromorphy of the reciprocals. -/
theorem sum_proximity_le_of_meromorphic {f : ℂ → ℂ} {q : ℕ} (A : Fin q → ℂ) {δ r : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Fin q, i ≠ j → δ ≤ ‖A i - A j‖)
    (hmero : ∀ j : Fin q, MeromorphicOn (fun z => (f z - A j)⁻¹) (sphere (0 : ℂ) |r|)) :
    ∑ j, proximity f (A j : WithTop ℂ) r
      ≤ proximity (fun z => ∑ j, (f z - A j)⁻¹) ⊤ r
        + ((q : ℝ) * Real.posLog (2 / δ) + Real.posLog ((q : ℝ) * (2 / δ)) + Real.log 2) := by
  classical
  have hmeroF : MeromorphicOn (fun z => ∑ j, (f z - A j)⁻¹) (sphere (0 : ℂ) |r|) := by
    have h := MeromorphicOn.sum (s := (Finset.univ : Finset (Fin q)))
      (f := fun j z => (f z - A j)⁻¹) (fun j _ => hmero j)
    have hfeq : (fun z : ℂ => ∑ j, (f z - A j)⁻¹) = ∑ j, fun z : ℂ => (f z - A j)⁻¹ := by
      funext z
      simp [Finset.sum_apply]
    rw [hfeq]
    exact h
  exact sum_proximity_le A hδ hsep (fun j => circleIntegrable_posLog_inv_sub_const (hmero j))
    hmeroF.circleIntegrable_posLog_norm

end GaloisForLFunctions.HTGeometry
