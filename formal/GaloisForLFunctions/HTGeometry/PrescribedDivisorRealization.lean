import Mathlib
import GaloisForLFunctions.HTGeometry.WeierstrassFactorizationTheorem

/-!
# Realization of a prescribed divisor on `ℂ`

Zeros are realized by a Weierstrass product and poles by the reciprocal of another, so a quotient of
two such products is a meromorphic function whose zero set and pole set are exactly the two
prescribed sequences, provided they are disjoint.  Multiplicities are encoded by repetitions.

The only inputs are that the two sequences are nonzero, tend to infinity, and are disjoint from one
another; nothing about their distribution is assumed.
-/

namespace GaloisForLFunctions

open Complex Filter Topology Set

noncomputable section

/-- The meromorphic function attached to a zero sequence and a pole sequence. -/
def divisorFunction (a b : ℕ → ℂ) : ℂ → ℂ :=
  weierstrassGenusProduct a / weierstrassGenusProduct b

/-- No countable family of points exhausts the plane. -/
theorem exists_notMem_range (b : ℕ → ℂ) : ∃ z : ℂ, z ∉ Set.range b := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have huniv : Set.range b = Set.univ := Set.eq_univ_of_forall hcon
  have hc : (Set.univ : Set ℂ).Countable := huniv ▸ Set.countable_range b
  refine Cardinal.not_countable_real ?_
  have hmap : (Set.univ : Set ℝ) ⊆ (fun z : ℂ => z.re) '' Set.univ := by
    intro x _
    exact ⟨(x : ℂ), Set.mem_univ _, by simp⟩
  exact Set.Countable.mono hmap (hc.image _)

/-- **The Weierstrass product is nowhere locally zero.** -/
theorem analyticOrderAt_weierstrassGenusProduct_ne_top {b : ℕ → ℂ}
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0) (z : ℂ) :
    analyticOrderAt (weierstrassGenusProduct b) z ≠ ⊤ := by
  obtain ⟨w, hw⟩ := exists_notMem_range b
  have hwne : weierstrassGenusProduct b w ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := (weierstrassGenusProduct_eq_zero_iff hb hbne w).mp h
    exact hw ⟨n, hn.symm⟩
  have han : AnalyticOnNhd ℂ (weierstrassGenusProduct b) Set.univ := fun x _ =>
    (differentiable_weierstrassGenusProduct hb hbne).analyticAt x
  refine han.analyticOrderAt_ne_top_of_isPreconnected (isPreconnected_univ)
    (Set.mem_univ w) (Set.mem_univ z) ?_
  rw [analyticOrderAt_eq_zero.mpr (Or.inr hwne)]
  exact (by norm_num : (0 : ℕ∞) ≠ ⊤)

theorem meromorphicOrderAt_weierstrassGenusProduct_ne_top {b : ℕ → ℂ}
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0) (z : ℂ) :
    meromorphicOrderAt (weierstrassGenusProduct b) z ≠ ⊤ := by
  rw [((differentiable_weierstrassGenusProduct hb hbne).analyticAt z).meromorphicOrderAt_eq]
  intro h
  exact analyticOrderAt_weierstrassGenusProduct_ne_top hb hbne z (by simpa using h)

/-- Negation of a finite positive order is negative. -/
theorem withTop_zero_sub_neg {x : WithTop ℤ} (hx : 0 < x) (htop : x ≠ ⊤) :
    (0 : WithTop ℤ) - x < 0 := by
  obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp htop
  have hn : (0 : ℤ) < n := by exact_mod_cast hx
  have h1 : (0 : WithTop ℤ) - ((n : ℤ) : WithTop ℤ) = ((-n : ℤ) : WithTop ℤ) := by
    rw [zero_sub]
    rfl
  rw [h1]
  have h2 : ((-n : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) := by
    exact_mod_cast (by linarith : (-n : ℤ) < 0)
  simpa using h2

/-- The two Weierstrass products are meromorphic on the plane. -/
theorem meromorphicOn_divisorFunction {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0) :
    MeromorphicOn (divisorFunction a b) Set.univ := by
  intro z _
  exact (((differentiable_weierstrassGenusProduct ha hane).analyticAt z).meromorphicAt).div
    (((differentiable_weierstrassGenusProduct hb hbne).analyticAt z).meromorphicAt)

/-- **The order of the realized function.**  With disjoint zero and pole sequences, the order at a
point is the order of the zero product minus the order of the pole product. -/
theorem meromorphicOrderAt_divisorFunction {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0) (z : ℂ) :
    meromorphicOrderAt (divisorFunction a b) z
      = meromorphicOrderAt (weierstrassGenusProduct a) z
        - meromorphicOrderAt (weierstrassGenusProduct b) z := by
  refine meromorphicOrderAt_div
    (((differentiable_weierstrassGenusProduct ha hane).analyticAt z).meromorphicAt)
    (((differentiable_weierstrassGenusProduct hb hbne).analyticAt z).meromorphicAt)

/-- **Away from both sequences the realized function is a unit.** -/
theorem meromorphicOrderAt_divisorFunction_eq_zero {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    {z : ℂ} (hza : z ∉ Set.range a) (hzb : z ∉ Set.range b) :
    meromorphicOrderAt (divisorFunction a b) z = 0 := by
  have hnum : weierstrassGenusProduct a z ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := (weierstrassGenusProduct_eq_zero_iff ha hane z).mp h
    exact hza ⟨n, hn.symm⟩
  have hden : weierstrassGenusProduct b z ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := (weierstrassGenusProduct_eq_zero_iff hb hbne z).mp h
    exact hzb ⟨n, hn.symm⟩
  have hnum0 : meromorphicOrderAt (weierstrassGenusProduct a) z = 0 := by
    rw [((differentiable_weierstrassGenusProduct ha hane).analyticAt z).meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (Or.inr hnum)]
    rfl
  have hden0 : meromorphicOrderAt (weierstrassGenusProduct b) z = 0 := by
    rw [((differentiable_weierstrassGenusProduct hb hbne).analyticAt z).meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (Or.inr hden)]
    rfl
  rw [meromorphicOrderAt_divisorFunction ha hane hb hbne, hnum0, hden0, sub_zero]

/-- **The zero set is exactly the first sequence.**  At a point of the zero sequence, disjoint from
the pole sequence, the realized function has strictly positive order. -/
theorem meromorphicOrderAt_divisorFunction_pos {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    {z : ℂ} (hza : z ∈ Set.range a) (hzb : z ∉ Set.range b) :
    0 < meromorphicOrderAt (divisorFunction a b) z := by
  obtain ⟨n, hn⟩ := hza
  have hnum : weierstrassGenusProduct a z = 0 :=
    (weierstrassGenusProduct_eq_zero_iff ha hane z).mpr ⟨n, hn.symm⟩
  have hden : weierstrassGenusProduct b z ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := (weierstrassGenusProduct_eq_zero_iff hb hbne z).mp h
    exact hzb ⟨m, hm.symm⟩
  have hden0 : meromorphicOrderAt (weierstrassGenusProduct b) z = 0 := by
    rw [((differentiable_weierstrassGenusProduct hb hbne).analyticAt z).meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (Or.inr hden)]
    rfl
  have hnumpos : 0 < meromorphicOrderAt (weierstrassGenusProduct a) z := by
    have han := (differentiable_weierstrassGenusProduct ha hane).analyticAt z
    refine (tendsto_zero_iff_meromorphicOrderAt_pos han.meromorphicAt).mp ?_
    have hc : ContinuousWithinAt (weierstrassGenusProduct a) {z}ᶜ z :=
      han.continuousAt.continuousWithinAt
    rw [ContinuousWithinAt, hnum] at hc
    exact hc
  rw [meromorphicOrderAt_divisorFunction ha hane hb hbne, hden0, sub_zero]
  exact hnumpos

/-- **The pole set is exactly the second sequence.** -/
theorem meromorphicOrderAt_divisorFunction_neg {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    {z : ℂ} (hza : z ∉ Set.range a) (hzb : z ∈ Set.range b) :
    meromorphicOrderAt (divisorFunction a b) z < 0 := by
  obtain ⟨n, hn⟩ := hzb
  have hden : weierstrassGenusProduct b z = 0 :=
    (weierstrassGenusProduct_eq_zero_iff hb hbne z).mpr ⟨n, hn.symm⟩
  have hnum : weierstrassGenusProduct a z ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := (weierstrassGenusProduct_eq_zero_iff ha hane z).mp h
    exact hza ⟨m, hm.symm⟩
  have hnum0 : meromorphicOrderAt (weierstrassGenusProduct a) z = 0 := by
    rw [((differentiable_weierstrassGenusProduct ha hane).analyticAt z).meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (Or.inr hnum)]
    rfl
  have hdenpos : 0 < meromorphicOrderAt (weierstrassGenusProduct b) z := by
    have han := (differentiable_weierstrassGenusProduct hb hbne).analyticAt z
    refine (tendsto_zero_iff_meromorphicOrderAt_pos han.meromorphicAt).mp ?_
    have hc : ContinuousWithinAt (weierstrassGenusProduct b) {z}ᶜ z :=
      han.continuousAt.continuousWithinAt
    rw [ContinuousWithinAt, hden] at hc
    exact hc
  rw [meromorphicOrderAt_divisorFunction ha hane hb hbne, hnum0]
  exact withTop_zero_sub_neg hdenpos (meromorphicOrderAt_weierstrassGenusProduct_ne_top hb hbne z)

end

end GaloisForLFunctions
