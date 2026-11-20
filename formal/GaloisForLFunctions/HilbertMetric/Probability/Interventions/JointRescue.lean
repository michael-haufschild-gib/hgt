import GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions

/-!
# Sharp joint rescue bounds with fixed pairings

The cause-count distinction in Jin and Cha (arXiv:2611.25397, Table 2) already
appears for two interventions. A coupling on each factual row glues the two
fixed factual--intervention laws. The row on failures has exactly a Fréchet
interval of possible joint rescues, including when the factual failure mass is zero.
-/

open scoped BigOperators NNReal

namespace GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions

open _root_.HTGeometry

noncomputable section

/-- A joint law of both counterfactuals, retaining the two pairings with the
factual outcome. Each factual row couples the two counterfactual rows. -/
abbrev JointPairing {p q r : FailureRate} (C : Pairing p q) (D : Pairing p r) :=
  ∀ f : Bool, FiniteNNCoupling (C.plan f) (D.plan f)

/-- The factual run fails and both single interventions rescue it. -/
def bothRescued {p q r : FailureRate} {C : Pairing p q} {D : Pairing p r}
    (J : JointPairing C D) : ℝ := (J true).plan false false

/-- The factual run fails and at least one single intervention rescues it. -/
def someRescued {p q r : FailureRate} {C : Pairing p q} {D : Pairing p r}
    (J : JointPairing C D) : ℝ :=
  (J true).plan false false + ((J true).plan false true : ℝ) + (J true).plan true false

private theorem sum_row {u v : Bool → ℝ≥0} (J : FiniteNNCoupling u v) (a : Bool) :
    (J.plan a false : ℝ) + J.plan a true = (u a : ℝ) := by
  have h := J.row a
  rw [Fintype.sum_bool, add_comm] at h
  exact_mod_cast h

private theorem sum_col {u v : Bool → ℝ≥0} (J : FiniteNNCoupling u v) (b : Bool) :
    (J.plan false b : ℝ) + J.plan true b = (v b : ℝ) := by
  have h := J.col b
  rw [Fintype.sum_bool, add_comm] at h
  exact_mod_cast h

private theorem sliceRange (u v : Bool → ℝ≥0) (m : ℝ)
    (hu : (u false : ℝ) + u true = m) (hv : (v false : ℝ) + v true = m) :
    Set.range (fun J : FiniteNNCoupling u v => (J.plan false false : ℝ)) =
      Set.Icc (max 0 ((u false : ℝ) + v false - m)) (min (u false : ℝ) (v false : ℝ)) := by
  ext x
  constructor
  · rintro ⟨J, rfl⟩
    exact ⟨max_le (J.plan false false).2
        (by linarith only [hu, sum_row J true, sum_row J false, sum_col J false,
          (J.plan true true).2]),
      le_min (by linarith only [sum_row J false, (J.plan false true).2])
        (by linarith only [sum_col J false, (J.plan true false).2])⟩
  · intro hx
    let t : Bool → Bool → ℝ
      | false, false => x
      | false, true => (u false : ℝ) - x
      | true, false => (v false : ℝ) - x
      | true, true => m - (u false : ℝ) - v false + x
    have hnn (a b : Bool) : 0 ≤ t a b := by
      cases a <;> cases b
      · exact (max_le_iff.mp hx.1).1
      · exact sub_nonneg.mpr ((le_min_iff.mp hx.2).1)
      · exact sub_nonneg.mpr ((le_min_iff.mp hx.2).2)
      · change 0 ≤ m - (u false : ℝ) - v false + x
        linarith only [(max_le_iff.mp hx.1).2]
    let J : FiniteNNCoupling u v := {
      plan := fun a b => ⟨t a b, hnn a b⟩
      row := by
        intro a
        rw [Fintype.sum_bool]
        apply NNReal.eq
        simp only [NNReal.coe_add]
        cases a
        · change (u false : ℝ) - x + x = u false
          ring
        · change (m - (u false : ℝ) - v false + x) + ((v false : ℝ) - x) = u true
          linarith only [hu]
      col := by
        intro b
        rw [Fintype.sum_bool]
        apply NNReal.eq
        simp only [NNReal.coe_add]
        cases b
        · change (v false : ℝ) - x + x = v false
          ring
        · change (m - (u false : ℝ) - v false + x) + ((u false : ℝ) - x) = v true
          linarith only [hv] }
    exact ⟨J, rfl⟩

/-- The total mass of a factual row in either fixed pairing. -/
private theorem factualRow {p q : FailureRate} (C : Pairing p q) (f : Bool) :
    (C.plan f false : ℝ) + C.plan f true = (failureLaw p f : ℝ) :=
  sum_row C f

/-- The complete range of the two-cause tail under fixed individual pairings. -/
theorem range_bothRescued {p q r : FailureRate} (C : Pairing p q) (D : Pairing p r) :
    Set.range (bothRescued (C := C) (D := D)) =
      Set.Icc (max 0 (rescue C + rescue D - (p.1 : ℝ))) (min (rescue C) (rescue D)) := by
  ext x
  have hslice : Set.range (fun J : FiniteNNCoupling (C.plan true) (D.plan true) =>
      (J.plan false false : ℝ)) =
      Set.Icc (max 0 (rescue C + rescue D - (p.1 : ℝ))) (min (rescue C) (rescue D)) :=
    sliceRange (C.plan true) (D.plan true) (p.1 : ℝ) (factualRow C true) (factualRow D true)
  constructor
  · rintro ⟨J, rfl⟩
    rw [← hslice]
    exact ⟨J true, rfl⟩
  · intro hx
    rw [← hslice] at hx
    obtain ⟨J₁, hJ₁⟩ := hx
    let m : ℝ := (failureLaw p false : ℝ)
    let a : ℝ := (C.plan false false : ℝ)
    let b : ℝ := (D.plan false false : ℝ)
    have ha : a ≤ m := by linarith only [factualRow C false, (C.plan false true).2]
    have hb : b ≤ m := by linarith only [factualRow D false, (D.plan false true).2]
    have hfeasible : max 0 (a + b - m) ≤ min a b :=
      le_min (max_le (C.plan false false).2 (by linarith only [hb]))
        (max_le (D.plan false false).2 (by linarith only [ha]))
    have h0 := sliceRange (C.plan false) (D.plan false) m (factualRow C false) (factualRow D false)
    have h0' : min a b ∈ Set.range (fun J : FiniteNNCoupling (C.plan false) (D.plan false) =>
        (J.plan false false : ℝ)) := by
      rw [h0]
      exact ⟨hfeasible, le_rfl⟩
    obtain ⟨J₀, _⟩ := h0'
    let J : JointPairing C D
      | false => J₀
      | true => J₁
    exact ⟨J, hJ₁⟩

/-- Inclusion-exclusion in the factual failure row. The sum of the two
rescue rates is fixed even as the joint tail varies. -/
theorem someRescued_add_bothRescued {p q r : FailureRate}
    {C : Pairing p q} {D : Pairing p r} (J : JointPairing C D) :
    someRescued J + bothRescued J = rescue C + rescue D := by
  change (↑((J true).plan false false) + ↑((J true).plan false true) +
    ↑((J true).plan true false)) + ↑((J true).plan false false) =
      (C.plan true false : ℝ) + (D.plan true false : ℝ)
  linarith only [sum_row (J true) false, sum_col (J true) false]

/-- The complete range of the one-or-more-cause tail under the same pairings. -/
theorem range_someRescued {p q r : FailureRate} (C : Pairing p q) (D : Pairing p r) :
    Set.range (someRescued (C := C) (D := D)) =
      Set.Icc (max (rescue C) (rescue D)) (min (p.1 : ℝ) (rescue C + rescue D)) := by
  let a := rescue C
  let b := rescue D
  let m : ℝ := p.1
  have hlow : a + b - min a b = max a b := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h]
      ring
    · rw [min_eq_right h, max_eq_left h]
      ring
  have hhigh : a + b - max 0 (a + b - m) = min m (a + b) := by
    rcases le_total (a+b) m with h | h
    · rw [max_eq_left (sub_nonpos.mpr h), min_eq_right h, sub_zero]
    · rw [max_eq_right (sub_nonneg.mpr h), min_eq_left h]
      ring
  ext y
  change y ∈ Set.range (someRescued (C := C) (D := D)) ↔
    y ∈ Set.Icc (max a b) (min m (a+b))
  rw [← hlow, ← hhigh]
  constructor
  · rintro ⟨J, rfl⟩
    have hb : bothRescued J ∈ Set.range (bothRescued (C := C) (D := D)) := ⟨J, rfl⟩
    rw [range_bothRescued] at hb
    have h : someRescued J + bothRescued J = a + b := someRescued_add_bothRescued J
    exact ⟨by linarith only [h, hb.2], by linarith only [h, hb.1]⟩
  · intro hy
    have hx : a+b-y ∈ Set.range (bothRescued (C := C) (D := D)) := by
      rw [range_bothRescued]
      exact ⟨by linarith only [hy.2], by linarith only [hy.1]⟩
    obtain ⟨J, hJ⟩ := hx
    have h : someRescued J + bothRescued J = a + b := someRescued_add_bothRescued J
    exact ⟨J, by linarith only [hJ, h]⟩

#print axioms range_bothRescued
#print axioms someRescued_add_bothRescued
#print axioms range_someRescued

end

end GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions
