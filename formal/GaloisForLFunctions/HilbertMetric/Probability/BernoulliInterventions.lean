import GaloisForLFunctions.HTGeometry.ConstitutiveHierarchicalMaximalCoupling

/-!
# Bernoulli intervention couplings

An intervention on a binary outcome leaves one free entry in the joint law.
The two failure marginals give the exact interval of rescue probabilities,
as in Jin and Cha (arXiv:2611.25397, §3.3). The same parametrization identifies
the unique coupling minimizing the probability of any outcome change.
-/

open scoped NNReal

namespace GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions

open _root_.HTGeometry

noncomputable section

/-- A probability specified as a nonnegative mass bounded by one. -/
abbrev Probability := Set.Iic (1 : ℝ≥0)

/-- Binary failure law, with `true` representing failure. -/
def failureLaw (p : Probability) : Bool → ℝ≥0
  | false => 1 - p.1
  | true => p.1

/-- Joint law of factual and intervened outcomes. -/
abbrev Pairing (p q : Probability) := FiniteNNCoupling (failureLaw p) (failureLaw q)

/-- The factual outcome fails and the intervened outcome succeeds. -/
def rescue {p q : Probability} (C : Pairing p q) : ℝ := C.plan true false

/-- The factual outcome succeeds and the intervened outcome fails. -/
def harm {p q : Probability} (C : Pairing p q) : ℝ := C.plan false true

private def mass (p : Probability) : ℝ := p.1

private theorem mass_nonneg (p : Probability) : 0 ≤ mass p := p.1.2

private theorem mass_le_one (p : Probability) : mass p ≤ 1 := by
  change (p.1 : ℝ) ≤ 1
  exact_mod_cast (show p.1 ≤ 1 from p.2)

private theorem coe_failureLaw_false (p : Probability) :
    (failureLaw p false : ℝ) = 1 - mass p := by
  exact NNReal.coe_sub p.2

private theorem row_true {p q : Probability} (C : Pairing p q) :
    rescue C + (C.plan true true : ℝ) = mass p := by
  have h := C.row true
  rw [Fintype.sum_bool, add_comm] at h
  change (C.plan true false : ℝ) + (C.plan true true : ℝ) = (p.1 : ℝ)
  exact_mod_cast h

private theorem col_true {p q : Probability} (C : Pairing p q) :
    harm C + (C.plan true true : ℝ) = mass q := by
  have h := C.col true
  rw [Fintype.sum_bool, add_comm] at h
  change (C.plan false true : ℝ) + (C.plan true true : ℝ) = (q.1 : ℝ)
  exact_mod_cast h

private theorem col_false {p q : Probability} (C : Pairing p q) :
    (C.plan false false : ℝ) + rescue C = 1 - mass q := by
  rw [← coe_failureLaw_false]
  have h := C.col false
  rw [Fintype.sum_bool, add_comm] at h
  change (C.plan false false : ℝ) + (C.plan true false : ℝ) = (failureLaw q false : ℝ)
  exact_mod_cast h

/-- The signed change in failure rate is independent of the pairing. -/
theorem rescue_sub_harm {p q : Probability} (C : Pairing p q) :
    rescue C - harm C = (p.1 : ℝ) - q.1 := by
  change rescue C - harm C = mass p - mass q
  linarith only [row_true C, col_true C]

/-- Any pairing changes outcomes on at least the absolute net change in failure mass. -/
theorem disagreement_ge {p q : Probability} (C : Pairing p q) :
    |(p.1 : ℝ) - q.1| ≤ rescue C + harm C := by
  rw [← rescue_sub_harm C, abs_le]
  constructor
  · linarith only [show 0 ≤ rescue C from (C.plan true false).2]
  · linarith only [show 0 ≤ harm C from (C.plan false true).2]

private def cells (p q x : ℝ) : Bool → Bool → ℝ
  | false, false => 1 - q - x
  | false, true => q - p + x
  | true, false => x
  | true, true => p - x

/-- The rescue entry determines every other entry of the joint law. -/
theorem pairing_ext {p q : Probability} {C D : Pairing p q}
    (h : rescue C = rescue D) : C = D := by
  have entry (A : Pairing p q) (a b : Bool) :
      (A.plan a b : ℝ) = cells (mass p) (mass q) (rescue A) a b := by
    cases a <;> cases b
    · simp only [cells]
      linarith only [col_false A]
    · simp only [cells]
      linarith only [row_true A, col_true A, show (A.plan false true : ℝ) = harm A from rfl]
    · rfl
    · simp only [cells]
      linarith only [row_true A]
  have he : C.plan = D.plan := by
    funext a b
    apply NNReal.eq
    rw [entry, entry, h]
  cases C
  cases D
  cases he
  rfl

/-- Exact feasible interval for the fraction of shots rescued by an intervention. -/
theorem range_rescue (p q : Probability) :
    Set.range (rescue (p := p) (q := q)) =
      Set.Icc (max 0 ((p.1 : ℝ) - q.1)) (min (p.1 : ℝ) (1 - q.1)) := by
  ext x
  constructor
  · rintro ⟨C, rfl⟩
    change max 0 (mass p - mass q) ≤ rescue C ∧ rescue C ≤ min (mass p) (1 - mass q)
    refine ⟨max_le (C.plan true false).2 ?_, le_min ?_ ?_⟩
    · linarith only [row_true C, col_true C, show 0 ≤ harm C from (C.plan false true).2]
    · linarith only [row_true C, (C.plan true true).2]
    · linarith only [col_false C, (C.plan false false).2]
  · intro hx
    change max 0 (mass p - mass q) ≤ x ∧ x ≤ min (mass p) (1 - mass q) at hx
    have hnn (a b : Bool) : 0 ≤ cells (mass p) (mass q) x a b := by
      cases a <;> cases b
      · exact sub_nonneg.mpr ((le_min_iff.mp hx.2).2)
      · linarith only [(max_le_iff.mp hx.1).2]
      · exact (max_le_iff.mp hx.1).1
      · exact sub_nonneg.mpr ((le_min_iff.mp hx.2).1)
    let C : Pairing p q := {
      plan := fun a b => ⟨cells (mass p) (mass q) x a b, hnn a b⟩
      row := by
        intro a
        rw [Fintype.sum_bool, add_comm]
        apply NNReal.eq
        cases a
        · simp only [NNReal.coe_add, coe_failureLaw_false]
          change (1 - mass q - x) + (mass q - mass p + x) = 1 - mass p
          ring
        · simp only [NNReal.coe_add]
          change x + (mass p - x) = mass p
          ring
      col := by
        intro b
        rw [Fintype.sum_bool, add_comm]
        apply NNReal.eq
        cases b
        · simp only [NNReal.coe_add, coe_failureLaw_false]
          change (1 - mass q - x) + x = 1 - mass q
          ring
        · simp only [NNReal.coe_add]
          change (mass q - mass p + x) + (mass p - x) = mass q
          ring }
    exact ⟨C, rfl⟩

/-- The minimum possible probability of an outcome change is the distance
between the marginals. Exactly one joint law attains it. -/
theorem existsUnique_minimum_disagreement (p q : Probability) :
    ∃! C : Pairing p q, rescue C + harm C = |(p.1 : ℝ) - q.1| := by
  let x := max 0 (mass p - mass q)
  have hx : x ∈ Set.range (rescue (p := p) (q := q)) := by
    rw [range_rescue]
    change x ≤ x ∧ x ≤ min (mass p) (1 - mass q)
    refine ⟨le_rfl, le_min (max_le (mass_nonneg p) ?_) (max_le ?_ ?_)⟩
    · linarith only [mass_nonneg q]
    · linarith only [mass_le_one q]
    · linarith only [mass_le_one p]
  obtain ⟨C, hC⟩ := hx
  have hD (D : Pairing p q) :
      rescue D + harm D = |mass p - mass q| ↔ rescue D = x := by
    have he : rescue D - harm D = mass p - mass q := rescue_sub_harm D
    by_cases h : 0 ≤ mass p - mass q
    · rw [abs_of_nonneg h, show x = mass p - mass q from max_eq_right h]
      constructor <;> intro h' <;> linarith only [he, h']
    · have h' := le_of_not_ge h
      rw [abs_of_nonpos h', show x = 0 from max_eq_left h']
      constructor <;> intro h'' <;> linarith only [he, h'']
  exact ⟨C, (hD C).2 hC, fun D h => pairing_ext ((hD D).1 h |>.trans hC.symm)⟩

/-- When both marginal probabilities are interior, there are two different
rescue rates for the same factual and intervened failure rates. -/
theorem interior_rescue_not_identified
    (p q : Set.Ioo (0 : ℝ≥0) 1) :
    let p' : Probability := ⟨p.1, p.2.2.le⟩
    let q' : Probability := ⟨q.1, q.2.2.le⟩
    ∃ C D : Pairing p' q', rescue C < rescue D := by
  dsimp only
  let p' : Probability := ⟨p.1, p.2.2.le⟩
  let q' : Probability := ⟨q.1, q.2.2.le⟩
  let l := max 0 (mass p' - mass q')
  let u := min (mass p') (1 - mass q')
  have hp0 : 0 < mass p' := by change 0 < (p.1 : ℝ); exact_mod_cast p.2.1
  have hq0 : 0 < mass q' := by change 0 < (q.1 : ℝ); exact_mod_cast q.2.1
  have hp1 : mass p' < 1 := by change (p.1 : ℝ) < 1; exact_mod_cast p.2.2
  have hq1 : mass q' < 1 := by change (q.1 : ℝ) < 1; exact_mod_cast q.2.2
  have hlu : l < u := by
    exact lt_min (max_lt hp0 (by linarith only [hq0]))
      (max_lt (by linarith only [hq1]) (by linarith only [hp1]))
  obtain ⟨C, hC⟩ : l ∈ Set.range (rescue (p := p') (q := q')) := by
    rw [range_rescue]
    exact ⟨le_rfl, hlu.le⟩
  obtain ⟨D, hD⟩ : u ∈ Set.range (rescue (p := p') (q := q')) := by
    rw [range_rescue]
    exact ⟨hlu.le, le_rfl⟩
  exact ⟨C, D, by rw [hC, hD]; exact hlu⟩

#print axioms rescue_sub_harm
#print axioms disagreement_ge
#print axioms range_rescue
#print axioms existsUnique_minimum_disagreement
#print axioms interior_rescue_not_identified

end

end GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions
