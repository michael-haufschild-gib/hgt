import GaloisForLFunctions.HTGeometry.Octonion.Alternative

namespace GaloisForLFunctions.HTGeometry.Octonion

/-- Bracketed words in two generators, used in Artin's theorem. -/
inductive ArtinWord where
  | atom : Bool → ArtinWord
  | prod : ArtinWord → ArtinWord → ArtinWord
deriving DecidableEq

namespace ArtinWord

def degree : ArtinWord → ℕ
  | atom _ => 1
  | prod u v => degree u + degree v

def head : ArtinWord → Bool
  | atom x => x
  | prod u _ => head u

def tail : ArtinWord → Option ArtinWord
  | atom _ => none
  | prod u v =>
      match tail u with
      | none => some v
      | some t => some (prod t v)

theorem degree_pos (w : ArtinWord) : 0 < degree w := by
  induction w with
  | atom => simp [degree]
  | prod u v ihu ihv => exact Nat.add_pos_left ihu _

theorem tail_prod_ne_none (u v : ArtinWord) : tail (prod u v) ≠ none := by
  simp only [tail]
  split <;> simp

theorem tail_eq_none_iff (w : ArtinWord) : tail w = none ↔ ∃ x, w = atom x := by
  cases w with
  | atom x => simp [tail]
  | prod u v =>
      constructor
      · intro h
        exact False.elim (tail_prod_ne_none u v h)
      · rintro ⟨x, h⟩
        cases h

theorem tail_degree {w t : ArtinWord} (h : tail w = some t) : degree t + 1 = degree w := by
  induction w generalizing t with
  | atom b => simp [tail] at h
  | prod u v ihu =>
      simp only [tail] at h
      split at h <;> rename_i hu
      · have hvt : v = t := Option.some.inj h
        cases hvt
        have hu' := (tail_eq_none_iff u).mp hu
        obtain ⟨b, rfl⟩ := hu'
        exact Nat.add_comm _ _
      · have hvt : prod _ v = t := Option.some.inj h
        cases hvt
        have ht := ihu hu
        simp only [degree]
        omega

theorem prod_has_tail (u v : ArtinWord) : ∃ t, tail (prod u v) = some t := by
  simp only [tail]
  split <;> rename_i h
  · exact ⟨v, rfl⟩
  · exact ⟨_, rfl⟩

variable {M : Type*} [NonUnitalNonAssocRing M]

def letter (a b : M) : Bool → M
  | false => a
  | true => b

def eval (a b : M) : ArtinWord → M
  | atom x => letter a b x
  | prod u v => eval a b u * eval a b v

@[simp] theorem eval_atom (a b : M) (x : Bool) : eval a b (atom x) = letter a b x := rfl
@[simp] theorem eval_prod (a b : M) (u v : ArtinWord) :
    eval a b (prod u v) = eval a b u * eval a b v := rfl

theorem eval_eq_head_mul_tail_of_lower [IsAlternative M] (a b : M) (n : ℕ)
    (H : ∀ u v z : ArtinWord,
      degree u + degree v + degree z < n →
        IsAlternative.associator (eval a b u) (eval a b v) (eval a b z) = 0)
    {w t : ArtinWord} (ht : tail w = some t) (hw : degree w < n) :
    eval a b w = letter a b (head w) * eval a b t := by
  induction w generalizing t with
  | atom x => simp [tail] at ht
  | prod u v ihu ihv =>
      simp only [tail] at ht
      split at ht <;> rename_i t₁ hu
      · have hvt : v = t := Option.some.inj ht
        cases hvt
        have hu' := (tail_eq_none_iff u).mp hu
        obtain ⟨x, rfl⟩ := hu'
        rfl
      · have hvt : prod t₁ v = t := Option.some.inj ht
        cases hvt
        have hu_lt : degree u < n := by
          have hv_pos := degree_pos v
          simp only [degree] at hw
          omega
        have hsub := ihu hu hu_lt
        have hdeg := tail_degree hu
        have hassoc :
            IsAlternative.associator (letter a b (head u)) (eval a b t₁) (eval a b v) = 0 := by
          simpa only [eval_atom] using H (atom (head u)) t₁ v (by
            have hsum : degree (atom (head u)) + degree t₁ + degree v =
                degree (prod u v) := by
              simp only [degree]
              omega
            rw [hsum]
            exact hw)
        change eval a b u * eval a b v =
          letter a b (head u) * (eval a b t₁ * eval a b v)
        rw [hsub]
        exact sub_eq_zero.mp hassoc

/-- Artin's word theorem: every three bracketed words in two elements associate. -/
theorem all_words_associate [IsAlternative M] (a b : M) (p q r : ArtinWord) :
    IsAlternative.associator (eval a b p) (eval a b q) (eval a b r) = 0 := by
  have aux : ∀ n : ℕ, ∀ p q r : ArtinWord,
      degree p + degree q + degree r = n →
        IsAlternative.associator (eval a b p) (eval a b q) (eval a b r) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p q r hsum
      have Hlower : ∀ u v z : ArtinWord,
          degree u + degree v + degree z < n →
            IsAlternative.associator (eval a b u) (eval a b v) (eval a b z) = 0 := by
        intro u v z hlt
        exact ih _ hlt u v z rfl
      have common : ∀ p q r : ArtinWord,
          head q = head r → degree p + degree q + degree r = n →
            IsAlternative.associator (eval a b p) (eval a b q) (eval a b r) = 0 := by
        intro p q r hhead hsum
        cases q with
        | atom qx =>
          cases r with
          | atom rx =>
            simp only [head] at hhead
            cases hhead
            exact IsAlternative.associator_right_self _ _
          | prod ru rv =>
            obtain ⟨tr, htr⟩ := prod_has_tail ru rv
            have hr_lt : degree (prod ru rv) < n := by
              have hp_pos := degree_pos p
              simp only [degree] at hsum ⊢
              omega
            have er := eval_eq_head_mul_tail_of_lower a b n Hlower htr hr_lt
            simp only [head] at hhead er ⊢
            rw [← hhead] at er
            rw [er]
            simp only [eval_atom]
            rw [IsAlternative.associator_swap_last, IsAlternative.associator_right_mul_left]
            simp only [neg_mul, neg_neg]
            have hz := Hlower p (atom qx) tr (by
              have hdeg := tail_degree htr
              simp only [degree] at hsum hdeg ⊢
              omega)
            have hz' : IsAlternative.associator (eval a b p) (letter a b qx) (eval a b tr) = 0 :=
              by simpa only [eval_atom] using hz
            rw [hz']
            simp
        | prod qu qv =>
          obtain ⟨tq, htq⟩ := prod_has_tail qu qv
          have hq_lt : degree (prod qu qv) < n := by
            have hp_pos := degree_pos p
            have hr_pos := degree_pos r
            simp only [degree] at hsum ⊢
            omega
          have eq_q := eval_eq_head_mul_tail_of_lower a b n Hlower htq hq_lt
          cases r with
          | atom rx =>
            simp only [head] at hhead
            simp only [head] at eq_q
            rw [hhead] at eq_q
            rw [eq_q]
            simp only [eval_atom]
            rw [IsAlternative.associator_right_mul_left]
            have hz := Hlower p (atom rx) tq (by
              have hdeg := tail_degree htq
              simp only [degree] at hsum hdeg ⊢
              omega)
            have hz' : IsAlternative.associator (eval a b p) (letter a b rx) (eval a b tq) = 0 :=
              by simpa only [eval_atom] using hz
            rw [hz']
            simp
          | prod ru rv =>
            obtain ⟨tr, htr⟩ := prod_has_tail ru rv
            have hr_lt : degree (prod ru rv) < n := by
              have hp_pos := degree_pos p
              simp only [degree] at hsum ⊢
              omega
            have eq_r := eval_eq_head_mul_tail_of_lower a b n Hlower htr hr_lt
            simp only [head] at hhead
            simp only [head] at eq_q eq_r
            rw [hhead] at eq_q
            rw [eq_q, eq_r, IsAlternative.artin_common_prefix_reduction]
            have hqdeg := tail_degree htq
            have hrdeg := tail_degree htr
            have hz1 := Hlower (prod p tq) (atom (head ru)) tr (by
              have hp_pos := degree_pos p
              simp only [degree] at hsum hqdeg hrdeg ⊢
              omega)
            have hz2 := Hlower (prod (atom (head ru)) tr) (atom (head ru)) tq (by
              have hp_pos := degree_pos p
              simp only [degree] at hsum hqdeg hrdeg ⊢
              omega)
            have hz3 := Hlower (prod (atom (head ru)) tr) p tq (by
              have hp_pos := degree_pos p
              simp only [degree] at hsum hqdeg hrdeg ⊢
              omega)
            have h1 : IsAlternative.associator (eval a b p * eval a b tq)
                (letter a b (head ru)) (eval a b tr) = 0 := by
              simpa only [eval_prod, eval_atom] using hz1
            have h2 : IsAlternative.associator (letter a b (head ru) * eval a b tr)
                (letter a b (head ru)) (eval a b tq) = 0 := by
              simpa only [eval_prod, eval_atom] using hz2
            have h3 : IsAlternative.associator (letter a b (head ru) * eval a b tr)
                (eval a b p) (eval a b tq) = 0 := by
              simpa only [eval_prod, eval_atom] using hz3
            rw [h1, h2, h3]
            simp
      by_cases hpq : head p = head q
      · calc
          IsAlternative.associator (eval a b p) (eval a b q) (eval a b r) =
              IsAlternative.associator (eval a b q) (eval a b r) (eval a b p) :=
                IsAlternative.associator_cyclic _ _ _
          _ = IsAlternative.associator (eval a b r) (eval a b p) (eval a b q) :=
                IsAlternative.associator_cyclic _ _ _
          _ = 0 := common r p q hpq (by omega)
      · by_cases hqr : head q = head r
        · exact common p q r hqr hsum
        · have hpr : head p = head r := by
            cases hp : head p <;> cases hq : head q <;> cases hr : head r <;> simp_all
          rw [IsAlternative.associator_swap_first]
          rw [common q p r hpr (by omega)]
          simp
  exact aux _ p q r rfl

end ArtinWord
end GaloisForLFunctions.HTGeometry.Octonion
