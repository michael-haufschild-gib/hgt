import Mathlib

/-!
# Degree bookkeeping for differential polynomials

A differential polynomial in `MvPolynomial (Fin (n + 2)) ℂ` has slot `0` for the point variable and
slot `j + 1` for the `j`-th jet.  Two numbers control every monomial: the total jet degree
`∑ⱼ m (j+1)` and the combined weight `m 0 + ∑ⱼ j · m (j+1)`, which bounds both the power of the
point variable and the weighted differentiation order at once.  Both are additive under
multiplication, so the bookkeeping propagates through arbitrary substitutions.
-/

open MvPolynomial Finset

namespace GaloisForLFunctions.HTGeometry

/-- `JetBd n r V Q` records that every monomial of `Q` has total jet degree at most `r` and
combined point-and-order weight at most `V`. -/
structure JetBd (n r V : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) : Prop where
  deg : ∀ m ∈ Q.support, ∑ j : Fin (n + 1), m j.succ ≤ r
  wt : ∀ m ∈ Q.support, m 0 + ∑ j : Fin (n + 1), (j : ℕ) * m j.succ ≤ V

namespace JetBd

variable {n r V r' V' : ℕ} {Q Q₁ Q₂ : MvPolynomial (Fin (n + 2)) ℂ}

theorem mono (h : JetBd n r V Q) (hr : r ≤ r') (hV : V ≤ V') : JetBd n r' V' Q :=
  ⟨fun m hm => le_trans (h.deg m hm) hr, fun m hm => le_trans (h.wt m hm) hV⟩

theorem of_support_empty (h : Q.support = ∅) : JetBd n 0 0 Q :=
  ⟨fun m hm => absurd hm (by rw [h]; simp), fun m hm => absurd hm (by rw [h]; simp)⟩

theorem zero : JetBd n 0 0 (0 : MvPolynomial (Fin (n + 2)) ℂ) :=
  of_support_empty (by simp)

theorem C_bd (c : ℂ) : JetBd n 0 0 (MvPolynomial.C c : MvPolynomial (Fin (n + 2)) ℂ) := by
  classical
  have hsupp : (MvPolynomial.C c : MvPolynomial (Fin (n + 2)) ℂ).support ⊆ {0} := by
    rw [MvPolynomial.support_C]
    split <;> simp
  constructor <;>
  · intro m hm
    have : m = 0 := by simpa using hsupp hm
    subst this
    simp

theorem X_zero : JetBd n 0 1 (MvPolynomial.X 0 : MvPolynomial (Fin (n + 2)) ℂ) := by
  classical
  have hsupp := MvPolynomial.support_X (R := ℂ) (n := (0 : Fin (n + 2)))
  constructor
  · intro m hm
    rw [hsupp, Finset.mem_singleton] at hm
    subst hm
    refine le_of_eq (Finset.sum_eq_zero fun j _ => ?_)
    rw [Finsupp.single_apply, if_neg (Fin.succ_ne_zero j).symm]
  · intro m hm
    rw [hsupp, Finset.mem_singleton] at hm
    subst hm
    have h1 : ∀ j : Fin (n + 1), (j : ℕ) * (Finsupp.single (0 : Fin (n + 2)) 1) j.succ = 0 := by
      intro j
      rw [Finsupp.single_apply, if_neg (Fin.succ_ne_zero j).symm, mul_zero]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_const_zero, add_zero,
      Finsupp.single_apply, if_pos rfl]

theorem X_succ (j : Fin (n + 1)) :
    JetBd n 1 (j : ℕ) (MvPolynomial.X j.succ : MvPolynomial (Fin (n + 2)) ℂ) := by
  classical
  have hsupp := MvPolynomial.support_X (R := ℂ) (n := j.succ)
  have hkey : ∀ (i : Fin (n + 1)),
      (Finsupp.single (j.succ : Fin (n + 2)) 1) i.succ = if j = i then 1 else 0 := by
    intro i
    rw [Finsupp.single_apply]
    by_cases h : j = i
    · subst h; simp
    · rw [if_neg (fun hc => h (Fin.succ_injective _ hc)), if_neg h]
  constructor
  · intro m hm
    rw [hsupp, Finset.mem_singleton] at hm
    subst hm
    rw [Finset.sum_congr rfl (fun i _ => hkey i)]
    simp
  · intro m hm
    rw [hsupp, Finset.mem_singleton] at hm
    subst hm
    have h0 : (Finsupp.single (j.succ : Fin (n + 2)) 1) 0 = 0 := by
      rw [Finsupp.single_apply, if_neg (Fin.succ_ne_zero j)]
    rw [h0, zero_add,
      Finset.sum_congr rfl (fun i _ => by rw [hkey i])]
    simp

theorem add (h₁ : JetBd n r V Q₁) (h₂ : JetBd n r V Q₂) : JetBd n r V (Q₁ + Q₂) := by
  classical
  constructor <;>
  · intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    exacts [by first | exact h₁.deg m h | exact h₁.wt m h,
      by first | exact h₂.deg m h | exact h₂.wt m h]

theorem mul (h₁ : JetBd n r V Q₁) (h₂ : JetBd n r' V' Q₂) :
    JetBd n (r + r') (V + V') (Q₁ * Q₂) := by
  classical
  have key : ∀ m ∈ (Q₁ * Q₂).support, ∃ a ∈ Q₁.support, ∃ b ∈ Q₂.support, m = a + b := by
    intro m hm
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.1 (MvPolynomial.support_mul Q₁ Q₂ hm)
    exact ⟨a, ha, b, hb, hab.symm⟩
  constructor
  · intro m hm
    obtain ⟨a, ha, b, hb, rfl⟩ := key m hm
    have : ∑ j : Fin (n + 1), (a + b) j.succ
        = (∑ j : Fin (n + 1), a j.succ) + ∑ j : Fin (n + 1), b j.succ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Finsupp.add_apply _ _ _
    rw [this]
    exact Nat.add_le_add (h₁.deg a ha) (h₂.deg b hb)
  · intro m hm
    obtain ⟨a, ha, b, hb, rfl⟩ := key m hm
    have h1 : ∑ j : Fin (n + 1), (j : ℕ) * (a + b) j.succ
        = (∑ j : Fin (n + 1), (j : ℕ) * a j.succ) + ∑ j : Fin (n + 1), (j : ℕ) * b j.succ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [Finsupp.add_apply, Nat.mul_add]
    have h2 : (a + b) 0 = a 0 + b 0 := Finsupp.add_apply _ _ _
    have ha' := h₁.wt a ha
    have hb' := h₂.wt b hb
    rw [h1, h2]
    omega

theorem pow (h : JetBd n r V Q) (k : ℕ) : JetBd n (k * r) (k * V) (Q ^ k) := by
  induction k with
  | zero =>
    simpa using (C_bd (n := n) (1 : ℂ)).mono (Nat.zero_le _) (Nat.zero_le _)
  | succ k ih =>
    rw [pow_succ]
    have := ih.mul h
    exact this.mono (by ring_nf; omega) (by ring_nf; omega)

theorem finsetProd {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin (n + 2)) ℂ)
    (rf Vf : ι → ℕ) (h : ∀ i ∈ s, JetBd n (rf i) (Vf i) (f i)) :
    JetBd n (∑ i ∈ s, rf i) (∑ i ∈ s, Vf i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (C_bd (n := n) (1 : ℂ))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem finsetSum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin (n + 2)) ℂ)
    (h : ∀ i ∈ s, JetBd n r V (f i)) : JetBd n r V (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (zero (n := n)).mono (Nat.zero_le _) (Nat.zero_le _)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A polynomial in the point variable alone has jet degree `0` and weight its degree. -/
theorem polynomial_point (q : Polynomial ℂ) :
    JetBd n 0 q.natDegree (Polynomial.aeval (MvPolynomial.X 0) q) := by
  classical
  rw [Polynomial.aeval_eq_sum_range]
  refine finsetSum _ _ fun i hi => ?_
  rw [MvPolynomial.smul_eq_C_mul]
  have hi' : i ≤ q.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  refine ((C_bd (n := n) (q.coeff i)).mul ((X_zero (n := n)).pow i)).mono ?_ ?_
  · simp
  · simpa using hi'

end JetBd

end GaloisForLFunctions.HTGeometry
