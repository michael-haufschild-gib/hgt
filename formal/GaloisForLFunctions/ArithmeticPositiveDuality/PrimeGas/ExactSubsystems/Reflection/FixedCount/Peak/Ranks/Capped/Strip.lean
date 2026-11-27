import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Ordered

/-! # First mismatch between two complementary strips of occupation numbers -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Capped

/-- Feasibility of the two transfer counts when the middle mode holds k particles and has l vacancies. -/
def Allowed (k l i j : ℕ) := i ≤ k+l ∧ j ≤ k+l ∧ j ≤ k+i ∧ i ≤ l+j

def height (a b : ℝ) (v : ℕ × ℕ) := (v.1 : ℝ)*a + (v.2 : ℝ)*b

def band (k l : ℕ) (a b : ℝ) := {z : ℝ | ∃ v : ℕ × ℕ, Allowed k l v.1 v.2 ∧ height a b v = z}

def mismatch (A B : Set ℝ) := (A \ B) ∪ (B \ A)

def threshold (k l : ℕ) (a b : ℝ) : ℝ := ((min k l + 1 : ℕ) : ℝ) * min a b

private theorem enough_room {k l i j : ℕ} (hi : i ≤ min k l) (hj : j ≤ min k l) :
    Allowed k l i j := by
  have := min_le_left k l
  have := min_le_right k l
  unfold Allowed
  omega

private theorem below_threshold (k l : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (v : ℕ × ℕ) (h : height a b v < threshold k l a b) :
    v.1 ≤ min k l ∧ v.2 ≤ min k l := by
  have hm := lt_min ha hb
  have coeff (n : ℕ) (hn : (n : ℝ)*min a b ≤ height a b v) : n ≤ min k l := by
    by_contra! hc
    have he : ((min k l + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hc
    exact h.not_ge ((mul_le_mul_of_nonneg_right he hm.le).trans hn)
  constructor
  · apply coeff
    exact (mul_le_mul_of_nonneg_left (min_le_left a b) (Nat.cast_nonneg v.1)).trans
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg v.2) hb.le))
  · apply coeff
    exact (mul_le_mul_of_nonneg_left (min_le_right a b) (Nat.cast_nonneg v.2)).trans
      (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg v.1) ha.le))

/-- Below the threshold every occupied transfer pair fits in both strips. -/
theorem band_agrees_below (k l : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z : ℝ} (hz : z < threshold k l a b) : z ∈ band k l a b ↔ z ∈ band l k a b := by
  constructor <;> rintro ⟨v,_,rfl⟩
  · obtain ⟨hi,hj⟩ := below_threshold k l ha hb v hz
    rw [min_comm] at hi hj
    exact ⟨v,enough_room hi hj,rfl⟩
  · obtain ⟨hi,hj⟩ := below_threshold k l ha hb v hz
    exact ⟨v,enough_room hi hj,rfl⟩

private theorem distinguished {k l : ℕ} {a b : ℝ} (inj : Function.Injective (height a b))
    (v : ℕ × ℕ) (hy : Allowed k l v.1 v.2) (hn : ¬Allowed l k v.1 v.2) :
    height a b v ∈ band k l a b \ band l k a b := by
  refine ⟨⟨v,hy,rfl⟩,?_⟩
  rintro ⟨w,hw,he⟩
  exact hn (inj he ▸ hw)

private theorem threshold_mem {k l : ℕ} (hkl : k < l) {a b : ℝ}
    (inj : Function.Injective (height a b)) :
    threshold k l a b ∈ mismatch (band k l a b) (band l k a b) := by
  rcases le_total a b with hab | hba
  · have h : height a b (k+1,0) = threshold k l a b := by
      simp only [height,threshold,min_eq_left hkl.le,min_eq_left hab,Nat.cast_zero,zero_mul,add_zero]
    rw [← h]
    exact Or.inl (distinguished inj (k+1,0) (by unfold Allowed; dsimp; omega) (by unfold Allowed; dsimp; omega))
  · have h : height a b (0,k+1) = threshold k l a b := by
      simp only [height,threshold,min_eq_left hkl.le,min_eq_right hba,Nat.cast_zero,zero_mul,zero_add]
    rw [← h]
    exact Or.inr (distinguished inj (0,k+1) (by unfold Allowed; dsimp; omega) (by unfold Allowed; dsimp; omega))

/-- When the signed filling is nonzero, the first asymmetric excitation is on the cheaper transfer axis. -/
theorem first_mismatch {k l : ℕ} (hkl : k ≠ l) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (inj : Function.Injective (height a b)) :
    IsLeast (mismatch (band k l a b) (band l k a b)) (threshold k l a b) := by
  constructor
  · rcases lt_or_gt_of_ne hkl with h | h
    · exact threshold_mem h inj
    · have hh := threshold_mem h inj
      simpa only [mismatch,Set.union_comm,threshold,min_comm l k] using hh
  · intro z hz
    by_contra! he
    have eqv := band_agrees_below k l ha hb he
    exact hz.elim (fun hh => hh.2 (eqv.mp hh.1)) (fun hh => hh.2 (eqv.mpr hh.1))

#print axioms band_agrees_below
#print axioms first_mismatch

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Capped
