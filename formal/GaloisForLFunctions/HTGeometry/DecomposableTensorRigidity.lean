import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCriticalMultiplicity

/-!
# Rigidity of decomposable tensors

A nonzero decomposable tensor determines its two factor lines.  If `a ⊗ b` and `a' ⊗ b'` span the
same line, then `a` and `a'` are proportional and so are `b` and `b'`, and the two proportionality
constants multiply to the given scalar.  In particular a nonzero decomposable tensor determines its
factors up to reciprocal scalars.

The proof is a single division.  Choosing coordinates `i₀, j₀` where `a` and `b` do not vanish, the
entries at `(i, j₀)` and `(i₀, j)` recover `a` and `b` from `a'` and `b'`, and the entry at
`(i₀, j₀)` identifies the product of the two constants.

`criticalHorizonSegreTensor` already records that such a tensor has vanishing `2 × 2` minors; the
statements here are the converse, recovering the factors from the tensor. -/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] {I J : Type*}

/-- A decomposable tensor vanishes exactly when one of its factors does. -/
theorem criticalHorizonSegreTensor_eq_zero_iff (a : I → K) (b : J → K) :
    criticalHorizonSegreTensor a b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    by_contra hcon
    have ha : a ≠ 0 := fun h0 => hcon (Or.inl h0)
    have hb : b ≠ 0 := fun h0 => hcon (Or.inr h0)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hb
    have := congrFun (congrFun h i) j
    simp only [criticalHorizonSegreTensor] at this
    exact (mul_ne_zero hi hj) this
  · rintro (rfl | rfl) <;> funext i j <;> simp [criticalHorizonSegreTensor]

/-- **Rigidity of decomposable tensors.**  Two proportional nonzero decomposable tensors have
proportional factors, and the two constants multiply to the given scalar. -/
theorem criticalHorizonSegreTensor_rigidity {a a' : I → K} {b b' : J → K} {c : K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : criticalHorizonSegreTensor a b = c • criticalHorizonSegreTensor a' b') :
    ∃ α β : K, α ≠ 0 ∧ β ≠ 0 ∧ α * β = c ∧
      (∀ i, a i = α * a' i) ∧ (∀ j, b j = β * b' j) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 ha
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hb
  have hentry : ∀ (i : I) (j : J), a i * b j = c * (a' i * b' j) := by
    intro i j
    have := congrFun (congrFun h i) j
    simpa only [criticalHorizonSegreTensor, Matrix.smul_apply, smul_eq_mul] using this
  have hbase := hentry i₀ j₀
  have ha'0 : a' i₀ ≠ 0 := by
    intro h0
    rw [h0, zero_mul, mul_zero] at hbase
    exact (mul_ne_zero hi₀ hj₀) hbase
  have hb'0 : b' j₀ ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mul_zero] at hbase
    exact (mul_ne_zero hi₀ hj₀) hbase
  refine ⟨a i₀ / a' i₀, b j₀ / b' j₀, div_ne_zero hi₀ ha'0, div_ne_zero hj₀ hb'0, ?_, ?_, ?_⟩
  · rw [div_mul_div_comm, div_eq_iff (mul_ne_zero ha'0 hb'0)]
    exact hbase
  · intro i
    have hi := hentry i j₀
    have hcancel : (a i * a' i₀) * (b j₀ * b' j₀) = (a i₀ * a' i) * (b j₀ * b' j₀) := by
      calc (a i * a' i₀) * (b j₀ * b' j₀)
          = (a i * b j₀) * (a' i₀ * b' j₀) := by ring
        _ = (c * (a' i * b' j₀)) * (a' i₀ * b' j₀) := by rw [hi]
        _ = (a' i * b' j₀) * (c * (a' i₀ * b' j₀)) := by ring
        _ = (a' i * b' j₀) * (a i₀ * b j₀) := by rw [← hbase]
        _ = (a i₀ * a' i) * (b j₀ * b' j₀) := by ring
    have hkey : a i * a' i₀ = a i₀ * a' i :=
      mul_right_cancel₀ (mul_ne_zero hj₀ hb'0) hcancel
    rw [div_mul_eq_mul_div, eq_div_iff ha'0]
    exact hkey
  · intro j
    have hj := hentry i₀ j
    have hcancel : (b j * b' j₀) * (a i₀ * a' i₀) = (b j₀ * b' j) * (a i₀ * a' i₀) := by
      calc (b j * b' j₀) * (a i₀ * a' i₀)
          = (a i₀ * b j) * (a' i₀ * b' j₀) := by ring
        _ = (c * (a' i₀ * b' j)) * (a' i₀ * b' j₀) := by rw [hj]
        _ = (a' i₀ * b' j) * (c * (a' i₀ * b' j₀)) := by ring
        _ = (a' i₀ * b' j) * (a i₀ * b j₀) := by rw [← hbase]
        _ = (b j₀ * b' j) * (a i₀ * a' i₀) := by ring
    have hkey : b j * b' j₀ = b j₀ * b' j :=
      mul_right_cancel₀ (mul_ne_zero hi₀ ha'0) hcancel
    rw [div_mul_eq_mul_div, eq_div_iff hb'0]
    exact hkey

/-- **Uniqueness up to reciprocal scalars.**  Equal nonzero decomposable tensors have proportional
factors with reciprocal constants. -/
theorem criticalHorizonSegreTensor_eq_rigidity {a a' : I → K} {b b' : J → K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : criticalHorizonSegreTensor a b = criticalHorizonSegreTensor a' b') :
    ∃ α β : K, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 1 ∧
      (∀ i, a i = α * a' i) ∧ (∀ j, b j = β * b' j) := by
  refine criticalHorizonSegreTensor_rigidity ha hb ?_
  rw [one_smul]
  exact h

/-- The left factor line is determined: proportional nonzero decomposable tensors have their first
factors on one line. -/
theorem criticalHorizonSegreTensor_left_line {a a' : I → K} {b b' : J → K} {c : K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : criticalHorizonSegreTensor a b = c • criticalHorizonSegreTensor a' b') :
    ∃ α : K, α ≠ 0 ∧ a = α • a' := by
  obtain ⟨α, β, hα, _, _, hleft, _⟩ := criticalHorizonSegreTensor_rigidity ha hb h
  exact ⟨α, hα, funext fun i => by simpa [Pi.smul_apply, smul_eq_mul] using hleft i⟩

/-- The right factor line is determined. -/
theorem criticalHorizonSegreTensor_right_line {a a' : I → K} {b b' : J → K} {c : K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : criticalHorizonSegreTensor a b = c • criticalHorizonSegreTensor a' b') :
    ∃ β : K, β ≠ 0 ∧ b = β • b' := by
  obtain ⟨_, β, _, hβ, _, _, hright⟩ := criticalHorizonSegreTensor_rigidity ha hb h
  exact ⟨β, hβ, funext fun j => by simpa [Pi.smul_apply, smul_eq_mul] using hright j⟩

/-- With one factor held fixed and nonzero, the other factor is determined outright. -/
theorem criticalHorizonSegreTensor_left_cancel {a a' : I → K} {b : J → K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : criticalHorizonSegreTensor a b = criticalHorizonSegreTensor a' b) :
    a = a' := by
  obtain ⟨α, β, _, _, hαβ, hleft, hright⟩ := criticalHorizonSegreTensor_eq_rigidity ha hb h
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hb
  have hβ : β = 1 := by
    have h1 : b j₀ = β * b j₀ := hright j₀
    have h2 : (1 - β) * b j₀ = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact (sub_eq_zero.mp h3).symm
    · exact absurd h3 hj₀
  have hα : α = 1 := by
    rw [hβ, mul_one] at hαβ
    exact hαβ
  funext i
  rw [hleft i, hα, one_mul]

/-- With the first factor held fixed and nonzero, the second factor is determined outright. -/
theorem criticalHorizonSegreTensor_right_cancel {a : I → K} {b b' : J → K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : criticalHorizonSegreTensor a b = criticalHorizonSegreTensor a b') :
    b = b' := by
  obtain ⟨α, β, _, _, hαβ, hleft, hright⟩ := criticalHorizonSegreTensor_eq_rigidity ha hb h
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 ha
  have hα : α = 1 := by
    have h1 : a i₀ = α * a i₀ := hleft i₀
    have h2 : (1 - α) * a i₀ = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact (sub_eq_zero.mp h3).symm
    · exact absurd h3 hi₀
  have hβ : β = 1 := by
    rw [hα, one_mul] at hαβ
    exact hαβ
  funext j
  rw [hright j, hβ, one_mul]

/-! ### Bilinearity -/

theorem criticalHorizonSegreTensor_add_left (a a' : I → K) (b : J → K) :
    criticalHorizonSegreTensor (a + a') b =
      criticalHorizonSegreTensor a b + criticalHorizonSegreTensor a' b := by
  funext i j
  simp [criticalHorizonSegreTensor, add_mul]

theorem criticalHorizonSegreTensor_smul_left (c : K) (a : I → K) (b : J → K) :
    criticalHorizonSegreTensor (c • a) b = c • criticalHorizonSegreTensor a b := by
  funext i j
  simp [criticalHorizonSegreTensor, mul_assoc]

theorem criticalHorizonSegreTensor_add_right (a : I → K) (b b' : J → K) :
    criticalHorizonSegreTensor a (b + b') =
      criticalHorizonSegreTensor a b + criticalHorizonSegreTensor a b' := by
  funext i j
  simp [criticalHorizonSegreTensor, mul_add]

theorem criticalHorizonSegreTensor_smul_right (c : K) (a : I → K) (b : J → K) :
    criticalHorizonSegreTensor a (c • b) = c • criticalHorizonSegreTensor a b := by
  funext i j
  simp [criticalHorizonSegreTensor]
  ring

/-- **Expansion in a product frame.**  A decomposable tensor whose factors are written in two
frames expands with coefficient array the outer product of the two coordinate vectors. -/
theorem criticalHorizonSegreTensor_sum_smul {I' J' : Type*} [Fintype I'] [Fintype J']
    (x : I' → K) (y : J' → K) (a : I' → (I → K)) (b : J' → (J → K)) :
    criticalHorizonSegreTensor (∑ i, x i • a i) (∑ j, y j • b j) =
      ∑ i, ∑ j, (x i * y j) • criticalHorizonSegreTensor (a i) (b j) := by
  funext p q
  simp only [criticalHorizonSegreTensor, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.sum_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, criticalHorizonSegreTensor]
  ring

end GaloisForLFunctions.HTGeometry
