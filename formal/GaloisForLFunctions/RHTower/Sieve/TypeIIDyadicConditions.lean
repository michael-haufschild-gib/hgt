import GaloisForLFunctions.RHTower.Sieve.GapSumDyadic
import GaloisForLFunctions.RHTower.Sieve.TypeIIBlockSwapBound

/-!
# Numeric curvature conditions for the two type-II orientations

The long and exchanged Cauchy--Schwarz orientations apply on complementary dyadic scales.  This
module discharges their pointwise phase premises from explicit inequalities in the block parameters.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- The long-orientation phase starts beyond four times every effective short parameter. -/
theorem four_r_div_le_of_mem_effSet {r : ℝ} {A B P Q L m : ℕ}
    (hA : 1 ≤ A) (hP : 1 ≤ P) (hQ : 2 ≤ Q) (hQ2P : Q ≤ 2 * P)
    (hr : 0 ≤ r) (h8 : 8 * r ≤ (A : ℝ))
    (hm : m ∈ effSet A B P Q L) :
    4 * (r / m) ≤ (P : ℝ) := by
  have hmconf := effSet_confined hP hQ m hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmconf.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hmge : (A : ℝ) / Q ≤ (m : ℝ) :=
    le_trans (cast_effLow_ge hA hQ) (by exact_mod_cast hmconf.2.1)
  have hdiv : r / m ≤ r / ((A : ℝ) / Q) :=
    div_le_div_of_nonneg_left hr (by positivity) hmge
  have heq : r / ((A : ℝ) / Q) = r * Q / A := by field_simp
  rw [heq] at hdiv
  have hQcast : (Q : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hQ2P
  have hq : r * (Q : ℝ) / A ≤ 2 * r * P / A := by
    apply div_le_div_of_nonneg_right
    nlinarith
    exact hA0.le
  have hlast : 4 * (2 * r * P / A) ≤ (P : ℝ) := by
    calc
      4 * (2 * r * P / A) = (8 * r) * P / A := by ring
      _ ≤ (A : ℝ) * P / A :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h8 hP0.le) hA0.le
      _ = (P : ℝ) := by field_simp
  linarith

/-- The long-orientation curvature parameter is at most one above its explicit threshold. -/
theorem curvedLambda_effSet_le_one {T r : ℝ} {A B P Q L m₁ m₂ : ℕ}
    (hT : 0 < T) (hA : 1 ≤ A) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hQ2P : Q ≤ 2 * P) (hr : 0 ≤ r) (hTr : T * r ≤ 9 * Real.pi * A * P ^ 2)
    (hm₁ : m₁ ∈ effSet A B P Q L) (hm₂ : m₂ ∈ effSet A B P Q L) :
    curvedLambda (T * |r / m₁ - r / m₂|) (P : ℝ) ≤ 1 := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hQcast : (Q : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hQ2P
  have hri : ∀ m ∈ effSet A B P Q L, r / (m : ℝ) ≤ 2 * r * P / A := by
    intro m hm
    have hmconf := effSet_confined hP hQ m hm
    have hmge : (A : ℝ) / Q ≤ (m : ℝ) :=
      le_trans (cast_effLow_ge hA hQ) (by exact_mod_cast hmconf.2.1)
    have hdiv := div_le_div_of_nonneg_left hr (by positivity : (0 : ℝ) < (A : ℝ) / Q) hmge
    have heq : r / ((A : ℝ) / Q) = r * Q / A := by field_simp
    rw [heq] at hdiv
    have hq : r * (Q : ℝ) / A ≤ 2 * r * P / A := by
      apply div_le_div_of_nonneg_right
      nlinarith
      exact hA0.le
    exact hdiv.trans hq
  have hnonneg : ∀ m : ℕ, 0 ≤ r / (m : ℝ) := fun m => by positivity
  have habs : |r / m₁ - r / m₂| ≤ 4 * r * P / A := by
    have h := abs_sub_le (r / (m₁ : ℝ)) 0 (r / (m₂ : ℝ))
    simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (hnonneg m₁),
      abs_of_nonneg (hnonneg m₂)] at h
    calc
      |r / m₁ - r / m₂| ≤ r / m₁ + r / m₂ := h
      _ ≤ 2 * r * P / A + 2 * r * P / A := add_le_add (hri m₁ hm₁) (hri m₂ hm₂)
      _ = 4 * r * P / A := by ring
  have hbound : T * (4 * r * P / A) ≤ 36 * Real.pi * P ^ 3 := by
    calc
      T * (4 * r * P / A) = (4 * P / A) * (T * r) := by ring
      _ ≤ (4 * P / A) * (9 * Real.pi * A * P ^ 2) :=
        mul_le_mul_of_nonneg_left hTr (by positivity)
      _ = 36 * Real.pi * P ^ 3 := by field_simp; ring
  rw [curvedLambda, div_le_one (by positivity)]
  exact (mul_le_mul_of_nonneg_left habs hT.le).trans hbound

/-- The exchanged-orientation phase starts beyond four times each block parameter. -/
theorem four_r_div_le_effLow_of_mem_Ico {r : ℝ} {A P Q d : ℕ}
    (hA : 1 ≤ A) (hP : 1 ≤ P) (hQ : 2 ≤ Q) (hQ2P : Q ≤ 2 * P)
    (hr : 0 ≤ r) (h8 : 8 * r ≤ (A : ℝ)) (hd : d ∈ Finset.Ico P Q) :
    4 * (r / d) ≤ ((effLow A Q : ℕ) : ℝ) := by
  rw [Finset.mem_Ico] at hd
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < P) hd.1)
  have hdcast : (P : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1
  have hdiv : r / d ≤ r / P := div_le_div_of_nonneg_left hr hP0 hdcast
  have hQcast : (Q : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hQ2P
  have hmid : 4 * (r / (P : ℝ)) ≤ (A : ℝ) / Q := by
    rw [show 4 * (r / (P : ℝ)) = (4 * r) / P by ring,
      div_le_div_iff₀ hP0 hQ0]
    nlinarith
  exact le_trans (by nlinarith) (cast_effLow_ge hA hQ)

/-- The exchanged-orientation curvature parameter is at most one below its explicit threshold. -/
theorem curvedLambda_Ico_effLow_le_one {T r : ℝ} {A P Q d₁ d₂ : ℕ}
    (hT : 0 < T) (hA : 1 ≤ A) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hQ2P : Q ≤ 2 * P) (hr : 0 ≤ r)
    (hTrP : 4 * T * r * P ^ 2 ≤ 9 * Real.pi * A ^ 3)
    (hd₁ : d₁ ∈ Finset.Ico P Q) (hd₂ : d₂ ∈ Finset.Ico P Q) :
    curvedLambda (T * |r / d₁ - r / d₂|) ((effLow A Q : ℕ) : ℝ) ≤ 1 := by
  rw [Finset.mem_Ico] at hd₁ hd₂
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hQcast : (Q : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hQ2P
  have hri : ∀ d : ℕ, P ≤ d → r / (d : ℝ) ≤ r / P := fun d hd =>
    div_le_div_of_nonneg_left hr hP0 (by exact_mod_cast hd)
  have habs : |r / d₁ - r / d₂| ≤ 2 * r / P := by
    have hnonneg : ∀ d : ℕ, 0 ≤ r / (d : ℝ) := fun d => by positivity
    have h := abs_sub_le (r / (d₁ : ℝ)) 0 (r / (d₂ : ℝ))
    simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (hnonneg d₁),
      abs_of_nonneg (hnonneg d₂)] at h
    calc
      |r / d₁ - r / d₂| ≤ r / d₁ + r / d₂ := h
      _ ≤ r / P + r / P := add_le_add (hri d₁ hd₁.1) (hri d₂ hd₂.1)
      _ = 2 * r / P := by ring
  have hlow : (A : ℝ) / (2 * P) ≤ ((effLow A Q : ℕ) : ℝ) :=
    le_trans (div_le_div_of_nonneg_left hA0.le hQ0 hQcast) (cast_effLow_ge hA hQ)
  have hM0 : (0 : ℝ) < ((effLow A Q : ℕ) : ℝ) := by
    exact_mod_cast one_le_effLow A Q
  have hmain : T * (2 * r / P) ≤ 36 * Real.pi * ((A : ℝ) / (2 * P)) ^ 3 := by
    rw [div_pow]
    field_simp
    nlinarith [hTrP]
  have hcube : ((A : ℝ) / (2 * P)) ^ 3 ≤ ((effLow A Q : ℕ) : ℝ) ^ 3 := by
    gcongr
  rw [curvedLambda, div_le_one (by positivity)]
  refine (mul_le_mul_of_nonneg_left habs hT.le).trans (hmain.trans ?_)
  nlinarith [hcube, Real.pi_pos]

/-- Under the transition-range global inequality, every dyadic scale satisfies at least one of
the two orientation thresholds. -/
theorem typeII_orientation_cover {T r : ℝ} {A P : ℕ}
    (hT : 0 < T) (hr : 0 < r) (hA : 1 ≤ A)
    (hglobal : 2 * T * r ≤ 9 * Real.pi * A ^ 2) :
    T * r ≤ 9 * Real.pi * A * P ^ 2 ∨
      4 * T * r * P ^ 2 ≤ 9 * Real.pi * A ^ 3 := by
  by_cases hlarge : T * r ≤ 9 * Real.pi * A * P ^ 2
  · exact Or.inl hlarge
  · right
    have hpi : 0 < Real.pi := Real.pi_pos
    have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    have hX0 : 0 < T * r := mul_pos hT hr
    have hlarge' : ¬T * r ≤ (P : ℝ) ^ 2 * (9 * Real.pi * A) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hlarge
    have hP2 : ((P : ℝ) ^ 2) < T * r / (9 * Real.pi * A) := by
      rw [lt_div_iff₀ (by positivity)]
      exact lt_of_not_ge hlarge'
    have hmul := mul_le_mul_of_nonneg_left hP2.le (by positivity : (0 : ℝ) ≤ 4 * T * r)
    have hsquare := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 2 * T * r) hglobal
    have hmid : 4 * T * r * (T * r / (9 * Real.pi * A))
        ≤ 9 * Real.pi * A ^ 3 := by
      rw [div_eq_mul_inv]
      field_simp
      nlinarith [hsquare]
    exact le_trans (by nlinarith [hmul]) hmid

end

end RHTower.Sieve
