import GaloisForLFunctions.HTGeometry.DifferentialOperatorOre

/-!
# Right division in the Ore ring of differential operators

Over a differential field the operator ring `K[∂;δ]` carries a division algorithm: for `b ≠ 0`
every `a` can be written `a = q * b + r` with `r = 0` or `degree r < degree b`.  The proof is the
usual leading-term cancellation, which works verbatim in the noncommutative setting because
multiplication by `∂` does not change leading coefficients:

`(a_n b_m⁻¹ ∂ⁿ⁻ᵐ) * b` has degree `n` and leading coefficient `a_n`.

This Euclidean structure is what replaces the skew field of rational pseudodifferential
operators in the two-sided order comparison: all that the right inverse is used for is a bounded
degree comparison, and division supplies it.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

theorem mono_ne_zero {n : ℕ} {a : K} (ha : a ≠ 0) : mono n a ≠ 0 := by
  intro h
  exact ha (by rw [← coeff_mono_self n a, h, coeff_zero])

theorem degree_mono {n : ℕ} {a : K} (ha : a ≠ 0) : degree (mono n a) = n :=
  le_antisymm (degree_mono_le n a) (le_degree (by rwa [coeff_mono_self]))

theorem leadCoeff_mono {n : ℕ} {a : K} (ha : a ≠ 0) : leadCoeff (mono n a) = a := by
  rw [leadCoeff, degree_mono ha, coeff_mono_self]

/-- An operator of degree at most `n` whose `n`-th coefficient vanishes has degree `< n`, unless
it is zero. -/
theorem degree_lt_of_coeff_eq_zero {p : DiffOp K} {n : ℕ} (hle : degree p ≤ n)
    (hcoeff : coeff p n = 0) (hp : p ≠ 0) : degree p < n :=
  lt_of_le_of_ne hle fun h => leadCoeff_ne_zero hp (by rw [leadCoeff, h, hcoeff])

theorem eq_zero_of_degree_le_zero {p : DiffOp K} (hle : degree p ≤ 0) (hcoeff : coeff p 0 = 0) :
    p = 0 := by
  refine eq_zero_iff.mpr fun n => ?_
  cases n with
  | zero => exact hcoeff
  | succ n => exact coeff_eq_zero_of_degree_lt (by omega)

/-- Leading-term cancellation: a single monomial multiple of `b` matches the top coefficient
of `a`. -/
theorem exists_leading_cancel {a b : DiffOp K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : degree b ≤ degree a) :
    ∃ c : DiffOp K, degree (a - c * b) ≤ degree a ∧ coeff (a - c * b) (degree a) = 0 := by
  have hla : leadCoeff a ≠ 0 := leadCoeff_ne_zero ha
  have hlb : leadCoeff b ≠ 0 := leadCoeff_ne_zero hb
  have hquot : leadCoeff a / leadCoeff b ≠ 0 := div_ne_zero hla hlb
  refine ⟨mono (degree a - degree b) (leadCoeff a / leadCoeff b), ?_, ?_⟩
  · refine le_trans (degree_sub_le a (mono (degree a - degree b)
      (leadCoeff a / leadCoeff b) * b)) (max_le le_rfl (le_of_eq ?_))
    rw [degree_mul (mono_ne_zero hquot) hb, degree_mono hquot]
    omega
  · have hdeg : degree (mono (degree a - degree b) (leadCoeff a / leadCoeff b) * b)
        = degree a := by
      rw [degree_mul (mono_ne_zero hquot) hb, degree_mono hquot]
      omega
    have htop : coeff (mono (degree a - degree b) (leadCoeff a / leadCoeff b) * b)
        (degree a) = leadCoeff a := by
      have h := leadCoeff_mul (mono_ne_zero (n := degree a - degree b) hquot) hb
      rw [leadCoeff, hdeg] at h
      rw [h, leadCoeff_mono hquot, div_mul_cancel₀ _ hlb]
    rw [coeff_sub, htop, leadCoeff, sub_self]

/-- Right division with remainder. -/
theorem exists_right_div {b : DiffOp K} (hb : b ≠ 0) (a : DiffOp K) :
    ∃ q r : DiffOp K, a = q * b + r ∧ (r = 0 ∨ degree r < degree b) := by
  have key : ∀ n : ℕ, ∀ a : DiffOp K, degree a ≤ n →
      ∃ q r : DiffOp K, a = q * b + r ∧ (r = 0 ∨ degree r < degree b) := by
    intro n
    induction n with
    | zero =>
      intro a ha
      by_cases hlt : degree a < degree b
      · exact ⟨0, a, by rw [zero_mul', zero_add], Or.inr hlt⟩
      · by_cases ha0 : a = 0
        · exact ⟨0, 0, by rw [ha0, zero_mul', zero_add], Or.inl rfl⟩
        · obtain ⟨c, hcle, hczero⟩ :=
            exists_leading_cancel ha0 hb (Nat.le_of_not_lt hlt)
          have hzero : a - c * b = 0 := by
            refine eq_zero_of_degree_le_zero (le_trans hcle ha) ?_
            have : degree a = 0 := Nat.le_zero.mp ha
            rwa [this] at hczero
          exact ⟨c, 0, by rw [add_zero, ← sub_eq_zero]; exact hzero, Or.inl rfl⟩
    | succ n ih =>
      intro a ha
      by_cases hlt : degree a < degree b
      · exact ⟨0, a, by rw [zero_mul', zero_add], Or.inr hlt⟩
      · by_cases ha0 : a = 0
        · exact ⟨0, 0, by rw [ha0, zero_mul', zero_add], Or.inl rfl⟩
        · obtain ⟨c, hcle, hczero⟩ :=
            exists_leading_cancel ha0 hb (Nat.le_of_not_lt hlt)
          by_cases hz : a - c * b = 0
          · exact ⟨c, 0, by rw [add_zero, ← sub_eq_zero]; exact hz, Or.inl rfl⟩
          · have hdlt : degree (a - c * b) < degree a :=
              degree_lt_of_coeff_eq_zero hcle hczero hz
            obtain ⟨q, r, hqr, hr⟩ := ih (a - c * b) (by omega)
            refine ⟨c + q, r, ?_, hr⟩
            rw [add_mul', add_assoc, ← hqr]
            abel
  exact key (degree a) a le_rfl


/-- Leading-term cancellation on the other side: a single monomial multiple of `b`, taken on the
right, matches the top coefficient of `a`. -/
theorem exists_leading_cancel_left {a b : DiffOp K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : degree b ≤ degree a) :
    ∃ c : DiffOp K, degree (a - b * c) ≤ degree a ∧ coeff (a - b * c) (degree a) = 0 := by
  have hla : leadCoeff a ≠ 0 := leadCoeff_ne_zero ha
  have hlb : leadCoeff b ≠ 0 := leadCoeff_ne_zero hb
  have hquot : (leadCoeff b)⁻¹ * leadCoeff a ≠ 0 :=
    mul_ne_zero (inv_ne_zero hlb) hla
  refine ⟨mono (degree a - degree b) ((leadCoeff b)⁻¹ * leadCoeff a), ?_, ?_⟩
  · refine le_trans (degree_sub_le a (b * mono (degree a - degree b)
      ((leadCoeff b)⁻¹ * leadCoeff a))) (max_le le_rfl (le_of_eq ?_))
    rw [degree_mul hb (mono_ne_zero hquot), degree_mono hquot]
    omega
  · have hdeg : degree (b * mono (degree a - degree b) ((leadCoeff b)⁻¹ * leadCoeff a))
        = degree a := by
      rw [degree_mul hb (mono_ne_zero (n := degree a - degree b) hquot), degree_mono hquot]
      omega
    have htop : coeff (b * mono (degree a - degree b) ((leadCoeff b)⁻¹ * leadCoeff a))
        (degree a) = leadCoeff a := by
      have h := leadCoeff_mul hb (mono_ne_zero (n := degree a - degree b) hquot)
      rw [leadCoeff, hdeg] at h
      rw [h, leadCoeff_mono hquot, ← mul_assoc, mul_inv_cancel₀ hlb, one_mul]
    rw [coeff_sub, htop, leadCoeff, sub_self]

/-- Left division with remainder. -/
theorem exists_left_div {b : DiffOp K} (hb : b ≠ 0) (a : DiffOp K) :
    ∃ q r : DiffOp K, a = b * q + r ∧ (r = 0 ∨ degree r < degree b) := by
  have key : ∀ n : ℕ, ∀ a : DiffOp K, degree a ≤ n →
      ∃ q r : DiffOp K, a = b * q + r ∧ (r = 0 ∨ degree r < degree b) := by
    intro n
    induction n with
    | zero =>
      intro a ha
      by_cases hlt : degree a < degree b
      · exact ⟨0, a, by rw [mul_zero', zero_add], Or.inr hlt⟩
      · by_cases ha0 : a = 0
        · exact ⟨0, 0, by rw [ha0, mul_zero', zero_add], Or.inl rfl⟩
        · obtain ⟨c, hcle, hczero⟩ :=
            exists_leading_cancel_left ha0 hb (Nat.le_of_not_lt hlt)
          have hzero : a - b * c = 0 := by
            refine eq_zero_of_degree_le_zero (le_trans hcle ha) ?_
            have hdz : degree a = 0 := Nat.le_zero.mp ha
            rwa [hdz] at hczero
          exact ⟨c, 0, by rw [add_zero, ← sub_eq_zero]; exact hzero, Or.inl rfl⟩
    | succ n ih =>
      intro a ha
      by_cases hlt : degree a < degree b
      · exact ⟨0, a, by rw [mul_zero', zero_add], Or.inr hlt⟩
      · by_cases ha0 : a = 0
        · exact ⟨0, 0, by rw [ha0, mul_zero', zero_add], Or.inl rfl⟩
        · obtain ⟨c, hcle, hczero⟩ :=
            exists_leading_cancel_left ha0 hb (Nat.le_of_not_lt hlt)
          by_cases hz : a - b * c = 0
          · exact ⟨c, 0, by rw [add_zero, ← sub_eq_zero]; exact hz, Or.inl rfl⟩
          · have hdlt : degree (a - b * c) < degree a :=
              degree_lt_of_coeff_eq_zero hcle hczero hz
            obtain ⟨q, r, hqr, hr⟩ := ih (a - b * c) (by omega)
            refine ⟨c + q, r, ?_, hr⟩
            rw [mul_add', add_assoc, ← hqr]
            abel
  exact key (degree a) a le_rfl

end

end DiffOp

end GaloisForLFunctions.HTGeometry
