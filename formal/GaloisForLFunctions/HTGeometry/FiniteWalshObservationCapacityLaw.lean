import GaloisForLFunctions.HTGeometry.PrimeWalshTailConstraint

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance finiteBoolCubeFintype
    {I : Type*} [Fintype I] :
    Fintype (I → Bool) :=
  Fintype.ofFinite _

private theorem conj_orientationWalshCharacter
    {I : Type*} [Fintype I]
    (B : Finset I) (x : I → Bool) :
    starRingEnd ℂ (orientationWalshCharacter B x) =
      orientationWalshCharacter B x := by
  classical
  unfold orientationWalshCharacter
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  cases x i <;> norm_num [primeDirichletSign]

theorem sum_conj_mul_inverseWalshCoefficient
    {I : Type*} [Fintype I]
    (f : (I → Bool) → ℂ) :
    (∑ B : Finset I,
        starRingEnd ℂ (inverseWalshCoefficient f B) *
          inverseWalshCoefficient f B) =
      ((2 : ℂ) ^ Fintype.card I)⁻¹ *
        ∑ x : I → Bool, starRingEnd ℂ (f x) * f x := by
  classical
  let D : ℂ := (2 : ℂ) ^ Fintype.card I
  have hD : D ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [show
      (∑ B : Finset I,
          starRingEnd ℂ (inverseWalshCoefficient f B) *
            inverseWalshCoefficient f B) =
        D⁻¹ * D⁻¹ *
          ∑ x : I → Bool, ∑ y : I → Bool,
            starRingEnd ℂ (f x) * f y *
              (∑ B : Finset I,
                orientationWalshCharacter B x *
                  orientationWalshCharacter B y) by
    simp only [inverseWalshCoefficient, D]
    simp only [map_mul, map_inv₀, map_pow, map_ofNat, map_sum]
    simp_rw [conj_orientationWalshCharacter]
    calc
      (∑ B : Finset I,
          ((2 : ℂ) ^ Fintype.card I)⁻¹ *
              (∑ x : I → Bool,
                starRingEnd ℂ (f x) *
                  orientationWalshCharacter B x) *
            (((2 : ℂ) ^ Fintype.card I)⁻¹ *
              ∑ y : I → Bool,
                f y * orientationWalshCharacter B y)) =
        ∑ B : Finset I,
          D⁻¹ * D⁻¹ *
            ((∑ x : I → Bool,
                starRingEnd ℂ (f x) *
                  orientationWalshCharacter B x) *
              ∑ y : I → Bool,
                f y * orientationWalshCharacter B y) := by
          apply Finset.sum_congr rfl
          intro B hB
          simp only [D]
          ring
      _ =
        D⁻¹ * D⁻¹ *
          ∑ B : Finset I,
            ((∑ x : I → Bool,
                starRingEnd ℂ (f x) *
                  orientationWalshCharacter B x) *
              ∑ y : I → Bool,
                f y * orientationWalshCharacter B y) := by
          rw [Finset.mul_sum]
      _ =
        D⁻¹ * D⁻¹ *
          ∑ x : I → Bool, ∑ y : I → Bool,
            starRingEnd ℂ (f x) * f y *
              (∑ B : Finset I,
                orientationWalshCharacter B x *
                  orientationWalshCharacter B y) := by
          congr 1
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y hy
          apply Finset.sum_congr rfl
          intro B hB
          ring]
  simp_rw [sum_orientationWalshCharacter_mul_eq]
  rw [show
      (∑ x : I → Bool, ∑ y : I → Bool,
          starRingEnd ℂ (f x) * f y *
            (if x = y then D else 0)) =
        D * ∑ x : I → Bool, starRingEnd ℂ (f x) * f x by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Fintype.sum_eq_single x]
    · simp [D, mul_comm]
    · intro y hy
      rw [if_neg (Ne.symm hy)]
      ring]
  field_simp [hD]
  ring

theorem sum_norm_sq_inverseWalshCoefficient
    {I : Type*} [Fintype I]
    (f : (I → Bool) → ℂ) :
    (∑ B : Finset I, ‖inverseWalshCoefficient f B‖ ^ (2 : ℕ)) =
      ((2 : ℝ) ^ Fintype.card I)⁻¹ *
        ∑ x : I → Bool, ‖f x‖ ^ (2 : ℕ) := by
  have hC :
      (∑ B : Finset I,
          (Complex.normSq (inverseWalshCoefficient f B) : ℂ)) =
        ((((2 : ℝ) ^ Fintype.card I)⁻¹ : ℝ) : ℂ) *
          ∑ x : I → Bool, (Complex.normSq (f x) : ℂ) := by
    simpa only [Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_inv, Complex.ofReal_pow,
      Complex.ofReal_ofNat] using
        (sum_conj_mul_inverseWalshCoefficient f)
  have hR :
      (∑ B : Finset I,
          Complex.normSq (inverseWalshCoefficient f B)) =
        ((2 : ℝ) ^ Fintype.card I)⁻¹ *
          ∑ x : I → Bool, Complex.normSq (f x) := by
    exact_mod_cast hC
  simpa only [Complex.normSq_eq_norm_sq] using hR

/-- Number of normalized Walsh coefficients visible at resolution `η`. -/
noncomputable def walshThresholdCount
    {I : Type*} [Fintype I]
    (f : (I → Bool) → ℂ) (η : ℝ) : ℕ :=
  (Finset.univ.filter fun B : Finset I =>
    η ≤ ‖inverseWalshCoefficient f B‖).card

/-- Threshold counting is bounded by total normalized Walsh energy. -/
theorem sq_mul_walshThresholdCount_le_meanSquare
    {I : Type*} [Fintype I]
    (f : (I → Bool) → ℂ) {η : ℝ} (hη : 0 ≤ η) :
    η ^ (2 : ℕ) * (walshThresholdCount f η : ℝ) ≤
      ((2 : ℝ) ^ Fintype.card I)⁻¹ *
        ∑ x : I → Bool, ‖f x‖ ^ (2 : ℕ) := by
  classical
  let active :=
    Finset.univ.filter fun B : Finset I =>
      η ≤ ‖inverseWalshCoefficient f B‖
  have hterm :
      ∀ B ∈ active,
        η ^ (2 : ℕ) ≤ ‖inverseWalshCoefficient f B‖ ^ (2 : ℕ) := by
    intro B hB
    have hle : η ≤ ‖inverseWalshCoefficient f B‖ :=
      Finset.mem_filter.mp hB |>.2
    nlinarith [norm_nonneg (inverseWalshCoefficient f B)]
  calc
    η ^ (2 : ℕ) * (walshThresholdCount f η : ℝ) =
        ∑ B ∈ active, η ^ (2 : ℕ) := by
          simp [walshThresholdCount, active, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ B ∈ active,
        ‖inverseWalshCoefficient f B‖ ^ (2 : ℕ) :=
      Finset.sum_le_sum fun B hB => hterm B hB
    _ ≤ ∑ B : Finset I,
        ‖inverseWalshCoefficient f B‖ ^ (2 : ℕ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun B _ _ => sq_nonneg ‖inverseWalshCoefficient f B‖)
    _ = ((2 : ℝ) ^ Fintype.card I)⁻¹ *
        ∑ x : I → Bool, ‖f x‖ ^ (2 : ℕ) :=
      sum_norm_sq_inverseWalshCoefficient f

/-- A uniform response bound controls operational Walsh dimension. -/
theorem sq_mul_walshThresholdCount_le_bound_sq
    {I : Type*} [Fintype I]
    (f : (I → Bool) → ℂ) {η B : ℝ}
    (hη : 0 ≤ η)
    (hf : ∀ x, ‖f x‖ ≤ B) :
    η ^ (2 : ℕ) * (walshThresholdCount f η : ℝ) ≤ B ^ (2 : ℕ) := by
  have hcard :
      Fintype.card (I → Bool) = 2 ^ Fintype.card I := by
    rw [Fintype.card_eq_nat_card, Nat.card_fun]
    norm_num [Nat.card_eq_fintype_card]
  calc
    η ^ (2 : ℕ) * (walshThresholdCount f η : ℝ) ≤
        ((2 : ℝ) ^ Fintype.card I)⁻¹ *
          ∑ x : I → Bool, ‖f x‖ ^ (2 : ℕ) :=
      sq_mul_walshThresholdCount_le_meanSquare f hη
    _ ≤ ((2 : ℝ) ^ Fintype.card I)⁻¹ *
          ∑ _x : I → Bool, B ^ (2 : ℕ) := by
      gcongr with x
      exact hf x
    _ = B ^ (2 : ℕ) := by
      simp only [Finset.sum_const, Finset.card_univ,
        hcard, nsmul_eq_mul]
      have htwo : (2 : ℝ) ^ Fintype.card I ≠ 0 := by positivity
      field_simp
      norm_num [Nat.cast_pow]

end

end GaloisForLFunctions.HTGeometry
