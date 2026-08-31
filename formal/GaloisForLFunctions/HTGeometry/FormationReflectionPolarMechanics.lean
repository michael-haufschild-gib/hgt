import GaloisForLFunctions.HTGeometry.ShiftedEulerTangentFiltration

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {P : Type u}

/-- Weighted total depth of a finite free-commutative formation profile. -/
def formationTotalWeight (weight : P → ℝ) (x : P →₀ ℕ) : ℝ :=
  ∑ p ∈ x.support, (x p : ℝ) * weight p

/-- Weight after forgetting multiplicity and retaining occupied support. -/
def formationSupportWeight (weight : P → ℝ) (x : P →₀ ℕ) : ℝ :=
  ∑ p ∈ x.support, weight p

/-- Multiplicity depth invisible to the support observer. -/
def formationMultiplicityDefect (weight : P → ℝ) (x : P →₀ ℕ) : ℝ :=
  formationTotalWeight weight x - formationSupportWeight weight x

/-- Exterior locus: every occupied generator occurs exactly once. -/
def FormationSquarefree (x : P →₀ ℕ) : Prop :=
  ∀ p ∈ x.support, x p = 1

/-- Full nonperturbative formation packet. -/
def formationReflectionPacketCoefficient
    (weight : P → ℝ) (x : P →₀ ℕ) (ω : ℂ) : ℂ :=
  Complex.exp (ω * (formationTotalWeight weight x : ℂ)) *
    ∏ p ∈ x.support,
      (1 - Complex.exp (-(2 * ω) * (weight p : ℂ)))

/-- Reflection multiplier, split into support parity and multiplicity depth. -/
def formationReflectionMultiplier
    (weight : P → ℝ) (x : P →₀ ℕ) (ω : ℂ) : ℂ :=
  (-1 : ℂ) ^ x.support.card *
    Complex.exp (-(2 * ω) * (formationMultiplicityDefect weight x : ℂ))

/-- Boundary partial phase of a formation profile. -/
def formationMobius (x : P →₀ ℕ) : ℂ :=
  by
    classical
    exact if FormationSquarefree x then (-1 : ℂ) ^ x.support.card else 0

theorem formationMultiplicityDefect_eq_sum
    (weight : P → ℝ) (x : P →₀ ℕ) :
    formationMultiplicityDefect weight x =
      ∑ p ∈ x.support, ((x p : ℝ) - 1) * weight p := by
  rw [formationMultiplicityDefect, formationTotalWeight, formationSupportWeight,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem formationMultiplicityDefect_nonneg
    {weight : P → ℝ} (x : P →₀ ℕ) (hweight : ∀ p ∈ x.support, 0 ≤ weight p) :
    0 ≤ formationMultiplicityDefect weight x := by
  rw [formationMultiplicityDefect_eq_sum]
  exact Finset.sum_nonneg fun p hp => mul_nonneg
    (by
      have hx : 1 ≤ x p := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
      have hxR : (1 : ℝ) ≤ (x p : ℝ) := by exact_mod_cast hx
      exact sub_nonneg.mpr hxR)
    (hweight p hp)

theorem formationMultiplicityDefect_eq_zero_iff
    {weight : P → ℝ} (x : P →₀ ℕ) (hweight : ∀ p ∈ x.support, 0 < weight p) :
    formationMultiplicityDefect weight x = 0 ↔ FormationSquarefree x := by
  rw [formationMultiplicityDefect_eq_sum]
  have hnonneg : ∀ p ∈ x.support, 0 ≤ ((x p : ℝ) - 1) * weight p := by
    intro p hp
    apply mul_nonneg
    · have hx : 1 ≤ x p := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
      have hxR : (1 : ℝ) ≤ (x p : ℝ) := by exact_mod_cast hx
      exact sub_nonneg.mpr hxR
    · exact (hweight p hp).le
  rw [Finset.sum_eq_zero_iff_of_nonneg hnonneg]
  constructor
  · intro h p hp
    have hterm := h p hp
    have hfirst : (x p : ℝ) - 1 = 0 :=
      (mul_eq_zero.mp hterm).resolve_right (hweight p hp).ne'
    exact_mod_cast sub_eq_zero.mp hfirst
  · intro h p hp
    rw [h p hp]
    norm_num

private theorem formationLocalFactor_neg (ω L : ℂ) :
    1 - Complex.exp (-(2 * (-ω)) * L) =
      -Complex.exp ((2 * ω) * L) * (1 - Complex.exp (-(2 * ω) * L)) := by
  rw [show -(2 * (-ω)) * L = (2 * ω) * L by ring]
  rw [show -(2 * ω) * L = -((2 * ω) * L) by ring, Complex.exp_neg]
  field_simp [Complex.exp_ne_zero]
  ring

/-- Coordinate-free full-packet reflection law. -/
theorem formationReflectionPacketCoefficient_neg
    (weight : P → ℝ) (x : P →₀ ℕ) (ω : ℂ) :
    formationReflectionPacketCoefficient weight x (-ω) =
      formationReflectionMultiplier weight x ω *
        formationReflectionPacketCoefficient weight x ω := by
  classical
  rw [formationReflectionPacketCoefficient, formationReflectionPacketCoefficient]
  have hprod :
      (∏ p ∈ x.support,
          (1 - Complex.exp (-(2 * (-ω)) * (weight p : ℂ)))) =
        (-1 : ℂ) ^ x.support.card *
          Complex.exp ((2 * ω) * (formationSupportWeight weight x : ℂ)) *
            ∏ p ∈ x.support,
              (1 - Complex.exp (-(2 * ω) * (weight p : ℂ))) := by
    calc
      _ = ∏ p ∈ x.support,
          (-Complex.exp ((2 * ω) * (weight p : ℂ)) *
            (1 - Complex.exp (-(2 * ω) * (weight p : ℂ)))) := by
              refine Finset.prod_congr rfl fun p _ => formationLocalFactor_neg ω _
      _ = (∏ p ∈ x.support, -Complex.exp ((2 * ω) * (weight p : ℂ))) *
            ∏ p ∈ x.support,
              (1 - Complex.exp (-(2 * ω) * (weight p : ℂ))) :=
              Finset.prod_mul_distrib
      _ = ((-1 : ℂ) ^ x.support.card *
            ∏ p ∈ x.support, Complex.exp ((2 * ω) * (weight p : ℂ))) *
            ∏ p ∈ x.support,
              (1 - Complex.exp (-(2 * ω) * (weight p : ℂ))) := by
              rw [Finset.prod_neg]
      _ = (-1 : ℂ) ^ x.support.card *
          Complex.exp ((2 * ω) * (formationSupportWeight weight x : ℂ)) *
            ∏ p ∈ x.support,
              (1 - Complex.exp (-(2 * ω) * (weight p : ℂ))) := by
              rw [← Complex.exp_sum]
              rw [formationSupportWeight]
              push_cast
              rw [Finset.mul_sum]
  rw [hprod, formationReflectionMultiplier, formationMultiplicityDefect]
  have hexp :
      Complex.exp ((-ω) * (formationTotalWeight weight x : ℂ)) *
          Complex.exp ((2 * ω) * (formationSupportWeight weight x : ℂ)) =
        Complex.exp (-(2 * ω) *
            ((formationTotalWeight weight x - formationSupportWeight weight x : ℝ) : ℂ)) *
          Complex.exp (ω * (formationTotalWeight weight x : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    Complex.exp ((-ω) * (formationTotalWeight weight x : ℂ)) *
        ((-1 : ℂ) ^ x.support.card *
          Complex.exp ((2 * ω) * (formationSupportWeight weight x : ℂ)) *
            ∏ p ∈ x.support,
              (1 - Complex.exp (-(2 * ω) * (weight p : ℂ)))) =
      (-1 : ℂ) ^ x.support.card *
        (Complex.exp ((-ω) * (formationTotalWeight weight x : ℂ)) *
          Complex.exp ((2 * ω) * (formationSupportWeight weight x : ℂ))) *
            ∏ p ∈ x.support,
              (1 - Complex.exp (-(2 * ω) * (weight p : ℂ))) := by ring
    _ = (-1 : ℂ) ^ x.support.card *
        (Complex.exp (-(2 * ω) *
            ((formationTotalWeight weight x - formationSupportWeight weight x : ℝ) : ℂ)) *
          Complex.exp (ω * (formationTotalWeight weight x : ℂ))) *
            ∏ p ∈ x.support,
              (1 - Complex.exp (-(2 * ω) * (weight p : ℂ))) := by rw [hexp]
    _ = (-1 : ℂ) ^ x.support.card *
        Complex.exp (-(2 * ω) *
          ((formationTotalWeight weight x - formationSupportWeight weight x : ℝ) : ℂ)) *
          (Complex.exp (ω * (formationTotalWeight weight x : ℂ)) *
            ∏ p ∈ x.support,
              (1 - Complex.exp (-(2 * ω) * (weight p : ℂ)))) := by ring

theorem formationReflectionMultiplier_neg_mul
    (weight : P → ℝ) (x : P →₀ ℕ) (ω : ℂ) :
    formationReflectionMultiplier weight x (-ω) *
      formationReflectionMultiplier weight x ω = 1 := by
  rw [formationReflectionMultiplier, formationReflectionMultiplier]
  have hsign :
      ((-1 : ℂ) ^ x.support.card) * ((-1 : ℂ) ^ x.support.card) = 1 := by
    rw [← pow_add]
    simp [← two_mul]
  have hexp :
      Complex.exp (-(2 * (-ω)) * (formationMultiplicityDefect weight x : ℂ)) *
        Complex.exp (-(2 * ω) * (formationMultiplicityDefect weight x : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    have harg :
        -(2 * (-ω)) * (formationMultiplicityDefect weight x : ℂ) +
          -(2 * ω) * (formationMultiplicityDefect weight x : ℂ) = 0 := by ring
    rw [harg, Complex.exp_zero]
  calc
    ((-1 : ℂ) ^ x.support.card *
        Complex.exp (-(2 * (-ω)) * (formationMultiplicityDefect weight x : ℂ))) *
      ((-1 : ℂ) ^ x.support.card *
        Complex.exp (-(2 * ω) * (formationMultiplicityDefect weight x : ℂ))) =
      (((-1 : ℂ) ^ x.support.card) * ((-1 : ℂ) ^ x.support.card)) *
        (Complex.exp (-(2 * (-ω)) * (formationMultiplicityDefect weight x : ℂ)) *
          Complex.exp (-(2 * ω) * (formationMultiplicityDefect weight x : ℂ))) := by ring
    _ = 1 := by rw [hsign, hexp, one_mul]

theorem norm_formationReflectionMultiplier_ofReal
    (weight : P → ℝ) (x : P →₀ ℕ) (a : ℝ) :
    ‖formationReflectionMultiplier weight x (a : ℂ)‖ =
      Real.exp (-2 * a * formationMultiplicityDefect weight x) := by
  rw [formationReflectionMultiplier, norm_mul, norm_pow, Complex.norm_exp]
  simp only [norm_neg, norm_one, one_pow, one_mul]
  congr 1
  simp

theorem formationReflectionMultiplier_div_norm_ofReal
    (weight : P → ℝ) (x : P →₀ ℕ) (a : ℝ) :
    formationReflectionMultiplier weight x (a : ℂ) /
        (‖formationReflectionMultiplier weight x (a : ℂ)‖ : ℂ) =
      (-1 : ℂ) ^ x.support.card := by
  rw [norm_formationReflectionMultiplier_ofReal, formationReflectionMultiplier]
  rw [Complex.ofReal_exp]
  have hexp :
      Complex.exp (-(2 * (a : ℂ)) * (formationMultiplicityDefect weight x : ℂ)) =
        Complex.exp ((-2 * a * formationMultiplicityDefect weight x : ℝ) : ℂ) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  have hne :
      Complex.exp ((-2 * a * formationMultiplicityDefect weight x : ℝ) : ℂ) ≠ 0 :=
    Complex.exp_ne_zero _
  field_simp

theorem norm_formationReflectionMultiplier_eq_one_iff
    {weight : P → ℝ} (x : P →₀ ℕ) (hweight : ∀ p ∈ x.support, 0 < weight p)
    {a : ℝ} (ha : 0 < a) :
    ‖formationReflectionMultiplier weight x (a : ℂ)‖ = 1 ↔ FormationSquarefree x := by
  rw [norm_formationReflectionMultiplier_ofReal, Real.exp_eq_one_iff]
  constructor
  · intro h
    apply (formationMultiplicityDefect_eq_zero_iff x hweight).mp
    nlinarith
  · intro h
    rw [(formationMultiplicityDefect_eq_zero_iff x hweight).mpr h]
    ring

/-- Universal boundary-phase theorem: exterior projection plus normalized reflection is the
Möbius law of every weighted free-commutative formation monoid. -/
theorem formationMobius_eq_reflection_boundaryPhase
    {weight : P → ℝ} (x : P →₀ ℕ) (hweight : ∀ p ∈ x.support, 0 < weight p)
    {a : ℝ} (ha : 0 < a) :
    formationMobius x =
      if ‖formationReflectionMultiplier weight x (a : ℂ)‖ = 1 then
        formationReflectionMultiplier weight x (a : ℂ) /
          (‖formationReflectionMultiplier weight x (a : ℂ)‖ : ℂ)
      else 0 := by
  by_cases hx : FormationSquarefree x
  · have hunit : ‖formationReflectionMultiplier weight x (a : ℂ)‖ = 1 :=
      (norm_formationReflectionMultiplier_eq_one_iff x hweight ha).mpr hx
    rw [formationMobius, if_pos hx, if_pos hunit,
      formationReflectionMultiplier_div_norm_ofReal]
  · have hnonunit : ‖formationReflectionMultiplier weight x (a : ℂ)‖ ≠ 1 := by
      intro hunit
      exact hx ((norm_formationReflectionMultiplier_eq_one_iff x hweight ha).mp hunit)
    rw [formationMobius, if_neg hx, if_neg hnonunit]

end

end GaloisForLFunctions.HTGeometry
