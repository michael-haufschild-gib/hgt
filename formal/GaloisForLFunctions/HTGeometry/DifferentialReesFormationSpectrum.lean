import GaloisForLFunctions.HTGeometry.AugmentationGradedFormationSpectrum
import GaloisForLFunctions.HTGeometry.FiniteLinearStateDifferentialEscape

/-!
# Differential Rees formation spectrum

The augmentation filtration becomes an intrinsic spectrum under the formation-number connection
`N = (T - 1) d/dT`.  This file proves its exact grade law and reflection covariance.  On a
punctured differential source chart it also proves the finite-state escape forced by
hypertranscendence: no finite state can be closed under both `u ∂` and inverse gauge `u⁻¹`.

These are the Lean certificates for ULF-TAFM-25.
-/

open scoped LaurentPolynomial Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open LaurentPolynomial

/-- Laurent derivative on the integral finite-history algebra. -/
def laurentFormationDerivative
    (P : AugmentationFormationAlgebra) : AugmentationFormationAlgebra :=
  P.coeff.sum fun n a => C (n * a) * T (n - 1)

@[simp] lemma laurentFormationDerivative_add
    (P Q : AugmentationFormationAlgebra) :
    laurentFormationDerivative (P + Q) =
      laurentFormationDerivative P + laurentFormationDerivative Q := by
  unfold laurentFormationDerivative
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index
  · intro n _hn
    simp
  · intro n _hn b₁ b₂
    rw [mul_add, map_add, add_mul]

@[simp] lemma laurentFormationDerivative_C_mul_T (a n : ℤ) :
    laurentFormationDerivative (C a * T n) = C (n * a) * T (n - 1) := by
  calc
    laurentFormationDerivative (C a * T n) =
        laurentFormationDerivative (AddMonoidAlgebra.single n a) := by
      rw [LaurentPolynomial.single_eq_C_mul_T]
    _ = C (n * a) * T (n - 1) := by
      unfold laurentFormationDerivative
      rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index]
      simp

private lemma C_mul_T_mul_C_mul_T (a b m n : ℤ) :
    (C a * T m : AugmentationFormationAlgebra) * (C b * T n) =
      C (a * b) * T (m + n) := by
  rw [← LaurentPolynomial.single_eq_C_mul_T,
    ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.single_mul_single,
    LaurentPolynomial.single_eq_C_mul_T]

private lemma laurentFormationDerivative_mul_C_mul_T
    (P : AugmentationFormationAlgebra) (a n : ℤ) :
    laurentFormationDerivative (P * (C a * T n)) =
      laurentFormationDerivative P * (C a * T n) +
        P * laurentFormationDerivative (C a * T n) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
      rw [add_mul, laurentFormationDerivative_add, hP, hQ,
        laurentFormationDerivative_add]
      ring
  | C_mul_T m b =>
      rw [C_mul_T_mul_C_mul_T, laurentFormationDerivative_C_mul_T,
        laurentFormationDerivative_C_mul_T, laurentFormationDerivative_C_mul_T,
        C_mul_T_mul_C_mul_T, C_mul_T_mul_C_mul_T]
      rw [show m - 1 + n = m + n - 1 by omega,
        show m + (n - 1) = m + n - 1 by omega,
        ← add_mul, ← map_add]
      congr 2
      ring

/-- Laurent formation derivative satisfies the Leibniz rule. -/
theorem laurentFormationDerivative_mul (P Q : AugmentationFormationAlgebra) :
    laurentFormationDerivative (P * Q) =
      laurentFormationDerivative P * Q + P * laurentFormationDerivative Q := by
  induction Q using LaurentPolynomial.induction_on' with
  | add Q S hQ hS =>
      rw [mul_add, laurentFormationDerivative_add, hQ, hS,
        laurentFormationDerivative_add]
      ring
  | C_mul_T n a =>
      exact laurentFormationDerivative_mul_C_mul_T P a n

@[simp] lemma laurentFormationDerivative_zero :
    laurentFormationDerivative (0 : AugmentationFormationAlgebra) = 0 := by
  simp [laurentFormationDerivative]

@[simp] lemma laurentFormationDerivative_neg (P : AugmentationFormationAlgebra) :
    laurentFormationDerivative (-P) = -laurentFormationDerivative P := by
  have h := laurentFormationDerivative_add P (-P)
  rw [add_neg_cancel, laurentFormationDerivative_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

@[simp] lemma laurentFormationDerivative_sub
    (P Q : AugmentationFormationAlgebra) :
    laurentFormationDerivative (P - Q) =
      laurentFormationDerivative P - laurentFormationDerivative Q := by
  rw [sub_eq_add_neg, laurentFormationDerivative_add,
    laurentFormationDerivative_neg, sub_eq_add_neg]

@[simp] lemma laurentFormationDerivative_one :
    laurentFormationDerivative (1 : AugmentationFormationAlgebra) = 0 := by
  rw [← LaurentPolynomial.single_zero_one_eq_one,
    LaurentPolynomial.single_eq_C_mul_T, laurentFormationDerivative_C_mul_T]
  simp

@[simp] lemma laurentFormationDerivative_T_one :
    laurentFormationDerivative
      (T 1 : AugmentationFormationAlgebra) = 1 := by
  rw [← one_mul (T 1 : AugmentationFormationAlgebra), ← map_one C,
    laurentFormationDerivative_C_mul_T]
  norm_num

@[simp] lemma laurentFormationDerivative_augmentationGenerator :
    laurentFormationDerivative
      (T 1 - 1 : AugmentationFormationAlgebra) = 1 := by
  rw [laurentFormationDerivative_sub, laurentFormationDerivative_T_one,
    laurentFormationDerivative_one, sub_zero]

/-- Derivative of every augmentation power. -/
theorem laurentFormationDerivative_augmentationGenerator_pow (r : ℕ) :
    laurentFormationDerivative
        ((T 1 - 1 : AugmentationFormationAlgebra) ^ r) =
      (r : AugmentationFormationAlgebra) * (T 1 - 1) ^ (r - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, laurentFormationDerivative_mul, ih,
        laurentFormationDerivative_augmentationGenerator]
      cases r with
      | zero => simp
      | succ r =>
          push_cast
          rw [pow_succ]
          ring

/-- Formation-number connection `N = (T - 1) d/dT`. -/
def formationNumber
    (P : AugmentationFormationAlgebra) : AugmentationFormationAlgebra :=
  (T 1 - 1) * laurentFormationDerivative P

/-- Exact Euler connection law on every augmentation boundary. -/
theorem formationNumber_boundary (r : ℕ) (P : AugmentationFormationAlgebra) :
    formationNumber (augmentationFormationBoundary r P) =
      (r : AugmentationFormationAlgebra) * augmentationFormationBoundary r P +
        augmentationFormationBoundary (r + 1) (laurentFormationDerivative P) := by
  rw [formationNumber, augmentationFormationBoundary,
    laurentFormationDerivative_mul,
    laurentFormationDerivative_augmentationGenerator_pow]
  cases r with
  | zero => simp [augmentationFormationBoundary]
  | succ r =>
      rw [show r + 1 - 1 = r by omega, pow_succ]
      simp only [augmentationFormationBoundary, pow_succ]
      ring

/-- Formation number acts by `r` on the `r`-th associated augmentation grade. -/
theorem formationNumber_associatedGrade (r : ℕ) (P : AugmentationFormationAlgebra) :
    SameModuloAugmentationBoundary (r + 1)
      (formationNumber (augmentationFormationBoundary r P))
      ((r : AugmentationFormationAlgebra) * augmentationFormationBoundary r P) := by
  refine ⟨laurentFormationDerivative P, ?_⟩
  rw [formationNumber_boundary]
  ring

/-- Laurent inversion reverses the coordinate derivative with its exact Jacobian. -/
theorem laurentFormationDerivative_invert (P : AugmentationFormationAlgebra) :
    laurentFormationDerivative (invert P) =
      -(T (-2) * invert (laurentFormationDerivative P)) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
      rw [map_add, laurentFormationDerivative_add, hP, hQ,
        laurentFormationDerivative_add, map_add]
      ring
  | C_mul_T n a =>
      rw [map_mul, invert_C, invert_T,
        laurentFormationDerivative_C_mul_T,
        laurentFormationDerivative_C_mul_T]
      have hinv :
          invert (C (n * a) * T (n - 1) : AugmentationFormationAlgebra) =
            C (n * a) * T (1 - n) := by
        rw [map_mul, invert_C, invert_T]
        congr 2
        omega
      rw [hinv]
      rw [show (T (-2) : AugmentationFormationAlgebra) =
          C 1 * T (-2) by simp,
        C_mul_T_mul_C_mul_T]
      simp only [one_mul]
      rw [← neg_mul, ← map_neg]
      congr 2
      · ring
      · omega

/-- Formation number has exact twisted covariance under Laurent reflection. -/
theorem formationNumber_invert (P : AugmentationFormationAlgebra) :
    formationNumber (invert P) = T (-1) * invert (formationNumber P) := by
  rw [formationNumber, laurentFormationDerivative_invert, formationNumber,
    map_mul, invert_augmentationGenerator]
  have hT :
      (T (-1 : ℤ) : AugmentationFormationAlgebra) * T (-1) = T (-2) := by
    rw [← T_add]
    norm_num
  rw [← hT]
  ring

private lemma formationNumber_boundary_factor (r : ℕ)
    (P : AugmentationFormationAlgebra) :
    formationNumber (augmentationFormationBoundary r P) =
      augmentationFormationBoundary r
        ((r : AugmentationFormationAlgebra) * P +
          (T 1 - 1) * laurentFormationDerivative P) := by
  rw [formationNumber_boundary]
  simp only [augmentationFormationBoundary, pow_succ]
  ring

/-- Reflection and formation number commute on every associated augmentation grade. -/
theorem formationNumber_reflection_associatedGrade
    (r : ℕ) (P : AugmentationFormationAlgebra) :
    SameModuloAugmentationBoundary (r + 1)
      (formationNumber (invert (augmentationFormationBoundary r P)))
      (invert (formationNumber (augmentationFormationBoundary r P))) := by
  rw [formationNumber_invert]
  let Q : AugmentationFormationAlgebra :=
    (r : AugmentationFormationAlgebra) * P +
      (T 1 - 1) * laurentFormationDerivative P
  have hfactor :
      formationNumber (augmentationFormationBoundary r P) =
        augmentationFormationBoundary r Q := by
    exact formationNumber_boundary_factor r P
  refine ⟨-T (-1) *
      ((-1 : AugmentationFormationAlgebra) ^ r *
        augmentationHistoryReflection r Q), ?_⟩
  rw [hfactor, invert_augmentationFormationBoundary]
  simp only [augmentationFormationBoundary, pow_succ]
  have hunit :
      (T 1 : AugmentationFormationAlgebra) * T (-1) = 1 := by
    rw [← T_add]
    norm_num
  have hshift :
      (T (-1) - 1 : AugmentationFormationAlgebra) =
        -(T 1 - 1) * T (-1) := by
    rw [neg_mul, sub_mul, hunit, one_mul]
    ring
  rw [show T (-1) *
      ((-1 : AugmentationFormationAlgebra) ^ r *
        ((T 1 - 1) ^ r * augmentationHistoryReflection r Q)) -
      ((-1 : AugmentationFormationAlgebra) ^ r *
        ((T 1 - 1) ^ r * augmentationHistoryReflection r Q)) =
      (T (-1) - 1) *
      ((-1 : AugmentationFormationAlgebra) ^ r *
        ((T 1 - 1) ^ r * augmentationHistoryReflection r Q)) by ring]
  rw [hshift]
  ring

/-- Punctured-chart formation connection `u ∂`. -/
def sourceFormationConnection
    {E : Type*} [Field E] [Differential E] (u x : E) : E :=
  u * x′

/-- A source state closed under formation evolution `u ∂`. -/
def FormationConnectionInvariantSubmodule
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (u : E) (V : Submodule F E) : Prop :=
  ∀ ⦃x : E⦄, x ∈ V → sourceFormationConnection u x ∈ V

/-- A source state closed under inverse punctured-chart gauge `u⁻¹`. -/
def InverseFormationGaugeInvariantSubmodule
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (u : E) (V : Submodule F E) : Prop :=
  ∀ ⦃x : E⦄, x ∈ V → u⁻¹ * x ∈ V

/-- Formation evolution plus inverse-gauge closure reconstructs ordinary differentiation. -/
theorem derivationInvariant_of_formationConnection_and_inverseGauge
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {u : E} (hu : u ≠ 0) {V : Submodule F E}
    (hN : FormationConnectionInvariantSubmodule u V)
    (hG : InverseFormationGaugeInvariantSubmodule u V) :
    DerivationInvariantSubmodule V := by
  intro x hx
  have hNx : sourceFormationConnection u x ∈ V := hN hx
  have hrecover : u⁻¹ * sourceFormationConnection u x ∈ V := hG hNx
  have heq : u⁻¹ * sourceFormationConnection u x = x′ := by
    rw [sourceFormationConnection, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  rw [heq] at hrecover
  exact hrecover

/-- A finite state closed under formation evolution and inverse gauge contains no HT source. -/
theorem not_mem_finiteFormationState_of_hypertranscendentalOver
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {u : E} (hu : u ≠ 0) (V : Submodule F E) [FiniteDimensional F V]
    {x : E} (hx : HypertranscendentalOver F x)
    (hN : FormationConnectionInvariantSubmodule u V)
    (hG : InverseFormationGaugeInvariantSubmodule u V) :
    x ∉ V := by
  exact not_mem_derivationInvariantSubmodule_of_hypertranscendentalOver V hx
    (derivationInvariant_of_formationConnection_and_inverseGauge hu hN hG)

/-- Positive noncompactness witness: a finite formation-stable state containing an HT source loses
some vector under inverse gauge. -/
theorem exists_inverseFormationGauge_escape_of_hypertranscendentalOver
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {u : E} (hu : u ≠ 0) (V : Submodule F E) [FiniteDimensional F V]
    {x : E} (hx : HypertranscendentalOver F x) (hxV : x ∈ V)
    (hN : FormationConnectionInvariantSubmodule u V) :
    ∃ y ∈ V, u⁻¹ * y ∉ V := by
  by_contra h
  have hG : InverseFormationGaugeInvariantSubmodule u V := by
    intro y hy
    by_contra hyout
    exact h ⟨y, hy, hyout⟩
  exact not_mem_finiteFormationState_of_hypertranscendentalOver hu V hx hN hG hxV

end

end GaloisForLFunctions.HTGeometry
