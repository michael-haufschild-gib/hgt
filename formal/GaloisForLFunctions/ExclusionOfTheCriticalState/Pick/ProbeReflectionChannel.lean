import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeSectorGrams
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Reflection averaging on the actual zero space

Averaging an observable with its conjugate by zero reflection removes precisely
its cross-sector part. The retained part is a conditional expectation onto the
reflection commutant. Multiplying the discarded part by an exponential gives
an exact dephasing semigroup.

This specializes unitary-conjugation averaging from Dzhenzher,
*Singularising quantum channels preserving kappa-additivity*, §3, to the
finite reflection group. No singularisation assertion is made for this group.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk

abbrev ZeroObservable := ZeroSpace →L[ℂ] ZeroSpace

/-- Conjugation by the actual critical-line reflection. -/
def reflectedObservable (A : ZeroObservable) : ZeroObservable :=
  zeroReflection * A * zeroReflection

/-- Reflection-invariant part of an observable. -/
def evenObservable (A : ZeroObservable) : ZeroObservable :=
  (1 / 2 : ℂ) • (A + reflectedObservable A)

/-- Cross-sector part of an observable. -/
def oddObservable (A : ZeroObservable) : ZeroObservable :=
  (1 / 2 : ℂ) • (A - reflectedObservable A)

theorem reflectedObservable_involutive (A : ZeroObservable) :
    reflectedObservable (reflectedObservable A) = A := by
  unfold reflectedObservable
  calc
    _ = (zeroReflection * zeroReflection) * A * (zeroReflection * zeroReflection) := by
      simp only [mul_assoc]
    _ = A := by rw [zeroReflection_sq, one_mul, mul_one]

theorem reflectedObservable_add (A B : ZeroObservable) :
    reflectedObservable (A + B) = reflectedObservable A + reflectedObservable B := by
  simp only [reflectedObservable, mul_add, add_mul]

theorem reflectedObservable_sub (A B : ZeroObservable) :
    reflectedObservable (A - B) = reflectedObservable A - reflectedObservable B := by
  simp only [reflectedObservable, mul_sub, sub_mul]

theorem reflectedObservable_smul (c : ℂ) (A : ZeroObservable) :
    reflectedObservable (c • A) = c • reflectedObservable A := by
  simp only [reflectedObservable, mul_smul_comm, smul_mul_assoc]

theorem reflectedObservable_even (A : ZeroObservable) :
    reflectedObservable (evenObservable A) = evenObservable A := by
  rw [evenObservable, reflectedObservable_smul, reflectedObservable_add,
    reflectedObservable_involutive]
  module

theorem reflectedObservable_odd (A : ZeroObservable) :
    reflectedObservable (oddObservable A) = -oddObservable A := by
  rw [oddObservable, reflectedObservable_smul, reflectedObservable_sub,
    reflectedObservable_involutive]
  module

theorem evenObservable_add_oddObservable (A : ZeroObservable) :
    evenObservable A + oddObservable A = A := by
  unfold evenObservable oddObservable
  module

/-- Reflection averaging fixes exactly the observables preserving both sectors. -/
theorem evenObservable_eq_self_iff (A : ZeroObservable) :
    evenObservable A = A ↔ zeroReflection * A = A * zeroReflection := by
  have hconj : reflectedObservable A = A ↔ zeroReflection * A = A * zeroReflection := by
    constructor
    · intro h
      have hm := congrArg (fun B : ZeroObservable => B * zeroReflection) h
      simpa only [reflectedObservable, mul_assoc, zeroReflection_sq, mul_one] using hm
    · intro h
      rw [reflectedObservable, h, mul_assoc, zeroReflection_sq, mul_one]
  rw [← hconj]
  constructor
  · intro h
    apply sub_eq_zero.mp
    calc
      reflectedObservable A - A = (2 : ℂ) • (evenObservable A - A) := by
        unfold evenObservable
        module
      _ = 0 := by rw [h, sub_self, smul_zero]
  · intro h
    rw [evenObservable, h]
    module

/-- Averaging is idempotent, so every cross-sector term is removed in one step. -/
theorem evenObservable_idempotent (A : ZeroObservable) :
    evenObservable (evenObservable A) = evenObservable A := by
  rw [evenObservable, reflectedObservable_even]
  module

/-- Averaging respects left and right multiplication by already invariant observables. -/
theorem evenObservable_bimodule (A B C : ZeroObservable) :
    evenObservable (evenObservable A * B * evenObservable C) =
      evenObservable A * evenObservable B * evenObservable C := by
  have hA := (evenObservable_eq_self_iff (evenObservable A)).mp
    (evenObservable_idempotent A)
  have hC := (evenObservable_eq_self_iff (evenObservable C)).mp
    (evenObservable_idempotent C)
  have hmul : reflectedObservable (evenObservable A * B * evenObservable C) =
      evenObservable A * reflectedObservable B * evenObservable C := by
    unfold reflectedObservable
    calc
      _ = (zeroReflection * evenObservable A) * B *
          (evenObservable C * zeroReflection) := by simp only [mul_assoc]
      _ = (evenObservable A * zeroReflection) * B *
          (zeroReflection * evenObservable C) := by rw [hA, ← hC]
      _ = _ := by simp only [mul_assoc]
  change (1 / 2 : ℂ) • (evenObservable A * B * evenObservable C +
    reflectedObservable (evenObservable A * B * evenObservable C)) = _
  rw [hmul]
  change _ = evenObservable A * ((1 / 2 : ℂ) • (B + reflectedObservable B)) * evenObservable C
  simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul]

/-- Sector attenuation, defined for every complex attenuation parameter. -/
def reflectionAttenuation (q : ℂ) (A : ZeroObservable) : ZeroObservable :=
  evenObservable A + q • oddObservable A

private theorem even_attenuation (q : ℂ) (A : ZeroObservable) :
    evenObservable (reflectionAttenuation q A) = evenObservable A := by
  rw [reflectionAttenuation, evenObservable, reflectedObservable_add,
    reflectedObservable_smul, reflectedObservable_even, reflectedObservable_odd]
  module

private theorem odd_attenuation (q : ℂ) (A : ZeroObservable) :
    oddObservable (reflectionAttenuation q A) = q • oddObservable A := by
  rw [reflectionAttenuation, oddObservable, reflectedObservable_add,
    reflectedObservable_smul, reflectedObservable_even, reflectedObservable_odd]
  module

/-- Attenuation parameters multiply exactly; there is no discretization error. -/
theorem reflectionAttenuation_mul (q r : ℂ) (A : ZeroObservable) :
    reflectionAttenuation q (reflectionAttenuation r A) =
      reflectionAttenuation (q * r) A := by
  rw [reflectionAttenuation, even_attenuation, odd_attenuation,
    reflectionAttenuation, mul_smul]

/-- The attenuation is explicitly an average of two reflection conjugations. -/
theorem reflectionAttenuation_eq_average (q : ℂ) (A : ZeroObservable) :
    reflectionAttenuation q A =
      ((1 + q) / 2) • A + ((1 - q) / 2) • reflectedObservable A := by
  unfold reflectionAttenuation evenObservable oddObservable
  module

/-- The exact disturbance is a scalar multiple of the reflection double commutator. -/
theorem reflectionAttenuation_sub (q : ℂ) (A : ZeroObservable) :
    reflectionAttenuation q A - A =
      ((q - 1) / 4) • (zeroReflection * (zeroReflection * A - A * zeroReflection) -
        (zeroReflection * A - A * zeroReflection) * zeroReflection) := by
  have hd : zeroReflection * (zeroReflection * A - A * zeroReflection) -
      (zeroReflection * A - A * zeroReflection) * zeroReflection =
      2 • (A - reflectedObservable A) := by
    simp only [mul_sub, sub_mul, ← mul_assoc, zeroReflection_sq, one_mul]
    rw [mul_assoc A zeroReflection zeroReflection, zeroReflection_sq, mul_one]
    unfold reflectedObservable
    module
  rw [hd, reflectionAttenuation_eq_average]
  module

/-- Exponential decay of cross-sector observables in nonnegative time. -/
def reflectionDephasing (t : NNReal) (A : ZeroObservable) : ZeroObservable :=
  reflectionAttenuation (Real.exp (-(t : ℝ)) : ℂ) A

theorem reflectionDephasing_zero (A : ZeroObservable) : reflectionDephasing 0 A = A := by
  change reflectionAttenuation (Real.exp (-(0 : ℝ)) : ℂ) A = A
  rw [neg_zero, Real.exp_zero, Complex.ofReal_one, reflectionAttenuation,
    one_smul, evenObservable_add_oddObservable]

/-- Unitary averaging generates an exact time-additive dephasing semigroup. -/
theorem reflectionDephasing_add (s t : NNReal) (A : ZeroObservable) :
    reflectionDephasing s (reflectionDephasing t A) = reflectionDephasing (s + t) A := by
  rw [reflectionDephasing, reflectionDephasing, reflectionAttenuation_mul,
    reflectionDephasing]
  congr 1
  rw [NNReal.coe_add, neg_add, Real.exp_add, Complex.ofReal_mul]

private theorem norm_reflectedObservable_le (A : ZeroObservable) :
    ‖reflectedObservable A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  change ‖zeroReflection (A (zeroReflection x))‖ ≤ ‖A‖ * ‖x‖
  rw [norm_zeroReflection, ← norm_zeroReflection x]
  exact A.le_opNorm _

theorem norm_reflectedObservable (A : ZeroObservable) :
    ‖reflectedObservable A‖ = ‖A‖ := by
  apply le_antisymm (norm_reflectedObservable_le A)
  simpa only [reflectedObservable_involutive] using
    norm_reflectedObservable_le (reflectedObservable A)

private theorem reflectionDephasing_average (t : NNReal) (A : ZeroObservable) :
    reflectionDephasing t A =
      (((1 + Real.exp (-(t : ℝ))) / 2 : ℝ) : ℂ) • A +
      (((1 - Real.exp (-(t : ℝ))) / 2 : ℝ) : ℂ) • reflectedObservable A := by
  simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_ofNat] using
    reflectionAttenuation_eq_average (Real.exp (-(t : ℝ)) : ℂ) A

/-- The dephasing semigroup contracts the operator norm at every nonnegative time. -/
theorem norm_reflectionDephasing_le (t : NNReal) (A : ZeroObservable) :
    ‖reflectionDephasing t A‖ ≤ ‖A‖ := by
  have hp : 0 ≤ (1 + Real.exp (-(t : ℝ))) / 2 := by positivity
  have hm : 0 ≤ (1 - Real.exp (-(t : ℝ))) / 2 := by
    have he : Real.exp (-(t : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr t.2)
    exact div_nonneg (sub_nonneg.mpr he) (by norm_num)
  rw [reflectionDephasing_average]
  calc
    _ ≤ ‖(((1 + Real.exp (-(t : ℝ))) / 2 : ℝ) : ℂ) • A‖ +
        ‖(((1 - Real.exp (-(t : ℝ))) / 2 : ℝ) : ℂ) • reflectedObservable A‖ := norm_add_le _ _
    _ = ‖A‖ := by
      rw [norm_smul, norm_smul, norm_reflectedObservable]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hm]
      ring

/-- Exact exponential decay of the cross-sector disturbance in operator norm. -/
theorem reflectionDephasing_error (t : NNReal) (A : ZeroObservable) :
    ‖reflectionDephasing t A - evenObservable A‖ =
      Real.exp (-(t : ℝ)) * ‖oddObservable A‖ := by
  rw [reflectionDephasing, reflectionAttenuation, add_sub_cancel_left, norm_smul]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Positive square observables remain positive, with an explicit sum of two squared norms. -/
theorem reflectionDephasing_square_energy (t : NNReal) (T : ZeroObservable) (x : ZeroSpace) :
    (inner ℂ x (reflectionDephasing t (T.adjoint * T) x)).re =
      (1 + Real.exp (-(t : ℝ))) / 2 * ‖T x‖ ^ 2 +
      (1 - Real.exp (-(t : ℝ))) / 2 * ‖T (zeroReflection x)‖ ^ 2 := by
  rw [reflectionDephasing_average]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply, reflectedObservable, inner_add_right, inner_smul_right]
  rw [← zeroReflection_inner_left, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    Complex.ofReal_re]

/-- Positivity follows from the constructed square observable, without a spectral premise. -/
theorem reflectionDephasing_square_nonneg (t : NNReal) (T : ZeroObservable) (x : ZeroSpace) :
    0 ≤ (inner ℂ x (reflectionDephasing t (T.adjoint * T) x)).re := by
  rw [reflectionDephasing_square_energy]
  have he : Real.exp (-(t : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr t.2)
  exact add_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
    (mul_nonneg (div_nonneg (sub_nonneg.mpr he) (by norm_num)) (sq_nonneg _))

#print axioms evenObservable_eq_self_iff
#print axioms evenObservable_bimodule
#print axioms reflectionAttenuation_mul
#print axioms reflectionAttenuation_sub
#print axioms reflectionDephasing_add
#print axioms norm_reflectionDephasing_le
#print axioms reflectionDephasing_error
#print axioms reflectionDephasing_square_nonneg

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
