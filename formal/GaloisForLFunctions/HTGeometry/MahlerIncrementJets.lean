import GaloisForLFunctions.HTGeometry.MahlerOstrowski

/-!
# Jets of a Mahler increment

The increments of the reduced-trace Mahler equations are of the form `A·h⁻¹` with `A` in the
perfect base.  Because the twisting coordinate is a constant of the commuting derivation, the jets
of such an increment are again of that form, with `A` replaced by its Euler jets and the power of
the twisting coordinate raised by one at each step.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc Differential

noncomputable section

variable {k : Type*} [Field k]

/-- The Mahler coordinate `w` inside the perfect base. -/
def wCoord (p : ℕ) (hp : 1 < p) : perfectBase (k := k) p hp :=
  ⟨ratFuncToHahn RatFunc.X, ratFuncToHahn_mem_perfectBase p hp _⟩

theorem ratFuncEulerOp_X : ratFuncEulerOp (RatFunc.X : RatFunc k) = RatFunc.X := by
  rw [ratFuncEulerOp]
  have hX : (RatFunc.X : RatFunc k)
      = algebraMap (Polynomial k) (RatFunc k) (Polynomial.X) := (RatFunc.algebraMap_X).symm
  rw [hX, ratFuncDerivative_algebraMap, Polynomial.derivative_X, map_one, mul_one]

theorem perfectBaseDeriv_wCoord [CharZero k] (p : ℕ) (hp : 1 < p) :
    perfectBaseDeriv p hp (wCoord (k := k) p hp) = wCoord (k := k) p hp := by
  refine Subtype.ext ?_
  show hahnQEuler (ratFuncToHahn (RatFunc.X : RatFunc k)) = ratFuncToHahn RatFunc.X
  rw [← ratFuncToHahn_eulerOp, ratFuncEulerOp_X]

theorem perfectConst_mul (p : ℕ) (hp : 1 < p) (c d : k) :
    perfectConst (k := k) p hp c * perfectConst p hp d = perfectConst p hp (c * d) := by
  refine Subtype.ext ?_
  show (HahnSeries.C c : HahnSeries ℚ k) * HahnSeries.C d = HahnSeries.C (c * d)
  rw [map_mul]

theorem perfectConst_one (p : ℕ) (hp : 1 < p) :
    perfectConst (k := k) p hp 1 = 1 := by
  refine Subtype.ext ?_
  show (HahnSeries.C (1 : k) : HahnSeries ℚ k) = 1
  rw [map_one]

theorem perfectBaseDeriv_wCoord_pow [CharZero k] (p : ℕ) (hp : 1 < p) (m : ℕ) :
    perfectBaseDeriv p hp (wCoord (k := k) p hp ^ m)
      = perfectConst p hp ((m : k)) * wCoord (k := k) p hp ^ m := by
  induction m with
  | zero =>
      rw [pow_zero, Nat.cast_zero]
      have h0 : perfectConst (k := k) p hp 0 = 0 := by
        refine Subtype.ext ?_
        show (HahnSeries.C (0 : k) : HahnSeries ℚ k) = 0
        rw [map_zero]
      rw [h0, zero_mul]
      have h1 : perfectBaseDeriv p hp (1 : perfectBase (k := k) p hp) = 0 := by
        have h := perfectBaseDeriv_leibniz p hp (1 : perfectBase (k := k) p hp) 1
        rw [one_mul, mul_one, one_mul] at h
        linear_combination -h
      exact h1
  | succ m ih =>
      rw [pow_succ, perfectBaseDeriv_leibniz, ih, perfectBaseDeriv_wCoord, Nat.cast_succ]
      have hc : perfectConst (k := k) p hp (((m : k)) + 1)
          = perfectConst p hp ((m : k)) + perfectConst p hp 1 := by
        refine Subtype.ext ?_
        show (HahnSeries.C (((m : k)) + 1) : HahnSeries ℚ k)
          = HahnSeries.C ((m : k)) + HahnSeries.C 1
        rw [map_add]
      rw [hc, perfectConst_one]
      ring

/-! ## The twisting coordinate is a constant of the base derivation -/

section Base

variable {F : Type*} [Field F] [Differential F]

theorem coeffDeriv_C (a : F) : coeffDeriv (Polynomial.C a) = Polynomial.C (a′) := by
  refine Polynomial.ext fun n => ?_
  rw [coeffDeriv_coeff, Polynomial.coeff_C, Polynomial.coeff_C]
  by_cases h : n = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, map_zero]

theorem twoCylDerivation_algebraMap_const (a : F) :
    twoCylDerivation (0 : F) (algebraMap F (RatFunc F) a)
      = algebraMap F (RatFunc F) (a′) := by
  have hC : (algebraMap F (RatFunc F) a)
      = algebraMap (Polynomial F) (RatFunc F) (Polynomial.C a) := (RatFunc.algebraMap_C a).symm
  rw [hC, twoCylDerivation_algebraMap, coeffDeriv_C, Polynomial.derivative_C, map_zero,
    map_zero, zero_mul, zero_mul, add_zero]
  exact RatFunc.algebraMap_C a′

theorem coeffDeriv_X : coeffDeriv (Polynomial.X : Polynomial F) = 0 := by
  refine Polynomial.ext fun n => ?_
  rw [coeffDeriv_coeff, Polynomial.coeff_X, Polynomial.coeff_zero]
  by_cases h : 1 = n
  · rw [if_pos h, Derivation.map_one_eq_zero]
  · rw [if_neg h, map_zero]

theorem twoCylDerivation_X_zero : twoCylDerivation (0 : F) (RatFunc.X : RatFunc F) = 0 := by
  have hX : (RatFunc.X : RatFunc F)
      = algebraMap (Polynomial F) (RatFunc F) Polynomial.X := (RatFunc.algebraMap_X).symm
  rw [hX, twoCylDerivation_algebraMap, coeffDeriv_X, map_zero, map_zero, zero_mul, zero_mul,
    add_zero]

theorem twoCylDerivation_one_zero : twoCylDerivation (0 : F) (1 : RatFunc F) = 0 := by
  have h := twoCylDerivation_algebraMap (0 : F) (1 : Polynomial F)
  rw [coeffDeriv_one, Polynomial.derivative_one, map_zero, map_zero, zero_mul, zero_mul,
    add_zero, map_one] at h
  exact h

theorem twoCylDerivation_XInv : twoCylDerivation (0 : F) ((RatFunc.X : RatFunc F)⁻¹) = 0 := by
  have hmul : (RatFunc.X : RatFunc F) * (RatFunc.X : RatFunc F)⁻¹ = 1 :=
    mul_inv_cancel₀ RatFunc.X_ne_zero
  have h := congrArg (twoCylDerivation (0 : F)) hmul
  rw [twoCylDerivation_leibniz, twoCylDerivation_one_zero, twoCylDerivation_X_zero,
    mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left RatFunc.X_ne_zero

theorem twoCylDerivation_XInv_pow (m : ℕ) :
    twoCylDerivation (0 : F) (((RatFunc.X : RatFunc F)⁻¹) ^ m) = 0 := by
  induction m with
  | zero => rw [pow_zero, twoCylDerivation_one_zero]
  | succ m ih =>
      rw [pow_succ, twoCylDerivation_leibniz, ih, twoCylDerivation_XInv, mul_zero, zero_add,
        mul_zero]

end Base

/-! ## The jets of an increment -/

theorem differentialJet_base_increment [CharZero k] (p : ℕ) (hp : 1 < p) (A : perfectBase (k := k) p hp) :
    letI := perfectAlgebra (k := k) p hp
    letI := perfectDifferential (k := k) p hp
    letI := mahlerPBaseDifferential (k := k) p hp
    ∀ j : ℕ, differentialJet j
        (algebraMap (perfectBase (k := k) p hp) (MahlerPBase k p hp) A * (RatFunc.X)⁻¹)
      = algebraMap (perfectBase (k := k) p hp) (MahlerPBase k p hp) (differentialJet j A)
        * ((RatFunc.X : MahlerPBase k p hp)⁻¹) ^ (j + 1) := by
  letI := perfectAlgebra (k := k) p hp
  letI := perfectDifferential (k := k) p hp
  letI := mahlerPBaseDifferential (k := k) p hp
  intro j
  induction j with
  | zero => rw [differentialJet_zero, differentialJet_zero, pow_one]
  | succ j ih =>
      rw [differentialJet_succ, ih, mahlerPBaseDifferential_deriv, twoCylDerivation_leibniz,
        twoCylDerivation_algebraMap_const, twoCylDerivation_XInv_pow, mul_zero, zero_add,
        differentialJet_succ, pow_succ]
      ring

/-! ## The increment of the reduced-trace Mahler equation -/

theorem perfectBaseDeriv_perfectConst [CharZero k] (p : ℕ) (hp : 1 < p) (c : k) :
    perfectBaseDeriv p hp (perfectConst p hp c) = 0 := by
  refine Subtype.ext ?_
  show hahnQEuler (HahnSeries.C c : HahnSeries ℚ k) = 0
  refine HahnSeries.coeff_inj.mp (funext fun γ => ?_)
  rw [coeff_hahnQEuler, HahnSeries.coeff_zero, HahnSeries.C_apply]
  by_cases h : γ = 0
  · subst h
    rw [HahnSeries.coeff_single_same]
    norm_num
  · rw [HahnSeries.coeff_single_of_ne h, mul_zero]

/-- The `j`-th jet coefficient of the reduced-trace increment. -/
def traceCoeff (p : ℕ) (hp : 1 < p) (j : ℕ) : perfectBase (k := k) p hp :=
  -(perfectConst p hp (((p : k)) - 2) * wCoord p hp
    + perfectConst p hp (((p : k)) ^ j) * wCoord p hp ^ p)

theorem differentialJet_traceCoeff [CharZero k] (p : ℕ) (hp : 1 < p) (j : ℕ) :
    letI := perfectAlgebra (k := k) p hp
    letI := perfectDifferential (k := k) p hp
    differentialJet j (traceCoeff (k := k) p hp 0) = traceCoeff (k := k) p hp j := by
  letI := perfectAlgebra (k := k) p hp
  letI := perfectDifferential (k := k) p hp
  induction j with
  | zero => rw [differentialJet_zero]
  | succ j ih =>
      rw [differentialJet_succ, ih, perfectDifferential_deriv, traceCoeff, traceCoeff,
        map_neg, map_add, perfectBaseDeriv_leibniz, perfectBaseDeriv_leibniz,
        perfectBaseDeriv_perfectConst, perfectBaseDeriv_perfectConst, perfectBaseDeriv_wCoord,
        perfectBaseDeriv_wCoord_pow, zero_mul, zero_mul, zero_add, zero_add,
        ← mul_assoc, perfectConst_mul]
      rw [show (((p : k)) ^ j * (p : k)) = ((p : k)) ^ (j + 1) from by rw [pow_succ]]

/-- The increment of the reduced-trace Mahler equation, `−((p−2)w + w^p)·h⁻¹`. -/
def traceIncrement (p : ℕ) (hp : 1 < p) : MahlerPBase k p hp :=
  algebraMap (perfectBase (k := k) p hp) (MahlerPBase k p hp) (traceCoeff p hp 0)
    * (RatFunc.X : MahlerPBase k p hp)⁻¹

theorem differentialJet_traceIncrement [CharZero k] (p : ℕ) (hp : 1 < p) (j : ℕ) :
    letI := perfectAlgebra (k := k) p hp
    letI := perfectDifferential (k := k) p hp
    letI := mahlerPBaseDifferential (k := k) p hp
    differentialJet j (traceIncrement (k := k) p hp)
      = algebraMap (perfectBase (k := k) p hp) (MahlerPBase k p hp) (traceCoeff p hp j)
        * ((RatFunc.X : MahlerPBase k p hp)⁻¹) ^ (j + 1) := by
  letI := perfectAlgebra (k := k) p hp
  letI := perfectDifferential (k := k) p hp
  letI := mahlerPBaseDifferential (k := k) p hp
  rw [traceIncrement, differentialJet_base_increment p hp _ j, differentialJet_traceCoeff]

end

end GaloisForLFunctions.HTGeometry
