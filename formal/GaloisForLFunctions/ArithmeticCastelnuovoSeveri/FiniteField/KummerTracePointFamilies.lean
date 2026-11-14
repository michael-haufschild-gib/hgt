import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.SquareFieldTraceFibers
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerNormFibers
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomials

/-!
# Rational Kummer fibers from trace-one elements

For `q=p^(d+1)` and `R=1+q+⋯+q^r`, a trace-one element `u` gives the
Kummer ordinate `u^R`. Its normalized branch value is the `R`-th power of
a Frobenius-fixed quotient. Multiplication by a `(q-1)`-st root of unity
in the middle fixed field gives further completely soluble affine fibers.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open Polynomial GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable (p : ℕ) [Fact p.Prime]

/-- A Frobenius difference of a trace-one element is trace-zero. -/
theorem squareTraceOne_difference (s k : ℕ) (u : SquareConstantField p s)
    (hu : u ^ p ^ (s + 1) + u = 1) :
    (u - u ^ p ^ k) ^ p ^ (s + 1) = -(u - u ^ p ^ k) := by
  have hQ : u ^ p ^ (s + 1) = 1 - u := by linear_combination hu
  have hcomm : (u ^ p ^ k) ^ p ^ (s + 1) = (u ^ p ^ (s + 1)) ^ p ^ k := by
    rw [← pow_mul, ← pow_mul]
    exact congrArg (fun n : ℕ => u ^ n) (Nat.mul_comm _ _)
  rw [sub_pow_char_pow, hcomm, hQ, sub_pow_char_pow, one_pow]
  ring

/-- The trace-normalized branch polynomial with prime-power parameter `q`. -/
def normalizedKummerBranch (s d r : ℕ) : (SquareConstantField p s)[X] :=
  kummerBranch ((kummerTraceConstant p s)⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
    (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1))

/-- Evaluation gives the literal normalized Kummer right-hand side. -/
theorem normalizedKummerBranch_eval (s d r : ℕ) (y : SquareConstantField p s) :
    (normalizedKummerBranch p s d r).eval y =
      ((kummerTraceConstant p s : SquareConstantField p s)⁻¹) ^
        kummerExponent (p ^ (d + 1)) (r + 1) * y *
          (1 - y ^ (p ^ (d + 1) - 1)) ^ kummerExponent (p ^ (d + 1)) (r + 1) := by
  have hq : 2 ≤ p ^ (d + 1) := Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  simp only [normalizedKummerBranch, kummerBranch, eval_mul, eval_C, eval_X, eval_pow,
    eval_sub, eval_one, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
    show p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 by omega]

/-- The branch value at `u^R` is an `R`-th power of an Artin–Schreier quotient. -/
theorem normalizedKummerBranch_trace_substitution (s d r : ℕ) (u : SquareConstantField p s) :
    (normalizedKummerBranch p s d r).eval (u ^ kummerExponent (p ^ (d + 1)) (r + 1)) =
      ((u - u ^ (p ^ (d + 1)) ^ (r + 1)) /
        (kummerTraceConstant p s : SquareConstantField p s)) ^
          kummerExponent (p ^ (d + 1)) (r + 1) := by
  have hq : 1 ≤ p ^ (d + 1) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hs := kummer_substitution (p ^ (d + 1) - 1) (r + 1) u
  rw [Nat.sub_add_cancel hq] at hs
  rw [normalizedKummerBranch_eval, div_pow, div_eq_mul_inv, ← inv_pow, hs]
  ring

/-- Scaling by a `(q-1)`-st root of unity scales the branch value by the same factor. -/
theorem normalizedKummerBranch_eval_scale (s d r : ℕ) (a y : SquareConstantField p s)
    (ha : a ^ (p ^ (d + 1) - 1) = 1) :
    (normalizedKummerBranch p s d r).eval (a * y) =
      a * (normalizedKummerBranch p s d r).eval y := by
  rw [normalizedKummerBranch_eval, normalizedKummerBranch_eval, mul_pow, ha, one_mul]
  ring

/-- A trace-one parameter produces a Frobenius-fixed branch value. -/
theorem normalizedKummerBranch_trace_fixed (s d r : ℕ) (u : SquareConstantField p s)
    (hu : u ^ p ^ (s + 1) + u = 1) :
    ((normalizedKummerBranch p s d r).eval
      (u ^ kummerExponent (p ^ (d + 1)) (r + 1))) ^ p ^ (s + 1) =
    (normalizedKummerBranch p s d r).eval (u ^ kummerExponent (p ^ (d + 1)) (r + 1)) := by
  have ht := squareTraceOne_difference p s ((d + 1) * (r + 1)) u hu
  rw [pow_mul] at ht
  have hf := kummerTraceConstant_ratio_fixed p s _ ht
  rw [normalizedKummerBranch_trace_substitution, ← pow_mul,
    Nat.mul_comm (kummerExponent (p ^ (d + 1)) (r + 1)) (p ^ (s + 1)), pow_mul, hf]

/-- Parameters excluded from the auxiliary fixed field give nonzero branch values. -/
theorem normalizedKummerBranch_trace_ne_zero (s d r : ℕ) (u : SquareConstantField p s)
    (hu : u ^ (p ^ (d + 1)) ^ (r + 1) ≠ u) :
    (normalizedKummerBranch p s d r).eval
      (u ^ kummerExponent (p ^ (d + 1)) (r + 1)) ≠ 0 := by
  rw [normalizedKummerBranch_trace_substitution]
  exact pow_ne_zero _ (div_ne_zero (sub_ne_zero.mpr (Ne.symm hu)) (Units.ne_zero _))

/-- Scalar parameters are the `(q-1)`-st roots of unity in the middle fixed field. -/
abbrev KummerTraceScalars (s d : ℕ) :=
  rootsOfUnity (p ^ (d + 1) - 1) (squareFrobeniusFixedField p s)

/-- A scalar parameter viewed as a unit of the ambient field. -/
def kummerTraceScalar (s d : ℕ) (a : KummerTraceScalars p s d) : (SquareConstantField p s)ˣ :=
  Units.map (squareFrobeniusFixedField p s).subtype.toMonoidHom a.val

/-- The scalar retains its defining root-of-unity equation. -/
theorem kummerTraceScalar_pow (s d : ℕ) (a : KummerTraceScalars p s d) :
    (kummerTraceScalar p s d a : SquareConstantField p s) ^ (p ^ (d + 1) - 1) = 1 := by
  have h := (mem_rootsOfUnity (p ^ (d + 1) - 1) a.val).mp a.property
  exact congrArg (fun z : (squareFrobeniusFixedField p s)ˣ =>
    ((z : squareFrobeniusFixedField p s) : SquareConstantField p s)) h

/-- The scalar is fixed by the middle Frobenius. -/
theorem kummerTraceScalar_fixed (s d : ℕ) (a : KummerTraceScalars p s d) :
    (kummerTraceScalar p s d a : SquareConstantField p s) ^ p ^ (s + 1) =
      (kummerTraceScalar p s d a : SquareConstantField p s) := a.val.val.property

/-- Trace-one parameters outside the auxiliary Frobenius fixed field. -/
abbrev KummerTraceParameters (s d r : ℕ) :=
  {u : SquareConstantField p s // u ^ p ^ (s + 1) + u = 1 ∧
    u ^ (p ^ (d + 1)) ^ (r + 1) ≠ u}

/-- The rational ordinate furnished by a scalar and a trace-one parameter. -/
def kummerTraceFamilyPoint (s d r : ℕ) (a : KummerTraceScalars p s d)
    (u : KummerTraceParameters p s d r) : SquareConstantField p s :=
  (kummerTraceScalar p s d a : SquareConstantField p s) *
    u.val ^ kummerExponent (p ^ (d + 1)) (r + 1)

/-- Every ordinate in the trace construction gives exactly `Q+1` rational affine points. -/
theorem kummerTraceFamilyPoint_fiber_card (s d r : ℕ) (a : KummerTraceScalars p s d)
    (u : KummerTraceParameters p s d r) :
    Nat.card {z : SquareConstantField p s | z ^ (p ^ (s + 1) + 1) =
      (normalizedKummerBranch p s d r).eval (kummerTraceFamilyPoint p s d r a u)} =
        p ^ (s + 1) + 1 := by
  have he : (normalizedKummerBranch p s d r).eval (kummerTraceFamilyPoint p s d r a u) =
      (kummerTraceScalar p s d a : SquareConstantField p s) *
        (normalizedKummerBranch p s d r).eval
          (u.val ^ kummerExponent (p ^ (d + 1)) (r + 1)) :=
    normalizedKummerBranch_eval_scale p s d r _ _ (kummerTraceScalar_pow p s d a)
  apply squareConstantField_norm_fiber_card_of_fixed
  · rw [he]
    exact mul_ne_zero (Units.ne_zero _) (normalizedKummerBranch_trace_ne_zero p s d r u.val u.property.2)
  · rw [he, mul_pow, kummerTraceScalar_fixed,
      normalizedKummerBranch_trace_fixed p s d r u.val u.property.1]

/-- A trace-one element outside an auxiliary fixed field has no distinct trace-one
multiple by an element of that fixed field. -/
theorem trace_one_ratio_rigidity (s k : ℕ) (u v : SquareConstantField p s)
    (hu : u ^ p ^ (s + 1) + u = 1) (hv : v ^ p ^ (s + 1) + v = 1)
    (hvA : v ^ p ^ k ≠ v) (hfixedRatio : (u / v) ^ p ^ k = u / v) : u = v := by
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), add_zero] at hv
    exact zero_ne_one hv
  let a := u / v
  let D := (iterateFrobenius (SquareConstantField p s) p k).eqLocusField (RingHom.id _)
  have ha : a ∈ D := hfixedRatio
  have haQ : a ^ p ^ (s + 1) ∈ D := by
    change (a ^ p ^ (s + 1)) ^ p ^ k = a ^ p ^ (s + 1)
    rw [← pow_mul, Nat.mul_comm (p ^ (s + 1)) (p ^ k), pow_mul, hfixedRatio]
  have huv : u = a * v := (div_mul_cancel₀ u hv0).symm
  have hrel : (a - a ^ p ^ (s + 1)) * v = 1 - a ^ p ^ (s + 1) := by
    rw [huv, mul_pow] at hu
    linear_combination hu - a ^ p ^ (s + 1) * hv
  by_cases hden : a - a ^ p ^ (s + 1) = 0
  · have hQ : a ^ p ^ (s + 1) = 1 := by
      rw [hden, zero_mul] at hrel
      exact (sub_eq_zero.mp hrel.symm).symm
    have ha1 := (sub_eq_zero.mp hden).trans hQ
    rw [huv, ha1, one_mul]
  · have hvEq : v = (1 - a ^ p ^ (s + 1)) / (a - a ^ p ^ (s + 1)) :=
      (eq_div_iff hden).mpr (by rw [mul_comm]; exact hrel)
    have hvD := D.div_mem (D.sub_mem D.one_mem haQ) (D.sub_mem ha haQ)
    rw [← hvEq] at hvD
    exact (hvA hvD).elim

/-- The trace-one parameters are nonzero. -/
theorem kummerTraceParameter_ne_zero (s d r : ℕ) (u : KummerTraceParameters p s d r) :
    u.val ≠ 0 := by
  intro h
  have hu := u.property.1
  rw [h, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), add_zero] at hu
  exact zero_ne_one hu

/-- Distinct scalar/trace parameter pairs give distinct ordinates. -/
theorem kummerTraceFamilyPoint_injective (s d r : ℕ) :
    Function.Injective (fun x : KummerTraceScalars p s d × KummerTraceParameters p s d r =>
      kummerTraceFamilyPoint p s d r x.1 x.2) := by
  rintro ⟨a, ⟨u, hu⟩⟩ ⟨b, ⟨v, hv⟩⟩ he
  have hv0 := kummerTraceParameter_ne_zero p s d r ⟨v, hv⟩
  have hq : 1 ≤ p ^ (d + 1) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hA := kummerExponent_mul_add (p ^ (d + 1) - 1) (r + 1)
  rw [Nat.sub_add_cancel hq] at hA
  have hp := congrArg (fun x : SquareConstantField p s => x ^ (p ^ (d + 1) - 1)) he
  change ((kummerTraceScalar p s d a : SquareConstantField p s) *
      u ^ kummerExponent (p ^ (d + 1)) (r + 1)) ^ (p ^ (d + 1) - 1) =
    ((kummerTraceScalar p s d b : SquareConstantField p s) *
      v ^ kummerExponent (p ^ (d + 1)) (r + 1)) ^ (p ^ (d + 1) - 1) at hp
  rw [mul_pow, mul_pow, kummerTraceScalar_pow, kummerTraceScalar_pow, one_mul, one_mul,
    ← pow_mul, ← pow_mul] at hp
  have hratio : (u / v) ^ p ^ ((d + 1) * (r + 1)) = u / v := by
    rw [pow_mul p, ← hA, pow_succ, div_pow, hp, div_self (pow_ne_zero _ hv0), one_mul]
  have huv : u = v := trace_one_ratio_rigidity p s ((d + 1) * (r + 1)) u v
    hu.1 hv.1 (by simpa only [pow_mul p] using hv.2) hratio
  have hsc : (kummerTraceScalar p s d a : SquareConstantField p s) =
      (kummerTraceScalar p s d b : SquareConstantField p s) := by
    change (kummerTraceScalar p s d a : SquareConstantField p s) * u ^ _ =
      (kummerTraceScalar p s d b : SquareConstantField p s) * v ^ _ at he
    rw [huv] at he
    exact mul_right_cancel₀ (pow_ne_zero _ hv0) he
  have hab : a = b := Subtype.ext (Units.ext (Subtype.ext hsc))
  exact Prod.ext hab (Subtype.ext huv)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
