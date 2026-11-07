import GaloisForLFunctions.ArithmeticKreinLangerTheory.StepanovsOrderOverTheFiniteField
import Mathlib.Algebra.LinearRecurrence

/-!
# The cut system over a curve

Over a curve with zeta function `Z(u) = P(u) / ((1 − u)(1 − q u))`, a stencil is a polynomial `E`, its multiplicity
is `E Z`, and a stencil with no pole contribution is `E = (1 − u)(1 − q u) E₀`, so its multiplicity is `E₀ P`. A tail
`T : ℕ → ℂ` reads a polynomial `f` by `⟨T, f⟩ = Σ_r f_r T(r)`, and **`T` is a kernel vector when it annihilates
every `E₀ P`**.

The structure is rigid and finite. `T` is a kernel vector iff it satisfies the linear recurrence with
characteristic polynomial `P`, so **the kernel has dimension exactly `deg P`**, and the power tail `T(r) = u^r` is a
kernel vector iff `P(u) = 0`. So:

* Over `𝔽_q[T]`, `P = 1`, and the kernel is zero: quantized norms leave no room for a fake.
* Over a curve, the zeros are the kernel vectors, there are `2g`, and every kernel vector obeys one recurrence.
* Over `ℤ`, the zeros of `ζ` are the power-law kernel vectors, and no recurrence holds.

This is the exact form of "recurrence is the shadow of Frobenius".

**Hasse–Weil in the language of cuts.** For the split hyperelliptic curves `y² = f(x)`, Stepanov's count gives
`‖ω‖ = √q` for every reciprocal root, so each kernel mode has exact decay `q^{-r/2}`.
-/

open Polynomial Finset
open GaloisForLFunctions.RHTower.Hyperelliptic

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The reading of a polynomial by a tail: `⟨T, f⟩ = Σ_r f_r T(r)`. -/
def tailPairing (T : ℕ → ℂ) : ℂ[X] →ₗ[ℂ] ℂ := Polynomial.lsum fun r => LinearMap.mulRight ℂ (T r)

theorem tailPairing_monomial (T : ℕ → ℂ) (n : ℕ) (a : ℂ) :
    tailPairing T (monomial n a) = a * T n := by
  simp [tailPairing, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

theorem tailPairing_C_mul_X_pow (T : ℕ → ℂ) (n : ℕ) (a : ℂ) :
    tailPairing T (C a * X ^ n) = a * T n := by
  rw [C_mul_X_pow_eq_monomial, tailPairing_monomial]

/-- `T` is a kernel vector of the cut system of `P`: it annihilates the ideal of `P`. -/
def IsCurveKernel (P : ℂ[X]) (T : ℕ → ℂ) : Prop := ∀ E : ℂ[X], tailPairing T (E * P) = 0

/-- The pairing with a monomial multiple of `P` is the recurrence at `n`. -/
theorem tailPairing_X_pow_mul (P : ℂ[X]) (T : ℕ → ℂ) (n : ℕ) :
    tailPairing T (X ^ n * P) = ∑ i ∈ range (P.natDegree + 1), P.coeff i * T (n + i) := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow]
  rw [mul_sum, map_sum]
  refine sum_congr rfl fun i _ => ?_
  have : X ^ n * (C (P.coeff i) * X ^ i) = C (P.coeff i) * X ^ (n + i) := by
    rw [pow_add]
    ring
  rw [this, tailPairing_C_mul_X_pow]

/-- **The kernel is the recurrence.** -/
theorem isCurveKernel_iff (P : ℂ[X]) (T : ℕ → ℂ) :
    IsCurveKernel P T ↔ ∀ n, ∑ i ∈ range (P.natDegree + 1), P.coeff i * T (n + i) = 0 := by
  constructor
  · intro h n
    rw [← tailPairing_X_pow_mul]
    exact h _
  · intro h E
    induction E using Polynomial.induction_on' with
    | add p q hp hq => rw [add_mul, map_add, hp, hq, add_zero]
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, mul_assoc, ← smul_eq_C_mul, map_smul, tailPairing_X_pow_mul, h n,
        smul_zero]

/-- **The power tail reads a polynomial by evaluation.** -/
theorem tailPairing_pow (u : ℂ) (f : ℂ[X]) : tailPairing (fun r => u ^ r) f = f.eval u := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, eval_add]
  | monomial n a => rw [tailPairing_monomial, eval_monomial]

/-- **Zeros are the power-law kernel.** -/
theorem isCurveKernel_pow_iff (P : ℂ[X]) (u : ℂ) :
    IsCurveKernel P (fun r => u ^ r) ↔ P.eval u = 0 := by
  constructor
  · intro h
    have := h 1
    rwa [one_mul, tailPairing_pow] at this
  · intro h E
    rw [tailPairing_pow, eval_mul, h, mul_zero]

/-- **Quantized norms leave no room.** The cut system of `𝔽_q[T]`, with `P = 1`, has zero kernel. -/
theorem eq_zero_of_isCurveKernel_one {T : ℕ → ℂ} (h : IsCurveKernel 1 T) (n : ℕ) : T n = 0 := by
  have := (isCurveKernel_iff 1 T).mp h n
  simpa using this

/-- The linear recurrence of a polynomial of positive degree. -/
def curveRecurrence (P : ℂ[X]) : LinearRecurrence ℂ where
  order := P.natDegree
  coeffs := fun i => -(P.coeff i / P.leadingCoeff)

/-- The kernel is the solution space of the recurrence. -/
theorem isCurveKernel_iff_isSolution {P : ℂ[X]} (hP : P ≠ 0) (T : ℕ → ℂ) :
    IsCurveKernel P T ↔ (curveRecurrence P).IsSolution T := by
  rw [isCurveKernel_iff]
  have hl : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hsplit : ∀ n, ∑ i ∈ range (P.natDegree + 1), P.coeff i * T (n + i) =
      ∑ i ∈ range P.natDegree, P.coeff i * T (n + i) + P.leadingCoeff * T (n + P.natDegree) := by
    intro n
    rw [Finset.sum_range_succ, coeff_natDegree]
  have hrhs : ∀ n, ∑ i : Fin P.natDegree, -(P.coeff i / P.leadingCoeff) * T (n + i) =
      -(∑ i ∈ range P.natDegree, P.coeff i * T (n + i)) / P.leadingCoeff := by
    intro n
    rw [Fin.sum_univ_eq_sum_range (fun i => -(P.coeff i / P.leadingCoeff) * T (n + i)) P.natDegree,
      neg_div, sum_div, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  constructor
  · intro h n
    change T (n + P.natDegree) = ∑ i : Fin P.natDegree, -(P.coeff i / P.leadingCoeff) * T (n + i)
    rw [hrhs, eq_div_iff hl]
    have := h n
    rw [hsplit] at this
    linear_combination this
  · intro h n
    have h1 : T (n + P.natDegree) =
        ∑ i : Fin P.natDegree, -(P.coeff i / P.leadingCoeff) * T (n + i) := h n
    rw [hrhs, eq_div_iff hl] at h1
    rw [hsplit]
    linear_combination h1

/-- The kernel of `P` as a subspace. -/
def curveKernel (P : ℂ[X]) : Submodule ℂ (ℕ → ℂ) where
  carrier := {T | IsCurveKernel P T}
  add_mem' := fun {a b} ha hb E => by
    have hadd : tailPairing (a + b) (E * P) = tailPairing a (E * P) + tailPairing b (E * P) := by
      generalize E * P = f
      induction f using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add, hp, hq]; ring
      | monomial n c => simp only [tailPairing_monomial, Pi.add_apply]; ring
    rw [hadd, ha E, hb E, add_zero]
  zero_mem' := fun E => by
    generalize E * P = f
    induction f using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, hp, hq, add_zero]
    | monomial n c => simp [tailPairing_monomial]
  smul_mem' := fun c {a} ha E => by
    have hsmul : tailPairing (c • a) (E * P) = c * tailPairing a (E * P) := by
      generalize E * P = f
      induction f using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add, hp, hq]; ring
      | monomial n d => simp only [tailPairing_monomial, Pi.smul_apply, smul_eq_mul]; ring
    rw [hsmul, ha E, mul_zero]

/-- **The kernel has dimension `deg P`.** -/
theorem rank_curveKernel {P : ℂ[X]} (hP : P ≠ 0) :
    Module.rank ℂ (curveKernel P) = P.natDegree := by
  have heq : curveKernel P = (curveRecurrence P).solSpace := by
    ext T
    exact isCurveKernel_iff_isSolution hP T
  rw [heq, LinearRecurrence.solSpace_rank]
  rfl

/-! ### Hasse–Weil in the language of cuts -/

variable {F : Type*} [Field F] [Fintype F]

/-- **Hasse–Weil in the language of cuts.** For a split hyperelliptic curve, each reciprocal root `ω` gives the kernel
vector `T(r) = ω^{-r}` of the reversed `L`-polynomial, and Stepanov's count makes its decay exactly `q^{-r/2}`. -/
theorem isCurveKernel_lRoots_of_stepanov (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hsplit : f.Splits) (hodd : Odd f.natDegree) {ω : ℂ} (hω : ω ∈ lRoots f) :
    IsCurveKernel (lPoly f).reverse (fun r => (ω⁻¹) ^ r) ∧
      ∀ r : ℕ, ‖(ω⁻¹) ^ r‖ = (Real.sqrt (Fintype.card F))⁻¹ ^ r := by
  have hnorm := (riemannHypothesis_splitHyperelliptic.{_, 0} hF hsq hsplit hodd).2.1 ω hω
  have hq : 0 < Real.sqrt (Fintype.card F) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hω0 : ω ≠ 0 := fun h => by
    rw [h, norm_zero] at hnorm
    exact hq.ne hnorm
  constructor
  · rw [isCurveKernel_pow_iff]
    have hroot : (lPoly f).IsRoot ω := by
      have := (Polynomial.mem_roots'.mp hω).2
      exact this
    letI : Invertible ω := invertibleOfNonzero hω0
    have h := (Polynomial.eval₂_reverse_eq_zero_iff (RingHom.id ℂ) ω (lPoly f)).mpr (by
      simpa [Polynomial.eval₂_id] using hroot)
    simpa [Polynomial.eval₂_id, invOf_eq_inv] using h
  · intro r
    rw [norm_pow, norm_inv, hnorm]

end GaloisForLFunctions.RigidArithmeticOfCuts
