import GaloisForLFunctions.HTGeometry.LinearAlgebra.NilpotentDilation
import GaloisForLFunctions.HTGeometry.Holonomy.FiniteAlgebraTransport

/-!
# Nilpotent generators realize arbitrary positive scalar holonomy

An Euler operator integrates to a multiplicative action of positive real
scales by inner algebra automorphisms. If its generator is nonzero, this action
is faithful. Edge transport therefore realizes every positive reversible clock
calibration and retains its exact obstruction to flatness.

Every finite nilpotent real matrix admits an Euler operator. This gives the
sharp complementary case to scalar flatness for nonnilpotent finite-algebra
generators. The graph may be infinite.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open NormedSpace

section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The inner dilation obtained by exponentiating the real logarithm times an Euler operator. -/
def clockEulerDilation (H : A) (q : ℝ) : A ≃ₐ[ℝ] A :=
  clockInnerAlgEquiv (clockExpUnit (K := ℝ) (Real.log q • H))

/-- The zero exponential is the identity unit. -/
theorem clockExpUnit_zero : clockExpUnit (K := ℝ) (0 : A) = 1 := by
  apply Units.ext
  exact exp_zero

/-- Negating the exponent inverts the exponential unit. -/
theorem clockExpUnit_neg (H : A) :
    clockExpUnit (K := ℝ) (-H) = (clockExpUnit (K := ℝ) H)⁻¹ := by
  apply Units.ext
  rfl

/-- Exponentials of scalar multiples of one operator form a one-parameter subgroup. -/
theorem clockExpUnit_add_smul (H : A) (s t : ℝ) :
    clockExpUnit (K := ℝ) ((s + t) • H) =
      clockExpUnit (K := ℝ) (s • H) * clockExpUnit (K := ℝ) (t • H) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply Units.ext
  change exp ((s + t) • H) = exp (s • H) * exp (t • H)
  rw [add_smul, exp_add_of_commute (((Commute.refl H).smul_left s).smul_right t)]

omit [CompleteSpace A] in
/-- Conjugation by the identity unit is the identity automorphism. -/
theorem clockInnerAlgEquiv_one : clockInnerAlgEquiv (K := ℝ) (1 : Aˣ) = 1 := by
  ext x
  change 1 * x * 1 = x
  rw [one_mul, mul_one]

omit [CompleteSpace A] in
/-- Inner conjugation respects multiplication of units. -/
theorem clockInnerAlgEquiv_mul (u v : Aˣ) :
    clockInnerAlgEquiv (K := ℝ) (u * v) = clockInnerAlgEquiv u * clockInnerAlgEquiv v := by
  ext x
  change (u.val * v.val) * x * (v.inv * u.inv) = u.val * (v.val * x * v.inv) * u.inv
  simp only [mul_assoc]

omit [CompleteSpace A] in
/-- Inverting a unit inverts its conjugation action. -/
theorem clockInnerAlgEquiv_inv (u : Aˣ) :
    clockInnerAlgEquiv (K := ℝ) u⁻¹ = (clockInnerAlgEquiv (K := ℝ) u)⁻¹ := rfl

/-- Unit scale acts trivially. -/
theorem clockEulerDilation_one (H : A) : clockEulerDilation H 1 = 1 := by
  rw [clockEulerDilation, Real.log_one, zero_smul, clockExpUnit_zero, clockInnerAlgEquiv_one]

/-- Logarithmic dilation respects multiplication of nonzero real scales. -/
theorem clockEulerDilation_mul (H : A) {q r : ℝ} (hq : q ≠ 0) (hr : r ≠ 0) :
    clockEulerDilation H (q * r) = clockEulerDilation H q * clockEulerDilation H r := by
  rw [clockEulerDilation, Real.log_mul hq hr, clockExpUnit_add_smul, clockInnerAlgEquiv_mul]
  rfl

/-- Reciprocal scales give inverse automorphisms. -/
theorem clockEulerDilation_inv (H : A) (q : ℝ) :
    clockEulerDilation H q⁻¹ = (clockEulerDilation H q)⁻¹ := by
  rw [clockEulerDilation, Real.log_inv, neg_smul, clockExpUnit_neg, clockInnerAlgEquiv_inv]
  rfl

/-- Positive dilation rescales the Euler generator by exactly its parameter. -/
theorem clockEulerDilation_scale (H N : A) (hHN : H * N - N * H = N)
    {q : ℝ} (hq : 0 < q) : clockEulerDilation H q N = q • N := by
  rw [clockEulerDilation, clockEuler_exponential H N hHN,
    ← Real.exp_eq_exp_ℝ, Real.exp_log hq]

/-- A nonzero Euler generator makes the action of positive scales faithful. -/
theorem clockEulerDilation_eq_iff (H N : A) (hHN : H * N - N * H = N)
    (hN : N ≠ 0) {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    clockEulerDilation H q = clockEulerDilation H r ↔ q = r := by
  constructor
  · intro h
    have he := congrArg (fun e : A ≃ₐ[ℝ] A => e N) h
    rw [clockEulerDilation_scale H N hHN hq, clockEulerDilation_scale H N hHN hr] at he
    have hz : (q - r) • N = 0 := by rw [sub_smul, he, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hN)
  · rintro rfl
    rfl

/-- Positive dilation has trivial kernel for a nonzero Euler generator. -/
theorem clockEulerDilation_eq_one_iff (H N : A) (hHN : H * N - N * H = N)
    (hN : N ≠ 0) {q : ℝ} (hq : 0 < q) : clockEulerDilation H q = 1 ↔ q = 1 := by
  simpa only [clockEulerDilation_one] using
    clockEulerDilation_eq_iff H N hHN hN hq zero_lt_one

end Algebra

section AlgebraGraph
variable {A V : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {G : SimpleGraph V}

/-- Full operator transport along a walk is dilation by its scalar reading. -/
theorem clockWalkTransport_eulerDilation (H : A)
    (c : V → V → ℝˣ) {u v : V} (p : G.Walk u v) :
    clockWalkTransport (fun u v => clockEulerDilation H (c u v : ℝ)) p =
      clockEulerDilation H (clockWalkTransport c p : ℝˣ) := by
  induction p with
  | nil => exact (clockEulerDilation_one H).symm
  | @cons u w v h p ih =>
    change clockEulerDilation H (c u w : ℝ) *
      clockWalkTransport (fun u v => clockEulerDilation H (c u v : ℝ)) p =
      clockEulerDilation H ((c u w : ℝ) * (clockWalkTransport c p : ℝˣ))
    rw [ih, clockEulerDilation_mul H (c u w).ne_zero (clockWalkTransport c p).ne_zero]

/-- An Euler generator realizes every positive reversible calibration, preserving flatness when nonzero. -/
theorem exists_euler_clock_transport (H N : A) (hH : H * N - N * H = N)
    (c : V → V → ℝˣ) (hc : ∀ {u v}, G.Adj u v → 0 < (c u v : ℝ))
    (hrev : ClockCalibrationReversible G c) :
    ∃ t : V → V → (A ≃ₐ[ℝ] A),
      ClockCalibrationReversible G t ∧
      (∀ {u v}, G.Adj u v → t u v N = (c u v : ℝ) • N) ∧
      (N ≠ 0 → (ClockCalibrationFlat G t ↔ ClockCalibrationFlat G c)) := by
  let t : V → V → (A ≃ₐ[ℝ] A) :=
    fun u v => clockEulerDilation H (c u v : ℝ)
  have ht : ∀ {u v}, G.Adj u v → t u v N = (c u v : ℝ) • N :=
    fun h => clockEulerDilation_scale H N hH (hc h)
  refine ⟨t, ?_, ht, ?_⟩
  · intro u v h
    change clockEulerDilation H (c v u : ℝ) = (clockEulerDilation H (c u v : ℝ))⁻¹
    rw [hrev h]
    simpa only [Units.val_inv_eq_inv_val] using clockEulerDilation_inv H (c u v : ℝ)
  · intro hn
    constructor
    · intro hf u p
      have hs := clockWalkTransport_algebra (fun _ => N) c t ht p
      rw [hf u p] at hs
      change N = ((clockWalkTransport c p : ℝˣ) : ℝ) • N at hs
      have hz : (((clockWalkTransport c p : ℝˣ) : ℝ) - 1) • N = 0 := by
        rw [sub_smul, one_smul, ← hs, sub_self]
      apply Units.ext
      exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hn)
    · intro hf u p
      change clockWalkTransport (fun u v => clockEulerDilation H (c u v : ℝ)) p = 1
      rw [clockWalkTransport_eulerDilation, hf u p]
      exact clockEulerDilation_one H

end AlgebraGraph

open scoped Matrix.Norms.Frobenius

/-- Every finite nilpotent real matrix realizes arbitrary positive reversible edge scales. -/
theorem exists_nilpotent_clock_transport {ι V : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph V} (N : Matrix ι ι ℝ) (hN : IsNilpotent N)
    (c : V → V → ℝˣ) (hc : ∀ {u v}, G.Adj u v → 0 < (c u v : ℝ))
    (hrev : ClockCalibrationReversible G c) :
    ∃ t : V → V → (Matrix ι ι ℝ ≃ₐ[ℝ] Matrix ι ι ℝ),
      ClockCalibrationReversible G t ∧
      (∀ {u v}, G.Adj u v → t u v N = (c u v : ℝ) • N) ∧
      (N ≠ 0 → (ClockCalibrationFlat G t ↔ ClockCalibrationFlat G c)) := by
  obtain ⟨H, hH⟩ := exists_matrixEuler_of_isNilpotent N hN
  exact exists_euler_clock_transport H N hH c hc hrev

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.clockEulerDilation_eq_iff
#print axioms GaloisForLFunctions.HTGeometry.clockWalkTransport_eulerDilation
#print axioms GaloisForLFunctions.HTGeometry.exists_euler_clock_transport
#print axioms GaloisForLFunctions.HTGeometry.exists_nilpotent_clock_transport
