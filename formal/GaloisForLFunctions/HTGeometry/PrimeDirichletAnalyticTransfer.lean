import GaloisForLFunctions.HTGeometry.DirichletLSeriesDifferentialTransfer
import GaloisForLFunctions.HTGeometry.FiniteAbscissaDirichletUpperEnd
import GaloisForLFunctions.HTGeometry.FinitePrimeCoefficientField
import GaloisForLFunctions.HTGeometry.PrimeExpLogFiberRigidity

/-!
# Analytic realization of signed prime Dirichlet carriers

This file places every Boolean prime orientation in the absolutely convergent Dirichlet algebra and
packages that algebra as a genuine complex subalgebra.  It is the analytic side of the
prime-Dirichlet tail differential matroid.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Filter Set Topology

noncomputable section

open scoped LSeries.notation

/-- The absolutely convergent right-half-plane arithmetic functions as a complex subalgebra. -/
def rightHalfPlaneArithmeticSubalgebra : Subalgebra ℂ (ArithmeticFunction ℂ) where
  carrier := rightHalfPlaneArithmeticSubring
  zero_mem' := rightHalfPlaneArithmeticSubring.zero_mem
  one_mem' := rightHalfPlaneArithmeticSubring.one_mem
  add_mem' := rightHalfPlaneArithmeticSubring.add_mem
  mul_mem' := rightHalfPlaneArithmeticSubring.mul_mem
  algebraMap_mem' := by
    intro c
    change ∀ y : ℝ, 1 < y → LSeriesSummable
      (fun n => (algebraMap ℂ (ArithmeticFunction ℂ) c) n) (y : ℂ)
    intro y hy
    have hone : LSeriesSummable
        (fun n => (1 : ArithmeticFunction ℂ) n) (y : ℂ) :=
      rightHalfPlaneArithmeticSubring.one_mem y hy
    simpa [Algebra.algebraMap_eq_smul_one] using hone.smul c

/-- Forgetting the complex-subalgebra packaging recovers the original convergence subring. -/
def rightHalfPlaneArithmeticSubalgebraToSubring :
    rightHalfPlaneArithmeticSubalgebra →+* rightHalfPlaneArithmeticSubring where
  toFun f := ⟨f.1, f.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A Boolean orientation as a prime-supported arithmetic function. -/
def signedPrimeArithmeticFunction (ε : Nat.Primes → Bool) : ArithmeticFunction ℂ :=
  arithmeticOfPrimeColumn (fun p => primeDirichletSign (ε p))

/-- Every signed prime carrier is bounded coefficientwise by one. -/
theorem signedPrimeArithmeticFunction_norm_le_one
    (ε : Nat.Primes → Bool) (n : ℕ) :
    ‖signedPrimeArithmeticFunction ε n‖ ≤ 1 := by
  by_cases hn : n.Prime
  · rw [show signedPrimeArithmeticFunction ε n = primeDirichletSign (ε ⟨n, hn⟩) by
      exact arithmeticOfPrimeColumn_apply_prime
        (fun p => primeDirichletSign (ε p)) ⟨n, hn⟩]
    cases ε ⟨n, hn⟩ <;> simp [primeDirichletSign]
  · simp [signedPrimeArithmeticFunction, arithmeticOfPrimeColumn, hn]

/-- The signed prime carrier belongs to the full absolute-convergence half-plane `Re s > 1`. -/
def signedPrimeRightHalfPlane (ε : Nat.Primes → Bool) :
    rightHalfPlaneArithmeticSubalgebra := by
  refine ⟨signedPrimeArithmeticFunction ε, ?_⟩
  change ∀ y : ℝ, 1 < y → LSeriesSummable
    (fun n => signedPrimeArithmeticFunction ε n) (y : ℂ)
  intro y hy
  apply LSeriesSummable_of_bounded_of_one_lt_re
    (m := 1) (fun n hn => signedPrimeArithmeticFunction_norm_le_one ε n)
  simpa using hy

@[simp]
theorem signedPrimeRightHalfPlane_coe (ε : Nat.Primes → Bool) :
    (signedPrimeRightHalfPlane ε).1 = signedPrimeArithmeticFunction ε := rfl

/-- Tail-independent Boolean orientations are algebraically independent already in the convergent
complex arithmetic-function algebra. -/
theorem signedPrimeRightHalfPlane_algebraicIndependent
    {J : Type*} [Fintype J] [DecidableEq J]
    (ε : J → Nat.Primes → Bool) (htail : PrimeOrientationTailIndependent ε) :
    AlgebraicIndependent ℂ (fun j => signedPrimeRightHalfPlane (ε j)) := by
  let incl : rightHalfPlaneArithmeticSubalgebra →ₐ[ℂ] ArithmeticFunction ℂ :=
    rightHalfPlaneArithmeticSubalgebra.val
  have hincl : Function.Injective incl := by
    intro x y hxy
    exact Subtype.ext hxy
  apply (AlgHom.algebraicIndependent_iff incl hincl).mp
  change AlgebraicIndependent ℂ
    (fun j => arithmeticOfPrimeColumn (fun p => primeDirichletSign (ε j p)))
  exact algebraicIndependent_arithmeticColumns_of_tailIndependent
    (fun j p => primeDirichletSign (ε j p)) htail

/-- The faithful rotated L-series map, now packaged as a complex algebra homomorphism into the
ambient upper-end germ algebra. -/
noncomputable def rightHalfPlaneLSeriesToUpperEndGerm :
    rightHalfPlaneArithmeticSubalgebra →ₐ[ℂ] Germ upperEndFilter ℂ where
  __ := (SubringClass.subtype upperEndAnalyticSubring).comp
    (rightHalfPlaneLSeriesToUpperEndAnalytic.comp
      rightHalfPlaneArithmeticSubalgebraToSubring)
  commutes' := by
    intro c
    change Germ.coeRingHom upperEndFilter
        (fun z : ℂ => LSeries
          (fun n => (algebraMap ℂ (ArithmeticFunction ℂ) c) n) (-Complex.I * z)) =
      algebraMap ℂ (Germ upperEndFilter ℂ) c
    have hcoeff : (fun n => (algebraMap ℂ (ArithmeticFunction ℂ) c) n) =
        c • LSeries.delta := by
      funext n
      simp [Algebra.algebraMap_eq_smul_one, ArithmeticFunction.smul_map,
        ArithmeticFunction.one_apply, LSeries.delta]
    rw [hcoeff]
    change (↑(fun z : ℂ => LSeries (c • LSeries.delta) (-Complex.I * z)) :
      Germ upperEndFilter ℂ) = algebraMap ℂ (Germ upperEndFilter ℂ) c
    have hfun : (fun z : ℂ => LSeries (c • LSeries.delta) (-Complex.I * z)) =
        fun _ => c := by
      funext z
      rw [LSeries_smul, LSeries_delta]
      simp
    rw [hfun]
    rfl

/-- The analytic-germ realization is injective by Dirichlet coefficient uniqueness. -/
theorem rightHalfPlaneLSeriesToUpperEndGerm_injective :
    Function.Injective rightHalfPlaneLSeriesToUpperEndGerm := by
  intro f g hfg
  apply Subtype.ext
  have hold : rightHalfPlaneLSeriesToUpperEndAnalytic
      (rightHalfPlaneArithmeticSubalgebraToSubring f) =
      rightHalfPlaneLSeriesToUpperEndAnalytic
        (rightHalfPlaneArithmeticSubalgebraToSubring g) := by
    apply Subtype.ext
    exact hfg
  exact congrArg Subtype.val
    (rightHalfPlaneLSeriesToUpperEndAnalytic_injective hold)

/-- Tail-independent signed prime Dirichlet series are algebraically independent as analytic
upper-end germs. -/
theorem signedPrimeUpperEndGerm_algebraicIndependent
    {J : Type*} [Fintype J] [DecidableEq J]
    (ε : J → Nat.Primes → Bool) (htail : PrimeOrientationTailIndependent ε) :
    AlgebraicIndependent ℂ
      (fun j => rightHalfPlaneLSeriesToUpperEndGerm (signedPrimeRightHalfPlane (ε j))) :=
  (signedPrimeRightHalfPlane_algebraicIndependent ε htail).map'
    rightHalfPlaneLSeriesToUpperEndGerm_injective

/-- The coefficient clock produced by differentiating after the rotation `s = -I z`. -/
def rotatedPrimeLogClock (p : Nat.Primes) : ℂ := Complex.I * primeLogClock p

/-- The rotated prime logarithmic clock is injective. -/
theorem rotatedPrimeLogClock_injective : Function.Injective rotatedPrimeLogClock := by
  intro p q hpq
  have hclock : primeLogClock p = primeLogClock q := by
    exact mul_left_cancel₀ Complex.I_ne_zero hpq
  have hlog : Real.log (p : ℕ) = Real.log (q : ℕ) := by
    exact Complex.ofReal_injective hclock
  have hcast : ((p : ℕ) : ℝ) = ((q : ℕ) : ℝ) :=
    Real.strictMonoOn_log.injOn
      (by change 0 < ((p : ℕ) : ℝ); exact_mod_cast p.2.pos)
      (by change 0 < ((q : ℕ) : ℝ); exact_mod_cast q.2.pos) hlog
  apply Subtype.ext
  exact_mod_cast hcast

/-- The order-`k` rotated derivative of a signed prime arithmetic carrier. -/
def signedPrimeRotatedJet (ε : Nat.Primes → Bool) (k : ℕ) :
    rightHalfPlaneArithmeticSubalgebra := by
  let f0 := rightHalfPlaneArithmeticSubalgebraToSubring (signedPrimeRightHalfPlane ε)
  let fk := (rightHalfPlaneRotatedDeriv^[k]) f0
  exact ⟨fk.1, fk.2⟩

/-- Coefficient formula for the iterated rotated derivation on any convergent arithmetic
function. -/
theorem rightHalfPlaneRotatedDeriv_iterate_apply
    (f : rightHalfPlaneArithmeticSubring) (k n : ℕ) :
    ((rightHalfPlaneRotatedDeriv^[k]) f).1 n =
      (Complex.I * (Real.log n : ℂ)) ^ k * f.1 n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', rightHalfPlaneRotatedDeriv_apply, ih, pow_succ]
      ring

/-- Exact coefficient formula for every rotated derivative jet. -/
theorem signedPrimeRotatedJet_apply
    (ε : Nat.Primes → Bool) (k n : ℕ) :
    (signedPrimeRotatedJet ε k).1 n =
      (Complex.I * (Real.log n : ℂ)) ^ k * signedPrimeArithmeticFunction ε n := by
  change ((rightHalfPlaneRotatedDeriv^[k])
      (rightHalfPlaneArithmeticSubalgebraToSubring (signedPrimeRightHalfPlane ε))).1 n = _
  rw [rightHalfPlaneRotatedDeriv_iterate_apply]
  rfl

/-- The rotated jet is the prime-supported arithmetic column with the expected logarithmic
coefficient. -/
theorem signedPrimeRotatedJet_eq_arithmeticOfPrimeColumn
    (ε : Nat.Primes → Bool) (k : ℕ) :
    (signedPrimeRotatedJet ε k).1 =
      arithmeticOfPrimeColumn
        (fun p => primeDirichletSign (ε p) * rotatedPrimeLogClock p ^ k) := by
  ext n
  by_cases hn : n.Prime
  · rw [signedPrimeRotatedJet_apply,
      show signedPrimeArithmeticFunction ε n = primeDirichletSign (ε ⟨n, hn⟩) by
        exact arithmeticOfPrimeColumn_apply_prime
          (fun p => primeDirichletSign (ε p)) ⟨n, hn⟩,
      show arithmeticOfPrimeColumn
          (fun p => primeDirichletSign (ε p) * rotatedPrimeLogClock p ^ k) n =
          primeDirichletSign (ε ⟨n, hn⟩) * rotatedPrimeLogClock ⟨n, hn⟩ ^ k by
        exact arithmeticOfPrimeColumn_apply_prime
          (fun p => primeDirichletSign (ε p) * rotatedPrimeLogClock p ^ k) ⟨n, hn⟩]
    simp only [rotatedPrimeLogClock, primeLogClock]
    ring
  · rw [signedPrimeRotatedJet_apply]
    simp [signedPrimeArithmeticFunction, arithmeticOfPrimeColumn, hn]

/-- Every finite derivative rectangle of a tail-independent orientation family is algebraically
independent in the convergent arithmetic-function algebra. -/
theorem signedPrimeRotatedJets_algebraicIndependent
    {J : Type*} [Fintype J] [DecidableEq J]
    (ε : J → Nat.Primes → Bool) (htail : PrimeOrientationTailIndependent ε)
    (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun jk : J × Fin (m + 1) => signedPrimeRotatedJet (ε jk.1) jk.2) := by
  let coeff : (J × Fin (m + 1)) → Nat.Primes → ℂ :=
    primeOrientationJetCoefficient ε rotatedPrimeLogClock m
  have hcoeff : TailCoefficientIndependent coeff :=
    primeOrientationJetCoefficient_tailIndependent_of_orientation ε rotatedPrimeLogClock
      rotatedPrimeLogClock_injective htail m
  have hraw := algebraicIndependent_arithmeticColumns_of_tailIndependent coeff hcoeff
  let incl : rightHalfPlaneArithmeticSubalgebra →ₐ[ℂ] ArithmeticFunction ℂ :=
    rightHalfPlaneArithmeticSubalgebra.val
  have hincl : Function.Injective incl := by
    intro x y hxy
    exact Subtype.ext hxy
  apply (AlgHom.algebraicIndependent_iff incl hincl).mp
  convert hraw using 1
  funext jk
  exact signedPrimeRotatedJet_eq_arithmeticOfPrimeColumn (ε jk.1) jk.2

/-- The same finite derivative rectangle is algebraically independent over the full intrinsic
finite-prime coefficient field in the ambient arithmetic fraction field. -/
theorem signedPrimeRotatedJets_algebraicIndependent_over_finitePrimeCoefficientField
    {J : Type*} [Fintype J] [DecidableEq J]
    (ε : J → Nat.Primes → Bool) (htail : PrimeOrientationTailIndependent ε)
    (m : ℕ) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun jk : J × Fin (m + 1) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (signedPrimeRotatedJet (ε jk.1) jk.2).1) := by
  let coeff : (J × Fin (m + 1)) → Nat.Primes → ℂ :=
    primeOrientationJetCoefficient ε rotatedPrimeLogClock m
  have hcoeff : TailCoefficientIndependent coeff :=
    primeOrientationJetCoefficient_tailIndependent_of_orientation ε rotatedPrimeLogClock
      rotatedPrimeLogClock_injective htail m
  have hraw :=
    algebraicIndependent_fractionPrimeColumns_over_finitePrimeCoefficientField coeff hcoeff
  convert hraw using 1
  funext jk
  congr 1
  exact signedPrimeRotatedJet_eq_arithmeticOfPrimeColumn (ε jk.1) jk.2

/-- Consequently every finite derivative rectangle is algebraically independent as a family of
actual analytic upper-end germs. -/
theorem signedPrimeUpperEndGerm_jets_algebraicIndependent
    {J : Type*} [Fintype J] [DecidableEq J]
    (ε : J → Nat.Primes → Bool) (htail : PrimeOrientationTailIndependent ε)
    (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun jk : J × Fin (m + 1) =>
        rightHalfPlaneLSeriesToUpperEndGerm
          (signedPrimeRotatedJet (ε jk.1) jk.2)) :=
  (signedPrimeRotatedJets_algebraicIndependent ε htail m).map'
    rightHalfPlaneLSeriesToUpperEndGerm_injective

/-- The rotated coefficient derivation on the complex convergence subalgebra. -/
def rightHalfPlaneRotatedDerivSubalgebra
    (f : rightHalfPlaneArithmeticSubalgebra) :
    rightHalfPlaneArithmeticSubalgebra := by
  let Df := rightHalfPlaneRotatedDeriv
    (rightHalfPlaneArithmeticSubalgebraToSubring f)
  exact ⟨Df.1, Df.2⟩

/-- The faithful analytic realization intertwines the coefficient derivation and germ
differentiation. -/
theorem upperEndGermDeriv_rightHalfPlaneLSeries
    (f : rightHalfPlaneArithmeticSubalgebra) :
    upperEndGermDeriv (rightHalfPlaneLSeriesToUpperEndGerm f) =
      rightHalfPlaneLSeriesToUpperEndGerm
        (rightHalfPlaneRotatedDerivSubalgebra f) := by
  exact congrArg Subtype.val
    (upperEndAnalyticDeriv_rightHalfPlaneLSeries
      (rightHalfPlaneArithmeticSubalgebraToSubring f))

/-- Successive signed arithmetic jets are generated by the rotated coefficient derivation. -/
theorem signedPrimeRotatedJet_succ
    (ε : Nat.Primes → Bool) (k : ℕ) :
    signedPrimeRotatedJet ε (k + 1) =
      rightHalfPlaneRotatedDerivSubalgebra (signedPrimeRotatedJet ε k) := by
  apply Subtype.ext
  change ((rightHalfPlaneRotatedDeriv^[k + 1])
      (rightHalfPlaneArithmeticSubalgebraToSubring (signedPrimeRightHalfPlane ε))).1 =
    (rightHalfPlaneRotatedDeriv
      ((rightHalfPlaneRotatedDeriv^[k])
        (rightHalfPlaneArithmeticSubalgebraToSubring
          (signedPrimeRightHalfPlane ε)))).1
  rw [Function.iterate_succ_apply']

/-- Each realized rotated jet is exactly the corresponding iterated analytic derivative. -/
theorem signedPrimeUpperEndGerm_iteratedDeriv
    (ε : Nat.Primes → Bool) (k : ℕ) :
    rightHalfPlaneLSeriesToUpperEndGerm (signedPrimeRotatedJet ε k) =
      (upperEndGermDeriv^[k])
        (rightHalfPlaneLSeriesToUpperEndGerm (signedPrimeRightHalfPlane ε)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show k + 1 = Nat.succ k from rfl, signedPrimeRotatedJet_succ,
        ← upperEndGermDeriv_rightHalfPlaneLSeries, Function.iterate_succ_apply', ← ih]

end

end GaloisForLFunctions.HTGeometry
