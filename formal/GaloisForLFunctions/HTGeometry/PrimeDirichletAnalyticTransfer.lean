import GaloisForLFunctions.HTGeometry.DirichletLSeriesDifferentialTransfer
import GaloisForLFunctions.HTGeometry.FiniteAbscissaDirichletUpperEnd
import GaloisForLFunctions.HTGeometry.FinitePrimeCoefficientField
import GaloisForLFunctions.HTGeometry.FinitePrimeRationalCoefficientField
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
    rightHalfPlaneLSeriesToUpperEndAnalytic
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
  have hold : rightHalfPlaneLSeriesToUpperEndAnalytic f =
      rightHalfPlaneLSeriesToUpperEndAnalytic g := by
    apply Subtype.ext
    exact hfg
  exact rightHalfPlaneLSeriesToUpperEndAnalytic_injective hold

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
    rightHalfPlaneArithmeticSubalgebra :=
  (rightHalfPlaneRotatedDeriv^[k]) (signedPrimeRightHalfPlane ε)

/-- Coefficient formula for the iterated rotated derivation on any convergent arithmetic
function. -/
theorem rightHalfPlaneRotatedDeriv_iterate_apply
    (f : rightHalfPlaneArithmeticSubalgebra) (k n : ℕ) :
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
  change ((rightHalfPlaneRotatedDeriv^[k]) (signedPrimeRightHalfPlane ε)).1 n = _
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

/-- The faithful analytic realization intertwines the coefficient derivation and germ
differentiation. -/
theorem upperEndGermDeriv_rightHalfPlaneLSeries
    (f : rightHalfPlaneArithmeticSubalgebra) :
    upperEndGermDeriv (rightHalfPlaneLSeriesToUpperEndGerm f) =
      rightHalfPlaneLSeriesToUpperEndGerm
        (rightHalfPlaneRotatedDeriv f) := by
  exact congrArg Subtype.val
    (upperEndAnalyticDeriv_rightHalfPlaneLSeries f)

/-- Successive signed arithmetic jets are generated by the rotated coefficient derivation. -/
theorem signedPrimeRotatedJet_succ
    (ε : Nat.Primes → Bool) (k : ℕ) :
    signedPrimeRotatedJet ε (k + 1) =
      rightHalfPlaneRotatedDeriv (signedPrimeRotatedJet ε k) := by
  apply Subtype.ext
  change ((rightHalfPlaneRotatedDeriv^[k + 1]) (signedPrimeRightHalfPlane ε)).1 =
    (rightHalfPlaneRotatedDeriv
      ((rightHalfPlaneRotatedDeriv^[k]) (signedPrimeRightHalfPlane ε))).1
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

/-! ## Arbitrary finite shift palettes -/

/-- On a prime, the coefficient shift defined by complex powers is the exponential prime-shift
factor used by the operator-tail rigidity theorem. -/
theorem cpowWeight_prime_eq_primeShiftFactor (a : ℂ) (p : Nat.Primes) :
    cpowWeight a (p : ℕ) = primeShiftFactor a p := by
  rw [cpowWeight, Complex.cpow_def_of_ne_zero]
  · rw [primeShiftFactor, ← Complex.natCast_log]
    congr 1
    simp [primeLogClock]
    ring
  · exact_mod_cast p.2.ne_zero

/-- A signed prime carrier in the translation-stable finite-abscissa algebra. -/
def signedPrimeFiniteAbscissa (ε : Nat.Primes → Bool) :
    finiteAbscissaArithmeticSubalgebra := by
  refine ⟨signedPrimeArithmeticFunction ε, 1, ?_⟩
  exact (signedPrimeRightHalfPlane ε).2

@[simp]
theorem signedPrimeFiniteAbscissa_coe (ε : Nat.Primes → Bool) :
    (signedPrimeFiniteAbscissa ε).1 = signedPrimeArithmeticFunction ε :=
  rfl

/-- The shifted order-`k` analytic derivative carrier, built inside the finite-abscissa algebra. -/
def signedPrimeShiftedRotatedJet
    (ε : Nat.Primes → Bool) (a : ℂ) (k : ℕ) :
    finiteAbscissaArithmeticSubalgebra :=
  finiteAbscissaDirichletShift a
    ((finiteAbscissaRotatedDeriv^[k]) (signedPrimeFiniteAbscissa ε))

/-- Exact natural-number coefficient formula for a shifted rotated jet. -/
theorem signedPrimeShiftedRotatedJet_apply
    (ε : Nat.Primes → Bool) (a : ℂ) (k n : ℕ) :
    (signedPrimeShiftedRotatedJet ε a k).1 n =
      cpowWeight a n * (Complex.I * (Real.log n : ℂ)) ^ k *
        signedPrimeArithmeticFunction ε n := by
  rw [signedPrimeShiftedRotatedJet, finiteAbscissaDirichletShift_apply,
    finiteAbscissaRotatedDeriv_iterate_apply]
  change cpowWeight a n *
      ((Complex.I * (Real.log n : ℂ)) ^ k * signedPrimeArithmeticFunction ε n) = _
  ring

/-- A shifted rotated jet is exactly the prime-supported column used by shift--jet tail
rigidity. -/
theorem signedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn
    (ε : Nat.Primes → Bool) (a : ℂ) (k : ℕ) :
    (signedPrimeShiftedRotatedJet ε a k).1 =
      arithmeticOfPrimeColumn
        (fun p => primeDirichletSign (ε p) * primeShiftFactor a p *
          rotatedPrimeLogClock p ^ k) := by
  ext n
  by_cases hn : n.Prime
  · rw [signedPrimeShiftedRotatedJet_apply,
      show signedPrimeArithmeticFunction ε n = primeDirichletSign (ε ⟨n, hn⟩) by
        exact arithmeticOfPrimeColumn_apply_prime
          (fun p => primeDirichletSign (ε p)) ⟨n, hn⟩,
      show arithmeticOfPrimeColumn
          (fun p => primeDirichletSign (ε p) * primeShiftFactor a p *
            rotatedPrimeLogClock p ^ k) n =
          primeDirichletSign (ε ⟨n, hn⟩) * primeShiftFactor a ⟨n, hn⟩ *
            rotatedPrimeLogClock ⟨n, hn⟩ ^ k by
        exact arithmeticOfPrimeColumn_apply_prime
          (fun p => primeDirichletSign (ε p) * primeShiftFactor a p *
            rotatedPrimeLogClock p ^ k) ⟨n, hn⟩]
    rw [show cpowWeight a n = primeShiftFactor a ⟨n, hn⟩ from
      cpowWeight_prime_eq_primeShiftFactor a ⟨n, hn⟩]
    simp only [rotatedPrimeLogClock, primeLogClock]
    ring
  · rw [signedPrimeShiftedRotatedJet_apply]
    simp [signedPrimeArithmeticFunction, arithmeticOfPrimeColumn, hn]

/-- Tail independence is invariant under multiplying each column by its own nonzero scalar. -/
theorem tailCoefficientIndependent_scale_columns
    {I P : Type*} [Fintype I]
    (c : I → P → ℂ) (u : I → ℂ) (hu : ∀ i, u i ≠ 0)
    (h : TailCoefficientIndependent c) :
    TailCoefficientIndependent (fun i p => u i * c i p) := by
  classical
  intro q hsupp
  let q' : I → ℂ := fun i => q i * u i
  have hq' : q' = 0 := h q' (by
    simpa only [q', mul_assoc] using hsupp)
  funext i
  have hi := congrFun hq' i
  simp only [q', Pi.zero_apply] at hi
  exact (mul_eq_zero.mp hi).resolve_right (hu i)

/-- A finite Boolean orientation family has finite coefficient-pattern range. -/
theorem primeOrientationCoefficientPattern_range_finite
    {J : Type*} [Fintype J] (ε : J → Nat.Primes → Bool) :
    (Set.range (coefficientPattern
      (fun j p => primeDirichletSign (ε j p)))).Finite := by
  classical
  let decode : (J → Bool) → (J → ℂ) :=
    fun b j => primeDirichletSign (b j)
  refine Set.Finite.subset (Set.finite_range decode) ?_
  rintro b ⟨p, rfl⟩
  exact ⟨fun j => ε j p, rfl⟩

/-- Every finite shift--derivative rectangle of a tail-independent Boolean orientation family has
full coefficient-tail rank.  The factor-clock rigidity is the existing prime exponential-
polynomial theorem; only the harmless powers of `I` from the analytic rotation are rescaled. -/
theorem signedPrimeShiftedRotatedJet_tailIndependent
    {J A : Type*} [Fintype J] [Fintype A] [Nonempty A]
    (ε : J → Nat.Primes → Bool) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re))
    (htail : PrimeOrientationTailIndependent ε) (m : ℕ) :
    TailCoefficientIndependent
      (fun jak : J × (A × Fin (m + 1)) => fun p =>
        primeDirichletSign (ε jak.1 p) * primeShiftFactor (alpha jak.2.1) p *
          rotatedPrimeLogClock p ^ (jak.2.2 : ℕ)) := by
  classical
  let c : J → Nat.Primes → ℂ := fun j p => primeDirichletSign (ε j p)
  let raw := coefficientShiftJet c
    (fun a p => primeShiftFactor (alpha a) p) primeLogClock m
  have hraw : TailCoefficientIndependent raw :=
    (primeCompleteShiftJetTailIndependent_iff c alpha hdistinct
      (primeOrientationCoefficientPattern_range_finite ε)).mpr htail m
  let u : J × (A × Fin (m + 1)) → ℂ :=
    fun jak => Complex.I ^ (jak.2.2 : ℕ)
  have hu : ∀ jak, u jak ≠ 0 := fun jak => pow_ne_zero _ Complex.I_ne_zero
  have hscaled := tailCoefficientIndependent_scale_columns raw u hu hraw
  convert hscaled using 1
  funext jak p
  simp only [raw, c, u, coefficientShiftJet, rotatedPrimeLogClock]
  rw [mul_pow]
  ring

/-- Every finite shifted derivative rectangle is algebraically independent in the
translation-stable finite-abscissa arithmetic algebra. -/
theorem signedPrimeShiftedRotatedJets_algebraicIndependent
    {J A : Type*} [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ε : J → Nat.Primes → Bool) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re))
    (htail : PrimeOrientationTailIndependent ε) (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun jak : J × (A × Fin (m + 1)) =>
        signedPrimeShiftedRotatedJet (ε jak.1) (alpha jak.2.1) jak.2.2) := by
  let coeff : J × (A × Fin (m + 1)) → Nat.Primes → ℂ :=
    fun jak p => primeDirichletSign (ε jak.1 p) *
      primeShiftFactor (alpha jak.2.1) p * rotatedPrimeLogClock p ^ (jak.2.2 : ℕ)
  have hcoeff : TailCoefficientIndependent coeff :=
    signedPrimeShiftedRotatedJet_tailIndependent ε alpha hdistinct htail m
  have hraw := algebraicIndependent_arithmeticColumns_of_tailIndependent coeff hcoeff
  let incl : finiteAbscissaArithmeticSubalgebra →ₐ[ℂ] ArithmeticFunction ℂ :=
    finiteAbscissaArithmeticSubalgebra.val
  have hincl : Function.Injective incl := by
    intro x y hxy
    exact Subtype.ext hxy
  apply (AlgHom.algebraicIndependent_iff incl hincl).mp
  convert hraw using 1
  funext jak
  exact signedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn
    (ε jak.1) (alpha jak.2.1) jak.2.2

/-- The shifted derivative rectangle remains algebraically independent over the intrinsic
finite-prime coefficient field in the arithmetic fraction field. -/
theorem signedPrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeCoefficientField
    {J A : Type*} [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ε : J → Nat.Primes → Bool) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re))
    (htail : PrimeOrientationTailIndependent ε) (m : ℕ) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun jak : J × (A × Fin (m + 1)) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (signedPrimeShiftedRotatedJet
            (ε jak.1) (alpha jak.2.1) jak.2.2).1) := by
  let coeff : J × (A × Fin (m + 1)) → Nat.Primes → ℂ :=
    fun jak p => primeDirichletSign (ε jak.1 p) *
      primeShiftFactor (alpha jak.2.1) p * rotatedPrimeLogClock p ^ (jak.2.2 : ℕ)
  have hcoeff : TailCoefficientIndependent coeff :=
    signedPrimeShiftedRotatedJet_tailIndependent ε alpha hdistinct htail m
  have hraw :=
    algebraicIndependent_fractionPrimeColumns_over_finitePrimeCoefficientField coeff hcoeff
  convert hraw using 1
  funext jak
  congr 1
  exact signedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn
    (ε jak.1) (alpha jak.2.1) jak.2.2

/-- After adjoining the independent Dirichlet coordinate, the full shifted derivative rectangle
is algebraically independent over the card's `E_fin(s)` coefficient field. -/
theorem signedPrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeRationalCoefficientField
    {J A : Type*} [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ε : J → Nat.Primes → Bool) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re))
    (htail : PrimeOrientationTailIndependent ε) (m : ℕ) :
    AlgebraicIndependent finitePrimeRationalCoefficientField
      (fun jak : J × (A × Fin (m + 1)) =>
        algebraMap arithmeticFunctionFractionField
          arithmeticFunctionRationalCoordinateField
          (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (signedPrimeShiftedRotatedJet
              (ε jak.1) (alpha jak.2.1) jak.2.2).1)) :=
  algebraicIndependent_constants_over_finitePrimeRationalCoefficientField _
    (signedPrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeCoefficientField
      ε alpha hdistinct htail m)

/-- Consequently every finite shifted derivative rectangle is algebraically independent as a
family of actual analytic upper-end germs. -/
theorem signedPrimeShiftedUpperEndGerm_jets_algebraicIndependent
    {J A : Type*} [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ε : J → Nat.Primes → Bool) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re))
    (htail : PrimeOrientationTailIndependent ε) (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun jak : J × (A × Fin (m + 1)) =>
        finiteAbscissaLSeriesToUpperEndGerm
          (signedPrimeShiftedRotatedJet
            (ε jak.1) (alpha jak.2.1) jak.2.2)) :=
  (signedPrimeShiftedRotatedJets_algebraicIndependent ε alpha hdistinct htail m).map'
    finiteAbscissaLSeriesToUpperEndGerm_injective

/-- Each shifted jet germ is exactly the translate of the corresponding iterated analytic
derivative of the unshifted signed prime carrier. -/
theorem signedPrimeShiftedRotatedJet_upperEndGerm
    (ε : Nat.Primes → Bool) (a : ℂ) (k : ℕ) :
    finiteAbscissaLSeriesToUpperEndGerm (signedPrimeShiftedRotatedJet ε a k) =
      upperEndTranslateGerm (Complex.I * a)
        ((upperEndGermDeriv^[k])
          (finiteAbscissaLSeriesToUpperEndGerm (signedPrimeFiniteAbscissa ε))) := by
  rw [signedPrimeShiftedRotatedJet,
    finiteAbscissaLSeriesToUpperEndGerm_dirichletShift,
    finiteAbscissaLSeriesToUpperEndGerm_iteratedDeriv]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

noncomputable section

/-- Multiplying each column by its own nonzero scalar preserves and reflects tail
independence. -/
theorem tailCoefficientIndependent_scale_columns_iff
    {I P : Type*} [Fintype I]
    (c : I → P → ℂ) (u : I → ℂ) (hu : ∀ i, u i ≠ 0) :
    TailCoefficientIndependent (fun i p => u i * c i p) ↔
      TailCoefficientIndependent c := by
  constructor
  · intro hscaled
    have hinv := tailCoefficientIndependent_scale_columns
      (fun i p => u i * c i p) (fun i => (u i)⁻¹)
      (fun i => inv_ne_zero (hu i)) hscaled
    convert hinv using 1
    funext i p
    simp [hu i]
  · exact tailCoefficientIndependent_scale_columns c u hu

/-- The full finite shift--derivative coefficient rectangle has tail rank exactly when the
underlying Boolean orientations have tail rank. This is the exact converse to the earlier
one-way analytic construction. -/
theorem signedPrimeShiftedRotatedJet_tailIndependent_iff
    {J A : Type*} [Fintype J] [Fintype A] [Nonempty A]
    (ε : J → Nat.Primes → Bool) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re)) (m : ℕ) :
    TailCoefficientIndependent
        (fun jak : J × (A × Fin (m + 1)) => fun p =>
          primeDirichletSign (ε jak.1 p) * primeShiftFactor (alpha jak.2.1) p *
            rotatedPrimeLogClock p ^ (jak.2.2 : ℕ)) ↔
      PrimeOrientationTailIndependent ε := by
  classical
  let c : J → Nat.Primes → ℂ := fun j p => primeDirichletSign (ε j p)
  let raw := coefficientShiftJet c
    (fun a p => primeShiftFactor (alpha a) p) primeLogClock m
  let u : J × (A × Fin (m + 1)) → ℂ :=
    fun jak => Complex.I ^ (jak.2.2 : ℕ)
  have hu : ∀ jak, u jak ≠ 0 := fun jak => pow_ne_zero _ Complex.I_ne_zero
  have hscale :
      TailCoefficientIndependent (fun jak p => u jak * raw jak p) ↔
        TailCoefficientIndependent raw :=
    tailCoefficientIndependent_scale_columns_iff raw u hu
  have hraw : TailCoefficientIndependent raw ↔ TailCoefficientIndependent c := by
    constructor
    · intro hm
      exact tailCoefficientIndependent_of_coefficientShiftJet c
        (fun a p => primeShiftFactor (alpha a) p) primeLogClock m
        (primeShiftFactor_hasNowhereZeroFactor alpha) hm
    · intro hc
      exact ((primeCompleteShiftJetTailIndependent_iff c alpha hdistinct
        (primeOrientationCoefficientPattern_range_finite ε)).mpr hc) m
  change TailCoefficientIndependent
      (fun jak : J × (A × Fin (m + 1)) => fun p =>
        primeDirichletSign (ε jak.1 p) * primeShiftFactor (alpha jak.2.1) p *
          rotatedPrimeLogClock p ^ (jak.2.2 : ℕ)) ↔
    TailCoefficientIndependent c
  rw [← hraw, ← hscale]
  have hfun :
      (fun jak : J × (A × Fin (m + 1)) => fun p =>
        primeDirichletSign (ε jak.1 p) * primeShiftFactor (alpha jak.2.1) p *
          rotatedPrimeLogClock p ^ (jak.2.2 : ℕ)) =
      (fun jak p => u jak * raw jak p) := by
    funext jak p
    simp only [raw, c, u, coefficientShiftJet, rotatedPrimeLogClock]
    rw [mul_pow]
    ring
  rw [hfun]

/-- **Exact shifted tail matroid over the finite-prime field.** Every finite rectangle of
translated analytic jets is algebraically independent over the intrinsic finite-prime field if
and only if the original Boolean orientation family is independent modulo finite prime support. -/
theorem signedPrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeCoefficientField_iff
    {J A : Type*} [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ε : J → Nat.Primes → Bool) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re)) (m : ℕ) :
    AlgebraicIndependent finitePrimeCoefficientField
        (fun jak : J × (A × Fin (m + 1)) =>
          algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (signedPrimeShiftedRotatedJet
              (ε jak.1) (alpha jak.2.1) jak.2.2).1) ↔
      PrimeOrientationTailIndependent ε := by
  let coeff : J × (A × Fin (m + 1)) → Nat.Primes → ℂ :=
    fun jak p => primeDirichletSign (ε jak.1 p) *
      primeShiftFactor (alpha jak.2.1) p * rotatedPrimeLogClock p ^ (jak.2.2 : ℕ)
  rw [← signedPrimeShiftedRotatedJet_tailIndependent_iff ε alpha hdistinct m]
  have h :=
    algebraicIndependent_fractionPrimeColumns_over_finitePrimeCoefficientField_iff coeff
  have hfamily :
      (fun jak : J × (A × Fin (m + 1)) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (signedPrimeShiftedRotatedJet
            (ε jak.1) (alpha jak.2.1) jak.2.2).1) =
      (fun jak => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimeColumn (coeff jak))) := by
    funext jak
    congr 1
    exact signedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn
      (ε jak.1) (alpha jak.2.1) jak.2.2
  rw [hfamily]
  exact h

/-- The unshifted carrier family is the degree-zero face of the exact tail matroid. -/
theorem signedPrimeArithmeticFunctions_algebraicIndependent_over_finitePrimeCoefficientField_iff
    {J : Type*} [Fintype J] [DecidableEq J]
    (ε : J → Nat.Primes → Bool) :
    AlgebraicIndependent finitePrimeCoefficientField
        (fun j => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (signedPrimeArithmeticFunction (ε j))) ↔
      PrimeOrientationTailIndependent ε := by
  simpa only [signedPrimeArithmeticFunction] using!
    (algebraicIndependent_fractionPrimeColumns_over_finitePrimeCoefficientField_iff
      (fun j p => primeDirichletSign (ε j p)))

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

noncomputable section

/-- **Exact shifted tail matroid over `E_fin(s)`.** Adjoining the independent rational coordinate
does not change the finite shifted-jet independence criterion. -/
theorem signedPrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeRationalCoefficientField_iff
    {J A : Type*} [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ε : J → Nat.Primes → Bool) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re)) (m : ℕ) :
    AlgebraicIndependent finitePrimeRationalCoefficientField
        (fun jak : J × (A × Fin (m + 1)) =>
          algebraMap arithmeticFunctionFractionField
            arithmeticFunctionRationalCoordinateField
            (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
              (signedPrimeShiftedRotatedJet
                (ε jak.1) (alpha jak.2.1) jak.2.2).1)) ↔
      PrimeOrientationTailIndependent ε := by
  rw [algebraicIndependent_constants_over_finitePrimeRationalCoefficientField_iff]
  exact
    signedPrimeShiftedRotatedJets_algebraicIndependent_over_finitePrimeCoefficientField_iff
      ε alpha hdistinct m

/-- The unshifted carrier tail matroid is likewise unchanged by adjoining the rational
coordinate. -/
theorem signedPrimeArithmeticFunctions_algebraicIndependent_over_finitePrimeRationalCoefficientField_iff
    {J : Type*} [Fintype J] [DecidableEq J]
    (ε : J → Nat.Primes → Bool) :
    AlgebraicIndependent finitePrimeRationalCoefficientField
        (fun j => algebraMap arithmeticFunctionFractionField
          arithmeticFunctionRationalCoordinateField
          (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (signedPrimeArithmeticFunction (ε j)))) ↔
      PrimeOrientationTailIndependent ε := by
  rw [algebraicIndependent_constants_over_finitePrimeRationalCoefficientField_iff]
  exact
    signedPrimeArithmeticFunctions_algebraicIndependent_over_finitePrimeCoefficientField_iff ε

end

end GaloisForLFunctions.HTGeometry
