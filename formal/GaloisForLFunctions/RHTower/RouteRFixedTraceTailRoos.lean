import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinSchattenWall
import GaloisForLFunctions.RHTower.PrimeLogTripleCluster
import GaloisForLFunctions.RHTower.CCMRationalAdelicCompletedXiFixedCoronaPolarization
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology
import GaloisForLFunctions.RHTower.DeningerMeyerRelationKernelBoundarySeparation
import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestPolarizedChainSource
import GaloisForLFunctions.HTGeometry.ShilovBoundaryMigrationDefect

/-!
# Exact tail--Roos model of Route R's fixed first-trace boundary

The fixed physical prime quotient has a canonical tail presentation.  A global coefficient
sequence gives compatible quotient tails; zero-prepending the next tail differs from the current
tail by one summable head atom.  This file proves that a summable Roos primitive for this diagonal
mismatch is unique: it must be the negative literal coefficient tail.  Consequently the diagonal
derived class vanishes exactly when the original sequence is summable.

Applied to the enumerated reflected-minus-forward activation-Fisher coefficient, this proves that
the explicit singular Gamma Bockstein's diagonal Roos class vanishes exactly at neutral grade.
The result neither assumes a Xi zero location nor supplies the still-missing arithmetic source
primitive.
-/

open GaloisForLFunctions.HTGeometry.BoundaryMigration

namespace RHTower

noncomputable section

/-- Countable coordinate model used for successive ordinary-prime tails. -/
abbrev RouteRTraceSequence := ℕ → ℂ

/-- Zero-prepending bond between successive relative tail coordinates. -/
def routeRPrependZero : RouteRTraceSequence →ₗ[ℂ] RouteRTraceSequence where
  toFun x
    | 0 => 0
    | n + 1 => x n
  map_add' x y := by
    funext n
    cases n <;> simp
  map_smul' c x := by
    funext n
    cases n <;> simp

@[simp] theorem routeRPrependZero_apply_zero (x : RouteRTraceSequence) :
    routeRPrependZero x 0 = 0 := rfl

@[simp] theorem routeRPrependZero_apply_succ
    (x : RouteRTraceSequence) (n : ℕ) :
    routeRPrependZero x (n + 1) = x n := rfl

/-- The `n`th relative tail of a global coefficient sequence. -/
def routeRTail (a : RouteRTraceSequence) (n : ℕ) : RouteRTraceSequence :=
  fun k => a (n + k)

@[simp] theorem routeRTail_apply
    (a : RouteRTraceSequence) (n k : ℕ) :
    routeRTail a n k = a (n + k) := rfl

/-- Diagonal boundary mismatch between consecutive coefficient tails. -/
def routeRDiagonalMismatch
    (a : RouteRTraceSequence) (n : ℕ) : RouteRTraceSequence :=
  routeRPrependZero (routeRTail a (n + 1)) - routeRTail a n

@[simp] theorem routeRDiagonalMismatch_apply_zero
    (a : RouteRTraceSequence) (n : ℕ) :
    routeRDiagonalMismatch a n 0 = -a n := by
  simp [routeRDiagonalMismatch, routeRTail]

@[simp] theorem routeRDiagonalMismatch_apply_succ
    (a : RouteRTraceSequence) (n k : ℕ) :
    routeRDiagonalMismatch a n (k + 1) = 0 := by
  simp [routeRDiagonalMismatch, routeRTail]
  have hindex : n + 1 + k = n + (k + 1) := by omega
  rw [hindex, sub_self]

/-- Constant inverse sequence whose bond zero-prepends the next relative tail. -/
def routeRTailRoosBond :
    ∀ _n : ℕ, RouteRTraceSequence →ₗ[ℂ] RouteRTraceSequence :=
  fun _ => routeRPrependZero

/-- Rigidity of the diagonal Roos equation: its only unrestricted primitive is the negative
literal tail family.  This is stronger than an existence criterion. -/
theorem routeRTailRoos_primitive_unique
    (a : RouteRTraceSequence) (h : ℕ → RouteRTraceSequence)
    (hh : inverseDifference (fun _ : ℕ => RouteRTraceSequence)
      routeRTailRoosBond h = routeRDiagonalMismatch a) :
    h = fun n => -routeRTail a n := by
  funext n k
  have hcoord : ∀ n k, h n k = -a (n + k) := by
    intro n k
    induction k generalizing n with
    | zero =>
        have hn := congrFun hh n
        have hn0 := congrFun hn 0
        simpa [inverseDifference, routeRTailRoosBond] using hn0
    | succ k ih =>
        have hn := congrFun hh n
        have hnk := congrFun hn (k + 1)
        have hstep : h n (k + 1) = h (n + 1) k := by
          exact sub_eq_zero.mp (by
            simpa [inverseDifference, routeRTailRoosBond] using hnk)
        rw [hstep, ih]
        congr 2
        omega
  rw [hcoord]
  simp [routeRTail]

/-- Fixed summable ideal on every relative tail stage. -/
def routeRSummableSequenceIdeal : Submodule ℂ RouteRTraceSequence where
  carrier := {a | Summable a}
  zero_mem' := summable_zero
  add_mem' ha hb := ha.add hb
  smul_mem' c a ha := by
    change Summable (fun i => c * a i)
    exact ha.const_smul c

/-- Every diagonal mismatch is a one-head-atom member of the fixed summable ideal. -/
def routeRDiagonalMismatchInIdeal
    (a : RouteRTraceSequence) (n : ℕ) : routeRSummableSequenceIdeal :=
  ⟨routeRDiagonalMismatch a n, by
    change Summable (routeRDiagonalMismatch a n)
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (Set.finite_singleton 0)
    intro k hk
    by_contra hk0
    apply hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    simp⟩

/-- Zero-prepending restricted to the fixed summable tail ideal. -/
def routeRTailRoosRestrictedBond :
    ∀ _n : ℕ, routeRSummableSequenceIdeal →ₗ[ℂ]
      routeRSummableSequenceIdeal :=
  fun _ =>
    routeRPrependZero.domRestrict routeRSummableSequenceIdeal |>.codRestrict
      routeRSummableSequenceIdeal (fun x => by
        change Summable (routeRPrependZero x)
        apply (summable_nat_add_iff
          (f := routeRPrependZero (x : RouteRTraceSequence)) 1).mp
        simpa only [routeRPrependZero_apply_succ] using
          (show Summable (x : RouteRTraceSequence) from x.property))

/-- Derived tail obstruction carried by the diagonal mismatch. -/
def routeRDiagonalTailRoosClass (a : RouteRTraceSequence) :
    DerivedLimitOne (fun _ : ℕ => routeRSummableSequenceIdeal)
      routeRTailRoosRestrictedBond :=
  Submodule.Quotient.mk (routeRDiagonalMismatchInIdeal a)

/-- Exact fixed-ideal classification: the diagonal tail obstruction is null-homologous precisely
when the original global coefficient sequence is summable. -/
theorem routeRDiagonalTailRoosClass_eq_zero_iff_summable
    (a : RouteRTraceSequence) :
    routeRDiagonalTailRoosClass a = 0 ↔ Summable a := by
  rw [routeRDiagonalTailRoosClass, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨h, hh⟩
    let hv : ℕ → RouteRTraceSequence := fun n => h n
    have hfull :
        inverseDifference (fun _ : ℕ => RouteRTraceSequence)
            routeRTailRoosBond hv = routeRDiagonalMismatch a := by
      funext n
      exact congrArg Subtype.val (congrFun hh n)
    have huniq := routeRTailRoos_primitive_unique a hv hfull
    have hs : Summable (hv 0) := (h 0).property
    have heq0 := congrFun huniq 0
    have heq : hv 0 = -a := by
      calc
        hv 0 = -routeRTail a 0 := heq0
        _ = -a := by
          funext k
          simp [routeRTail]
    rw [heq] at hs
    simpa using hs.neg
  · intro ha
    let h : ∀ _n : ℕ, routeRSummableSequenceIdeal := fun n =>
      ⟨-routeRTail a n, by
        have htail : Summable (routeRTail a n) := by
          apply ha.comp_injective
          intro i j hij
          exact Nat.add_left_cancel hij
        exact htail.neg⟩
    refine ⟨h, ?_⟩
    funext n
    apply Subtype.ext
    change (-routeRTail a n) - routeRPrependZero (-routeRTail a (n + 1)) =
      routeRDiagonalMismatch a n
    rw [map_neg]
    unfold routeRDiagonalMismatch
    abel

/-- Reflected-minus-forward Fisher Bockstein in canonical increasing-prime coordinates. -/
def routeRPrimeGammaBocksteinSequence (t : ℝ) : RouteRTraceSequence :=
  fun n =>
    primeActivationOccupancyFisherComplexTwist (-t) (nthPrimeEquiv n) -
      primeActivationOccupancyFisherComplexTwist t (nthPrimeEquiv n)

/-- In the moderate strip, the enumerated coefficient is summable exactly at neutral grade. -/
theorem summable_routeRPrimeGammaBocksteinSequence_iff
    {t : ℝ} (ht : |t| < 1) :
    Summable (routeRPrimeGammaBocksteinSequence t) ↔ t = 0 := by
  let f : PrimeTraceSequence :=
    primeActivationOccupancyFisherComplexTwist (-t) -
      primeActivationOccupancyFisherComplexTwist t
  have henum : Summable (routeRPrimeGammaBocksteinSequence t) ↔ Summable f := by
    change Summable (f ∘ nthPrimeEquiv) ↔ Summable f
    exact nthPrimeEquiv.summable_iff
  rw [henum]
  have hclass : Summable f ↔ primeGammaCofinalBockstein t = 0 := by
    have hrepr : primeGammaCofinalBockstein t =
        (Submodule.Quotient.mk f :
          PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal) := by
      unfold primeGammaCofinalBockstein primeFixedPhysicalFisherClass
      exact (Submodule.Quotient.mk_sub primeFirstTraceSummableIdeal).symm
    rw [hrepr, Submodule.Quotient.mk_eq_zero]
    rfl
  exact hclass.trans (primeGammaCofinalBockstein_eq_zero_iff ht)

/-- Route R's explicit diagonal Gamma Bockstein is null-homologous exactly at neutral grade. -/
theorem routeRPrimeGammaDiagonalTailRoosClass_eq_zero_iff
    {t : ℝ} (ht : |t| < 1) :
    routeRDiagonalTailRoosClass (routeRPrimeGammaBocksteinSequence t) = 0 ↔
      t = 0 := by
  rw [routeRDiagonalTailRoosClass_eq_zero_iff_summable,
    summable_routeRPrimeGammaBocksteinSequence_iff ht]

/-! ## Pre-divisor Gamma aperture and its literal fixed-ideal primitive -/

/-- Gamma damping of the explicit all-prime Bockstein mass.  The aperture parameter is independent
of divisor placement. -/
def primeGammaCofinalBocksteinDampedMass
    (epsilon t : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-epsilon) * primeGammaCofinalBocksteinMagnitude t p

/-- Sharp trace-wall law: Gamma damping makes the explicit Bockstein summable precisely in the
open cone `|t| < epsilon` (apart from the identically zero neutral grade). -/
theorem summable_primeGammaCofinalBocksteinDampedMass_iff
    (epsilon t : ℝ) :
    Summable (primeGammaCofinalBocksteinDampedMass epsilon t) ↔
      t = 0 ∨ |t| < epsilon := by
  by_cases ht : t = 0
  · subst t
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      have hzero : primeGammaCofinalBocksteinDampedMass epsilon 0 =
          fun _ : Nat.Primes => 0 := by
        funext p
        simp [primeGammaCofinalBocksteinDampedMass,
          primeGammaCofinalBocksteinMagnitude]
      rw [hzero]
      exact summable_zero
  · have hc : 0 < (1 / 4 : ℝ) * (1 - (2 : ℝ) ^ (-2 * |t|)) := by
      have habs : 0 < |t| := abs_pos.mpr ht
      have hpow : (2 : ℝ) ^ (-2 * |t|) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      positivity
    have hbounds : ∀ p : Nat.Primes,
        ((1 / 4 : ℝ) * (1 - (2 : ℝ) ^ (-2 * |t|))) *
              (p : ℝ) ^ (|t| - 1 - epsilon) ≤
            primeGammaCofinalBocksteinDampedMass epsilon t p ∧
          primeGammaCofinalBocksteinDampedMass epsilon t p ≤
            (p : ℝ) ^ (|t| - 1 - epsilon) := by
      intro p
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
      have hdamp0 : 0 ≤ (p : ℝ) ^ (-epsilon) := Real.rpow_nonneg hp0.le _
      have hmag := primeGammaCofinalBocksteinMagnitude_bounds t p
      have hpow : (p : ℝ) ^ (-epsilon) * (p : ℝ) ^ (|t| - 1) =
          (p : ℝ) ^ (|t| - 1 - epsilon) := by
        rw [← Real.rpow_add hp0]
        congr 1
        ring
      constructor
      · rw [primeGammaCofinalBocksteinDampedMass]
        calc
          (1 / 4 : ℝ) * (1 - (2 : ℝ) ^ (-2 * |t|)) *
                (p : ℝ) ^ (|t| - 1 - epsilon) =
              (p : ℝ) ^ (-epsilon) *
                ((1 / 4 : ℝ) * (1 - (2 : ℝ) ^ (-2 * |t|)) *
                  (p : ℝ) ^ (|t| - 1)) := by rw [← hpow]; ring
          _ ≤ (p : ℝ) ^ (-epsilon) *
                primeGammaCofinalBocksteinMagnitude t p :=
            mul_le_mul_of_nonneg_left hmag.1 hdamp0
      · rw [primeGammaCofinalBocksteinDampedMass]
        calc
          (p : ℝ) ^ (-epsilon) *
                primeGammaCofinalBocksteinMagnitude t p ≤
              (p : ℝ) ^ (-epsilon) * (p : ℝ) ^ (|t| - 1) :=
            mul_le_mul_of_nonneg_left hmag.2 hdamp0
          _ = (p : ℝ) ^ (|t| - 1 - epsilon) := hpow
    constructor
    · intro hsum
      have hscaled : Summable (fun p : Nat.Primes =>
          ((1 / 4 : ℝ) * (1 - (2 : ℝ) ^ (-2 * |t|))) *
            (p : ℝ) ^ (|t| - 1 - epsilon)) :=
        Summable.of_nonneg_of_le (fun _ => by positivity)
          (fun p => (hbounds p).1) hsum
      have hmodel : Summable (fun p : Nat.Primes =>
          (p : ℝ) ^ (|t| - 1 - epsilon)) :=
        (summable_mul_left_iff hc.ne').mp hscaled
      have hexp := (Nat.Primes.summable_rpow).mp hmodel
      exact Or.inr (by linarith)
    · rintro (_ | hthreshold)
      · contradiction
      · have hmodel : Summable (fun p : Nat.Primes =>
            (p : ℝ) ^ (|t| - 1 - epsilon)) :=
          (Nat.Primes.summable_rpow).2 (by linarith)
        exact Summable.of_nonneg_of_le (fun _ => by
          exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
            (abs_nonneg _)) (fun p => (hbounds p).2) hmodel

/-- Enumerated coefficient-faithful Gamma-damped Bockstein sequence. -/
def routeRPrimeGammaDampedBocksteinSequence
    (epsilon t : ℝ) : RouteRTraceSequence :=
  fun n =>
    (↑(((nthPrimeEquiv n : ℕ) : ℝ) ^ (-epsilon)) : ℂ) *
      (primeActivationOccupancyFisherComplexTwist (-t) (nthPrimeEquiv n) -
        primeActivationOccupancyFisherComplexTwist t (nthPrimeEquiv n))

theorem norm_routeRPrimeGammaDampedBocksteinSequence
    (epsilon t : ℝ) (n : ℕ) :
    ‖routeRPrimeGammaDampedBocksteinSequence epsilon t n‖ =
      primeGammaCofinalBocksteinDampedMass epsilon t (nthPrimeEquiv n) := by
  rw [routeRPrimeGammaDampedBocksteinSequence, norm_mul, Complex.norm_real]
  have hp0 : 0 ≤ (((nthPrimeEquiv n : ℕ) : ℝ) ^ (-epsilon)) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hp0]
  simp only [primeActivationOccupancyFisherComplexTwist]
  rw [← Complex.ofReal_sub]
  rw [Complex.norm_real, Real.norm_eq_abs]
  change (((nthPrimeEquiv n : ℕ) : ℝ) ^ (-epsilon)) *
      |primeActivationOccupancyFisherTwist (-t) (nthPrimeEquiv n) -
        primeActivationOccupancyFisherTwist t (nthPrimeEquiv n)| = _
  rfl

theorem summable_routeRPrimeGammaDampedBocksteinSequence_iff
    (epsilon t : ℝ) :
    Summable (routeRPrimeGammaDampedBocksteinSequence epsilon t) ↔
      t = 0 ∨ |t| < epsilon := by
  rw [← summable_primeGammaCofinalBocksteinDampedMass_iff epsilon t]
  constructor
  · intro hsum
    apply nthPrimeEquiv.summable_iff.mp
    exact (summable_norm_iff.mpr hsum).congr fun n =>
      norm_routeRPrimeGammaDampedBocksteinSequence epsilon t n
  · intro hsum
    apply summable_norm_iff.mp
    exact (nthPrimeEquiv.summable_iff.mpr hsum).congr fun n =>
      (norm_routeRPrimeGammaDampedBocksteinSequence epsilon t n).symm

/-- Literal source-side tail primitive in the fixed summable ideal, valid throughout the safe
Gamma cone. -/
def routeRPrimeGammaSafeConeTailPrimitive
    (epsilon t : ℝ) (hcone : |t| < epsilon) :
    ∀ _n : ℕ, routeRSummableSequenceIdeal :=
  fun n =>
    ⟨-routeRTail (routeRPrimeGammaDampedBocksteinSequence epsilon t) n, by
      have hall : Summable (routeRPrimeGammaDampedBocksteinSequence epsilon t) :=
        (summable_routeRPrimeGammaDampedBocksteinSequence_iff epsilon t).2
          (Or.inr hcone)
      have htail : Summable
          (routeRTail (routeRPrimeGammaDampedBocksteinSequence epsilon t) n) := by
        apply hall.comp_injective
        intro i j hij
        exact Nat.add_left_cancel hij
      exact htail.neg⟩

/-- The literal source tail has exactly the damped diagonal Bockstein as Roos boundary. -/
theorem routeRPrimeGammaSafeConeTailPrimitive_boundary
    (epsilon t : ℝ) (hcone : |t| < epsilon) :
    inverseDifference (fun _ : ℕ => routeRSummableSequenceIdeal)
        routeRTailRoosRestrictedBond
        (routeRPrimeGammaSafeConeTailPrimitive epsilon t hcone) =
      routeRDiagonalMismatchInIdeal
        (routeRPrimeGammaDampedBocksteinSequence epsilon t) := by
  funext n
  apply Subtype.ext
  change (-routeRTail (routeRPrimeGammaDampedBocksteinSequence epsilon t) n) -
      routeRPrependZero
        (-routeRTail (routeRPrimeGammaDampedBocksteinSequence epsilon t) (n + 1)) =
    routeRDiagonalMismatch
      (routeRPrimeGammaDampedBocksteinSequence epsilon t) n
  rw [map_neg]
  unfold routeRDiagonalMismatch
  abel

/-- Inside the Gamma aperture, the damped all-prime Bockstein has zero fixed-tail class. -/
theorem routeRPrimeGammaSafeConeDiagonalTailRoosClass_eq_zero
    (epsilon t : ℝ) (hcone : |t| < epsilon) :
    routeRDiagonalTailRoosClass
        (routeRPrimeGammaDampedBocksteinSequence epsilon t) = 0 :=
  (routeRDiagonalTailRoosClass_eq_zero_iff_summable _).2
    ((summable_routeRPrimeGammaDampedBocksteinSequence_iff epsilon t).2
      (Or.inr hcone))

/-! ## Exact variable-grade Euler source boundary -/

/-- Pre-divisor source retaining the complete real modular-grade line and every ordinary-prime
coefficient.  Reflection acts on the grade before any Xi fibre is selected. -/
abbrev RouteRPrimeGammaVariableGradeSource :=
  ℝ → RouteRTraceSequence

/-- Reflection of the pre-divisor modular grade. -/
def routeRPrimeGammaVariableGradeReflection :
    RouteRPrimeGammaVariableGradeSource →ₗ[ℂ]
      RouteRPrimeGammaVariableGradeSource where
  toFun f t := f (-t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reflection-minus-identity source differential. -/
def routeRPrimeGammaVariableGradeBoundary :
    RouteRPrimeGammaVariableGradeSource →ₗ[ℂ]
      RouteRPrimeGammaVariableGradeSource :=
  routeRPrimeGammaVariableGradeReflection - LinearMap.id

/-- Complete forward activation-Fisher family before fixing a modular grade. -/
def routeRPrimeGammaVariableGradeFisherSource :
    RouteRPrimeGammaVariableGradeSource :=
  fun t n =>
    primeActivationOccupancyFisherComplexTwist t (nthPrimeEquiv n)

/-- The variable-grade boundary space. -/
def routeRPrimeGammaVariableGradeBoundarySpace :
    Submodule ℂ RouteRPrimeGammaVariableGradeSource :=
  LinearMap.range routeRPrimeGammaVariableGradeBoundary

/-- Absolute source quotient before physical fixed-fibre specialization. -/
abbrev RouteRPrimeGammaVariableGradeSourceHomology :=
  RouteRPrimeGammaVariableGradeSource ⧸
    routeRPrimeGammaVariableGradeBoundarySpace

/-- Variable-grade central Bockstein class. -/
def routeRPrimeGammaVariableGradeCentralBocksteinClass :
    RouteRPrimeGammaVariableGradeSourceHomology :=
  Submodule.Quotient.mk
    (routeRPrimeGammaVariableGradeBoundary
      routeRPrimeGammaVariableGradeFisherSource)

/-- Before fixing a grade, the complete reflected-minus-forward Fisher family is a literal source
boundary.  Both Gamma orientations remain present as the two reflected source values. -/
theorem routeRPrimeGammaVariableGradeCentralBocksteinClass_eq_zero :
    routeRPrimeGammaVariableGradeCentralBocksteinClass = 0 := by
  rw [routeRPrimeGammaVariableGradeCentralBocksteinClass,
    Submodule.Quotient.mk_eq_zero]
  exact ⟨routeRPrimeGammaVariableGradeFisherSource, rfl⟩

/-- Fixed-grade evaluation of the exact source boundary is the explicit Route R Bockstein
sequence.  Thus evaluation and passage to source homology do not commute automatically. -/
theorem routeRPrimeGammaVariableGradeBoundary_apply
    (t : ℝ) :
    routeRPrimeGammaVariableGradeBoundary
        routeRPrimeGammaVariableGradeFisherSource t =
      routeRPrimeGammaBocksteinSequence t := by
  funext n
  rfl

/-- Sharp specialization wall: although the variable-grade class is always a source boundary,
its fixed-tail physical specialization is null exactly at neutral grade. -/
theorem
    routeRPrimeGammaVariableGradeBoundary_fixedTailClass_eq_zero_iff
    {t : ℝ} (ht : |t| < 1) :
    routeRDiagonalTailRoosClass
        (routeRPrimeGammaVariableGradeBoundary
          routeRPrimeGammaVariableGradeFisherSource t) = 0 ↔
      t = 0 := by
  rw [routeRPrimeGammaVariableGradeBoundary_apply,
    routeRPrimeGammaDiagonalTailRoosClass_eq_zero_iff ht]

/-! ## Literal polarized Euler Fisher-column provenance -/

/-- Ordinary-prime column of the explicit polarized Euler Fisher source. -/
def routeRPrimeGammaEulerFisherColumn (p : Nat.Primes) : ℂ :=
  eulerPrimitiveBoundaryFisherColumn
    (fun _ : Unit => (((p : ℕ) : ℝ) : ℂ)) ()

/-- The Euler source column is twice the activation-Fisher density used by Route R. -/
theorem routeRPrimeGammaEulerFisherColumn_eq_two_mul_density
    (p : Nat.Primes) :
    routeRPrimeGammaEulerFisherColumn p =
      ((2 * primeActivationOccupancyFisherDensity p : ℝ) : ℂ) := by
  rw [routeRPrimeGammaEulerFisherColumn,
    eulerPrimitiveBoundaryFisherColumn,
    primeActivationOccupancyFisherDensity_eq]
  push_cast
  ring

/-- The coefficient is not an inserted scalar: it is the actual test/score column of the
pre-divisor polarized Euler source Gram. -/
theorem routeRPrimeGammaEulerFisherColumn_eq_sourcePairing
    (p : Nat.Primes) :
    routeRPrimeGammaEulerFisherColumn p =
      eulerPrimitiveBoundaryPolarizedPairing
        (eulerPrimitiveBoundaryPolarizedTest
          ((((p : ℕ) : ℝ) : ℂ)))
        eulerPrimitiveBoundaryPolarizedScore := by
  rw [routeRPrimeGammaEulerFisherColumn,
    eulerPrimitiveBoundaryPolarizedPairing_test_score]
  · rfl
  · simp
    exact_mod_cast p.2.pos

/-- Coefficient-faithful Euler-source realization of the local Route R Bockstein.  Its sole
orientation factor is the reflected-minus-forward power skew; the positive Fisher column is
retained without division or divisor specialization. -/
theorem routeRPrimeGammaBockstein_eq_eulerFisherSourceColumn
    (t : ℝ) (p : Nat.Primes) :
    ((primeActivationOccupancyFisherTwist (-t) p -
        primeActivationOccupancyFisherTwist t p : ℝ) : ℂ) =
      ((((p : ℝ) ^ (-t) - (p : ℝ) ^ t) / 2 : ℝ) : ℂ) *
        routeRPrimeGammaEulerFisherColumn p := by
  rw [routeRPrimeGammaEulerFisherColumn,
    primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherTwist,
    eulerPrimitiveBoundaryFisherColumn,
    primeActivationOccupancyFisherDensity_eq]
  push_cast
  ring

/-! ## Coefficient-faithful comparison with the arithmetic central Bockstein -/

/-- Natural same-prime transfer coefficient from Deninger central holonomy to the activation-
Fisher Bockstein.  It is defined before divisor specialization and never vanishes. -/
def routeRPrimeGammaCentralTransferFactor
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  -primeActivationOccupancyFisherDensity p *
    (1 + (p : ℝ) ^ (-t))

/-- Exact source-native factorization.  Route R's reflected-minus-forward Fisher coefficient is
the same-prime central holonomy defect times a canonical, nondivisive transfer coefficient. -/
theorem routeRPrimeGammaBockstein_eq_centralGainDefect
    (t : ℝ) (p : Nat.Primes) :
    primeActivationOccupancyFisherTwist (-t) p -
        primeActivationOccupancyFisherTwist t p =
      routeRPrimeGammaCentralTransferFactor t p *
        ((p : ℝ) ^ t - 1) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hprod : (p : ℝ) ^ (-t) * (p : ℝ) ^ t = 1 := by
    rw [← Real.rpow_add hp0]
    norm_num
  rw [primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherTwist,
    routeRPrimeGammaCentralTransferFactor]
  calc
    (p : ℝ) ^ (-t) * primeActivationOccupancyFisherDensity p -
          (p : ℝ) ^ t * primeActivationOccupancyFisherDensity p =
        primeActivationOccupancyFisherDensity p *
          ((p : ℝ) ^ (-t) - (p : ℝ) ^ t) := by ring
    _ = -primeActivationOccupancyFisherDensity p *
          (1 + (p : ℝ) ^ (-t)) * ((p : ℝ) ^ t - 1) +
        primeActivationOccupancyFisherDensity p *
          ((p : ℝ) ^ (-t) * (p : ℝ) ^ t - 1) := by ring
    _ = -primeActivationOccupancyFisherDensity p *
          (1 + (p : ℝ) ^ (-t)) * ((p : ℝ) ^ t - 1) := by
      rw [hprod]
      ring

theorem routeRPrimeGammaCentralTransferFactor_ne_zero
    (t : ℝ) (p : Nat.Primes) :
    routeRPrimeGammaCentralTransferFactor t p ≠ 0 := by
  rw [routeRPrimeGammaCentralTransferFactor]
  have hdensity : 0 < primeActivationOccupancyFisherDensity p := by
    rw [primeActivationOccupancyFisherDensity_eq_damping_sq]
    exact sq_pos_of_pos (xiMobiusPrimeSchurValuationDamping_pos p)
  have hsum : 0 < 1 + (p : ℝ) ^ (-t) := by positivity
  exact mul_ne_zero (neg_ne_zero.mpr hdensity.ne') hsum.ne'

/-- At an ordinary-prime clock, the Deninger half-density mate gain is the literal real power with
centered exponent `2 re(s) - 1`. -/
theorem deningerHalfDensityMateGain_prime_eq_rpow
    (p : Nat.Primes) (s : ℂ) :
    deningerHalfDensityMateGain p s =
      (p : ℝ) ^ (2 * s.re - 1) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [deningerHalfDensityMateGain, Real.rpow_def_of_pos hp0]
  congr 1
  ring

/-- Coefficient-faithful pre-divisor Cartier comparison between the fixed-trace Gamma Bockstein and
the rational-adelic paracyclic central defect. -/
theorem routeRPrimeGammaBockstein_eq_deningerCentralDefect
    (p : Nat.Primes) (s : ℂ) :
    primeActivationOccupancyFisherTwist (-(2 * s.re - 1)) p -
        primeActivationOccupancyFisherTwist (2 * s.re - 1) p =
      routeRPrimeGammaCentralTransferFactor (2 * s.re - 1) p *
        (deningerHalfDensityMateGain p s - 1) := by
  rw [deningerHalfDensityMateGain_prime_eq_rpow]
  exact routeRPrimeGammaBockstein_eq_centralGainDefect _ _

/-! ## Exact comparison with the pre-divisor Gaussian source determinant -/

/-- Divided power character at one ordinary prime, extended at neutral grade by its logarithmic
derivative.  Unlike a pointwise quotient chosen after divisor specialization, this coefficient is
defined on the full pre-divisor real grade line. -/
def routeRPrimeGammaPowerSecant (t : ℝ) (p : Nat.Primes) : ℝ :=
  if t = 0 then Real.log (p : ℝ)
  else ((p : ℝ) ^ t - 1) / t

/-- The power secant reconstructs the ordinary-prime character defect at every grade, including
the neutral grade. -/
theorem routeRPrimeGammaPowerSecant_mul
    (t : ℝ) (p : Nat.Primes) :
    routeRPrimeGammaPowerSecant t p * t = (p : ℝ) ^ t - 1 := by
  by_cases ht : t = 0
  · subst t
    simp [routeRPrimeGammaPowerSecant]
  · rw [routeRPrimeGammaPowerSecant, if_neg ht]
    exact div_mul_cancel₀ _ ht

/-- The pre-divisor power secant never vanishes.  Thus passage from the additive horizontal
fracture to the multiplicative prime character loses no coefficient. -/
theorem routeRPrimeGammaPowerSecant_ne_zero
    (t : ℝ) (p : Nat.Primes) :
    routeRPrimeGammaPowerSecant t p ≠ 0 := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hp0 : 0 < (p : ℝ) := lt_trans Real.zero_lt_one hp1
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp1).ne'
  by_cases ht : t = 0
  · simp [routeRPrimeGammaPowerSecant, ht, hlog]
  · rw [routeRPrimeGammaPowerSecant, if_neg ht]
    apply div_ne_zero _ ht
    apply sub_ne_zero.mpr
    intro hpow
    rw [Real.rpow_def_of_pos hp0] at hpow
    have hprod : Real.log (p : ℝ) * t = 0 :=
      (Real.exp_eq_one_iff _).mp hpow
    exact ht ((mul_eq_zero.mp hprod).resolve_left hlog)

/-- Direct additive/multiplicative source comparison.  The fixed-trace Bockstein is the unsquared
Green fracture multiplied by the canonical nowhere-zero ordinary-prime transfer. -/
theorem routeRPrimeGammaBockstein_eq_greenFractureTransfer
    (p : Nat.Primes) (s : ℂ) :
    ((primeActivationOccupancyFisherTwist
          (-(2 * s.re - 1)) p -
        primeActivationOccupancyFisherTwist
          (2 * s.re - 1) p : ℝ) : ℂ) =
      (((routeRPrimeGammaCentralTransferFactor (2 * s.re - 1) p *
        routeRPrimeGammaPowerSecant (2 * s.re - 1) p : ℝ) : ℂ) *
        xiNearbyPoleDualityAdjunctionFracture s) := by
  let t : ℝ := 2 * s.re - 1
  have hfracture : xiNearbyPoleDualityAdjunctionFracture s = (t : ℂ) := by
    rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
    norm_num [t]
    ring
  have hbeta := congrArg (fun x : ℝ => (x : ℂ))
    (routeRPrimeGammaBockstein_eq_centralGainDefect t p)
  change ((primeActivationOccupancyFisherTwist (-t) p -
      primeActivationOccupancyFisherTwist t p : ℝ) : ℂ) =
    (((routeRPrimeGammaCentralTransferFactor t p *
      routeRPrimeGammaPowerSecant t p : ℝ) : ℂ) *
      xiNearbyPoleDualityAdjunctionFracture s)
  rw [hfracture]
  calc
    ((primeActivationOccupancyFisherTwist (-t) p -
        primeActivationOccupancyFisherTwist t p : ℝ) : ℂ) =
        ((routeRPrimeGammaCentralTransferFactor t p *
          ((p : ℝ) ^ t - 1) : ℝ) : ℂ) := hbeta
    _ = ((routeRPrimeGammaCentralTransferFactor t p *
          (routeRPrimeGammaPowerSecant t p * t) : ℝ) : ℂ) := by
      rw [routeRPrimeGammaPowerSecant_mul]
    _ = (((routeRPrimeGammaCentralTransferFactor t p *
          routeRPrimeGammaPowerSecant t p : ℝ) : ℂ) * (t : ℂ)) := by
      push_cast
      ring

/-- Canonical coefficient transporting the target-free reflected Gaussian source determinant to
Route R's same-prime fixed-trace Bockstein.  All factors are pre-divisor or fixed source data; no
critical-line condition occurs in the definition. -/
def routeRPrimeGammaXiWronskianTransferFactor
    (p : Nat.Primes) (q : XiZeroCopy) : ℂ :=
  (((routeRPrimeGammaCentralTransferFactor
      (2 * (q.1 : ℂ).re - 1) p *
        routeRPrimeGammaPowerSecant (2 * (q.1 : ℂ).re - 1) p : ℝ) : ℂ) /
    DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale q)

/-- The source-determinant comparison is coefficient-faithful: its transport coefficient never
vanishes on any Xi copy or ordinary-prime fibre. -/
theorem routeRPrimeGammaXiWronskianTransferFactor_ne_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    routeRPrimeGammaXiWronskianTransferFactor p q ≠ 0 := by
  apply div_ne_zero
  · exact Complex.ofReal_ne_zero.mpr
      (mul_ne_zero
        (routeRPrimeGammaCentralTransferFactor_ne_zero _ p)
        (routeRPrimeGammaPowerSecant_ne_zero _ p))
  · exact
      DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale_ne_zero q

/-- **Coefficient-level source comparison.**  Route R's explicit fixed-trace Bockstein coefficient
is exactly the target-free reflected Gaussian source Wronskian multiplied by a canonical
nowhere-zero pre-divisor transfer.  This identifies the tail--Roos, paracyclic, and Green defects
as one retained class, not merely three expressions with the same zero set. -/
theorem routeRPrimeGammaBockstein_eq_gaussianSourceWronskianTransfer
    (p : Nat.Primes) (q : XiZeroCopy) :
    ((primeActivationOccupancyFisherTwist
          (-(2 * (q.1 : ℂ).re - 1)) p -
        primeActivationOccupancyFisherTwist
          (2 * (q.1 : ℂ).re - 1) p : ℝ) : ℂ) =
      routeRPrimeGammaXiWronskianTransferFactor p q *
        DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLineWronskian q := by
  let t : ℝ := 2 * (q.1 : ℂ).re - 1
  let scale : ℂ :=
    DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale q
  have hscale : scale ≠ 0 :=
    DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale_ne_zero q
  have hfracture :
      xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) = (t : ℂ) := by
    rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
    norm_num [t]
    ring
  have hbeta := congrArg (fun x : ℝ => (x : ℂ))
    (routeRPrimeGammaBockstein_eq_centralGainDefect t p)
  change ((primeActivationOccupancyFisherTwist (-t) p -
      primeActivationOccupancyFisherTwist t p : ℝ) : ℂ) =
    ((((routeRPrimeGammaCentralTransferFactor t p *
          routeRPrimeGammaPowerSecant t p : ℝ) : ℂ) / scale) *
      DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLineWronskian q)
  rw [DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLineWronskian_eq_greenFracture_mul,
    hfracture]
  calc
    ((primeActivationOccupancyFisherTwist (-t) p -
        primeActivationOccupancyFisherTwist t p : ℝ) : ℂ) =
        ((routeRPrimeGammaCentralTransferFactor t p *
          ((p : ℝ) ^ t - 1) : ℝ) : ℂ) := hbeta
    _ = ((routeRPrimeGammaCentralTransferFactor t p *
          (routeRPrimeGammaPowerSecant t p * t) : ℝ) : ℂ) := by
      rw [routeRPrimeGammaPowerSecant_mul]
    _ = ((((routeRPrimeGammaCentralTransferFactor t p *
            routeRPrimeGammaPowerSecant t p : ℝ) : ℂ) / scale) *
          ((t : ℂ) * scale)) := by
      push_cast
      field_simp

/-! ## Relation-kernel realization of the same central class -/

/-- Route R's local Bockstein carried by the nonzero source-pointed Calderón--Witt commutator
calibrator.  This is a genuine relation-kernel coefficient object rather than a scalar quotient. -/
def routeRPrimeGammaXiRelationKernelCalibrator
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    DeningerCalderonWittDegreeTwo p :=
  ((primeActivationOccupancyFisherTwist
        (-(2 * (rho : ℂ).re - 1)) p -
      primeActivationOccupancyFisherTwist
        (2 * (rho : ℂ).re - 1) p : ℝ) : ℂ) •
    deningerCalderonWittSourcePointedTau p

/-- **Tail/source-cover identification.**  The explicit fixed-trace Bockstein on the retained
prime atom is the same nowhere-zero transfer of the Green-scaled relation-kernel transgression
ray constructed on the source-pointed free rational cover. -/
theorem routeRPrimeGammaXiRelationKernelCalibrator_eq_greenTransgressionRay
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    routeRPrimeGammaXiRelationKernelCalibrator p rho =
      (((routeRPrimeGammaCentralTransferFactor
          (2 * (rho : ℂ).re - 1) p *
        routeRPrimeGammaPowerSecant
          (2 * (rho : ℂ).re - 1) p : ℝ) : ℂ) •
        (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) •
          deningerCalderonWittSourcePointedTau p)) := by
  rw [routeRPrimeGammaXiRelationKernelCalibrator,
    routeRPrimeGammaBockstein_eq_greenFractureTransfer]
  rw [mul_smul]

/-! ## Actual Xi and fixed same-fibre physical landing -/

/-- The diagonal tail--Roos class of the actual centered Xi grade. -/
def routeRPrimeGammaXiDiagonalTailRoosClass (rho : XiDivisorSupport) :=
  routeRDiagonalTailRoosClass
    (routeRPrimeGammaBocksteinSequence (2 * (rho : ℂ).re - 1))

/-- Exact base-change identity from the unconditional variable-grade source boundary to the
actual fixed Xi tail class.  This is the specialization whose compatibility with source homology
is the remaining landing problem. -/
theorem routeRPrimeGammaVariableGradeBoundary_fixedXiSpecialization
    (rho : XiDivisorSupport) :
    routeRDiagonalTailRoosClass
        (routeRPrimeGammaVariableGradeBoundary
          routeRPrimeGammaVariableGradeFisherSource
          (2 * (rho : ℂ).re - 1)) =
      routeRPrimeGammaXiDiagonalTailRoosClass rho := by
  rw [routeRPrimeGammaVariableGradeBoundary_apply,
    routeRPrimeGammaXiDiagonalTailRoosClass]

/-- On every actual Xi support point, diagonal fixed-ideal null-homology is exactly critical-line
placement. -/
theorem routeRPrimeGammaXiDiagonalTailRoosClass_eq_zero_iff_re_eq_half
    (rho : XiDivisorSupport) :
    routeRPrimeGammaXiDiagonalTailRoosClass rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [routeRPrimeGammaXiDiagonalTailRoosClass,
    routeRPrimeGammaDiagonalTailRoosClass_eq_zero_iff
      (xiCenteredPrimeIdealRate_abs_lt_one rho)]
  constructor <;> intro h <;> linarith

/-- Exact comparison with the independently constructed rational-adelic cofinal source homology.
The fixed-tail Gamma class is null precisely when the physical paracyclic defect of the retained
trace-one prime atom is null in the canonical Tate relative complex. -/
theorem routeRPrimeGammaXiDiagonalTailRoosClass_eq_zero_iff_sourceNullHomologous
    {n : ℕ} (hn : 2 ≤ n) (p : Nat.Primes) (m : ℕ)
    (rho : XiDivisorSupport) :
    routeRPrimeGammaXiDiagonalTailRoosClass rho = 0 ↔
      CCMMobiusThetaPhysicalDefectSourceNullHomologous n rho p m := by
  rw [routeRPrimeGammaXiDiagonalTailRoosClass_eq_zero_iff_re_eq_half,
    ccmMobiusThetaPhysicalDefectSourceNullHomologous_iff hn]

/-- The new fixed-tail class and Route R's explicit same-fibre Hodge-mate coefficient vanish
together.  This is the coefficient-faithful bridge from singular all-prime homology to the
completed physical corona port. -/
theorem routeRPrimeGammaXiDiagonalTailRoosClass_eq_zero_iff_hodgeMateCoefficient_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    routeRPrimeGammaXiDiagonalTailRoosClass rho = 0 ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 :=
  (routeRPrimeGammaXiDiagonalTailRoosClass_eq_zero_iff_re_eq_half rho).trans
    (ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half p rho).symm

/-- Fully identified specialization frontier: the pre-divisor variable-grade Bockstein is an
absolute source boundary, while its actual fixed-Xi base change is null precisely when the fixed
physical Hodge-mate coefficient vanishes. -/
theorem
    routeRPrimeGammaVariableGradeBoundary_fixedXiClass_eq_zero_iff_hodgeMateCoefficient_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    routeRDiagonalTailRoosClass
        (routeRPrimeGammaVariableGradeBoundary
          routeRPrimeGammaVariableGradeFisherSource
          (2 * (rho : ℂ).re - 1)) = 0 ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 := by
  rw [routeRPrimeGammaVariableGradeBoundary_fixedXiSpecialization,
    routeRPrimeGammaXiDiagonalTailRoosClass_eq_zero_iff_hodgeMateCoefficient_eq_zero]

/-- A source proof of the fixed-tail boundary law discharges the explicit Hodge-mate coefficient,
with no additional physical-lift premise. -/
theorem ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_of_tailRoosClass_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hsource : routeRPrimeGammaXiDiagonalTailRoosClass rho = 0) :
    ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 :=
  (routeRPrimeGammaXiDiagonalTailRoosClass_eq_zero_iff_hodgeMateCoefficient_eq_zero
    p rho).mp hsource

/-- Fixed-tail source null-homology gives the actual fixed same-fibre norm identity. -/
theorem ccmRationalAdelicPrimeXiSameFiberNormIdentity_of_tailRoosClass_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hsource : routeRPrimeGammaXiDiagonalTailRoosClass rho = 0) :
    CCMRationalAdelicPrimeXiSameFiberNormIdentity p rho :=
  (ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_hodgeMateCoefficient_eq_zero
    p rho).2
      (ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_of_tailRoosClass_eq_zero
        p rho hsource)

/-- Fixed-tail source null-homology gives the actual source-dagger identity. -/
theorem ccmRationalAdelicPrimeXiSourceDaggerIdentity_of_tailRoosClass_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hsource : routeRPrimeGammaXiDiagonalTailRoosClass rho = 0) :
    CCMRationalAdelicPrimeXiSourceDaggerIdentity p rho :=
  (ccmRationalAdelicPrimeXiSourceDaggerIdentity_iff_hodgeMateCoefficient_eq_zero
    p rho).2
      (ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_of_tailRoosClass_eq_zero
        p rho hsource)

/-- Global source-native fixed-tail null-homology statement. -/
def RouteRPrimeGammaXiGlobalDiagonalTailRoosNullHomology : Prop :=
  ∀ rho : XiDivisorSupport,
    routeRPrimeGammaXiDiagonalTailRoosClass rho = 0

/-- Exact Route R endpoint: global null-homology of the explicit fixed-tail Bockstein class is
equivalent to RH.  The forward implication now passes through the actual completed-Xi Hodge
coefficient rather than an abstract quotient. -/
theorem routeRPrimeGammaXiGlobalDiagonalTailRoosNullHomology_iff_riemannHypothesis :
    RouteRPrimeGammaXiGlobalDiagonalTailRoosNullHomology ↔ RiemannHypothesis := by
  constructor
  · intro hsource
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    apply (forall_ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_riemannHypothesis p).1
    intro rho
    exact ccmRationalAdelicPrimeXiSameFiberNormIdentity_of_tailRoosClass_eq_zero
      p rho (hsource rho)
  · intro hRH rho
    exact (routeRPrimeGammaXiDiagonalTailRoosClass_eq_zero_iff_re_eq_half rho).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
