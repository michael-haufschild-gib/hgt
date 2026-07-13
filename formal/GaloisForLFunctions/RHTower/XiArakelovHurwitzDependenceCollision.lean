import GaloisForLFunctions.RHTower.XiArakelovHurwitzAlgebraicityCollision
import GaloisForLFunctions.Hurwitz.IntegerTranslationDifferentialMatroid

/-!
# Hurwitz value relations feed the Arakelov algebraicity collision

For two nonintegral exponents, the intrinsic continued-Hurwitz differential matroid says that the
two functions are differentially dependent exactly when their monodromy characters agree.

Consequently, differential dependence of the Xi-indexed Hurwitz function with any nonintegral
anchor carrying an algebraic monodromy character transfers algebraicity to the Xi character.  If
the same hypothetical right-half Xi zero has algebraic Arakelov coordinate, the already formalized
Arakelov--Hurwitz Gelfond--Schneider collision forces RH.

The anchor may vary with the divisor point and need not lie on the critical line.  This module thus
isolates an actual function-value relation as a producer for one arithmetic input, rather than
assuming the Xi character algebraic without a mechanism.
-/

open Complex Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit

/-- The two-exponent family used by the intrinsic continued-Hurwitz differential matroid. -/
def continuedHurwitzPairExponent (s t : ℂ) : Bool → ℂ :=
  fun b => if b then t else s

/-- A genuine algebraic differential relation between the two analytically continued Hurwitz
functions in the shift variable. -/
def ContinuedHurwitzPairDifferentiallyDependent (s t : ℂ) : Prop :=
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  ¬ DifferentialIndependent (RatFunc ℂ)
    (fun b : Bool => continuedHzetaUpperEndMero (continuedHurwitzPairExponent s t b))

/-- Differential dependence of two nonintegral continued-Hurwitz functions forces equality of
their monodromy characters. -/
theorem monoScalar_eq_of_continuedHurwitzPairDifferentiallyDependent
    {s t : ℂ}
    (hs : ∀ m : ℤ, s ≠ (m : ℂ))
    (ht : ∀ m : ℤ, t ≠ (m : ℂ))
    (hdep : ContinuedHurwitzPairDifferentiallyDependent s t) :
    monoScalar s = monoScalar t := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  by_contra hne
  apply hdep
  apply (continued_hurwitz_intrinsic_residue_differentialMatroid_law
    (continuedHurwitzPairExponent s t) ?_).mpr
  · intro b₁ b₂ hq
    cases b₁ <;> cases b₂ <;> simp_all [continuedHurwitzPairExponent]
  · intro b m
    cases b <;> simp [continuedHurwitzPairExponent, hs, ht]

/-- Exact two-point value law: continued-Hurwitz differential dependence is equality of the two
monodromy-character values. -/
theorem continuedHurwitzPairDifferentiallyDependent_iff_monoScalar_eq
    {s t : ℂ}
    (hs : ∀ m : ℤ, s ≠ (m : ℂ))
    (ht : ∀ m : ℤ, t ≠ (m : ℂ)) :
    ContinuedHurwitzPairDifferentiallyDependent s t ↔
      monoScalar s = monoScalar t := by
  constructor
  · exact monoScalar_eq_of_continuedHurwitzPairDifferentiallyDependent hs ht
  · intro hq
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
    letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    intro hDI
    have hinj := (continued_hurwitz_intrinsic_residue_differentialMatroid_law
      (continuedHurwitzPairExponent s t) (by
        intro b m
        cases b <;> simp [continuedHurwitzPairExponent, hs, ht])).mp hDI
    have hfalseTrue : (false : Bool) = true := by
      apply hinj
      simpa [continuedHurwitzPairExponent] using hq
    simp at hfalseTrue

/-- Source-value hypothesis: every hypothetical right-half Xi zero has algebraic Arakelov
coordinate and its continued-Hurwitz function is differentially dependent with some nonintegral
anchor whose monodromy character is algebraic. -/
def XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter : Prop :=
  ∀ rho : XiDivisorSupport, 1 / 2 < (rho : ℂ).re →
    IsAlgebraic ℚ (arakelovW (rho : ℂ)) ∧
      ∃ tau : ℂ,
        (∀ m : ℤ, tau ≠ (m : ℂ)) ∧
        IsAlgebraic ℚ (monoScalar tau) ∧
        ContinuedHurwitzPairDifferentiallyDependent (rho : ℂ) tau

/-- The Hurwitz value relation transfers the anchor's algebraic character to the Xi divisor
point, discharging the character-algebraicity input of the arithmetic collision. -/
theorem xiRightArakelovHurwitzAlgebraic_of_dependentOnAlgebraicCharacter
    (h : XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter) :
    XiRightArakelovHurwitzAlgebraic := by
  intro rho hrho
  obtain ⟨hw, tau, htau, hqtau, hdep⟩ := h rho hrho
  refine ⟨hw, ?_⟩
  have hqrho : monoScalar (rho : ℂ) = monoScalar tau :=
    monoScalar_eq_of_continuedHurwitzPairDifferentiallyDependent
      (fun m => openCriticalStrip_point_ne_int
        (xi_divisor_support_re_mem_open_unit rho) m)
      htau hdep
  rw [xiHurwitzMonodromyCharacter, hqrho]
  exact hqtau

/-- **Value-relation chain to RH.** Algebraic Arakelov coordinates plus differential dependence
with algebraic-character Hurwitz anchors force RH. -/
theorem riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter
    (h : XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiRightArakelovHurwitzAlgebraic
    (xiRightArakelovHurwitzAlgebraic_of_dependentOnAlgebraicCharacter h)

/-- Add one exponent to a finite Hurwitz anchor family. -/
def continuedHurwitzAugmentedExponent {I : Type*}
    (s : ℂ) (anchor : I → ℂ) : Option I → ℂ
  | none => s
  | some i => anchor i

/-- The Hurwitz function at `s` lies in the differential-matroid closure of a finite anchor
family when adjoining it destroys differential independence. -/
def ContinuedHurwitzDifferentiallyDependentOverAnchors
    {I : Type*} [Fintype I] [DecidableEq I]
    (s : ℂ) (anchor : I → ℂ) : Prop :=
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  ¬ DifferentialIndependent (RatFunc ℂ)
    (fun o : Option I =>
      continuedHzetaUpperEndMero (continuedHurwitzAugmentedExponent s anchor o))

/-- If a nonintegral Hurwitz exponent lies in the differential-matroid closure of a finite
monodromy-separated anchor family, its character equals one of the anchor characters. -/
theorem exists_anchor_monoScalar_eq_of_continuedHurwitzDependentOverAnchors
    {I : Type*} [Fintype I] [DecidableEq I]
    {s : ℂ} {anchor : I → ℂ}
    (hs : ∀ m : ℤ, s ≠ (m : ℂ))
    (hanchor : ∀ i m, anchor i ≠ (m : ℂ))
    (hinj : Function.Injective (fun i => monoScalar (anchor i)))
    (hdep : ContinuedHurwitzDifferentiallyDependentOverAnchors s anchor) :
    ∃ i, monoScalar s = monoScalar (anchor i) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  by_contra hnone
  simp only [not_exists] at hnone
  apply hdep
  apply (continued_hurwitz_intrinsic_residue_differentialMatroid_law
    (continuedHurwitzAugmentedExponent s anchor) ?_).mpr
  · intro o₁ o₂ heq
    cases o₁ with
    | none =>
        cases o₂ with
        | none => rfl
        | some j => exact (hnone j heq).elim
    | some i =>
        cases o₂ with
        | none => exact (hnone i heq.symm).elim
        | some j => exact congrArg some (hinj heq)
  · intro o m
    cases o with
    | none => exact hs m
    | some i => exact hanchor i m

/-- A finite differential-matroid closure relation over algebraic-character anchors transfers
algebraicity to the captured monodromy character. -/
theorem monoScalar_isAlgebraic_of_continuedHurwitzDependentOverAlgebraicAnchors
    {I : Type*} [Fintype I] [DecidableEq I]
    {s : ℂ} {anchor : I → ℂ}
    (hs : ∀ m : ℤ, s ≠ (m : ℂ))
    (hanchor : ∀ i m, anchor i ≠ (m : ℂ))
    (hinj : Function.Injective (fun i => monoScalar (anchor i)))
    (halg : ∀ i, IsAlgebraic ℚ (monoScalar (anchor i)))
    (hdep : ContinuedHurwitzDifferentiallyDependentOverAnchors s anchor) :
    IsAlgebraic ℚ (monoScalar s) := by
  obtain ⟨i, hi⟩ :=
    exists_anchor_monoScalar_eq_of_continuedHurwitzDependentOverAnchors
      hs hanchor hinj hdep
  rw [hi]
  exact halg i

/-- **Finite-anchor value-relation chain to RH.** If every hypothetical right-half Xi-indexed
Hurwitz function lies in the differential-matroid closure of one finite algebraic-character anchor
family, and its Arakelov coordinate is algebraic, then RH follows. -/
theorem riemannHypothesis_of_xiRightArakelovAlgebraic_of_finiteHurwitzAnchorCapture
    {I : Type*} [Fintype I] [DecidableEq I]
    (anchor : I → ℂ)
    (hanchor : ∀ i m, anchor i ≠ (m : ℂ))
    (hinj : Function.Injective (fun i => monoScalar (anchor i)))
    (halg : ∀ i, IsAlgebraic ℚ (monoScalar (anchor i)))
    (hcapture : ∀ rho : XiDivisorSupport, 1 / 2 < (rho : ℂ).re →
      IsAlgebraic ℚ (arakelovW (rho : ℂ)) ∧
        ContinuedHurwitzDifferentiallyDependentOverAnchors (rho : ℂ) anchor) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiRightArakelovHurwitzAlgebraic
  intro rho hrho
  obtain ⟨hw, hdep⟩ := hcapture rho hrho
  refine ⟨hw, ?_⟩
  rw [xiHurwitzMonodromyCharacter]
  exact monoScalar_isAlgebraic_of_continuedHurwitzDependentOverAlgebraicAnchors
    (fun m => openCriticalStrip_point_ne_int
      (xi_divisor_support_re_mem_open_unit rho) m)
    hanchor hinj halg hdep

end

end RHTower
