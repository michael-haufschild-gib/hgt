import GaloisForLFunctions.HTGeometry.AffineFirstOrderDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.EllipticGammaPairedIncrement

/-!
# Differential algebraicity along translation-defect spans

These laws propagate differential algebraicity over the paired elliptic compositum from every
translate of one additive defect to integer multiples and finite sums of shift parameters.  The
hypotheses are translation-uniform, so no false coefficient-fixing assumption is made.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

local instance translationDefectDADomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance translationDefectDAComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance translationDefectDAComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  meromorphicEllipticCompositumComplexAlgebraMero

local instance translationDefectDAAmbientDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance translationDefectDAMeroCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField Set.univ)).injective

local instance translationDefectDARestrictedDifferential (sigma tau : ℂ) :
    Differential (meromorphicEllipticCompositum sigma tau) :=
  meromorphicEllipticCompositumDifferential sigma tau

local instance translationDefectDADifferentialAlgebra (sigma tau : ℂ) :
    DifferentialAlgebra (meromorphicEllipticCompositum sigma tau)
      (meroField Set.univ) :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    (meromorphicEllipticCompositum sigma tau)
    (meromorphicEllipticCompositum_derivationClosed sigma tau) x⟩

/-- The difference of two translation defects is the translate of the defect at the parameter
difference. -/
theorem addTranslationMeroEquiv_defect_sub (h k : ℂ)
    (x : meroField Set.univ) :
    (addTranslationMeroEquiv h x - x) -
        (addTranslationMeroEquiv k x - x) =
      addTranslationMeroEquiv k (addTranslationMeroEquiv (h - k) x - x) := by
  rw [(addTranslationMeroEquiv k).map_sub, addTranslationMeroEquiv_add]
  rw [show k + (h - k) = h by ring]
  ring

/-- If every translate of one generator defect is DA over the paired elliptic base, the same is
true for every translate of each natural multiple of that generator. -/
theorem differentialAlgebraicOver_addTranslationMeroEquiv_defect_nsmul
    (sigma tau : ℂ) (x : meroField Set.univ) (g : ℂ)
    (hgen : ∀ q : ℂ,
      DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
        (addTranslationMeroEquiv q (addTranslationMeroEquiv g x - x)))
    (q : ℂ) : ∀ n : ℕ,
      DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
        (addTranslationMeroEquiv q (addTranslationMeroEquiv (n • g) x - x)) := by
  intro n
  induction n with
  | zero =>
      rw [zero_nsmul, addTranslationMeroEquiv_zero_apply, sub_self, map_zero]
      exact differentialAlgebraicOver_algebraMap 0
  | succ n ih =>
      have heq :
          addTranslationMeroEquiv q
              (addTranslationMeroEquiv ((n + 1) • g) x - x) =
            addTranslationMeroEquiv q
                (addTranslationMeroEquiv (n • g) x - x) +
              addTranslationMeroEquiv (q + n • g)
                (addTranslationMeroEquiv g x - x) := by
        rw [add_nsmul, one_nsmul, addTranslationMeroEquiv_defect_add,
          (addTranslationMeroEquiv q).map_add, addTranslationMeroEquiv_add]
      rw [heq]
      exact differentialAlgebraicOver_add ih (hgen _)

/-- **Integer-span defect law.**  DA of all translates of one generator defect propagates to all
translated integer multiples, with negative multiples supplied by exact value reflection. -/
theorem differentialAlgebraicOver_addTranslationMeroEquiv_defect_zsmul
    (sigma tau : ℂ) (x : meroField Set.univ) (g : ℂ)
    (hgen : ∀ q : ℂ,
      DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
        (addTranslationMeroEquiv q (addTranslationMeroEquiv g x - x)))
    (q : ℂ) (n : ℤ) :
      DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
        (addTranslationMeroEquiv q (addTranslationMeroEquiv (n • g) x - x)) := by
  cases n with
  | ofNat n =>
      simpa using differentialAlgebraicOver_addTranslationMeroEquiv_defect_nsmul
        sigma tau x g hgen q n
  | negSucc n =>
      let p : ℂ := (n + 1) • g
      have hpos := differentialAlgebraicOver_addTranslationMeroEquiv_defect_nsmul
        sigma tau x g hgen (q - p) (n + 1)
      have heq :
          addTranslationMeroEquiv q
              (addTranslationMeroEquiv (-(p : ℂ)) x - x) =
            -addTranslationMeroEquiv (q - p)
              (addTranslationMeroEquiv p x - x) := by
        rw [addTranslationMeroEquiv_defect_neg,
          (addTranslationMeroEquiv q).map_neg,
          addTranslationMeroEquiv_add]
        congr 2
      rw [show Int.negSucc n • g = -p by
        simp [p]
        ring]
      rw [heq]
      exact differentialAlgebraicOver_neg hpos

/-- Translated DA defect families over the paired elliptic base are closed under addition of their
shift parameters. -/
theorem differentialAlgebraicOver_addTranslationMeroEquiv_defect_add
    (sigma tau : ℂ) (x : meroField Set.univ) (h k : ℂ)
    (hh : ∀ q : ℂ,
      DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
        (addTranslationMeroEquiv q (addTranslationMeroEquiv h x - x)))
    (hk : ∀ q : ℂ,
      DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
        (addTranslationMeroEquiv q (addTranslationMeroEquiv k x - x)))
    (q : ℂ) : DifferentialAlgebraicOver (meromorphicEllipticCompositum sigma tau)
      (addTranslationMeroEquiv q (addTranslationMeroEquiv (h + k) x - x)) := by
  have heq :
      addTranslationMeroEquiv q (addTranslationMeroEquiv (h + k) x - x) =
        addTranslationMeroEquiv q (addTranslationMeroEquiv h x - x) +
          addTranslationMeroEquiv (q + h)
            (addTranslationMeroEquiv k x - x) := by
    rw [addTranslationMeroEquiv_defect_add,
      (addTranslationMeroEquiv q).map_add,
      addTranslationMeroEquiv_add]
  rw [heq]
  exact differentialAlgebraicOver_add (hh q) (hk (q + h))

end


end GaloisForLFunctions
