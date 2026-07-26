import GaloisForLFunctions.RHTower.DeningerArithmeticTopologicalJetDual
import GaloisForLFunctions.RHTower.DeningerArithmeticRealStructure
import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.CompletedFluxGradedReality
import Mathlib.Topology.CompactOpen

/-!
# Deninger compact-open graded Real-jet universality

The algebraic functional-equation involution on Deninger's entire source is continuous for the
compact-open topology. It preserves the Xi differential range and therefore descends to a
continuous conjugate-linear involution on compact-open middle cohomology.

At the same time, every continuous point jet transforms by conjugating its base point, reflecting
it through the origin, and multiplying derivative degree `k` by `(-1)^k`. On the actual Xi
divisor, the transformed base point is exactly the centered coordinate of the conjugate zero.
Thus one Real involution controls the full infinite continuous jet tower with an exact graded
parity character.
-/

open Complex Filter Set TopologicalSpace Topology

namespace RHTower

noncomputable section

private def deningerNegConjContinuousMap : C(ℂ, ℂ) :=
  ⟨fun z => -(starRingEnd ℂ) z, Complex.continuous_conj.neg⟩

private def deningerConjContinuousMap : C(ℂ, ℂ) :=
  ⟨starRingEnd ℂ, Complex.continuous_conj⟩

/-- Functional-equation reflection as a continuous conjugate-linear compact-open source map. -/
def deningerCompactOpenFunctionalEquationSigma :
    DeningerCompactOpenEntire →L⋆[ℂ] DeningerCompactOpenEntire where
  toFun F :=
    deningerCompactOpenEntireEquiv.symm
      (deningerEntireFunctionalEquationSigma
        (deningerCompactOpenEntireEquiv F))
  map_add' F G := by
    apply deningerCompactOpenEntireEquiv.injective
    simp
  map_smul' c F := by
    apply deningerCompactOpenEntireEquiv.injective
    simp
  cont := by
    apply Continuous.subtype_mk
    change Continuous fun F : DeningerCompactOpenEntire =>
      deningerConjContinuousMap.comp
        ((F.1 : C(ℂ, ℂ)).comp deningerNegConjContinuousMap)
    exact
      (ContinuousMap.continuous_postcomp deningerConjContinuousMap).comp
        ((ContinuousMap.continuous_precomp deningerNegConjContinuousMap).comp
          continuous_subtype_val)

@[simp]
theorem deningerCompactOpenFunctionalEquationSigma_apply
    (F : DeningerCompactOpenEntire) (z : ℂ) :
    deningerCompactOpenFunctionalEquationSigma F z =
      (starRingEnd ℂ) (F (-(starRingEnd ℂ) z)) :=
  rfl

/-- Compact-open functional-equation reflection is involutive. -/
theorem deningerCompactOpenFunctionalEquationSigma_sq
    (F : DeningerCompactOpenEntire) :
    deningerCompactOpenFunctionalEquationSigma
        (deningerCompactOpenFunctionalEquationSigma F) = F := by
  apply deningerCompactOpenEntireEquiv.injective
  exact deningerEntireFunctionalEquationSigma_sq
    (deningerCompactOpenEntireEquiv F)

/-- Compact-open functional-equation reflection commutes with the Xi differential. -/
theorem deningerCompactOpenFunctionalEquationSigma_XiMul
    (F : DeningerCompactOpenEntire) :
    deningerCompactOpenFunctionalEquationSigma
        (deningerCompactOpenXiMul F) =
      deningerCompactOpenXiMul
        (deningerCompactOpenFunctionalEquationSigma F) := by
  apply deningerCompactOpenEntireEquiv.injective
  change deningerEntireFunctionalEquationSigma
      (deningerEntireXi * deningerCompactOpenEntireEquiv F) =
    deningerEntireXi *
      deningerEntireFunctionalEquationSigma
        (deningerCompactOpenEntireEquiv F)
  rw [deningerEntireFunctionalEquationSigma_mul,
    deningerEntireFunctionalEquationSigma_Xi]

/-- The compact-open Xi range is stable under functional-equation reflection. -/
theorem deningerCompactOpenFunctionalEquationSigma_mem_XiRange
    {F : DeningerCompactOpenEntire}
    (hF : F ∈ deningerCompactOpenXiRange) :
    deningerCompactOpenFunctionalEquationSigma F ∈
      deningerCompactOpenXiRange := by
  obtain ⟨G, rfl⟩ := hF
  refine ⟨deningerCompactOpenFunctionalEquationSigma G, ?_⟩
  exact (deningerCompactOpenFunctionalEquationSigma_XiMul G).symm

/-- Continuous even Real involution descended to compact-open middle cohomology. -/
def deningerArithmeticCompactOpenH1EvenSigma :
    DeningerArithmeticCompactOpenH1 →L⋆[ℂ]
      DeningerArithmeticCompactOpenH1 where
  toFun :=
    Quotient.map' deningerCompactOpenFunctionalEquationSigma
      (fun x y hxy => by
        have hrel :
            QuotientAddGroup.leftRel
              deningerCompactOpenXiRange.toAddSubgroup x y :=
          hxy
        apply QuotientAddGroup.leftRel_apply.mpr
        have hmem :=
          QuotientAddGroup.leftRel_apply.mp hrel
        change -x + y ∈ deningerCompactOpenXiRange at hmem
        change
          -deningerCompactOpenFunctionalEquationSigma x +
              deningerCompactOpenFunctionalEquationSigma y ∈
            deningerCompactOpenXiRange
        have himg :=
          deningerCompactOpenFunctionalEquationSigma_mem_XiRange hmem
        have heq :
            deningerCompactOpenFunctionalEquationSigma (-x + y) =
              -deningerCompactOpenFunctionalEquationSigma x +
                deningerCompactOpenFunctionalEquationSigma y := by
          ext z
          change
            (starRingEnd ℂ)
                ((-x + y) (-(starRingEnd ℂ) z)) =
              -(starRingEnd ℂ)
                  (x (-(starRingEnd ℂ) z)) +
                (starRingEnd ℂ)
                  (y (-(starRingEnd ℂ) z))
          simp
        rw [heq] at himg
        exact himg)
  map_add' := by
    rintro ⟨x⟩ ⟨y⟩
    change DeningerCompactOpenQuotient.mk deningerCompactOpenXiRange
        (deningerCompactOpenFunctionalEquationSigma (x + y)) =
      DeningerCompactOpenQuotient.mk deningerCompactOpenXiRange
          (deningerCompactOpenFunctionalEquationSigma x) +
        DeningerCompactOpenQuotient.mk deningerCompactOpenXiRange
          (deningerCompactOpenFunctionalEquationSigma y)
    rw [map_add, DeningerCompactOpenQuotient.mk_add]
  map_smul' := by
    rintro c ⟨x⟩
    change DeningerCompactOpenQuotient.mk deningerCompactOpenXiRange
        (deningerCompactOpenFunctionalEquationSigma (c • x)) =
      (starRingEnd ℂ) c •
        DeningerCompactOpenQuotient.mk deningerCompactOpenXiRange
          (deningerCompactOpenFunctionalEquationSigma x)
    rw [map_smulₛₗ, DeningerCompactOpenQuotient.mk_smul]
  cont :=
    continuous_quot_lift _
      (continuous_quot_mk.comp
        deningerCompactOpenFunctionalEquationSigma.continuous)

@[simp]
theorem deningerArithmeticCompactOpenH1EvenSigma_class
    (F : DeningerCompactOpenEntire) :
    deningerArithmeticCompactOpenH1EvenSigma
        (deningerArithmeticCompactOpenH1Class F) =
      deningerArithmeticCompactOpenH1Class
        (deningerCompactOpenFunctionalEquationSigma F) :=
  rfl

/-- The descended compact-open Real map remains an involution. -/
theorem deningerArithmeticCompactOpenH1EvenSigma_sq
    (x : DeningerArithmeticCompactOpenH1) :
    deningerArithmeticCompactOpenH1EvenSigma
        (deningerArithmeticCompactOpenH1EvenSigma x) = x := by
  refine Quotient.inductionOn x ?_
  intro F
  exact congrArg
    (DeningerCompactOpenQuotient.mk deningerCompactOpenXiRange)
    (deningerCompactOpenFunctionalEquationSigma_sq F)

/-- Every compact-open point jet obeys the all-order graded functional-equation law. -/
theorem deningerCompactOpenJet_functionalEquationSigma
    (F : DeningerCompactOpenEntire) (z : ℂ) (k : ℕ) :
    deningerCompactOpenJet z k
        (deningerCompactOpenFunctionalEquationSigma F) =
      (-1 : ℂ) ^ k *
        (starRingEnd ℂ) (deningerCompactOpenJet
          (-(starRingEnd ℂ) z) k F) := by
  change iteratedDeriv k
      ((starRingEnd ℂ) ∘
        (fun w : ℂ => F (-w)) ∘ (starRingEnd ℂ)) z =
    (-1 : ℂ) ^ k *
      (starRingEnd ℂ)
        (iteratedDeriv k (F : ℂ → ℂ)
          (-(starRingEnd ℂ) z))
  rw [iteratedDeriv_conj_conj]
  change
    (starRingEnd ℂ)
        (iteratedDeriv k (fun w : ℂ => F (-w))
          ((starRingEnd ℂ) z)) =
      (-1 : ℂ) ^ k *
        (starRingEnd ℂ)
          (iteratedDeriv k (F : ℂ → ℂ)
            (-(starRingEnd ℂ) z))
  rw [iteratedDeriv_comp_neg]
  simp only [smul_eq_mul, map_mul, map_pow, map_neg, map_one]

/-- Conjugating a Xi zero sends its centered coordinate to negative conjugation. -/
theorem xiSpectralPointSupport_zeroConj_for_compactOpen
    (rho : XiDivisorSupport) :
    xiSpectralPointSupport (xiZeroConjEquiv rho) =
      -(starRingEnd ℂ) (xiSpectralPointSupport rho) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one]
    simpa [one_div] using
      congrArg Inv.inv (map_ofNat (starRingEnd ℂ) 2)
  rw [xiSpectralPointSupport, xiSpectralPointSupport]
  change
    (((starRingEnd ℂ) (rho : ℂ)) - 1 / 2) * (-I) =
      -(starRingEnd ℂ) (((rho : ℂ) - 1 / 2) * (-I))
  simp only [map_mul, map_sub, map_neg, hhalf, conj_I]
  ring

/-- On Xi support, the all-order graded Real law reindexes through the conjugate zero. -/
theorem deningerCompactOpenXiJet_functionalEquationSigma
    (F : DeningerCompactOpenEntire) (rho : XiDivisorSupport) (k : ℕ) :
    deningerCompactOpenJet (xiSpectralPointSupport rho) k
        (deningerCompactOpenFunctionalEquationSigma F) =
      (-1 : ℂ) ^ k *
        (starRingEnd ℂ)
          (deningerCompactOpenJet
            (xiSpectralPointSupport (xiZeroConjEquiv rho)) k F) := by
  rw [deningerCompactOpenJet_functionalEquationSigma,
    xiSpectralPointSupport_zeroConj_for_compactOpen]

/--
**Deninger compact-open graded Real-jet universality.**

One continuous involution preserves the Xi differential, descends to topological cohomology, and
acts on every derivative order over every Xi divisor point by conjugate-zero reindexing and the
exact parity character `(-1)^k`.
-/
theorem deninger_compactOpen_gradedRealJetUniversality :
    (∀ F : DeningerCompactOpenEntire,
      deningerCompactOpenFunctionalEquationSigma
          (deningerCompactOpenFunctionalEquationSigma F) = F) ∧
    (∀ F : DeningerCompactOpenEntire,
      deningerCompactOpenFunctionalEquationSigma
          (deningerCompactOpenXiMul F) =
        deningerCompactOpenXiMul
          (deningerCompactOpenFunctionalEquationSigma F)) ∧
    (∀ x : DeningerArithmeticCompactOpenH1,
      deningerArithmeticCompactOpenH1EvenSigma
          (deningerArithmeticCompactOpenH1EvenSigma x) = x) ∧
    (∀ (F : DeningerCompactOpenEntire)
        (rho : XiDivisorSupport) (k : ℕ),
      deningerCompactOpenJet (xiSpectralPointSupport rho) k
          (deningerCompactOpenFunctionalEquationSigma F) =
        (-1 : ℂ) ^ k *
          (starRingEnd ℂ)
            (deningerCompactOpenJet
              (xiSpectralPointSupport (xiZeroConjEquiv rho)) k F)) := by
  exact ⟨deningerCompactOpenFunctionalEquationSigma_sq,
    deningerCompactOpenFunctionalEquationSigma_XiMul,
    deningerArithmeticCompactOpenH1EvenSigma_sq,
    deningerCompactOpenXiJet_functionalEquationSigma⟩

end

end RHTower
