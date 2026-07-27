import GaloisForLFunctions.RHTower.KRealKernelCokernel

/-!
# Paugam sign--conjugation as an odd `K_R` object

Paugam splits the nonreal spectral suspension into upper and lower
imaginary parts.  Complex conjugation exchanges the two halves.  Multiplying
conjugation by `+1` on one half and `-1` on the other produces an
anti-linear operator whose square is `-1`.

This file formalizes that algebra without a zero set, positivity premise,
or Riemann hypothesis.  Positivity of the resulting cup--Hodge form is
deliberately not asserted.
-/

open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

variable {Vplus Vminus : Type*}
variable [AddCommGroup Vplus] [Module ℂ Vplus]
variable [AddCommGroup Vminus] [Module ℂ Vminus]

/--
Abstract upper/lower spectral decomposition with anti-linear conjugation
exchanging the two halves.
-/
structure PaugamSpectralExchange where
  plusToMinus : Vplus →ₗ⋆[ℂ] Vminus
  minusToPlus : Vminus →ₗ⋆[ℂ] Vplus
  minus_plus : ∀ x, minusToPlus (plusToMinus x) = x
  plus_minus : ∀ y, plusToMinus (minusToPlus y) = y

namespace PaugamSpectralExchange

/--
Paugam's operator `C = diag(1,-1) c` on the upper/lower product.
-/
def signConjugationSigma
    (E : PaugamSpectralExchange (Vplus := Vplus) (Vminus := Vminus)) :
    (Vplus × Vminus) →ₗ⋆[ℂ] (Vplus × Vminus) where
  toFun x := (E.minusToPlus x.2, -E.plusToMinus x.1)
  map_add' x y := by
    apply Prod.ext
    · simp
    · simp
      abel
  map_smul' c x := by
    ext <;> simp

@[simp]
theorem signConjugationSigma_apply
    (E : PaugamSpectralExchange (Vplus := Vplus) (Vminus := Vminus))
    (x : Vplus × Vminus) :
    E.signConjugationSigma x =
      (E.minusToPlus x.2, -E.plusToMinus x.1) :=
  rfl

/-- The sign--conjugation operator is genuinely quaternionic. -/
theorem signConjugationSigma_sq
    (E : PaugamSpectralExchange (Vplus := Vplus) (Vminus := Vminus))
    (x : Vplus × Vminus) :
    E.signConjugationSigma (E.signConjugationSigma x) = -x := by
  apply Prod.ext
  · simp [E.minus_plus]
  · simp [E.plus_minus]

/-- The upper/lower spectral product is an odd object of Deninger's `K_R`. -/
def kReal
    (E : PaugamSpectralExchange (Vplus := Vplus) (Vminus := Vminus)) :
    KRealStructure true (Vplus × Vminus) where
  sigma := E.signConjugationSigma
  sq x := by
    rw [E.signConjugationSigma_sq]
    rfl

/-- Componentwise infinitesimal flow on the upper/lower product. -/
def splitEnd
    (thetaPlus : Module.End ℂ Vplus)
    (thetaMinus : Module.End ℂ Vminus) :
    Module.End ℂ (Vplus × Vminus) where
  toFun x := (thetaPlus x.1, thetaMinus x.2)
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp

@[simp]
theorem splitEnd_apply
    (thetaPlus : Module.End ℂ Vplus)
    (thetaMinus : Module.End ℂ Vminus)
    (x : Vplus × Vminus) :
    splitEnd thetaPlus thetaMinus x =
      (thetaPlus x.1, thetaMinus x.2) :=
  rfl

/--
If conjugation exchanges the upper and lower flow restrictions, Paugam's
odd structure commutes with the infinitesimal flow.
-/
theorem signConjugationSigma_commutes_splitEnd
    (E : PaugamSpectralExchange (Vplus := Vplus) (Vminus := Vminus))
    (thetaPlus : Module.End ℂ Vplus)
    (thetaMinus : Module.End ℂ Vminus)
    (hPlus :
      ∀ x, E.plusToMinus (thetaPlus x) =
        thetaMinus (E.plusToMinus x))
    (hMinus :
      ∀ y, E.minusToPlus (thetaMinus y) =
        thetaPlus (E.minusToPlus y))
    (x : Vplus × Vminus) :
    E.signConjugationSigma (splitEnd thetaPlus thetaMinus x) =
      splitEnd thetaPlus thetaMinus (E.signConjugationSigma x) := by
  apply Prod.ext
  · exact hMinus x.2
  · simp [hPlus]

/--
Alternating form induced by a bilinear upper-to-lower duality.
-/
def splitPairing
    (B : Vplus →ₗ[ℂ] Vminus →ₗ[ℂ] ℂ) :
    LinearMap.BilinForm ℂ (Vplus × Vminus) where
  toFun x :=
    { toFun := fun y => B x.1 y.2 - B y.1 x.2
      map_add' := by
        intro y z
        simp
        ring
      map_smul' := by
        intro c y
        simp
        ring }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp
    ring
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    simp
    ring

@[simp]
theorem splitPairing_apply
    (B : Vplus →ₗ[ℂ] Vminus →ₗ[ℂ] ℂ)
    (x y : Vplus × Vminus) :
    splitPairing B x y = B x.1 y.2 - B y.1 x.2 :=
  rfl

theorem splitPairing_skew
    (B : Vplus →ₗ[ℂ] Vminus →ₗ[ℂ] ℂ)
    (x y : Vplus × Vminus) :
    splitPairing B x y = -splitPairing B y x := by
  simp

theorem splitPairing_isAlt
    (B : Vplus →ₗ[ℂ] Vminus →ₗ[ℂ] ℂ) :
    (splitPairing B).IsAlt := by
  intro x
  simp

/-- Exact diagonal of Paugam's cup form followed by sign--conjugation. -/
theorem splitPairing_signConjugation_self
    (E : PaugamSpectralExchange (Vplus := Vplus) (Vminus := Vminus))
    (B : Vplus →ₗ[ℂ] Vminus →ₗ[ℂ] ℂ)
    (x : Vplus × Vminus) :
    splitPairing B x (E.signConjugationSigma x) =
      -B x.1 (E.plusToMinus x.1) -
        B (E.minusToPlus x.2) x.2 := by
  simp [splitPairing, signConjugationSigma]

/--
The cross-pairing weight-one law implies Deninger's weight-one law on
the full upper/lower alternating form.
-/
theorem splitPairing_weightOne
    (B : Vplus →ₗ[ℂ] Vminus →ₗ[ℂ] ℂ)
    (thetaPlus : Module.End ℂ Vplus)
    (thetaMinus : Module.End ℂ Vminus)
    (hB :
      ∀ x y,
        B (thetaPlus x) y + B x (thetaMinus y) = B x y)
    (x y : Vplus × Vminus) :
    splitPairing B (splitEnd thetaPlus thetaMinus x) y +
    splitPairing B x (splitEnd thetaPlus thetaMinus y) =
      splitPairing B x y := by
  simp only [splitPairing_apply, splitEnd_apply]
  linear_combination hB x.1 y.2 - hB y.1 x.2

section Cokernel

variable {Uplus Uminus : Type*}
variable [AddCommGroup Uplus] [Module ℂ Uplus]
variable [AddCommGroup Uminus] [Module ℂ Uminus]

/-- Componentwise map between upper/lower spectral products. -/
def splitLinearMap
    (fPlus : Uplus →ₗ[ℂ] Vplus)
    (fMinus : Uminus →ₗ[ℂ] Vminus) :
    (Uplus × Uminus) →ₗ[ℂ] (Vplus × Vminus) where
  toFun x := (fPlus x.1, fMinus x.2)
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp

@[simp]
theorem splitLinearMap_apply
    (fPlus : Uplus →ₗ[ℂ] Vplus)
    (fMinus : Uminus →ₗ[ℂ] Vminus)
    (x : Uplus × Uminus) :
    splitLinearMap fPlus fMinus x = (fPlus x.1, fMinus x.2) :=
  rfl

/-- A split map intertwining conjugation is a morphism of odd `K_R` objects. -/
def splitKRealMorphism
    (EU : PaugamSpectralExchange (Vplus := Uplus) (Vminus := Uminus))
    (EV : PaugamSpectralExchange (Vplus := Vplus) (Vminus := Vminus))
    (fPlus : Uplus →ₗ[ℂ] Vplus)
    (fMinus : Uminus →ₗ[ℂ] Vminus)
    (hPlus : ∀ x,
      EV.plusToMinus (fPlus x) = fMinus (EU.plusToMinus x))
    (hMinus : ∀ y,
      EV.minusToPlus (fMinus y) = fPlus (EU.minusToPlus y)) :
    KRealMorphism EU.kReal EV.kReal where
  map := splitLinearMap fPlus fMinus
  commutes x := by
    apply Prod.ext
    · exact hMinus x.2
    · simpa [kReal, signConjugationSigma, splitLinearMap] using
        congrArg Neg.neg (hPlus x.1)

/-- The algebraic cokernel of an equivariant split Poisson map is odd in `K_R`. -/
def cokernelKReal
    (EU : PaugamSpectralExchange (Vplus := Uplus) (Vminus := Uminus))
    (EV : PaugamSpectralExchange (Vplus := Vplus) (Vminus := Vminus))
    (fPlus : Uplus →ₗ[ℂ] Vplus)
    (fMinus : Uminus →ₗ[ℂ] Vminus)
    (hPlus : ∀ x,
      EV.plusToMinus (fPlus x) = fMinus (EU.plusToMinus x))
    (hMinus : ∀ y,
      EV.minusToPlus (fMinus y) = fPlus (EU.minusToPlus y)) :
    KRealStructure true
      ((Vplus × Vminus) ⧸ LinearMap.range (splitLinearMap fPlus fMinus)) :=
  KRealStructure.cokernel EU.kReal EV.kReal
    (splitKRealMorphism EU EV fPlus fMinus hPlus hMinus)

@[simp]
theorem cokernelKReal_sigma_mkQ
    (EU : PaugamSpectralExchange (Vplus := Uplus) (Vminus := Uminus))
    (EV : PaugamSpectralExchange (Vplus := Vplus) (Vminus := Vminus))
    (fPlus : Uplus →ₗ[ℂ] Vplus)
    (fMinus : Uminus →ₗ[ℂ] Vminus)
    (hPlus : ∀ x,
      EV.plusToMinus (fPlus x) = fMinus (EU.plusToMinus x))
    (hMinus : ∀ y,
      EV.minusToPlus (fMinus y) = fPlus (EU.minusToPlus y))
    (v : Vplus × Vminus) :
    (cokernelKReal EU EV fPlus fMinus hPlus hMinus).sigma
        ((LinearMap.range (splitLinearMap fPlus fMinus)).mkQ v) =
      (LinearMap.range (splitLinearMap fPlus fMinus)).mkQ
        (EV.signConjugationSigma v) := by
  rfl

end Cokernel

end PaugamSpectralExchange

end

end RHTower
