import GaloisForLFunctions.RHTower.DeningerPrimeGammaReflectedDiagonal

/-!
# Poincare duality on prime--Gamma packet cohomology

The lower and upper source packet spaces were quotiented by the exact left and right radicals of
their arithmetic pairing.  This file performs the universal quotient descent.  The resulting
pairing is separating on both quotient sectors by construction.  Their direct sum carries the
canonical alternating degree-one cup form

`ω((x₋,x₊),(y₋,y₊)) = B(x₋,y₊) - B(y₋,x₊)`,

and Lean proves this form nondegenerate.  This is source-defined algebraic Poincare duality; no
Hilbert topology, Hodge star, positivity, or RH is used.
-/

namespace RHTower

noncomputable section

/-- Pairing with a fixed upper packet, as a linear functional on lower packets. -/
def deningerPrimeGammaSourceCupRightLinear
    (y : DeningerPrimeGammaUpperPacket) :
    DeningerPrimeGammaLowerPacket →ₗ[ℂ] ℂ where
  toFun x := deningerPrimeGammaSourceCup x y
  map_add' x₁ x₂ := by simp
  map_smul' a x := by simp

/-- Descend the lower variable through its exact left radical. -/
def deningerPrimeGammaSourceCupOnH1Minus
    (y : DeningerPrimeGammaUpperPacket) :
    DeningerPrimeGammaH1Minus →ₗ[ℂ] ℂ :=
  deningerPrimeGammaLeftRadical.liftQ
    (deningerPrimeGammaSourceCupRightLinear y) (by
      intro x hx
      change deningerPrimeGammaSourceCup x y = 0
      exact (mem_deningerPrimeGammaLeftRadical_iff x).1 hx y)

@[simp]
theorem deningerPrimeGammaSourceCupOnH1Minus_mkQ
    (x : DeningerPrimeGammaLowerPacket)
    (y : DeningerPrimeGammaUpperPacket) :
    deningerPrimeGammaSourceCupOnH1Minus y
        (deningerPrimeGammaH1MinusClass x) =
      deningerPrimeGammaSourceCup x y := by
  exact LinearMap.congr_fun
    (Submodule.liftQ_mkQ deningerPrimeGammaLeftRadical
      (deningerPrimeGammaSourceCupRightLinear y) (by
        intro u hu
        change deningerPrimeGammaSourceCup u y = 0
        exact (mem_deningerPrimeGammaLeftRadical_iff u).1 hu y))
    x

/-- The upper packet maps linearly to the dual of the lower quotient. -/
def deningerPrimeGammaUpperToH1MinusDual :
    DeningerPrimeGammaUpperPacket →ₗ[ℂ]
      (DeningerPrimeGammaH1Minus →ₗ[ℂ] ℂ) where
  toFun y := deningerPrimeGammaSourceCupOnH1Minus y
  map_add' y₁ y₂ := by
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := deningerPrimeGammaLeftRadical.mkQ_surjective q
    change
      deningerPrimeGammaSourceCup x (y₁ + y₂) =
        deningerPrimeGammaSourceCup x y₁ +
          deningerPrimeGammaSourceCup x y₂
    simp
  map_smul' a y := by
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := deningerPrimeGammaLeftRadical.mkQ_surjective q
    change
      deningerPrimeGammaSourceCup x (a • y) =
        a • deningerPrimeGammaSourceCup x y
    simp

theorem ker_deningerPrimeGammaUpperToH1MinusDual :
    LinearMap.ker deningerPrimeGammaUpperToH1MinusDual =
      deningerPrimeGammaRightRadical := by
  ext y
  rw [LinearMap.mem_ker, mem_deningerPrimeGammaRightRadical_iff]
  constructor
  · intro hy x
    have h := LinearMap.congr_fun hy (deningerPrimeGammaH1MinusClass x)
    simpa using h
  · intro hy
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := deningerPrimeGammaLeftRadical.mkQ_surjective q
    simpa using hy x

/-- Perfect source pairing as an injective map from the upper quotient to the lower dual. -/
def deningerPrimeGammaH1PlusToH1MinusDual :
    DeningerPrimeGammaH1Plus →ₗ[ℂ]
      (DeningerPrimeGammaH1Minus →ₗ[ℂ] ℂ) :=
  deningerPrimeGammaRightRadical.liftQ
    deningerPrimeGammaUpperToH1MinusDual (by
      rw [← ker_deningerPrimeGammaUpperToH1MinusDual])

/-- Descended source Poincare pairing between the two degree-one sectors. -/
def deningerPrimeGammaPoincarePairing
    (x : DeningerPrimeGammaH1Minus)
    (y : DeningerPrimeGammaH1Plus) : ℂ :=
  deningerPrimeGammaH1PlusToH1MinusDual y x

@[simp]
theorem deningerPrimeGammaPoincarePairing_mkQ
    (x : DeningerPrimeGammaLowerPacket)
    (y : DeningerPrimeGammaUpperPacket) :
    deningerPrimeGammaPoincarePairing
        (deningerPrimeGammaH1MinusClass x)
        (deningerPrimeGammaH1PlusClass y) =
      deningerPrimeGammaSourceCup x y := by
  change
    deningerPrimeGammaH1PlusToH1MinusDual
        (deningerPrimeGammaRightRadical.mkQ y)
        (deningerPrimeGammaLeftRadical.mkQ x) =
      deningerPrimeGammaSourceCup x y
  have hright := LinearMap.congr_fun
    (Submodule.liftQ_mkQ deningerPrimeGammaRightRadical
      deningerPrimeGammaUpperToH1MinusDual (by
        rw [← ker_deningerPrimeGammaUpperToH1MinusDual]))
    y
  rw [show deningerPrimeGammaH1PlusToH1MinusDual
      (deningerPrimeGammaRightRadical.mkQ y) =
        deningerPrimeGammaUpperToH1MinusDual y by
      exact hright]
  exact deningerPrimeGammaSourceCupOnH1Minus_mkQ x y

theorem deningerPrimeGammaPoincarePairing_separatingLeft
    {x : DeningerPrimeGammaH1Minus}
    (hx : ∀ y, deningerPrimeGammaPoincarePairing x y = 0) :
    x = 0 := by
  obtain ⟨x, rfl⟩ := deningerPrimeGammaLeftRadical.mkQ_surjective x
  apply (Submodule.Quotient.mk_eq_zero deningerPrimeGammaLeftRadical).2
  apply (mem_deningerPrimeGammaLeftRadical_iff x).2
  intro y
  have h := hx (deningerPrimeGammaH1PlusClass y)
  simpa using h

theorem deningerPrimeGammaPoincarePairing_separatingRight
    {y : DeningerPrimeGammaH1Plus}
    (hy : ∀ x, deningerPrimeGammaPoincarePairing x y = 0) :
    y = 0 := by
  obtain ⟨y, rfl⟩ := deningerPrimeGammaRightRadical.mkQ_surjective y
  apply (Submodule.Quotient.mk_eq_zero deningerPrimeGammaRightRadical).2
  apply (mem_deningerPrimeGammaRightRadical_iff y).2
  intro x
  have h := hy (deningerPrimeGammaH1MinusClass x)
  simpa using h

/-- Algebraic degree-one source cohomology before topological completion. -/
abbrev DeningerPrimeGammaH1 :=
  DeningerPrimeGammaH1Minus × DeningerPrimeGammaH1Plus

/-- Alternating degree-one cup product followed by the endpoint trace. -/
def deningerPrimeGammaH1CupTrace :
    LinearMap.BilinForm ℂ DeningerPrimeGammaH1 :=
  LinearMap.mk₂ ℂ
    (fun x y =>
      deningerPrimeGammaPoincarePairing x.1 y.2 -
        deningerPrimeGammaPoincarePairing y.1 x.2)
    (by
      intro x x' y
      obtain ⟨yneg, ypos⟩ := y
      simp [deningerPrimeGammaPoincarePairing]
      ring)
    (by
      intro a x y
      obtain ⟨yneg, ypos⟩ := y
      simp [deningerPrimeGammaPoincarePairing, smul_eq_mul]
      ring)
    (by
      intro x y y'
      obtain ⟨xneg, xpos⟩ := x
      simp [deningerPrimeGammaPoincarePairing]
      ring)
    (by
      intro a x y
      obtain ⟨xneg, xpos⟩ := x
      simp [deningerPrimeGammaPoincarePairing, smul_eq_mul]
      ring)

theorem deningerPrimeGammaH1CupTrace_apply
    (x y : DeningerPrimeGammaH1) :
    deningerPrimeGammaH1CupTrace x y =
      deningerPrimeGammaPoincarePairing x.1 y.2 -
        deningerPrimeGammaPoincarePairing y.1 x.2 :=
  rfl

/-- The source degree-one cup product is alternating. -/
theorem deningerPrimeGammaH1CupTrace_isAlt :
    deningerPrimeGammaH1CupTrace.IsAlt := by
  intro x
  rw [deningerPrimeGammaH1CupTrace_apply, sub_self]

/-- Exact radical reduction makes the source degree-one cup product nondegenerate. -/
theorem deningerPrimeGammaH1CupTrace_nondegenerate :
    deningerPrimeGammaH1CupTrace.Nondegenerate := by
  refine deningerPrimeGammaH1CupTrace_isAlt.isRefl
    |>.nondegenerate_iff_separatingLeft.mpr ?_
  intro x hx
  have hxneg : x.1 = 0 := by
    apply deningerPrimeGammaPoincarePairing_separatingLeft
    intro y
    have h := hx (0, y)
    simpa [deningerPrimeGammaH1CupTrace_apply,
      deningerPrimeGammaPoincarePairing] using h
  have hxpos : x.2 = 0 := by
    apply deningerPrimeGammaPoincarePairing_separatingRight
    intro y
    have h := hx (y, 0)
    have h' :
        -deningerPrimeGammaPoincarePairing y x.2 = 0 := by
      simpa [deningerPrimeGammaH1CupTrace_apply,
        deningerPrimeGammaPoincarePairing] using h
    simpa using h'
  exact Prod.ext hxneg hxpos

end

end RHTower
