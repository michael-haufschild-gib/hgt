import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittMilnorIncidence

/-!
# Oriented Calderón--Witt arithmetic source

The exterior Calderón--Witt cup is onto its algebraic suspension
center.  Used alone as the last differential, it therefore kills top
cohomology.  The arithmetic source instead carries the graph of cup
against a source-derived Haar orientation:

`w ↦ (cup(w), -tr(cup(w)))`.

The complementary trace `(z,c) ↦ tr(z)+c` has this graph as its exact
kernel.  Thus Milnor incidence remains the exact middle boundary while
the cokernel is one orientation line.  Both local and all-prime
constructions are made on the directed algebraic rational-Witt source,
before Hilbert completion.
-/

namespace RHTower

open scoped DirectSum

noncomputable section

/-! ## Canonical source unit and normalized Haar orientation -/

/-- Haar square mass of the source unit. -/
def deningerCalderonWittAlgebraicUnitMass
    (p : Nat.Primes) : ℂ :=
  inner ℂ
    (deningerCalderonWittAlgebraicUnitPacket p).1
    (deningerCalderonWittAlgebraicUnitPacket p).1

theorem deningerCalderonWittAlgebraicUnitMass_ne_zero
    (p : Nat.Primes) :
    deningerCalderonWittAlgebraicUnitMass p ≠ 0 := by
  rw [deningerCalderonWittAlgebraicUnitMass, inner_self_ne_zero]
  intro h
  apply deningerCalderonWittAlgebraicUnitPacket_ne_zero p
  apply Subtype.ext
  exact h

/-- Normalized source Haar coefficient on the algebraic packet. -/
def deningerCalderonWittAlgebraicPacketTrace
    (p : Nat.Primes) :
    DeningerPrimeFinitePacketGaugeAlgebraic p →ₗ[ℂ] ℂ where
  toFun a :=
    (deningerCalderonWittAlgebraicUnitMass p)⁻¹ *
      inner ℂ
        (deningerCalderonWittAlgebraicUnitPacket p).1 a.1
  map_add' a b := by
    change
      (deningerCalderonWittAlgebraicUnitMass p)⁻¹ *
          inner ℂ (deningerCalderonWittAlgebraicUnitPacket p).1
            (a.1 + b.1) =
        (deningerCalderonWittAlgebraicUnitMass p)⁻¹ *
            inner ℂ (deningerCalderonWittAlgebraicUnitPacket p).1 a.1 +
          (deningerCalderonWittAlgebraicUnitMass p)⁻¹ *
            inner ℂ (deningerCalderonWittAlgebraicUnitPacket p).1 b.1
    rw [inner_add_right, mul_add]
  map_smul' c a := by
    change
      (deningerCalderonWittAlgebraicUnitMass p)⁻¹ *
          inner ℂ (deningerCalderonWittAlgebraicUnitPacket p).1
            (c • a.1) =
        c •
          ((deningerCalderonWittAlgebraicUnitMass p)⁻¹ *
            inner ℂ (deningerCalderonWittAlgebraicUnitPacket p).1 a.1)
    rw [inner_smul_right, smul_eq_mul]
    ring

@[simp]
theorem deningerCalderonWittAlgebraicPacketTrace_unit
    (p : Nat.Primes) :
    deningerCalderonWittAlgebraicPacketTrace p
        (deningerCalderonWittAlgebraicUnitPacket p) =
      1 := by
  change
    (deningerCalderonWittAlgebraicUnitMass p)⁻¹ *
      deningerCalderonWittAlgebraicUnitMass p = 1
  exact
    inv_mul_cancel₀
      (deningerCalderonWittAlgebraicUnitMass_ne_zero p)

/-- Constant-packet section of the normalized packet trace. -/
def deningerCalderonWittAlgebraicPacketConstantSection
    (p : Nat.Primes) :
    ℂ →ₗ[ℂ] DeningerPrimeFinitePacketGaugeAlgebraic p where
  toFun c := c • deningerCalderonWittAlgebraicUnitPacket p
  map_add' c d := by
    rw [add_smul]
  map_smul' c d := by
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (smul_smul c d
        (deningerCalderonWittAlgebraicUnitPacket p)).symm

/-- Packet trace retracts the constant source section. -/
theorem deningerCalderonWittAlgebraicPacketTrace_section
    (p : Nat.Primes) :
    (deningerCalderonWittAlgebraicPacketTrace p).comp
        (deningerCalderonWittAlgebraicPacketConstantSection p) =
      LinearMap.id := by
  apply LinearMap.ext
  intro c
  simp [deningerCalderonWittAlgebraicPacketConstantSection]

/-- Source-derived orientation trace on the algebraic suspension
center. -/
def deningerCalderonWittAlgebraicCenterTrace
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeTwo p →ₗ[ℂ] ℂ where
  toFun z :=
    deningerCalderonWittAlgebraicPacketTrace p
      ((deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv p).symm z)
  map_add' z w := by
    rw [map_add, map_add]
  map_smul' c z := by
    rw [map_smul, map_smul]
    simp only [RingHom.id_apply]

/-- Center section induced by the constant algebraic packet. -/
def deningerCalderonWittAlgebraicCenterOrientationSection
    (p : Nat.Primes) :
    ℂ →ₗ[ℂ] DeningerCalderonWittAlgebraicDegreeTwo p where
  toFun c :=
    deningerPrimeFinitePacketGaugeAlgebraicFirstMode p
      (deningerCalderonWittAlgebraicPacketConstantSection p c)
  map_add' c d := by
    rw [map_add, map_add]
  map_smul' c d := by
    rw [map_smul, map_smul]
    simp only [RingHom.id_apply]

/-- The source center orientation is normalized, not an adjoined
zero functional. -/
@[simp]
theorem deningerCalderonWittAlgebraicCenterTrace_orientationSection
    (p : Nat.Primes) (c : ℂ) :
    deningerCalderonWittAlgebraicCenterTrace p
        (deningerCalderonWittAlgebraicCenterOrientationSection p c) =
      c := by
  change
    deningerCalderonWittAlgebraicPacketTrace p
        ((deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv p).symm
          (deningerPrimeFinitePacketGaugeAlgebraicFirstMode p
            (deningerCalderonWittAlgebraicPacketConstantSection p c))) =
      c
  rw [←
    deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv_apply p]
  rw [(deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv p).symm_apply_apply]
  exact LinearMap.congr_fun
    (deningerCalderonWittAlgebraicPacketTrace_section p) c

/-- Center orientation trace is onto, with its source-derived
constant-packet section. -/
theorem deningerCalderonWittAlgebraicCenterTrace_surjective
    (p : Nat.Primes) :
    Function.Surjective
      (deningerCalderonWittAlgebraicCenterTrace p) := by
  intro c
  exact
    ⟨deningerCalderonWittAlgebraicCenterOrientationSection p c,
      deningerCalderonWittAlgebraicCenterTrace_orientationSection p c⟩

/-! ## Local oriented Milnor--Arakelov source -/

/-- Graph embedding of a center class against its orientation
coefficient. -/
def deningerCalderonWittOrientedCenterGraph
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeTwo p →ₗ[ℂ]
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) where
  toFun z := (z, -deningerCalderonWittAlgebraicCenterTrace p z)
  map_add' z w := by
    apply Prod.ext
    · rfl
    · change
        -deningerCalderonWittAlgebraicCenterTrace p (z + w) =
          -deningerCalderonWittAlgebraicCenterTrace p z +
            -deningerCalderonWittAlgebraicCenterTrace p w
      rw [map_add]
      abel
  map_smul' c z := by
    apply Prod.ext
    · rfl
    · change
        -deningerCalderonWittAlgebraicCenterTrace p (c • z) =
          c • -deningerCalderonWittAlgebraicCenterTrace p z
      rw [map_smul, smul_neg]

/-- Oriented last differential: exterior cup followed by the
source-orientation graph. -/
def deningerCalderonWittOrientedBoundary
    (p : Nat.Primes) :
    (⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne p)) →ₗ[ℂ]
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) :=
  (deningerCalderonWittOrientedCenterGraph p).comp
    (deningerCalderonWittAlgebraicExteriorCup p)

/-- Arakelov trace complementary to the oriented cup graph. -/
def deningerCalderonWittOrientedTrace
    (p : Nat.Primes) :
    (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ] ℂ where
  toFun z := deningerCalderonWittAlgebraicCenterTrace p z.1 + z.2
  map_add' z w := by
    simp
    ring
  map_smul' c z := by
    simp
    ring

/-- The oriented boundary image is exactly the trace kernel. -/
theorem deningerCalderonWittOrientedBoundary_exact :
    Function.Exact
      (deningerCalderonWittOrientedBoundary p)
      (deningerCalderonWittOrientedTrace p) := by
  intro z
  constructor
  · intro hz
    change
      deningerCalderonWittAlgebraicCenterTrace p z.1 + z.2 =
        0 at hz
    obtain ⟨w, hw⟩ :=
      deningerCalderonWittAlgebraicExteriorCup_surjective p z.1
    refine ⟨w, ?_⟩
    apply Prod.ext
    · exact hw
    · change
        -deningerCalderonWittAlgebraicCenterTrace p
          (deningerCalderonWittAlgebraicExteriorCup p w) =
          z.2
      rw [hw]
      exact neg_eq_of_add_eq_zero_right hz
  · rintro ⟨w, rfl⟩
    change
      deningerCalderonWittAlgebraicCenterTrace p
          (deningerCalderonWittAlgebraicExteriorCup p w) +
        -deningerCalderonWittAlgebraicCenterTrace p
          (deningerCalderonWittAlgebraicExteriorCup p w) =
        0
    exact add_neg_cancel _

/-- Oriented trace is onto via the independent orientation
coordinate. -/
theorem deningerCalderonWittOrientedTrace_surjective :
    Function.Surjective
      (deningerCalderonWittOrientedTrace p) := by
  intro c
  exact ⟨(0, c), by simp [deningerCalderonWittOrientedTrace]⟩

/-- Milnor incidence remains exactly the kernel of the oriented
boundary. -/
theorem deningerCalderonWittOrientedMilnorIncidence_exact :
    Function.Exact
      (deningerCalderonWittMilnorIncidence p).subtype
      (deningerCalderonWittOrientedBoundary p) := by
  intro w
  constructor
  · intro hw
    apply (deningerCalderonWittMilnorIncidence_exact p w).1
    exact congrArg Prod.fst hw
  · intro hw
    have hcup :
        deningerCalderonWittAlgebraicExteriorCup p w = 0 :=
      (deningerCalderonWittMilnorIncidence_exact p w).2 hw
    apply Prod.ext
    · exact hcup
    · change
        -deningerCalderonWittAlgebraicCenterTrace p
            (deningerCalderonWittAlgebraicExteriorCup p w) =
          0
      rw [hcup, map_zero, neg_zero]

/-- Local source complex with exact Milnor middle and a surviving
orientation line in top degree. -/
def deningerCalderonWittOrientedSourceComplex
    (p : Nat.Primes) :
    DeningerArithmeticThreeTermComplex ℂ
      (deningerCalderonWittMilnorIncidence p)
      (⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne p))
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) where
  d0 := (deningerCalderonWittMilnorIncidence p).subtype
  d1 := deningerCalderonWittOrientedBoundary p
  d1_comp_d0 :=
    deningerCalderonWittOrientedMilnorIncidence_exact
      |>.linearMap_comp_eq_zero

theorem deningerCalderonWittOrientedSourceComplex_H0_eq_zero
    (p : Nat.Primes)
    (x : (deningerCalderonWittOrientedSourceComplex p).H0) :
    x = 0 :=
  deningerThreeTermH0_eq_zero_of_injective
    (deningerCalderonWittOrientedSourceComplex p)
    (deningerCalderonWittMilnorIncidence p).subtype_injective x

theorem deningerCalderonWittOrientedSourceComplex_H1_eq_zero
    (p : Nat.Primes)
    (x : (deningerCalderonWittOrientedSourceComplex p).H1) :
    x = 0 :=
  deningerThreeTermH1_eq_zero_of_exact
    (deningerCalderonWittOrientedSourceComplex p)
    deningerCalderonWittOrientedMilnorIncidence_exact x

/-- Local top cohomology is canonically the orientation line. -/
def deningerCalderonWittOrientedSourceComplexH2Equiv
    (p : Nat.Primes) :
    (deningerCalderonWittOrientedSourceComplex p).H2 ≃ₗ[ℂ] ℂ :=
  deningerCalderonWittOrientedBoundary_exact.linearEquivOfSurjective
    deningerCalderonWittOrientedTrace_surjective

/-- Inclusion of the surviving orientation coordinate. -/
def deningerCalderonWittOrientationInclusion
    (p : Nat.Primes) :
    ℂ →ₗ[ℂ] (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) where
  toFun c := (0, c)
  map_add' _ _ := by
    ext <;> simp
  map_smul' _ _ := by
    ext <;> simp

/-- Green lift of the center coordinate to the exterior source. -/
def deningerCalderonWittOrientedTopGreenLift
    (p : Nat.Primes) :
    (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ]
      (⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne p)) :=
  (deningerCalderonWittExteriorCupSection p).comp
    (LinearMap.fst ℂ
      (DeningerCalderonWittAlgebraicDegreeTwo p) ℂ)

/-- Top Green decomposition: boundary graph plus its surviving
orientation component equals the original top cochain. -/
theorem deningerCalderonWittOrientedTopGreenDecomposition
    (p : Nat.Primes)
    (z : DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) :
    deningerCalderonWittOrientedBoundary p
        (deningerCalderonWittOrientedTopGreenLift p z) +
      deningerCalderonWittOrientationInclusion p
        (deningerCalderonWittOrientedTrace p z) =
      z := by
  have hcup := LinearMap.congr_fun
    (deningerCalderonWittExteriorCup_section p) z.1
  change
    (deningerCalderonWittAlgebraicExteriorCup p
        (deningerCalderonWittExteriorCupSection p z.1),
      -deningerCalderonWittAlgebraicCenterTrace p
        (deningerCalderonWittAlgebraicExteriorCup p
          (deningerCalderonWittExteriorCupSection p z.1))) +
      (0,
        deningerCalderonWittAlgebraicCenterTrace p z.1 + z.2) =
      z
  rw [show
    deningerCalderonWittAlgebraicExteriorCup p
        (deningerCalderonWittExteriorCupSection p z.1) = z.1 by
      simpa [LinearMap.comp_apply] using hcup]
  apply Prod.ext
  · simp
  · simp

/-! ## Local Green forms and exact radicals -/

/-- Middle Green form pulled back from the algebraic suspension
center along exterior cup. -/
def deningerCalderonWittMiddleGreenForm
    (p : Nat.Primes)
    (w v :
      ⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne p)) : ℂ :=
  inner ℂ
    (deningerCalderonWittAlgebraicExteriorCup p w)
    (deningerCalderonWittAlgebraicExteriorCup p v)

/-- Middle Green self-pairing is nonnegative. -/
theorem deningerCalderonWittMiddleGreenForm_self_nonneg
    (p : Nat.Primes)
    (w :
      ⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne p)) :
    0 ≤
      Complex.re
        (deningerCalderonWittMiddleGreenForm p w w) := by
  change
    0 ≤ Complex.re
      (inner ℂ
        (deningerCalderonWittAlgebraicExteriorCup p w)
        (deningerCalderonWittAlgebraicExteriorCup p w))
  exact
    inner_self_nonneg
      (𝕜 := ℂ)
      (x := deningerCalderonWittAlgebraicExteriorCup p w)

/-- **Exact middle radical.** Green energy vanishes exactly on
Milnor-incidence boundaries. -/
theorem deningerCalderonWittMiddleGreenForm_self_eq_zero_iff
    (p : Nat.Primes)
    (w :
      ⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne p)) :
    deningerCalderonWittMiddleGreenForm p w w = 0 ↔
      w ∈ deningerCalderonWittMilnorIncidence p := by
  change
    inner ℂ
        (deningerCalderonWittAlgebraicExteriorCup p w)
        (deningerCalderonWittAlgebraicExteriorCup p w) = 0 ↔
      deningerCalderonWittAlgebraicExteriorCup p w = 0
  exact
    inner_self_eq_zero
      (𝕜 := ℂ)
      (x := deningerCalderonWittAlgebraicExteriorCup p w)

/-- Top Green form pulled back from the surviving orientation line. -/
def deningerCalderonWittTopGreenForm
    (p : Nat.Primes)
    (z w : DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) : ℂ :=
  inner ℂ
    (deningerCalderonWittOrientedTrace p z)
    (deningerCalderonWittOrientedTrace p w)

/-- Top Green self-pairing is nonnegative. -/
theorem deningerCalderonWittTopGreenForm_self_nonneg
    (p : Nat.Primes)
    (z : DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) :
    0 ≤ Complex.re (deningerCalderonWittTopGreenForm p z z) := by
  change
    0 ≤ Complex.re
      (inner ℂ
        (deningerCalderonWittOrientedTrace p z)
        (deningerCalderonWittOrientedTrace p z))
  exact
    inner_self_nonneg
      (𝕜 := ℂ)
      (x := deningerCalderonWittOrientedTrace p z)

/-- **Exact top radical.** Orientation energy vanishes exactly on
oriented source boundaries. -/
theorem deningerCalderonWittTopGreenForm_self_eq_zero_iff
    (p : Nat.Primes)
    (z : DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) :
    deningerCalderonWittTopGreenForm p z z = 0 ↔
      z ∈ LinearMap.range
        (deningerCalderonWittOrientedBoundary p) := by
  change
    inner ℂ
        (deningerCalderonWittOrientedTrace p z)
        (deningerCalderonWittOrientedTrace p z) = 0 ↔
      z ∈ LinearMap.range
        (deningerCalderonWittOrientedBoundary p)
  rw [inner_self_eq_zero]
  exact deningerCalderonWittOrientedBoundary_exact z

/-! ## All-prime oriented Milnor--Arakelov source -/

/-- Finite-support sum of local source orientation coefficients. -/
def deningerCalderonWittAlgebraicGlobalCenterTrace :
    DeningerCalderonWittAlgebraicGlobalDegreeTwo →ₗ[ℂ] ℂ :=
  DirectSum.toModule ℂ Nat.Primes ℂ
    deningerCalderonWittAlgebraicCenterTrace

@[simp]
theorem deningerCalderonWittAlgebraicGlobalCenterTrace_lof
    (p : Nat.Primes)
    (z : DeningerCalderonWittAlgebraicDegreeTwo p) :
    deningerCalderonWittAlgebraicGlobalCenterTrace
        (DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeTwo p z) =
      deningerCalderonWittAlgebraicCenterTrace p z := by
  rw [deningerCalderonWittAlgebraicGlobalCenterTrace,
    DirectSum.toModule_lof]

/-- A local constant-packet orientation inserted into the all-prime
center. -/
def deningerCalderonWittGlobalPrimeCenterOrientationSection
    (p : Nat.Primes) :
    ℂ →ₗ[ℂ] DeningerCalderonWittAlgebraicGlobalDegreeTwo :=
  (DirectSum.lof ℂ Nat.Primes
    DeningerCalderonWittAlgebraicDegreeTwo p).comp
      (deningerCalderonWittAlgebraicCenterOrientationSection p)

@[simp]
theorem deningerCalderonWittAlgebraicGlobalCenterTrace_primeSection
    (p : Nat.Primes) (c : ℂ) :
    deningerCalderonWittAlgebraicGlobalCenterTrace
        (deningerCalderonWittGlobalPrimeCenterOrientationSection p c) =
      c := by
  rw [deningerCalderonWittGlobalPrimeCenterOrientationSection,
    LinearMap.comp_apply,
    deningerCalderonWittAlgebraicGlobalCenterTrace_lof,
    deningerCalderonWittAlgebraicCenterTrace_orientationSection]

/-- Every prime separately supplies the global orientation
coefficient. -/
theorem deningerCalderonWittAlgebraicGlobalCenterTrace_surjective
    (p : Nat.Primes) :
    Function.Surjective
      deningerCalderonWittAlgebraicGlobalCenterTrace := by
  intro c
  exact
    ⟨deningerCalderonWittGlobalPrimeCenterOrientationSection p c,
      deningerCalderonWittAlgebraicGlobalCenterTrace_primeSection p c⟩

/-- All-prime center graph against the finite-support source
orientation trace. -/
def deningerCalderonWittGlobalOrientedCenterGraph :
    DeningerCalderonWittAlgebraicGlobalDegreeTwo →ₗ[ℂ]
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) where
  toFun z := (z, -deningerCalderonWittAlgebraicGlobalCenterTrace z)
  map_add' z w := by
    apply Prod.ext
    · rfl
    · change
        -deningerCalderonWittAlgebraicGlobalCenterTrace (z + w) =
          -deningerCalderonWittAlgebraicGlobalCenterTrace z +
            -deningerCalderonWittAlgebraicGlobalCenterTrace w
      rw [map_add]
      abel
  map_smul' c z := by
    apply Prod.ext
    · rfl
    · change
        -deningerCalderonWittAlgebraicGlobalCenterTrace (c • z) =
          c • -deningerCalderonWittAlgebraicGlobalCenterTrace z
      rw [map_smul, smul_neg]

/-- All-prime oriented source boundary. -/
def deningerCalderonWittGlobalOrientedBoundary :
    (⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne) →ₗ[ℂ]
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) :=
  deningerCalderonWittGlobalOrientedCenterGraph.comp
    deningerCalderonWittAlgebraicGlobalExteriorCup

/-- All-prime source Arakelov trace. -/
def deningerCalderonWittGlobalOrientedTrace :
    (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] ℂ where
  toFun z := deningerCalderonWittAlgebraicGlobalCenterTrace z.1 + z.2
  map_add' z w := by
    simp
    ring
  map_smul' c z := by
    simp
    ring

/-- Global oriented boundary image is exactly the global trace
kernel. -/
theorem deningerCalderonWittGlobalOrientedBoundary_exact :
    Function.Exact
      deningerCalderonWittGlobalOrientedBoundary
      deningerCalderonWittGlobalOrientedTrace := by
  intro z
  constructor
  · intro hz
    change
      deningerCalderonWittAlgebraicGlobalCenterTrace z.1 + z.2 =
        0 at hz
    obtain ⟨w, hw⟩ :=
      deningerCalderonWittAlgebraicGlobalExteriorCup_surjective z.1
    refine ⟨w, ?_⟩
    apply Prod.ext
    · exact hw
    · change
        -deningerCalderonWittAlgebraicGlobalCenterTrace
            (deningerCalderonWittAlgebraicGlobalExteriorCup w) =
          z.2
      rw [hw]
      exact neg_eq_of_add_eq_zero_right hz
  · rintro ⟨w, rfl⟩
    change
      deningerCalderonWittAlgebraicGlobalCenterTrace
          (deningerCalderonWittAlgebraicGlobalExteriorCup w) +
        -deningerCalderonWittAlgebraicGlobalCenterTrace
          (deningerCalderonWittAlgebraicGlobalExteriorCup w) =
        0
    exact add_neg_cancel _

theorem deningerCalderonWittGlobalOrientedTrace_surjective :
    Function.Surjective
      deningerCalderonWittGlobalOrientedTrace := by
  intro c
  exact ⟨(0, c), by simp [deningerCalderonWittGlobalOrientedTrace]⟩

/-- Global Milnor incidence is exactly the kernel of the oriented
boundary. -/
theorem deningerCalderonWittGlobalOrientedMilnorIncidence_exact :
    Function.Exact
      deningerCalderonWittGlobalMilnorIncidence.subtype
      deningerCalderonWittGlobalOrientedBoundary := by
  intro w
  constructor
  · intro hw
    apply (deningerCalderonWittGlobalMilnorIncidence_exact w).1
    exact congrArg Prod.fst hw
  · intro hw
    have hcup :
        deningerCalderonWittAlgebraicGlobalExteriorCup w = 0 :=
      (deningerCalderonWittGlobalMilnorIncidence_exact w).2 hw
    apply Prod.ext
    · exact hcup
    · change
        -deningerCalderonWittAlgebraicGlobalCenterTrace
            (deningerCalderonWittAlgebraicGlobalExteriorCup w) =
          0
      rw [hcup, map_zero, neg_zero]

/-- All-prime algebraic source complex with exact middle and one
surviving orientation line. -/
def deningerCalderonWittGlobalOrientedSourceComplex :
    DeningerArithmeticThreeTermComplex ℂ
      deningerCalderonWittGlobalMilnorIncidence
      (⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne)
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) where
  d0 := deningerCalderonWittGlobalMilnorIncidence.subtype
  d1 := deningerCalderonWittGlobalOrientedBoundary
  d1_comp_d0 :=
    deningerCalderonWittGlobalOrientedMilnorIncidence_exact
      |>.linearMap_comp_eq_zero

theorem deningerCalderonWittGlobalOrientedSourceComplex_H0_eq_zero
    (x : deningerCalderonWittGlobalOrientedSourceComplex.H0) :
    x = 0 :=
  deningerThreeTermH0_eq_zero_of_injective
    deningerCalderonWittGlobalOrientedSourceComplex
    deningerCalderonWittGlobalMilnorIncidence.subtype_injective x

theorem deningerCalderonWittGlobalOrientedSourceComplex_H1_eq_zero
    (x : deningerCalderonWittGlobalOrientedSourceComplex.H1) :
    x = 0 :=
  deningerThreeTermH1_eq_zero_of_exact
    deningerCalderonWittGlobalOrientedSourceComplex
    deningerCalderonWittGlobalOrientedMilnorIncidence_exact x

/-- Global top cohomology is canonically one source orientation
line. -/
def deningerCalderonWittGlobalOrientedSourceComplexH2Equiv :
    deningerCalderonWittGlobalOrientedSourceComplex.H2 ≃ₗ[ℂ] ℂ :=
  deningerCalderonWittGlobalOrientedBoundary_exact.linearEquivOfSurjective
    deningerCalderonWittGlobalOrientedTrace_surjective

/-- Inclusion of global orientation cochains. -/
def deningerCalderonWittGlobalOrientationInclusion :
    ℂ →ₗ[ℂ]
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) where
  toFun c := (0, c)
  map_add' _ _ := by
    ext <;> simp
  map_smul' _ _ := by
    ext <;> simp

/-- Global Green lift of the center coordinate. -/
def deningerCalderonWittGlobalOrientedTopGreenLift :
    (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ]
      (⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne) :=
  deningerCalderonWittGlobalExteriorCupSection.comp
    (LinearMap.fst ℂ
      DeningerCalderonWittAlgebraicGlobalDegreeTwo ℂ)

/-- Global top Green decomposition into exact graph boundary and
surviving orientation. -/
theorem deningerCalderonWittGlobalOrientedTopGreenDecomposition
    (z : DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) :
    deningerCalderonWittGlobalOrientedBoundary
        (deningerCalderonWittGlobalOrientedTopGreenLift z) +
      deningerCalderonWittGlobalOrientationInclusion
        (deningerCalderonWittGlobalOrientedTrace z) =
      z := by
  have hcup := LinearMap.congr_fun
    deningerCalderonWittGlobalExteriorCup_section z.1
  change
    (deningerCalderonWittAlgebraicGlobalExteriorCup
        (deningerCalderonWittGlobalExteriorCupSection z.1),
      -deningerCalderonWittAlgebraicGlobalCenterTrace
        (deningerCalderonWittAlgebraicGlobalExteriorCup
          (deningerCalderonWittGlobalExteriorCupSection z.1))) +
      (0,
        deningerCalderonWittAlgebraicGlobalCenterTrace z.1 + z.2) =
      z
  rw [show
    deningerCalderonWittAlgebraicGlobalExteriorCup
        (deningerCalderonWittGlobalExteriorCupSection z.1) = z.1 by
      simpa [LinearMap.comp_apply] using hcup]
  apply Prod.ext
  · simp
  · simp

/-! ## All-prime Green forms and exact radicals -/

/-- Prime-coordinate Green form on the all-prime middle source.  The
whole family is retained; no scalar prime summation can erase packet
directions. -/
def deningerCalderonWittGlobalMiddleGreenCoordinate
    (p : Nat.Primes)
    (w v :
      ⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne) : ℂ :=
  inner ℂ
    (DirectSum.component ℂ Nat.Primes
      DeningerCalderonWittAlgebraicDegreeTwo p
        (deningerCalderonWittAlgebraicGlobalExteriorCup w))
    (DirectSum.component ℂ Nat.Primes
      DeningerCalderonWittAlgebraicDegreeTwo p
        (deningerCalderonWittAlgebraicGlobalExteriorCup v))

theorem deningerCalderonWittGlobalMiddleGreenCoordinate_self_nonneg
    (p : Nat.Primes)
    (w :
      ⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne) :
    0 ≤ Complex.re
      (deningerCalderonWittGlobalMiddleGreenCoordinate p w w) := by
  change
    0 ≤ Complex.re
      (inner ℂ
        (DirectSum.component ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeTwo p
            (deningerCalderonWittAlgebraicGlobalExteriorCup w))
        (DirectSum.component ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeTwo p
            (deningerCalderonWittAlgebraicGlobalExteriorCup w)))
  exact
    inner_self_nonneg
      (𝕜 := ℂ)
      (x :=
        DirectSum.component ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeTwo p
            (deningerCalderonWittAlgebraicGlobalExteriorCup w))

/-- **Exact all-prime middle radical.** Every prime-coordinate Green
energy vanishes exactly on global Milnor incidence. -/
theorem
    deningerCalderonWittGlobalMiddleGreenCoordinate_self_eq_zero_iff
    (w :
      ⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne) :
    (∀ p : Nat.Primes,
      deningerCalderonWittGlobalMiddleGreenCoordinate p w w = 0) ↔
      w ∈ deningerCalderonWittGlobalMilnorIncidence := by
  constructor
  · intro h
    change
      deningerCalderonWittAlgebraicGlobalExteriorCup w = 0
    apply DirectSum.ext_component ℂ
    intro p
    have hp := h p
    change
      inner ℂ
          (DirectSum.component ℂ Nat.Primes
            DeningerCalderonWittAlgebraicDegreeTwo p
              (deningerCalderonWittAlgebraicGlobalExteriorCup w))
          (DirectSum.component ℂ Nat.Primes
            DeningerCalderonWittAlgebraicDegreeTwo p
              (deningerCalderonWittAlgebraicGlobalExteriorCup w)) =
        0 at hp
    exact
      (inner_self_eq_zero
        (𝕜 := ℂ)
        (x :=
          DirectSum.component ℂ Nat.Primes
            DeningerCalderonWittAlgebraicDegreeTwo p
              (deningerCalderonWittAlgebraicGlobalExteriorCup w))).mp hp
  · intro hw p
    change
      deningerCalderonWittAlgebraicGlobalExteriorCup w = 0 at hw
    simp [deningerCalderonWittGlobalMiddleGreenCoordinate, hw]

/-- All-prime top Green form. -/
def deningerCalderonWittGlobalTopGreenForm
    (z w : DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) : ℂ :=
  inner ℂ
    (deningerCalderonWittGlobalOrientedTrace z)
    (deningerCalderonWittGlobalOrientedTrace w)

theorem deningerCalderonWittGlobalTopGreenForm_self_nonneg
    (z : DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) :
    0 ≤ Complex.re
      (deningerCalderonWittGlobalTopGreenForm z z) := by
  change
    0 ≤ Complex.re
      (inner ℂ
        (deningerCalderonWittGlobalOrientedTrace z)
        (deningerCalderonWittGlobalOrientedTrace z))
  exact
    inner_self_nonneg
      (𝕜 := ℂ)
      (x := deningerCalderonWittGlobalOrientedTrace z)

/-- **Exact all-prime top radical.** -/
theorem deningerCalderonWittGlobalTopGreenForm_self_eq_zero_iff
    (z : DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) :
    deningerCalderonWittGlobalTopGreenForm z z = 0 ↔
      z ∈ LinearMap.range
        deningerCalderonWittGlobalOrientedBoundary := by
  change
    inner ℂ
        (deningerCalderonWittGlobalOrientedTrace z)
        (deningerCalderonWittGlobalOrientedTrace z) = 0 ↔
      z ∈ LinearMap.range
        deningerCalderonWittGlobalOrientedBoundary
  rw [inner_self_eq_zero]
  exact deningerCalderonWittGlobalOrientedBoundary_exact z

end

end RHTower
