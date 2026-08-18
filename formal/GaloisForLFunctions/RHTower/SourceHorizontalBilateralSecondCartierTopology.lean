import GaloisForLFunctions.RHTower.FrankensteinXiBidirectionalIntegralCartierSource
import GaloisForLFunctions.RHTower.SourceHorizontalEulerWoldIndefiniteEndpointAnnihilation

/-!
# Bilateral second-Cartier source topology

The first Cartier conormal identifies Laurent inversion with a sign: the forward and inverse
classes become negatives in `I / I²`.  This module retains the next source layer.  In the second
infinitesimal neighborhood `R / I³`, strict inversion satisfies

```text
[q⁻¹ - 1] = -[q - 1] + [(q - 1)²].
```

The quadratic class is nonzero, and the two literal orientations are integrally independent.
Thus their span is a genuine rank-two source lattice rather than a scalar orientation line.

Its complexification has a coefficient-faithful Hardy realization: the two basis vectors map to
the positive and reflected Hardy halves.  The map is injective, its range has complex dimension
two, and the quadratic source class maps to the full bilateral eigenfamily.  Consequently that
class is exactly Stokes-flat for every nonzero character.

The construction survives the literal Euler--Wold endpoint scale and preserves the actual Xi
support multiplicity.  It does not prove RH: off the critical line the quadratic image is not a
fixed-circle moderate distribution.  The result therefore constructs the non-scalar source
topology while isolating its remaining physical moderation/order obstruction.
-/

open Complex
open GaloisForLFunctions.HTGeometry
open LaurentPolynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The second integral Cartier neighborhood -/

/-- Second infinitesimal neighborhood of the integral Laurent Cartier divisor. -/
abbrev DeningerIntegralCartierSecondNeighborhood :=
  DeningerIntegralCartierSourceRing ⧸ DeningerIntegralCartierSourceIdeal ^ 3

/-- Forward orientation retained modulo the cube of the Cartier ideal. -/
def deningerIntegralCartierSecondForwardClass :
    DeningerIntegralCartierSecondNeighborhood :=
  Ideal.Quotient.mk (DeningerIntegralCartierSourceIdeal ^ 3)
    deningerIntegralCartierSourceGenerator

/-- Literal inverse orientation retained modulo the cube of the Cartier ideal. -/
def deningerIntegralCartierSecondInverseClass :
    DeningerIntegralCartierSecondNeighborhood :=
  Ideal.Quotient.mk (DeningerIntegralCartierSourceIdeal ^ 3)
    (inversion ℤ deningerIntegralCartierSourceGenerator)

/-- Even quadratic inversion ghost in the second Cartier neighborhood. -/
def deningerIntegralCartierSecondGhostClass :
    DeningerIntegralCartierSecondNeighborhood :=
  Ideal.Quotient.mk (DeningerIntegralCartierSourceIdeal ^ 3)
    (deningerIntegralCartierSourceGenerator ^ 2)

/-- Exact second-order inversion expansion.  The omitted term is a unit times the cube of the
Cartier generator, so it vanishes precisely in the second infinitesimal neighborhood. -/
theorem deningerIntegralCartierInversion_secondOrder_remainder :
    inversion ℤ deningerIntegralCartierSourceGenerator -
        (-deningerIntegralCartierSourceGenerator +
          deningerIntegralCartierSourceGenerator ^ 2) ∈
      DeningerIntegralCartierSourceIdeal ^ 3 := by
  rw [deningerIntegralCartierSourceGenerator, inversion_sub_one]
  have hT :
      (T (-1) : DeningerIntegralCartierSourceRing) * T 1 = 1 := by
    rw [← LaurentPolynomial.T_add]
    simp
  have heq :
      -(T (-1) : DeningerIntegralCartierSourceRing) * (T 1 - 1) -
          (-(T 1 - 1) + (T 1 - 1) ^ 2) =
        -(T (-1) : DeningerIntegralCartierSourceRing) * (T 1 - 1) ^ 3 := by
    linear_combination ((T 1) ^ 2 - 3 * T 1 + 2) * hT
  rw [heq]
  change
    -(T (-1) : DeningerIntegralCartierSourceRing) *
        deningerIntegralCartierSourceGenerator ^ 3 ∈
      Ideal.span ({deningerIntegralCartierSourceGenerator} :
        Set DeningerIntegralCartierSourceRing) ^ 3
  rw [Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton'.mpr
    ⟨-(T (-1) : DeningerIntegralCartierSourceRing), by ring⟩

/-- The two literal orientations close through, rather than erase, the quadratic ghost. -/
theorem deningerIntegralCartierSecondForward_add_inverse :
    deningerIntegralCartierSecondForwardClass +
        deningerIntegralCartierSecondInverseClass =
      deningerIntegralCartierSecondGhostClass := by
  rw [← sub_eq_zero, deningerIntegralCartierSecondForwardClass,
    deningerIntegralCartierSecondInverseClass,
    deningerIntegralCartierSecondGhostClass, ← map_add, ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  change
    deningerIntegralCartierSourceGenerator +
        inversion ℤ deningerIntegralCartierSourceGenerator -
          deningerIntegralCartierSourceGenerator ^ 2 ∈
      DeningerIntegralCartierSourceIdeal ^ 3
  have h := deningerIntegralCartierInversion_secondOrder_remainder
  convert h using 1
  ring

/-- Strict Laurent inversion is involutive on the retained source generator. -/
theorem deningerIntegralCartierInversion_involutive_on_generator :
    inversion ℤ (inversion ℤ deningerIntegralCartierSourceGenerator) =
      deningerIntegralCartierSourceGenerator := by
  simp [deningerIntegralCartierSourceGenerator]

/-- The quadratic source ghost is inversion-fixed modulo the third Cartier power.  This is the
second-order even law complementary to first-conormal oddness. -/
theorem deningerIntegralCartierInversion_ghost_remainder :
    inversion ℤ (deningerIntegralCartierSourceGenerator ^ 2) -
        deningerIntegralCartierSourceGenerator ^ 2 ∈
      DeningerIntegralCartierSourceIdeal ^ 3 := by
  have hplus : inversion ℤ deningerIntegralCartierSourceGenerator +
      deningerIntegralCartierSourceGenerator ∈
        DeningerIntegralCartierSourceIdeal ^ 2 := by
    simpa [deningerIntegralCartierSourceGenerator] using
      (inversion_conormal_odd (k := ℤ))
  have hinv : inversion ℤ deningerIntegralCartierSourceGenerator ∈
      DeningerIntegralCartierSourceIdeal := by
    simpa [deningerIntegralCartierSourceGenerator] using
      (inversion_mem_span (k := ℤ))
  have hminus : inversion ℤ deningerIntegralCartierSourceGenerator -
      deningerIntegralCartierSourceGenerator ∈
        DeningerIntegralCartierSourceIdeal :=
    Ideal.sub_mem _ hinv (by
      simpa [deningerIntegralCartierSourceGenerator] using
        (generator_mem (k := ℤ)))
  have hprod := Ideal.mul_mem_mul hplus hminus
  rw [← pow_succ] at hprod
  rw [map_pow]
  rw [show inversion ℤ deningerIntegralCartierSourceGenerator ^ 2 -
      deningerIntegralCartierSourceGenerator ^ 2 =
        (inversion ℤ deningerIntegralCartierSourceGenerator +
          deningerIntegralCartierSourceGenerator) *
        (inversion ℤ deningerIntegralCartierSourceGenerator -
          deningerIntegralCartierSourceGenerator) by ring]
  exact hprod

/-- Cancellation two levels deep in a principal regular Cartier ideal. -/
theorem deningerIntegralCartier_mul_sq_mem_cube_iff
    (q : DeningerIntegralCartierSourceRing) :
    q * deningerIntegralCartierSourceGenerator ^ 2 ∈
        DeningerIntegralCartierSourceIdeal ^ 3 ↔
      q ∈ DeningerIntegralCartierSourceIdeal := by
  change
    q * deningerIntegralCartierSourceGenerator ^ 2 ∈
        Ideal.span ({deningerIntegralCartierSourceGenerator} :
          Set DeningerIntegralCartierSourceRing) ^ 3 ↔
      q ∈ Ideal.span ({deningerIntegralCartierSourceGenerator} :
        Set DeningerIntegralCartierSourceRing)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton',
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply (deningerIntegralCartierSourceGenerator_isRegular.pow 2).right
    calc
      (a * deningerIntegralCartierSourceGenerator) *
          deningerIntegralCartierSourceGenerator ^ 2 =
        a * deningerIntegralCartierSourceGenerator ^ 3 := by ring
      _ = q * deningerIntegralCartierSourceGenerator ^ 2 := ha
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    ring

/-- The even quadratic ghost is not killed in `R / I³`. -/
theorem deningerIntegralCartierSecondGhostClass_ne_zero :
    deningerIntegralCartierSecondGhostClass ≠ 0 := by
  intro h
  rw [deningerIntegralCartierSecondGhostClass,
    Ideal.Quotient.eq_zero_iff_mem] at h
  have hmem : (1 : DeningerIntegralCartierSourceRing) ∈
      DeningerIntegralCartierSourceIdeal :=
    (deningerIntegralCartier_mul_sq_mem_cube_iff 1).1 (by simpa using h)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  have hc := congrArg (cartier ℤ) ha
  simp at hc

/-- Integral coordinate lattice generated by the two literal orientations in `R / I³`. -/
def deningerIntegralCartierSecondCoordinateMap :
    (ℤ × ℤ) →+ DeningerIntegralCartierSecondNeighborhood where
  toFun v :=
    v.1 • deningerIntegralCartierSecondForwardClass +
      v.2 • deningerIntegralCartierSecondInverseClass
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel

/-- Vanishing of a second-Cartier coordinate forces both integral orientation coefficients to
vanish. -/
theorem deningerIntegralCartierSecondCoordinateMap_eq_zero
    {v : ℤ × ℤ} (h : deningerIntegralCartierSecondCoordinateMap v = 0) :
    v = 0 := by
  rcases v with ⟨a, b⟩
  change
    a • deningerIntegralCartierSecondForwardClass +
        b • deningerIntegralCartierSecondInverseClass = 0 at h
  rw [deningerIntegralCartierSecondForwardClass,
    deningerIntegralCartierSecondInverseClass, ← map_zsmul, ← map_zsmul,
    ← map_add, Ideal.Quotient.eq_zero_iff_mem] at h
  simp only [zsmul_eq_mul] at h
  have hrel := deningerIntegralCartierInversion_secondOrder_remainder
  have hmem :
      (((a : DeningerIntegralCartierSourceRing) - b) +
          (b : DeningerIntegralCartierSourceRing) *
            deningerIntegralCartierSourceGenerator) *
          deningerIntegralCartierSourceGenerator ∈
        DeningerIntegralCartierSourceIdeal ^ 3 := by
    have heq :
        (a : DeningerIntegralCartierSourceRing) *
              deningerIntegralCartierSourceGenerator +
            (b : DeningerIntegralCartierSourceRing) *
              inversion ℤ deningerIntegralCartierSourceGenerator =
          (((a : DeningerIntegralCartierSourceRing) - b) +
              (b : DeningerIntegralCartierSourceRing) *
                deningerIntegralCartierSourceGenerator) *
              deningerIntegralCartierSourceGenerator +
            (b : DeningerIntegralCartierSourceRing) *
              (inversion ℤ deningerIntegralCartierSourceGenerator -
                (-deningerIntegralCartierSourceGenerator +
                  deningerIntegralCartierSourceGenerator ^ 2)) := by
      ring
    rw [heq] at h
    have hrem :
        (b : DeningerIntegralCartierSourceRing) *
            (inversion ℤ deningerIntegralCartierSourceGenerator -
              (-deningerIntegralCartierSourceGenerator +
                deningerIntegralCartierSourceGenerator ^ 2)) ∈
          DeningerIntegralCartierSourceIdeal ^ 3 :=
      Ideal.mul_mem_left _ _ hrel
    simpa only [add_sub_cancel_right] using Ideal.sub_mem _ h hrem
  have hcofactor :
      ((a : DeningerIntegralCartierSourceRing) - b) +
          (b : DeningerIntegralCartierSourceRing) *
            deningerIntegralCartierSourceGenerator ∈
        DeningerIntegralCartierSourceIdeal ^ 2 := by
    change
      (((a : DeningerIntegralCartierSourceRing) - b) +
            (b : DeningerIntegralCartierSourceRing) *
              deningerIntegralCartierSourceGenerator) *
          deningerIntegralCartierSourceGenerator ∈
        Ideal.span ({deningerIntegralCartierSourceGenerator} :
          Set DeningerIntegralCartierSourceRing) ^ 3 at hmem
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    change
      ((a : DeningerIntegralCartierSourceRing) - b) +
          (b : DeningerIntegralCartierSourceRing) *
            deningerIntegralCartierSourceGenerator ∈
        Ideal.span ({deningerIntegralCartierSourceGenerator} :
          Set DeningerIntegralCartierSourceRing) ^ 2
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨c, ?_⟩
    apply deningerIntegralCartierSourceGenerator_isRegular.right
    calc
      (c * deningerIntegralCartierSourceGenerator ^ 2) *
          deningerIntegralCartierSourceGenerator =
        c * deningerIntegralCartierSourceGenerator ^ 3 := by ring
      _ = ((((a : DeningerIntegralCartierSourceRing) - b) +
          (b : DeningerIntegralCartierSourceRing) *
            deningerIntegralCartierSourceGenerator) *
              deningerIntegralCartierSourceGenerator) := hc
  have hab : a = b := by
    have hsubset : DeningerIntegralCartierSourceIdeal ^ 2 ≤
        DeningerIntegralCartierSourceIdeal := Ideal.pow_le_self (by omega)
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (hsubset hcofactor)
    have heval := congrArg (cartier ℤ) hd
    simp [deningerIntegralCartierSourceGenerator] at heval
    have hab0 : a - b = 0 := by exact_mod_cast heval.symm
    exact sub_eq_zero.mp hab0
  subst a
  have hbmem : (b : DeningerIntegralCartierSourceRing) ∈
      DeningerIntegralCartierSourceIdeal := by
    have hcube :
        (b : DeningerIntegralCartierSourceRing) *
            deningerIntegralCartierSourceGenerator ^ 2 ∈
          DeningerIntegralCartierSourceIdeal ^ 3 := by
      simpa [sub_self, zero_add, pow_two, mul_assoc] using hmem
    exact (deningerIntegralCartier_mul_sq_mem_cube_iff
      (b : DeningerIntegralCartierSourceRing)).1 hcube
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hbmem
  have heval := congrArg (cartier ℤ) hd
  simp at heval
  have hb : b = 0 := by exact_mod_cast heval.symm
  simp [hb]

/-- The two source orientations are integrally independent in the second neighborhood. -/
theorem deningerIntegralCartierSecondCoordinateMap_injective :
    Function.Injective deningerIntegralCartierSecondCoordinateMap := by
  intro x y h
  apply sub_eq_zero.mp
  apply deningerIntegralCartierSecondCoordinateMap_eq_zero
  rw [map_sub, h, sub_self]

/-- Literal rank-two integral source lattice inside the second Cartier neighborhood.  Defining
it as the range, rather than replacing it by an abstract pair, keeps every later Hardy vector
attached to its Laurent source class. -/
abbrev DeningerIntegralCartierSecondSourceLattice :=
  AddMonoidHom.range deningerIntegralCartierSecondCoordinateMap

/-- Integral source coordinates are equivalent to the literal Laurent source lattice. -/
noncomputable def deningerIntegralCartierSecondCoordinateEquiv :
    (ℤ × ℤ) ≃+ DeningerIntegralCartierSecondSourceLattice :=
  AddEquiv.ofBijective
    deningerIntegralCartierSecondCoordinateMap.rangeRestrict
    ⟨fun _ _ h => deningerIntegralCartierSecondCoordinateMap_injective
      (congrArg Subtype.val h),
      AddMonoidHom.rangeRestrict_surjective _⟩

/-- Forward class as an element of the literal second-Cartier source lattice. -/
noncomputable def deningerIntegralCartierSecondForwardLatticeClass :
    DeningerIntegralCartierSecondSourceLattice :=
  deningerIntegralCartierSecondCoordinateEquiv (1, 0)

/-- Inverse class as an element of the literal second-Cartier source lattice. -/
noncomputable def deningerIntegralCartierSecondInverseLatticeClass :
    DeningerIntegralCartierSecondSourceLattice :=
  deningerIntegralCartierSecondCoordinateEquiv (0, 1)

/-- Quadratic class as an element of the literal second-Cartier source lattice. -/
noncomputable def deningerIntegralCartierSecondGhostLatticeClass :
    DeningerIntegralCartierSecondSourceLattice :=
  deningerIntegralCartierSecondCoordinateEquiv (1, 1)

@[simp] theorem deningerIntegralCartierSecondForwardLatticeClass_val :
    (deningerIntegralCartierSecondForwardLatticeClass :
      DeningerIntegralCartierSecondNeighborhood) =
        deningerIntegralCartierSecondForwardClass := by
  change deningerIntegralCartierSecondCoordinateMap (1, 0) = _
  simp [deningerIntegralCartierSecondCoordinateMap]

@[simp] theorem deningerIntegralCartierSecondInverseLatticeClass_val :
    (deningerIntegralCartierSecondInverseLatticeClass :
      DeningerIntegralCartierSecondNeighborhood) =
        deningerIntegralCartierSecondInverseClass := by
  change deningerIntegralCartierSecondCoordinateMap (0, 1) = _
  simp [deningerIntegralCartierSecondCoordinateMap]

/-- The integral source-lattice sum is the nonzero quadratic quotient class, not zero. -/
@[simp] theorem deningerIntegralCartierSecondGhostLatticeClass_val :
    (deningerIntegralCartierSecondGhostLatticeClass :
      DeningerIntegralCartierSecondNeighborhood) =
        deningerIntegralCartierSecondGhostClass := by
  change deningerIntegralCartierSecondCoordinateMap (1, 1) = _
  simp [deningerIntegralCartierSecondCoordinateMap,
    deningerIntegralCartierSecondForward_add_inverse]

/-- The literal quadratic source class remains nonzero in the rank-two source lattice. -/
theorem deningerIntegralCartierSecondGhostLatticeClass_ne_zero :
    deningerIntegralCartierSecondGhostLatticeClass ≠ 0 := by
  intro h
  apply deningerIntegralCartierSecondGhostClass_ne_zero
  have hval := congrArg Subtype.val h
  simpa using hval

/-! ## Complex rank-two Hardy source topology -/

/-- Complexification of the integral two-orientation source lattice. -/
abbrev SourceHorizontalBilateralSecondJetSource := ℂ × ℂ

/-- Forward source orientation. -/
def sourceHorizontalBilateralSecondJetForward :
    SourceHorizontalBilateralSecondJetSource := (1, 0)

/-- Inverse source orientation. -/
def sourceHorizontalBilateralSecondJetInverse :
    SourceHorizontalBilateralSecondJetSource := (0, 1)

/-- Quadratic source ghost, the sum of the two retained orientations. -/
def sourceHorizontalBilateralSecondJetGhost :
    SourceHorizontalBilateralSecondJetSource := (1, 1)

/-- Canonical integral-to-complex base change.  Unlike a fitted reporter, it changes neither
orientation coefficient. -/
def sourceHorizontalBilateralSecondJetIntegralCoordinates :
    (ℤ × ℤ) →+ SourceHorizontalBilateralSecondJetSource where
  toFun v := ((v.1 : ℂ), (v.2 : ℂ))
  map_zero' := by simp
  map_add' x y := by ext <;> simp

/-- Integral coefficients remain faithful after canonical complexification. -/
theorem sourceHorizontalBilateralSecondJetIntegralCoordinates_injective :
    Function.Injective sourceHorizontalBilateralSecondJetIntegralCoordinates := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  simp [sourceHorizontalBilateralSecondJetIntegralCoordinates] at hfst hsnd
  exact Prod.ext (by exact_mod_cast hfst) (by exact_mod_cast hsnd)

/-- Canonical complexification of the literal Laurent source lattice. -/
noncomputable def deningerIntegralCartierSecondSourceComplexification :
    DeningerIntegralCartierSecondSourceLattice →+
      SourceHorizontalBilateralSecondJetSource :=
  sourceHorizontalBilateralSecondJetIntegralCoordinates.comp
    deningerIntegralCartierSecondCoordinateEquiv.symm.toAddMonoidHom

/-- The literal second-Cartier source lattice embeds in its two-dimensional complexification. -/
theorem deningerIntegralCartierSecondSourceComplexification_injective :
    Function.Injective deningerIntegralCartierSecondSourceComplexification :=
  sourceHorizontalBilateralSecondJetIntegralCoordinates_injective.comp
    deningerIntegralCartierSecondCoordinateEquiv.symm.injective

/-- The complexification square commutes on every integral source coordinate. -/
theorem deningerIntegralCartierSecondSourceComplexification_coordinate
    (v : ℤ × ℤ) :
    deningerIntegralCartierSecondSourceComplexification
        (deningerIntegralCartierSecondCoordinateEquiv v) =
      sourceHorizontalBilateralSecondJetIntegralCoordinates v := by
  simp [deningerIntegralCartierSecondSourceComplexification]

@[simp] theorem deningerIntegralCartierSecondSourceComplexification_forward :
    deningerIntegralCartierSecondSourceComplexification
        deningerIntegralCartierSecondForwardLatticeClass =
      sourceHorizontalBilateralSecondJetForward := by
  rw [deningerIntegralCartierSecondForwardLatticeClass,
    deningerIntegralCartierSecondSourceComplexification_coordinate]
  ext <;> simp [sourceHorizontalBilateralSecondJetIntegralCoordinates,
    sourceHorizontalBilateralSecondJetForward]

@[simp] theorem deningerIntegralCartierSecondSourceComplexification_inverse :
    deningerIntegralCartierSecondSourceComplexification
        deningerIntegralCartierSecondInverseLatticeClass =
      sourceHorizontalBilateralSecondJetInverse := by
  rw [deningerIntegralCartierSecondInverseLatticeClass,
    deningerIntegralCartierSecondSourceComplexification_coordinate]
  ext <;> simp [sourceHorizontalBilateralSecondJetIntegralCoordinates,
    sourceHorizontalBilateralSecondJetInverse]

@[simp] theorem deningerIntegralCartierSecondSourceComplexification_ghost :
    deningerIntegralCartierSecondSourceComplexification
        deningerIntegralCartierSecondGhostLatticeClass =
      sourceHorizontalBilateralSecondJetGhost := by
  rw [deningerIntegralCartierSecondGhostLatticeClass,
    deningerIntegralCartierSecondSourceComplexification_coordinate]
  ext <;> simp [sourceHorizontalBilateralSecondJetIntegralCoordinates,
    sourceHorizontalBilateralSecondJetGhost]

/-- Coefficient-faithful realization of both source orientations as the two Hardy chambers. -/
def sourceHorizontalBilateralSecondJetHardyDescent (lam : ℂ) :
    SourceHorizontalBilateralSecondJetSource →ₗ[ℂ] (ℤ → ℂ) where
  toFun v e :=
    v.1 * hardyPositiveHalf lam e + v.2 * hardyNegativeHalf lam e
  map_add' x y := by
    funext e
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext e
    simp [mul_add, mul_assoc]

/-- Continuous realization of the rank-two complex source topology in the product topology on
bilateral Hardy sequences. -/
noncomputable def sourceHorizontalBilateralSecondJetHardyContinuousDescent
    (lam : ℂ) :
    SourceHorizontalBilateralSecondJetSource →L[ℂ] (ℤ → ℂ) :=
  ContinuousLinearMap.mk
    (sourceHorizontalBilateralSecondJetHardyDescent lam)
    (LinearMap.continuous_of_finiteDimensional _)

@[simp] theorem sourceHorizontalBilateralSecondJetHardyDescent_forward
    (lam : ℂ) :
    sourceHorizontalBilateralSecondJetHardyDescent lam
        sourceHorizontalBilateralSecondJetForward =
      hardyPositiveHalf lam := by
  funext e
  simp [sourceHorizontalBilateralSecondJetHardyDescent,
    sourceHorizontalBilateralSecondJetForward]

@[simp] theorem sourceHorizontalBilateralSecondJetHardyDescent_inverse
    (lam : ℂ) :
    sourceHorizontalBilateralSecondJetHardyDescent lam
        sourceHorizontalBilateralSecondJetInverse =
      hardyNegativeHalf lam := by
  funext e
  simp [sourceHorizontalBilateralSecondJetHardyDescent,
    sourceHorizontalBilateralSecondJetInverse]

/-- The complex quadratic ghost is the sum of the two independent orientations. -/
theorem sourceHorizontalBilateralSecondJetGhost_eq_add :
    sourceHorizontalBilateralSecondJetGhost =
      sourceHorizontalBilateralSecondJetForward +
        sourceHorizontalBilateralSecondJetInverse := by
  ext <;> simp [sourceHorizontalBilateralSecondJetGhost,
    sourceHorizontalBilateralSecondJetForward,
    sourceHorizontalBilateralSecondJetInverse]

/-- The quadratic ghost realizes the complete bilateral eigenfamily. -/
@[simp] theorem sourceHorizontalBilateralSecondJetHardyDescent_ghost
    (lam : ℂ) :
    sourceHorizontalBilateralSecondJetHardyDescent lam
        sourceHorizontalBilateralSecondJetGhost =
      bilateralEigenFamily lam := by
  rw [sourceHorizontalBilateralSecondJetGhost_eq_add, map_add,
    sourceHorizontalBilateralSecondJetHardyDescent_forward,
    sourceHorizontalBilateralSecondJetHardyDescent_inverse,
    hardyPositiveHalf_add_hardyNegativeHalf]

/-- Hardy descent whose domain is the literal Laurent quotient source lattice, not an unrelated
abstract vector space. -/
noncomputable def deningerIntegralCartierSecondSourceHardyDescent (lam : ℂ) :
    DeningerIntegralCartierSecondSourceLattice →+ (ℤ → ℂ) :=
  (sourceHorizontalBilateralSecondJetHardyDescent lam).toAddMonoidHom.comp
    deningerIntegralCartierSecondSourceComplexification

/-- Source complexification followed by Hardy descent is the canonical coefficient map on every
integral Laurent coordinate. -/
theorem deningerIntegralCartierSecondSourceHardyDescent_coordinate
    (lam : ℂ) (v : ℤ × ℤ) :
    deningerIntegralCartierSecondSourceHardyDescent lam
        (deningerIntegralCartierSecondCoordinateEquiv v) =
      sourceHorizontalBilateralSecondJetHardyDescent lam
        (sourceHorizontalBilateralSecondJetIntegralCoordinates v) := by
  simp [deningerIntegralCartierSecondSourceHardyDescent,
    deningerIntegralCartierSecondSourceComplexification_coordinate]

@[simp] theorem deningerIntegralCartierSecondSourceHardyDescent_forward
    (lam : ℂ) :
    deningerIntegralCartierSecondSourceHardyDescent lam
        deningerIntegralCartierSecondForwardLatticeClass =
      hardyPositiveHalf lam := by
  rw [deningerIntegralCartierSecondForwardLatticeClass,
    deningerIntegralCartierSecondSourceHardyDescent_coordinate]
  rw [show sourceHorizontalBilateralSecondJetIntegralCoordinates (1, 0) =
      sourceHorizontalBilateralSecondJetForward by
    ext <;> simp [sourceHorizontalBilateralSecondJetIntegralCoordinates,
      sourceHorizontalBilateralSecondJetForward]]
  exact sourceHorizontalBilateralSecondJetHardyDescent_forward lam

@[simp] theorem deningerIntegralCartierSecondSourceHardyDescent_inverse
    (lam : ℂ) :
    deningerIntegralCartierSecondSourceHardyDescent lam
        deningerIntegralCartierSecondInverseLatticeClass =
      hardyNegativeHalf lam := by
  rw [deningerIntegralCartierSecondInverseLatticeClass,
    deningerIntegralCartierSecondSourceHardyDescent_coordinate]
  rw [show sourceHorizontalBilateralSecondJetIntegralCoordinates (0, 1) =
      sourceHorizontalBilateralSecondJetInverse by
    ext <;> simp [sourceHorizontalBilateralSecondJetIntegralCoordinates,
      sourceHorizontalBilateralSecondJetInverse]]
  exact sourceHorizontalBilateralSecondJetHardyDescent_inverse lam

@[simp] theorem deningerIntegralCartierSecondSourceHardyDescent_ghost
    (lam : ℂ) :
    deningerIntegralCartierSecondSourceHardyDescent lam
        deningerIntegralCartierSecondGhostLatticeClass =
      bilateralEigenFamily lam := by
  rw [deningerIntegralCartierSecondGhostLatticeClass,
    deningerIntegralCartierSecondSourceHardyDescent_coordinate]
  rw [show sourceHorizontalBilateralSecondJetIntegralCoordinates (1, 1) =
      sourceHorizontalBilateralSecondJetGhost by
    ext <;> simp [sourceHorizontalBilateralSecondJetIntegralCoordinates,
      sourceHorizontalBilateralSecondJetGhost]]
  exact sourceHorizontalBilateralSecondJetHardyDescent_ghost lam

/-- The two Hardy chambers retain both source coordinates. -/
theorem sourceHorizontalBilateralSecondJetHardyDescent_injective
    {lam : ℂ} (hlam : lam ≠ 0) :
    Function.Injective (sourceHorizontalBilateralSecondJetHardyDescent lam) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrFun h 0
  have hm := congrFun h (-1)
  simp [sourceHorizontalBilateralSecondJetHardyDescent,
    hardyPositiveHalf, hardyNegativeHalf] at h0 hm
  have hbd : b = d := hm.resolve_right hlam
  exact Prod.ext h0 hbd

/-- The descent is faithful already on the literal integral Laurent source lattice. -/
theorem deningerIntegralCartierSecondSourceHardyDescent_injective
    {lam : ℂ} (hlam : lam ≠ 0) :
    Function.Injective (deningerIntegralCartierSecondSourceHardyDescent lam) :=
  (sourceHorizontalBilateralSecondJetHardyDescent_injective hlam).comp
    deningerIntegralCartierSecondSourceComplexification_injective

/-- Linear equivalence onto the induced non-scalar Hardy source topology. -/
noncomputable def sourceHorizontalBilateralSecondJetHardyDescentEquiv
    {lam : ℂ} (hlam : lam ≠ 0) :
    SourceHorizontalBilateralSecondJetSource ≃ₗ[ℂ]
      LinearMap.range (sourceHorizontalBilateralSecondJetHardyDescent lam) :=
  LinearEquiv.ofInjective _
    (sourceHorizontalBilateralSecondJetHardyDescent_injective hlam)

/-- The induced Hardy source topology is genuinely two-dimensional. -/
theorem finrank_sourceHorizontalBilateralSecondJetHardyDescent_range
    {lam : ℂ} (hlam : lam ≠ 0) :
    Module.finrank ℂ
        (LinearMap.range (sourceHorizontalBilateralSecondJetHardyDescent lam)) = 2 := by
  rw [← LinearEquiv.finrank_eq
    (sourceHorizontalBilateralSecondJetHardyDescentEquiv hlam)]
  simp

/-- The quadratic source character is literally Stokes-flat at every nonzero grade. -/
theorem sourceHorizontalBilateralSecondJetHardyDescent_ghost_stokesFlat
    {lam : ℂ} (hlam : lam ≠ 0) :
    bilateralSewing lam
        (sourceHorizontalBilateralSecondJetHardyDescent lam
          sourceHorizontalBilateralSecondJetGhost) = 0 := by
  rw [sourceHorizontalBilateralSecondJetHardyDescent_ghost]
  exact bilateralSewing_eigenFamily hlam

/-- Sharp physical firewall: the non-scalar ghost is fixed-circle moderate exactly at unit
character modulus. -/
theorem sourceHorizontalBilateralSecondJetHardyDescent_ghost_moderate_iff
    {lam : ℂ} (hlam : lam ≠ 0) :
    bilateralModerate
        (sourceHorizontalBilateralSecondJetHardyDescent lam
          sourceHorizontalBilateralSecondJetGhost) ↔
      ‖lam‖ = 1 := by
  rw [sourceHorizontalBilateralSecondJetHardyDescent_ghost]
  constructor
  · intro hmod
    by_contra hnorm
    have hzero := bilateral_shift_eigen_eq_zero_of_norm_ne_one hnorm hmod (by
      intro e
      simp only [bilateralEigenFamily]
      rw [show -(e - 1) = 1 + -e by ring, zpow_add₀ hlam, zpow_one])
    have hne : bilateralEigenFamily lam ≠ 0 := by
      intro hz
      have hzero0 := congrFun hz 0
      simp [bilateralEigenFamily] at hzero0
    exact hne hzero
  · intro hnorm
    refine ⟨1, 0, fun e => ?_⟩
    simp [bilateralEigenFamily, norm_zpow, hnorm]

/-- Simultaneous physical moderation of the two separately retained source orientations is still
the sharp unit-character condition.  Non-scalar admission therefore does not smuggle in RH. -/
theorem sourceHorizontalBilateralSecondJetHardyDescent_orientations_moderate_iff
    {lam : ℂ} (hlam : lam ≠ 0) :
    (bilateralModerate
        (sourceHorizontalBilateralSecondJetHardyDescent lam
          sourceHorizontalBilateralSecondJetForward) ∧
      bilateralModerate
        (sourceHorizontalBilateralSecondJetHardyDescent lam
          sourceHorizontalBilateralSecondJetInverse)) ↔
      ‖lam‖ = 1 := by
  rw [sourceHorizontalBilateralSecondJetHardyDescent_forward,
    sourceHorizontalBilateralSecondJetHardyDescent_inverse,
    hardyHalves_both_moderate_iff hlam]

/-! ## Literal endpoint-scaled descent -/

/-- The rank-two Hardy source descent after the literal Euler--Wold endpoint scaling. -/
def sourceHorizontalEndpointSecondJetHardyDescent
    (c : ℂ) (N : ℕ) (lam : ℂ) :
    SourceHorizontalBilateralSecondJetSource →ₗ[ℂ] (ℤ → ℂ) where
  toFun v e :=
    (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ) *
      sourceHorizontalBilateralSecondJetHardyDescent lam v e
  map_add' x y := by
    funext e
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext e
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem sourceHorizontalEndpointSecondJetHardyDescent_forward
    (c : ℂ) (N : ℕ) (lam : ℂ) :
    sourceHorizontalEndpointSecondJetHardyDescent c N lam
        sourceHorizontalBilateralSecondJetForward =
      sourceHorizontalEndpointScaledHardyPositiveHalf c N lam := by
  funext e
  simp [sourceHorizontalEndpointSecondJetHardyDescent,
    sourceHorizontalEndpointScaledHardyPositiveHalf]

@[simp] theorem sourceHorizontalEndpointSecondJetHardyDescent_inverse
    (c : ℂ) (N : ℕ) (lam : ℂ) :
    sourceHorizontalEndpointSecondJetHardyDescent c N lam
        sourceHorizontalBilateralSecondJetInverse =
      sourceHorizontalEndpointScaledHardyNegativeHalf c N lam := by
  funext e
  simp [sourceHorizontalEndpointSecondJetHardyDescent,
    sourceHorizontalEndpointScaledHardyNegativeHalf]

/-- Endpoint scaling preserves the nonlinear source relation. -/
theorem sourceHorizontalEndpointSecondJetHardyDescent_ghost
    (c : ℂ) (N : ℕ) (lam : ℂ) :
    sourceHorizontalEndpointSecondJetHardyDescent c N lam
        sourceHorizontalBilateralSecondJetGhost =
      sourceHorizontalEndpointScaledHardyPositiveHalf c N lam +
        sourceHorizontalEndpointScaledHardyNegativeHalf c N lam := by
  rw [sourceHorizontalBilateralSecondJetGhost_eq_add, map_add,
    sourceHorizontalEndpointSecondJetHardyDescent_forward,
    sourceHorizontalEndpointSecondJetHardyDescent_inverse]

/-- A nonzero endpoint scale retains both source coordinates. -/
theorem sourceHorizontalEndpointSecondJetHardyDescent_injective
    {c : ℂ} {N : ℕ} {lam : ℂ}
    (hscale : sourceHorizontalWoldBVKreinGhostEnergy c N ≠ 0)
    (hlam : lam ≠ 0) :
    Function.Injective (sourceHorizontalEndpointSecondJetHardyDescent c N lam) := by
  intro x y hxy
  apply sourceHorizontalBilateralSecondJetHardyDescent_injective hlam
  funext e
  have he := congrFun hxy e
  simp only [sourceHorizontalEndpointSecondJetHardyDescent,
    LinearMap.coe_mk, AddHom.coe_mk] at he
  exact mul_left_cancel₀ (by exact_mod_cast hscale) he

/-- The endpoint-scaled induced source topology remains rank two. -/
theorem finrank_sourceHorizontalEndpointSecondJetHardyDescent_range
    {c : ℂ} {N : ℕ} {lam : ℂ}
    (hscale : sourceHorizontalWoldBVKreinGhostEnergy c N ≠ 0)
    (hlam : lam ≠ 0) :
    Module.finrank ℂ
        (LinearMap.range (sourceHorizontalEndpointSecondJetHardyDescent c N lam)) = 2 := by
  let e : SourceHorizontalBilateralSecondJetSource ≃ₗ[ℂ]
      LinearMap.range (sourceHorizontalEndpointSecondJetHardyDescent c N lam) :=
    LinearEquiv.ofInjective _
      (sourceHorizontalEndpointSecondJetHardyDescent_injective hscale hlam)
  rw [← LinearEquiv.finrank_eq e]
  simp

/-- Endpoint scaling leaves the quadratic source character Stokes-flat. -/
theorem sourceHorizontalEndpointSecondJetHardyDescent_ghost_stokesFlat
    (c : ℂ) (N : ℕ) {lam : ℂ} (hlam : lam ≠ 0) :
    bilateralSewing lam
        (sourceHorizontalEndpointSecondJetHardyDescent c N lam
          sourceHorizontalBilateralSecondJetGhost) = 0 := by
  change bilateralSewing lam (fun e =>
    (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ) *
      sourceHorizontalBilateralSecondJetHardyDescent lam
        sourceHorizontalBilateralSecondJetGhost e) = 0
  rw [bilateralSewing_const_mul,
    sourceHorizontalBilateralSecondJetHardyDescent_ghost,
    bilateralSewing_eigenFamily hlam]
  funext e
  simp

/-- Nonzero endpoint scaling does not hide the exact moderation threshold of the quadratic
source character. -/
theorem sourceHorizontalEndpointSecondJetHardyDescent_ghost_moderate_iff
    {c : ℂ} {N : ℕ} {lam : ℂ}
    (hscale : sourceHorizontalWoldBVKreinGhostEnergy c N ≠ 0)
    (hlam : lam ≠ 0) :
    bilateralModerate
        (sourceHorizontalEndpointSecondJetHardyDescent c N lam
          sourceHorizontalBilateralSecondJetGhost) ↔
      ‖lam‖ = 1 := by
  change bilateralModerate (fun e =>
    (sourceHorizontalWoldBVKreinGhostEnergy c N : ℂ) *
      sourceHorizontalBilateralSecondJetHardyDescent lam
        sourceHorizontalBilateralSecondJetGhost e) ↔ _
  rw [bilateralModerate_const_mul_iff (by exact_mod_cast hscale),
    sourceHorizontalBilateralSecondJetHardyDescent_ghost_moderate_iff hlam]

/-! ## Actual Xi divisor and multiplicity fidelity -/

/-- Actual Gamma--Julia Xi endpoint descent on one retained support copy. -/
def sourceHorizontalActualXiEndpointSecondJetHardyDescent
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) (p : Nat.Primes) :
    SourceHorizontalBilateralSecondJetSource →ₗ[ℂ] (ℤ → ℂ) :=
  sourceHorizontalEndpointSecondJetHardyDescent
    (sourceHorizontalActualXiConormalCoefficient x u q r) N
    (bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport))

/-- Actual Xi/Gamma--Julia endpoint descent with the literal second-Cartier Laurent source lattice
as its domain.  This composite is the promised source-topology map; the `ℂ × ℂ` map above is
its canonical complex realization. -/
noncomputable def sourceHorizontalActualXiEndpointSecondCartierHardyDescent
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) (p : Nat.Primes) :
    DeningerIntegralCartierSecondSourceLattice →+ (ℤ → ℂ) :=
  (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p).toAddMonoidHom.comp
    deningerIntegralCartierSecondSourceComplexification

theorem sourceHorizontalActualXiEndpointSecondJetHardyDescent_forward
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) (p : Nat.Primes) :
    sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
        sourceHorizontalBilateralSecondJetForward =
      sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u q r N p := by
  rw [sourceHorizontalActualXiEndpointSecondJetHardyDescent,
    sourceHorizontalEndpointSecondJetHardyDescent_forward]
  rfl

theorem sourceHorizontalActualXiEndpointSecondJetHardyDescent_inverse
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) (p : Nat.Primes) :
    sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
        sourceHorizontalBilateralSecondJetInverse =
      sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u q r N p := by
  rw [sourceHorizontalActualXiEndpointSecondJetHardyDescent,
    sourceHorizontalEndpointSecondJetHardyDescent_inverse]
  rfl

@[simp] theorem sourceHorizontalActualXiEndpointSecondCartierHardyDescent_forward
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) (p : Nat.Primes) :
    sourceHorizontalActualXiEndpointSecondCartierHardyDescent x u q r N p
        deningerIntegralCartierSecondForwardLatticeClass =
      sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u q r N p := by
  simp [sourceHorizontalActualXiEndpointSecondCartierHardyDescent,
    sourceHorizontalActualXiEndpointSecondJetHardyDescent_forward]

@[simp] theorem sourceHorizontalActualXiEndpointSecondCartierHardyDescent_inverse
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) (p : Nat.Primes) :
    sourceHorizontalActualXiEndpointSecondCartierHardyDescent x u q r N p
        deningerIntegralCartierSecondInverseLatticeClass =
      sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u q r N p := by
  simp [sourceHorizontalActualXiEndpointSecondCartierHardyDescent,
    sourceHorizontalActualXiEndpointSecondJetHardyDescent_inverse]

@[simp] theorem sourceHorizontalActualXiEndpointSecondCartierHardyDescent_ghost
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) (p : Nat.Primes) :
    sourceHorizontalActualXiEndpointSecondCartierHardyDescent x u q r N p
        deningerIntegralCartierSecondGhostLatticeClass =
      sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u q r N p +
        sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u q r N p := by
  simp [sourceHorizontalActualXiEndpointSecondCartierHardyDescent,
    sourceHorizontalEndpointSecondJetHardyDescent_ghost,
    sourceHorizontalActualXiEndpointSecondJetHardyDescent]
  rfl

/-- A nonzero Xi endpoint coefficient makes the literal source-lattice descent faithful. -/
theorem sourceHorizontalActualXiEndpointSecondCartierHardyDescent_injective
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    Function.Injective
      (sourceHorizontalActualXiEndpointSecondCartierHardyDescent x u q r N p) := by
  let c := sourceHorizontalActualXiConormalCoefficient x u q r
  let lam := bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport)
  have hc : c ≠ 0 :=
    sourceHorizontalActualXiConormalCoefficient_ne_zero q hkappa hr
  have hscale : sourceHorizontalWoldBVKreinGhostEnergy c N ≠ 0 := by
    exact ne_of_gt (mul_pos (mul_pos (by norm_num)
      (Complex.normSq_pos.mpr hc)) hjet)
  have hp0 : 0 < (p : ℕ) := lt_of_lt_of_le two_pos p.2.two_le
  have hlam : lam ≠ 0 := bilateralHalfDensityCharacter_ne_zero hp0 _
  exact (sourceHorizontalEndpointSecondJetHardyDescent_injective
    hscale hlam).comp deningerIntegralCartierSecondSourceComplexification_injective

/-- Actual quadratic source ghost on one Xi support copy. -/
def sourceHorizontalActualXiEndpointScaledHardyGhost
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) (p : Nat.Primes) :
    ℤ → ℂ :=
  sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u q r N p +
    sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u q r N p

/-- Summing the non-scalar ghost over the actual support fibre restores analytic multiplicity. -/
theorem sourceHorizontalActualXiEndpointScaledHardyGhost_fiber_sum
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) (p : Nat.Primes) :
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiEndpointScaledHardyGhost x u s.1 r N p) =
        xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiEndpointScaledHardyGhost x u q r N p := by
  simp_rw [sourceHorizontalActualXiEndpointScaledHardyGhost]
  rw [Finset.sum_add_distrib,
    sourceHorizontalActualXiEndpointScaledHardyPositiveHalf_fiber_sum,
    sourceHorizontalActualXiEndpointScaledHardyNegativeHalf_fiber_sum,
    smul_add]

/-- **Capstone.** Every actual strict-right Xi copy has an injective rank-two source-topology
descent carrying both literal endpoint-scaled Hardy orientations. Their nonzero quadratic source
ghost is Stokes-flat and multiplicity-faithful, but it is not a fixed-circle moderate distribution.
Thus simultaneous non-scalar admission is constructed without pretending that its remaining
physical moderation law is automatic. -/
theorem sourceHorizontalActualXiEndpointSecondJetHardyDescent_capstone
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    Function.Injective
        (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p) ∧
      Module.finrank ℂ
        (LinearMap.range
          (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p)) = 2 ∧
      sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
          sourceHorizontalBilateralSecondJetGhost =
        sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u q r N p +
          sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u q r N p ∧
      bilateralSewing
        (bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport))
        (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
          sourceHorizontalBilateralSecondJetGhost) = 0 ∧
      ¬ bilateralModerate
        (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
          sourceHorizontalBilateralSecondJetGhost) ∧
      (∑ s : XiRightSupportFiber q,
        sourceHorizontalActualXiEndpointScaledHardyGhost x u s.1 r N p) =
          xiSupportMultiplicity q.1.1 •
            sourceHorizontalActualXiEndpointScaledHardyGhost x u q r N p := by
  let c := sourceHorizontalActualXiConormalCoefficient x u q r
  let lam := bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport)
  have hc : c ≠ 0 :=
    sourceHorizontalActualXiConormalCoefficient_ne_zero q hkappa hr
  have hscale : sourceHorizontalWoldBVKreinGhostEnergy c N ≠ 0 := by
    exact ne_of_gt (mul_pos (mul_pos (by norm_num)
      (Complex.normSq_pos.mpr hc)) hjet)
  have hp0 : 0 < (p : ℕ) := lt_of_lt_of_le two_pos p.2.two_le
  have hlam : lam ≠ 0 := bilateralHalfDensityCharacter_ne_zero hp0 _
  have hright : 1 / 2 < ((q.1.1 : XiDivisorSupport) : ℂ).re := by
    have hcenter := xiRightCenteredZero_re_pos q
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hcenter
    norm_num at hcenter ⊢
    linarith
  have hnorm : ‖lam‖ ≠ 1 := by
    intro h
    have hline := (norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le
      (q.1.1 : XiDivisorSupport)).1 h
    linarith
  refine ⟨sourceHorizontalEndpointSecondJetHardyDescent_injective hscale hlam,
    finrank_sourceHorizontalEndpointSecondJetHardyDescent_range hscale hlam,
    ?_, ?_, ?_,
    sourceHorizontalActualXiEndpointScaledHardyGhost_fiber_sum x u q r N p⟩
  · exact sourceHorizontalEndpointSecondJetHardyDescent_ghost c N lam
  · exact sourceHorizontalEndpointSecondJetHardyDescent_ghost_stokesFlat c N hlam
  · intro hmod
    apply hnorm
    apply
      (sourceHorizontalEndpointSecondJetHardyDescent_ghost_moderate_iff
        hscale hlam).1
    simpa [sourceHorizontalActualXiEndpointSecondJetHardyDescent, c, lam] using hmod

/-- **Literal-source capstone.** Every actual strict-right Xi copy admits both Hardy orientations
simultaneously through one injective map whose domain is the nonzero rank-two Laurent source
lattice in `R / I³`.  The quadratic source class maps to their Stokes-flat sum, and analytic
multiplicity is preserved.  Its off-line image is nevertheless non-moderate, so this theorem
constructs the missing non-scalar descent without assuming the remaining physical order law. -/
theorem sourceHorizontalActualXiEndpointSecondCartierHardyDescent_capstone
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    deningerIntegralCartierSecondGhostLatticeClass ≠ 0 ∧
      Function.Injective
        (sourceHorizontalActualXiEndpointSecondCartierHardyDescent x u q r N p) ∧
      sourceHorizontalActualXiEndpointSecondCartierHardyDescent x u q r N p
          deningerIntegralCartierSecondForwardLatticeClass =
        sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u q r N p ∧
      sourceHorizontalActualXiEndpointSecondCartierHardyDescent x u q r N p
          deningerIntegralCartierSecondInverseLatticeClass =
        sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u q r N p ∧
      sourceHorizontalActualXiEndpointSecondCartierHardyDescent x u q r N p
          deningerIntegralCartierSecondGhostLatticeClass =
        sourceHorizontalActualXiEndpointScaledHardyPositiveHalf x u q r N p +
          sourceHorizontalActualXiEndpointScaledHardyNegativeHalf x u q r N p ∧
      bilateralSewing
        (bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport))
        (sourceHorizontalActualXiEndpointSecondCartierHardyDescent x u q r N p
          deningerIntegralCartierSecondGhostLatticeClass) = 0 ∧
      ¬ bilateralModerate
        (sourceHorizontalActualXiEndpointSecondCartierHardyDescent x u q r N p
          deningerIntegralCartierSecondGhostLatticeClass) ∧
      (∑ s : XiRightSupportFiber q,
        sourceHorizontalActualXiEndpointScaledHardyGhost x u s.1 r N p) =
          xiSupportMultiplicity q.1.1 •
            sourceHorizontalActualXiEndpointScaledHardyGhost x u q r N p := by
  rcases sourceHorizontalActualXiEndpointSecondJetHardyDescent_capstone
      q hkappa hr N hjet p with
    ⟨_, _, hghost, hstokes, hnotModerate, hfiber⟩
  refine ⟨deningerIntegralCartierSecondGhostLatticeClass_ne_zero,
    sourceHorizontalActualXiEndpointSecondCartierHardyDescent_injective
      q hkappa hr N hjet p,
    sourceHorizontalActualXiEndpointSecondCartierHardyDescent_forward x u q r N p,
    sourceHorizontalActualXiEndpointSecondCartierHardyDescent_inverse x u q r N p,
    sourceHorizontalActualXiEndpointSecondCartierHardyDescent_ghost x u q r N p,
    ?_, ?_, hfiber⟩
  · rw [sourceHorizontalActualXiEndpointSecondCartierHardyDescent_ghost,
      ← hghost]
    exact hstokes
  · rw [sourceHorizontalActualXiEndpointSecondCartierHardyDescent_ghost,
      ← hghost]
    exact hnotModerate

end

end RHTower
