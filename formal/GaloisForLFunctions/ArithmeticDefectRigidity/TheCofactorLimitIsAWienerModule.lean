import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorLimitCarriesACyclicDilationAction
import GaloisForLFunctions.ArithmeticOrientationTheory.BoundedMultiplicativeSequencesActOnWienerAlgebras

/-!
# Wiener integration of the actual cofactor action

The integer dilation operators extend to the critical Wiener algebra by their
absolutely convergent coefficient series.
-/

noncomputable section
set_option autoImplicit false


open Finset Filter Topology RHTower
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.HTGeometry
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- Extend the positive-integer dilation sequence by zero at the unused index zero. -/
def naturalDilation {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (n : ℕ) : Hilbert L →L[ℂ] Hilbert L :=
  if h : 0 < n then dilation L ⟨n, h⟩ else 0

open Finset
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.HTGeometry
open WienerAlgebraAt

theorem naturalDilation_zero {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) : naturalDilation L 0 = 0 := by
  exact dif_neg (Nat.not_lt_zero 0)

theorem naturalDilation_pos {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (n : ℕ) (hn : 0 < n) :
    naturalDilation L n = dilation L ⟨n, hn⟩ := dif_pos hn

theorem naturalDilation_one {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) : naturalDilation L 1 = 1 := by
  rw [naturalDilation_pos L 1 Nat.zero_lt_one]
  exact dilation_one L

theorem naturalDilation_mul {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (m n : ℕ) :
    naturalDilation L (m * n) = naturalDilation L m * naturalDilation L n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_mul, naturalDilation_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [mul_zero, naturalDilation_zero]
  rw [naturalDilation_pos L m hm, naturalDilation_pos L n hn,
    naturalDilation_pos L (m * n) (Nat.mul_pos hm hn)]
  exact (dilation_mul L ⟨m, hm⟩ ⟨n, hn⟩).symm

theorem norm_naturalDilation_le {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (n : ℕ) (hn : n ≠ 0) :
    ‖naturalDilation L n‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [naturalDilation_pos L n (Nat.pos_of_ne_zero hn)]
  calc
    _ ≤ 1 / Real.sqrt (n : ℝ) := norm_dilation_le L ⟨n, Nat.pos_of_ne_zero hn⟩
    _ = _ := by rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg n), one_div]

/-- The actual cofactor action integrated over every critical Wiener kernel. -/
def wienerRepresentation {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    WienerAlgebraAt (1 / 2) →ₐ[ℂ] (Hilbert L →L[ℂ] Hilbert L) :=
  sequenceRepresentation (naturalDilation L) (naturalDilation_zero L)
    (norm_naturalDilation_le L) (naturalDilation_one L) (naturalDilation_mul L)

/-- The same representation with its norm-continuous linear structure explicit. -/
def wienerLinear {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    WienerAlgebraAt (1 / 2) →L[ℂ] (Hilbert L →L[ℂ] Hilbert L) :=
  sequenceExtension (naturalDilation L) (naturalDilation_zero L) (norm_naturalDilation_le L)

theorem wienerRepresentation_eq_linear {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (a : WienerAlgebraAt (1 / 2)) :
    wienerRepresentation L a = wienerLinear L a := rfl

theorem wienerRepresentation_pointMass {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (p : ℕ+) :
    wienerRepresentation L (pointMass p) = dilation L p := by
  change sequenceExtension _ _ _ (pointMass p) = _
  rw [sequenceExtension_pointMass, naturalDilation_pos L p p.property]
  rfl

theorem norm_wienerRepresentation_le {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (a : WienerAlgebraAt (1 / 2)) :
    ‖wienerRepresentation L a‖ ≤ ‖a‖ :=
  norm_tsum_coefficient_smul_le (naturalDilation L) (naturalDilation_zero L)
    (norm_naturalDilation_le L) a

/-- The Wiener algebra's annihilator of the actual cofactor Hilbert space. -/
def annihilator {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) : Ideal (WienerAlgebraAt (1 / 2)) :=
  RingHom.ker (wienerRepresentation L).toRingHom

/-- Commutativity and cyclicity identify vector and operator annihilation. -/
theorem mem_annihilator_iff {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (a : WienerAlgebraAt (1 / 2)) :
    a ∈ annihilator L ↔ wienerRepresentation L a (vector L 1) = 0 := by
  constructor
  · intro h
    change wienerRepresentation L a = 0 at h
    rw [h]
    rfl
  · intro h
    change wienerRepresentation L a = 0
    apply KernelHilbert.ext_on_vectors (complexKernel L)
    intro p
    change wienerRepresentation L a (vector L p) = 0
    have hc : wienerRepresentation L a * dilation L p =
        dilation L p * wienerRepresentation L a := by
      rw [← wienerRepresentation_pointMass, ← map_mul, ← map_mul, mul_comm a]
    calc
      _ = (wienerRepresentation L a * dilation L p) (vector L 1) := by
        rw [mul_apply_eq_comp, dilation_vector, mul_one]
      _ = (dilation L p * wienerRepresentation L a) (vector L 1) := by rw [hc]
      _ = 0 := by rw [mul_apply_eq_comp, h, map_zero]

/-- Nonzero receiver mass makes the annihilator a proper ideal. -/
theorem annihilator_ne_top {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) : annihilator L ≠ ⊤ := by
  intro h
  have hmem : (1 : WienerAlgebraAt (1 / 2)) ∈ annihilator L := h ▸ Submodule.mem_top
  have hz := (mem_annihilator_iff L 1).mp hmem
  rw [map_one] at hz
  exact vector_one_ne_zero L hz

/-- Continuity makes the module annihilator closed in the Wiener norm. -/
theorem annihilator_closed {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    IsClosed (annihilator L : Set (WienerAlgebraAt (1 / 2))) := by
  change IsClosed ((wienerLinear L) ⁻¹' {(0 : Hilbert L →L[ℂ] Hilbert L)})
  exact isClosed_singleton.preimage (wienerLinear L).continuous

/-- The spectral hull of the actual cofactor module. -/
def moduleHull {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) : Set BohrPoint :=
  {ω | ∀ a ∈ annihilator L, ArithmeticOrientationTheory.bohrEval (1 / 2) a.toFn ω = 0}

/-- Every actual cofactor limit has a nonempty spectral hull. -/
theorem moduleHull_nonempty {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) : (moduleHull L).Nonempty := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (annihilator_ne_top L)
  letI := hM
  refine ⟨characterBohrPoint M.toCharacterSpace, fun a ha => ?_⟩
  rw [← apply_eq_bohrEval]
  exact M.toCharacterSpace_apply_eq_zero_of_mem (hle ha)


end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

namespace GaloisForLFunctions.ArithmeticDefectRigidity.CofactorLimit

abbrev naturalDilation (ε : SubcriticalDamping) (n : ℕ) : Hilbert ε →L[ℂ] Hilbert ε :=
  ActualCofactorLimit.naturalDilation (ActualCofactorLimit.chosen ε) n

theorem naturalDilation_zero (ε : SubcriticalDamping) : naturalDilation ε 0 = 0 :=
  ActualCofactorLimit.naturalDilation_zero (ActualCofactorLimit.chosen ε)

theorem naturalDilation_pos (ε : SubcriticalDamping) (n : ℕ) (hn : 0 < n) :
    naturalDilation ε n = dilation ε ⟨n, hn⟩ :=
  ActualCofactorLimit.naturalDilation_pos (ActualCofactorLimit.chosen ε) n hn

theorem naturalDilation_one (ε : SubcriticalDamping) : naturalDilation ε 1 = 1 :=
  ActualCofactorLimit.naturalDilation_one (ActualCofactorLimit.chosen ε)

theorem naturalDilation_mul (ε : SubcriticalDamping) (m n : ℕ) :
    naturalDilation ε (m * n) = naturalDilation ε m * naturalDilation ε n :=
  ActualCofactorLimit.naturalDilation_mul (ActualCofactorLimit.chosen ε) m n

theorem norm_naturalDilation_le (ε : SubcriticalDamping) (n : ℕ) (hn : n ≠ 0) :
    ‖naturalDilation ε n‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
  ActualCofactorLimit.norm_naturalDilation_le (ActualCofactorLimit.chosen ε) n hn

abbrev wienerRepresentation (ε : SubcriticalDamping) :
    WienerAlgebraAt (1 / 2) →ₐ[ℂ] (Hilbert ε →L[ℂ] Hilbert ε) :=
  ActualCofactorLimit.wienerRepresentation (ActualCofactorLimit.chosen ε)

abbrev wienerLinear (ε : SubcriticalDamping) :
    WienerAlgebraAt (1 / 2) →L[ℂ] (Hilbert ε →L[ℂ] Hilbert ε) :=
  ActualCofactorLimit.wienerLinear (ActualCofactorLimit.chosen ε)

theorem wienerRepresentation_eq_linear (ε : SubcriticalDamping) (a : WienerAlgebraAt (1 / 2)) :
    wienerRepresentation ε a = wienerLinear ε a :=
  ActualCofactorLimit.wienerRepresentation_eq_linear (ActualCofactorLimit.chosen ε) a

theorem wienerRepresentation_pointMass (ε : SubcriticalDamping) (p : ℕ+) :
    wienerRepresentation ε (pointMass p) = dilation ε p :=
  ActualCofactorLimit.wienerRepresentation_pointMass (ActualCofactorLimit.chosen ε) p

theorem norm_wienerRepresentation_le (ε : SubcriticalDamping) (a : WienerAlgebraAt (1 / 2)) :
    ‖wienerRepresentation ε a‖ ≤ ‖a‖ :=
  ActualCofactorLimit.norm_wienerRepresentation_le (ActualCofactorLimit.chosen ε) a

abbrev annihilator (ε : SubcriticalDamping) : Ideal (WienerAlgebraAt (1 / 2)) :=
  ActualCofactorLimit.annihilator (ActualCofactorLimit.chosen ε)

theorem mem_annihilator_iff (ε : SubcriticalDamping) (a : WienerAlgebraAt (1 / 2)) :
    a ∈ annihilator ε ↔ wienerRepresentation ε a (vector ε 1) = 0 :=
  ActualCofactorLimit.mem_annihilator_iff (ActualCofactorLimit.chosen ε) a

theorem annihilator_ne_top (ε : SubcriticalDamping) : annihilator ε ≠ ⊤ :=
  ActualCofactorLimit.annihilator_ne_top (ActualCofactorLimit.chosen ε)

theorem annihilator_closed (ε : SubcriticalDamping) :
    IsClosed (annihilator ε : Set (WienerAlgebraAt (1 / 2))) :=
  ActualCofactorLimit.annihilator_closed (ActualCofactorLimit.chosen ε)

abbrev moduleHull (ε : SubcriticalDamping) : Set BohrPoint :=
  ActualCofactorLimit.moduleHull (ActualCofactorLimit.chosen ε)

theorem moduleHull_nonempty (ε : SubcriticalDamping) : (moduleHull ε).Nonempty :=
  ActualCofactorLimit.moduleHull_nonempty (ActualCofactorLimit.chosen ε)

end GaloisForLFunctions.ArithmeticDefectRigidity.CofactorLimit
