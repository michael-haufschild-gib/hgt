import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorLimitCarriesACyclicDilationAction
import GaloisForLFunctions.ArithmeticOrientationTheory.BoundedMultiplicativeSequencesActOnWienerAlgebras

/-!
# Wiener integration of the actual cofactor action

The integer dilation operators extend to the critical Wiener algebra by their
absolutely convergent coefficient series.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity.CofactorLimit

/-- Extend the positive-integer dilation sequence by zero at the unused index zero. -/
def naturalDilation (ε : SubcriticalDamping) (n : ℕ) : Hilbert ε →L[ℂ] Hilbert ε :=
  if h : 0 < n then dilation ε ⟨n, h⟩ else 0

open Finset
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.HTGeometry
open WienerAlgebraAt

theorem naturalDilation_zero (ε : SubcriticalDamping) : naturalDilation ε 0 = 0 := by
  simp only [naturalDilation, lt_self_iff_false, dif_neg]

theorem naturalDilation_pos (ε : SubcriticalDamping) (n : ℕ) (hn : 0 < n) :
    naturalDilation ε n = dilation ε ⟨n, hn⟩ := dif_pos hn

theorem naturalDilation_one (ε : SubcriticalDamping) : naturalDilation ε 1 = 1 := by
  rw [naturalDilation_pos ε 1 Nat.zero_lt_one]
  exact dilation_one ε

theorem naturalDilation_mul (ε : SubcriticalDamping) (m n : ℕ) :
    naturalDilation ε (m * n) = naturalDilation ε m * naturalDilation ε n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_mul, naturalDilation_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [mul_zero, naturalDilation_zero]
  rw [naturalDilation_pos ε m hm, naturalDilation_pos ε n hn,
    naturalDilation_pos ε (m * n) (Nat.mul_pos hm hn)]
  exact (dilation_mul ε ⟨m, hm⟩ ⟨n, hn⟩).symm

theorem norm_naturalDilation_le (ε : SubcriticalDamping) (n : ℕ) (hn : n ≠ 0) :
    ‖naturalDilation ε n‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [naturalDilation_pos ε n (Nat.pos_of_ne_zero hn)]
  calc
    _ ≤ 1 / Real.sqrt (n : ℝ) := norm_dilation_le ε ⟨n, Nat.pos_of_ne_zero hn⟩
    _ = _ := by rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg n), one_div]

/-- The actual cofactor action integrated over every critical Wiener kernel. -/
def wienerRepresentation (ε : SubcriticalDamping) :
    WienerAlgebraAt (1 / 2) →ₐ[ℂ] (Hilbert ε →L[ℂ] Hilbert ε) :=
  sequenceRepresentation (naturalDilation ε) (naturalDilation_zero ε)
    (norm_naturalDilation_le ε) (naturalDilation_one ε) (naturalDilation_mul ε)

/-- The same representation with its norm-continuous linear structure explicit. -/
def wienerLinear (ε : SubcriticalDamping) :
    WienerAlgebraAt (1 / 2) →L[ℂ] (Hilbert ε →L[ℂ] Hilbert ε) :=
  sequenceExtension (naturalDilation ε) (naturalDilation_zero ε) (norm_naturalDilation_le ε)

theorem wienerRepresentation_eq_linear (ε : SubcriticalDamping) (a : WienerAlgebraAt (1 / 2)) :
    wienerRepresentation ε a = wienerLinear ε a := rfl

theorem wienerRepresentation_pointMass (ε : SubcriticalDamping) (p : ℕ+) :
    wienerRepresentation ε (pointMass p) = dilation ε p := by
  change sequenceExtension _ _ _ (pointMass p) = _
  rw [sequenceExtension_pointMass, naturalDilation_pos ε p p.property]

theorem norm_wienerRepresentation_le (ε : SubcriticalDamping) (a : WienerAlgebraAt (1 / 2)) :
    ‖wienerRepresentation ε a‖ ≤ ‖a‖ :=
  norm_tsum_coefficient_smul_le (naturalDilation ε) (naturalDilation_zero ε)
    (norm_naturalDilation_le ε) a

/-- The Wiener algebra's annihilator of the actual cofactor Hilbert space. -/
def annihilator (ε : SubcriticalDamping) : Ideal (WienerAlgebraAt (1 / 2)) :=
  RingHom.ker (wienerRepresentation ε).toRingHom

/-- Commutativity and cyclicity identify vector and operator annihilation. -/
theorem mem_annihilator_iff (ε : SubcriticalDamping) (a : WienerAlgebraAt (1 / 2)) :
    a ∈ annihilator ε ↔ wienerRepresentation ε a (vector ε 1) = 0 := by
  constructor
  · intro h
    change wienerRepresentation ε a = 0 at h
    rw [h]
    rfl
  · intro h
    change wienerRepresentation ε a = 0
    apply KernelHilbert.ext_on_vectors (complexKernel ε)
    intro p
    change wienerRepresentation ε a (vector ε p) = 0
    have hc : wienerRepresentation ε a * dilation ε p =
        dilation ε p * wienerRepresentation ε a := by
      rw [← wienerRepresentation_pointMass, ← map_mul, ← map_mul, mul_comm a]
    calc
      _ = (wienerRepresentation ε a * dilation ε p) (vector ε 1) := by
        rw [ContinuousLinearMap.mul_apply, dilation_vector, mul_one]
      _ = (dilation ε p * wienerRepresentation ε a) (vector ε 1) := by rw [hc]
      _ = 0 := by rw [ContinuousLinearMap.mul_apply, h, map_zero]

/-- Nonzero receiver mass makes the annihilator a proper ideal. -/
theorem annihilator_ne_top (ε : SubcriticalDamping) : annihilator ε ≠ ⊤ := by
  intro h
  have hmem : (1 : WienerAlgebraAt (1 / 2)) ∈ annihilator ε := h ▸ Submodule.mem_top
  have hz := (mem_annihilator_iff ε 1).mp hmem
  rw [map_one] at hz
  exact vector_one_ne_zero ε hz

/-- Continuity makes the module annihilator closed in the Wiener norm. -/
theorem annihilator_closed (ε : SubcriticalDamping) : IsClosed (annihilator ε : Set _) := by
  change IsClosed ((wienerLinear ε) ⁻¹' {(0 : Hilbert ε →L[ℂ] Hilbert ε)})
  exact isClosed_singleton.preimage (wienerLinear ε).continuous

/-- The spectral hull of the actual cofactor module. -/
def moduleHull (ε : SubcriticalDamping) : Set BohrPoint :=
  {ω | ∀ a ∈ annihilator ε, bohrEval (1 / 2) a.toFn ω = 0}

/-- Every actual cofactor limit has a nonempty spectral hull. -/
theorem moduleHull_nonempty (ε : SubcriticalDamping) : (moduleHull ε).Nonempty := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (annihilator_ne_top ε)
  letI := hM
  refine ⟨characterBohrPoint M.toCharacterSpace, fun a ha => ?_⟩
  rw [← apply_eq_bohrEval]
  exact M.toCharacterSpace_apply_eq_zero_of_mem (hle ha)

end GaloisForLFunctions.ArithmeticDefectRigidity.CofactorLimit
