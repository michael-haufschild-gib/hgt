import GaloisForLFunctions.RHTower.DeningerTateGraphGreenPrimeSector
import GaloisForLFunctions.RHTower.DeningerArithmeticPositiveCalderonKoszul
import GaloisForLFunctions.RHTower.SeamSpectrumDensity

/-!
# Prime/Kummer coercivity localization for Deninger's arithmetic Hodge route

Tate normalization gives every nonconstant prime-circle mode the same lower spectral gap `2π`.
The gap survives arbitrary finite incidence compression.  In contrast, signed multi-prime Kummer
frequencies form the gapless prime-log lattice.  Thus nonuniform incidence cohomology cannot be
created by isolated prime oscillations; it must see the Kummer/horizontal sector, cross-sector
coupling, or a failure of transition compatibility.

These are the unconditional quantitative statements behind
`DAC_PRIME_KUMMER_COERCIVITY_LOCALIZATION`.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

/-- Every nonconstant Tate-normalized prime-circle mode has the prime-independent gap `2π`. -/
theorem deningerTateCircleModeRate_succ_gap (k : ℕ) :
    2 * Real.pi ≤ deningerTateCircleModeRate (k + 1) := by
  simp only [deningerTateCircleModeRate, Nat.cast_add, Nat.cast_one]
  have hpi : 0 < 2 * Real.pi := mul_pos zero_lt_two Real.pi_pos
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

/-- Squared mass of a finite packet of nonconstant Tate-normalized circle modes. -/
def deningerTatePacketMass {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ i, (a i) ^ 2

/-- Positive-generator energy of a finite packet, indexed from its first nonconstant mode. -/
def deningerTatePacketEnergy {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ i, deningerTateCircleModeRate (i.1 + 1) * (a i) ^ 2

/-- Every finite Tate packet is uniformly coercive with gap `2π`. -/
theorem deningerTatePacketEnergy_uniform_coercive {n : ℕ} (a : Fin n → ℝ) :
    2 * Real.pi * deningerTatePacketMass a ≤ deningerTatePacketEnergy a := by
  rw [deningerTatePacketMass, deningerTatePacketEnergy, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right
      (deningerTateCircleModeRate_succ_gap i.1) (sq_nonneg (a i))

section Compression

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Compression of a finite-dimensional operator to an incidence subspace. -/
def deningerIncidenceCompression (A : E →ₗ[ℝ] E) (L : Submodule ℝ E) : L →ₗ[ℝ] L :=
  L.orthogonalProjectionOnto.toLinearMap.comp (A.comp L.subtype)

/-- Orthogonal compression preserves the quadratic form on the incidence subspace. -/
theorem deningerIncidenceCompression_inner_eq
    (A : E →ₗ[ℝ] E) (L : Submodule ℝ E) (x : L) :
    inner ℝ (deningerIncidenceCompression A L x) x =
      inner ℝ (A (x : E)) (x : E) := by
  change inner ℝ (L.orthogonalProjectionOnto (A (x : E))) x = _
  rw [L.inner_orthogonalProjectionOnto_eq_of_mem_right]

/-- A coercive operator stays quantitatively bounded below after arbitrary incidence compression. -/
theorem deningerIncidenceCompression_norm_lower
    (A : E →ₗ[ℝ] E) (L : Submodule ℝ E) (kappa : ℝ)
    (hcoercive : ∀ x : E, kappa * ‖x‖ ^ 2 ≤ inner ℝ (A x) x)
    (x : L) :
    kappa * ‖x‖ ≤ ‖deningerIncidenceCompression A L x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hq := hcoercive (x : E)
  rw [← deningerIncidenceCompression_inner_eq A L x] at hq
  have habs :
      inner ℝ (deningerIncidenceCompression A L x) x ≤
        ‖inner ℝ (deningerIncidenceCompression A L x) x‖ :=
    Real.le_norm_self _
  have hcs :
      ‖inner ℝ (deningerIncidenceCompression A L x) x‖ ≤
        ‖deningerIncidenceCompression A L x‖ * ‖x‖ :=
    norm_inner_le_norm _ _
  have hmul :
      kappa * ‖x‖ ^ 2 ≤ ‖deningerIncidenceCompression A L x‖ * ‖x‖ :=
    hq.trans (habs.trans hcs)
  nlinarith

end Compression

/-- The signed prime-log lattice admits no positive uniform spectral gap. -/
theorem deningerPrimeLogLattice_no_uniform_positive_gap :
    ¬ ∃ kappa : ℝ, 0 < kappa ∧
      ∀ x : ℝ, x ∈ GaloisForLFunctions.RHTower.primeLogLattice →
        x ≠ 0 → kappa ≤ |x| := by
  rintro ⟨kappa, hkappa, hgap⟩
  obtain ⟨x, hxmem, hxpos, hxlt⟩ :=
    GaloisForLFunctions.RHTower.primeLogLattice_arbitrarily_small_rate kappa hkappa
  have hbound := hgap x hxmem (ne_of_gt hxpos)
  rw [abs_of_pos hxpos] at hbound
  linarith

/-- Local Tate modes are uniformly gapped while the signed global Kummer lattice is gapless. -/
theorem deningerPrimeKummer_gap_localization :
    (∀ k : ℕ, 2 * Real.pi ≤ deningerTateCircleModeRate (k + 1)) ∧
      ¬ ∃ kappa : ℝ, 0 < kappa ∧
        ∀ x : ℝ, x ∈ GaloisForLFunctions.RHTower.primeLogLattice →
          x ≠ 0 → kappa ≤ |x| := by
  exact ⟨deningerTateCircleModeRate_succ_gap,
    deningerPrimeLogLattice_no_uniform_positive_gap⟩

end


end RHTower
