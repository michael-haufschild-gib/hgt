import GaloisForLFunctions.RHTower.MobiusMellinGammaNormalCone
import GaloisForLFunctions.RHTower.SquarefreeHeightReesBlowup

/-!
# Squarefree--Möbius double-normal-cone duality

Two independent Euler-pole blow-ups carry the same squarefree partition section with opposite
variance.  The fixed-height squarefree boundary is

`ζ(2) * squarefreePartition (1 + iγ)`,

whereas the exceptional Möbius normal-cone section is its reciprocal without the scalar `ζ(2)`.
Their pairing is therefore the parameter-free constant `ζ(2)`.
-/

open Complex Filter Set
open scoped Topology

noncomputable section
namespace RHTower

open GaloisForLFunctions

/-- The squarefree partition section is nonzero on the closed vertical Euler boundary. -/
theorem squarefreePartition_one_add_mul_I_ne_zero
    (gamma : ℝ) :
    squarefreePartition ((1 : ℂ) + (gamma : ℂ) * Complex.I) ≠ 0 := by
  let t : ℂ := (1 : ℂ) + (gamma : ℂ) * Complex.I
  have htRe : 1 ≤ t.re := by
    simp [t]
  have hzetaT : riemannZeta t ≠ 0 := by
    intro hzeta
    exact riemannZeta_ne_zero_of_one_le_re htRe hzeta
  have htwoTRe : 1 < (2 * t).re := by
    simp [t, Complex.mul_re]
  have hzetaTwoT : riemannZeta (2 * t) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re htwoTRe
  simpa only [squarefreePartition, t] using div_ne_zero hzetaT hzetaTwoT

/-- **Squarefree--Möbius double-normal-cone universality.**  At every nonzero physical height,
the squarefree macroscopic boundary and the Möbius exceptional normal-cone section are reciprocal
up to `ζ(2)`.  The first two clauses retain both limiting constructions; the last clause is their
exact, aperture- and height-independent pairing. -/
theorem squarefreeMobius_completeDoubleNormalConeDualityUniversality
    {delta : ℝ} (hdelta : 0 ≤ delta) {gamma : ℝ} (hgamma : gamma ≠ 0) :
    Tendsto (fun sigma : ℝ => squarefreeMacroscopicHeightOverlap sigma delta gamma)
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (2 : ℂ) *
          squarefreePartition ((1 : ℂ) + (gamma : ℂ) * Complex.I))) ∧
      Tendsto
        (fun base : ℂ =>
          mobiusCompletedNormalConeTransfer squarefreePartition base
            ((1 : ℂ) + (gamma : ℂ) * Complex.I))
        (𝓝 1)
        (𝓝 ((squarefreePartition
          ((1 : ℂ) + (gamma : ℂ) * Complex.I))⁻¹)) ∧
      (riemannZeta (2 : ℂ) *
          squarefreePartition ((1 : ℂ) + (gamma : ℂ) * Complex.I)) *
        mobiusCompletedNormalConeTransfer squarefreePartition 1
          ((1 : ℂ) + (gamma : ℂ) * Complex.I) =
        riemannZeta (2 : ℂ) := by
  have hpartition :
      squarefreePartition ((1 : ℂ) + (gamma : ℂ) * Complex.I) ≠ 0 :=
    squarefreePartition_one_add_mul_I_ne_zero gamma
  refine ⟨tendsto_squarefreeMacroscopicHeightOverlap hdelta hgamma,
    tendsto_mobiusCompletedNormalConeTransfer_one hpartition, ?_⟩
  rw [mobiusCompletedNormalConeTransfer_one]
  field_simp

end RHTower
