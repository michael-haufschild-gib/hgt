import GaloisForLFunctions.ArakelovW
import GaloisForLFunctions.Bottcher.ModularLambdaCovering

/-!
# Functional-equation orbits through the modular-lambda braid

The Arakelov coordinate `w_rho = 1 - 1/rho` turns functional-equation reflection into inversion.
The modular lambda Hauptmodul is onto the twice-punctured plane, and the anharmonic braid word
`S*T*S` also acts by inversion.  Consequently every nonexceptional functional-equation pair,
including every off-critical pair, has a modular-lambda lift on which reflection is the braid word.

This is a positive uniformization theorem and an RH no-go: holomorphic modular/anharmonic symmetry
alone accepts the whole punctured plane.  The critical-line selector is the additional
antiholomorphic/unitary condition `|w| = 1`; it is not supplied by the modular lift.
-/

open Complex Set

namespace GaloisForLFunctions

noncomputable section

/-- A nonexceptional Arakelov coordinate lies in the modular-lambda target
`C \ {0,1}`. -/
theorem arakelovW_mem_punctured (rho : ℂ) (h0 : rho ≠ 0) (h1 : rho ≠ 1) :
    arakelovW rho ∈ ({0, 1} : Set ℂ)ᶜ := by
  rw [Bottcher.mem_compl01, arakelovW_eq_div rho h0]
  refine ⟨div_ne_zero (sub_ne_zero.mpr h1) h0, ?_⟩
  intro h
  rw [div_eq_one_iff_eq h0] at h
  exact one_ne_zero (by linear_combination -h)

/-- The Arakelov coordinate packaged as a point of the twice-punctured plane. -/
def arakelovWPunct (rho : ℂ) (h0 : rho ≠ 0) (h1 : rho ≠ 1) : Bottcher.Punctured :=
  ⟨arakelovW rho, arakelovW_mem_punctured rho h0 h1⟩

@[simp] theorem arakelovWPunct_coe (rho : ℂ) (h0 : rho ≠ 0) (h1 : rho ≠ 1) :
    (arakelovWPunct rho h0 h1 : ℂ) = arakelovW rho := rfl

/-- Functional-equation reflection is inversion in the Arakelov coordinate. -/
theorem arakelovW_sigma_eq_inv (rho : ℂ) (h0 : rho ≠ 0) (h1 : rho ≠ 1) :
    arakelovW (sigma rho) = (arakelovW rho)⁻¹ :=
  eq_inv_of_mul_eq_one_right (arakelovW_mul_sigma rho h0 h1)

/-- **Universal modular lift of a functional-equation pair.**  Every nonexceptional `rho` has an
upper-half-plane lift whose modular-lambda value is its Arakelov coordinate; the braid word
`S*T*S` sends that lift to the functional-equation-reflected coordinate.  The same lift lies over
the unit circle exactly when `rho` lies on the critical line. -/
theorem exists_modularLambda_lift_FE_braid (rho : ℂ) (h0 : rho ≠ 0) (h1 : rho ≠ 1) :
    ∃ tau : UpperHalfPlane,
      (Bottcher.lambdaPunct tau : ℂ) = arakelovW rho ∧
      (Bottcher.lambdaPunct
          ((ModularGroup.S * ModularGroup.T * ModularGroup.S) • tau) : ℂ) =
        arakelovW (sigma rho) ∧
      (‖(Bottcher.lambdaPunct tau : ℂ)‖ = 1 ↔ rho.re = 1 / 2) := by
  obtain ⟨tau, htau⟩ := Bottcher.lambdaPunct_surjective (arakelovWPunct rho h0 h1)
  refine ⟨tau, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val htau
  · have hword :
        Bottcher.lambdaPunct
            ((ModularGroup.S * ModularGroup.T * ModularGroup.S) • tau) =
          (Bottcher.anharmS * Bottcher.anharmT * Bottcher.anharmS)
            (Bottcher.lambdaPunct tau) := by
      rw [mul_smul, mul_smul, Bottcher.lambdaPunct_smul_S,
        Bottcher.lambdaPunct_smul_T, Bottcher.lambdaPunct_smul_S]
      rfl
    rw [hword]
    have htauc : (Bottcher.lambdaPunct tau : ℂ) = arakelovW rho := by
      simpa only [arakelovWPunct_coe] using congrArg Subtype.val htau
    have hw0 : (Bottcher.lambdaPunct tau : ℂ) ≠ 0 :=
      Bottcher.punct_ne_zero (Bottcher.lambdaPunct tau)
    have hinv :
        (((Bottcher.anharmS * Bottcher.anharmT * Bottcher.anharmS)
          (Bottcher.lambdaPunct tau) : Bottcher.Punctured) : ℂ) =
            (Bottcher.lambdaPunct tau : ℂ)⁻¹ := by
      change 1 - (1 - (Bottcher.lambdaPunct tau : ℂ)) /
          ((1 - (Bottcher.lambdaPunct tau : ℂ)) - 1) =
        (Bottcher.lambdaPunct tau : ℂ)⁻¹
      rw [show (1 - (Bottcher.lambdaPunct tau : ℂ)) - 1 =
        -(Bottcher.lambdaPunct tau : ℂ) by ring]
      field_simp [hw0]
      ring
    rw [hinv, htauc, arakelovW_sigma_eq_inv rho h0 h1]
  · rw [congrArg Subtype.val htau]
    exact arakelovW_norm_one_iff_critical rho h0

/-- Off-critical points also admit the full modular-lambda functional-equation braid lift, and the
lift then lies strictly off the unit circle.  This is the explicit nonselection corollary. -/
theorem exists_modularLambda_lift_FE_braid_off_unit (rho : ℂ) (h0 : rho ≠ 0) (h1 : rho ≠ 1)
    (hoff : rho.re ≠ 1 / 2) :
    ∃ tau : UpperHalfPlane,
      (Bottcher.lambdaPunct tau : ℂ) = arakelovW rho ∧
      (Bottcher.lambdaPunct
          ((ModularGroup.S * ModularGroup.T * ModularGroup.S) • tau) : ℂ) =
        arakelovW (sigma rho) ∧
      ‖(Bottcher.lambdaPunct tau : ℂ)‖ ≠ 1 := by
  obtain ⟨tau, htau, hreflect, hunit⟩ := exists_modularLambda_lift_FE_braid rho h0 h1
  exact ⟨tau, htau, hreflect, fun h => hoff (hunit.mp h)⟩

end

end GaloisForLFunctions
