import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import GaloisForLFunctions.HTGeometry.PhotonicTimeCrystalDynamicChirality

/-!
# No finite dressed Laurent carrier for literal rotating material

Finite Floquet packets are Laurent polynomials. The real rotating source has a
constant term and nonzero positive/negative helical terms. Multiplication by
that symbol has no nonzero finite-dimensional invariant complex subspace,
whether or not the subspace is spanned by coordinate sidebands.

This is a material-action obstruction, not a no-go for a projected Maxwell
monodromy or for an infinite boundary map.
-/

open LaurentPolynomial GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section
set_option autoImplicit false

/-- Constant plus balanced positive/negative helical material symbol. -/
def ptrMaterialSymbol (a d : ℂ) : LaurentPolynomial ℂ :=
  C d + C a * T 1 + C a * T (-1)

/-- The upper helical coefficient is exactly the source amplitude. -/
theorem ptrMaterialSymbol_coeff_one (a d : ℂ) :
    (ptrMaterialSymbol a d).coeff 1 = a := by
  simp [ptrMaterialSymbol, ← single_eq_C_mul_T]

/-- A nonzero helical amplitude makes the symbol nonconstant. -/
theorem ptrMaterialSymbol_ne_constant (a d : ℂ) (ha : a ≠ 0) (lam : ℂ) :
    ptrMaterialSymbol a d ≠ C lam := by
  intro h
  have hc := congrArg (fun q : LaurentPolynomial ℂ => q.coeff 1) h
  simp only [ptrMaterialSymbol_coeff_one, C_apply, if_neg (by decide : (1 : ℤ) ≠ 0)] at hc
  exact ha hc

/-- No nonzero finite packet is an eigenvector of literal material
multiplication. -/
theorem ptrMaterialSymbol_no_eigenvector (a d : ℂ) (ha : a ≠ 0)
    (f : LaurentPolynomial ℂ) (lam : ℂ)
    (hf : ptrMaterialSymbol a d * f = lam • f) : f = 0 := by
  have hprod : (ptrMaterialSymbol a d - C lam) * f = 0 := by
    rw [sub_mul]
    exact sub_eq_zero.mpr (by simpa only [smul_eq_C_mul] using hf)
  rcases mul_eq_zero.mp hprod with hP | hf0
  · exact False.elim (ptrMaterialSymbol_ne_constant a d ha lam (sub_eq_zero.mp hP))
  · exact hf0

/-- No finite-dimensional dressed packet sector is invariant under literal
nonconstant rotating-material multiplication. -/
theorem ptrMaterialSymbol_no_finite_invariant (a d : ℂ) (ha : a ≠ 0)
    (W : Submodule ℂ (LaurentPolynomial ℂ))
    [FiniteDimensional ℂ W]
    (hstable : ∀ f ∈ W, ptrMaterialSymbol a d * f ∈ W) :
    W = ⊥ := by
  by_contra hW
  letI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  let T : Module.End ℂ W :=
    (LinearMap.mulLeft ℂ (ptrMaterialSymbol a d)).restrict (by
      intro f hf
      exact hstable f hf)
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue T
  obtain ⟨f, hf⟩ := hlam.exists_hasEigenvector
  have heig : ptrMaterialSymbol a d * (f : LaurentPolynomial ℂ) =
      lam • (f : LaurentPolynomial ℂ) := by
    have h := Module.End.mem_eigenspace_iff.mp hf.1
    simpa only [T, LinearMap.restrict_apply, LinearMap.mulLeft_apply,
      Submodule.coe_smul] using congrArg Subtype.val h
  have hf0 := ptrMaterialSymbol_no_eigenvector a d ha f lam heig
  exact hf.2 (Subtype.ext hf0)

/-- The positive physical helical phase as a unit for Laurent evaluation. -/
def ptrHelicalUnit (m : ℤ) (θ Ω t : ℝ) : ℂˣ :=
  Units.mk0 (rotatingPositiveHarmonic m θ Ω t) (by
    unfold rotatingPositiveHarmonic
    exact Complex.exp_ne_zero _)

/-- The negative harmonic is the inverse of the positive harmonic. -/
theorem ptr_negative_eq_positive_inv (m : ℤ) (θ Ω t : ℝ) :
    rotatingNegativeHarmonic m θ Ω t =
      (rotatingPositiveHarmonic m θ Ω t)⁻¹ := by
  simpa only [rotatingNegativeHarmonic, rotatingPositiveHarmonic, neg_mul] using
    Complex.exp_neg (Complex.I * (rotatingModulationPhase m θ Ω t : ℂ))

/-- The Laurent symbol evaluates to the corpus's literal rotating complex
permittivity, retaining both helicities and the loss coordinate. -/
theorem ptrMaterialSymbol_eval_source
    (εbar δε εLoss : ℝ) (m : ℤ) (θ Ω t : ℝ) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) (ptrHelicalUnit m θ Ω t)
      (ptrMaterialSymbol (((εbar * δε / 2 : ℝ) : ℂ))
        ((εbar : ℂ) + Complex.I * (εLoss : ℂ))) =
      rotatingComplexPermittivity εbar δε εLoss m θ Ω t := by
  rw [rotatingComplexPermittivity_helical_decomposition]
  simp only [ptrMaterialSymbol, map_add, map_mul, eval₂_C,
    RingHom.id_apply, eval₂_T, zpow_one, zpow_neg,
    Units.val_inv_eq_inv_val]
  change ((εbar : ℂ) + Complex.I * (εLoss : ℂ)) +
      ((εbar * δε / 2 : ℝ) : ℂ) * rotatingPositiveHarmonic m θ Ω t +
      ((εbar * δε / 2 : ℝ) : ℂ) *
        (rotatingPositiveHarmonic m θ Ω t)⁻¹ = _
  rw [← ptr_negative_eq_positive_inv]
  ring

end
end RHTower
