import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PoissonPrincipalCyclesOnTheScalingSurface
import GaloisForLFunctions.HTGeometry.HermitianRadicalPositivity

/-!
# Arithmetic sharp and positive degree radicals on genuine cohomology

Arithmetic sharp descends through the actual Poisson boundary and preserves
convolution. A Hermitian linear degree therefore gives a sesquilinear form.
Its nonnegative square law forces every null vector to annihilate all mixed
products, including their imaginary parts.
-/

noncomputable section
open Complex RHTower
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Arithmetic sharp respects literal source convolution. -/
theorem meyerSourceSharp_convolution (g h : DeningerMeyerStrongLogTarget) :
    deningerMeyerSourceSharp (deningerMeyerSourceConvolution g h) =
      deningerMeyerSourceConvolution (deningerMeyerSourceSharp g) (deningerMeyerSourceSharp h) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  simp only [deningerMeyerSourceSharp_mellin, deningerMeyerSourceConvolution_mellin, star_mul]
  exact mul_comm _ _

/-- Arithmetic sharp on the actual Poisson quotient, with its conjugate-linear structure. -/
def meyerCohomologySharp :
    DeningerMeyerStrongLogCohomology →ₗ⋆[ℂ] DeningerMeyerStrongLogCohomology :=
  deningerMeyerStrongLogCohomologyJ.comp deningerMeyerCohomologyConj

@[simp] theorem meyerCohomologySharp_mk (g : DeningerMeyerStrongLogTarget) :
    meyerCohomologySharp (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (deningerMeyerSourceSharp g) := rfl

@[simp] theorem meyerCohomologySharp_sq (u : DeningerMeyerStrongLogCohomology) :
    meyerCohomologySharp (meyerCohomologySharp u) = u := by
  change deningerMeyerStrongLogCohomologyJ
    (deningerMeyerCohomologyConj
      (deningerMeyerStrongLogCohomologyJ (deningerMeyerCohomologyConj u))) = u
  rw [deningerMeyerCohomologyConj_J, deningerMeyerCohomologyConj_sq,
    deningerMeyerStrongLogCohomologyJ_sq]

/-- The genuine quotient has the same arithmetic involutive product law. -/
theorem meyerCohomologySharp_convolution (u v : DeningerMeyerStrongLogCohomology) :
    meyerCohomologySharp (deningerMeyerCohomologyConvolution u v) =
      deningerMeyerCohomologyConvolution (meyerCohomologySharp u) (meyerCohomologySharp v) := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    induction v using Submodule.Quotient.induction_on with
    | H h =>
      simp only [deningerMeyerCohomologyConvolution_mk, meyerCohomologySharp_mk,
        meyerSourceSharp_convolution]

/-- The original product paired by an arbitrary complex-linear cohomological degree. -/
def meyerDegreePair (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (u v : DeningerMeyerStrongLogCohomology) : ℂ :=
  d (deningerMeyerCohomologyConvolution u (meyerCohomologySharp v))

theorem meyerDegreePair_add_left (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (u v w : DeningerMeyerStrongLogCohomology) :
    meyerDegreePair d (u + v) w = meyerDegreePair d u w + meyerDegreePair d v w := by
  simp only [meyerDegreePair, map_add, LinearMap.add_apply]

theorem meyerDegreePair_add_right (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (u v w : DeningerMeyerStrongLogCohomology) :
    meyerDegreePair d u (v + w) = meyerDegreePair d u v + meyerDegreePair d u w := by
  simp only [meyerDegreePair, map_add]

theorem meyerDegreePair_smul_left (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (c : ℂ) (u v : DeningerMeyerStrongLogCohomology) :
    meyerDegreePair d (c • u) v = c * meyerDegreePair d u v := by
  simp only [meyerDegreePair, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem meyerDegreePair_smul_right (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (c : ℂ) (u v : DeningerMeyerStrongLogCohomology) :
    meyerDegreePair d u (c • v) = conj c * meyerDegreePair d u v := by
  rw [meyerDegreePair, LinearMap.map_smulₛₗ, map_smul, map_smul]
  rfl

/-- Hermiticity of the degree gives the full complex mixed symmetry. -/
theorem meyerDegreePair_conj_symm (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (u v : DeningerMeyerStrongLogCohomology) :
    meyerDegreePair d u v = conj (meyerDegreePair d v u) := by
  have h := hd (deningerMeyerCohomologyConvolution v (meyerCohomologySharp u))
  rw [meyerCohomologySharp_convolution, meyerCohomologySharp_sq,
    deningerMeyerCohomologyConvolution_comm] at h
  exact h

/-- A positive Hermitian degree has no mixed reading on a null square class. -/
theorem meyerPositiveDegree_null_pair (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    {u : DeningerMeyerStrongLogCohomology} (hu : (meyerDegreePair d u u).re = 0)
    (v : DeningerMeyerStrongLogCohomology) : meyerDegreePair d u v = 0 := by
  have hsymm (a b : DeningerMeyerStrongLogCohomology) :
      (meyerDegreePair d a b).re = (meyerDegreePair d b a).re := by
    rw [meyerDegreePair_conj_symm d hd a b, Complex.conj_re]
  have hexp (t : ℝ) (a b : DeningerMeyerStrongLogCohomology) :
      (meyerDegreePair d (a + (t : ℂ) • b) (a + (t : ℂ) • b)).re =
        (meyerDegreePair d a a).re + 2 * t * (meyerDegreePair d a b).re +
          t ^ 2 * (meyerDegreePair d b b).re := by
    simp only [meyerDegreePair_add_left, meyerDegreePair_add_right,
      meyerDegreePair_smul_left, meyerDegreePair_smul_right, Complex.conj_ofReal,
      Complex.add_re, Complex.re_ofReal_mul, hsymm b a]
    ring
  have hn (w : DeningerMeyerStrongLogCohomology) : (meyerDegreePair d u w).re = 0 :=
    GaloisForLFunctions.HTGeometry.symmBilin_eq_zero_of_self_eq_zero
      (S := fun a b => (meyerDegreePair d a b).re)
      (comb := fun t a b => a + (t : ℂ) • b) hexp hpos hu w
  have hi := hn (I • v)
  rw [meyerDegreePair_smul_right, Complex.conj_I] at hi
  apply Complex.ext
  · exact hn v
  · change (meyerDegreePair d u v).im = 0
    simpa only [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] using hi

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
