import GaloisForLFunctions.HTGeometry.ComplexAffineLinePolynomialAvoidance
import GaloisForLFunctions.HTGeometry.PolynomialHermitianSpectrumGenericity

/-!
# One-knob activation of maximal projective spectra

The spectral obstructions of a polynomial Hermitian family are complex polynomials in the real
parameters, one for each nonzero balanced integer character.  A single witness parameter at which
the spectrum is maximally projective makes every one of them a nonzero polynomial, so the complex
affine-line avoidance layer applies: along almost every affine line in parameter space, all
obstructions survive outside a countable set of coupling strengths.

This is the one-knob form of generic maximal projective rank.  Genericity in the full parameter
space is a full-measure statement; along a line it sharpens to a countable exceptional set, which
is what a single physical coupling constant sees.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- An enumeration of the integer characters of a finite spectrum. -/
def spectralCharacterEnumeration (I : Type*) [Fintype I] [DecidableEq I] : ℕ → (I → ℤ) := by
  classical
  exact (exists_surjective_nat (I → ℤ)).choose

theorem spectralCharacterEnumeration_surjective (I : Type*) [Fintype I] [DecidableEq I] :
    Function.Surjective (spectralCharacterEnumeration I) := by
  classical
  exact (exists_surjective_nat (I → ℤ)).choose_spec

/-- The obstruction polynomial attached to the `r`-th character, replaced by `1` when that
character is trivial or unbalanced. -/
def enumeratedSpectralObstruction
    (coefficient : Fin (Fintype.card I) → MvPolynomial (Fin m) ℂ) (r : ℕ) :
    MvPolynomial (Fin m) ℂ := by
  classical
  exact
    if SpectralCharacterBalanced (spectralCharacterEnumeration I r) ∧
        spectralCharacterEnumeration I r ≠ 0 then
      complexSpectralCoefficientObstructionPullback coefficient
        (spectralCharacterEnumeration I r)
    else 1

theorem enumeratedSpectralObstruction_ne_zero
    (coefficient : Fin (Fintype.card I) → MvPolynomial (Fin m) ℂ)
    (p₀ : Fin m → ℝ)
    (hp₀ : p₀ ∈ complexSpectralCoefficientProjectiveGenericSet (I := I) coefficient)
    (r : ℕ) : enumeratedSpectralObstruction (I := I) coefficient r ≠ 0 := by
  classical
  rw [enumeratedSpectralObstruction]
  split_ifs with hk
  · intro hzero
    refine hp₀ _ hk.1 hk.2 ?_
    rw [hzero]
    simp
  · exact one_ne_zero

/-- **One-knob spectral activation.**  If one parameter of a polynomial Hermitian family has
maximally projective spectrum, then along almost every affine line in parameter space every
nonzero balanced obstruction survives outside a countable set of coupling strengths. -/
theorem countable_exceptional_coupling_complexSpectralGenericSet
    (coefficient : Fin (Fintype.card I) → MvPolynomial (Fin m) ℂ)
    (p₀ : Fin m → ℝ)
    (hp₀ : p₀ ∈ complexSpectralCoefficientProjectiveGenericSet (I := I) coefficient) :
    ∀ᵐ av : (Fin m → ℝ) × (Fin m → ℝ) ∂(volume.prod volume),
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C,
          (fun i => av.1 i + g * av.2 i) ∈
            complexSpectralCoefficientProjectiveGenericSet (I := I) coefficient := by
  classical
  filter_upwards [countable_complexMvPolynomialAffineLineAvoidance_ae_pair
    (enumeratedSpectralObstruction (I := I) coefficient)
    (enumeratedSpectralObstruction_ne_zero coefficient p₀ hp₀)] with av hav
  obtain ⟨C, hC, hgC⟩ := hav
  refine ⟨C, hC, fun g hg k hbalanced hk => ?_⟩
  obtain ⟨r, hr⟩ := spectralCharacterEnumeration_surjective I k
  have hobs := hgC g hg r
  rw [enumeratedSpectralObstruction, if_pos ⟨hr ▸ hbalanced, hr ▸ hk⟩, hr] at hobs
  exact hobs

/-- **One-knob activation for a polynomial Hermitian matrix family.** -/
theorem countable_exceptional_coupling_polynomialMatrixGenericSet
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (p₀ : Fin m → ℝ) (hp₀ : p₀ ∈ polynomialMatrixProjectiveGenericSet M) :
    ∀ᵐ av : (Fin m → ℝ) × (Fin m → ℝ) ∂(volume.prod volume),
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C,
          (fun i => av.1 i + g * av.2 i) ∈ polynomialMatrixProjectiveGenericSet M := by
  unfold polynomialMatrixProjectiveGenericSet at hp₀ ⊢
  exact countable_exceptional_coupling_complexSpectralGenericSet _ p₀ hp₀

/-- **One-knob activation of the actual eigenvalue packet.**  Along almost every affine line of
parameters, all but countably many coupling strengths give a maximally projective spectrum. -/
theorem countable_exceptional_coupling_maximallyProjectiveEigenvalues
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (hHerm : ∀ p : Fin m → ℝ,
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p t : ℂ)))).IsHermitian)
    (p₀ : Fin m → ℝ) (hp₀ : p₀ ∈ polynomialMatrixProjectiveGenericSet M) :
    ∀ᵐ av : (Fin m → ℝ) × (Fin m → ℝ) ∂(volume.prod volume),
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C,
          MaximallyProjectiveEnergy
            (hHerm (fun i => av.1 i + g * av.2 i)).eigenvalues := by
  filter_upwards [countable_exceptional_coupling_polynomialMatrixGenericSet M p₀ hp₀] with av hav
  obtain ⟨C, hC, hgC⟩ := hav
  refine ⟨C, hC, fun g hg => ?_⟩
  exact maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet M _ (hgC g hg)
    (hHerm _)

/-- A maximally projective parameter lies in the obstruction-generic set. -/
theorem mem_polynomialMatrixProjectiveGenericSet_of_maximallyProjective
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (p₀ : Fin m → ℝ)
    (hH : (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
      (fun t => (p₀ t : ℂ)))).IsHermitian)
    (hmax : MaximallyProjectiveEnergy hH.eigenvalues) :
    p₀ ∈ polynomialMatrixProjectiveGenericSet M := by
  intro k hbalanced hk
  refine complexSpectralCoefficientObstructionPullback_has_real_witness
    (matrixCharacteristicElementaryPolynomial M) p₀ hH.eigenvalues hmax ?_ k hbalanced hk
  intro i
  rw [eval_matrixCharacteristicElementaryPolynomial]
  exact matrixCharacteristicElementaryCoefficient_eq_hermitianEigenvalues _ hH i

/-- **One-knob activation from a single witness.**  This is the coupling-line form of generic
maximal projective rank: one maximally projective member of a polynomial Hermitian family forces,
along almost every affine line of parameters, maximal projective rank at all but countably many
coupling strengths. -/
theorem countable_exceptional_coupling_of_maximallyProjective_witness
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (hHerm : ∀ p : Fin m → ℝ,
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p t : ℂ)))).IsHermitian)
    (p₀ : Fin m → ℝ)
    (hmax : MaximallyProjectiveEnergy (hHerm p₀).eigenvalues) :
    ∀ᵐ av : (Fin m → ℝ) × (Fin m → ℝ) ∂(volume.prod volume),
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C,
          MaximallyProjectiveEnergy
            (hHerm (fun i => av.1 i + g * av.2 i)).eigenvalues :=
  countable_exceptional_coupling_maximallyProjectiveEigenvalues M hHerm p₀
    (mem_polynomialMatrixProjectiveGenericSet_of_maximallyProjective M p₀ (hHerm p₀) hmax)

end

end GaloisForLFunctions.HTGeometry
