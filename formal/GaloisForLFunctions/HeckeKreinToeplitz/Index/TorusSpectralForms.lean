import GaloisForLFunctions.HTGeometry.TorusPolynomialParseval
import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula

/-!
# Torus spectral forms on a free lattice

Torus points give distinct unitary lattice characters. Fourier coefficients
of a positive measure have Gram energy equal to the integral of a squared
packet norm, and every vector in the character span has a finite packet form.
-/

open Complex Finset MeasureTheory
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

variable {I : Type*} [Countable I]

/-- Evaluation at a torus point is a unitary character of the free lattice. -/
def torusLatticeCharacter (θ : UnitAddTorus I) : Multiplicative (I →₀ ℤ) →* ℂ where
  toFun u := torusCharacter u.toAdd θ
  map_one' := torusCharacter_zero θ
  map_mul' u v := torusCharacter_add_index u.toAdd v.toAdd θ

omit [Countable I] in
theorem torusLatticeCharacter_unitary (θ : UnitAddTorus I) :
    IsUnitaryChar (torusLatticeCharacter θ) := by
  classical
  intro u
  change ‖torusCharacter u.toAdd θ‖ = 1
  simp only [torusCharacter_apply, norm_prod, fourier_apply, Circle.norm_coe, prod_const_one]

omit [Countable I] in
theorem torusLatticeCharacter_injective :
    Function.Injective (torusLatticeCharacter (I := I)) := by
  classical
  intro θ η h
  funext i
  have hi := congrArg (fun χ : Multiplicative (I →₀ ℤ) →* ℂ =>
    χ (Multiplicative.ofAdd (Finsupp.single i 1))) h
  have hval (z : UnitAddTorus I) :
      torusLatticeCharacter z (Multiplicative.ofAdd (Finsupp.single i 1)) = fourier 1 (z i) := by
    change torusCharacter (Finsupp.single i 1) z = _
    rw [torusCharacter_apply_of_subset (s := {i}) Finsupp.support_single_subset z,
      prod_singleton, Finsupp.single_eq_same]
  have hf : fourier 1 (θ i) = fourier 1 (η i) := by
    simpa only [hval] using hi
  apply AddCircle.injective_toCircle one_ne_zero
  apply Subtype.ext
  simpa only [fourier_one] using hf

/-- Fourier coefficients of a finite measure, as a free-lattice kernel. -/
def torusFourierKernel (μ : Measure (UnitAddTorus I))
    (u : Multiplicative (I →₀ ℤ)) : ℂ := ∫ θ, torusCharacter u.toAdd θ ∂μ

omit [Countable I] in
theorem isHermKernel_torusFourierKernel (μ : Measure (UnitAddTorus I)) :
    IsHermKernel (torusFourierKernel μ) := by
  intro u
  change (∫ θ, torusCharacter (-u.toAdd) θ ∂μ) =
    conj (∫ θ, torusCharacter u.toAdd θ ∂μ)
  simp_rw [torusCharacter_neg_index]
  exact integral_conj

/-- The Gram form of a positive measure's Fourier coefficients is packet energy. -/
theorem hermQuad_gram_torusFourierKernel
    (μ : Measure (UnitAddTorus I)) [IsFiniteMeasure μ]
    {J : Type*} [Fintype J] (x : J → Multiplicative (I →₀ ℤ)) (c : J → ℂ) :
    hermQuad (gram (torusFourierKernel μ) x) c =
      ∫ θ, ‖∑ a, c a * torusCharacter (x a).toAdd θ‖ ^ 2 ∂μ := by
  classical
  rw [hermQuad_gram]
  have he : (∑ a, ∑ b, conj (c a) * torusFourierKernel μ ((x a)⁻¹ * x b) * c b) =
      ((∫ θ, ‖∑ a, c a * torusCharacter (x a).toAdd θ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [integral_norm_sq_torusCharacter_sum_measure]
    apply sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    have hx : ((x a)⁻¹ * x b).toAdd = (x b).toAdd - (x a).toAdd := by
      change -(x a).toAdd + (x b).toAdd = _
      abel
    rw [torusFourierKernel, hx]
    ring
  rw [he, Complex.ofReal_re]

theorem isPosDefKernel_torusFourierKernel
    (μ : Measure (UnitAddTorus I)) [IsFiniteMeasure μ] :
    IsPosDefKernel (torusFourierKernel μ) := by
  refine ⟨isHermKernel_torusFourierKernel μ, fun n x c => ?_⟩
  rw [hermQuad_gram_torusFourierKernel]
  exact integral_nonneg fun θ => sq_nonneg _

omit [Countable I] in
/-- Every vector in the character span has a finite packet presentation. -/
theorem exists_finite_torus_packet {f : C(UnitAddTorus I, ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (torusCharacter (ι := I)))) :
    ∃ (n : ℕ) (x : Fin n → I →₀ ℤ) (c : Fin n → ℂ),
      ∀ θ, f θ = ∑ a, c a * torusCharacter (x a) θ := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨x, rfl⟩ := hf
    exact ⟨1, fun _ => x, fun _ => 1, fun θ => by simp⟩
  | zero =>
    exact ⟨0, Fin.elim0, Fin.elim0, fun θ => by simp⟩
  | add f g _ _ ihf ihg =>
    obtain ⟨n, x, c, hc⟩ := ihf
    obtain ⟨m, y, d, hd⟩ := ihg
    refine ⟨n + m, Fin.append x y, Fin.append c d, fun θ => ?_⟩
    simp only [ContinuousMap.add_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      hc, hd]
  | smul a f _ ih =>
    obtain ⟨n, x, c, hc⟩ := ih
    refine ⟨n, x, fun j => a * c j, fun θ => ?_⟩
    simp only [ContinuousMap.smul_apply, smul_eq_mul, hc, mul_sum, mul_assoc]

end

end GaloisForLFunctions.HeckeKreinToeplitz
