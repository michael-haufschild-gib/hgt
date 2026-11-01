import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteNegativeIndexDrop
import GaloisForLFunctions.HeckeKreinToeplitz.Index.PositiveCoefficients

/-!
# Coefficients orthogonal to a nonpositive direction

An orbit in the orthogonal complement of a nonzero nonpositive vector has
one fewer possible negative direction than the ambient negative Hilbert
factor. Finite Gram synthesis transfers the dimension bound to the global
kernel index.
-/

noncomputable section
set_option autoImplicit false
open Complex Module Finset
open scoped ComplexConjugate InnerProductSpace
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {G H E : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The linear functional obtained by fixing the first argument of the form. -/
def pairingLinear (w : H × E) : (H × E) →ₗ[ℂ] ℂ where
  toFun := pairing w
  map_add' := pairing_add_right w
  map_smul' c v := pairing_smul_right c w v

theorem isHermitianForm_reverse_pairing : IsHermitianForm (fun v w : H × E => pairing w v) :=
  { add_left := fun u v w => pairing_add_right w u v
    smul_left := fun c v w => pairing_smul_right c w v
    symm := fun v w => (pairing_conj_symm v w).symm }

variable (ρ : G →* End ℂ (H × E))
    (hρ : ∀ g v w, pairing (ρ g v) (ρ g w) = pairing v w)

include hρ in
theorem coefficient_orbit_pairing (v : H × E) (g h : G) :
    pairing (ρ g v) (ρ h v) = pairing v (ρ (g⁻¹ * h) v) :=
  invariantHermitianForm_orbit_pairing ρ (fun u w => pairing w u)
    (fun g u w => hρ g w u) v g h

include hρ in
/-- Every coefficient of an invariant Hermitian form is a Hermitian kernel. -/
theorem isHermKernel_coefficient (v : H × E) : IsHermKernel (fun g => pairing v (ρ g v)) := by
  intro g
  calc
    pairing v (ρ g⁻¹ v) = pairing (ρ g v) v := by
      simpa only [map_one, Module.End.one_apply, mul_one] using
        (coefficient_orbit_pairing ρ hρ v g 1).symm
    _ = conj (pairing v (ρ g v)) := (pairing_conj_symm (ρ g v) v).symm

/-- Finite synthesis of an orbit family. -/
def coefficientSynthesis (v : H × E) {ι : Type*} [Fintype ι] (x : ι → G) :
    (ι → ℂ) →ₗ[ℂ] (H × E) where
  toFun c := ∑ i, c i • ρ (x i) v
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

include hρ in
/-- The coefficient Gram form is the square of its synthesized orbit vector. -/
theorem hermQuad_coefficientSynthesis (v : H × E) {ι : Type*} [Fintype ι]
    (x : ι → G) (c : ι → ℂ) :
    hermQuad (gram (fun g => pairing v (ρ g v)) x) c =
      (pairing (coefficientSynthesis ρ v x c) (coefficientSynthesis ρ v x c)).re := by
  have hs := hermitianForm_fin_synthesis (isHermitianForm_reverse_pairing (H := H) (E := E))
    (fun i => ρ (x i) v) (fun i => ρ (x i) v) c c
  have he : (∑ i, ∑ j, c i * star (c j) * pairing (ρ (x j) v) (ρ (x i) v)) =
      ∑ i, ∑ j, conj (c i) * pairing v (ρ ((x i)⁻¹ * x j) v) * c j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [coefficient_orbit_pairing ρ hρ, Complex.star_def]
    ring
  rw [he] at hs
  rw [hermQuad_gram]
  exact (congrArg Complex.re hs).symm

/-- Orthogonality of the orbit passes to each finite synthesis. -/
theorem coefficientSynthesis_orthogonal (v w : H × E)
    (ho : ∀ g, pairing w (ρ g v) = 0) {ι : Type*} [Fintype ι]
    (x : ι → G) (c : ι → ℂ) : pairing w (coefficientSynthesis ρ v x c) = 0 := by
  change pairingLinear w (∑ i, c i • ρ (x i) v) = 0
  have hz (i : ι) : pairingLinear w (ρ (x i) v) = 0 := ho (x i)
  rw [map_sum]
  simp only [map_smul, hz, smul_zero, Finset.sum_const_zero]

include hρ in
/-- An orbit orthogonal to a nonpositive line has one fewer possible negative square. -/
theorem negIndex_coefficient_le_of_orthogonal_nonpositive [FiniteDimensional ℂ E]
    {r : ℕ} (hE : finrank ℂ E ≤ r + 1) (v : H × E) {w : H × E}
    (hw : w ≠ 0) (hwq : (pairing w w).re ≤ 0) (ho : ∀ g, pairing w (ρ g v) = 0) :
    negIndex (fun g => pairing v (ρ g v)) ≤ r := by
  apply negIndex_le_iff.mpr
  intro n x
  have hd := hermNegIndex_add_one_le_of_orthogonal
    (gram (fun g => pairing v (ρ g v)) x) (coefficientSynthesis ρ v x)
    (hermQuad_coefficientSynthesis ρ hρ v x) hw hwq
    (coefficientSynthesis_orthogonal ρ v w ho x)
  have hn : hermNegIndex (gram (fun g => pairing v (ρ g v)) x) ≤ r := by omega
  exact_mod_cast hn

#print axioms negIndex_coefficient_le_of_orthogonal_nonpositive

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
