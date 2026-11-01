import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteHermitianDiagonalization
import GaloisForLFunctions.HTGeometry.FiniteWeightedHilbertSpace

/-!
# Complete signed Hilbert models for finite Hermitian forms

Separate positive and negative diagonal weights. The corresponding finite
weighted Hilbert spaces are complete, and retain the original coordinates.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset Module
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteSignature

variable {ι : Type*} [Fintype ι]

/-- The positive spectral coordinates, with their original positive weights. -/
abbrev PositiveSpace (d : ι → ℝ) :=
  FiniteWeightedHilbert.Space (fun i : {j // 0 < d j} => d i) (fun i => i.property)

omit [Fintype ι] in
private theorem negative_weight_pos (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (i : {j // ¬0 < d j}) : 0 < -d i :=
  neg_pos.mpr ((lt_or_eq_of_le (le_of_not_gt i.property)).resolve_right (hd i))

/-- The negative spectral coordinates, made positive by reversing the weights. -/
abbrev NegativeSpace (d : ι → ℝ) (hd : ∀ i, d i ≠ 0) :=
  FiniteWeightedHilbert.Space (fun i : {j // ¬0 < d j} => -d i) (negative_weight_pos d hd)

/-- Partition diagonal coordinates by the sign of their weight. -/
def splitCoordinates (d : ι → ℝ) (hd : ∀ i, d i ≠ 0) :
    (ι → ℂ) ≃ₗ[ℂ] PositiveSpace d × NegativeSpace d hd where
  toEquiv := Equiv.piEquivPiSubtypeProd (fun i => 0 < d i) (fun _ => ℂ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem weightedPairing_split (d : ι → ℝ) (hd : ∀ i, d i ≠ 0) (x y : ι → ℂ) :
    FiniteWeightedHilbert.weightedPairing d x y =
      inner ℂ (splitCoordinates d hd x).1 (splitCoordinates d hd y).1 -
        inner ℂ (splitCoordinates d hd x).2 (splitCoordinates d hd y).2 := by
  change (∑ i, (d i : ℂ) * conj (x i) * y i) =
    (∑ i : {j // 0 < d j}, (d i : ℂ) * conj (x i) * y i) -
      ∑ i : {j // ¬0 < d j}, ((-d i : ℝ) : ℂ) * conj (x i) * y i
  simp only [Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  exact (Fintype.sum_subtype_add_sum_subtype (fun i => 0 < d i)
    (fun i => (d i : ℂ) * conj (x i) * y i)).symm

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Nondegeneracy excludes every zero diagonal weight. -/
theorem diagonal_weights_ne_zero {B : V → V → ℂ}
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) {n : ℕ}
    (e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (d : Fin n → ℝ)
    (hdiag : ∀ v w, B v w = ∑ i, (d i : ℂ) * conj (e w i) * e v i) :
    ∀ i, d i ≠ 0 := by
  classical
  intro i hi
  let v := e.symm (WithLp.toLp 2 (Pi.single i (1 : ℂ)))
  have hv : ∀ j, e v j = (Pi.single i (1 : ℂ) : Fin n → ℂ) j := by
    intro j
    change e (e.symm _) j = _
    rw [e.apply_symm_apply]
  have hz : v = 0 := hnd v fun w => by
    rw [hdiag]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hji : j = i
    · subst j
      rw [hi, Complex.ofReal_zero, zero_mul, zero_mul]
    · rw [hv j, Pi.single_eq_of_ne hji, mul_zero]
  have hvi := hv i
  rw [hz, map_zero] at hvi
  exact zero_ne_one (by simpa only [PiLp.zero_apply, Pi.single_eq_same] using hvi)

/-- Every nondegenerate finite Hermitian form is a difference of complete Hilbert forms. -/
theorem exists_signed_hilbert_coordinates {B : V → V → ℂ}
    (hB : IsHermitianForm B) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) :
    ∃ (n : ℕ) (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
      (e : V ≃ₗ[ℂ] PositiveSpace d × NegativeSpace d hd),
      ∀ v w, B v w = inner ℂ (e w).1 (e v).1 - inner ℂ (e w).2 (e v).2 := by
  obtain ⟨n, e, d, hdiag⟩ := exists_hermitian_diagonal_coordinates hB
  have hd := diagonal_weights_ne_zero hnd e d hdiag
  let s := (e.trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ))).trans (splitCoordinates d hd)
  refine ⟨n, d, hd, s, ?_⟩
  intro v w
  rw [hdiag]
  exact weightedPairing_split d hd (fun i => e w i) (fun i => e v i)

#print axioms exists_signed_hilbert_coordinates

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteSignature
