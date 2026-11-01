import GaloisForLFunctions.HeckeKreinToeplitz.Index.RadicalHilbertComplement
import GaloisForLFunctions.HeckeKreinToeplitz.Index.CommutingFiniteIndexIsometries

/-!
# Isometries on the radical quotient

The positive Hilbert complement represents the quotient by the radical.
Projecting a subspace-preserving isometry onto this complement gives an
invertible form-isometry; commuting families remain commuting.
-/

noncomputable section
set_option autoImplicit false
open Complex

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E]

omit [CompleteSpace H] [CompleteSpace E] [FiniteDimensional ℂ E] in
theorem inverse_pairing (T : (H × E) ≃L[ℂ] (H × E))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w) (v w : H × E) :
    pairing (T.symm v) (T.symm w) = pairing v w := by
  have h := hT (T.symm v) (T.symm w)
  rw [T.apply_symm_apply, T.apply_symm_apply] at h
  exact h.symm

variable (W : Submodule ℂ (H × E)) (T : (H × E) ≃L[ℂ] (H × E))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w)
    (hf : ∀ v ∈ W, T v ∈ W) (hb : ∀ v ∈ W, T.symm v ∈ W)

/-- An intermediate radical projection does not change the quotient action. -/
theorem radicalRetraction_map_radicalRetraction (v : H × E) :
    radicalRetraction W (T (radicalRetraction W v)) = radicalRetraction W (T v) := by
  have h := radicalRetraction_eq_zero W
    (map_mem_restrictedRadical W T hT hf hb (sub_radicalRetraction_mem W v))
  rw [map_sub, map_sub, sub_eq_zero] at h
  exact h.symm

/-- The induced invertible isometry on a concrete representative of the radical quotient. -/
def radicalQuotientEquiv : radicalComplement W ≃L[ℂ] radicalComplement W where
  toFun v := ⟨radicalRetraction W (T v), radicalRetraction_mem W (hf v v.property.1)⟩
  invFun v := ⟨radicalRetraction W (T.symm v), radicalRetraction_mem W (hb v v.property.1)⟩
  left_inv v := by
    apply Subtype.ext
    change radicalRetraction W (T.symm (radicalRetraction W (T v))) = (v : H × E)
    rw [radicalRetraction_map_radicalRetraction W T.symm (inverse_pairing T hT) hb hf,
      T.symm_apply_apply, radicalRetraction_eq_self W v.property]
  right_inv v := by
    apply Subtype.ext
    change radicalRetraction W (T (radicalRetraction W (T.symm v))) = (v : H × E)
    rw [radicalRetraction_map_radicalRetraction W T hT hf hb,
      T.apply_symm_apply, radicalRetraction_eq_self W v.property]
  map_add' u v := by
    apply Subtype.ext
    change radicalRetraction W (T ((u : H × E) + (v : H × E))) = _
    rw [map_add, map_add]
    rfl
  map_smul' a v := by
    apply Subtype.ext
    change radicalRetraction W (T (a • (v : H × E))) = _
    rw [map_smul, map_smul]
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (radicalRetraction W).continuous.comp (T.continuous.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (radicalRetraction W).continuous.comp (T.symm.continuous.comp continuous_subtype_val)

theorem radicalQuotientEquiv_pairing (u v : radicalComplement W) :
    pairing (radicalQuotientEquiv W T hT hf hb u : H × E)
      (radicalQuotientEquiv W T hT hf hb v : H × E) = pairing (u : H × E) (v : H × E) := by
  change pairing (radicalRetraction W (T u)) (radicalRetraction W (T v)) = _
  rw [pairing_radicalRetraction W (hf u u.property.1) (hf v v.property.1), hT]

omit T hT hf hb in
/-- Commuting isometries induce commuting quotient isometries. -/
theorem radicalQuotientEquiv_commute {ι : Type*}
    (T : ι → (H × E) ≃L[ℂ] (H × E))
    (hT : ∀ i v w, pairing (T i v) (T i w) = pairing v w)
    (hW : IsBiInvariant T W)
    (hc : ∀ i j v, T i (T j v) = T j (T i v))
    (i j : ι) (v : radicalComplement W) :
    radicalQuotientEquiv W (T i) (hT i) (fun v hv => (hW i v hv).1)
        (fun v hv => (hW i v hv).2)
      (radicalQuotientEquiv W (T j) (hT j) (fun v hv => (hW j v hv).1)
        (fun v hv => (hW j v hv).2) v) =
    radicalQuotientEquiv W (T j) (hT j) (fun v hv => (hW j v hv).1)
        (fun v hv => (hW j v hv).2)
      (radicalQuotientEquiv W (T i) (hT i) (fun v hv => (hW i v hv).1)
        (fun v hv => (hW i v hv).2) v) := by
  apply Subtype.ext
  change radicalRetraction W (T i (radicalRetraction W (T j v))) =
    radicalRetraction W (T j (radicalRetraction W (T i v)))
  rw [radicalRetraction_map_radicalRetraction W (T i) (hT i)
      (fun v hv => (hW i v hv).1) (fun v hv => (hW i v hv).2),
    radicalRetraction_map_radicalRetraction W (T j) (hT j)
      (fun v hv => (hW j v hv).1) (fun v hv => (hW j v hv).2), hc]

#print axioms radicalQuotientEquiv
#print axioms radicalQuotientEquiv_pairing
#print axioms radicalQuotientEquiv_commute

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
