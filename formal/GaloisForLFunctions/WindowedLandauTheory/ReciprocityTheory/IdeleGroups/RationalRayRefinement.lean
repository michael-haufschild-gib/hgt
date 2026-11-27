import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelicRayRefinement
import GaloisForLFunctions.RHTower.Artin.FrobeniusElementsRestrictToASubextension

/-! Multiples of the absolute norm of a modulus give rational ray refinements. -/

noncomputable section

open NumberField GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions

namespace GlobalTheory.Reciprocity.IdeleRay

variable (K : Type*) [Field K] [NumberField K]

theorem normModulus_fin_le_of_absNorm_dvd (m : Modulus K) {d : ℕ} [NeZero d]
    (hd : m.fin.absNorm ∣ d) : (normModulus K d).fin ≤ m.fin := by
  obtain ⟨q, hq⟩ := hd
  change Ideal.span {(d : 𝓞 K)} ≤ m.fin
  rw [Ideal.span_singleton_le_iff_mem, hq, Nat.cast_mul]
  exact m.fin.mul_mem_right _ (Ideal.absNorm_mem m.fin)

theorem normModulus_fin_le_of_dvd {c d : ℕ} [NeZero c] [NeZero d] (h : c ∣ d) :
    (normModulus K d).fin ≤ (normModulus K c).fin := by
  obtain ⟨q, hq⟩ := h
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact ⟨(q : 𝓞 K), by rw [hq, Nat.cast_mul]⟩

/-- Modulus reduction between two rational ray class groups. -/
def rationalRayReduction {c d : ℕ} [NeZero c] [NeZero d] (h : c ∣ d) :
    RayClassGroup (normModulus K d) →* RayClassGroup (normModulus K c) :=
  rayClassReduction _ (normModulus_fin_le_of_dvd K h)

theorem rationalRayReduction_comp_toRayClass {c d : ℕ} [NeZero c] [NeZero d] (h : c ∣ d) :
    (rationalRayReduction K h).comp (toRayClass (normModulus K d)) =
      toRayClass (normModulus K c) :=
  rayClassReduction_comp_toRayClass _ (normModulus_fin_le_of_dvd K h)

end GlobalTheory.Reciprocity.IdeleRay
