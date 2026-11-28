import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionNormOfBaseChange

/-! If one completion has the full global degree, it is the only
completion above the base place. The global norm then has one factor. -/

noncomputable section

open NumberField IsDedekindDomain
open scoped GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

theorem localNorm_eq_globalNorm_of_full_degree
    (h : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = Module.finrank K L)
    (y : L) :
    Algebra.norm (v.adicCompletion K) (algebraMap L (w.adicCompletion L) y) =
      algebraMap K (v.adicCompletion K) (Algebra.norm K y) := by
  classical
  let W := finitePlacesAbove L v
  let i : W := ⟨w, (mem_finitePlacesAbove L v w).mpr inferInstance⟩
  let f (j : W) := Module.finrank (v.adicCompletion K) (j.val.adicCompletion L)
  have hs : ∑ j : W, f j = f i := (sum_finiteCompletion_finrank L v).trans h.symm
  have hsingle (j : W) : j = i := by
    by_contra hji
    have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
    have hsum := Finset.sum_erase_add (s := (Finset.univ : Finset W)) f (Finset.mem_univ i)
    rw [hs] at hsum
    have hz : ∑ x ∈ (Finset.univ : Finset W).erase i, f x = 0 := by omega
    have hjle := Finset.single_le_sum (f := f) (fun x _ => Nat.zero_le (f x)) hj
    rw [hz] at hjle
    have hp : 0 < f j := Module.finrank_pos
    omega
  rw [algebraMap_norm_eq_prod_finiteCompletion_norms]
  symm
  exact Fintype.prod_eq_single i (fun j hj => (hj (hsingle j)).elim)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.localNorm_eq_globalNorm_of_full_degree
