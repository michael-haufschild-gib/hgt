import GaloisForLFunctions.HTGeometry.CubicRootSign
import GaloisForLFunctions.HTGeometry.S3ActionFlips
import GaloisForLFunctions.HTGeometry.MultiquadraticNormalFlips

/-!
# Simultaneous cubic root actions with independent discriminants

Independent discriminant square classes give individual sign flips in the
normal ambient field. Together with the full action on each cubic, these
force every tuple of three-letter permutations.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial
variable {F L ι : Type*} [Field F] [Field L] [Algebra F L] [Fintype ι]

/-- The simultaneous action on ordered roots of a finite family of split cubics. -/
def cubicFamilyRootAction (P : ι → Cubic F)
    [∀ i, Fact (((P i).toPoly.map (algebraMap F L)).Splits)]
    (e : ∀ i, (P i).toPoly.rootSet L ≃ Fin 3) :
    (L ≃ₐ[F] L) →* (ι → Equiv.Perm (Fin 3)) :=
  { toFun := fun σ i => cubicOrderedRootAction (P i) (e i) σ
    map_one' := by funext i; exact map_one _
    map_mul' := by intro σ τ; funext i; exact map_mul _ σ τ }

/-- Independent discriminant packets eliminate all finite entanglement between S3 cubics. -/
theorem cubicFamilyRootAction_surjective [CharZero F] [CharZero L] [Normal F L]
    (P : ι → Cubic F) (ha : ∀ i, (P i).a ≠ 0)
    (hirr : ∀ i, Irreducible (P i).toPoly)
    (hind : ∀ T : Finset ι, T.Nonempty → ¬ IsSquare (∏ i ∈ T, (P i).discr))
    [∀ i, Fact (((P i).toPoly.map (algebraMap F L)).Splits)]
    (e : ∀ i, (P i).toPoly.rootSet L ≃ Fin 3) :
    Function.Surjective (cubicFamilyRootAction P e) := by
  classical
  let r : ι → L := fun i => cubicOrderedDiscriminantRoot (P i) (e i)
  have hns (i : ι) : ¬ IsSquare (P i).discr := by
    simpa using hind {i} (Finset.singleton_nonempty i)
  have hsq (i : ι) : r i * r i = algebraMap F L (P i).discr :=
    cubicOrderedDiscriminantRoot_sq (P i) (ha i) (hirr i).separable (e i)
  have hr (i : ι) : r i ≠ 0 := by
    intro h
    have hd : algebraMap F L (P i).discr = 0 := by rw [← hsq i, h, zero_mul]
    have hz : (P i).discr = 0 := (algebraMap F L).injective (hd.trans (map_zero _).symm)
    exact hns i (hz ▸ IsSquare.zero)
  apply s3_hom_surjective_of_coordinate_and_flips
  · intro i
    exact cubicOrderedRootAction_surjective (P i) (ha i) (hirr i) (hns i) (e i)
  · intro i
    obtain ⟨σ, hσi, hσj⟩ := exists_normal_independent_radical_flip
      (fun j => (P j).discr) r (by norm_num) hsq hind Finset.univ i
    refine ⟨σ, ?_, ?_⟩
    · exact (cubicOrderedRootAction_sign_eq_neg_one_iff (P i) (e i) σ (hr i)).mpr hσi
    · intro j hji
      exact (cubicOrderedRootAction_sign_eq_one_iff (P j) (e j) σ (hr j)).mpr
        (hσj j (Finset.mem_univ _) hji)

end GaloisForLFunctions.HTGeometry
