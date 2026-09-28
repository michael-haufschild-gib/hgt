import GaloisForLFunctions.HTGeometry.RangeDeterminantFormation

/-!
# Range determinant line: image, gauge range, and phase quotient

For an injective formation `F`, the image of the top exterior map is exactly the included range
determinant line; a source gauge `A` leaves the range unchanged and acts on the top exterior power
by `det A`.  In complex coordinates, rescaling one frame vector by `c` rescales the Pluecker vector
by `c` and the Gram determinant (the squared Pluecker norm) by `‖c‖²`: a unit phase is invisible to
Gram positivity.
-/

namespace GaloisForLFunctions.HTGeometry

open Module Set

noncomputable section

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The image of the top exterior formation map is the included range determinant line. -/
theorem range_exteriorPower_map_eq_range_rangeDeterminantToAmbient [FiniteDimensional K V]
    (n : ℕ) (f : V →ₗ[K] W) (hf : Function.Injective f) (hdim : finrank K V = n) :
    LinearMap.range (exteriorPower.map n f) =
      LinearMap.range (rangeDeterminantToAmbient n f) := by
  rw [exteriorPower_formation_factorization, LinearMap.range_comp]
  have hsurj : LinearMap.range (sourceExteriorToRange n f) = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact (sourceDeterminantRangeEquiv n f hf hdim).surjective
  rw [hsurj, Submodule.map_top]

/-- A surjective source gauge leaves the range of a formation map unchanged. -/
theorem range_comp_of_surjective (f : V →ₗ[K] W) {a : V →ₗ[K] V}
    (ha : Function.Surjective a) : LinearMap.range (f.comp a) = LinearMap.range f :=
  LinearMap.range_comp_of_range_eq_top f (LinearMap.range_eq_top.mpr ha)

/-- The top exterior power of a source gauge is its determinant character. -/
theorem exteriorPower_map_top_eq_det_smul {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : Basis ι K V) (a : V →ₗ[K] V) :
    exteriorPower.map (Fintype.card ι) a =
      LinearMap.det a • (LinearMap.id : ⋀[K]^(Fintype.card ι) V →ₗ[K] _) :=
  exteriorPower_map_card_eq_det_smul b a

section Phase

variable {κ : Type*} [Fintype κ] [LinearOrder κ] {d : ℕ}

omit [Fintype κ] [LinearOrder κ] in
/-- Rescaling one frame vector rescales the Pluecker wedge. -/
theorem hermFeatureWedge_update_smul [DecidableEq (Fin d)] (v : Fin d → κ → ℂ) (i : Fin d)
    (c : ℂ) : hermFeatureWedge (Function.update v i (c • v i)) = c • hermFeatureWedge v := by
  unfold hermFeatureWedge
  rw [AlternatingMap.map_update_smul, Function.update_eq_self]

/-- Rescaling one frame vector rescales every maximal minor. -/
theorem hermFeatureMinor_update_smul (v : Fin d → κ → ℂ) (i : Fin d) (c : ℂ)
    (s : Set.powersetCard κ d) :
    hermFeatureMinor (Function.update v i (c • v i)) s = c * hermFeatureMinor v s := by
  classical
  rw [← hermFeatureWedge_coordinate, ← hermFeatureWedge_coordinate,
    hermFeatureWedge_update_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- **Phase quotient.**  Rescaling one frame vector by `c` multiplies the squared Pluecker norm
(equivalently the Gram determinant) by `‖c‖²`. -/
theorem hermPluckerNormSq_update_smul (v : Fin d → κ → ℂ) (i : Fin d) (c : ℂ) :
    hermPluckerNormSq (Function.update v i (c • v i)) = ‖c‖ ^ 2 * hermPluckerNormSq v := by
  unfold hermPluckerNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hermFeatureMinor_update_smul, norm_mul, mul_pow]

/-- A unit phase on one frame vector changes the Pluecker vector but not the Gram determinant. -/
theorem hermFeatureGram_det_update_unit (v : Fin d → κ → ℂ) (i : Fin d) {c : ℂ}
    (hc : ‖c‖ = 1) :
    (hermFeatureGram (Function.update v i (c • v i))).det = (hermFeatureGram v).det := by
  rw [det_hermFeatureGram_eq_pluckerNormSq, det_hermFeatureGram_eq_pluckerNormSq,
    hermPluckerNormSq_update_smul, hc, one_pow, one_mul]

/-- Negating one frame vector negates the Pluecker vector and fixes the Gram determinant. -/
theorem hermFeature_negate_one (v : Fin d → κ → ℂ) (i : Fin d) :
    hermFeatureWedge (Function.update v i ((-1 : ℂ) • v i)) = -hermFeatureWedge v ∧
      (hermFeatureGram (Function.update v i ((-1 : ℂ) • v i))).det =
        (hermFeatureGram v).det := by
  classical
  refine ⟨by rw [hermFeatureWedge_update_smul]; exact neg_one_smul ℂ (hermFeatureWedge v), ?_⟩
  exact hermFeatureGram_det_update_unit v i (by simp)

end Phase

end

end GaloisForLFunctions.HTGeometry
