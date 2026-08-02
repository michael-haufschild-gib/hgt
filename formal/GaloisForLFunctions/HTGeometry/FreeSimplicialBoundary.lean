import GaloisForLFunctions.HTGeometry.FreeLocallyConvexSeminorm

/-!
# The alternating face differential is bounded

The differential of the free chain complex on a simplicial family is the alternating sum of the maps
induced by the face maps, and a prism operator has the same shape: a finite combination of maps
induced by maps of simplices, with unit coefficients.  Every such combination is bounded for the
free locally convex seminorms, so the differential, an induced chain map, and a prism homotopy are
all continuous.

* `freeBoundary` : the alternating face differential on free modules.
* `freeSeminorm_freeBoundary_le` : **the differential is bounded.**
* `freeSeminorm_freeSimplicialMap_le` : **an induced chain map is bounded.**
* `freeSeminorm_freePrism_le` : **a prism operator is bounded.**
-/

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 : Type*} [NormedField 𝕜]

/-! ## The alternating face differential -/

/-- The alternating sum of the maps induced by a family of face maps. -/
def freeBoundary {A B : Type*} (d : Fin (n + 2) → A → B) : (A →₀ 𝕜) →ₗ[𝕜] (B →₀ 𝕜) :=
  ∑ i : Fin (n + 2), ((-1 : 𝕜) ^ (i : ℕ)) • Finsupp.lmapDomain 𝕜 𝕜 (d i)

theorem freeBoundary_apply {A B : Type*} (d : Fin (n + 2) → A → B) (f : A →₀ 𝕜) :
    freeBoundary (𝕜 := 𝕜) (n := n) d f
      = ∑ i : Fin (n + 2), ((-1 : 𝕜) ^ (i : ℕ)) • Finsupp.mapDomain (d i) f := by
  rw [freeBoundary, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Finsupp.lmapDomain_apply]

/-- **The alternating face differential is bounded** for the free locally convex seminorms. -/
theorem freeSeminorm_freeBoundary_le {A B : Type*} (d : Fin (n + 2) → A → B) (w : B → ℝ)
    (hw : ∀ b, 0 ≤ w b) (f : A →₀ 𝕜) :
    freeSeminorm (𝕜 := 𝕜) w hw (freeBoundary (n := n) d f)
      ≤ ∑ i : Fin (n + 2),
          freeSeminorm (𝕜 := 𝕜) (fun a => w (d i a)) (fun a => hw (d i a)) f := by
  rw [freeBoundary_apply]
  refine le_trans (freeSeminorm_sum_mapDomain_le w hw Finset.univ d
    (fun i => ((-1 : 𝕜) ^ (i : ℕ))) f) (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  have hnorm : ‖((-1 : 𝕜) ^ (i : ℕ))‖ = 1 := by
    rw [norm_pow, norm_neg, norm_one, one_pow]
  rw [hnorm, one_mul]

/-! ## Induced chain maps and prism operators -/

/-- **A map of simplices induces a bounded map of free chain spaces.** -/
theorem freeSeminorm_freeSimplicialMap_le {A B : Type*} (φ : A → B) (w : B → ℝ)
    (hw : ∀ b, 0 ≤ w b) (f : A →₀ 𝕜) :
    freeSeminorm (𝕜 := 𝕜) w hw (Finsupp.lmapDomain 𝕜 𝕜 φ f)
      ≤ freeSeminorm (𝕜 := 𝕜) (fun a => w (φ a)) (fun a => hw (φ a)) f := by
  rw [Finsupp.lmapDomain_apply]
  exact freeSeminorm_mapDomain_le w hw φ f

/-- **A prism operator is bounded**: any finite combination of maps induced by maps of simplices,
with coefficients of norm at most one, is bounded by the sum of the pulled-back seminorms. -/
theorem freeSeminorm_freePrism_le {A B α : Type*} (s : Finset α) (φ : α → A → B) (c : α → 𝕜)
    (hc : ∀ a ∈ s, ‖c a‖ ≤ 1) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) (f : A →₀ 𝕜) :
    freeSeminorm (𝕜 := 𝕜) w hw (∑ a ∈ s, c a • Finsupp.mapDomain (φ a) f)
      ≤ ∑ a ∈ s,
          freeSeminorm (𝕜 := 𝕜) (fun x => w (φ a x)) (fun x => hw (φ a x)) f := by
  refine le_trans (freeSeminorm_sum_mapDomain_le w hw s φ c f) ?_
  refine Finset.sum_le_sum fun a ha => ?_
  have hnn : (0 : ℝ) ≤ freeSeminorm (𝕜 := 𝕜) (fun x => w (φ a x)) (fun x => hw (φ a x)) f :=
    apply_nonneg _ _
  calc ‖c a‖ * freeSeminorm (𝕜 := 𝕜) (fun x => w (φ a x)) (fun x => hw (φ a x)) f
      ≤ 1 * freeSeminorm (𝕜 := 𝕜) (fun x => w (φ a x)) (fun x => hw (φ a x)) f :=
        mul_le_mul_of_nonneg_right (hc a ha) hnn
    _ = freeSeminorm (𝕜 := 𝕜) (fun x => w (φ a x)) (fun x => hw (φ a x)) f := one_mul _

end GaloisForLFunctions

end
