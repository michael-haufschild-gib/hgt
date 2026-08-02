import Mathlib.Analysis.Seminorm
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# The free locally convex seminorms on a free module

The free locally convex space on a set is the free module with the locally convex direct sum
topology, whose seminorms are the weighted `ℓ¹` seminorms `f ↦ ∑ ‖f i‖ w i` for nonnegative
weights `w`.  A map of index sets induces a linear map bounded for these seminorms, with the
pulled-back weight as the dominating seminorm — so any finite combination of set-induced maps, such
as a simplicial differential or a prism operator, is continuous.

* `freeSeminorm` : **the weighted `ℓ¹` seminorm on the free module on a set.**
* `freeSeminorm_single` : its value on a generator.
* `freeSeminorm_mapDomain_le` : **a map of index sets induces a bounded linear map.**
-/

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 ι κ : Type*} [NormedField 𝕜]

/-! ## The weighted `ℓ¹` seminorm -/

/-- The value of the weighted `ℓ¹` seminorm on the free module. -/
def freeSeminormFun (w : ι → ℝ) (f : ι →₀ 𝕜) : ℝ := f.sum fun i c => ‖c‖ * w i

theorem freeSeminormFun_zero (w : ι → ℝ) : freeSeminormFun (𝕜 := 𝕜) w 0 = 0 := by
  simp [freeSeminormFun]

theorem freeSeminormFun_single (w : ι → ℝ) (i : ι) (c : 𝕜) :
    freeSeminormFun w (Finsupp.single i c) = ‖c‖ * w i := by
  rw [freeSeminormFun, Finsupp.sum_single_index]
  rw [norm_zero, zero_mul]

theorem freeSeminormFun_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (f : ι →₀ 𝕜) :
    0 ≤ freeSeminormFun w f := by
  refine Finset.sum_nonneg fun i _ => ?_
  exact mul_nonneg (norm_nonneg _) (hw i)

theorem freeSeminormFun_add_le {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (f g : ι →₀ 𝕜) :
    freeSeminormFun w (f + g) ≤ freeSeminormFun w f + freeSeminormFun w g := by
  classical
  have hf : freeSeminormFun w f = ∑ i ∈ f.support ∪ g.support, ‖f i‖ * w i := by
    refine Finsupp.sum_of_support_subset f Finset.subset_union_left _ ?_
    intro i _
    rw [norm_zero, zero_mul]
  have hg : freeSeminormFun w g = ∑ i ∈ f.support ∪ g.support, ‖g i‖ * w i := by
    refine Finsupp.sum_of_support_subset g Finset.subset_union_right _ ?_
    intro i _
    rw [norm_zero, zero_mul]
  have hfg : freeSeminormFun w (f + g)
      = ∑ i ∈ f.support ∪ g.support, ‖(f + g) i‖ * w i := by
    refine Finsupp.sum_of_support_subset (f + g) Finsupp.support_add _ ?_
    intro i _
    rw [norm_zero, zero_mul]
  rw [hf, hg, hfg, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hnorm : ‖(f + g) i‖ ≤ ‖f i‖ + ‖g i‖ := by
    rw [Finsupp.add_apply]
    exact norm_add_le _ _
  calc ‖(f + g) i‖ * w i ≤ (‖f i‖ + ‖g i‖) * w i :=
        mul_le_mul_of_nonneg_right hnorm (hw i)
    _ = ‖f i‖ * w i + ‖g i‖ * w i := by ring

theorem freeSeminormFun_smul (w : ι → ℝ) (c : 𝕜) (f : ι →₀ 𝕜) :
    freeSeminormFun w (c • f) = ‖c‖ * freeSeminormFun w f := by
  classical
  have hc : freeSeminormFun w (c • f) = ∑ i ∈ f.support, ‖(c • f) i‖ * w i := by
    refine Finsupp.sum_of_support_subset (c • f) Finsupp.support_smul _ ?_
    intro i _
    rw [norm_zero, zero_mul]
  rw [hc, freeSeminormFun, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, norm_mul, mul_assoc]

/-- **The weighted `ℓ¹` seminorm on the free module on a set.** -/
def freeSeminorm (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) : Seminorm 𝕜 (ι →₀ 𝕜) where
  toFun := freeSeminormFun w
  map_zero' := freeSeminormFun_zero w
  add_le' := freeSeminormFun_add_le hw
  neg' f := by
    have h := freeSeminormFun_smul w (-1 : 𝕜) f
    rw [neg_one_smul, norm_neg, norm_one, one_mul] at h
    exact h
  smul' := freeSeminormFun_smul w

@[simp] theorem freeSeminorm_apply (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (f : ι →₀ 𝕜) :
    freeSeminorm (𝕜 := 𝕜) w hw f = freeSeminormFun w f := rfl

theorem freeSeminorm_single (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (i : ι) (c : 𝕜) :
    freeSeminorm (𝕜 := 𝕜) w hw (Finsupp.single i c) = ‖c‖ * w i :=
  freeSeminormFun_single w i c

/-! ## Splitting off a generator -/

theorem freeSeminormFun_single_add (w : ι → ℝ) {i : ι} {c : 𝕜} {f : ι →₀ 𝕜}
    (hi : i ∉ f.support) :
    freeSeminormFun w (Finsupp.single i c + f) = ‖c‖ * w i + freeSeminormFun w f := by
  classical
  have hdisj : Disjoint (Finsupp.single i c).support f.support := by
    refine Finset.disjoint_left.mpr fun j hj hjf => ?_
    have hji : j = i := Finset.mem_singleton.mp (Finsupp.support_single_subset hj)
    rw [hji] at hjf
    exact hi hjf
  rw [freeSeminormFun, Finsupp.sum_add_index_of_disjoint hdisj]
  congr 1
  exact freeSeminormFun_single w i c

/-! ## Maps induced by set maps -/

/-- **A map of index sets induces a bounded linear map**: the seminorm of the image is bounded by
the seminorm of the argument for the pulled-back weight. -/
theorem freeSeminorm_mapDomain_le (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (φ : ι → κ) (f : ι →₀ 𝕜) :
    freeSeminorm (𝕜 := 𝕜) w hw (Finsupp.mapDomain φ f)
      ≤ freeSeminorm (𝕜 := 𝕜) (fun i => w (φ i)) (fun i => hw (φ i)) f := by
  classical
  induction f using Finsupp.induction with
  | zero =>
    rw [Finsupp.mapDomain_zero]
    exact le_of_eq (by rw [freeSeminorm_apply, freeSeminorm_apply, freeSeminormFun_zero,
      freeSeminormFun_zero])
  | single_add i c f hi _ ih =>
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    refine le_trans (map_add_le_add (freeSeminorm (𝕜 := 𝕜) w hw) _ _) ?_
    have hright : freeSeminorm (𝕜 := 𝕜) (fun j => w (φ j)) (fun j => hw (φ j))
        (Finsupp.single i c + f)
        = ‖c‖ * w (φ i)
          + freeSeminorm (𝕜 := 𝕜) (fun j => w (φ j)) (fun j => hw (φ j)) f := by
      rw [freeSeminorm_apply, freeSeminorm_apply,
        freeSeminormFun_single_add (fun j => w (φ j)) hi]
    rw [hright]
    refine add_le_add (le_of_eq ?_) ih
    exact freeSeminorm_single w hw (φ i) c

/-- **A finite combination of set-induced maps is bounded** — the shape of a simplicial
differential or a prism operator. -/
theorem freeSeminorm_sum_mapDomain_le (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) {α : Type*} (s : Finset α)
    (φ : α → ι → κ) (c : α → 𝕜) (f : ι →₀ 𝕜) :
    freeSeminorm (𝕜 := 𝕜) w hw (∑ a ∈ s, c a • Finsupp.mapDomain (φ a) f)
      ≤ ∑ a ∈ s, ‖c a‖
        * freeSeminorm (𝕜 := 𝕜) (fun i => w (φ a i)) (fun i => hw (φ a i)) f := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, freeSeminorm_apply, freeSeminormFun_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine le_trans (map_add_le_add (freeSeminorm (𝕜 := 𝕜) w hw) _ _) (add_le_add ?_ ih)
    rw [map_smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (freeSeminorm_mapDomain_le w hw (φ a) f) (norm_nonneg _)

end GaloisForLFunctions

end
