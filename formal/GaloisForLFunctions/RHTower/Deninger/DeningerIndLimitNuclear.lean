import GaloisForLFunctions.RHTower.Deninger.DeningerSigmaNuclear
import GaloisForLFunctions.RHTower.Deninger.DeningerQuotientNuclearCompleted
import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearTransportC

/-!
# A countable inductive limit of nuclear spaces is nuclear

A locally convex final topology under a surjection is the quotient topology of the source, read
through the isomorphism with the quotient by the kernel: its seminorms are the infima of the source
seminorms over the preimages.  So nuclearity passes to it, by quotient permanence together with the
transport of nuclearity along a linear isomorphism.

A locally convex inductive limit is the final topology of the map from the direct sum of the stages.
Its seminorms are therefore the final seminorms of the direct sum seminorms, each stage maps
continuously into the limit, and every seminorm bounded on each stage is dominated by one of them —
so this presentation really is the inductive limit topology, and not a coarser one.  Since a
countable direct sum of nuclear spaces is nuclear, so is a countable inductive limit.

* `deningerFinalSeminorm` : **the seminorm of a locally convex final topology.**
* `deningerFinalSeminorm_le`, `le_deningerFinalSeminorm` : it is the largest seminorm bounded by the
  source seminorm on preimages.
* `deningerIsNuclearSpaceC_final` : **nuclearity passes to a final topology.**
* `deningerIndLimitFamily`, `deningerIndLimitFamily_stage_le`, `le_deningerIndLimitFamily` : the
  inductive limit presentation and its universal property.
* `deningerIsNuclearSpaceC_indLimit` : **a countable inductive limit of nuclear spaces is
  nuclear.**
-/

namespace RHTower

open scoped NNReal

section Final

variable {𝕜 E L : Type*} [NontriviallyNormedField 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup L] [Module 𝕜 L]

/-- The isomorphism of the quotient by the kernel with the target of a surjection. -/
noncomputable def deningerQuotKerEquiv (S : E →ₗ[𝕜] L) (hS : Function.Surjective S) :
    (E ⧸ LinearMap.ker S) ≃ₗ[𝕜] L :=
  S.quotKerEquivOfSurjective hS

theorem deningerQuotKerEquiv_mk (S : E →ₗ[𝕜] L) (hS : Function.Surjective S) (x : E) :
    deningerQuotKerEquiv S hS (Submodule.Quotient.mk x) = S x :=
  LinearMap.quotKerEquivOfSurjective_apply_mk S hS x

theorem deningerQuotKerEquiv_symm_apply (S : E →ₗ[𝕜] L) (hS : Function.Surjective S) (x : E) :
    (deningerQuotKerEquiv S hS).symm (S x)
      = (Submodule.Quotient.mk x : E ⧸ LinearMap.ker S) := by
  rw [LinearEquiv.symm_apply_eq, deningerQuotKerEquiv_mk]

/-- **The seminorm of a locally convex final topology**: the infimum of a seminorm of the source
over the preimages of a surjection. -/
noncomputable def deningerFinalSeminorm (S : E →ₗ[𝕜] L) (hS : Function.Surjective S)
    (p : Seminorm 𝕜 E) : Seminorm 𝕜 L :=
  (deningerQuotientSeminorm (LinearMap.ker S) p).comp
    ((deningerQuotKerEquiv S hS).symm : L →ₗ[𝕜] (E ⧸ LinearMap.ker S))

theorem deningerFinalSeminorm_apply (S : E →ₗ[𝕜] L) (hS : Function.Surjective S)
    (p : Seminorm 𝕜 E) (y : L) :
    deningerFinalSeminorm S hS p y
      = deningerQuotientSeminorm (LinearMap.ker S) p ((deningerQuotKerEquiv S hS).symm y) :=
  Seminorm.comp_apply _ _ _

/-- The final seminorm is at most the source seminorm of any preimage. -/
theorem deningerFinalSeminorm_le (S : E →ₗ[𝕜] L) (hS : Function.Surjective S)
    (p : Seminorm 𝕜 E) (x : E) : deningerFinalSeminorm S hS p (S x) ≤ p x := by
  rw [deningerFinalSeminorm_apply, deningerQuotKerEquiv_symm_apply]
  exact deningerQuotientSeminorm_mk_le _ _ x

/-- **The final seminorm is the largest seminorm bounded by the source seminorm on preimages.** -/
theorem le_deningerFinalSeminorm (S : E →ₗ[𝕜] L) (hS : Function.Surjective S)
    (p : Seminorm 𝕜 E) (r : Seminorm 𝕜 L) (h : ∀ x : E, r (S x) ≤ p x) (y : L) :
    r y ≤ deningerFinalSeminorm S hS p y := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨z, hz, hlt⟩ := deningerQuotientSeminorm_exists_lt (LinearMap.ker S) p
    ((deningerQuotKerEquiv S hS).symm y) hε
  have hSz : S z = y := by
    have hcong := congrArg (deningerQuotKerEquiv S hS) hz
    rwa [deningerQuotKerEquiv_mk, LinearEquiv.apply_symm_apply] at hcong
  calc r y = r (S z) := by rw [hSz]
    _ ≤ p z := h z
    _ ≤ deningerFinalSeminorm S hS p y + ε := by
        rw [deningerFinalSeminorm_apply]
        exact hlt.le

end Final

section IndLimitFamily

variable {𝕜 L : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup L] [Module 𝕜 L]
variable {ι : Type*} [DecidableEq ι] {F : ι → Type*}
variable [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)]

/-- **The presentation of a locally convex inductive limit**: the final seminorms of the map from
the direct sum of the stages. -/
noncomputable def deningerIndLimitFamily {κ : ι → Type*} (P : ∀ i, SeminormFamily 𝕜 (F i) (κ i))
    (S : (Π₀ i, F i) →ₗ[𝕜] L) (hS : Function.Surjective S) :
    SeminormFamily 𝕜 L ((∀ i, κ i) × (ι → ℝ≥0)) :=
  fun ac => deningerFinalSeminorm S hS (deningerSigmaFamily P ac)

/-- **Each stage maps continuously into the inductive limit.** -/
theorem deningerIndLimitFamily_stage_le {κ : ι → Type*} (P : ∀ i, SeminormFamily 𝕜 (F i) (κ i))
    (S : (Π₀ i, F i) →ₗ[𝕜] L) (hS : Function.Surjective S)
    (ac : (∀ i, κ i) × (ι → ℝ≥0)) (i : ι) (u : F i) :
    deningerIndLimitFamily P S hS ac (S (DFinsupp.lsingle (R := 𝕜) i u))
      ≤ (ac.2 i : ℝ) * P i (ac.1 i) u :=
  le_trans (deningerFinalSeminorm_le S hS _ _) (le_of_eq (deningerSigmaFamily_single P ac i u))

/-- **The inductive limit topology is the finest one making every stage continuous**: a seminorm
bounded on each stage is dominated by a member of the presentation. -/
theorem le_deningerIndLimitFamily {κ : ι → Type*} (P : ∀ i, SeminormFamily 𝕜 (F i) (κ i))
    (S : (Π₀ i, F i) →ₗ[𝕜] L) (hS : Function.Surjective S) (r : Seminorm 𝕜 L)
    (α : ∀ i, κ i) (C : ι → ℝ≥0)
    (h : ∀ (i : ι) (u : F i), r (S (DFinsupp.lsingle (R := 𝕜) i u)) ≤ (C i : ℝ) * P i (α i) u)
    (y : L) : r y ≤ deningerIndLimitFamily P S hS (α, C) y := by
  classical
  have hsub : ∀ (s : Finset ι) (g : ι → L), r (∑ i ∈ s, g i) ≤ ∑ i ∈ s, r (g i) := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (map_add_le_add r _ _) (add_le_add le_rfl ih)
  refine le_deningerFinalSeminorm S hS _ r (fun x => ?_) y
  have hfin := x.finite_support
  have hsupp : ∀ i ∉ hfin.toFinset, x i = 0 := by
    intro i hi
    by_contra hne
    exact hi (hfin.mem_toFinset.mpr hne)
  have hx : x = ∑ i ∈ hfin.toFinset, DFinsupp.lsingle (R := 𝕜) i (x i) :=
    deningerSigma_eq_sum_single (𝕜 := 𝕜) x hfin.toFinset hsupp
  have hSx : S x = ∑ i ∈ hfin.toFinset, S (DFinsupp.lsingle (R := 𝕜) i (x i)) := by
    conv_lhs => rw [hx]
    rw [map_sum]
  have hsum : Summable fun i => (C i : ℝ) * P i (α i) (x i) := by
    have h0 := deningerSigmaSummable (fun i => C i • P i (α i)) x
    have hco : ∀ i, ((C i • P i (α i)) : Seminorm 𝕜 (F i)) (x i)
        = (C i : ℝ) * P i (α i) (x i) := fun i => by
      rw [smul_apply, NNReal.smul_def, smul_eq_mul]
    simpa only [hco] using h0
  calc r (S x) = r (∑ i ∈ hfin.toFinset, S (DFinsupp.lsingle (R := 𝕜) i (x i))) := by rw [hSx]
    _ ≤ ∑ i ∈ hfin.toFinset, r (S (DFinsupp.lsingle (R := 𝕜) i (x i))) := hsub _ _
    _ ≤ ∑ i ∈ hfin.toFinset, (C i : ℝ) * P i (α i) (x i) :=
        Finset.sum_le_sum fun i _ => h i (x i)
    _ ≤ deningerSigmaFamily P (α, C) x := by
        rw [deningerSigmaFamily_apply]
        exact hsum.sum_le_tsum _ fun i _ => mul_nonneg (C i).coe_nonneg (apply_nonneg _ _)

end IndLimitFamily

section Nuclear

variable {𝕜 E L : Type*} [RCLike 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup L] [Module 𝕜 L]

/-- **Nuclearity passes to a locally convex final topology.** -/
theorem deningerIsNuclearSpaceC_final {ι : Type*} (P : SeminormFamily 𝕜 E ι)
    (hP : DeningerIsNuclearSpaceC P) (S : E →ₗ[𝕜] L) (hS : Function.Surjective S) :
    DeningerIsNuclearSpaceC (fun i => deningerFinalSeminorm S hS (P i)) := by
  have hquot : DeningerIsNuclearSpaceC
      (fun i => deningerQuotientSeminorm (LinearMap.ker S) (P i)) :=
    deningerIsNuclearSpaceC_quotient_of_C P (LinearMap.ker S) hP
  refine deningerIsNuclearSpaceC_of_linearEquiv
    (fun i => deningerFinalSeminorm S hS (P i))
    (fun i => deningerQuotientSeminorm (LinearMap.ker S) (P i))
    ((deningerQuotKerEquiv S hS).symm) (fun i y => ?_) hquot
  exact deningerFinalSeminorm_apply S hS (P i) y

variable {ι : Type} [DecidableEq ι] [Countable ι] {F : ι → Type*}
variable [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)]

/-- **A countable inductive limit of nuclear spaces is nuclear.** -/
theorem deningerIsNuclearSpaceC_indLimit {κ : ι → Type*} (P : ∀ i, SeminormFamily 𝕜 (F i) (κ i))
    (hP : ∀ i, DeningerIsNuclearSpaceC (P i)) (S : (Π₀ i, F i) →ₗ[𝕜] L)
    (hS : Function.Surjective S) :
    DeningerIsNuclearSpaceC (deningerIndLimitFamily P S hS) :=
  deningerIsNuclearSpaceC_final _ (deningerIsNuclearSpaceC_sigma P hP) S hS

end Nuclear

end RHTower
