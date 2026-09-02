import GaloisForLFunctions.HTGeometry.PseudoDiffOpValuation

/-!
# Completion of the rational pseudodifferential division ring

Mathlib's `CompletableTopField` and completion field instance are stated for commutative fields.
Their proof uses only division-ring algebra.  This file supplies the corresponding noncommutative
class and completion instances, then verifies its Cauchy-inversion condition for the valuation
topology on `PseudoDiffOp K`.
-/

noncomputable section

open Filter Set
open Topology
open uniformity
open UniformSpace UniformSpace.Completion
open scoped WithZeroTopology

namespace GaloisForLFunctions.HTGeometry

namespace DivisionCompletion

/-- A topological division ring is completable when it is separated and inversion sends every
Cauchy filter bounded away from zero to a Cauchy filter. -/
class CompletableTopDivisionRing (D : Type*) [DivisionRing D] [UniformSpace D] : Prop
    extends T0Space D where
  nice : ∀ F : Filter D, Cauchy F → 𝓝 0 ⊓ F = ⊥ →
    Cauchy (Filter.map (fun x => x⁻¹) F)

variable (D : Type*) [DivisionRing D] [UniformSpace D]

/-- A separated division ring embeds nontrivially in its uniform completion. -/
instance instNontrivial [T0Space D] : Nontrivial (Completion D) :=
  (isUniformEmbedding_coe D).injective.nontrivial

/-- Extension of inversion from a division ring to its uniform completion. -/
def hatInv : Completion D → Completion D :=
  isDenseInducing_coe.extend fun x : D => (↑x⁻¹ : Completion D)

@[fun_prop] theorem continuous_hatInv [CompletableTopDivisionRing D]
    {x : Completion D} (h : x ≠ 0) : ContinuousAt (hatInv D) x := by
  refine isDenseInducing_coe.continuousAt_extend ?_
  apply mem_of_superset (compl_singleton_mem_nhds h)
  intro y y_ne
  rw [mem_compl_singleton_iff] at y_ne
  apply CompleteSpace.complete
  have heq : (fun (x : D) => (↑x⁻¹ : Completion D)) =
      ((fun (y : D) => (↑y : Completion D)) ∘ (fun (x : D) => (x⁻¹ : D))) := by
    simp [Function.comp_def]
  rw [heq, ← Filter.map_map]
  apply Cauchy.map _ (Completion.uniformContinuous_coe D)
  apply CompletableTopDivisionRing.nice
  · haveI := isDenseInducing_coe.comap_nhds_neBot y
    apply cauchy_nhds.comap
    rw [Completion.comap_coe_eq_uniformity]
  · have eq_bot : 𝓝 (0 : Completion D) ⊓ 𝓝 y = ⊥ := by
      by_contra hbot
      exact y_ne (eq_of_nhds_neBot <| neBot_iff.mpr hbot).symm
    rw [isDenseInducing_coe.nhds_eq_comap (0 : D), ← Filter.comap_inf]
    norm_cast
    rw [eq_bot]
    exact comap_bot

open scoped Classical in
/-- Inversion on a division-ring completion, with zero fixed. -/
instance instInv [CompletableTopDivisionRing D] : Inv (Completion D) :=
  ⟨fun x => if x = 0 then 0 else hatInv D x⟩

variable [IsTopologicalDivisionRing D] [CompletableTopDivisionRing D]

omit [CompletableTopDivisionRing D] in
/-- Extended inversion agrees with inversion on the dense source division ring. -/
theorem hatInv_extends {x : D} (h : x ≠ 0) :
    hatInv D (x : Completion D) = ↑(x⁻¹ : D) :=
  isDenseInducing_coe.extend_eq_at
    ((continuous_coe D).continuousAt.comp (continuousAt_inv₀ h))

@[norm_cast] theorem coe_inv (x : D) :
    (x : Completion D)⁻¹ = ((x⁻¹ : D) : Completion D) := by
  by_cases h : x = 0
  · rw [h, inv_zero]
    dsimp [Inv.inv]
    norm_cast
    simp
  · conv_lhs => dsimp [Inv.inv]
    rw [if_neg]
    · exact hatInv_extends D h
    · exact fun H => h (isDenseEmbedding_coe.injective H)

variable [IsUniformAddGroup D]

/-- Every nonzero completion element has the extended inverse as a right inverse. -/
theorem mul_hatInv_cancel {x : Completion D} (hx : x ≠ 0) :
    x * hatInv D x = 1 := by
  haveI : T1Space (Completion D) := T2Space.t1Space
  let f := fun x : Completion D => x * hatInv D x
  let c := fun x : D => (x : Completion D)
  change f x = 1
  have hcont : ContinuousAt f x := by fun_prop
  have hclosure : x ∈ closure (c '' {0}ᶜ) := by
    have hdense := isDenseInducing_coe.dense x
    rw [← image_univ, show (univ : Set D) = {0} ∪ {0}ᶜ from (union_compl_self _).symm,
      image_union] at hdense
    apply mem_closure_of_mem_closure_union hdense
    rw [image_singleton]
    exact compl_singleton_mem_nhds hx
  have hfclosure : f x ∈ closure (f '' c '' {0}ᶜ) := mem_closure_image hcont hclosure
  have hsubset : f '' c '' {0}ᶜ ⊆ {1} := by
    rw [image_image]
    rintro _ ⟨z, z_ne, rfl⟩
    rw [mem_singleton_iff]
    rw [mem_compl_singleton_iff] at z_ne
    dsimp [f]
    rw [hatInv_extends D z_ne, ← coe_mul, mul_inv_cancel₀ z_ne, coe_one]
  replace hfclosure := closure_mono hsubset hfclosure
  rwa [closure_singleton, mem_singleton_iff] at hfclosure

/-- The uniform completion of a completable topological division ring is a division ring. -/
instance instDivisionRing [Nontrivial (Completion D)] : DivisionRing (Completion D) where
  mul_inv_cancel := fun x hx => by
    simp only [Inv.inv, if_neg hx, mul_hatInv_cancel D hx]
  inv_zero := by simp only [Inv.inv, ite_true]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- The completed division ring has continuous inversion away from zero. -/
instance instIsTopologicalDivisionRing [Nontrivial (Completion D)] :
    IsTopologicalDivisionRing (Completion D) :=
  { Completion.topologicalRing with
    continuousAt_inv₀ := by
      intro x hx
      have heq : {y | hatInv D y = y⁻¹} ∈ 𝓝 x :=
        have hsubset : {(0 : Completion D)}ᶜ ⊆ {y : Completion D | hatInv D y = y⁻¹} := by
          intro y hy
          rw [mem_compl_singleton_iff] at hy
          dsimp [Inv.inv]
          rw [if_neg hy]
        mem_of_superset (compl_singleton_mem_nhds hx) hsubset
      exact ContinuousAt.congr (continuous_hatInv D hx) heq }

end DivisionCompletion

namespace DivisionValuedCompletion

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Valued

variable {D : Type*} [DivisionRing D]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [hv : Valued D Γ₀] [DivisionCompletion.CompletableTopDivisionRing D]

local notation "hat" => UniformSpace.Completion

/-- Extension of a division-ring valuation to its uniform completion, valued first in its
intrinsic value group. -/
noncomputable def extension : hat D → ValueGroup₀ (.ofClass hv.v) :=
  Completion.isDenseInducing_coe.extend hv.v.restrict

/-- The intrinsic-value-group extension is continuous. -/
theorem continuous_extension : Continuous (extension : hat D → _) := by
  refine Completion.isDenseInducing_coe.continuous_extend ?_
  intro x₀
  rcases eq_or_ne x₀ 0 with (rfl | hx₀)
  · refine ⟨0, ?_⟩
    rw [← Completion.coe_zero, ← Completion.isDenseInducing_coe.isInducing.nhds_eq_comap]
    exact Valued.continuous_valuation.tendsto' 0 0 (map_zero hv.v.restrict)
  · have preimage_one : hv.v ⁻¹' {(1 : Γ₀)} ∈ 𝓝 (1 : D) := by
      have hone : (hv.v (1 : D) : Γ₀) ≠ 0 := by
        rw [Valuation.map_one]
        exact zero_ne_one.symm
      convert! Valued.locally_const hone
      ext x
      rw [Valuation.map_one, mem_preimage, mem_singleton_iff, mem_setOf_eq]
    obtain ⟨V, V_in, hV⟩ : ∃ V ∈ 𝓝 (1 : hat D),
        ∀ x : D, (x : hat D) ∈ V → (hv.v x : Γ₀) = 1 := by
      rwa [Completion.isDenseInducing_coe.nhds_eq_comap, mem_comap] at preimage_one
    have hV' : ∃ V' ∈ 𝓝 (1 : hat D), (0 : hat D) ∉ V' ∧
        ∀ x (_ : x ∈ V') y (_ : y ∈ V'), x * y⁻¹ ∈ V := by
      have htend : Tendsto (fun p : hat D × hat D => p.1 * p.2⁻¹)
          ((𝓝 1) ×ˢ (𝓝 1)) (𝓝 1) := by
        rw [← nhds_prod_eq]
        conv =>
          congr
          rfl
          rfl
          rw [← one_mul (1 : hat D)]
        refine Tendsto.mul continuous_fst.continuousAt
          (Tendsto.comp ?_ continuous_snd.continuousAt)
        convert! (continuousAt_inv₀ (zero_ne_one.symm : 1 ≠ (0 : hat D))).tendsto
        exact inv_one.symm
      rcases tendsto_prod_self_iff.mp htend V V_in with ⟨U, U_in, hU⟩
      let Dstar := ({0}ᶜ : Set (hat D))
      have hstar : Dstar ∈ 𝓝 (1 : hat D) :=
        compl_singleton_mem_nhds zero_ne_one.symm
      exact ⟨U ∩ Dstar, Filter.inter_mem U_in hstar,
        ⟨fun ⟨_, h'⟩ => h' rfl,
          fun x ⟨hx, _⟩ y ⟨hy, _⟩ => hU _ _ hx hy⟩⟩
    rcases hV' with ⟨V', V'_in, zeroV', hV'⟩
    have nhds_right : (fun x => x * x₀) '' V' ∈ 𝓝 x₀ := by
      have hl : Function.LeftInverse (fun x : hat D => x * x₀⁻¹)
          (fun x : hat D => x * x₀) := by
        intro x
        simp only [mul_assoc, mul_inv_cancel₀ hx₀, mul_one]
      have hr : Function.RightInverse (fun x : hat D => x * x₀⁻¹)
          (fun x : hat D => x * x₀) := by
        intro x
        simp only [mul_assoc, inv_mul_cancel₀ hx₀, mul_one]
      have hc : Continuous (fun x : hat D => x * x₀⁻¹) := by fun_prop
      rw [image_eq_preimage_of_inverse hl hr]
      rw [← mul_inv_cancel₀ hx₀] at V'_in
      exact hc.continuousAt V'_in
    have hz : ∃ z₀ : D, ∃ y₀ ∈ V',
        (z₀ : hat D) = y₀ * x₀ ∧ z₀ ≠ 0 := by
      rcases Completion.denseRange_coe.mem_nhds nhds_right with
        ⟨z₀, y₀, y₀_in, H : y₀ * x₀ = z₀⟩
      refine ⟨z₀, y₀, y₀_in, H.symm, ?_⟩
      rintro rfl
      exact mul_ne_zero (ne_of_mem_of_not_mem y₀_in zeroV') hx₀ H
    rcases hz with ⟨z₀, y₀, y₀_in, hz₀, z₀_ne⟩
    have vz₀_ne : hv.v.restrict z₀ ≠ 0 := by rwa [Valuation.ne_zero_iff]
    refine ⟨hv.v.restrict z₀, ?_⟩
    rw [WithZeroTopology.tendsto_of_ne_zero vz₀_ne, eventually_comap]
    filter_upwards [nhds_right] with x x_in a ha
    rcases x_in with ⟨y, y_in, rfl⟩
    have hone : hv.v.restrict (a * z₀⁻¹) = 1 := by
      rw [hv.v.restrict_def, ValueGroup₀.restrict₀_eq_one_iff]
      apply hV
      rw [Completion.coe_mul, ← DivisionCompletion.coe_inv D z₀]
      have heq : (a : hat D) * (z₀ : hat D)⁻¹ = y * y₀⁻¹ := by
        calc
          (a : hat D) * (z₀ : hat D)⁻¹ =
              (y * x₀) * (y₀ * x₀)⁻¹ := by rw [ha, hz₀]
          _ = (y * x₀) * (x₀⁻¹ * y₀⁻¹) := by rw [mul_inv_rev]
          _ = y * y₀⁻¹ := by
            simp only [mul_assoc, ← mul_assoc x₀ x₀⁻¹ y₀⁻¹,
              mul_inv_cancel₀ hx₀, one_mul]
      rw [heq]
      exact hV' y y_in y₀ y₀_in
    calc
      hv.v.restrict a = hv.v.restrict (a * z₀⁻¹ * z₀) := by
        rw [mul_assoc, inv_mul_cancel₀ z₀_ne, mul_one]
      _ = hv.v.restrict (a * z₀⁻¹) * hv.v.restrict z₀ :=
        Valuation.map_mul _ _ _
      _ = hv.v.restrict z₀ := by rw [hone, one_mul]

omit [DivisionCompletion.CompletableTopDivisionRing D] in
/-- The intrinsic extension agrees with the source valuation on the dense embedding. -/
@[simp, norm_cast] theorem extension_extends (x : D) :
    extension (x : hat D) = hv.v.restrict x := by
  refine Completion.isDenseInducing_coe.extend_eq_of_tendsto ?_
  rw [← Completion.isDenseInducing_coe.nhds_eq_comap]
  exact Valued.continuous_valuation.continuousAt

/-- Extension of a valuation on a division ring to its completed division ring. -/
noncomputable def extensionValuation : Valuation (hat D) Γ₀ where
  toFun := ValueGroup₀.embedding ∘ extension
  map_zero' := by
    rw [Function.comp_apply, map_eq_zero, ← hv.v.restrict.map_zero (R := D),
      ← extension_extends (0 : D), Completion.coe_zero]
  map_one' := by
    rw [Function.comp_apply, ← Completion.coe_one, extension_extends (1 : D),
      Valuation.map_one _, map_one]
  map_mul' x y := by
    simp only [Function.comp_apply, ← map_mul]
    rw [embedding_strictMono.injective.eq_iff]
    apply Completion.induction_on₂ x y
      (p := fun x y => extension (x * y) = extension x * extension y)
    · have c1 : Continuous fun x : hat D × hat D => extension (x.1 * x.2) :=
        continuous_extension.comp (continuous_fst.mul continuous_snd)
      have c2 : Continuous fun x : hat D × hat D => extension x.1 * extension x.2 :=
        (continuous_extension.comp continuous_fst).mul
          (continuous_extension.comp continuous_snd)
      exact isClosed_eq c1 c2
    · intro x y
      norm_cast
      exact Valuation.map_mul _ _ _
  map_add_le_max' x y := by
    simp_rw [le_max_iff, Function.comp_apply]
    rw [embedding_strictMono.le_iff_le, embedding_strictMono.le_iff_le (f := embedding)]
    apply Completion.induction_on₂ x y
      (p := fun x y => extension (x + y) ≤ extension x ∨ extension (x + y) ≤ extension y)
    · have hcont : Continuous (extension : hat D → _) := continuous_extension
      exact (isClosed_le (by fun_prop) <| hcont.comp continuous_fst).union
        (isClosed_le (by fun_prop) <| hcont.comp continuous_snd)
    · intro x y
      norm_cast
      exact le_max_iff.mp (hv.v.restrict.map_add x y)

@[simp] theorem extensionValuation_apply_coe (x : D) :
    extensionValuation (x : hat D) = hv.v x := by
  simp [extensionValuation, extension_extends]

end DivisionValuedCompletion

namespace DiffOp

open scoped Differential
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Valued

variable {K : Type*} [Field K] [Differential K]

/-- The order-valued rational pseudodifferential division ring satisfies the Cauchy-inversion
criterion, hence its completion is again a division ring. -/
instance pseudoDiffOpCompletable :
    DivisionCompletion.CompletableTopDivisionRing
      (WithVal (pseudoDiffOpValuation (K := K))) :=
  { ValuedRing.separated with
    nice := by
      letI hvD : Valued (WithVal (pseudoDiffOpValuation (K := K)))
          PseudoDiffOpValueGroup := inferInstance
      rintro F hF h0
      have hbound : ∃ γ₀ : (ValueGroup₀ (.ofClass hvD.v))ˣ, ∃ M ∈ F,
          ∀ x ∈ M, (γ₀.1) ≤ hvD.v.restrict x := by
        rcases Filter.inf_eq_bot_iff.mp h0 with ⟨U, U_in, M, M_in, H⟩
        rcases Valued.mem_nhds_zero.mp U_in with ⟨γ₀, hU⟩
        exact ⟨γ₀, M, M_in, fun x xM => le_of_not_gt (fun hyp => by
          have hxU : x ∈ U ∩ M := ⟨hU hyp, xM⟩
          rwa [H] at hxU)⟩
      rcases hbound with ⟨γ₀, M₀, M₀_in, H₀⟩
      rw [Valued.cauchy_iff] at hF ⊢
      refine ⟨hF.1.map _, ?_⟩
      replace hF := hF.2
      intro γ
      rcases hF (min (γ * γ₀ * γ₀) γ₀) with ⟨M₁, M₁_in, H₁⟩
      use (fun x : WithVal (pseudoDiffOpValuation (K := K)) => x⁻¹) '' (M₀ ∩ M₁)
      constructor
      · rw [mem_map]
        exact mem_of_superset (Filter.inter_mem M₀_in M₁_in) (subset_preimage_image _ _)
      · rintro _ ⟨x, ⟨x_in₀, x_in₁⟩, rfl⟩ _ ⟨y, ⟨_, y_in₁⟩, rfl⟩
        simp only
        specialize H₁ x x_in₁ y y_in₁
        replace x_in₀ := H₀ x x_in₀
        apply Valuation.inversion_estimate
        · have hxv : hvD.v.restrict x ≠ 0 := by
            intro hz
            rw [hz] at x_in₀
            exact (Units.ne_zero γ₀) (bot_unique x_in₀)
          exact (Valuation.ne_zero_iff _).mp hxv
        · refine lt_of_lt_of_le H₁ ?_
          grw [Units.min_val, mul_assoc, Units.val_mul, Units.val_mul, x_in₀] }

/-- The completed rational pseudodifferential division ring carries the unique continuous
extension of the order valuation. -/
noncomputable def completedPseudoDiffOpValuation :
    Valuation (CompletedPseudoDiffOp K) PseudoDiffOpValueGroup :=
  DivisionValuedCompletion.extensionValuation

/-- Valuation ring of the completed rational pseudodifferential division ring. -/
abbrev CompletedPseudoDiffOpInteger :=
  (completedPseudoDiffOpValuation (K := K)).integer

@[simp] theorem completedPseudoDiffOpValuation_apply_coe
    (x : WithVal (pseudoDiffOpValuation (K := K))) :
    completedPseudoDiffOpValuation (x : CompletedPseudoDiffOp K) =
      pseudoDiffOpValuation x.ofVal := by
  exact DivisionValuedCompletion.extensionValuation_apply_coe x

end DiffOp

end GaloisForLFunctions.HTGeometry
