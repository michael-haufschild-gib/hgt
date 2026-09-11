import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencySynthesis
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.NormedSpace
open Complex Set Function
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section GenericInvariantClassification
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
local instance frequencyInvariantGenericEndRing : NormedRing (E →L[ℂ] E) :=
  ContinuousLinearMap.toNormedRing

private def closedGen (v : I → E) (A : Set I) : Submodule ℂ E :=
  (Submodule.span ℂ (Set.range (fun i : A => v i.val))).topologicalClosure

private theorem closedGen_closed (v : I → E) (A : Set I) :
    IsClosed (closedGen v A : Set E) :=
  (Submodule.span ℂ (Set.range (fun i : A => v i.val))).isClosed_topologicalClosure

private theorem closedGen_mem (v : I → E) (A : Set I) (i : I) (hi : i ∈ A) :
    v i ∈ closedGen v A :=
  (Submodule.span ℂ (Set.range (fun j : A => v j.val))).le_topologicalClosure
    (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)

private theorem closedGen_le (v : I → E) (A : Set I) (W : Submodule ℂ E)
    (hW : IsClosed (W : Set E)) (hv : ∀ i ∈ A, v i ∈ W) : closedGen v A ≤ W := by
  apply hW.closure_subset_iff.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hv i.val i.property

private theorem closedGen_mono (v : I → E) {A B : Set I} (hAB : A ⊆ B) :
    closedGen v A ≤ closedGen v B :=
  closedGen_le v A (closedGen v B) (closedGen_closed v B)
    (fun i hi => closedGen_mem v B i (hAB hi))

private theorem closedGen_mode_iff [DecidableEq I] (D : Submodule ℂ E) (v : I → D)
    (a : I → D →L[ℂ] ℂ) (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (A : Set I) (i : I) :
    (v i).val ∈ closedGen (fun j => (v j).val) A ↔ i ∈ A := by
  classical
  constructor
  · intro hi
    by_contra hia
    obtain ⟨g, hg, hgn⟩ := exists_extension_norm_eq D (a i)
    have hle : closedGen (fun j => (v j).val) A ≤ g.ker := by
      apply closedGen_le _ A g.ker g.isClosed_ker
      intro j hj
      change g (v j).val = 0
      rw [hg (v j), hd]
      apply if_neg
      intro hij
      exact hia (hij.symm ▸ hj)
    have hz : g (v i).val = 0 := hle hi
    have ho : a i (v i) = 1 := by simpa only [if_pos rfl, ite_true] using hd i i
    exact one_ne_zero (ho.symm.trans ((hg (v i)).symm.trans hz))
  · exact closedGen_mem (fun j => (v j).val) A i

private theorem closedGen_injective (v : I → E)
    (hm : ∀ A i, v i ∈ closedGen v A ↔ i ∈ A) : Function.Injective (closedGen v) := by
  intro A B hAB
  ext i
  calc
    i ∈ A ↔ v i ∈ closedGen v A := (hm A i).symm
    _ ↔ v i ∈ closedGen v B := by rw [hAB]
    _ ↔ i ∈ B := hm B i

private theorem closedGen_invariant (T : E →L[ℂ] E) (v : I → E) (z : I → ℂ)
    (he : ∀ i, T (v i) = z i • v i) (A : Set I) :
    ∀ w ∈ closedGen v A, T w ∈ closedGen v A := by
  have hclosed : IsClosed {w : E | T w ∈ closedGen v A} :=
    (closedGen_closed v A).preimage T.continuous
  apply hclosed.closure_subset_iff.mpr
  intro w hw
  change T w ∈ closedGen v A
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    change T (v i.val) ∈ closedGen v A
    rw [he]
    exact (closedGen v A).smul_mem _ (closedGen_mem v A i.val i.property)
  | zero => rw [map_zero]; exact (closedGen v A).zero_mem
  | add u w hu hw ihu ihw => rw [map_add]; exact (closedGen v A).add_mem ihu ihw
  | smul c u hu ih => rw [map_smul]; exact (closedGen v A).smul_mem c ih

private theorem invariant_power (T : E →L[ℂ] E) (W : Submodule ℂ E)
    (hi : ∀ w ∈ W, T w ∈ W) (n : ℕ) : ∀ w ∈ W, (T ^ n) w ∈ W := by
  induction n with
  | zero => intro w hw; change w ∈ W; exact hw
  | succ n ih =>
    intro w hw
    rw [pow_succ, mul_apply_eq_comp]
    exact ih (T w) (hi w hw)

private theorem cyclic_le (T : E →L[ℂ] E) (W : Submodule ℂ E)
    (hW : IsClosed (W : Set E)) (hi : ∀ w ∈ W, T w ∈ W) (u : E) (hu : u ∈ W) :
    (Submodule.span ℂ (Set.range (fun n : ℕ => (T ^ n) u))).topologicalClosure ≤ W := by
  apply hW.closure_subset_iff.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact invariant_power T W hi n u hu

private theorem closed_invariant_classification [DecidableEq I]
    (D : Submodule ℂ E) (hD : IsClosed (D : Set E)) (v : I → D)
    (a : I → D →L[ℂ] ℂ) (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (T : E →L[ℂ] E) (z : I → ℂ) (he : ∀ i, T (v i).val = z i • (v i).val)
    (hs : ∀ u : D, u.val ∈ closedGen (fun i => (v i).val) (Function.support (fun i => a i u)))
    (hc : ∀ u : D,
      (Submodule.span ℂ (Set.range (fun n : ℕ => (T ^ n) u.val))).topologicalClosure =
        closedGen (fun i => (v i).val) (Function.support (fun i => a i u)))
    (W : Submodule ℂ E) :
    (∃! A : Set I, closedGen (fun i => (v i).val) A = W) ↔
      IsClosed (W : Set E) ∧ W ≤ D ∧ ∀ w ∈ W, T w ∈ W := by
  classical
  let f := fun i => (v i).val
  have hinj : Function.Injective (closedGen f) :=
    closedGen_injective f (closedGen_mode_iff D v a hd)
  constructor
  · rintro ⟨A, rfl, huniq⟩
    exact ⟨closedGen_closed f A,
      closedGen_le f A D hD (fun i hi => (v i).property),
      closedGen_invariant T f z he A⟩
  · rintro ⟨hW, hWD, hTW⟩
    let A : Set I := {i | f i ∈ W}
    have hAW : closedGen f A ≤ W := closedGen_le f A W hW (fun i hi => hi)
    have hWA : W ≤ closedGen f A := by
      intro w hw
      let u : D := ⟨w, hWD hw⟩
      have hcyc := cyclic_le T W hW hTW u.val hw
      have hactive : closedGen f (Function.support (fun i => a i u)) ≤ W :=
        hc u ▸ hcyc
      have hsub : Function.support (fun i => a i u) ⊆ A := by
        intro i hi
        exact hactive (closedGen_mem f _ i hi)
      exact closedGen_mono f hsub (hs u)
    have hEq : closedGen f A = W := le_antisymm hAW hWA
    refine ⟨A, hEq, ?_⟩
    intro B hB
    exact hinj (hB.trans hEq.symm)
end GenericInvariantClassification
local instance frequencyInvariantActualEndRing : NormedRing
    (causalBoundedChain →L[ℂ] causalBoundedChain) := ContinuousLinearMap.toNormedRing

/-- Closing a selected frequency span introduces no additional actual modes:
a genuine unit chain belongs precisely when its frequency was selected. -/
theorem causalFrequencySynthesisSpace_mode_mem_iff (b : ℝ) (A : Set ℝ) (ω : ℝ) :
    causalBoundedUnitEigenchain b ω ∈ causalFrequencySynthesisSpace b A ↔ ω ∈ A :=
  closedGen_mode_iff (causalFrequencySpace b) (causalFrequencyMode b)
    (causalFrequencyCoefficient b) (causalFrequencyCoefficient_mode b) A ω

/-- The actual closed subspaces contained in the completed frequency space and
preserved by the forward shift are exactly the closed spans of unique frequency
sets. The conditions are classified, not assumed as premises. -/
theorem causalFrequencyInvariantSubspace_iff (b : ℝ)
    (W : Submodule ℂ causalBoundedChain) :
    (∃! A : Set ℝ, causalFrequencySynthesisSpace b A = W) ↔
      IsClosed (W : Set causalBoundedChain) ∧ W ≤ causalFrequencySpace b ∧
        ∀ w ∈ W, causalBoundedChainShift w ∈ W :=
  closed_invariant_classification (causalFrequencySpace b)
    (causalFrequencyCore b).isClosed_topologicalClosure (causalFrequencyMode b)
    (causalFrequencyCoefficient b) (causalFrequencyCoefficient_mode b)
    causalBoundedChainShift (fun ω => (causalUnitBoundaryRate b ω).val)
    (causalBoundedChainShift_unitEigenchain b)
    (causalFrequencySpace_mem_closed_span_support b) (causalFrequencyCyclicSpace_eq_support b) W

end RHTower.FokasLenells
