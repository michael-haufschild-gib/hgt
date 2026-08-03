import GaloisForLFunctions.HTGeometry.BarnesLadderStepDA
import GaloisForLFunctions.HTGeometry.BarnesFrameReindex

/-!
# The ladder step between subframes

The ladder step deletes one direction from an index type.  Iterating it produces nested subtypes, so
it is restated here between the subframes carried by a finite set of directions and by that set with
one element erased.  Reindexing invariance of the source identifies the nested subtype with the
single-level one, so the step reads

```text
σ_{ω_k} Ψ_S - Ψ_S + Ψ_{S.erase k}   is DA over ℂ(z),
```

for every direction `k` of a set `S` with at least two directions.  This is the form an induction on
the number of directions consumes.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The frame carried by a finite set of directions. -/
def subframe (ω : ι → ℂ) (S : Finset ι) : {i : ι // i ∈ S} → ℂ := fun i => ω i.1

omit [Fintype ι] [DecidableEq ι] in
theorem subframe_im_pos {ω : ι → ℂ} (hω : ∀ i, 0 < (ω i).im) (S : Finset ι) :
    ∀ i, 0 < (subframe ω S i).im := fun i => hω i.1

/-- Erasing a direction from a set matches deleting it from the subtype. -/
def eraseSubtypeEquiv (S : Finset ι) (k : ι) (hk : k ∈ S) :
    {i' : {i : ι // i ∈ S} // i' ≠ ⟨k, hk⟩} ≃ {i : ι // i ∈ S.erase k} where
  toFun i' := ⟨i'.1.1, Finset.mem_erase.mpr ⟨fun hc => i'.2 (Subtype.ext hc), i'.1.2⟩⟩
  invFun i := ⟨⟨i.1, Finset.mem_of_mem_erase i.2⟩,
    fun hc => (Finset.mem_erase.mp i.2).1 (congrArg Subtype.val hc)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

omit [Fintype ι] in
theorem deletedFrame_subframe (ω : ι → ℂ) (S : Finset ι) (k : ι) (hk : k ∈ S) :
    deletedFrame (subframe ω S) ⟨k, hk⟩
      = subframe ω (S.erase k) ∘ eraseSubtypeEquiv S k hk := by
  funext i'
  rfl

omit [Fintype ι] in
/-- **The ladder step between subframes.** -/
theorem differentialAlgebraicOver_subframe_ladder_step (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (S : Finset ι) (k : ι) (hk : k ∈ S) (h2 : 2 ≤ S.card)
    [Nonempty {i : ι // i ∈ S}] [Nonempty {i : ι // i ∈ S.erase k}] :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (addTranslationMeroEquiv (ω k)
            (barnesSourceLogDerivMero (subframe ω S) (subframe_im_pos hω S))
          - barnesSourceLogDerivMero (subframe ω S) (subframe_im_pos hω S)
        + barnesSourceLogDerivMero (subframe ω (S.erase k))
            (subframe_im_pos hω (S.erase k))) := by
  classical
  haveI hne : Nonempty {i' : {i : ι // i ∈ S} // i' ≠ ⟨k, hk⟩} := by
    have hcard : 1 < Fintype.card {i : ι // i ∈ S} := by
      rw [Fintype.card_coe]
      omega
    obtain ⟨i', hi'⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨k, hk⟩
    exact ⟨⟨i', hi'⟩⟩
  have hstep := differentialAlgebraicOver_barnesSource_ladder_step (subframe ω S)
    (subframe_im_pos hω S) ⟨k, hk⟩
  have hlower : barnesSourceLogDerivMero (deletedFrame (subframe ω S) ⟨k, hk⟩)
        (deletedFrame_im_pos (subframe_im_pos hω S) ⟨k, hk⟩)
      = barnesSourceLogDerivMero (subframe ω (S.erase k)) (subframe_im_pos hω (S.erase k)) := by
    have hframe := deletedFrame_subframe ω S k hk
    have := barnesSourceLogDerivMero_comp_equiv (eraseSubtypeEquiv S k hk)
      (subframe ω (S.erase k)) (subframe_im_pos hω (S.erase k))
      (fun i' => subframe_im_pos hω (S.erase k) _)
    rw [← this]
    exact barnesSourceLogDerivMero_congr hframe _ _
  rw [hlower] at hstep
  have hω' : subframe ω S ⟨k, hk⟩ = ω k := rfl
  rw [hω'] at hstep
  exact hstep

end

end GaloisForLFunctions.HTGeometry
