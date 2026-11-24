import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PairedOccupation.ArcOverlap
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.ArcPowers
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.TranslatedArcs

/-! # Two-date Haar occupation from one overlap factor per eigenphase -/

open Set MeasureTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.PairedOccupation
noncomputable section
variable {I : Type*} [Fintype I] [Nonempty I]

/-- Initial packets for which both the starting and lagged phases fit
some arc of width r. Each endpoint can choose its own center. -/
def pairedArcs (r : ℝ) (u : I → UnitAddCircle) : Set (I → UnitAddCircle) :=
  enclosingUnitArc r ∩ (fun θ => θ+u) ⁻¹' enclosingUnitArc r

private def box (r : ℝ) (u : I → UnitAddCircle) (a b : UnitAddCircle) :=
  univ.pi fun i => (fun z : UnitAddCircle => z-a) ⁻¹' commonForwardUnitArc r (b-a-u i)

private theorem box_iff {r : ℝ} {u θ : I → UnitAddCircle} {a b : UnitAddCircle} :
    θ∈box r u a b ↔ ∀ i, θ i-a∈forwardUnitArc r ∧ θ i+u i-b∈forwardUnitArc r := by
  simp only [box,mem_univ_pi,mem_preimage,commonForwardUnitArc,mem_inter_iff]
  exact forall_congr' fun i => by rw [show θ i-a-(b-a-u i)=θ i+u i-b by abel]

private theorem contained {r : ℝ} (θ : I → UnitAddCircle) (a : UnitAddCircle)
    (h : ∀ i, θ i-a∈forwardUnitArc r) : θ∈enclosingUnitArc r := by
  classical
  choose y hy he using h
  obtain ⟨b,_,hb⟩ := Finset.exists_min_image Finset.univ y Finset.univ_nonempty
  refine mem_iUnion.mpr ⟨b,fun i _ => ⟨y i-y b,⟨sub_nonneg.mpr (hb i (Finset.mem_univ _)),?_⟩,?_⟩⟩
  · linarith only [(hy i).2,(hy b).1]
  · rw [AddCircle.coe_sub,he,he]; abel

private theorem box_volume (r : ℝ) (u : I → UnitAddCircle) (a b : UnitAddCircle) :
    volume (box r u a b)=∏ i, volume (commonForwardUnitArc r (b-a-u i)) := by
  rw [box,volume_pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  simp only [sub_eq_add_neg,measure_preimage_add_right]

/-- Fixing the two origins of the covering arcs gives an exact product
lower bound. The common phase difference c can be chosen after the lag. -/
theorem product_lower (r : ℝ) (u : I → UnitAddCircle) (c : UnitAddCircle) :
    (∏ i, volume (commonForwardUnitArc r (c-u i))) ≤ volume (pairedArcs r u) := by
  have hb : box r u 0 c ⊆ pairedArcs r u := by
    intro θ ht
    have h := box_iff.mp ht
    exact ⟨contained θ 0 (fun i => (h i).1),contained (θ+u) c (fun i => (h i).2)⟩
  simpa only [box_volume,sub_zero] using measure_mono hb

private theorem rounded {r δ : ℝ} (hr : 0≤r) {Q : ℕ} (g : Fin Q → UnitAddCircle)
    (hg : ∀ z : UnitAddCircle, ∃ j, z-g j∈forwardUnitArc δ)
    (θ : I → UnitAddCircle) (ht : θ∈enclosingUnitArc r) :
    ∃ j, ∀ i, θ i-g j∈forwardUnitArc (r+δ) := by
  obtain ⟨b,hb⟩ := HarmonicRuns.exists_anchor_lifts hr ht
  obtain ⟨j,v,hv,he⟩ := hg (θ b)
  refine ⟨j,fun i => ?_⟩
  obtain ⟨y,hy,hey⟩ := hb i
  exact ⟨y+v,⟨add_nonneg hy.1 hv.1,add_le_add hy.2 hv.2⟩,
    by rw [AddCircle.coe_add,hey,he]; abel⟩

/-- One finite grid of arc origins bounds the joint Haar occupation at
all dimensions and lags. Only the width is enlarged by δ. -/
theorem product_grid_upper {δ : ℝ} (hδ : 0<δ) :
    ∃ Q : ℕ, ∃ g : Fin Q → UnitAddCircle, ∀ (I : Type) [Fintype I] [Nonempty I],
      ∀ r : ℝ, 0≤r → ∀ u : I → UnitAddCircle,
      volume (pairedArcs r u) ≤ ∑ j : Fin Q × Fin Q,
        ∏ i, volume (commonForwardUnitArc (r+δ) (g j.2-g j.1-u i)) := by
  obtain ⟨Q,g,hg⟩ := HarmonicRuns.finite_forward_grid hδ
  refine ⟨Q,g,?_⟩
  intro I _ _ r hr u
  let B (j : Fin Q × Fin Q) := box (r+δ) u (g j.1) (g j.2)
  have hsub : pairedArcs r u ⊆ ⋃ j, B j := by
    rintro θ ⟨h₁,h₂⟩
    obtain ⟨a,ha⟩ := rounded hr g hg θ h₁
    obtain ⟨b,hb⟩ := rounded hr g hg (θ+u) h₂
    exact mem_iUnion.mpr ⟨(a,b),box_iff.mpr fun i => ⟨ha i,hb i⟩⟩
  exact (measure_mono hsub).trans ((measure_iUnion_le B).trans_eq (by simp only [tsum_fintype,B,box_volume]))

#print axioms product_lower
#print axioms product_grid_upper
end
end GaloisForLFunctions.HTGeometry.PairedOccupation
