import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.CrossingOrigin

/-! # Comparing crossings before and after an incoming circuit -/

open Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open PrescribedTimes
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- A positive crossing time attains the prescribed level or higher. -/
theorem crossing_attains_of_pos {n j : ℕ} {ρ : ℝ} {x : PrefixIndex n→ℝ}
    (hp : 0<crossingOrigin n j ρ x) :
    ρ≤pathGateDistance n j x (crossingOrigin n j ρ x) := by
  let E := {t : ℝ | 0≤t ∧ ρ≤pathGateDistance n j x t}
  change 0<sInf E at hp
  have hE : E.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h,Real.sInf_empty] at hp
    exact hp.false
  have hc : IsClosed E := isClosed_Ici.inter (isClosed_le continuous_const
    ((continuous_distance n j).comp (continuous_const.prodMk continuous_id)))
  exact (show sInf E∈E from hc.csInf_mem hE ⟨0,fun _ hx => hx.1⟩).2

/-- Adding the incoming circuit preserves an initial interval of low
distance. Subtracting it forces a crossing by the first distant increment.
The low interval is expressed using an arbitrary power threshold P. -/
theorem shifted_first_crossing {N s j i k : ℕ} (H : selfAdjoint (Reg N)) {v σ ρ : ℝ}
    (hv : HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val v))
    (hi : s+i≤j) (hk : s+j≤k) (hρ : ρ∈Icc (9/80:ℝ) (1/8))
    (hσ : 0≤σ) (hhigh : 1/4≤orbitCircuitDistance H k σ)
    (P : ℝ→Prop) (hstart : P 0) (hearly : ∀ t, 0≤t → P t →
      HasProjectiveCircuitApproximation N (1/160) i (unitaryEvolution H.val t)) :
    ∃ τ : ℝ, IsLeast {t : ℝ | 0≤t ∧ ρ≤orbitCircuitDistance H j (v+t)} τ ∧
      orbitCircuitDistance H j (v+τ)=ρ ∧ ¬P τ ∧ τ≤σ := by
  let f (t : ℝ) := orbitCircuitDistance H j (v+t)
  let E := {t : ℝ | 0≤t ∧ ρ≤f t}
  have small (t : ℝ) (ht : 0≤t) (hp : P t) : f t<ρ := by
    obtain ⟨z,hz,D,hD,hfit⟩ := affordable_add_time H hv (hearly t ht hp)
    have he : f t≤1/10+1/160 := (hasProjectiveCircuitApproximation_iff_infDist
      (unitaryEvolution H.val (v+t)) j _).mp ⟨z,hz,D,hD.trans hi,hfit⟩
    linarith only [he,hρ.1]
  have ends : σ∈E := by
    refine ⟨hσ,le_of_not_gt ?_⟩
    intro hbad
    have fit := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val (v+σ)) j ρ).mpr hbad.le
    obtain ⟨z,hz,D,hD,hfit⟩ := affordable_add_time H (hv.neg_time H) fit
    rw [show -v+(v+σ)=σ by ring] at hfit
    have he : orbitCircuitDistance H k σ≤1/10+ρ := (hasProjectiveCircuitApproximation_iff_infDist
      (unitaryEvolution H.val σ) k _).mp ⟨z,hz,D,hD.trans hk,hfit⟩
    linarith only [he,hhigh,hρ.2]
  have hb : BddBelow E := ⟨0,fun _ ht => ht.1⟩
  have hc : Continuous f := (orbitCircuitDistance_lipschitz H j).continuous.comp
    (continuous_const.add continuous_id)
  have closedE : IsClosed E := isClosed_Ici.inter (isClosed_le continuous_const hc)
  let τ := sInf E
  have hm : IsLeast E τ := ⟨closedE.csInf_mem ⟨σ,ends⟩ hb, fun _ ht => csInf_le hb ht⟩
  obtain ⟨r,hr,he⟩ := intermediate_value_Icc hm.1.1 hc.continuousOn
    (show ρ∈Icc (f 0) (f τ) from ⟨(small 0 le_rfl hstart).le,hm.1.2⟩)
  have hτ : r=τ := le_antisymm hr.2 (hm.2 ⟨hr.1,he.ge⟩)
  exact ⟨τ,hm,hτ ▸ he,fun h => (small τ hm.1.1 h).not_ge hm.1.2,hm.2 ends⟩

#print axioms shifted_first_crossing
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
