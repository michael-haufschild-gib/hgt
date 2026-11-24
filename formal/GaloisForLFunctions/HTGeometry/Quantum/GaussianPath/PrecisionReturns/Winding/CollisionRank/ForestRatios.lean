import GaloisForLFunctions.HTGeometry.SortedGapRatioGlobalExtremality

/-! # Extremality of ratios of spectral gaps with several distinct anchors -/

open Set MeasureTheory
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
noncomputable section

/-- Ratios of differences between each leaf and its class representative.
The first edge supplies the denominator. -/
def forestRatio {I : Type*} {n : ℕ} (leaf root : Fin (n+1) → I) (E : I → ℝ) (j : Fin n) :=
  (E (leaf j.succ)-E (root j.succ))/(E (leaf 0)-E (root 0))

private def charge {D n : ℕ} (leaf root : Fin n → Fin D) (c : Fin n → ℝ) (j : Fin D) :=
  anchoredWeight leaf c j-anchoredWeight root c j

private theorem balanced {D n : ℕ} (leaf root : Fin n → Fin D) (c : Fin n → ℝ) :
    ∑ j, charge leaf root c j=0 := by
  simp only [charge,Finset.sum_sub_distrib,sum_anchoredWeight,sub_self]

private theorem pairing {D n : ℕ} (leaf root : Fin n → Fin D) (c : Fin n → ℝ) (E : Fin D → ℝ) :
    ∑ j, charge leaf root c j*E j=∑ i, c i*(E (leaf i)-E (root i)) := by
  simp only [charge,sub_mul,Finset.sum_sub_distrib,sum_anchoredWeight_mul,mul_sub]

private theorem leaf_charge {D n : ℕ} {leaf root : Fin n → Fin D} (hinj : Function.Injective leaf)
    (hdis : ∀ i j, root i ≠ leaf j) (c : Fin n → ℝ) (j : Fin n) :
    charge leaf root c (leaf j)=c j := by
  rw [charge,anchoredWeight_apply hinj]
  simp [anchoredWeight,hdis]

/-- On every connected simple chart of the ensemble, ratios of independent
star-forest gap differences are extremal. Representatives may repeat. -/
theorem forest_chart {n L D : ℕ} [NeZero L] (hn : 0<n) {P : Fin L → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (hS : SpectrumEscapesRealRelations (range (spectralEnsembleMatrix P)))
    {leaf root : Fin (n+1) → Fin D} (hinj : Function.Injective leaf) (hdis : ∀ i j, root i ≠ leaf j)
    {U : Set (Fin L → ℝ)} (hU : IsOpen U) (hc : IsPreconnected U) (hne : U.Nonempty)
    (hs : U ⊆ simpleEnsembleLocus hP) :
    volume {x ∈ U | KleinbockMargulis.VWA (forestRatio leaf root (sortedEnsembleSpectrum hP x))} = 0 := by
  let E := sortedEnsembleSpectrum hP
  let g := fun x (i : Fin (n+1)) => E x (leaf i)-E x (root i)
  have hden (x) (hx : x∈U) : g x 0 ≠ 0 := fun he =>
    (hdis 0 0) ((injective_sortedEnsembleSpectrum hP (hs hx)) (sub_eq_zero.mp he)).symm
  apply KleinbockMargulis.theoremA_analytic hn hU hc
  · intro x hx
    apply analyticAt_pi_iff.mpr
    intro j
    have hg (i : Fin (n+1)) : AnalyticAt ℝ (fun y => g y i) x :=
      (analyticAt_sortedEnsembleSpectrum hP (hs hx) (leaf i)).sub
        (analyticAt_sortedEnsembleSpectrum hP (hs hx) (root i))
    exact (hg j.succ).div (hg 0) (hden x hx)
  · intro w heq
    obtain ⟨x₀,hx₀⟩ := hne
    let κ := ∑ i, w i*forestRatio leaf root (E x₀) i
    let c : Fin (n+1) → ℝ := Fin.cons (α:=fun _ => ℝ) (-κ) w
    by_contra! hw
    have hnon : charge leaf root c ≠ 0 := by
      intro hzero
      apply hw
      funext i
      have hh := congrFun hzero (leaf i.succ)
      rw [leaf_charge hinj hdis] at hh
      exact hh
    have hfamily : realAffineMatrix 0 P = spectralEnsembleMatrix P :=
      funext fun x => realAffineMatrix_zero_eq_spectralEnsembleMatrix P x
    apply not_relation_on_open_of_spectrumEscapes 0 P (by rw [hfamily]; exact hS)
      (balanced leaf root c) hnon hU ⟨x₀,hx₀⟩ E (fun x hx => injective_sortedEnsembleSpectrum hP (hs hx))
      (fun x _ i => by rw [hfamily]; exact matrixCharpolyRelation_sortedEnsembleSpectrum hP x i)
    intro x hx
    rw [pairing,Fin.sum_univ_succ]
    change -κ*g x 0+(∑ i, w i*g x i.succ)=0
    have hm := congrArg (fun y : ℝ => y*g x 0) (heq x hx x₀ hx₀)
    change (∑ i, w i*(g x i.succ/g x 0))*g x 0=κ*g x 0 at hm
    rw [Finset.sum_mul] at hm
    have he (i : Fin n) : w i*(g x i.succ/g x 0)*g x 0=w i*g x i.succ := by field_simp [hden x hx]
    simp only [he] at hm
    linarith only [hm]

#print axioms forest_chart
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
