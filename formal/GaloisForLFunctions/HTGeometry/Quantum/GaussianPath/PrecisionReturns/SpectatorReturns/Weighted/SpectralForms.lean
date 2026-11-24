import GaloisForLFunctions.HTGeometry.SortedGapRatioGlobalStrongExtremality

/-! # Strong extremality of ratios of independent balanced spectral forms -/

open Set MeasureTheory Finset
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
noncomputable section

/-- Integer spectral characters, considered as a family of real linear forms. -/
def IndependentRows {I : Type*} {m : ℕ} (A : Fin m→I→ℤ) : Prop :=
  ∀ c : Fin m→ℝ, (∀ j, ∑ i, c i*(A i j:ℝ)=0) → c=0

def action {I : Type*} [Fintype I] (a : I→ℤ) (E : I→ℝ) := ∑ j, (a j:ℝ)*E j

/-- Energy actions divided by the action of the first row. -/
def ratios {I : Type*} [Fintype I] {n : ℕ} (A : Fin (n+1)→I→ℤ) (E : I→ℝ) :=
  fun i : Fin n => action (A i.succ) E/action (A 0) E

private theorem combine {I : Type*} [Fintype I] {m : ℕ} (A : Fin m→I→ℤ) (c : Fin m→ℝ) (E : I→ℝ) :
    (∑ j, (∑ i, c i*(A i j:ℝ))*E j)=∑ i, c i*action (A i) E := by
  simp only [action,sum_mul,mul_sum,mul_assoc]
  exact sum_comm

/-- On every simple spectral chart avoiding zero denominator, an affine
relation on the ratios would give a nonzero balanced relation on the spectrum. -/
theorem spectral_form_chart {n L D : ℕ} [NeZero L] {P : Fin L→Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ i, (P i).IsHermitian) (hS : SpectrumEscapesRealRelations (range (spectralEnsembleMatrix P)))
    (A : Fin (n+1)→Fin D→ℤ) (hb : ∀ i, SpectralCharacterBalanced (A i)) (hi : IndependentRows A)
    {U : Set (Fin L→ℝ)} (ho : IsOpen U) (hc : IsPreconnected U) (hne : U.Nonempty)
    (hs : U⊆simpleEnsembleLocus hP) (hd : ∀ x∈U, action (A 0) (sortedEnsembleSpectrum hP x)≠0) :
    volume {x∈U | KleinbockMargulis.VWMA (ratios A (sortedEnsembleSpectrum hP x))}=0 := by
  let E := sortedEnsembleSpectrum hP
  let g := fun x i => action (A i) (E x)
  apply KleinbockMargulis.theoremA_analytic_multiplicative ho hc
  · intro x hx
    apply analyticAt_pi_iff.mpr
    intro i
    have hg (j : Fin (n+1)) : AnalyticAt ℝ (fun y => g y j) x :=
      analyticAt_sortedSpectralAction hP (fun k => (A j k:ℝ)) (hs hx)
    exact (hg i.succ).div (hg 0) (hd x hx)
  intro w hw
  obtain ⟨x₀,hx₀⟩ := hne
  let κ := ∑ i, w i*ratios A (E x₀) i
  let c := Fin.cons (α:=fun _ => ℝ) (-κ) w
  let v := fun j => ∑ i, c i*(A i j:ℝ)
  have hbal : ∑ j, v j=0 := by
    have hb' (i : Fin (n+1)) : ∑ j, (A i j:ℝ)=0 := by exact_mod_cast hb i
    change (∑ j, ∑ i, c i*(A i j:ℝ))=0
    rw [sum_comm]; simp only [←mul_sum,hb',mul_zero,sum_const_zero]
  by_contra! hnon
  have hv : v≠0 := by
    intro hz
    have he := hi c (fun j => congrFun hz j)
    apply hnon
    exact funext fun i => congrFun he i.succ
  have hf : realAffineMatrix 0 P=spectralEnsembleMatrix P :=
    funext fun x => realAffineMatrix_zero_eq_spectralEnsembleMatrix P x
  apply not_relation_on_open_of_spectrumEscapes 0 P (by rw [hf]; exact hS) hbal hv ho ⟨x₀,hx₀⟩ E
    (fun x hx => injective_sortedEnsembleSpectrum hP (hs hx))
    (fun x _ j => by rw [hf]; exact matrixCharpolyRelation_sortedEnsembleSpectrum hP x j)
  intro x hx
  change (∑ j, (∑ i, c i*(A i j:ℝ))*E x j)=0
  rw [combine,Fin.sum_univ_succ]
  have he := congrArg (fun z : ℝ => z*g x 0) (hw x hx x₀ hx₀)
  change (∑ i, w i*(g x i.succ/g x 0))*g x 0=κ*g x 0 at he
  have hh (i : Fin n) : w i*(g x i.succ/g x 0)*g x 0=w i*g x i.succ := by field_simp [show g x 0≠0 from hd x hx]
  simp only [sum_mul,hh] at he
  change -κ*g x 0+(∑ i, w i*g x i.succ)=0
  linarith only [he]

/-- A countable ball cover removes the chart choice. Denominator zeros
are excluded explicitly, allowing characters with more than two levels. -/
theorem spectral_form_null {n L D : ℕ} [NeZero L] {P : Fin L→Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ i, (P i).IsHermitian) (hS : SpectrumEscapesRealRelations (range (spectralEnsembleMatrix P)))
    (A : Fin (n+1)→Fin D→ℤ) (hb : ∀ i, SpectralCharacterBalanced (A i)) (hi : IndependentRows A) :
    volume {x | x∈simpleEnsembleLocus hP ∧ action (A 0) (sortedEnsembleSpectrum hP x)≠0 ∧
      KleinbockMargulis.VWMA (ratios A (sortedEnsembleSpectrum hP x))}=0 := by
  let U := simpleEnsembleLocus hP ∩ {x | action (A 0) (sortedEnsembleSpectrum hP x)≠0}
  let bad := {x | KleinbockMargulis.VWMA (ratios A (sortedEnsembleSpectrum hP x))}
  have ho : IsOpen U := (isOpen_simpleEnsembleLocus hP).inter
    (isOpen_ne_fun (continuous_sortedSpectralAction hP (fun j => (A 0 j:ℝ))) continuous_const)
  let B (p : {p : (Fin L→ℝ)×ℝ // 0<p.2 ∧ Metric.ball p.1 p.2⊆U}) := Metric.ball p.val.1 p.val.2
  obtain ⟨T,hT,he⟩ := TopologicalSpace.isOpen_iUnion_countable B (fun _ => Metric.isOpen_ball)
  refine measure_mono_null (t:=⋃ p∈T, B p ∩ bad) ?_ ?_
  · rintro x ⟨hs,hd,hv⟩
    obtain ⟨r,hr,hh⟩ := Metric.isOpen_iff.mp ho x ⟨hs,hd⟩
    have hm : x∈⋃ p∈T, B p := by
      rw [he]; exact mem_iUnion.mpr ⟨⟨(x,r),hr,hh⟩,Metric.mem_ball_self hr⟩
    obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp hm
    exact mem_iUnion₂.mpr ⟨p,hp,hx,hv⟩
  rw [measure_biUnion_null_iff hT]
  intro p _
  exact spectral_form_chart hP hS A hb hi Metric.isOpen_ball Metric.isPreconnected_ball
    ⟨p.val.1,Metric.mem_ball_self p.property.1⟩ (fun _ hx => (p.property.2 hx).1)
    (fun _ hx => (p.property.2 hx).2)

#print axioms spectral_form_null
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
