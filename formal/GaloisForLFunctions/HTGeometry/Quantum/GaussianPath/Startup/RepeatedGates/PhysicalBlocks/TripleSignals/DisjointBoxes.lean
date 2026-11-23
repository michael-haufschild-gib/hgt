import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.LocalReplacement
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Disorder.BoxFrequency
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliThresholdObstruction

/-! # Disjoint four-row boxes forcing nonmerging gates -/
open MeasureTheory Filter Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
open Temporal
noncomputable section
abbrev TripleBoxIndex := Fin 4 × PathPauliDirections
def blockCoordinate (p : ℕ × TripleBoxIndex) : ℕ × PathPauliDirections :=
  (4*p.1+p.2.1.val,p.2.2)
theorem blockCoordinate_injective : Function.Injective blockCoordinate := by
  rintro ⟨a,i,d⟩ ⟨b,j,e⟩ h
  obtain ⟨he,hd⟩ := Prod.mk.inj h
  change 4*a+i.val=4*b+j.val at he
  have h₁ := i.isLt
  have h₂ := j.isLt
  have hab : a=b := by omega
  have hij : i=j := Fin.ext (by omega : i.val=j.val)
  exact Prod.ext hab (Prod.ext hij hd)

private def leftDirection : TripleBoxIndex := (1,.inr (2,0))
private def rightDirection : TripleBoxIndex := (2,.inr (2,2))
def boxField (q : ℝ) (i : TripleBoxIndex) : ℝ := if i=leftDirection ∨ i=rightDirection then q else 0
def goodBox (q δ : ℝ) (ω : PathPauliDisorder) (k : ℕ) : Prop :=
  ∀ i, ω (blockCoordinate (k,i)) ∈ Set.Icc (boxField q i-δ) (boxField q i+δ)
open scoped Classical in
def goodBoxes (q δ : ℝ) (ω : PathPauliDisorder) (m : ℕ) :=
  (range m).filter (goodBox q δ ω)

/-- At least half the exact Gaussian probability appears as a block frequency. -/
theorem good_boxes_half_mass (q : ℝ) {δ : ℝ} (hδ : 0<δ) :
    let mass := gaussianBoxMass (fun i => boxField q i-δ) (fun i => boxField q i+δ)
    0<mass/2 ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ m : ℕ in atTop,
      mass/2*m ≤ ((goodBoxes q δ ω m).card:ℝ) := by
  classical
  let lo (i : TripleBoxIndex) := boxField q i-δ
  let hi (i : TripleBoxIndex) := boxField q i+δ
  have hbox (i : TripleBoxIndex) : lo i<hi i := by dsimp only [lo,hi]; linarith only [hδ]
  obtain ⟨hp,h⟩ := gaussian_disjoint_box_half_mass blockCoordinate blockCoordinate_injective lo hi hbox
  refine ⟨hp,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with m hm
  have he : goodBoxes q δ ω m = (range m).filter (fun k => ∀ j, ω (blockCoordinate (k,j)) ∈ Set.Icc (lo j) (hi j)) := by
    ext k
    simp only [goodBoxes,goodBox,mem_filter,lo,hi]
  rw [he]
  exact hm

/-- Every open coefficient neighborhood of the calibrated packet has
positive frequency in the same infinite Gaussian sample. -/
theorem good_boxes_density (q : ℝ) {δ : ℝ} (hδ : 0<δ) :
    ∃ p : ℝ, 0<p ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ m : ℕ in atTop,
      p*m ≤ ((goodBoxes q δ ω m).card:ℝ) :=
  ⟨_,good_boxes_half_mass q hδ⟩

private theorem source_inj {n : ℕ} : Function.Injective (@pathPauliSourceCoordinate n) := by
  rintro (⟨i,a⟩ | ⟨i,a⟩) (⟨j,b⟩ | ⟨j,b⟩) h <;>
    simp [pathPauliSourceCoordinate,Fin.ext_iff] at h ⊢ <;> exact h

private theorem source_row_bounds {n k : ℕ} {e f : Fin (n+1)}
    (he : e.val=4*k+1) (hf : f.val=4*k+2) {l : PathLabel n}
    (hl : l∈(tripleSites e f).biUnion pathIncidentLabels) :
    4*k ≤ (pathPauliSourceCoordinate l).1 ∧ (pathPauliSourceCoordinate l).1 < 4*k+4 := by
  classical
  obtain ⟨v,hv,h⟩ := mem_biUnion.mp hl
  have hi := (mem_filter.mp h).2
  have hv' : 4*k+1≤v.val ∧ v.val≤4*k+3 := by
    simp only [tripleSites,mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl|rfl <;> simp only [Fin.val_castSucc,Fin.val_succ] <;> omega
  rcases l with ⟨s,a⟩ | ⟨r,ab⟩
  · change s=v at hi
    change 4*k ≤ s.val ∧ s.val < 4*k+4
    rw [hi]
    omega
  · change r.castSucc=v ∨ r.succ=v at hi
    change 4*k≤r.val ∧ r.val<4*k+4
    rcases hi with rfl|rfl <;> simp only [Fin.val_castSucc,Fin.val_succ] at hv' <;> omega

private theorem box_controls {n k : ℕ} {e f : Fin (n+1)} (he : e.val=4*k+1) (hf : f.val=4*k+2)
    {q q' δ : ℝ} {ω : PathPauliDisorder} (hg : goodBox q' δ ω k) (hq : |q'-q|≤δ)
    (l : PathLabel n) (hl : l∈(tripleSites e f).biUnion pathIncidentLabels) :
    |pathPauliDisorderShell ω n l-tripleField e f q l| ≤ 2*δ := by
  let c := pathPauliSourceCoordinate l
  obtain ⟨h₁,h₂⟩ := source_row_bounds he hf hl
  let i : TripleBoxIndex := (⟨c.1-4*k,by dsimp [c]; omega⟩,c.2)
  have hi : blockCoordinate (k,i)=c := Prod.ext (by dsimp [blockCoordinate,i,c]; omega) rfl
  have hlc : blockCoordinate (k,leftDirection)=pathPauliSourceCoordinate (.inr (e,2,0)) :=
    Prod.ext he.symm rfl
  have hrc : blockCoordinate (k,rightDirection)=pathPauliSourceCoordinate (.inr (f,2,2)) :=
    Prod.ext hf.symm rfl
  have eqv (j : TripleBoxIndex) (u : PathLabel n) (hj : blockCoordinate (k,j)=pathPauliSourceCoordinate u) :
      i=j ↔ l=u := by
    constructor
    · intro h
      exact source_inj (hi.symm.trans ((congrArg (fun a => blockCoordinate (k,a)) h).trans hj))
    · intro h
      exact congrArg Prod.snd (blockCoordinate_injective (hi.trans ((congrArg pathPauliSourceCoordinate h).trans hj.symm)))
  have hs := hg i
  change ω (blockCoordinate (k,i)) ∈ Set.Icc _ _ at hs
  rw [hi] at hs
  have hc : |ω c-boxField q' i| ≤ δ := abs_le.mpr ⟨by linarith only [hs.1],by linarith only [hs.2]⟩
  rw [pathPauliDisorderShell_apply_source]
  apply (abs_sub_le (ω c) (boxField q' i) (tripleField e f q l)).trans
  apply (add_le_add hc _).trans_eq (show δ+δ=2*δ by ring)
  have hd : leftDirection≠rightDirection := by decide
  by_cases h : i=leftDirection
  · have h' : i≠rightDirection := fun hx => hd (h.symm.trans hx)
    rw [boxField,if_pos (Or.inl h),tripleField,if_pos ((eqv _ _ hlc).mp h),
      if_neg (mt (eqv _ _ hrc).mpr h'),add_zero]
    exact hq
  · by_cases h' : i=rightDirection
    · rw [boxField,if_pos (Or.inr h'),tripleField,if_neg (mt (eqv _ _ hlc).mpr h),if_pos ((eqv _ _ hrc).mp h'),zero_add]
      exact hq
    · rw [boxField,if_neg (not_or.mpr ⟨h,h'⟩),tripleField,if_neg (mt (eqv _ _ hlc).mpr h),
        if_neg (mt (eqv _ _ hrc).mpr h'),zero_add,sub_self,abs_zero]
      exact (abs_nonneg _).trans hq

/-- Each calibrated box contributes a different marked wire, including
when the circuit can use gates between arbitrarily distant sites. -/
theorem count_good_boxes {n : ℕ} {q q' δ t : ℝ} {ω : PathPauliDisorder}
    (hq : |q'-q|≤δ) (ht : (q*sqrt 2)*t=π/2) (hsmall : |t| * (63*(2*δ))≤1/8)
    (C : TwoQubitCircuit (n+2)) (z : ℂ) (hz : ‖z‖=1)
    (he : ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖ ≤ 1/4) :
    (goodBoxes q' δ ω ((n+1)/4)).card ≤ (marked (circuitWord C)).card := by
  classical
  let M := marked (circuitWord C)
  apply (card_le_card (t:=M.image (fun v => v.val/4)) _).trans card_image_le
  intro k hk
  obtain ⟨hk,hbox⟩ := mem_filter.mp hk
  have hh := mem_range.mp hk
  let e : Fin (n+1) := ⟨4*k+1,by omega⟩
  let f : Fin (n+1) := ⟨4*k+2,by omega⟩
  have hδ := (abs_nonneg _).trans hq
  have hs := triple_exchange_of_fit (e:=e) (f:=f) (Fin.ext (by rfl)) _ q (2*δ) t
    (by linarith only [hδ]) ht hsmall (box_controls (k:=k) rfl rfl hbox hq) C z hz he
  have hc : 2<(tripleSites e f).card := by
    have h₁ : e.castSucc≠e.succ := e.castSucc_lt_succ.ne
    have h₂ : e.castSucc≠f.succ := by intro h; have := congrArg Fin.val h; change 4*k+1=4*k+2+1 at this; omega
    have h₃ : e.succ≠f.succ := by intro h; have := congrArg Fin.val h; change 4*k+1+1=4*k+2+1 at this; omega
    simp [tripleSites,h₁,h₂,h₃]
  obtain ⟨v,hv,hm⟩ := exchanging_meets_marked (circuitWord C) _ hc (fun i hi j hj => hs j hj i hi)
  apply mem_image.mpr ⟨v,hm,?_⟩
  simp only [tripleSites,mem_insert,mem_singleton] at hv
  rcases hv with rfl|rfl|rfl <;> simp only [Fin.val_castSucc,Fin.val_succ,e,f] <;> omega

#print axioms count_good_boxes
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
