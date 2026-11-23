import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.CrossedSignals
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.SelectedOverlap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.SeparatedCuts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.SeamDensity

/-! # The overlap cost of a circuit cut crossing many detectable bonds -/
open GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
open WeakBonds
noncomputable section

/-- The two endpoint layers contain at most twice their radius in bonds. -/
theorem boundary_count (n R : ℕ) :
    (Finset.univ.filter fun e : Fin (n+1) => e.val<R ∨ n<e.val+R).card ≤ 2*R := by
  let L := Finset.univ.filter fun e : Fin (n+1) => e.val<R
  let H := Finset.univ.filter fun e : Fin (n+1) => n<e.val+R
  have hl : L.card ≤ (Finset.range R).card :=
    Finset.card_le_card_of_injOn Fin.val (fun _ he => Finset.mem_range.mpr (Finset.mem_filter.mp he).2)
      Fin.val_injective.injOn
  have hh : H.card ≤ (Finset.range R).card := by
    apply Finset.card_le_card_of_injOn (fun e : Fin (n+1) => n-e.val)
    · intro e he
      have h := (Finset.mem_filter.mp he).2
      change n<e.val+R at h
      apply Finset.mem_range.mpr
      change n-e.val < R
      have := e.isLt
      omega
    · intro e _ f _ h
      change n-e.val=n-f.val at h
      exact Fin.ext (by have := e.isLt; have := f.isLt; omega)
  have hs : (Finset.univ.filter fun e : Fin (n+1) => e.val<R ∨ n<e.val+R) ⊆ L∪H := by
    intro e he
    rcases (Finset.mem_filter.mp he).2 with h|h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have h := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  rw [Finset.card_range] at hl hh
  omega

/-- After removing failed guard strips and the two edge regions, one
color and residue class supplies disjoint witnesses against the circuit. -/
theorem crowded_cut_overlap {n m : ℕ} (hm : 0 < m) (R : ℕ) (ω : PathPauliDisorder)
    (C : TwoQubitCircuit (n+2)) (c : Cut C) {t r γ δ : ℝ} (hr : δ<r) (hweak : 36*|t| *γ≤δ)
    (hcount : 2*(2*R+2)*m+(missedBonds n R γ ω).card+2*R ≤
      (detectable c (pathPauliDisorderShell ω n) t r).card) :
    (m:ℝ)*(r-δ)*‖inner ℂ (choiVector (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t))
      (choiVector C.eval.val)‖ ≤ 2*Real.sqrt m+m*δ := by
  classical
  let u := pathPauliDisorderShell ω n
  let D := detectable c u t r
  let A := missedBonds n R γ ω
  let B := Finset.univ.filter fun e : Fin (n+1) => e.val<R ∨ n<e.val+R
  let F := D \ (A∪B)
  have hcard : 2*(2*R+2)*m ≤ F.card := by
    have hsub : D ⊆ F∪(A∪B) := by
      intro e he
      by_cases h : e∈A∪B
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he,h⟩)
    have h₁ := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h₂ := Finset.card_union_le A B
    have h₃ : B.card≤2*R := boundary_count n R
    change 2*(2*R+2)*m+A.card+2*R≤D.card at hcount
    omega
  have hf (e) (he : e∈F) : e∈crossed c ∧ r < |bondSignal e u t| :=
    Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1
  obtain ⟨S,e,hi,hcut,he,hsep⟩ := oriented_subfamily (by omega : 0<2*R+2) c F (fun i h => (hf i h).1) hcard
  have hbr (i : Fin m) : ∃ a b : Fin (n+1), a<e i ∧ e i<b ∧ (e i).val≤a.val+R ∧
      b.val≤(e i).val+R ∧ ‖edgePart u a‖≤9*γ ∧ ‖edgePart u b‖≤9*γ := by
    have hn := (Finset.mem_sdiff.mp (he i).1).2
    have hA : e i∉A := fun h => hn (Finset.mem_union_left _ h)
    have hB : ¬((e i).val<R ∨ n<(e i).val+R) :=
      fun h => hn (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
    exact brackets_of_not_missed ω (e:=e i) (by omega) (by omega) hA
  choose a b hab hbe hleft hright ha hb using hbr
  have hd (i j) (hij : i≠j) : Disjoint (middleBlock (a i) (b i)) (middleBlock (a j) (b j)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have h₁ := Finset.mem_Ioc.mp hp
    have h₂ := Finset.mem_Ioc.mp hq
    have hne : (e i).val≠(e j).val := fun h => hij (hi (Fin.ext h))
    rcases lt_or_gt_of_ne hne with h|h
    · have hs := hsep i j h
      have hl := hleft j
      have hr := hright i
      simp only [Fin.lt_def,Fin.le_def,Fin.val_castSucc] at h₁ h₂
      omega
    · have hs := hsep j i h
      have hl := hleft i
      have hr := hright j
      simp only [Fin.lt_def,Fin.le_def,Fin.val_castSucc] at h₁ h₂
      omega
  apply selected_bond_overlap hm u t C S hcut e a b hi (fun i => (he i).2.1) (fun i => (he i).2.2)
    (fun i => ⟨hab i,hbe i⟩) hd hr (fun i => (hf _ (he i).1).2.le)
  intro i
  exact (mul_le_mul_of_nonneg_left (add_le_add (ha i) (hb i)) (mul_nonneg two_pos.le (abs_nonneg t))).trans
    ((show 2*|t| *(9*γ+9*γ)=36*|t| *γ by ring).le.trans hweak)

#print axioms crowded_cut_overlap

/-- A square number of packets gives a square-root fluctuation term.
The displayed inequalities suffice to exclude overlap κ. -/
theorem overlap_of_square_packets {r κ δ : ℝ} {k : ℕ} (hr : 0<r) (hκ : 0<κ)
    (h₁ : δ ≤ r/4) (h₂ : δ ≤ r*κ/8) (hk' : 8 < (k:ℝ)*(r*κ)) :
    ∀ v : ℝ, ((k*k:ℕ):ℝ)*(r-δ)*v ≤ 2*Real.sqrt (k*k:ℕ)+(k*k:ℕ)*δ → v<κ := by
  let m := k*k
  have hδr : δ < r := h₁.trans_lt (by linarith only [hr])
  have hkpos : 0 < (k:ℝ) := by
    by_contra! h
    linarith only [mul_nonpos_of_nonpos_of_nonneg h (mul_pos hr hκ).le,hk']
  intro v hov
  change (m:ℝ)*(r-δ)*v ≤ 2*Real.sqrt m+m*δ at hov
  by_contra! hfit
  have hab := (mul_le_mul_of_nonneg_left hfit (mul_nonneg (Nat.cast_nonneg m) (sub_pos.mpr hδr).le)).trans hov
  have hcoeff : r*κ/2 ≤ (r-δ)*κ-δ := by
    linarith only [mul_le_mul_of_nonneg_right h₁ hκ.le,
      h₂,mul_pos hr hκ]
  simp only [m,Nat.cast_mul,Real.sqrt_mul_self (Nat.cast_nonneg k)] at hab
  nlinarith only [hab,mul_le_mul_of_nonneg_left hcoeff (mul_self_nonneg (k:ℝ)),
    mul_lt_mul_of_pos_left hk' hkpos,hkpos]

/-- At a fixed detection threshold, finitely many separated packets
exclude any prescribed positive overlap, with a positive error margin. -/
theorem overlap_parameters {r κ : ℝ} (hr : 0<r) (hκ : 0<κ) :
    ∃ δ>0, δ<r ∧ ∃ m : ℕ, 0 < m ∧ ∀ v : ℝ,
      (m:ℝ)*(r-δ)*v ≤ 2*Real.sqrt m+m*δ → v<κ := by
  let δ := min (r/4) (r*κ/8)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  have hδr : δ<r := (min_le_left ..).trans_lt (by linarith only [hr])
  obtain ⟨k,hk⟩ := exists_nat_gt (8/(r*κ))
  have hkpos := (div_pos (by norm_num : (0:ℝ)<8) (mul_pos hr hκ)).trans hk
  have hk' := (div_lt_iff₀ (mul_pos hr hκ)).mp hk
  let m := k*k
  refine ⟨δ,hδ,hδr,m,Nat.mul_pos (Nat.cast_pos.mp hkpos) (Nat.cast_pos.mp hkpos),?_⟩
  exact overlap_of_square_packets hr hκ (min_le_left ..) (min_le_right ..) hk'

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
