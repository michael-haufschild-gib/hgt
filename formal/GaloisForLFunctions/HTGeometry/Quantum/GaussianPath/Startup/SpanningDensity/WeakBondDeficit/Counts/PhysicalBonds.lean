import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.MovingBoxes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.BondSets

/-! # Weak and removable bond counts on the actual Hamiltonian prefix -/

open Finset MeasureTheory Filter
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open BlockDilations.AdaptiveCuts
noncomputable section

private theorem row_iff (ω : PathPauliDisorder) (n : ℕ) (e : Fin (n+1)) (h : ℝ) :
    e∈weakEdges (pathPauliDisorderShell ω n) h ↔ bondRow9 ω e.val∈weakBond h := by
  constructor
  · intro he k _
    exact abs_le.mp ((mem_filter.mp he).2 ((finProdFinEquiv (m:=3) (n:=3)).symm k))
  · intro he
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    intro ab
    change |ω (e.val,Sum.inr ab)|≤h
    have hh : |bondRow9 ω e.val (finProdFinEquiv ab)|≤h :=
      abs_le.mpr (he (finProdFinEquiv ab) (Set.mem_univ _))
    simpa only [bondRow9,Equiv.symm_apply_apply] using hh

private theorem physical_counts (ω : PathPauliDisorder) (n : ℕ) (h : ℝ) :
    let u := pathPauliDisorderShell ω n
    (weakEdges u h).card=boxCount ω 0 1 (n+1) h ∧
      (removable u h).card=boxCount ω 1 2 (n/2) h := by
  intro u
  rw [boxCount_as_filter,boxCount_as_filter]
  constructor
  · apply congrArg Finset.card
    ext e
    apply (row_iff ω n e h).trans
    simp only [mem_filter,mem_univ,true_and,zero_add,one_mul]
  · let f (j : Fin (n/2)) : Fin (n+1) := ⟨1+2*j.val,by have := j.isLt; omega⟩
    symm
    apply card_bij (fun j _ => f j)
    · intro j hj
      have hrow := (mem_filter.mp hj).2
      apply mem_filter.mpr
      exact ⟨(row_iff ω n _ h).mpr hrow,by dsimp only [f]; have := j.isLt; omega⟩
    · intro i _ j _ hij
      have he := congrArg Fin.val hij
      change 1+2*i.val=1+2*j.val at he
      exact Fin.ext (by omega)
    · intro e he
      obtain ⟨hw,hp,hn⟩ := mem_filter.mp he
      let j : Fin (n/2) := ⟨e.val/2,by omega⟩
      have hj : f j=e := Fin.ext (by change 1+2*(e.val/2)=e.val; omega)
      refine ⟨j,mem_filter.mpr ⟨mem_univ _,?_⟩,hj⟩
      change bondRow9 ω (f j).val∈weakBond h
      rw [hj]
      exact (row_iff ω n e h).mp hw

/-- All weak bonds give the upper count. A disjoint family of internal
odd bonds gives the lower count and can actually be omitted in a sweep. -/
theorem gaussian_weak_edge_counts :
    ∃ c>0, ∃ C>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let u := pathPauliDisorderShell ω n
      ∀ h : ℝ, 0<h → h≤1 → 4*2^20≤K*h^20 →
        c*K*h^9≤(removable u h).card ∧ ((weakEdges u h).card:ℝ)≤C*K*h^9 := by
  obtain ⟨c,hc,C,hC,hw⟩ := gaussian_moving_boxes
  refine ⟨c/4,by positivity,C,hC,?_⟩
  have hdiv : Tendsto (fun n : ℕ => n/2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro j
    filter_upwards [eventually_ge_atTop (2*j)] with n hn
    omega
  filter_upwards [hw] with ω hw
  filter_upwards [hdiv.eventually (hw 1 2 (by decide)),
    (tendsto_add_atTop_nat 1).eventually (hw 0 1 (by decide)),eventually_ge_atTop 6] with n hodd hall hn
  intro K u h hh h₁ hscale
  have hM : K≤4*((n/2:ℕ):ℝ) := by dsimp only [K]; exact_mod_cast (show n+2≤4*(n/2) by omega)
  have hMN : ((n/2:ℕ):ℝ)≤((n+1:ℕ):ℝ) := by exact_mod_cast (show n/2≤n+1 by omega)
  have hNK : ((n+1:ℕ):ℝ)≤K := by dsimp only [K]; exact_mod_cast (show n+1≤n+2 by omega)
  have hlow : 2^20≤((n/2:ℕ):ℝ)*h^20 := by
    linarith only [hscale,mul_le_mul_of_nonneg_right hM (pow_nonneg hh.le 20)]
  have hlo := (hodd h hh h₁ hlow).1
  have hhi := (hall h hh h₁ (hlow.trans (mul_le_mul_of_nonneg_right hMN (pow_nonneg hh.le 20)))).2
  obtain ⟨hcard,hr⟩ := physical_counts ω n h
  rw [hr,hcard]
  constructor
  · apply le_trans _ hlo
    nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hc.le) (pow_nonneg hh.le 9)]
  · exact hhi.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNK hC.le) (pow_nonneg hh.le 9))

#print axioms gaussian_weak_edge_counts
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
