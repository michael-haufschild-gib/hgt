import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.CutMass

/-! # Simultaneous Pauli-axis choices on disjoint physical bonds -/

open Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
variable {n : ℕ}

/-- All axis choices on a matching extend to one product frame. -/
theorem axis_frame_on_matching (F : Finset (Fin (n+1))) (b : Fin (n+1)→Fin 3×Fin 3)
    (hm : ∀ e∈F, ∀ f∈F, e.castSucc≠f.succ) :
    ∃ a : Fin (n+2)→Fin 3, ∀ e∈F, (a e.castSucc,a e.succ)=b e := by
  classical
  let a (v : Fin (n+2)) : Fin 3 :=
    if h : ∃ e∈F, e.castSucc=v then (b h.choose).1
    else if h : ∃ e∈F, e.succ=v then (b h.choose).2 else 0
  refine ⟨a,?_⟩
  intro e he
  have hl : ∃ f∈F, f.castSucc=e.castSucc := ⟨e,he,rfl⟩
  have hr : ∃ f∈F, f.succ=e.succ := ⟨e,he,rfl⟩
  have hn : ¬∃ f∈F, f.castSucc=e.succ := fun ⟨f,hf,h⟩ => hm f hf e he h
  have hleft : hl.choose=e := Fin.ext (congrArg (fun i : Fin (n+2) => i.val) hl.choose_spec.2)
  have hright : hr.choose=e := Fin.succ_injective _ hr.choose_spec.2
  simp only [a,dif_pos hl,dif_neg hn,dif_pos hr,hleft,hright]

/-- In each bond choose any one of its nine couplings, possibly
a largest one and with a different pair of axes on every bond.
Two disjoint matchings suffice to test the entire cut. -/
theorem matched_axes_cut (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (t : ℝ) (z : ℂ) (hz : ‖z‖=1)
    (hc : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4)
    (ht : |t| * ‖u‖≤1/100) (b : Fin (n+1)→Fin 3×Fin 3) :
    4 * |t| * (∑ e∈crossed c, |u (.inr (e,b e))|)<2*π := by
  classical
  let A := crossed c
  let E := A.filter (fun e => e.val%2=0)
  let O := A\E
  have for_matching (F : Finset (Fin (n+1))) (hf : F⊆A)
      (hm : ∀ e∈F, ∀ f∈F, e.castSucc≠f.succ) :
      4 * |t| * (∑ e∈F, |u (.inr (e,b e))|)<π := by
    obtain ⟨a,ha⟩ := axis_frame_on_matching F b hm
    have hrow : (∑ e∈F, |u (.inr (e,b e))|) ≤ ∑ e∈A, |u (.inr (e,a e.castSucc,a e.succ))| := calc
      _ = ∑ e∈F, |u (.inr (e,a e.castSucc,a e.succ))| :=
        sum_congr rfl fun e he => by rw [ha e he]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hf (fun _ _ _ => abs_nonneg _)
    exact (mul_le_mul_of_nonneg_left hrow (by positivity)).trans_lt (every_frame_cut u C c t z hz hc ht a)
  have hpar {F : Finset (Fin (n+1))} {r : ℕ} (h : ∀ e∈F, e.val%2=r) :
      ∀ e∈F, ∀ f∈F, e.castSucc≠f.succ := by
    intro e he f hf hef
    have hval : e.val=f.val+1 := congrArg Fin.val hef
    have h₁ := h e he
    have h₂ := h f hf
    omega
  have hE := for_matching E (filter_subset ..) (hpar (r:=0) (fun e he => (mem_filter.mp he).2))
  have hO := for_matching O sdiff_subset (hpar (r:=1) (by
    intro e he
    obtain ⟨hi,hn⟩ := mem_sdiff.mp he
    have ho : e.val%2≠0 := fun h => hn (mem_filter.mpr ⟨hi,h⟩)
    omega))
  have hparts := sum_sdiff (filter_subset (fun e : Fin (n+1) => e.val%2=0) A)
    (f:=fun e => |u (.inr (e,b e))|)
  change (∑ e∈O, |u (.inr (e,b e))|)+(∑ e∈E, |u (.inr (e,b e))|)=_ at hparts
  change 4 * |t| * (∑ e∈A, |u (.inr (e,b e))|)<2*π
  rw [←hparts,mul_add]
  linarith only [hE,hO]

#print axioms matched_axes_cut
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
