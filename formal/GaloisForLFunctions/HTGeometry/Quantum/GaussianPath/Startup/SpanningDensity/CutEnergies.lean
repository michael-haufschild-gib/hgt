import GaloisForLFunctions.HTGeometry.Quantum.PathPauliSpectralWidth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.PathCuts

/-! # Classical energy contrast for the four corners of a gate-respecting cut -/
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
noncomputable section

/-- Flip the first and second color classes independently. -/
def corner {ι : Type*} (c x : ι→Bool) (a b : Bool) (i : ι) : Bool :=
  xor (x i) (if c i then a else b)

def spin (b : Bool) : ℝ := if b then -1 else 1

/-- Alternating sum on a two-by-two rectangle. -/
def contrast (f : Bool→Bool→ℝ) := f false false + f true true - f true false - f false true

private theorem contrast_sum {ι : Type*} [Fintype ι] (f : ι→Bool→Bool→ℝ) :
    contrast (fun a b => ∑ i, f i a b)=∑ i, contrast (f i) := by
  simp only [contrast,Finset.sum_sub_distrib,Finset.sum_add_distrib]

private theorem pair_contrast (c d x y : Bool) :
    contrast (fun a b => spin (xor x (if c then a else b))*spin (xor y (if d then a else b))) =
      if c=d then 0 else 4*(spin x*spin y) := by
  cases c <;> cases d <;> cases x <;> cases y <;> norm_num [contrast,spin]

/-- The mixed contrast cancels all onsite fields and retains exactly
four times the signed longitudinal energy across the cut. -/
theorem energy_contrast {n : ℕ} (u : PathShell n) (c x : Fin (n+2)→Bool) :
    contrast (fun a b => pathDiagEnergy u (corner c x a b)) =
      4*∑ e ∈ Finset.univ.filter (fun e : Fin (n+1) => c e.castSucc ≠ c e.succ),
        u (.inr (e,2,2))*(spin (x e.castSucc)*spin (x e.succ)) := by
  let site (i : Fin (n+2)) (a b : Bool) := u (.inl (i,2))*spin (corner c x a b i)
  let pair (e : Fin (n+1)) (a b : Bool) := u (.inr (e,2,2))*
    (spin (corner c x a b e.castSucc)*spin (corner c x a b e.succ))
  have hsite (i : Fin (n+2)) : contrast (site i)=0 := by
    cases hi : c i <;> simp [site,contrast,corner,hi]
  have hpair (e : Fin (n+1)) : contrast (pair e) = if c e.castSucc≠c e.succ then
      4*(u (.inr (e,2,2))*(spin (x e.castSucc)*spin (x e.succ))) else 0 := by
    have h : contrast (pair e)=u (.inr (e,2,2))*contrast (fun a b =>
        spin (corner c x a b e.castSucc)*spin (corner c x a b e.succ)) := by
      simp only [contrast,pair]; ring
    rw [h]
    unfold corner
    rw [pair_contrast]
    by_cases he : c e.castSucc=c e.succ <;> simp [he]
    ring
  have hE (a b : Bool) : pathDiagEnergy u (corner c x a b) =
      (∑ i, site i a b)+(∑ e, pair e a b) := by
    unfold pathDiagEnergy
    congr 1
    · simp only [zSetSign_singleton,site,spin]
    · apply Finset.sum_congr rfl
      intro e _
      have he : e.castSucc≠e.succ := by
        intro hh; have hv := congrArg Fin.val hh; simp at hv
      simp [pair,zSetSign,spin,he]
  simp_rw [hE]
  rw [show contrast (fun a b => (∑ i, site i a b)+(∑ e, pair e a b)) =
    contrast (fun a b => ∑ i, site i a b)+contrast (fun a b => ∑ e, pair e a b) by
      unfold contrast; ring,contrast_sum,contrast_sum]
  simp only [hsite,hpair,Finset.sum_const_zero,zero_add,Finset.mul_sum,Finset.sum_filter,mul_ite,mul_zero]

/-- Every assignment of signs on the physical edges is the product of
neighboring spin signs of one common computational configuration. -/
theorem realize_edge_signs {n : ℕ} (p : Fin n→Bool) :
    ∃ x : Fin (n+1)→Bool, ∀ e, spin (x e.castSucc)*spin (x e.succ)=spin (p e) := by
  let x : Fin (n+1)→Bool := Fin.induction false (fun i b => xor b (p i))
  refine ⟨x,?_⟩
  intro e
  have h : x e.succ=xor (x e.castSucc) (p e) := Fin.induction_succ ..
  rw [h]
  cases x e.castSucc <;> cases p e <;> norm_num [spin]

#print axioms energy_contrast
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
