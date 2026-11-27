import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.RotatedShell
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.SeamDensity

/-! # Pauli frame changes preserve every weak seam on the physical chain -/

open Finset
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
open private wordSign abs_sign axesEquiv permute from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.RotatedShell
variable {n : ℕ}

theorem rotated_bond_magnitude (a : Fin (n+2)→Fin 3) (u : PathShell n) (e : Fin (n+1)) (q : Fin 3×Fin 3) :
    |rotatedShell a u (.inr (e,q))|=
      |u (.inr (e,Equiv.swap (a e.castSucc) 2 q.1,Equiv.swap (a e.succ) 2 q.2))| := by
  change |wordSign a _*u _|=_
  rw [abs_mul,abs_sign,one_mul]
  rfl

theorem rotated_coordinate_cap (a : Fin (n+2)→Fin 3) (u : PathShell n) {R : ℝ}
    (h : ∀ l, |u l|≤R) (l : PathLabel n) : |rotatedShell a u l|≤R := by
  change |wordSign a _*u _|≤R
  rw [abs_mul,abs_sign,one_mul]
  exact h _

/-- Extend the rotated prefix to the original infinite draw by keeping
the coefficients outside its sites and bonds. -/
def rotatedDraw (a : Fin (n+2)→Fin 3) (ω : PathPauliDisorder) : PathPauliDisorder :=
  fun p => match p.2 with
    | .inl b => if h : p.1<n+2 then rotatedShell a (pathPauliDisorderShell ω n) (.inl (⟨p.1,h⟩,b)) else ω p
    | .inr q => if h : p.1<n+1 then rotatedShell a (pathPauliDisorderShell ω n) (.inr (⟨p.1,h⟩,q)) else ω p

theorem shell_rotated_draw (a : Fin (n+2)→Fin 3) (ω : PathPauliDisorder) :
    pathPauliDisorderShell (rotatedDraw a ω) n=rotatedShell a (pathPauliDisorderShell ω n) := by
  ext l
  rcases l with ⟨i,b⟩|⟨e,q⟩
  · change (if _ : i.val<n+2 then _ else _)=_
    rw [dif_pos i.isLt]
  · change (if _ : e.val<n+1 then _ else _)=_
    rw [dif_pos e.isLt]

theorem weak_row_rotated_draw (a : Fin (n+2)→Fin 3) (ω : PathPauliDisorder) (j : ℕ) (γ : ℝ) :
    FixedHorizon.weakRow γ (rotatedDraw a ω) j ↔ FixedHorizon.weakRow γ ω j := by
  by_cases hj : j<n+1
  · let e : Fin (n+1) := ⟨j,hj⟩
    let p (q : Fin 3×Fin 3) := (Equiv.swap (a e.castSucc) 2 q.1,Equiv.swap (a e.succ) 2 q.2)
    have he (q : Fin 3×Fin 3) : |FixedHorizon.bondRow (rotatedDraw a ω) j q|=|FixedHorizon.bondRow ω j (p q)| := by
      change |(if _ : j<n+1 then _ else _)|=_
      rw [dif_pos hj]
      exact rotated_bond_magnitude a _ e q
    constructor
    · intro h q
      have ht := h (p q)
      rwa [he,show p (p q)=q by simp [p]] at ht
    · intro h q
      rw [he]
      exact h _
  · change (∀ q, |(if _ : j<n+1 then _ else _)|≤γ) ↔ _
    simp only [dif_neg hj]
    rfl

/-- The same bracket strips succeed and fail before and after rotation,
including strips that extend beyond the end of the prefix. -/
theorem rotated_missed_bonds (a : Fin (n+2)→Fin 3) (ω : PathPauliDisorder) (R : ℕ) (γ : ℝ) :
    FixedHorizon.missedBonds n R γ (rotatedDraw a ω)=FixedHorizon.missedBonds n R γ ω := by
  ext e
  simp only [FixedHorizon.missedBonds,mem_filter,mem_univ,true_and,FixedHorizon.failedStrips,
    Set.mem_union,FixedHorizon.absentStrip,Set.mem_setOf_eq,weak_row_rotated_draw]

#print axioms rotated_missed_bonds
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
