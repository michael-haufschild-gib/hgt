import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.PeriodicCuts

/-! # Physical Pauli labels in a full contiguous block -/

open Finset
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
open SpectralGapMass.Bulk.PeriodicCuts
noncomputable section

variable {n m B : ℕ}

/-- The interval of wires starting at B and having length L. -/
def intervalWires (N B L : ℕ) := univ.filter (fun v : Fin N => B ≤ v.val ∧ v.val < B+L)

def numberWires (h : B+(m+2) ≤ n+2) : Fin (m+2) ≃ intervalWires (n+2) B (m+2) where
  toFun i := ⟨⟨B+i.val,by have := i.isLt; omega⟩,mem_filter.mpr ⟨mem_univ _,by change B ≤ B+i.val ∧ B+i.val < B+(m+2); have := i.isLt; omega⟩⟩
  invFun j := ⟨j.val.val-B,by have := (mem_filter.mp j.2).2; omega⟩
  left_inv i := Fin.ext (by dsimp; omega)
  right_inv j := Subtype.ext (Fin.ext (by dsimp; have := (mem_filter.mp j.2).2; omega))

/-- Translation of both ends of each local Pauli term. -/
def translateLabel (h : B+(m+2) ≤ n+2) : PathLabel m → PathLabel n
  | .inl (i,a) => .inl ((numberWires h i).val,a)
  | .inr (e,p) => .inr (⟨B+e.val,by have := e.isLt; omega⟩,p)

theorem translateLabel_injective (h : B+(m+2) ≤ n+2) : Function.Injective (translateLabel h) := by
  rintro (⟨i,a⟩|⟨i,a⟩) (⟨j,b⟩|⟨j,b⟩) eq <;>
    simp [translateLabel,numberWires,Fin.ext_iff] at eq ⊢ <;> exact eq

def lastRow : PathLabel n → ℕ
  | .inl (i,_) => i.val
  | .inr (e,_) => e.val+1

/-- Ownership is precisely containment of both endpoints in the half-open interval. -/
theorem owner_iff_interval {L : ℕ} (hL : 0 < L) (b : Fin (n+2)) (l : PathLabel n) :
    owner L l = some b ↔ b.val*L ≤ (pathPauliSourceCoordinate l).1 ∧ lastRow l < b.val*L+L := by
  have he (x y : Fin (n+2)) : (if x = y then some x else none) = some b ↔ x = b ∧ y = b := by
    by_cases h : x = y
    · subst y; simp
    · simp [h]; exact fun hx hy => h (hx.trans hy.symm)
  unfold owner
  rw [he]
  simp only [Fin.ext_iff]
  rcases l with ⟨i,a⟩|⟨e,p⟩
  · change i.val/L = b.val ∧ i.val/L = b.val ↔ b.val*L ≤ i.val ∧ i.val < b.val*L+L
    rw [and_self,Nat.div_eq_iff hL]
    omega
  · change e.val/L = b.val ∧ (e.val+1)/L = b.val ↔ b.val*L ≤ e.val ∧ e.val+1 < b.val*L+L
    rw [Nat.div_eq_iff hL,Nat.div_eq_iff hL]
    omega

theorem owned_translate (b : Fin (n+2)) (h : b.val*(m+2)+(m+2) ≤ n+2) (l : PathLabel m) :
    owner (m+2) (translateLabel h l) = some b := by
  rw [owner_iff_interval (by omega)]
  rcases l with ⟨i,a⟩|⟨e,p⟩
  · change _ ≤ b.val*(m+2)+i.val ∧ b.val*(m+2)+i.val < _
    have := i.isLt; omega
  · change _ ≤ b.val*(m+2)+e.val ∧ b.val*(m+2)+e.val+1 < _
    have := e.isLt; omega

theorem translate_covers (b : Fin (n+2)) (h : b.val*(m+2)+(m+2) ≤ n+2)
    (l : PathLabel n) (hl : owner (m+2) l = some b) : ∃ k, translateLabel h k = l := by
  rw [owner_iff_interval (by omega)] at hl
  rcases l with ⟨i,a⟩|⟨e,p⟩
  · change b.val*(m+2) ≤ i.val ∧ i.val < b.val*(m+2)+(m+2) at hl
    refine ⟨.inl (⟨i.val-b.val*(m+2),by omega⟩,a),?_⟩
    exact congrArg Sum.inl (Prod.ext (Fin.ext (by change b.val*(m+2)+(i.val-b.val*(m+2))=i.val; omega)) rfl)
  · change b.val*(m+2) ≤ e.val ∧ e.val+1 < b.val*(m+2)+(m+2) at hl
    refine ⟨.inr (⟨e.val-b.val*(m+2),by omega⟩,p),?_⟩
    exact congrArg Sum.inr (Prod.ext (Fin.ext (by change b.val*(m+2)+(e.val-b.val*(m+2))=e.val; omega)) rfl)

end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
