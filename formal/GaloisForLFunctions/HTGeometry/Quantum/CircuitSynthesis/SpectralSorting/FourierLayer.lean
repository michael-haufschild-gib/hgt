import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.SpectralSorting.BinaryPhases
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Subregister.Lift

/-! # One binary Fourier layer on physical wires -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralSorting
noncomputable section
open DiagonalSynthesis
private abbrev Q (n : ℕ) := Fin n→Bool
private abbrev R (n : ℕ) := Matrix (Q n) (Q n) ℂ

/-- Leave the last bit unchanged while transforming the low register. -/
def extendLow {n : ℕ} (U : R n) : R (n+1) := fun x y =>
  if x (Fin.last n)=y (Fin.last n) then U (x ∘ Fin.castSucc) (y ∘ Fin.castSucc) else 0

theorem realizes_extendLow {n k : ℕ} {U : R n} (h : Realizes k U) : Realizes k (extendLow U) := by
  classical
  let S : Finset (Fin (n+1)) := Finset.univ.erase (Fin.last n)
  let f (j : Fin n) : S := ⟨j.castSucc,Finset.mem_erase.mpr ⟨Fin.castSucc_ne_last j,Finset.mem_univ _⟩⟩
  let e := Equiv.ofBijective f (show Function.Bijective f from
    ⟨fun i j h => Fin.castSucc_injective n (congrArg Subtype.val h),by
      intro j
      have hj := (Finset.mem_erase.mp j.2).1
      refine ⟨j.val.castLT (Fin.lt_last_iff_ne_last.mpr hj),?_⟩
      exact Subtype.ext (Fin.ext rfl)⟩)
  have he : Subregister.place e U=extendLow U := by
    ext x y
    have hout : restrictOutsideConfiguration S x=restrictOutsideConfiguration S y ↔ x (Fin.last n)=y (Fin.last n) := by
      constructor
      · intro h
        exact congrFun h ⟨Fin.last n,Finset.notMem_erase ..⟩
      · intro h
        funext i
        have hlast : i.val=Fin.last n := by
          by_contra hi
          exact i.2 (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩)
        exact hlast ▸ h
    simp only [Subregister.place,liftLocalMatrix,hout,extendLow]
    split_ifs
    · rfl
    · rfl
  obtain ⟨z,hz,C,hC,hU⟩ := h
  refine ⟨z,hz,Subregister.placeCircuit e C,hC,?_⟩
  rw [←he,hU,Subregister.place_smul,Subregister.placeCircuit_eval]

/-- Each matrix coefficient has only one intermediate bit string.
Its high bit comes from the output and its low bits come from the input. -/
theorem layer_entry {n : ℕ} (U : R n) (g : Q (n+1)→ℂ) (y x : Q (n+1)) :
    (extendLow U*diagonal g*bitMix (Fin.last n)) y x =
      U (y ∘ Fin.castSucc) (x ∘ Fin.castSucc) *
        g (Function.update x (Fin.last n) (y (Fin.last n))) *
        boolHadamardMatrix (y (Fin.last n)) (x (Fin.last n)) := by
  classical
  let h := Fin.last n
  let z := Function.update x h (y h)
  have hz : z h=y h := Function.update_self ..
  have hlow (i : Fin n) : z i.castSucc=x i.castSucc := Function.update_of_ne (Fin.castSucc_ne_last i) ..
  have hmatch : ∀ j, j≠h → z j=x j := fun j hj => Function.update_of_ne hj ..
  rw [Matrix.mul_apply,Finset.sum_eq_single z]
  · rw [Matrix.mul_diagonal,extendLow,if_pos hz.symm,bitMix,if_pos hmatch,hz]
    have he : z ∘ Fin.castSucc=x ∘ Fin.castSucc := funext hlow
    rw [he]
  · intro w _ hw
    rw [Matrix.mul_diagonal,extendLow,bitMix]
    by_cases htop : y h=w h
    · rw [if_pos htop]
      have hm : ¬∀ j, j≠h → w j=x j := by
        intro hall
        apply hw
        funext j
        by_cases hj : j=h
        · subst j; exact htop.symm.trans hz.symm
        · exact (hall j hj).trans (hmatch j hj).symm
      rw [if_neg hm,mul_zero]
    · rw [if_neg htop,zero_mul,zero_mul]
  · simp

#print axioms realizes_extendLow
end
end GaloisForLFunctions.HTGeometry.SpectralSorting
