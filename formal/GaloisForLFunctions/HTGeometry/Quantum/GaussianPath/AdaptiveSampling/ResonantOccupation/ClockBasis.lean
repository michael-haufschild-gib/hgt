import GaloisForLFunctions.HTGeometry.FrequencyLatticeBasis
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.Aliasing

/-! # Free angular frequencies on residue classes of an arbitrary integer clock -/

open Finset Real
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ResonantOccupation
noncomputable section

private theorem free_without_pivot {k : ℕ} (γ : Fin (k+1) → ℝ) (hγ : RationallyIndependentFrequency γ)
    (c : Fin (k+1) → ℤ) (hc : finiteTorusCharacterDetuning c γ=2*π)
    (p : Fin (k+1)) (hp : c p≠0) : FreeAtStep (γ ∘ p.succAbove) 1 := by
  intro m z hz
  let w := p.insertNth (α := fun _ => ℤ) 0 m
  have hw : finiteTorusCharacterDetuning w γ=finiteTorusCharacterDetuning m (γ ∘ p.succAbove) := by
    rw [finiteTorusCharacterDetuning,Fin.sum_univ_succAbove _ p]
    simp [w,finiteTorusCharacterDetuning]
  have hrel := resonance_proportional hγ (one_ne_zero : (1:ℝ)≠0)
    (v:=c) (k:=1) (w:=w) (l:=z) (by simpa using hc) (by rw [hw]; exact hz) p
  have hz0 : z*c p=0 := by simpa [w] using hrel.symm
  have hz' := (mul_eq_zero.mp hz0).resolve_right hp
  rw [hz',Int.cast_zero,zero_mul,one_mul] at hz
  have hh := hγ w (hw.trans hz)
  funext i
  simpa [w] using congrFun hh (p.succAbove i)

/-- After passing to a residue class of a positive modulus, every
sampled frequency is an integer combination of frequencies free at
step one, up to an integer multiple of a full turn. -/
theorem exists_free_clock_basis {I : Type*} [Fintype I] (β : I → ℝ) :
    ∃ (L : ℕ) (_ : 0<L) (k : ℕ) (γ : Fin k → ℝ) (M : I → Fin k → ℤ) (h : I → ℤ),
      FreeAtStep γ 1 ∧ ∀ i, (L:ℝ)*β i=(h i:ℝ)*(2*π)+∑ j, (M i j:ℝ)*γ j := by
  classical
  let F : Option I → ℝ := fun i => i.elim (2*π) β
  obtain ⟨k,γ,M,_,hγ,_,_,hM,_⟩ := exists_frequency_integer_basis F
  have hc : 2*π=∑ j, (M none j:ℝ)*γ j := hM none
  cases k with
  | zero =>
    simp at hc
  | succ k =>
    let c := M none
    obtain ⟨p,hp⟩ : ∃ p, c p≠0 := by
      by_contra! hh
      have hz : ∀ j, M none j=0 := hh
      simp only [hz,Int.cast_zero,zero_mul,sum_const_zero] at hc
      exact (mul_ne_zero two_ne_zero pi_ne_zero) hc
    let a := c p
    let L := a.natAbs*a.natAbs
    have hL : 0<L := Nat.mul_pos (Int.natAbs_pos.mpr hp) (Int.natAbs_pos.mpr hp)
    have hsq : (L:ℝ)=(a:ℝ)*a := by exact_mod_cast Int.natAbs_mul_self (a:=a)
    let R i j := (L:ℤ)*M (some i) (p.succAbove j)-M (some i) p*a*c (p.succAbove j)
    refine ⟨L,hL,k,γ ∘ p.succAbove,R,fun i => M (some i) p*a,free_without_pivot γ hγ c hc.symm p hp,?_⟩
    intro i
    have hi : β i=∑ j, (M (some i) j:ℝ)*γ j := hM (some i)
    rw [Fin.sum_univ_succAbove _ p] at hi hc
    have hs : ∑ j, (R i j:ℝ)*γ (p.succAbove j) =
        (L:ℝ)*(∑ j, (M (some i) (p.succAbove j):ℝ)*γ (p.succAbove j))-
        ((M (some i) p:ℝ)*(a:ℝ))*(∑ j, (c (p.succAbove j):ℝ)*γ (p.succAbove j)) := by
      simp only [R,Int.cast_sub,Int.cast_mul,Int.cast_natCast,sub_mul,mul_assoc,
        sum_sub_distrib,mul_sum]
    simp only [Function.comp_apply,Int.cast_mul,hs]
    rw [hi,hc]
    change (L:ℝ)*_=(M (some i) p:ℝ)*(a:ℝ)*((a:ℝ)*γ p+_)+_
    rw [hsq]
    dsimp only [c]
    ring

#print axioms exists_free_clock_basis
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ResonantOccupation
