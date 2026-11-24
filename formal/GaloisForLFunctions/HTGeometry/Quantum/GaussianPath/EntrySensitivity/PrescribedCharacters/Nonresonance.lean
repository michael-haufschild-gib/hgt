import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.FirstEntry
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.Weyl
import Mathlib.NumberTheory.Real.Irrational

/-! # Nonresonance at a first scalar entry of irrational arc width -/

open Set Finset MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters
open AdaptiveSampling PrecisionReturns
noncomputable section

/-- Extend an anchored character by the unique coefficient at the
reference level that makes the sum of coefficients zero. -/
private theorem lift_character {I : Type*} [Fintype I] [DecidableEq I] (E : I → ℝ) (i : I)
    (n : {j : I // j≠i} → ℤ) :
    ∃ m : I → ℤ, (∑ j, m j)=0 ∧
      (∑ j, (m j:ℝ)*E j)=finiteTorusCharacterDetuning n (projectiveFrequency E i) ∧
      ∀ j : {j : I // j≠i}, m j.val=n j := by
  let m (j : I) := if h : j≠i then n ⟨j,h⟩ else -∑ b, n b
  have keep (j : {j : I // j≠i}) : m j.val=n j := dif_pos j.property
  have base : m i = -∑ b, n b := dif_neg (not_not_intro rfl)
  refine ⟨m,?_,?_,keep⟩
  · rw [Fintype.sum_eq_add_sum_subtype_ne m i,base]
    simp only [keep,neg_add_cancel]
  · rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => (m j:ℝ)*E j) i,base]
    simp only [keep,Int.cast_neg,Int.cast_sum,neg_mul,Finset.sum_mul,finiteTorusCharacterDetuning,
      projectiveFrequency,mul_sub,Finset.sum_sub_distrib]
    abel

private theorem irrational_period {r : ℝ} (hr : Irrational r) {c q z : ℤ}
    (h : (c:ℝ)*((q:ℝ)+r)=z) : c=0 := by
  by_contra hn
  have hc : (c:ℝ)≠0 := by exact_mod_cast hn
  apply (irrational_iff_ne_rational r).mp hr (z-c*q) c hn
  apply (eq_div_iff hc).mpr
  push_cast
  linear_combination h

/-- At the absolute first return to a prescribed scalar error of
irrational arc width, no nonzero projective character has integer
winding. All outside origins are allowed on one typical draw. -/
theorem gaussian_first_entry_free (ε : ℝ) (hε : 0<ε) (hs : ε<sqrt 2)
    (hr : Irrational (SharpOccupation.physicalArc ε)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∀ a > (0:ℝ), ε < orbitCircuitDistance H 0 a → ∀ b : Label k,
        FreeAtStep (projectiveFrequency (energy ω k) b) (firstVisit H a 0 ε) := by
  let tick (z : ℤ) := (z:ℝ)*(2*π)
  filter_upwards [gaussian_first_entry_character (range tick) (countable_range _) ε hε hs] with ω hω k
  intro u H a ha hout b n z hz
  let v := firstVisit H a 0 ε
  let E := energy ω k
  obtain ⟨i,j,_,⟨q,hq⟩,hh⟩ := hω k a ha hout
  obtain ⟨m,hbal,he,keep⟩ := lift_character E b n
  have ht : v*(∑ l, (m l:ℝ)*E l)=tick z := (congrArg (v*·) he).trans hz
  have hm := hh m hbal ⟨z,ht.symm⟩
  have heq : ∑ l, (m l:ℝ)*E l=(m i:ℝ)*(E i-E j) := by
    calc
      _ = ∑ l, (m i:ℝ)*((pairCharge i j l:ℝ)*E l) := by
        apply Finset.sum_congr rfl
        intro l _
        conv_lhs => rw [hm l,Int.cast_mul,mul_assoc]
      _ = _ := by rw [←Finset.mul_sum,pair_action]
  have hmul : (m i:ℝ)*(2*π*((q:ℝ)+SharpOccupation.physicalArc ε))=tick z := by
    rw [←hq,←ht,heq]
    ring
  have hv : m i=0 := irrational_period hr (c:=m i) (q:=q) (z:=z) <|
    mul_right_cancel₀ (by positivity : 2*π≠0) <| by
      calc
        _ = (m i:ℝ)*(2*π*((q:ℝ)+SharpOccupation.physicalArc ε)) := by ring
        _ = _ := hmul
  funext l
  rw [←keep l,hm l.val,hv,zero_mul,Pi.zero_apply]

#print axioms gaussian_first_entry_free
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters
