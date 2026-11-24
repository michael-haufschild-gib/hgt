import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.ActionRatios
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.FirstVisit

/-! # All prescribed balanced actions at a first scalar entry -/

open Matrix MeasureTheory Set Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters
open EmptyVisitFlux FirstGate PrecisionReturns
noncomputable section

/-- Primitive charge for the difference of two energy levels. -/
def pairCharge {I : Type*} [DecidableEq I] (i j : I) (l : I) : ℤ :=
  (if l=i then 1 else 0)-(if l=j then 1 else 0)

private theorem pair_balanced {I : Type*} [Fintype I] [DecidableEq I] (i j : I) :
    ∑ l, pairCharge i j l=0 := by simp [pairCharge,sum_sub_distrib]

theorem pair_action {I : Type*} [Fintype I] [DecidableEq I] (i j : I) (E : I → ℝ) :
    ∑ l, (pairCharge i j l:ℝ)*E l=E i-E j := by
  have term (a l : I) : ((if l=a then 1 else 0 : ℤ):ℝ)*E l=(if l=a then E a else 0) := by
    by_cases h : l=a <;> simp [h]
  simp only [pairCharge,Int.cast_sub,sub_mul,sum_sub_distrib,term]
  simp

/-- Fix a countable list of target angles and the scalar tolerance before
drawing the chain. At each actual first scalar entry, any balanced charge
whose lifted action is on the list is an integer multiple of the closing
pair. The observation origin may be chosen after seeing the disorder. -/
theorem gaussian_first_entry_character (T : Set ℝ) (hT : T.Countable)
    (ε : ℝ) (hε : 0 < ε) (hs : ε < sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let E := energy ω k
      ∀ a > (0:ℝ), ε < orbitCircuitDistance H 0 a → let v := firstVisit H a 0 ε
        ∃ i j : Label k, i≠j ∧ (∃ q : ℤ, v*(E i-E j)=2*π*((q:ℝ)+SharpOccupation.physicalArc ε)) ∧
          ∀ m : Label k → ℤ, (∑ l, m l)=0 → (v*∑ l, (m l:ℝ)*E l) ∈ T →
            ∀ l, m l=m i*pairCharge i j l := by
  classical
  let r := SharpOccupation.physicalArc ε
  let tick (q : ℤ) := 2*π*((q:ℝ)+r)
  let S := T ∪ range tick
  filter_upwards [gaussian_two_actions S (hT.union (countable_range tick))] with ω hω k
  intro u H E a ha hout v
  obtain ⟨hav,he⟩ := first_empty_entry_of_outside H hε hs hout
  have hr := (SharpOccupation.physicalArc_spec hε hs).1
  let w := fun l => -E l/(2*π)
  obtain ⟨i,j,hface⟩ := (entry_iff_closed_face w hr.1.le hr.2).mp he
  have hij : i≠j := fun h => hface.1.ne (congrArg w h.symm)
  obtain ⟨q,hq⟩ := lift_gap (fun l => -E l) v i j hface.2.1
  have hgap : v*(E i-E j)=tick q := by
    have hh := (div_eq_iff (by positivity : 2*π≠0)).mp hq
    dsimp only [tick]
    rw [neg_sub_neg] at hh
    exact hh.trans (mul_comm _ _)
  have hd : E i≠E j := by
    intro h
    exact hface.1.ne (by change -E j/(2*π)= -E i/(2*π); rw [h])
  have hb : v*(E i-E j)≠0 := mul_ne_zero (ha.trans hav).ne' (sub_ne_zero.mpr hd)
  refine ⟨i,j,hij,⟨q,hgap⟩,?_⟩
  intro m hm hmt
  let A := v*∑ l, (m l:ℝ)*E l
  let B := v*(E i-E j)
  have hsB : B ∈ S := Or.inr ⟨q,hgap.symm⟩
  have hrow := hω k v m (pairCharge i j) hm (pair_balanced i j)
    (Or.inl hmt) (by rw [pair_action]; exact hsB)
  have hrel (l : Label k) : B*(m l:ℝ)=A*(pairCharge i j l:ℝ) := by
    simpa only [pair_action] using hrow l
  have hi : B*(m i:ℝ)=A := by
    have hpair : pairCharge i j i=1 := by simp [pairCharge,hij]
    simpa only [hpair,Int.cast_one,mul_one] using hrel i
  intro l
  have hh : B*(m l:ℝ)=B*((m i:ℝ)*(pairCharge i j l:ℝ)) := by
    rw [←mul_assoc,hi]; exact hrel l
  exact_mod_cast mul_left_cancel₀ hb hh

#print axioms gaussian_first_entry_character
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters
