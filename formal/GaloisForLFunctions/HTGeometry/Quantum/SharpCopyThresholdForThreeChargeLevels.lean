import GaloisForLFunctions.HTGeometry.Quantum.ResonancesOfTensorChargeObservations
import Mathlib.Data.Matrix.Notation

/-!
# An arbitrarily late phase threshold on three charge levels

For levels of charge 0, 1 and m, the two coherences through level zero may
have independent phases. The direct edge between 1 and m is absent. A
balanced tensor entry sensitive to their relative phase must therefore
use at least m unit edges and one long edge. A positive trace-one state
attains this lower bound.
-/

noncomputable section
open Finset Matrix
namespace GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels

private def smallLabel : Fin 3 → ℤ := ![0,1,0]
def phaseLabel : Fin 3 → ℤ := ![0,0,1]

def charge (m : ℕ) (i : Fin 3) : ℤ := smallLabel i + (m : ℤ)*phaseLabel i

/-- A density matrix with two occupied edges meeting at the zero-charge level. -/
def base : Matrix (Fin 3) (Fin 3) ℂ := !![1/2,1/4,1/4; 1/4,1/4,0; 1/4,0,1/4]

def state (z : Circle) := twist phaseLabel z base

/-- The states are normalized Gram matrices throughout the phase circle. -/
theorem density (z : Circle) : (state z).PosSemidef ∧ (state z).trace=1 := by
  let B : Matrix (Fin 2) (Fin 3) ℂ := !![1/2,1/2,0; 1/2,0,1/2]
  have he : base=Bᴴ*B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [base,B,mul_apply,Fin.sum_univ_succ,conjTranspose_apply]
  have hbase : base.PosSemidef := he.symm ▸ posSemidef_conjTranspose_mul_self B
  refine ⟨twist_posSemidef _ _ _ hbase,?_⟩
  rw [state,twist_trace]
  norm_num [base,trace,diag_apply,Fin.sum_univ_succ]

private theorem edge_cost (i j : Fin 3) (h : base i j ≠ 0) :
    |smallLabel i-smallLabel j| + |phaseLabel i-phaseLabel j| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> norm_num [smallLabel,phaseLabel,base] at *

/-- Every active frequency d costs at least (m+1)|d| copies. -/
theorem frequency_cost (m n : ℕ) (d : ℤ) (hd : d ∈ frequencies (charge m) phaseLabel base n) :
    ((m : ℤ)+1)*|d| ≤ n := by
  obtain ⟨u,v,hn,rfl⟩ := (frequency_iff _ _ _ _ _).1 hd
  rw [observe_entry] at hn
  split at hn <;> rename_i h
  · have hlocal (k : Fin n) : base (u k) (v k) ≠ 0 :=
      fun hz => hn (prod_eq_zero (mem_univ k) hz)
    have hq : displacement smallLabel u v = -(m : ℤ)*displacement phaseLabel u v := by
      simp only [displacement,charge,show ∀ a b c e : ℤ, a+m*b-(c+m*e)=(a-c)+m*(b-e)
        from fun _ _ _ _ => by ring,sum_add_distrib,← mul_sum] at h
      change _ = -(m : ℤ)*(∑ k, (phaseLabel (u k)-phaseLabel (v k)))
      change (∑ k, (smallLabel (u k)-smallLabel (v k))) + _ = 0 at h
      linear_combination h
    have hc : |displacement smallLabel u v| + |displacement phaseLabel u v| ≤ (n : ℤ) := by
      refine (add_le_add (abs_sum_le_sum_abs _ _) (abs_sum_le_sum_abs _ _)).trans ?_
      rw [← sum_add_distrib]
      calc
        _ ≤ ∑ _k : Fin n, (1 : ℤ) := sum_le_sum fun k _ => edge_cost _ _ (hlocal k)
        _ = _ := by simp
    rw [hq,abs_mul,abs_neg,abs_of_nonneg (Int.natCast_nonneg m)] at hc
    exact (by linear_combination hc)
  · exact (hn rfl).elim

/-- Total-charge observation through m copies is identical around the entire phase circle. -/
theorem invisible_through (m n : ℕ) (hn : n ≤ m) (z w : Circle) :
    observe (charge m) (state z) n = observe (charge m) (state w) n := by
  apply (indistinguishable_iff _ _ _ _ _ _).2
  intro d hd
  have h := frequency_cost m n d hd
  have hz : d=0 := by
    by_contra hne
    have hp : 1 ≤ |d| := by exact Int.add_one_le_iff.mpr (abs_pos.mpr hne)
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (m : ℤ)+1)
    have hn' : (n : ℤ) ≤ m := by exact_mod_cast hn
    linarith only [h,hm,hn']
  simp [hz]

/-- One long edge is balanced by exactly m unit edges with the opposite orientation. -/
theorem first_frequency (m : ℕ) : 1 ∈ frequencies (charge m) phaseLabel base (m+1) := by
  let u : Fin (m+1) → Fin 3 := Fin.cons 2 (fun _ => 0)
  let v : Fin (m+1) → Fin 3 := Fin.cons 0 (fun _ => 1)
  apply (frequency_iff _ _ _ _ _).2
  refine ⟨u,v,?_,?_⟩
  · rw [observe_entry]
    have he : displacement (charge m) u v=0 := by
      simp [displacement,u,v,Fin.sum_univ_succ,charge,phaseLabel,smallLabel]
    rw [if_pos he,Fin.prod_univ_succ]
    norm_num [u,v,base]
  · simp [displacement,u,v,Fin.sum_univ_succ,phaseLabel]

/-- The first identifying observation recovers the entire phase, at m+1 copies. -/
theorem identified_at (m : ℕ) (z w : Circle) :
    observe (charge m) (state z) (m+1) = observe (charge m) (state w) (m+1) ↔ z=w := by
  constructor
  · intro h
    simpa using (indistinguishable_iff _ _ _ _ _ _).1 h 1 (first_frequency m)
  · rintro rfl
    rfl

end GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels.density
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels.frequency_cost
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels.invisible_through
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels.first_frequency
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels.identified_at
