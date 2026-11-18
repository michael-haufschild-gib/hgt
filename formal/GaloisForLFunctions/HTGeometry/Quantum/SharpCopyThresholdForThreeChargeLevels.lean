import GaloisForLFunctions.HTGeometry.Quantum.ResonancesOfTensorChargeObservations
import Mathlib.LinearAlgebra.Matrix.Notation

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
open scoped ComplexOrder
namespace GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels

def smallLabel : Fin 3 → ℤ := ![0,1,0]
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
      norm_num [base,B,mul_apply,Fin.sum_univ_succ,conjTranspose_apply,map_ofNat]
  have hbase : base.PosSemidef := he.symm ▸ posSemidef_conjTranspose_mul_self B
  refine ⟨twist_posSemidef _ _ _ hbase,?_⟩
  rw [state,twist_trace]
  norm_num [base,trace,diag_apply,Fin.sum_univ_succ]

/-- The example has simple spectrum 0, 1/4, 3/4 for every phase and every
copy threshold. Its purely spectral data therefore reveal no phase. -/
theorem state_charpoly (z : Circle) :
    (state z).charpoly = Polynomial.X * (Polynomial.X - Polynomial.C (1/4 : ℂ)) *
      (Polynomial.X - Polynomial.C (3/4 : ℂ)) := by
  rw [state,twist_charpoly,Matrix.charpoly,Matrix.det_fin_three]
  have h₂ : Polynomial.C (1/2 : ℂ) = Polynomial.C (1/4 : ℂ) + Polynomial.C (1/4 : ℂ) := by
    rw [← map_add]; norm_num
  have h₃ : Polynomial.C (3/4 : ℂ) =
      Polynomial.C (1/4 : ℂ) + Polynomial.C (1/4 : ℂ) + Polynomial.C (1/4 : ℂ) := by
    rw [← map_add,← map_add]; norm_num
  have hoff {i j : Fin 3} (h : i≠j) := charmatrix_apply_ne base i j h
  simp only [charmatrix_apply_eq,hoff (by decide : (0 : Fin 3)≠1),
    hoff (by decide : (0 : Fin 3)≠2),hoff (by decide : (1 : Fin 3)≠0),
    hoff (by decide : (1 : Fin 3)≠2),hoff (by decide : (2 : Fin 3)≠0),
    hoff (by decide : (2 : Fin 3)≠1),
    show base 0 0=1/2 from rfl,show base 0 1=1/4 from rfl,show base 0 2=1/4 from rfl,
    show base 1 0=1/4 from rfl,show base 1 1=1/4 from rfl,show base 1 2=0 from rfl,
    show base 2 0=1/4 from rfl,show base 2 1=0 from rfl,show base 2 2=1/4 from rfl,
    map_zero,h₂,h₃]
  ring

theorem edge_cost (i j : Fin 3) (h : base i j ≠ 0) :
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
      change (∑ k, (smallLabel (u k)-smallLabel (v k))) =
        -(m : ℤ)*(∑ k, (phaseLabel (u k)-phaseLabel (v k)))
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
    apply mul_ne_zero
    · change (1/4 : ℂ)≠0
      norm_num
    · apply prod_ne_zero_iff.mpr
      intro k _
      change (1/4 : ℂ)≠0
      norm_num
  · simp [displacement,u,v,Fin.sum_univ_succ,phaseLabel]

/-- The entire visible spectrum is a consecutive interval. Each extra
block of m+1 copies exposes exactly one further harmonic in each direction. -/
theorem all_frequencies (m n : ℕ) (d : ℤ) :
    d ∈ frequencies (charge m) phaseLabel base n ↔ (m+1)*d.natAbs ≤ n := by
  constructor
  · intro h
    have hc := frequency_cost m n d h
    exact_mod_cast (show ((m+1 : ℕ) : ℤ)*(d.natAbs : ℤ) ≤ n by simpa using hc)
  · intro h
    have padded : Monotone (frequencies (charge m) phaseLabel base) :=
      monotone_nat_of_le_succ fun j => frequencies_mono _ _ _ 0 (by norm_num [base]) j
    have many (k : ℕ) : (k : ℤ) ∈ frequencies (charge m) phaseLabel base (k*(m+1)) := by
      simpa only [mul_one] using multiple_frequency _ _ _ (first_frequency m) k
    have hs : base.transpose = base := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    cases d with
    | ofNat k =>
      exact padded (by simpa [Nat.mul_comm] using h) (many k)
    | negSucc k =>
      have hh := transpose_frequency _ _ _ (many (k+1))
      rw [hs] at hh
      exact padded (by simpa [Nat.mul_comm] using h) hh

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
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels.all_frequencies
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels.identified_at

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels.state_charpoly

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.ThreeLevels.edge_cost
