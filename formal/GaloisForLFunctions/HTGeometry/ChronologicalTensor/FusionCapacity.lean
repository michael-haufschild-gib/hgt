import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Fusion
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Fusion capacity as an actual supremum and its logarithmic spectrum

The repeated cubic fusion bounds and witnesses determine a bounded
supremum over all unit-budget block probes. This supremum is exactly
sixCapacity^n, including the empty product. Its logarithm consequently
has a strictly positive constant spacing and is additive under fusion.
No arithmetic spectrum is supplied as an assumption.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def fusedCapacityValues (n : ℕ) : Set ℝ :=
  {z | ∃ a b c d e : Fin n → ℝ, blockCost n a b c d e ≤ 1 ∧
    z=|fusedResponse n a b c d e|}

def fusedCapacity (n : ℕ) : ℝ := sSup (fusedCapacityValues n)

theorem fusedCapacityValues_upper (n : ℕ) :
    ∀ z ∈ fusedCapacityValues n, z ≤ sixCapacity^n := by
  rintro z ⟨a,b,c,d,e,hcost,rfl⟩
  have hnonneg : 0 ≤ blockCost n a b c d e := by
    unfold blockCost sixCost
    positivity
  have hpow := pow_le_pow_left₀ hnonneg hcost (3*n)
  rw [one_pow] at hpow
  exact (fused_sharp_bound n a b c d e).trans
    ((mul_le_mul_of_nonneg_left hpow (pow_nonneg sixCapacity_nonneg n)).trans_eq (mul_one _))

theorem fusedCapacityValues_bddAbove (n : ℕ) : BddAbove (fusedCapacityValues n) :=
  ⟨sixCapacity^n,fusedCapacityValues_upper n⟩

theorem fusedCapacityValues_attained (n : ℕ) : sixCapacity^n ∈ fusedCapacityValues n := by
  cases n with
  | zero =>
    refine ⟨(fun _ => 0),(fun _ => 0),(fun _ => 0),(fun _ => 0),(fun _ => 0),?_,?_⟩
    · simp [blockCost]
    · simp [fusedResponse]
  | succ n =>
    have h := fused_attained n
    exact ⟨(fun _ => ((1-peakPosition)/2)/(n+1)),(fun _ => 0),
      (fun _ => peakPosition/(n+1)),(fun _ => 0),(fun _ => ((1-peakPosition)/2)/(n+1)),
      h.1.le,h.2.symm⟩

theorem fusedCapacity_exact (n : ℕ) : fusedCapacity n=sixCapacity^n := by
  apply le_antisymm
  · exact csSup_le ⟨_,fusedCapacityValues_attained n⟩ (fusedCapacityValues_upper n)
  · exact le_csSup (fusedCapacityValues_bddAbove n) (fusedCapacityValues_attained n)

def fusionSpacing : ℝ := Real.log (fusedCapacity 1)

def fusionEnergy (n : ℕ) : ℝ := Real.log (fusedCapacity n)

theorem fusionSpacing_eq : fusionSpacing=Real.log sixCapacity := by
  rw [fusionSpacing,fusedCapacity_exact,pow_one]

theorem fusionSpacing_pos : 0 < fusionSpacing := by
  rw [fusionSpacing_eq]
  exact Real.log_pos sixCapacity_gt_one

theorem fusionEnergy_eq (n : ℕ) : fusionEnergy n=(n : ℝ)*fusionSpacing := by
  rw [fusionEnergy,fusedCapacity_exact,Real.log_pow,fusionSpacing_eq]

theorem fusionEnergy_add (n m : ℕ) : fusionEnergy (n+m)=fusionEnergy n+fusionEnergy m := by
  rw [fusionEnergy_eq,fusionEnergy_eq,fusionEnergy_eq,Nat.cast_add]
  ring

theorem fusionEnergy_zero : fusionEnergy 0=0 := by
  rw [fusionEnergy_eq,Nat.cast_zero,zero_mul]

theorem fusionEnergy_succ_pos (n : ℕ) : 0 < fusionEnergy (n+1) := by
  rw [fusionEnergy_eq]
  exact mul_pos (by positivity) fusionSpacing_pos

theorem fusionEnergy_strictMono : StrictMono fusionEnergy := by
  intro n m hnm
  rw [fusionEnergy_eq,fusionEnergy_eq]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hnm) fusionSpacing_pos

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
