import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution.Variation

/-! # Finite determination of the first asymmetric moment -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution

open Finset Filter
open scoped Topology

variable {I : Type*} [Fintype I]

/-- Reflection of the centered energy multiset is equivalent to cancellation
of the odd moments through the state count. -/
theorem reflection_iff_odd_moments (E : I → ℝ) :
    Reflects E ↔ ∀ j≤Fintype.card I, Odd j → moment (centered E) j=0 := by
  rw [reflects_iff_centered_pair,pairs_iff_matches]
  simp only [zero_sub]
  rw [matches_iff_moments]
  have neg (j : ℕ) (hj : Odd j) :
      moment (fun i => -centered E i) j = - moment (centered E) j := by
    simp only [moment,hj.neg_pow,sum_neg_distrib]
  constructor
  · intro eq j bound odd
    have h := eq j bound
    rw [neg j odd] at h
    linarith only [h]
  · intro zero j bound
    rcases Nat.even_or_odd j with even | odd
    · simp only [moment,even.neg_pow]
    · rw [neg j odd,zero j bound odd,neg_zero]

/-- Every asymmetric preparation has an odd first signal between three
and the number of states. It fixes both leading coefficients. -/
theorem asymmetric_order (E : I → ℝ) :
    Reflects E ∨ ∃ m : ℕ, 3 ≤ m+1 ∧ m+1 ≤ Fintype.card I ∧ Odd (m+1) ∧
      moment (centered E) (m+1)≠0 ∧
      (∀ k < m+1, Odd k → moment (centered E) k=0) ∧
      Tendsto (fun t => oddTrace (centered E) t/t^(m+1)) (𝓝[≠] 0)
        (𝓝 (2*moment (centered E) (m+1)/((m+1).factorial : ℝ))) ∧
      Tendsto (fun t => t*variation (centered E) 1 t/t^(m+1)) (𝓝[≠] 0)
        (𝓝 (2*moment (centered E) (m+1)/(m.factorial : ℝ))) := by
  classical
  by_cases symm : Reflects E
  · exact Or.inl symm
  right
  rw [reflection_iff_odd_moments] at symm
  push Not at symm
  obtain ⟨n,hn,no,hv⟩ := symm
  let P := fun k : ℕ => Odd k ∧ moment (centered E) k≠0
  have ex : ∃ k, P k := ⟨n,no,hv⟩
  have first := Nat.find_spec ex
  have bound : Nat.find ex ≤ Fintype.card I := (Nat.find_min' ex ⟨no,hv⟩).trans hn
  have early (k : ℕ) (h : k < Nat.find ex) (ho : Odd k) : moment (centered E) k=0 :=
    by_contra fun hm => Nat.find_min ex h ⟨ho,hm⟩
  obtain ⟨ho,hm⟩ := first
  have one : moment (centered E) 1=0 := by simpa only [moment,pow_one] using sum_centered E
  obtain ⟨m,eq⟩ := Nat.exists_eq_succ_of_ne_zero (show Nat.find ex≠0 by
    intro h; rw [h] at ho; simp at ho)
  rw [eq] at ho hm bound early
  have large : 3 ≤ m+1 := by
    obtain ⟨j,hj⟩ := ho
    have notOne : m+1≠1 := fun h => hm (by rw [show m.succ=1 from h]; exact one)
    omega
  refine ⟨m,large,bound,ho,hm,early,?_⟩
  have odds (k : ℕ) (hk : Odd k) : variation (centered E) k 0=2*moment (centered E) k := by
    simp only [variation_origin,moment,hk.neg_pow,sum_neg_distrib,sub_neg_eq_add,two_mul]
  have vanish (k : ℕ) (hk : k < m+1) : variation (centered E) k 0=0 := by
    rcases Nat.even_or_odd k with he | odd
    · simp only [variation_origin,moment,he.neg_pow,sub_self]
    · rw [odds k odd,early k hk odd,mul_zero]
  simpa only [odds (m+1) ho] using joint_limit (centered E) m vanish

#print axioms reflection_iff_odd_moments
#print axioms asymmetric_order

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution
