import GaloisForLFunctions.HTGeometry.AtomicResponseMoments

/-!
# Finite response probes identify low-order atomic moment data

The polynomial sufficiency mechanism in section 4.1 of Araújo, arXiv:2609.05560 becomes an
exact finite observation equivalence for the existing CCM moments. Three quadratic probes
recover the first three moments and therefore the entire order-two Hankel section. Four
cubic probes recover the first four moments. Source weights may be signed or unnormalized.
-/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Three quadratic response probes carry exactly mass, first moment, and second moment. -/
theorem quadratic_response_three_probes_iff_moments {n m : ℕ}
    (w z : Fin n → ℝ) (v t : Fin m → ℝ) :
    (finiteResponseForce (fun u => u ^ (2 : ℕ)) w z 0 = finiteResponseForce (fun u => u ^ (2 : ℕ)) v t 0 ∧
      finiteResponseForce (fun u => u ^ (2 : ℕ)) w z 1 = finiteResponseForce (fun u => u ^ (2 : ℕ)) v t 1 ∧
      finiteResponseForce (fun u => u ^ (2 : ℕ)) w z (-1) = finiteResponseForce (fun u => u ^ (2 : ℕ)) v t (-1)) ↔
    (RHTower.ccmAtomicMixedMoment w z 0 = RHTower.ccmAtomicMixedMoment v t 0 ∧
      RHTower.ccmAtomicMixedMoment w z 1 = RHTower.ccmAtomicMixedMoment v t 1 ∧
      RHTower.ccmAtomicMixedMoment w z 2 = RHTower.ccmAtomicMixedMoment v t 2) := by
  constructor
  · rintro ⟨h0, h1, hn⟩
    simp only [finiteResponseForce_quadratic_moments] at h0 h1 hn
    norm_num at h0 h1 hn
    exact ⟨by linarith, by linarith, h0⟩
  · rintro ⟨h0, h1, h2⟩
    simp [finiteResponseForce_quadratic_moments, h0, h1, h2]

/-- Four cubic response probes carry exactly the first four atomic moments, including mass. -/
theorem cubic_response_four_probes_iff_moments {n m : ℕ}
    (w z : Fin n → ℝ) (v t : Fin m → ℝ) :
    (finiteResponseForce (fun u => u ^ (3 : ℕ)) w z 0 = finiteResponseForce (fun u => u ^ (3 : ℕ)) v t 0 ∧
      finiteResponseForce (fun u => u ^ (3 : ℕ)) w z 1 = finiteResponseForce (fun u => u ^ (3 : ℕ)) v t 1 ∧
      finiteResponseForce (fun u => u ^ (3 : ℕ)) w z (-1) = finiteResponseForce (fun u => u ^ (3 : ℕ)) v t (-1) ∧
      finiteResponseForce (fun u => u ^ (3 : ℕ)) w z 2 = finiteResponseForce (fun u => u ^ (3 : ℕ)) v t 2) ↔
    (RHTower.ccmAtomicMixedMoment w z 0 = RHTower.ccmAtomicMixedMoment v t 0 ∧
      RHTower.ccmAtomicMixedMoment w z 1 = RHTower.ccmAtomicMixedMoment v t 1 ∧
      RHTower.ccmAtomicMixedMoment w z 2 = RHTower.ccmAtomicMixedMoment v t 2 ∧
      RHTower.ccmAtomicMixedMoment w z 3 = RHTower.ccmAtomicMixedMoment v t 3) := by
  constructor
  · rintro ⟨h0, h1, hn, h2⟩
    simp only [finiteResponseForce_cubic_moments] at h0 h1 hn h2
    norm_num at h0 h1 hn h2
    exact ⟨by linarith, by linarith, by linarith, h0⟩
  · rintro ⟨h0, h1, h2, h3⟩
    simp [finiteResponseForce_cubic_moments, h0, h1, h2, h3]

/-- The order-two Hankel section records precisely the three moments seen by quadratic response. -/
theorem atomicHankel_two_eq_iff_response_moments {n m : ℕ}
    (w z : Fin n → ℝ) (v t : Fin m → ℝ) :
    atomicHankel w z 2 = atomicHankel v t 2 ↔
      (RHTower.ccmAtomicMixedMoment w z 0 = RHTower.ccmAtomicMixedMoment v t 0 ∧
        RHTower.ccmAtomicMixedMoment w z 1 = RHTower.ccmAtomicMixedMoment v t 1 ∧
        RHTower.ccmAtomicMixedMoment w z 2 = RHTower.ccmAtomicMixedMoment v t 2) := by
  constructor
  · intro h
    exact ⟨congrFun (congrFun h 0) 0, congrFun (congrFun h 0) 1, congrFun (congrFun h 1) 1⟩
  · rintro ⟨h0, h1, h2⟩
    ext i j
    fin_cases i <;> fin_cases j <;> first | exact h0 | exact h1 | exact h2

/-- Three force readings identify an existing Hankel section without observing its entries. -/
theorem quadratic_response_three_probes_iff_hankel {n m : ℕ}
    (w z : Fin n → ℝ) (v t : Fin m → ℝ) :
    (finiteResponseForce (fun u => u ^ (2 : ℕ)) w z 0 = finiteResponseForce (fun u => u ^ (2 : ℕ)) v t 0 ∧
      finiteResponseForce (fun u => u ^ (2 : ℕ)) w z 1 = finiteResponseForce (fun u => u ^ (2 : ℕ)) v t 1 ∧
      finiteResponseForce (fun u => u ^ (2 : ℕ)) w z (-1) = finiteResponseForce (fun u => u ^ (2 : ℕ)) v t (-1)) ↔
        atomicHankel w z 2 = atomicHankel v t 2 :=
  (quadratic_response_three_probes_iff_moments w z v t).trans
    (atomicHankel_two_eq_iff_response_moments w z v t).symm

end
end GaloisForLFunctions.HTGeometry
