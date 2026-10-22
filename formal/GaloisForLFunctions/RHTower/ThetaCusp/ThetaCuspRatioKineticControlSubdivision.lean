import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticReducedDrift
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open Finset EvenCompactBernstein

theorem degreeElevationCoefficient_chain (n i j k : ℕ) (hi : i ≤ n) :
    degreeElevationCoefficient n j k*degreeElevationCoefficient n k i=
      degreeElevationCoefficient n j i*degreeElevationCoefficient i j k := by
  by_cases hjk : j ≤ k
  · by_cases hki : k ≤ i
    · have hji : j ≤ i := le_trans hjk hki
      simp only [degreeElevationCoefficient,hjk,hki,hji,if_true]
      have h := Nat.choose_mul (n:=n-j) (k:=i-j) (s:=k-j) (by omega)
      have hn : n-j-(k-j)=n-k := by omega
      have hi' : i-j-(k-j)=i-k := by omega
      rw [hn,hi'] at h
      exact_mod_cast h.symm
    · by_cases hji : j ≤ i
      · have hz : (i-j).choose (k-j)=0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [degreeElevationCoefficient,hjk,hki,hji,hz]
      · simp [degreeElevationCoefficient,hjk,hki,hji]
  · simp [degreeElevationCoefficient,hjk]

theorem degreeElevationCoefficient_weighted (n i j : ℕ) (hi : i ≤ n) (t : ℝ) :
    kineticBernstein i
      (fun k => degreeElevationCoefficient n j k*degreeElevationCoefficient n k i) t=
        degreeElevationCoefficient n j i*t^j := by
  by_cases hji : j ≤ i
  · simp only [kineticBernstein,degreeElevationCoefficient_chain n i j _ hi,mul_assoc,
      ←Finset.mul_sum]
    rw [monomial_bernstein_reconstruction i j hji]
  · have hzero (k : ℕ) (hk : k∈range (i+1)) : degreeElevationCoefficient n j k=0 := by
      have hjk : ¬j ≤ k := by have := mem_range.mp hk; omega
      simp [degreeElevationCoefficient,hjk]
    rw [kineticBernstein,Finset.sum_eq_zero (by
      intro k hk
      rw [hzero k hk,zero_mul,zero_mul])]
    simp [degreeElevationCoefficient,hji]

theorem kineticControl_contraction (n : ℕ) (a : ℕ → ℝ)
    (i : ℕ) (hi : i ≤ n) (t : ℝ) :
    kineticControl n (fun j => a j*t^j) i=
      kineticBernstein i (fun k => kineticControl n a k*degreeElevationCoefficient n k i) t := by
  symm
  unfold kineticBernstein kineticControl
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = a j*kineticBernstein i
        (fun k => degreeElevationCoefficient n j k*degreeElevationCoefficient n k i) t := by
      simp only [kineticBernstein,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [degreeElevationCoefficient_weighted n i j hi]
      ring

theorem reducedKineticControl_contraction (h v Z t : ℝ) (i : ℕ) (hi : i ≤ 19) :
    reducedKineticControl h v (t*Z) i=
      kineticBernstein i
        (fun k => reducedKineticControl h v Z k*degreeElevationCoefficient 19 k i) t := by
  unfold reducedKineticControl
  convert kineticControl_contraction 19
    (fun j => reducedKineticCoefficient h v j*Z^j) i hi t using 1
  congr 1
  funext j
  rw [mul_pow]
  ring

end
end HTGeometry.ThetaRatioKineticContraction
