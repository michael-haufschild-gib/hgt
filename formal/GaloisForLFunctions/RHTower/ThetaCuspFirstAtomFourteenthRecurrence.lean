import GaloisForLFunctions.RHTower.ThetaCuspOddFourGaussianFlow

/-!
# Literal fourteenth first-atom reflection recurrence

The odd-four successor uses the fourteenth reflected derivative of the actual
first theta atom.  This finite triangular identity retains every lower even
affine and Gaussian jet; it has no Gaussian-limit replacement.
-/

namespace RHTower.ThetaCuspOddFour
noncomputable section

private theorem sinh_two_jet_even_zero (k : ℕ) :
    iteratedDeriv (2*k) (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sinh 2]
  rw [Real.iteratedDeriv_even_sinh]
  simp

private theorem sinh_two_jet_odd (k : ℕ) :
    iteratedDeriv (2*k+1) (fun t : ℝ => Real.sinh (2*t)) 0 =
      (2 : ℝ)^(2*k+1) := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sinh 2]
  rw [Real.iteratedDeriv_odd_sinh]
  simp

/-- Exact order-fourteen triangular recurrence, retaining all seven lower even jets. -/
theorem affine_jet_fourteen (q B : ℝ) :
    let J (n : ℕ) := iteratedDeriv n
      (fun t : ℝ => affine q B t+6*gaussian q t) 0
    iteratedDeriv 14 (affine q B) 0 =
      -4*q*(26*J 12+2288*J 10+41184*J 8+219648*J 6+
        366080*J 4+159744*J 2+8192*J 0) := by
  dsimp only
  have h := affine_jet_succ q B 13
  have hs0 : iteratedDeriv 0 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_jet_even_zero 0
  have hs2 : iteratedDeriv 2 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_jet_even_zero 1
  have hs4 : iteratedDeriv 4 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_jet_even_zero 2
  have hs6 : iteratedDeriv 6 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_jet_even_zero 3
  have hs8 : iteratedDeriv 8 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_jet_even_zero 4
  have hs10 : iteratedDeriv 10 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_jet_even_zero 5
  have hs12 : iteratedDeriv 12 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_jet_even_zero 6
  have hs1 : iteratedDeriv 1 (fun t : ℝ => Real.sinh (2*t)) 0 = 2 := by
    convert sinh_two_jet_odd 0 using 1; norm_num
  have hs3 : iteratedDeriv 3 (fun t : ℝ => Real.sinh (2*t)) 0 = 8 := by
    convert sinh_two_jet_odd 1 using 1; norm_num
  have hs5 : iteratedDeriv 5 (fun t : ℝ => Real.sinh (2*t)) 0 = 32 := by
    convert sinh_two_jet_odd 2 using 1; norm_num
  have hs7 : iteratedDeriv 7 (fun t : ℝ => Real.sinh (2*t)) 0 = 128 := by
    convert sinh_two_jet_odd 3 using 1; norm_num
  have hs9 : iteratedDeriv 9 (fun t : ℝ => Real.sinh (2*t)) 0 = 512 := by
    convert sinh_two_jet_odd 4 using 1; norm_num
  have hs11 : iteratedDeriv 11 (fun t : ℝ => Real.sinh (2*t)) 0 = 2048 := by
    convert sinh_two_jet_odd 5 using 1; norm_num
  have hs13 : iteratedDeriv 13 (fun t : ℝ => Real.sinh (2*t)) 0 = 8192 := by
    convert sinh_two_jet_odd 6 using 1; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9,
    hs10, hs11, hs12, hs13] at h
  norm_num [Nat.choose] at h
  simp only [iteratedDeriv_zero] at h ⊢
  convert h using 1; ring

/-- The literal `(1,1)` theta reflection fourteenth jet obeys the same recurrence. -/
theorem firstAtomReflectionJet_fourteen (x : ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let J (n : ℕ) := iteratedDeriv n
      (fun t : ℝ => affine q ((2*q-3)^(2 : ℕ)) t+6*gaussian q t) 0
    thetaCuspFirstAtomReflectionJet 14 x =
      -16*q^(3 : ℕ)*Real.exp (x-2*q)*
        (26*J 12+2288*J 10+41184*J 8+219648*J 6+
          366080*J 4+159744*J 2+8192*J 0) := by
  dsimp only
  set q := thetaCuspSingleAtomReflectionScale 1 x
  have hfun : (fun t : ℝ =>
      thetaCuspSourceTerm (x+t) 1*thetaCuspSourceTerm (x-t) 1) =
      fun t => (4*q^(2 : ℕ)*Real.exp (x-2*q))*
        affine q ((2*q-3)^(2 : ℕ)) t := by
    funext t
    simpa [q] using firstAtomPair_eq_affine x t
  unfold thetaCuspFirstAtomReflectionJet
  rw [hfun, iteratedDeriv_const_mul_field]
  rw [affine_jet_fourteen]
  ring

end
end RHTower.ThetaCuspOddFour
