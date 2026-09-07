import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomReflectedTwelve
import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomCompensationError

/-! # Complete two-atom error matrix for the compensated even rank-four source -/
namespace RHTower
noncomputable section

/-- The corrected even matrix of the two retained atoms, with its original normalization. -/
def thetaCuspTwoAtomEvenFourCompensated (C x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (-1 : ℝ)^(i.val+j.val)*thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x +
    if i.val = 3 ∧ j.val = 3 then C*thetaCuspTwoAtomCompensationSource x else 0

/-- Finite entry error including every reflected term and the whole correction error. -/
def thetaCuspEvenFourTwoAtomErrorMatrix (x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    (∑ k ∈ Finset.range (2*(i.val+j.val)+1), ((2*(i.val+j.val)).choose k : ℝ)*
      |thetaCuspFirstAtomReflectionJet k x| *
        thetaCuspTwoAtomReflectionErrorBoundTwelve (2*(i.val+j.val)-k) x) +
    if i.val = 3 ∧ j.val = 3 then 3000000000000*thetaCuspTwoAtomCompensationErrorBound x else 0

/-- The same complete entry error works for every coefficient in the proved rational band. -/
theorem abs_thetaCuspEvenFour_sub_two_entry_le {C x : ℝ}
    (hC : 1000000000000 ≤ C) (hCU : C ≤ 3000000000000)
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) (i j : Fin 4) :
    |thetaCuspNativeEvenFourCompensated C x i j-thetaCuspTwoAtomEvenFourCompensated C x i j| ≤
      thetaCuspEvenFourTwoAtomErrorMatrix x i j := by
  have hn : 2*(i.val+j.val) ≤ 12 := by omega
  have h := abs_thetaCuspNativeReflectionJet_sub_two_le_factored_twelve hn hq
  have hs : |(-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x-
      (-1 : ℝ)^(i.val+j.val)*thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x| ≤
      ∑ k ∈ Finset.range (2*(i.val+j.val)+1), ((2*(i.val+j.val)).choose k : ℝ)*
        |thetaCuspFirstAtomReflectionJet k x| *
          thetaCuspTwoAtomReflectionErrorBoundTwelve (2*(i.val+j.val)-k) x := by
    simpa only [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using h
  unfold thetaCuspNativeEvenFourCompensated thetaCuspTwoAtomEvenFourCompensated
    thetaCuspEvenFourTwoAtomErrorMatrix
  split_ifs with hh
  · have hc := abs_thetaCuspCenterCompensationSource_sub_two_mul_le hC hCU hq
    rw [show (-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x+
        C*thetaCuspCenterCompensationSource x-
        ((-1 : ℝ)^(i.val+j.val)*thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x+
          C*thetaCuspTwoAtomCompensationSource x) =
        ((-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x-
          (-1 : ℝ)^(i.val+j.val)*thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x)+
        (C*thetaCuspCenterCompensationSource x-C*thetaCuspTwoAtomCompensationSource x) by ring]
    exact (abs_add_le _ _).trans (add_le_add hs hc)
  · simpa only [add_zero] using hs

/-- Every quadratic comparison retains the entire entrywise error, including all off-diagonal terms. -/
theorem abs_thetaCuspEvenFour_sub_two_quadratic_le {C x : ℝ}
    (hC : 1000000000000 ≤ C) (hCU : C ≤ 3000000000000)
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) (v : Fin 4 → ℝ) :
    |∑ i, ∑ j, v i*(thetaCuspNativeEvenFourCompensated C x i j-
        thetaCuspTwoAtomEvenFourCompensated C x i j)*v j| ≤
      ∑ i, ∑ j, |v i| *thetaCuspEvenFourTwoAtomErrorMatrix x i j*|v j| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  simp only [abs_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (abs_thetaCuspEvenFour_sub_two_entry_le hC hCU hq i j)
      (abs_nonneg _)) (abs_nonneg _)

/-- Complete canonical quadratic error on the physical middle region, with no coefficient premise. -/
theorem abs_thetaCuspCanonicalEvenFour_sub_two_quadratic_le {x : ℝ}
    (hx : 8/95 ≤ x) (v : Fin 4 → ℝ) :
    |∑ i, ∑ j, v i*(thetaCuspNativeEvenFourCompensated
        thetaCuspNativeEvenCompensationCoefficient x i j-
      thetaCuspTwoAtomEvenFourCompensated thetaCuspNativeEvenCompensationCoefficient x i j)*v j| ≤
      ∑ i, ∑ j, |v i| *thetaCuspEvenFourTwoAtomErrorMatrix x i j*|v j| :=
  abs_thetaCuspEvenFour_sub_two_quadratic_le
    thetaCuspNativeEvenCompensationCoefficient_bounds.1.le
    thetaCuspNativeEvenCompensationCoefficient_bounds.2.le
    (thirtySevenTenths_le_firstAtomScale_of_energy_endpoint hx) v

/-- A fixed rational lower model uses the appropriate endpoint of the coefficient band. -/
def thetaCuspTwoAtomEvenFourLower (x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (-1 : ℝ)^(i.val+j.val)*thetaCuspTwoAtomReflectionJet (2*(i.val+j.val)) x +
    if i.val = 3 ∧ j.val = 3 then
      min (1000000000000*thetaCuspTwoAtomCompensationSource x)
        (3000000000000*thetaCuspTwoAtomCompensationSource x) else 0

/-- The rational endpoint model is below every retained corrected quadratic form in the band. -/
theorem thetaCuspTwoAtomEvenFourLower_quadratic_le {C x : ℝ}
    (hC : 1000000000000 ≤ C) (hCU : C ≤ 3000000000000) (v : Fin 4 → ℝ) :
    (∑ i, ∑ j, v i*thetaCuspTwoAtomEvenFourLower x i j*v j) ≤
      ∑ i, ∑ j, v i*thetaCuspTwoAtomEvenFourCompensated C x i j*v j := by
  have hc : min (1000000000000*thetaCuspTwoAtomCompensationSource x)
      (3000000000000*thetaCuspTwoAtomCompensationSource x) ≤
        C*thetaCuspTwoAtomCompensationSource x := by
    rcases le_total 0 (thetaCuspTwoAtomCompensationSource x) with hg | hg
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hC hg)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hCU hg)
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  unfold thetaCuspTwoAtomEvenFourLower thetaCuspTwoAtomEvenFourCompensated
  split_ifs with h
  · have hij : i = j := Fin.ext (h.1.trans h.2.symm)
    subst j
    have hm := mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg (v i))
    nlinarith only [hm]
  · exact le_rfl

/-- A finite rational two-atom expression minus the complete error bounds the actual canonical form. -/
theorem thetaCuspCanonicalEvenFour_quadratic_ge_twoAtomLower_sub_error {x : ℝ}
    (hx : 8/95 ≤ x) (v : Fin 4 → ℝ) :
    (∑ i, ∑ j, v i*thetaCuspTwoAtomEvenFourLower x i j*v j) -
        (∑ i, ∑ j, |v i| *thetaCuspEvenFourTwoAtomErrorMatrix x i j*|v j|) ≤
      ∑ i, ∑ j, v i*thetaCuspNativeEvenFourCompensated
        thetaCuspNativeEvenCompensationCoefficient x i j*v j := by
  have hl := thetaCuspTwoAtomEvenFourLower_quadratic_le
    thetaCuspNativeEvenCompensationCoefficient_bounds.1.le
    thetaCuspNativeEvenCompensationCoefficient_bounds.2.le (x := x) v
  have he := (abs_le.mp (abs_thetaCuspCanonicalEvenFour_sub_two_quadratic_le hx v)).1
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib] at he
  linarith only [hl, he]

end
end RHTower
