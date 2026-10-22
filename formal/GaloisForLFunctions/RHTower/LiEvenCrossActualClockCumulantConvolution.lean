import GaloisForLFunctions.RHTower.PrimeArchThetaAllOrderCumulant
/-!
# The signed factorial convolution of the actual theta cumulants

Parity extraction from the all-order central source identity gives the exact finite coefficient
law needed for the clock Volterra equation. The normalized raw theta moments retain their
literal zeroth raw-source normalization throughout.
-/

open scoped BigOperators
namespace RHTower
noncomputable section
lemma sum_range_two (f : ℕ → ℂ) (n : ℕ) :
    ∑ i ∈ Finset.range (2*n), f i = ∑ j ∈ Finset.range n, (f (2*j) + f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring
private lemma xiJet_even (n : ℕ) :
    thetaCuspXiJet (2*n) = (((-1:ℝ)^n * thetaCuspRawEvenMoment n : ℝ):ℂ) := by
  simp [thetaCuspXiJet, show Even (2*n) from ⟨n, by omega⟩]
private lemma productJet_even (n : ℕ) : thetaCuspPrimeArchProductJet (2*n) = 0 := by
  simp [thetaCuspPrimeArchProductJet, Nat.not_odd_iff_even.mpr (show Even (2*n) from ⟨n, by omega⟩)]
private lemma productJet_odd (n : ℕ) : thetaCuspPrimeArchProductJet (2*n+1) =
    ((2*n+1).factorial : ℂ) * (normalizedPrimeArchMoment n : ℂ) := by
  simp [thetaCuspPrimeArchProductJet, show Odd (2*n+1) from ⟨n, by omega⟩]
private lemma raw_recurrence (n : ℕ) :
    (-1:ℝ)^(n+1)*thetaCuspRawEvenMoment (n+1) +
      ∑ j ∈ Finset.range (n+1),
        (((2*n+1).choose (2*j+1):ℝ) * ((2*j+1).factorial:ℝ) *
          normalizedPrimeArchMoment j * (-1:ℝ)^(n-j) * thetaCuspRawEvenMoment (n-j)) = 0 := by
  have h := thetaCusp_allOrderCumulantRecurrence (2*n+1)
  rw [show 2*n+1+1=2*(n+1) by omega, xiJet_even,
    sum_range_two] at h
  have hs : ∑ j ∈ Finset.range (n+1),
      ((↑((2*n+1).choose (2*j)) : ℂ) * thetaCuspPrimeArchProductJet (2*j) *
          thetaCuspXiJet (2*n+1-2*j) +
        (↑((2*n+1).choose (2*j+1)) : ℂ) * thetaCuspPrimeArchProductJet (2*j+1) *
          thetaCuspXiJet (2*n+1-(2*j+1))) =
      ((∑ j ∈ Finset.range (n+1),
        (((2*n+1).choose (2*j+1):ℝ) * ((2*j+1).factorial:ℝ) *
          normalizedPrimeArchMoment j * (-1:ℝ)^(n-j) * thetaCuspRawEvenMoment (n-j)):ℝ):ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
    rw [productJet_even, productJet_odd, show 2*n-2*j=2*(n-j) by omega,
      xiJet_even]
    push_cast
    ring
  rw [hs] at h
  exact_mod_cast h
/-- Exact normalized factorial recurrence for every actual prime--archimedean source moment. -/
theorem liEvenCrossActualClock_signedCumulantConvolution (n : ℕ) :
    ∑ j ∈ Finset.range (n+1),
      (-1:ℝ)^j * normalizedPrimeArchMoment j * thetaCuspNormalizedEvenMoment (n-j) /
        ((2*(n-j)).factorial:ℝ) =
      (2*n+2:ℝ) * thetaCuspNormalizedEvenMoment (n+1) /
        ((2*n+2).factorial:ℝ) := by
  have h := raw_recurrence n
  have hfact : (((2*n+1).factorial:ℕ):ℝ) ≠ 0 := by positivity
  have hR : thetaCuspRawEvenMoment 0 ≠ 0 := ne_of_gt thetaCuspRawEvenMoment_zero_pos
  have hsign : (-1:ℝ)^n ≠ 0 := by positivity
  have hs : (∑ j ∈ Finset.range (n+1),
        (((2*n+1).choose (2*j+1):ℝ) * ((2*j+1).factorial:ℝ) *
          normalizedPrimeArchMoment j * (-1:ℝ)^(n-j) * thetaCuspRawEvenMoment (n-j))) =
      (-1:ℝ)^n * ((2*n+1).factorial:ℝ) * thetaCuspRawEvenMoment 0 *
        (∑ j ∈ Finset.range (n+1),
          (-1:ℝ)^j * normalizedPrimeArchMoment j * thetaCuspNormalizedEvenMoment (n-j) /
            ((2*(n-j)).factorial:ℝ)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
    have hk : 2*j+1 ≤ 2*n+1 := by omega
    have hc := Nat.choose_mul_factorial_mul_factorial hk
    have hc' : ((2*n+1).choose (2*j+1):ℝ) * ((2*j+1).factorial:ℝ) *
        ((2*(n-j)).factorial:ℝ) = ((2*n+1).factorial:ℝ) := by
      rw [show 2*n+1-(2*j+1)=2*(n-j) by omega] at hc
      exact_mod_cast hc
    have hf : ((2*(n-j)).factorial:ℝ) ≠ 0 := by positivity
    have hc'' : ((2*n+1).choose (2*j+1):ℝ) * ((2*j+1).factorial:ℝ) =
        ((2*n+1).factorial:ℝ) / ((2*(n-j)).factorial:ℝ) :=
      (eq_div_iff hf).mpr hc'
    have hsg : (-1:ℝ)^(n-j) = (-1:ℝ)^n * (-1:ℝ)^j := by
      rw [← pow_add, show n+j=2*j+(n-j) by omega, pow_add, pow_mul]
      norm_num
    rw [hc'', hsg, thetaCuspNormalizedEvenMoment]
    field_simp
  rw [hs, pow_succ] at h
  have hfnext : ((2*n+2).factorial:ℝ) = (2*n+2:ℝ)*((2*n+1).factorial:ℝ) := by
    rw [show 2*n+2= (2*n+1)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hh : ((2*n+1).factorial:ℝ) * thetaCuspRawEvenMoment 0 *
      (∑ j ∈ Finset.range (n+1),
        (-1:ℝ)^j * normalizedPrimeArchMoment j * thetaCuspNormalizedEvenMoment (n-j) /
          ((2*(n-j)).factorial:ℝ)) = thetaCuspRawEvenMoment (n+1) := by
    apply (mul_left_cancel₀ hsign)
    linear_combination h
  rw [hfnext, thetaCuspNormalizedEvenMoment]
  field_simp [hR, hfact]
  linear_combination hh
end
end RHTower
