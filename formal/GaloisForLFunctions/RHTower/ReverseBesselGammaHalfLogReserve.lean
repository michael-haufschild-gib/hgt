import GaloisForLFunctions.RHTower.ReverseBesselFixedFrequencyBlindness
import GaloisForLFunctions.RHTower.SquaredXiChebyshevWindow
import GaloisForLFunctions.RHTower.RadialGramOffDiagonalDecay

/-!
# Square-root cutoff and half-log reserve for the reverse-Bessel Gamma cost

For the normalized squared-Xi reverse-Bessel coefficients, define the factorial-weighted order
`j + 1` cost

`A(n,j) = (b(n,j+1) / b(n,0)) * j!`.

Fixed-order coefficient convergence only gives the nonuniform majorant `A(n,j) ≤ 1/(j+1)`.
The exact adjacent reverse-Bessel recurrence contains substantially more moving-degree information:
each term controls its own decrement.  Telescoping from an arbitrary cutoff `r` gives

`sum_{r ≤ j < n} A(n,j) ≤ 2n/(r+1)^2`.

Taking `r = floor(sqrt n)` leaves a tail strictly below `2`, while the head costs only the
harmonic sum through `floor(sqrt n)`.  Consequently every positive degree `N` satisfies the
closed finite inequality

`sum_{j < N} A(N,j) ≤ 3 + (1/2) log N`.

This is a uniform moving-degree theorem; it does not follow from the corpus' fixed-frequency
reverse-Bessel limit.  It exposes a half-logarithmic reserve in the Gamma packet at the parabolic
source scale.
-/

open scoped BigOperators
open Finset

namespace RHTower

noncomputable section

/-- The factorial-weighted normalized coefficient with actual jet order `j+1`. -/
def reverseBesselGammaCostTerm (n j : ℕ) : ℝ :=
  reverseBesselRatio n (j + 1) * (j.factorial : ℝ)

/-- Full positive factorial-weighted Gamma-jet cost at degree `n`. -/
def reverseBesselGammaCost (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, reverseBesselGammaCostTerm n j

theorem reverseBesselRatio_nonneg_all (n j : ℕ) : 0 ≤ reverseBesselRatio n j := by
  rw [reverseBesselRatio]
  exact div_nonneg (by positivity) (weight_zero_pos n).le

theorem reverseBesselRatio_le_factorial_all (n j : ℕ) :
    reverseBesselRatio n j ≤ 1 / (j.factorial : ℝ) := by
  rcases le_or_gt j n with hj | hj
  · rw [reverseBesselRatio, div_le_iff₀ (weight_zero_pos n)]
    have hle := weight_le_div (n := n) (j := j) hj
    rw [show (1 : ℝ) / (j.factorial : ℝ) * (squaredRadialJetWeight n 0 : ℝ) =
        (squaredRadialJetWeight n 0 : ℝ) / (j.factorial : ℝ) by ring]
    exact hle
  · rw [reverseBesselRatio, squaredRadialJetWeight_eq_zero_of_lt n j hj]
    simp

theorem reverseBesselGammaCostTerm_nonneg (n j : ℕ) :
    0 ≤ reverseBesselGammaCostTerm n j := by
  exact mul_nonneg (reverseBesselRatio_nonneg_all n (j + 1)) (by positivity)

theorem reverseBesselGammaCostTerm_le_harmonic (n j : ℕ) :
    reverseBesselGammaCostTerm n j ≤ 1 / ((j : ℝ) + 1) := by
  have hratio := reverseBesselRatio_le_factorial_all n (j + 1)
  rw [reverseBesselGammaCostTerm]
  calc
    reverseBesselRatio n (j + 1) * (j.factorial : ℝ)
        ≤ (1 / ((j + 1).factorial : ℝ)) * (j.factorial : ℝ) := by
          gcongr
    _ = 1 / ((j : ℝ) + 1) := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp

theorem reverseBesselRatio_succ_eq {n j : ℕ} (hjn : j < n) :
    reverseBesselRatio n (j + 1) =
      reverseBesselRatio n j *
        (2 * ((n : ℝ) - j) / ((2 * (n : ℝ) - j) * ((j : ℝ) + 1))) := by
  have hrecQ := squaredRadialJetWeight_adjacent (n := n) (j := j) hjn
  have hrec :
      (squaredRadialJetWeight n (j + 1) : ℝ) * (2 * (n : ℝ) - j) * ((j : ℝ) + 1) =
        (squaredRadialJetWeight n j : ℝ) * (2 * ((n : ℝ) - j)) := by
    have hrecR :
        ((j : ℝ) + 1) * (squaredRadialJetWeight n (j + 1) : ℝ) *
            (2 * (n : ℝ) - j) =
          2 * ((n : ℝ) - j) * (squaredRadialJetWeight n j : ℝ) := by
      exact_mod_cast hrecQ
    linear_combination hrecR
  have h2n : 2 * (n : ℝ) - j ≠ 0 := by
    have hjR : (j : ℝ) < n := by exact_mod_cast hjn
    nlinarith
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have key : (squaredRadialJetWeight n (j + 1) : ℝ) =
      (squaredRadialJetWeight n j : ℝ) * (2 * ((n : ℝ) - j)) /
        ((2 * (n : ℝ) - j) * ((j : ℝ) + 1)) := by
    rw [eq_div_iff (mul_ne_zero h2n hj1)]
    linear_combination hrec
  rw [reverseBesselRatio, reverseBesselRatio, key]
  ring

theorem reverseBesselGammaCostTerm_succ_cleared {n j : ℕ} (hj : j + 1 < n) :
    (((j : ℝ) + 2) * (2 * (n : ℝ) - ((j : ℝ) + 1))) *
        reverseBesselGammaCostTerm n (j + 1) =
      (2 * ((j : ℝ) + 1) * ((n : ℝ) - ((j : ℝ) + 1))) *
        reverseBesselGammaCostTerm n j := by
  rw [reverseBesselGammaCostTerm, reverseBesselGammaCostTerm,
    reverseBesselRatio_succ_eq (n := n) (j := j + 1) hj, Nat.factorial_succ]
  push_cast
  have hden1 : 2 * (n : ℝ) - ((j : ℝ) + 1) ≠ 0 := by
    have hjR : (j : ℝ) + 1 < n := by exact_mod_cast hj
    nlinarith
  have hden2 : (j : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem reverseBesselGammaCostTerm_decrement {n j : ℕ} (hj : j + 1 < n) :
    (((j : ℝ) + 1) / (2 * (n : ℝ))) * reverseBesselGammaCostTerm n j ≤
      reverseBesselGammaCostTerm n j - reverseBesselGammaCostTerm n (j + 1) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hkn : (j : ℝ) + 1 < n := by exact_mod_cast hj
  have hrec := reverseBesselGammaCostTerm_succ_cleared (n := n) (j := j) hj
  have ht := reverseBesselGammaCostTerm_nonneg n j
  have h2nk : 0 < 2 * (n : ℝ) - ((j : ℝ) + 1) := by nlinarith
  have hden : 0 < ((j : ℝ) + 2) * (2 * (n : ℝ) - ((j : ℝ) + 1)) := by positivity
  have hnext : reverseBesselGammaCostTerm n (j + 1) =
      (2 * ((j : ℝ) + 1) * ((n : ℝ) - ((j : ℝ) + 1)) /
          (((j : ℝ) + 2) * (2 * (n : ℝ) - ((j : ℝ) + 1)))) *
        reverseBesselGammaCostTerm n j := by
    rw [show
      (2 * ((j : ℝ) + 1) * ((n : ℝ) - ((j : ℝ) + 1)) /
          (((j : ℝ) + 2) * (2 * (n : ℝ) - ((j : ℝ) + 1)))) *
        reverseBesselGammaCostTerm n j =
      (2 * ((j : ℝ) + 1) * ((n : ℝ) - ((j : ℝ) + 1)) *
        reverseBesselGammaCostTerm n j) /
          (((j : ℝ) + 2) * (2 * (n : ℝ) - ((j : ℝ) + 1))) by ring]
    rw [eq_div_iff hden.ne']
    linear_combination hrec
  have hscalar :
      ((j : ℝ) + 1) / (2 * (n : ℝ)) ≤
        1 - 2 * ((j : ℝ) + 1) * ((n : ℝ) - ((j : ℝ) + 1)) /
          (((j : ℝ) + 2) * (2 * (n : ℝ) - ((j : ℝ) + 1))) := by
    field_simp
    nlinarith [sq_nonneg ((j : ℝ) + 1)]
  rw [hnext]
  nlinarith [mul_le_mul_of_nonneg_right hscalar ht]

theorem reverseBesselGammaCostTerm_eq_zero_of_degree_le {n j : ℕ} (hj : n ≤ j) :
    reverseBesselGammaCostTerm n j = 0 := by
  rw [reverseBesselGammaCostTerm, reverseBesselRatio,
    squaredRadialJetWeight_eq_zero_of_lt n (j + 1) (by omega)]
  simp

theorem reverseBesselGammaCostTerm_decrement_all {n j : ℕ} (hj : j < n) :
    (((j : ℝ) + 1) / (2 * (n : ℝ))) * reverseBesselGammaCostTerm n j ≤
      reverseBesselGammaCostTerm n j - reverseBesselGammaCostTerm n (j + 1) := by
  by_cases hnext : j + 1 < n
  · exact reverseBesselGammaCostTerm_decrement hnext
  · have hjn : j + 1 = n := by omega
    have hz : reverseBesselGammaCostTerm n (j + 1) = 0 :=
      reverseBesselGammaCostTerm_eq_zero_of_degree_le (by omega)
    rw [hz, sub_zero]
    have ht := reverseBesselGammaCostTerm_nonneg n j
    have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hjcast : (j : ℝ) + 1 = n := by exact_mod_cast hjn
    rw [hjcast]
    have hhalf : (n : ℝ) / (2 * (n : ℝ)) = 1 / 2 := by field_simp
    rw [hhalf]
    nlinarith

/-- Telescoping tail law: after any positive index cutoff `r+1`, the remaining factorial-weighted
reverse-Bessel Gamma cost is at most `2n/(r+1)^2`. -/
theorem sum_Ico_reverseBesselGammaCostTerm_le {n r : ℕ} (hr : r < n) :
    ∑ j ∈ Finset.Ico r n, reverseBesselGammaCostTerm n j ≤
      2 * (n : ℝ) / (((r : ℝ) + 1) ^ 2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : 0 < ((r : ℝ) + 1) / (2 * (n : ℝ)) := by positivity
  have hpoint : ∀ j ∈ Finset.Ico r n,
      (((r : ℝ) + 1) / (2 * (n : ℝ))) * reverseBesselGammaCostTerm n j ≤
        reverseBesselGammaCostTerm n j - reverseBesselGammaCostTerm n (j + 1) := by
    intro j hj
    have hrj : r ≤ j := (Finset.mem_Ico.mp hj).1
    have hjn : j < n := (Finset.mem_Ico.mp hj).2
    have hdec := reverseBesselGammaCostTerm_decrement_all (n := n) (j := j) hjn
    have hcoef : ((r : ℝ) + 1) / (2 * (n : ℝ)) ≤
        ((j : ℝ) + 1) / (2 * (n : ℝ)) := by
      gcongr
    exact le_trans (mul_le_mul_of_nonneg_right hcoef
      (reverseBesselGammaCostTerm_nonneg n j)) hdec
  have hsum := Finset.sum_le_sum hpoint
  have htel :
      (∑ j ∈ Finset.Ico r n,
        (reverseBesselGammaCostTerm n j - reverseBesselGammaCostTerm n (j + 1))) =
        reverseBesselGammaCostTerm n r - reverseBesselGammaCostTerm n n := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_assoc]
    rw [Finset.sum_range_sub'
      (fun i => reverseBesselGammaCostTerm n (r + i)) (n - r), Nat.add_zero,
      show r + (n - r) = n by omega]
  have hzero : reverseBesselGammaCostTerm n n = 0 :=
    reverseBesselGammaCostTerm_eq_zero_of_degree_le (le_refl n)
  rw [← Finset.mul_sum, htel, hzero, sub_zero] at hsum
  have hscale : 0 ≤ 2 * (n : ℝ) / ((r : ℝ) + 1) := by positivity
  have htail :
      ∑ j ∈ Finset.Ico r n, reverseBesselGammaCostTerm n j ≤
        (2 * (n : ℝ) / ((r : ℝ) + 1)) * reverseBesselGammaCostTerm n r := by
    calc
      ∑ j ∈ Finset.Ico r n, reverseBesselGammaCostTerm n j =
          (2 * (n : ℝ) / ((r : ℝ) + 1)) *
            ((((r : ℝ) + 1) / (2 * (n : ℝ))) *
              ∑ j ∈ Finset.Ico r n, reverseBesselGammaCostTerm n j) := by
                field_simp
      _ ≤ (2 * (n : ℝ) / ((r : ℝ) + 1)) *
          reverseBesselGammaCostTerm n r := mul_le_mul_of_nonneg_left hsum hscale
  calc
    ∑ j ∈ Finset.Ico r n, reverseBesselGammaCostTerm n j
        ≤ (2 * (n : ℝ) / ((r : ℝ) + 1)) *
          reverseBesselGammaCostTerm n r := htail
    _ ≤ (2 * (n : ℝ) / ((r : ℝ) + 1)) * (1 / ((r : ℝ) + 1)) := by
      gcongr
      exact reverseBesselGammaCostTerm_le_harmonic n r
    _ = 2 * (n : ℝ) / (((r : ℝ) + 1) ^ 2) := by
      field_simp

/-- Square-root cutoff: the full factorial-weighted reverse-Bessel Gamma cost consists of a
harmonic head through `floor(sqrt n)` and a uniformly bounded tail. -/
theorem reverseBesselGammaCost_le_sqrt_harmonic_add_two (n : ℕ) :
    reverseBesselGammaCost n ≤ radialHarmonicSum (Nat.sqrt n) + 2 := by
  let r := Nat.sqrt n
  change reverseBesselGammaCost n ≤ radialHarmonicSum r + 2
  have hrn : r ≤ n := Nat.sqrt_le_self n
  have hhead :
      ∑ j ∈ Finset.range r, reverseBesselGammaCostTerm n j ≤ radialHarmonicSum r := by
    rw [radialHarmonicSum]
    apply Finset.sum_le_sum
    intro j hj
    exact reverseBesselGammaCostTerm_le_harmonic n j
  by_cases hr : r < n
  · have htail := sum_Ico_reverseBesselGammaCostTerm_le (n := n) (r := r) hr
    have hsqrtNat : n < (r + 1) ^ 2 := by
      rw [pow_two]
      simpa [r, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt n
    have hsqrtReal : (n : ℝ) < ((r : ℝ) + 1) ^ 2 := by exact_mod_cast hsqrtNat
    have htailTwo :
        ∑ j ∈ Finset.Ico r n, reverseBesselGammaCostTerm n j < 2 := by
      refine lt_of_le_of_lt htail ?_
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ((r : ℝ) + 1) ^ 2)]
      nlinarith
    rw [reverseBesselGammaCost]
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun j => reverseBesselGammaCostTerm n j) hrn
    rw [← hsplit]
    linarith
  · have hre : r = n := by omega
    calc
      reverseBesselGammaCost n =
          ∑ j ∈ Finset.range n, reverseBesselGammaCostTerm n j := rfl
      _ = ∑ j ∈ Finset.range r, reverseBesselGammaCostTerm n j := by rw [hre]
      _ ≤ radialHarmonicSum r := hhead
      _ ≤ radialHarmonicSum r + 2 := by linarith

/-- **Half-log reserve.** At every positive degree, the factorial-weighted normalized Gamma-jet
cost uses at most half the logarithmic degree scale, up to the absolute constant `3`. -/
theorem reverseBesselGammaCost_le_halfLogReserve (n : ℕ) :
    reverseBesselGammaCost (n + 1) ≤
      3 + (1 / 2 : ℝ) * Real.log (n + 1 : ℕ) := by
  let N := n + 1
  let r := Nat.sqrt N
  have hN : 1 ≤ N := by omega
  have hr : 1 ≤ r := by
    exact Nat.sqrt_pos.2 (by omega : 0 < N)
  have hcost := reverseBesselGammaCost_le_sqrt_harmonic_add_two N
  change reverseBesselGammaCost N ≤ radialHarmonicSum r + 2 at hcost
  have hharm := radialHarmonicSum_le_one_add_log hr
  have hsquareNat : r ^ 2 ≤ N := by
    simpa [pow_two, r, N] using Nat.sqrt_le N
  have hsquareReal : ((r : ℝ) ^ 2) ≤ (N : ℝ) := by exact_mod_cast hsquareNat
  have hlog : Real.log ((r : ℝ) ^ 2) ≤ Real.log (N : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (show (r : ℝ) ^ 2 ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; positivity)
      (show (N : ℝ) ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; positivity)
      hsquareReal
  rw [Real.log_pow] at hlog
  change reverseBesselGammaCost N ≤ 3 + (1 / 2 : ℝ) * Real.log (N : ℝ)
  norm_num at hlog ⊢
  nlinarith

end

end RHTower
