import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourGaussianFlow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Gaussian companion jets at the fourteenth source order

The exact Gaussian flow behind the literal first-atom affine profile has
polynomial even jets through order twelve.  Their common q⁻⁸ scale vanishes,
so they cannot replace or cancel the leading twelfth affine jet in the
fourteenth first-atom recurrence.
-/

namespace RHTower.ThetaCuspOddFour
noncomputable section

/-- The companion Gaussian flow has the same finite convolution but no affine coupling. -/
theorem gaussian_jet_succ (q : ℝ) (n : ℕ) :
    iteratedDeriv (n+1) (gaussian q) 0 =
      -4*q * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        iteratedDeriv i (fun t : ℝ => Real.sinh (2*t)) 0 *
          iteratedDeriv (n-i) (gaussian q) 0 := by
  have hfun : deriv (gaussian q) = fun t =>
      -4*q*Real.sinh (2*t)*gaussian q t :=
    funext fun t => (gaussian_hasDerivAt q t).deriv
  have hs : ContDiffAt ℝ n (fun t : ℝ => Real.sinh (2*t)) 0 := by fun_prop
  have hg : ContDiffAt ℝ n (gaussian q) 0 := by
    change ContDiffAt ℝ n
      (fun t : ℝ => Real.exp (-2*q*(Real.cosh (2*t)-1))) 0
    fun_prop
  rw [iteratedDeriv_succ', hfun]
  conv_lhs =>
    arg 2
    ext t
    rw [show -4*q*Real.sinh (2*t)*gaussian q t =
        (-4*q)*(Real.sinh (2*t)*gaussian q t) by ring]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_mul hs hg]

private theorem sinh_two_even (k : ℕ) :
    iteratedDeriv (2*k) (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sinh 2]
  rw [Real.iteratedDeriv_even_sinh]
  simp

private theorem sinh_two_odd (k : ℕ) :
    iteratedDeriv (2*k+1) (fun t : ℝ => Real.sinh (2*t)) 0 =
      (2 : ℝ)^(2*k+1) := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_sinh 2]
  rw [Real.iteratedDeriv_odd_sinh]
  simp

private def g0 (_q : ℝ) : ℝ := 1
private def g1 (q : ℝ) : ℝ := 8*q
private def g2 (q : ℝ) : ℝ := 4*q*(6*g1 q-8*g0 q)
private def g3 (q : ℝ) : ℝ := 4*q*(10*g2 q-80*g1 q+32*g0 q)
private def g4 (q : ℝ) : ℝ := 4*q*(14*g3 q-280*g2 q+672*g1 q-128*g0 q)
private def g5 (q : ℝ) : ℝ :=
  4*q*(18*g4 q-672*g3 q+4032*g2 q-4608*g1 q+512*g0 q)
private def g6 (q : ℝ) : ℝ :=
  4*q*(22*g5 q-1320*g4 q+14784*g3 q-42240*g2 q+28160*g1 q-2048*g0 q)

private theorem gaussian_even_zero (q : ℝ) :
    iteratedDeriv 0 (gaussian q) 0 = g0 q := by
  simp [g0, gaussian]

private theorem gaussian_even_two (q : ℝ) :
    iteratedDeriv 2 (gaussian q) 0 = -g1 q := by
  have h := gaussian_jet_succ q 1
  have hs0 := sinh_two_even 0
  have hs1 : iteratedDeriv 1 (fun t : ℝ => Real.sinh (2*t)) 0 = 2 := by
    convert sinh_two_odd 0 using 1; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hs0, hs1] at h
  norm_num [Nat.choose] at h
  have hg0 : gaussian q 0 = 1 := by simp [gaussian]
  rw [hg0] at h
  dsimp [g0, g1] at *
  linarith only [h]

private theorem gaussian_even_four (q : ℝ) :
    iteratedDeriv 4 (gaussian q) 0 = g2 q := by
  have h := gaussian_jet_succ q 3
  have hs0 := sinh_two_even 0
  have hs2 : iteratedDeriv 2 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 1
  have hs1 : iteratedDeriv 1 (fun t : ℝ => Real.sinh (2*t)) 0 = 2 := by
    convert sinh_two_odd 0 using 1; norm_num
  have hs3 : iteratedDeriv 3 (fun t : ℝ => Real.sinh (2*t)) 0 = 8 := by
    convert sinh_two_odd 1 using 1; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    hs0, hs1, hs2, hs3] at h
  norm_num [Nat.choose] at h
  have hg0 : gaussian q 0 = 1 := by simp [gaussian]
  rw [hg0, gaussian_even_two] at h
  rw [h]
  dsimp [g0, g1, g2]
  ring

private theorem gaussian_even_six (q : ℝ) :
    iteratedDeriv 6 (gaussian q) 0 = -g3 q := by
  have h := gaussian_jet_succ q 5
  have hs0 := sinh_two_even 0
  have hs2 : iteratedDeriv 2 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 1
  have hs4 : iteratedDeriv 4 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 2
  have hs1 : iteratedDeriv 1 (fun t : ℝ => Real.sinh (2*t)) 0 = 2 := by
    convert sinh_two_odd 0 using 1; norm_num
  have hs3 : iteratedDeriv 3 (fun t : ℝ => Real.sinh (2*t)) 0 = 8 := by
    convert sinh_two_odd 1 using 1; norm_num
  have hs5 : iteratedDeriv 5 (fun t : ℝ => Real.sinh (2*t)) 0 = 32 := by
    convert sinh_two_odd 2 using 1; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    hs0, hs1, hs2, hs3, hs4, hs5] at h
  norm_num [Nat.choose] at h
  have hg0 : gaussian q 0 = 1 := by simp [gaussian]
  rw [hg0, gaussian_even_two, gaussian_even_four] at h
  rw [h]
  dsimp [g0, g1, g2, g3]
  ring

private theorem gaussian_even_eight (q : ℝ) :
    iteratedDeriv 8 (gaussian q) 0 = g4 q := by
  have h := gaussian_jet_succ q 7
  have hs0 := sinh_two_even 0
  have hs2 : iteratedDeriv 2 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 1
  have hs4 : iteratedDeriv 4 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 2
  have hs6 : iteratedDeriv 6 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 3
  have hs1 : iteratedDeriv 1 (fun t : ℝ => Real.sinh (2*t)) 0 = 2 := by
    convert sinh_two_odd 0 using 1; norm_num
  have hs3 : iteratedDeriv 3 (fun t : ℝ => Real.sinh (2*t)) 0 = 8 := by
    convert sinh_two_odd 1 using 1; norm_num
  have hs5 : iteratedDeriv 5 (fun t : ℝ => Real.sinh (2*t)) 0 = 32 := by
    convert sinh_two_odd 2 using 1; norm_num
  have hs7 : iteratedDeriv 7 (fun t : ℝ => Real.sinh (2*t)) 0 = 128 := by
    convert sinh_two_odd 3 using 1; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at h
  norm_num [Nat.choose] at h
  have hg0 : gaussian q 0 = 1 := by simp [gaussian]
  rw [hg0, gaussian_even_two, gaussian_even_four, gaussian_even_six] at h
  rw [h]
  dsimp [g0, g1, g2, g3, g4]
  ring

private theorem gaussian_even_ten (q : ℝ) :
    iteratedDeriv 10 (gaussian q) 0 = -g5 q := by
  have h := gaussian_jet_succ q 9
  have hs0 := sinh_two_even 0
  have hs2 : iteratedDeriv 2 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 1
  have hs4 : iteratedDeriv 4 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 2
  have hs6 : iteratedDeriv 6 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 3
  have hs8 : iteratedDeriv 8 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 4
  have hs1 : iteratedDeriv 1 (fun t : ℝ => Real.sinh (2*t)) 0 = 2 := by
    convert sinh_two_odd 0 using 1; norm_num
  have hs3 : iteratedDeriv 3 (fun t : ℝ => Real.sinh (2*t)) 0 = 8 := by
    convert sinh_two_odd 1 using 1; norm_num
  have hs5 : iteratedDeriv 5 (fun t : ℝ => Real.sinh (2*t)) 0 = 32 := by
    convert sinh_two_odd 2 using 1; norm_num
  have hs7 : iteratedDeriv 7 (fun t : ℝ => Real.sinh (2*t)) 0 = 128 := by
    convert sinh_two_odd 3 using 1; norm_num
  have hs9 : iteratedDeriv 9 (fun t : ℝ => Real.sinh (2*t)) 0 = 512 := by
    convert sinh_two_odd 4 using 1; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9] at h
  norm_num [Nat.choose] at h
  have hg0 : gaussian q 0 = 1 := by simp [gaussian]
  rw [hg0, gaussian_even_two, gaussian_even_four, gaussian_even_six,
    gaussian_even_eight] at h
  rw [h]
  dsimp [g0, g1, g2, g3, g4, g5]
  ring

private theorem gaussian_even_twelve (q : ℝ) :
    iteratedDeriv 12 (gaussian q) 0 = g6 q := by
  have h := gaussian_jet_succ q 11
  have hs0 := sinh_two_even 0
  have hs2 : iteratedDeriv 2 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 1
  have hs4 : iteratedDeriv 4 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 2
  have hs6 : iteratedDeriv 6 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 3
  have hs8 : iteratedDeriv 8 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 4
  have hs10 : iteratedDeriv 10 (fun t : ℝ => Real.sinh (2*t)) 0 = 0 := by
    simpa using sinh_two_even 5
  have hs1 : iteratedDeriv 1 (fun t : ℝ => Real.sinh (2*t)) 0 = 2 := by
    convert sinh_two_odd 0 using 1; norm_num
  have hs3 : iteratedDeriv 3 (fun t : ℝ => Real.sinh (2*t)) 0 = 8 := by
    convert sinh_two_odd 1 using 1; norm_num
  have hs5 : iteratedDeriv 5 (fun t : ℝ => Real.sinh (2*t)) 0 = 32 := by
    convert sinh_two_odd 2 using 1; norm_num
  have hs7 : iteratedDeriv 7 (fun t : ℝ => Real.sinh (2*t)) 0 = 128 := by
    convert sinh_two_odd 3 using 1; norm_num
  have hs9 : iteratedDeriv 9 (fun t : ℝ => Real.sinh (2*t)) 0 = 512 := by
    convert sinh_two_odd 4 using 1; norm_num
  have hs11 : iteratedDeriv 11 (fun t : ℝ => Real.sinh (2*t)) 0 = 2048 := by
    convert sinh_two_odd 5 using 1; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11] at h
  norm_num [Nat.choose] at h
  have hg0 : gaussian q 0 = 1 := by simp [gaussian]
  rw [hg0, gaussian_even_two, gaussian_even_four, gaussian_even_six,
    gaussian_even_eight, gaussian_even_ten] at h
  rw [h]
  dsimp [g0, g1, g2, g3, g4, g5, g6]
  ring

private def h0 (_u : ℝ) : ℝ := 1
private def h1 (_u : ℝ) : ℝ := 8
private def h2 (u : ℝ) : ℝ := 4*(6*h1 u-8*u*h0 u)
private def h3 (u : ℝ) : ℝ := 4*(10*h2 u-80*u*h1 u+32*u^2*h0 u)
private def h4 (u : ℝ) : ℝ :=
  4*(14*h3 u-280*u*h2 u+672*u^2*h1 u-128*u^3*h0 u)
private def h5 (u : ℝ) : ℝ :=
  4*(18*h4 u-672*u*h3 u+4032*u^2*h2 u-4608*u^3*h1 u+512*u^4*h0 u)
private def h6 (u : ℝ) : ℝ :=
  4*(22*h5 u-1320*u*h4 u+14784*u^2*h3 u-42240*u^3*h2 u+
    28160*u^4*h1 u-2048*u^5*h0 u)

private theorem g0_scale {q : ℝ} (_hq : q ≠ 0) : g0 q = q^0*h0 q⁻¹ := by
  simp [g0, h0]

private theorem g1_scale {q : ℝ} (_hq : q ≠ 0) : g1 q = q^1*h1 q⁻¹ := by
  simp [g1, h1]
  ring

private theorem g2_scale {q : ℝ} (hq : q ≠ 0) : g2 q = q^2*h2 q⁻¹ := by
  dsimp only [g2, h2]
  rw [g1_scale hq, g0_scale hq]
  field_simp [hq]

private theorem g3_scale {q : ℝ} (hq : q ≠ 0) : g3 q = q^3*h3 q⁻¹ := by
  dsimp only [g3, h3]
  rw [g2_scale hq, g1_scale hq, g0_scale hq]
  field_simp [hq]

private theorem g4_scale {q : ℝ} (hq : q ≠ 0) : g4 q = q^4*h4 q⁻¹ := by
  dsimp only [g4, h4]
  rw [g3_scale hq, g2_scale hq, g1_scale hq, g0_scale hq]
  field_simp [hq]

private theorem g5_scale {q : ℝ} (hq : q ≠ 0) : g5 q = q^5*h5 q⁻¹ := by
  dsimp only [g5, h5]
  rw [g4_scale hq, g3_scale hq, g2_scale hq, g1_scale hq, g0_scale hq]
  field_simp [hq]

private theorem g6_scale {q : ℝ} (hq : q ≠ 0) : g6 q = q^6*h6 q⁻¹ := by
  dsimp only [g6, h6]
  rw [g5_scale hq, g4_scale hq, g3_scale hq, g2_scale hq,
    g1_scale hq, g0_scale hq]
  field_simp [hq]

private theorem scaled_polynomial_vanishes (m k : ℕ) (hk : 0 < k)
    (g h : ℝ → ℝ) (hc : ContinuousAt h 0)
    (hscale : ∀ q : ℝ, q ≠ 0 → g q = q^m*h q⁻¹) :
    Filter.Tendsto (fun q : ℝ => g q/q^(m+k)) Filter.atTop (nhds 0) := by
  have hc' : ContinuousAt (fun u : ℝ => u^k*h u) 0 :=
    (continuousAt_id.pow k).mul hc
  have hlim := hc'.tendsto.comp (tendsto_inv_atTop_zero :
    Filter.Tendsto (fun q : ℝ => q⁻¹) Filter.atTop (nhds 0))
  have hzero : (0 : ℝ)^k*h 0 = 0 := by simp [hk.ne']
  rw [hzero] at hlim
  apply hlim.congr'
  filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with q hq
  rw [hscale q hq, pow_add]
  dsimp only [Function.comp_apply]
  field_simp [hq]
  have hpow : (1/q)^k*q^k = (1 : ℝ) := by
    rw [← mul_pow]
    field_simp [hq]
    simp
  calc
    (1/q)^k*h (1/q)*q^k = ((1/q)^k*q^k)*h (1/q) := by ring
    _ = h (1/q) := by rw [hpow]; ring

theorem gaussian_twelve_scaled_eight_tendsto_zero :
    Filter.Tendsto (fun q : ℝ => iteratedDeriv 12 (gaussian q) 0 / q^8)
      Filter.atTop (nhds 0) := by
  have hc : ContinuousAt h6 0 := by
    change ContinuousAt (fun u : ℝ => h6 u) 0
    dsimp [h6, h5, h4, h3, h2, h1, h0]
    fun_prop
  simpa only [gaussian_even_twelve] using
    scaled_polynomial_vanishes 6 2 (by omega) g6 h6 hc
      (fun q hq => g6_scale hq)

theorem gaussian_lower_scaled_eight_tendsto_zero (j : Fin 6) :
    Filter.Tendsto
      (fun q : ℝ => iteratedDeriv (2*j.val) (gaussian q) 0 / q^8)
      Filter.atTop (nhds 0) := by
  fin_cases j
  · have hc : ContinuousAt h0 0 := by
      change ContinuousAt (fun u : ℝ => h0 u) 0
      dsimp [h0]
      fun_prop
    simpa [gaussian_even_zero] using
      scaled_polynomial_vanishes 0 8 (by omega) g0 h0 hc
        (fun q hq => g0_scale hq)
  · have hc : ContinuousAt h1 0 := by
      change ContinuousAt (fun u : ℝ => h1 u) 0
      dsimp [h1]
      fun_prop
    have h := (scaled_polynomial_vanishes 1 7 (by omega) g1 h1 hc
      (fun q hq => g1_scale hq)).neg
    convert h using 1
    funext q
    norm_num only
    rw [gaussian_even_two]
    ring
    all_goals norm_num
  · have hc : ContinuousAt h2 0 := by
      change ContinuousAt (fun u : ℝ => h2 u) 0
      dsimp [h2, h1, h0]
      fun_prop
    simpa [gaussian_even_four] using
      scaled_polynomial_vanishes 2 6 (by omega) g2 h2 hc
        (fun q hq => g2_scale hq)
  · have hc : ContinuousAt h3 0 := by
      change ContinuousAt (fun u : ℝ => h3 u) 0
      dsimp [h3, h2, h1, h0]
      fun_prop
    have h := (scaled_polynomial_vanishes 3 5 (by omega) g3 h3 hc
      (fun q hq => g3_scale hq)).neg
    convert h using 1
    funext q
    norm_num only
    rw [gaussian_even_six]
    ring
    all_goals norm_num
  · have hc : ContinuousAt h4 0 := by
      change ContinuousAt (fun u : ℝ => h4 u) 0
      dsimp [h4, h3, h2, h1, h0]
      fun_prop
    simpa [gaussian_even_eight] using
      scaled_polynomial_vanishes 4 4 (by omega) g4 h4 hc
        (fun q hq => g4_scale hq)
  · have hc : ContinuousAt h5 0 := by
      change ContinuousAt (fun u : ℝ => h5 u) 0
      dsimp [h5, h4, h3, h2, h1, h0]
      fun_prop
    have h := (scaled_polynomial_vanishes 5 3 (by omega) g5 h5 hc
      (fun q hq => g5_scale hq)).neg
    convert h using 1
    funext q
    norm_num only
    rw [gaussian_even_ten]
    ring
    all_goals norm_num

end
end RHTower.ThetaCuspOddFour

