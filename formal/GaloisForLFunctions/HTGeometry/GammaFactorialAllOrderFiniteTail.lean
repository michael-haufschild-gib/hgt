import GaloisForLFunctions.HTGeometry.GammaFactorialAllOrderZetaLayer
import GaloisForLFunctions.Hurwitz.ShiftedPowerTailAsymptotic

/-!
# Even-order finite-tail residues of the Gamma factorial microscope

The bounded zeta layer cancels at every positive even polygamma order.  This file resolves the
next scale.  After multiplication by `(n+1)^m`, the surviving Euler-product tail converges to the
universal nonzero rational coefficient `-(m-1)!`.

The proof combines the exact Gamma pole-jet law with the continuum asymptotic
`x^m ∑_{k≥0}(x+k)^(-(m+1)) → 1/m`.  The factorial displacement of the microscope is negligible
against every polynomial scale, both in the local polygamma term and in the shifted generalized
harmonic sum.  No numerical approximation is used.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

open scoped BigOperators

theorem shiftedHarmonicPowerSum_zero (p n : ℕ) :
    shiftedHarmonicPowerSum p n 0 =
      ∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) ^ p)⁻¹) := by
  simp [shiftedHarmonicPowerSum]

theorem hzeta_natSucc_eq_riemannZeta_sub_shiftedHarmonicPowerSum_zero
    {p : ℕ} (hp : 1 < p) (n : ℕ) :
    HurwitzZetaShift.hzeta (p : ℂ) (((n + 1 : ℕ) : ℂ)) =
      riemannZeta (p : ℂ) - shiftedHarmonicPowerSum p n 0 := by
  induction n with
  | zero =>
      simpa [shiftedHarmonicPowerSum] using
        (hzeta_one_eq_riemannZeta (s := (p : ℂ)) (by
          rw [Complex.natCast_re]
          exact_mod_cast hp))
  | succ n ih =>
      have hs : 1 < ((p : ℂ)).re := by
        rw [Complex.natCast_re]
        exact_mod_cast hp
      have hstep := hzeta_add_one hs (((n + 1 : ℕ) : ℂ))
      have hcast : (((n + 1 + 1 : ℕ) : ℂ)) = (((n + 1 : ℕ) : ℂ)) + 1 := by
        push_cast
        ring
      rw [← hcast] at hstep
      rw [hstep, ih]
      simp only [shiftedHarmonicPowerSum, sub_zero, Finset.sum_range_succ]
      rw [Complex.cpow_neg, Complex.cpow_natCast]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

theorem tendsto_scaled_riemannZeta_sub_shiftedHarmonicPowerSum_zero
    (q : ℕ) (hq : 0 < q) :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ q) *
        (riemannZeta ((q + 1 : ℕ) : ℂ) -
          shiftedHarmonicPowerSum (q + 1) n 0)) atTop
      (𝓝 ((1 / (q : ℝ) : ℝ) : ℂ)) := by
  have h := (tendsto_scaled_hzeta_nat_ofReal q hq).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  apply h.congr'
  filter_upwards with n
  simp only [Function.comp_apply]
  have hcast : ((((n + 1 : ℕ) : ℝ) : ℂ)) = (((n + 1 : ℕ) : ℂ)) := by
    norm_cast
  rw [hcast]
  rw [hzeta_natSucc_eq_riemannZeta_sub_shiftedHarmonicPowerSum_zero
    (show 1 < q + 1 by omega) n]

theorem tendsto_natSuccPow_mul_localPolygamma_sub
    (m : ℕ) (x : ℂ) (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ m) *
      (iteratedDeriv m Complex.digamma
          (1 + reciprocalGammaFactorialScale n * x) -
        iteratedDeriv m Complex.digamma 1)) atTop (𝓝 0) := by
  let z : ℕ → ℂ := fun n => reciprocalGammaFactorialScale n * x
  let f : ℂ → ℂ := iteratedDeriv m Complex.digamma
  have hz0 : Tendsto z atTop (𝓝 0) := by
    simpa [z] using tendsto_reciprocalGammaFactorialScale_zero.mul_const x
  have hzne : ∀ n, z n ≠ 0 := fun n =>
    mul_ne_zero (div_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero n)) hx
  have hzWithin : Tendsto z atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hz0, Filter.Eventually.of_forall fun n => by
      simp [hzne n]⟩
  have hOff1 : ∀ k : ℕ, (1 : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have hre := congrArg Complex.re hk
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hder : HasDerivAt f (deriv f 1) 1 :=
    (analyticAt_iteratedDeriv_of_analyticAt
      (analyticAt_digamma_of_offPoles hOff1) m).differentiableAt.hasDerivAt
  have hquot := hder.tendsto_slope_zero.comp hzWithin
  simp only [smul_eq_mul] at hquot
  have hscale0 :=
    (tendsto_factorialScale_pow_mul_natSuccPow_zero 1 m (by omega)).mul_const x
  simp only [zero_mul] at hscale0
  have hscale : Tendsto (fun n => z n * (((n + 1 : ℕ) : ℂ) ^ m))
      atTop (𝓝 0) := by
    convert hscale0 using 1
    funext n
    simp only [z]
    ring
  have hprod := hquot.mul hscale
  simp only [mul_zero] at hprod
  apply hprod.congr'
  filter_upwards with n
  change ((z n)⁻¹ * (f (1 + z n) - f 1)) *
      (z n * (((n + 1 : ℕ) : ℂ) ^ m)) =
        (((n + 1 : ℕ) : ℂ) ^ m) * (f (1 + z n) - f 1)
  field_simp [hzne n]

theorem tendsto_natSuccPow_mul_shiftedHarmonicPowerSum_sub_zero
    {p : ℕ} (hp : 1 < p) (x : ℂ) :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ (p - 1)) *
      (shiftedHarmonicPowerSum p n (reciprocalGammaFactorialScale n * x) -
        shiftedHarmonicPowerSum p n 0)) atTop (𝓝 0) := by
  let C : ℝ := 2 * (p : ℝ) * 2 ^ (p - 1)
  let z : ℕ → ℂ := fun n => reciprocalGammaFactorialScale n * x
  have hz0 : Tendsto z atTop (𝓝 0) := by
    simpa [z] using tendsto_reciprocalGammaFactorialScale_zero.mul_const x
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ 1 / 2 :=
    (hz0.norm.eventually_lt_const (by norm_num)).mono fun _ h => h.le
  have hmajor : Tendsto (fun n =>
      C * ‖x‖ * ‖reciprocalGammaFactorialScale n ^ 1 *
        (((n + 1 : ℕ) : ℂ) ^ p)‖) atTop (𝓝 0) := by
    simpa using
      (tendsto_factorialScale_pow_mul_natSuccPow_zero 1 p (by omega)).norm.const_mul
        (C * ‖x‖)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) _ hmajor
  filter_upwards [hsmall] with n hn
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  have hdiff := norm_shiftedHarmonicPowerSum_sub_unshifted_le hn
    (Nat.le_of_lt hp) n
  rw [← shiftedHarmonicPowerSum_zero] at hdiff
  have hH := harmonic_cast_real_le_natSucc n
  have hN : (0 : ℝ) ≤ (n + 1 : ℕ) := by positivity
  calc
    ((n + 1 : ℕ) : ℝ) ^ (p - 1) *
        ‖shiftedHarmonicPowerSum p n (z n) - shiftedHarmonicPowerSum p n 0‖
      ≤ ((n + 1 : ℕ) : ℝ) ^ (p - 1) *
          (C * ‖z n‖ * (harmonic n : ℝ)) := by gcongr
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ (p - 1) *
          (C * ‖z n‖ * (((n + 1 : ℕ) : ℝ))) := by
      gcongr
      simpa only [Nat.cast_add, Nat.cast_one] using hH
    _ = C * ‖x‖ * ‖reciprocalGammaFactorialScale n ^ 1 *
          (((n + 1 : ℕ) : ℂ) ^ p)‖ := by
      simp only [z, norm_mul, norm_pow, pow_one, Complex.norm_natCast]
      have hpow : ((n + 1 : ℕ) : ℝ) ^ (p - 1) * ((n + 1 : ℕ) : ℝ) =
          ((n + 1 : ℕ) : ℝ) ^ p := by
        rw [← pow_succ]
        congr 1
        omega
      rw [← hpow]
      ring

/-- At positive even polygamma order, the zeta cancellation exposes a universal rational
finite-tail coefficient. -/
theorem tendsto_gammaFactorialEvenPolygamma_regular_finiteTail
    (r : ℕ) {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ (2 * r + 2)) *
      (iteratedDeriv (2 * r + 2) Complex.digamma
          (1 + reciprocalGammaFactorialScale n * x) +
        (((2 * r + 2).factorial : ℂ) *
          shiftedHarmonicPowerSum (2 * r + 3) n
            (reciprocalGammaFactorialScale n * x)))) atTop
      (𝓝 (-(((2 * r + 1).factorial : ℂ)))) := by
  let m : ℕ := 2 * r + 2
  have hm : 0 < m := by simp [m]
  have hm1 : m + 1 = 2 * r + 3 := by simp [m]
  have hlocal := tendsto_natSuccPow_mul_localPolygamma_sub m x hx
  have hshift0 := tendsto_natSuccPow_mul_shiftedHarmonicPowerSum_sub_zero
    (p := m + 1) (show 1 < m + 1 by omega) x
  have hshift := hshift0.const_mul (m.factorial : ℂ)
  have hshift' : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ m) *
      ((m.factorial : ℂ) *
        (shiftedHarmonicPowerSum (m + 1) n
            (reciprocalGammaFactorialScale n * x) -
          shiftedHarmonicPowerSum (m + 1) n 0))) atTop (𝓝 0) := by
    have hexp : m + 1 - 1 = m := by omega
    simp only [hexp, mul_zero] at hshift
    convert hshift using 1
    funext n
    ring
  have htail := tendsto_scaled_riemannZeta_sub_shiftedHarmonicPowerSum_zero m hm
  have htail' := htail.const_mul (-((m.factorial : ℂ)))
  have hlimit :
      -((m.factorial : ℂ)) * (((1 / (m : ℝ) : ℝ) : ℂ)) =
        -(((m - 1).factorial : ℂ)) := by
    rw [← Nat.mul_factorial_pred (ne_of_gt hm)]
    push_cast
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hm
    field_simp [hm0]
  rw [hlimit] at htail'
  have hodd : Odd (m + 1) := ⟨r + 1, by simp [m]; omega⟩
  have hsign : (-1 : ℂ) ^ (m + 1) = -1 := hodd.neg_one_pow
  have hpsiOne : iteratedDeriv m Complex.digamma 1 =
      -((m.factorial : ℂ) * riemannZeta ((m + 1 : ℕ) : ℂ)) := by
    have h := polygamma_one_eq_riemannZeta (m - 1)
    have hmadd : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm.ne')
    have hmadd2 : m - 1 + 2 = m + 1 := by omega
    rw [hmadd, hmadd2, hsign] at h
    simpa using h
  have hbase : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ m) *
      (iteratedDeriv m Complex.digamma 1 +
        (m.factorial : ℂ) * shiftedHarmonicPowerSum (m + 1) n 0))
      atTop (𝓝 (-(((m - 1).factorial : ℂ)))) := by
    apply htail'.congr'
    filter_upwards with n
    rw [hpsiOne]
    ring
  have herror := hlocal.add hshift'
  simp only [add_zero] at herror
  have htotal := herror.add hbase
  simp only [zero_add] at htotal
  convert htotal using 1
  · funext n
    dsimp only [m]
    rw [hm1]
    ring
  · have hm2 : m - 1 = 2 * r + 1 := by omega
    rw [hm2]

/-- **All-order even finite-tail residue.**  After the reciprocal principal jet and bounded zeta
layer both cancel, magnification by `(n+1)^m` leaves `-(m-1)!`. -/
theorem tendsto_gammaFactorialScaledPolygamma_even_finiteTail
    (r : ℕ) {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ (2 * r + 2)) *
      ((gammaFactorialScaledPolygamma (2 * r + 2) n x -
          (-(((2 * r + 2).factorial : ℂ) / x ^ (2 * r + 3)))) /
        reciprocalGammaFactorialScale n ^ (2 * r + 3))) atTop
      (𝓝 (-(((2 * r + 1).factorial : ℂ)))) := by
  let m : ℕ := 2 * r + 2
  let s : ℕ → ℂ := reciprocalGammaFactorialScale
  let z : ℕ → ℂ := fun n => s n * x
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa [z, s] using tendsto_reciprocalGammaFactorialScale_zero.mul_const x
  have hregular : ∀ᶠ n : ℕ in atTop, ∀ k : ℤ, z n ≠ (k : ℂ) := by
    have hlt : ∀ᶠ n : ℕ in atTop, ‖z n‖ < 1 :=
      hz.norm.eventually_lt_const (by norm_num)
    filter_upwards [hlt] with n hzn k
    have hsn : s n ≠ 0 := by
      dsimp [s]
      exact div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    exact ne_intCast_of_ne_zero_of_norm_lt_one (mul_ne_zero hsn hx) hzn k
  have htail := tendsto_gammaFactorialEvenPolygamma_regular_finiteTail r hx
  apply htail.congr'
  filter_upwards [hregular] with n hzn
  have hsn : reciprocalGammaFactorialScale n ≠ 0 := by
    exact div_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero n)
  have hodd : Odd (m + 1) := ⟨r + 1, by simp [m]; omega⟩
  have hsign : (-1 : ℂ) ^ (m + 1) = -1 := hodd.neg_one_pow
  change (((n + 1 : ℕ) : ℂ) ^ m) *
      (iteratedDeriv m Complex.digamma
          (1 + reciprocalGammaFactorialScale n * x) +
        (m.factorial : ℂ) * shiftedHarmonicPowerSum (m + 1) n
          (reciprocalGammaFactorialScale n * x)) =
    (((n + 1 : ℕ) : ℂ) ^ m) *
      ((gammaFactorialScaledPolygamma m n x -
          (-((m.factorial : ℂ) / x ^ (m + 1)))) /
        reciprocalGammaFactorialScale n ^ (m + 1))
  rw [gammaFactorialScaledPolygamma_eq_principal_add m n hx]
  · rw [hsign]
    field_simp [hsn]
    ring
  · simpa [z, s] using hzn

end

end GaloisForLFunctions
