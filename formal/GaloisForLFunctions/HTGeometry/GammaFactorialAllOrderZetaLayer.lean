import GaloisForLFunctions.HTGeometry.GammaFactorialAllOrderPoleJet
import GaloisForLFunctions.Hurwitz.PolygammaHurwitzValue

/-!
# All-order harmonic-zeta parity of the Gamma factorial microscope

This file evaluates the bounded layer in the exact all-order pole-jet law.  Shifted generalized
harmonic sums along the factorial microscope converge to the corresponding Riemann zeta value.
Consequently the natural correction of the scaled `m`-th polygamma jet is

`(1 + (-1)^(m+1)) m! ζ(m+1)`.

Thus every odd polygamma order has a nonzero even-zeta transverse residue, while every positive
even order cancels at this layer and passes control to the finite Euler-product tail.  The theorem
is uniform in the finite jet order and uses no numerical approximation.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

open scoped BigOperators

theorem norm_shiftedInversePow_sub_inversePow_le {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) {p : ℕ} (hp : 1 ≤ p) (j : ℕ) :
    ‖((((j + 1 : ℕ) : ℂ) - z) ^ p)⁻¹ -
        ((((j + 1 : ℕ) : ℂ) ^ p)⁻¹)‖ ≤
      (2 * (p : ℝ) * 2 ^ (p - 1)) * ‖z‖ / ((j + 1 : ℕ) : ℝ) := by
  let k : ℝ := ((j + 1 : ℕ) : ℝ)
  let c : ℂ := ((j + 1 : ℕ) : ℂ)
  let u : ℂ := (c - z)⁻¹
  let v : ℂ := c⁻¹
  have hk : 1 ≤ k := by
    dsimp [k]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hu : ‖u‖ ≤ 2 / k := by
    simpa [u, c, k] using norm_shiftedInverse_le hz j
  have hv : ‖v‖ = 1 / k := by
    dsimp [v, c, k]
    rw [norm_inv, Complex.norm_natCast]
    ring
  have htwoDiv : 2 / k ≤ 2 := by
    exact (div_le_iff₀ hkpos).2 (by nlinarith)
  have hu2 : ‖u‖ ≤ 2 := hu.trans htwoDiv
  have hv2 : ‖v‖ ≤ 2 := by
    rw [hv]
    have h1 : 1 / k ≤ 1 := (div_le_one hkpos).2 hk
    linarith
  have hdiff0 := norm_shiftedInverse_sub_inverse_le hz j
  have hdiff : ‖u - v‖ ≤ 2 * ‖z‖ / k := by
    have hk2 : 1 ≤ k ^ (2 : ℕ) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hk2
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg z))
    have hcoarse : 2 * ‖z‖ / k ^ (2 : ℕ) ≤ 2 * ‖z‖ / k := by
      field_simp [hkpos.ne']
      nlinarith [hmul]
    have hdiff1 : ‖u - v‖ ≤ 2 * ‖z‖ / k ^ (2 : ℕ) := by
      simpa [u, v, c, k] using hdiff0
    exact hdiff1.trans hcoarse
  let S : ℂ := ∑ i ∈ Finset.range p, u ^ i * v ^ (p - 1 - i)
  have hS : ‖S‖ ≤ (p : ℝ) * 2 ^ (p - 1) := by
    dsimp [S]
    calc
      ‖∑ i ∈ Finset.range p, u ^ i * v ^ (p - 1 - i)‖ ≤
          ∑ i ∈ Finset.range p, ‖u ^ i * v ^ (p - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range p, (2 : ℝ) ^ (p - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hip : i < p := Finset.mem_range.mp hi
        rw [norm_mul, norm_pow, norm_pow]
        calc
          ‖u‖ ^ i * ‖v‖ ^ (p - 1 - i) ≤
              (2 : ℝ) ^ i * 2 ^ (p - 1 - i) := by gcongr
          _ = 2 ^ (p - 1) := by
            rw [← pow_add]
            congr 1
            omega
      _ = (p : ℝ) * 2 ^ (p - 1) := by simp
  have hid : (u - v) * S = u ^ p - v ^ p := by
    dsimp [S]
    exact (Commute.all u v).mul_geom_sum₂ p
  change ‖((c - z) ^ p)⁻¹ - (c ^ p)⁻¹‖ ≤ _
  rw [← inv_pow, ← inv_pow]
  rw [← hid, norm_mul]
  calc
    ‖u - v‖ * ‖S‖ ≤
        (2 * ‖z‖ / k) * ((p : ℝ) * 2 ^ (p - 1)) := by gcongr
    _ = (2 * (p : ℝ) * 2 ^ (p - 1)) * ‖z‖ / k := by ring

theorem norm_shiftedHarmonicPowerSum_sub_unshifted_le {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    ‖shiftedHarmonicPowerSum p n z -
        ∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) ^ p)⁻¹)‖ ≤
      (2 * (p : ℝ) * 2 ^ (p - 1)) * ‖z‖ * (harmonic n : ℝ) := by
  rw [shiftedHarmonicPowerSum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ j ∈ Finset.range n,
        (((((j + 1 : ℕ) : ℂ) - z) ^ p)⁻¹ -
          ((((j + 1 : ℕ) : ℂ) ^ p)⁻¹))‖ ≤
        ∑ j ∈ Finset.range n,
          ‖((((j + 1 : ℕ) : ℂ) - z) ^ p)⁻¹ -
            ((((j + 1 : ℕ) : ℂ) ^ p)⁻¹)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range n,
        (2 * (p : ℝ) * 2 ^ (p - 1)) * ‖z‖ /
          ((j + 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_shiftedInversePow_sub_inversePow_le hz hp j
    _ = (2 * (p : ℝ) * 2 ^ (p - 1)) * ‖z‖ * (harmonic n : ℝ) := by
      rw [harmonic]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp

theorem tendsto_unshiftedHarmonicPowerSum_riemannZeta
    {p : ℕ} (hp : 1 < p) :
    Tendsto (fun n : ℕ =>
      ∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) ^ p)⁻¹)) atTop
      (𝓝 (riemannZeta (p : ℂ))) := by
  have hsummable : Summable (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ p) := by
    have hcpow : Summable (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ (p : ℂ)) :=
      Complex.summable_one_div_nat_cpow.mpr (by
        rw [Complex.natCast_re]
        exact_mod_cast hp)
    simpa only [Complex.cpow_natCast] using hcpow
  have hzeta : HasSum (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ p)
      (riemannZeta (p : ℂ)) := by
    rw [show riemannZeta (p : ℂ) = ∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ p by
      simpa using zeta_nat_eq_tsum_of_gt_one hp]
    exact hsummable.hasSum
  have h := hzeta.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  convert h using 1
  funext n
  change (∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) ^ p)⁻¹)) =
    ∑ i ∈ Finset.range (n + 1), (1 : ℂ) / (i : ℂ) ^ p
  rw [Finset.sum_range_succ']
  have hp0 : p ≠ 0 := by omega
  simp [hp0]

theorem tendsto_shiftedHarmonicPowerSum_factorial
    {p : ℕ} (hp : 1 < p) (x : ℂ) :
    Tendsto (fun n : ℕ => shiftedHarmonicPowerSum p n
      (reciprocalGammaFactorialScale n * x)) atTop
      (𝓝 (riemannZeta (p : ℂ))) := by
  let z : ℕ → ℂ := fun n => reciprocalGammaFactorialScale n * x
  let C : ℝ := 2 * (p : ℝ) * 2 ^ (p - 1)
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa [z] using tendsto_reciprocalGammaFactorialScale_zero.mul_const x
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ 1 / 2 :=
    (hz.norm.eventually_lt_const (by norm_num)).mono fun _ h => h.le
  have hmajor : Tendsto (fun n => C * ‖z n‖ * (harmonic n : ℝ))
      atTop (𝓝 0) := by
    have h := tendsto_gammaHarmonicMicroscopeScale_zero.norm.const_mul
      (C * ‖x‖)
    convert h using 1
    · funext n
      have hnormH : ‖(harmonic n : ℂ)‖ = (harmonic n : ℝ) := by
        rw [show (harmonic n : ℂ) = ((harmonic n : ℝ) : ℂ) by norm_cast]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        exact_mod_cast (show (0 : ℚ) ≤ harmonic n by
          rw [harmonic]
          positivity)
      simp only [z, C, gammaHarmonicMicroscopeScale, norm_mul, hnormH]
      ring
    · norm_num
  have hdiff : Tendsto (fun n =>
      shiftedHarmonicPowerSum p n (z n) -
        ∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) ^ p)⁻¹))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) _ hmajor
    filter_upwards [hsmall] with n hn
    exact norm_shiftedHarmonicPowerSum_sub_unshifted_le hn (Nat.le_of_lt hp) n
  have hsum := hdiff.add (tendsto_unshiftedHarmonicPowerSum_riemannZeta hp)
  have heq : ∀ n : ℕ,
      (shiftedHarmonicPowerSum p n (z n) -
          (∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) ^ p)⁻¹)) +
        (∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) ^ p)⁻¹))) =
      shiftedHarmonicPowerSum p n (z n) := by
    intro n
    ring
  simpa [z] using hsum.congr' (Filter.Eventually.of_forall heq)

/-- **All-order bounded zeta layer.**  After removing the reciprocal principal jet, the correction
at its natural factorial order is the sum of the local and shifted-harmonic zeta values. -/
theorem tendsto_gammaFactorialScaledPolygamma_correction
    {m : ℕ} (hm : 1 ≤ m) {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      (gammaFactorialScaledPolygamma m n x -
          ((-1 : ℂ) ^ (m + 1) * (m.factorial : ℂ) / x ^ (m + 1))) /
        reciprocalGammaFactorialScale n ^ (m + 1)) atTop
      (𝓝 (((-1 : ℂ) ^ (m + 1) + 1) * (m.factorial : ℂ) *
        riemannZeta ((m + 1 : ℕ) : ℂ))) := by
  let s : ℕ → ℂ := reciprocalGammaFactorialScale
  let z : ℕ → ℂ := fun n => s n * x
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa [z, s] using tendsto_reciprocalGammaFactorialScale_zero.mul_const x
  have hinput : Tendsto (fun n => 1 + z n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hz :
      Tendsto (fun n => 1 + z n) atTop (𝓝 (1 + 0)))
  have hOff1 : ∀ k : ℕ, (1 : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have hre := congrArg Complex.re hk
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hlocal0 : Tendsto (fun n => iteratedDeriv m Complex.digamma (1 + z n))
      atTop (𝓝 (iteratedDeriv m Complex.digamma 1)) :=
    (analyticAt_iteratedDeriv_of_analyticAt
      (analyticAt_digamma_of_offPoles hOff1) m).continuousAt.tendsto.comp hinput
  have hpsiOne : iteratedDeriv m Complex.digamma 1 =
      (-1 : ℂ) ^ (m + 1) * (m.factorial : ℂ) *
        riemannZeta ((m + 1 : ℕ) : ℂ) := by
    have h := polygamma_one_eq_riemannZeta (m - 1)
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have hm2 : m - 1 + 2 = m + 1 := by omega
    rw [hm1, hm2] at h
    exact h
  rw [hpsiOne] at hlocal0
  have hsum := tendsto_shiftedHarmonicPowerSum_factorial
    (show 1 < m + 1 by omega) x
  have hsum' := hsum.const_mul (m.factorial : ℂ)
  have hlimit := hlocal0.add hsum'
  have hlimit' : Tendsto (fun n =>
      iteratedDeriv m Complex.digamma (1 + z n) +
        (m.factorial : ℂ) * shiftedHarmonicPowerSum (m + 1) n (z n))
      atTop (𝓝 (((-1 : ℂ) ^ (m + 1) + 1) * (m.factorial : ℂ) *
        riemannZeta ((m + 1 : ℕ) : ℂ))) := by
    have hvalue :
        (-1 : ℂ) ^ (m + 1) * (m.factorial : ℂ) *
              riemannZeta ((m + 1 : ℕ) : ℂ) +
            (m.factorial : ℂ) * riemannZeta ((m + 1 : ℕ) : ℂ) =
          ((-1 : ℂ) ^ (m + 1) + 1) * (m.factorial : ℂ) *
            riemannZeta ((m + 1 : ℕ) : ℂ) := by ring
    rw [hvalue] at hlimit
    simpa [z, s] using hlimit
  have hregular : ∀ᶠ n : ℕ in atTop, ∀ k : ℤ, z n ≠ (k : ℂ) := by
    have hlt : ∀ᶠ n : ℕ in atTop, ‖z n‖ < 1 :=
      hz.norm.eventually_lt_const (by norm_num)
    filter_upwards [hlt] with n hzn k
    have hsn : s n ≠ 0 := by
      dsimp [s]
      exact div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    exact ne_intCast_of_ne_zero_of_norm_lt_one (mul_ne_zero hsn hx) hzn k
  have heq : ∀ᶠ n : ℕ in atTop,
      (gammaFactorialScaledPolygamma m n x -
          ((-1 : ℂ) ^ (m + 1) * (m.factorial : ℂ) / x ^ (m + 1))) /
          s n ^ (m + 1) =
        iteratedDeriv m Complex.digamma (1 + z n) +
          (m.factorial : ℂ) * shiftedHarmonicPowerSum (m + 1) n (z n) := by
    filter_upwards [hregular] with n hzn
    have hsn : reciprocalGammaFactorialScale n ≠ 0 := by
      exact div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    change (gammaFactorialScaledPolygamma m n x -
          ((-1 : ℂ) ^ (m + 1) * (m.factorial : ℂ) / x ^ (m + 1))) /
          reciprocalGammaFactorialScale n ^ (m + 1) =
        iteratedDeriv m Complex.digamma
            (1 + reciprocalGammaFactorialScale n * x) +
          (m.factorial : ℂ) * shiftedHarmonicPowerSum (m + 1) n
            (reciprocalGammaFactorialScale n * x)
    rw [gammaFactorialScaledPolygamma_eq_principal_add m n hx]
    · field_simp [hsn]
      ring
    · simpa [z] using hzn
  exact hlimit'.congr' (heq.mono fun _ h => h.symm)

/-- At every odd polygamma order the two zeta contributions reinforce, giving a nonzero
factorial-scale residue. -/
theorem tendsto_gammaFactorialScaledPolygamma_odd_correction
    (r : ℕ) {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      (gammaFactorialScaledPolygamma (2 * r + 1) n x -
          ((2 * r + 1).factorial : ℂ) / x ^ (2 * r + 2)) /
        reciprocalGammaFactorialScale n ^ (2 * r + 2)) atTop
      (𝓝 (2 * (((2 * r + 1).factorial : ℂ) *
        riemannZeta ((2 * r + 2 : ℕ) : ℂ)))) := by
  have h := tendsto_gammaFactorialScaledPolygamma_correction
    (m := 2 * r + 1) (by omega) hx
  have hexp : 2 * r + 1 + 1 = 2 * r + 2 := by omega
  have heven : Even (2 * r + 2) := ⟨r + 1, by omega⟩
  have hsign : (-1 : ℂ) ^ (2 * r + 2) = 1 := heven.neg_one_pow
  simp only [hexp, hsign, one_mul] at h
  have htwo : (1 : ℂ) + 1 = 2 := by norm_num
  rw [htwo] at h
  simpa [mul_assoc] using h

theorem gammaFactorialScaledPolygamma_odd_correction_limit_ne_zero
    (r : ℕ) :
    2 * (((2 * r + 1).factorial : ℂ) *
      riemannZeta ((2 * r + 2 : ℕ) : ℂ)) ≠ 0 := by
  apply mul_ne_zero (by norm_num)
  apply mul_ne_zero
  · exact_mod_cast Nat.factorial_ne_zero (2 * r + 1)
  · apply riemannZeta_ne_zero_of_one_lt_re
    rw [Complex.natCast_re]
    exact_mod_cast (show 1 < 2 * r + 2 by omega)

/-- At every positive even polygamma order, the local odd-zeta value and the generalized harmonic
limit cancel.  The next nonzero datum must therefore come from the finite tail. -/
theorem tendsto_gammaFactorialScaledPolygamma_even_correction
    (r : ℕ) {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      (gammaFactorialScaledPolygamma (2 * r + 2) n x -
          (-(((2 * r + 2).factorial : ℂ) / x ^ (2 * r + 3)))) /
        reciprocalGammaFactorialScale n ^ (2 * r + 3)) atTop (𝓝 0) := by
  have h := tendsto_gammaFactorialScaledPolygamma_correction
    (m := 2 * r + 2) (by omega) hx
  have hexp : 2 * r + 2 + 1 = 2 * r + 3 := by omega
  have hodd : Odd (2 * r + 3) := ⟨r + 1, by omega⟩
  have hsign : (-1 : ℂ) ^ (2 * r + 3) = -1 := hodd.neg_one_pow
  simp only [hexp, hsign, neg_one_mul, neg_add_cancel, zero_mul] at h
  convert h using 1
  funext n
  ring

end

end GaloisForLFunctions
