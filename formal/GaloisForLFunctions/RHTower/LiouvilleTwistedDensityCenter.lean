import GaloisForLFunctions.RHTower.LiouvilleTwistedHarmonicDecay
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The actual twisted exponential center at every real scale

For the fixed completely multiplicative twist `f(2)=I`, `f(p)=-1` at odd primes,
the complete exponential density satisfies `log T * F(1/T) → 0` as real `T → ∞`.
The proof uses the exact Abel identity for the full harmonic partial sums. Splitting
at `floor (sqrt T)` controls the complete short sum, while logarithmic harmonic
cancellation controls the entire remaining tail. The earlier square-scale limit is
retained. No unproved tail or center premise is assumed.

This supplies the center obligation for MC-C12.92's moving-prime simple-zero
construction at every sufficiently small positive damping parameter. No critical
Liouville bound or RH conclusion follows from this logarithmic estimate alone.
-/

open Filter RHTower.LiouvilleHarmonic
open scoped Topology BigOperators

namespace RHTower.LiouvilleTwistedDensity
noncomputable section

private theorem harmonic_bounded : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖harmonic twisted n‖ ≤ B := by
  obtain ⟨B, hB⟩ := RHTower.deningerBounded_of_tendsto tendsto_harmonic_twisted_zero.norm
  simp only [abs_norm] at hB
  exact ⟨B, (norm_nonneg _).trans (hB 0), hB⟩

private theorem summable_harmonic_geometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => harmonic twisted n * (q : ℂ) ^ n) := by
  obtain ⟨B, _, hB⟩ := harmonic_bounded
  apply ((summable_geometric_of_lt_one hq0 hq1).mul_left B).of_norm_bounded
  intro n
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
  exact mul_le_mul_of_nonneg_right (hB n) (pow_nonneg hq0 n)

theorem density_eq_harmonic_average {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    density q = (1 - (q : ℂ)) * ∑' n : ℕ, harmonic twisted n * (q : ℂ) ^ n := by
  have hc (N : ℕ) : (∑ n ∈ Finset.range (N + 1), coefficient n) = harmonic twisted N := rfl
  have hpartial : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, coefficient n) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp tendsto_harmonic_twisted_zero
  have hqnorm : ‖(q : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have habel := (Complex.abel_aux hpartial hqnorm).neg
  simp only [zero_sub, hc, neg_mul, Finset.sum_neg_distrib, mul_neg, neg_neg] at habel
  exact tendsto_nhds_unique habel
    ((summable_harmonic_geometric hq0 hq1).hasSum.tendsto_sum_nat.const_mul (1 - (q : ℂ)))

private theorem log_average_bound {q B ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hB0 : 0 ≤ B) (hB : ∀ n, ‖harmonic twisted n‖ ≤ B) (hε : 0 ≤ ε) (N : ℕ)
    (htail : ∀ n, N ≤ n → ‖(Real.log ((n : ℝ) + 1) : ℂ) * harmonic twisted n‖ ≤ ε) :
    ‖(Real.log ((N : ℝ) + 1) : ℂ) * density q‖ ≤
      (1 - q) * ((N : ℝ) * (Real.log ((N : ℝ) + 1) * B)) + ε := by
  let L := Real.log ((N : ℝ) + 1)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  let u : ℕ → ℂ := fun n => (L : ℂ) * (harmonic twisted n * (q : ℂ) ^ n)
  have hu : Summable u := (summable_harmonic_geometric hq0 hq1).mul_left (L : ℂ)
  have hnorm (n : ℕ) : ‖u n‖ = L * ‖harmonic twisted n‖ * q ^ n := by
    simp only [u, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hL, abs_of_nonneg hq0, mul_assoc]
  have hhead : ‖∑ n ∈ Finset.range N, u n‖ ≤ (N : ℝ) * (L * B) := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖u n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, L * B := Finset.sum_le_sum fun n _ => by
        rw [hnorm]
        calc
          _ ≤ (L * B) * q ^ n := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hB n) hL) (pow_nonneg hq0 n)
          _ ≤ L * B := mul_le_of_le_one_right (mul_nonneg hL hB0) (pow_le_one₀ hq0 hq1.le)
      _ = _ := by simp
  have htail' : ‖∑' n : ℕ, u (n + N)‖ ≤ ε * (1 - q)⁻¹ := by
    apply tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hq0 hq1).mul_left ε)
    intro n
    have hh := htail (n + N) (by omega)
    have hnlog : L ≤ Real.log (((n + N : ℕ) : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show N + 1 ≤ n + N + 1 by omega))
    have hnlog0 : 0 ≤ Real.log (((n + N : ℕ) : ℝ) + 1) := by
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnlog0] at hh
    rw [hnorm]
    calc
      _ ≤ ε * q ^ (n + N) := mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_right hnlog (norm_nonneg _)).trans hh) (pow_nonneg hq0 _)
      _ ≤ ε * q ^ n := mul_le_mul_of_nonneg_left (by
        rw [pow_add]
        exact mul_le_of_le_one_right (pow_nonneg hq0 n) (pow_le_one₀ hq0 hq1.le)) hε
  have hsum : ‖∑' n : ℕ, u n‖ ≤ (N : ℝ) * (L * B) + ε * (1 - q)⁻¹ := by
    rw [← hu.sum_add_tsum_nat_add N]
    exact (norm_add_le _ _).trans (add_le_add hhead htail')
  have heq : (L : ℂ) * density q = (1 - (q : ℂ)) * ∑' n : ℕ, u n := by
    rw [density_eq_harmonic_average hq0 hq1]
    simp only [u, tsum_mul_left]
    ring
  have hnq : ‖(1 : ℂ) - (q : ℂ)‖ = 1 - q := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hq1.le)]
  change ‖(L : ℂ) * density q‖ ≤ _
  rw [heq, norm_mul, hnq]
  calc
    _ ≤ (1 - q) * ((N : ℝ) * (L * B) + ε * (1 - q)⁻¹) :=
      mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hq1.le)
    _ = _ := by field_simp [sub_ne_zero.mpr hq1.ne']; ring

theorem tendsto_log_mul_exponentialDensity_square_zero :
    Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 1) : ℂ) *
      exponentialDensity (1 / ((N : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := harmonic_bounded
  have hscale : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => B * (Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hscale).const_mul B
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp tendsto_log_mul_harmonic_twisted_zero (ε / 2) hhalf
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hsmall (ε / 2) hhalf
  refine ⟨max J K, fun N hN => ?_⟩
  let x : ℝ := (N : ℝ) + 1
  have hx : 0 < x := by dsimp [x]; positivity
  let q : ℝ := Real.exp (-(1 / x ^ 2))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr
    (neg_lt_zero.mpr (by positivity : (0 : ℝ) < 1 / x ^ 2))
  have hqbound : 1 - q ≤ 1 / x ^ 2 := by
    have h := Real.add_one_le_exp (-(1 / x ^ 2))
    dsimp [q]
    linarith
  have htail : ∀ n, N ≤ n → ‖(Real.log ((n : ℝ) + 1) : ℂ) * harmonic twisted n‖ ≤ ε / 2 := by
    intro n hn
    have h := hK n (le_trans ((le_max_right J K).trans hN) hn)
    simpa only [dist_zero_right] using h.le
  have hbound := log_average_bound hq0 hq1 hB0 hB hhalf.le N htail
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) N])
  have herror : (1 - q) * ((N : ℝ) * (Real.log x * B)) ≤ B * (Real.log x / x) := by
    calc
      _ ≤ (1 / x ^ 2) * ((N : ℝ) * (Real.log x * B)) :=
        mul_le_mul_of_nonneg_right hqbound (by positivity)
      _ ≤ (1 / x ^ 2) * (x * (Real.log x * B)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (by dsimp [x]; linarith : (N : ℝ) ≤ x) (mul_nonneg hlog hB0)) (by positivity)
      _ = _ := by field_simp [hx.ne']
  have hshort := hJ N ((le_max_left J K).trans hN)
  rw [Real.dist_eq, sub_zero] at hshort
  have hshort' : B * (Real.log x / x) < ε / 2 := (le_abs_self _).trans_lt hshort
  rw [dist_zero_right, exponentialDensity_eq_density]
  change ‖(Real.log x : ℂ) * density q‖ < ε
  calc
    _ ≤ (1 - q) * ((N : ℝ) * (Real.log x * B)) + ε / 2 := hbound
    _ ≤ B * (Real.log x / x) + ε / 2 := by linarith only [herror]
    _ < ε := by linarith only [hshort']

/-- The actual full twisted center has logarithmic cancellation at every real scale. -/
theorem tendsto_log_mul_exponentialDensity_reciprocal_zero :
    Tendsto (fun T : ℝ => (Real.log T : ℂ) * exponentialDensity (1/T)) atTop (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := harmonic_bounded
  have hNlim : Tendsto (fun T : ℝ => ⌊Real.sqrt T⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_sqrt_atTop
  have hscale : Tendsto (fun T : ℝ => (⌊Real.sqrt T⌋₊ : ℝ)+1) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).comp hNlim
  have hsmall : Tendsto (fun T : ℝ => B *
      (Real.log ((⌊Real.sqrt T⌋₊ : ℝ)+1) / ((⌊Real.sqrt T⌋₊ : ℝ)+1))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hscale).const_mul B
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp tendsto_log_mul_harmonic_twisted_zero
    (ε/4) (by linarith)
  have hshort := hsmall.eventually (isOpen_Iio.mem_nhds (by linarith : (0 : ℝ) < ε/8))
  filter_upwards [hshort, hNlim.eventually (eventually_ge_atTop K),
    eventually_ge_atTop (4 : ℝ)] with T hs hNK hT
  let N : ℕ := ⌊Real.sqrt T⌋₊
  let x : ℝ := (N : ℝ)+1
  have hT0 : 0 < T := by linarith
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hx : 0 < x := by dsimp [x]; positivity
  have hN1 : 1 ≤ N := Nat.le_floor (by
    have h := Real.sqrt_le_sqrt (by linarith : (1 : ℝ) ≤ T)
    simpa only [Real.sqrt_one, Nat.cast_one] using h)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hfloor : (N : ℝ) ≤ Real.sqrt T := Nat.floor_le (Real.sqrt_nonneg T)
  have hceil : Real.sqrt T < x := Nat.lt_floor_add_one _
  have hNsq : (N : ℝ)^2 ≤ T := by
    nlinarith [Real.sq_sqrt hT0.le, mul_nonneg (sub_nonneg.mpr hfloor)
      (add_nonneg (Real.sqrt_nonneg T) hn0)]
  have hTx : T ≤ x^2 := by
    nlinarith [Real.sq_sqrt hT0.le, mul_nonneg (sub_nonneg.mpr hceil.le)
      (add_nonneg hx.le (Real.sqrt_nonneg T))]
  have hratio : Real.log T ≤ 2 * Real.log x := by
    have h := Real.log_le_log hT0 hTx
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by dsimp [x]; linarith)
  let q := Real.exp (-(1/T))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (one_div_pos.mpr hT0))
  have hqbound : 1-q ≤ 1/T := by
    have h := Real.add_one_le_exp (-(1/T))
    dsimp [q]
    linarith
  have htail : ∀ n, N ≤ n → ‖(Real.log ((n : ℝ)+1) : ℂ) * harmonic twisted n‖ ≤ ε/4 := by
    intro n hn
    have h := hK n (le_trans hNK hn)
    simpa only [dist_zero_right] using h.le
  have hb := log_average_bound hq0 hq1 hB0 hB (by linarith : (0 : ℝ) ≤ ε/4) N htail
  have hNratio : (N : ℝ) / T ≤ 2/x := by
    apply (div_le_div_iff₀ hT0 hx).mpr
    dsimp [x]
    nlinarith [mul_nonneg (sub_nonneg.mpr hN1r) hn0]
  have hhead : (1-q) * ((N : ℝ) * (Real.log x * B)) ≤ 2*B*(Real.log x/x) := by
    calc
      _ ≤ (1/T) * ((N : ℝ) * (Real.log x * B)) :=
        mul_le_mul_of_nonneg_right hqbound (by positivity)
      _ = ((N : ℝ)/T) * (Real.log x * B) := by ring
      _ ≤ (2/x) * (Real.log x * B) := mul_le_mul_of_nonneg_right hNratio (by positivity)
      _ = _ := by ring
  have hcompare : ‖(Real.log T : ℂ) * density q‖ ≤ 2 * ‖(Real.log x : ℂ) * density q‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hlogT, abs_of_nonneg hlogx]
    nlinarith [mul_le_mul_of_nonneg_right hratio (norm_nonneg (density q))]
  change B*(Real.log x/x) < ε/8 at hs
  rw [dist_zero_right, exponentialDensity_eq_density]
  change ‖(Real.log T : ℂ) * density q‖ < ε
  calc
    _ ≤ 2 * ‖(Real.log x : ℂ) * density q‖ := hcompare
    _ ≤ 2 * ((1-q) * ((N : ℝ) * (Real.log x * B)) + ε/4) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 4*B*(Real.log x/x) + ε/2 := by linarith
    _ < ε := by linarith

end
end RHTower.LiouvilleTwistedDensity
