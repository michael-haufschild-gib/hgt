import GaloisForLFunctions.BiScaleUncertainty.HighFrequencyLaplaceEnergyMeanValue
import Zeta23.FromPNTPlus.Mertens

/-!
# The band theorem: the Laplace energy is band-limited to `|ξ| ≤ √(N+2)` up to `O(log N)`

Feeding Mertens' first theorem (`Σ_{n ≤ x} Λ(n)/n ≤ log x + log 4 + 4`) and Chebyshev's bound
(`ψ(x) ≤ (log 4 + 4) x`) into the high-frequency law at the band frequency `ξ₀ = √(N+2) = e^{L/2}`
gives the unconditional, fully explicit inequality

`laplaceEnergy N ≤ ∫_{|ξ| ≤ √(N+2)} S_N(ξ) dξ + (52 (log 4 + 4)/π³) · L + (32 + 8(log 4 + 4))/π² + 4/(3π⁴)`,

while trivially `∫_{|ξ| ≤ √(N+2)} S_N ≤ laplaceEnergy N`.  Together with the two-sided comparison of
the Laplace energy with the mean-square Chebyshev error this proves, inside the field,

`Σ_{n<x} (ψ(n) − n)²/(n(n+1)) = O(log x)  ⟺  ∫_{|ξ| ≤ √x} ‖ν̂_x(ξ)‖² dξ/(¼ + 4π²ξ²) = O(log x)`:

the square-root barrier is exactly the statement that the pole-subtracted truncated `−ζ'/ζ` has
bounded average energy on the critical-line band of ordinates `|t| ≤ 2π√x`.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators CompactlySupported Real FourierTransform

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-! ## Mertens and Chebyshev inputs for the diagonal sums -/

/-- Mertens' first theorem on the window: `Σ_{n ≤ N+2} Λ(n)/n ≤ L + log 4 + 4`. -/
theorem sum_vonMangoldt_div_le_cutoff_add (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 (N + 2), ArithmeticFunction.vonMangoldt n / n) ≤
      cutoff N + (Real.log 4 + 4) := by
  have h := Mertens.sum_mangoldt_div_eq_log (x := ((N + 2 : ℕ) : ℝ))
    (by exact_mod_cast (show 1 ≤ N + 2 by omega))
  rw [Nat.floor_natCast] at h
  have hIoc : Finset.Ioc 0 (N + 2) = Finset.Icc 1 (N + 2) := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hIoc] at h
  have := (abs_le.1 h).2
  unfold cutoff
  linarith

theorem atomicDiagonal_le_cutoff_mul (N : ℕ) :
    atomicDiagonal N ≤ cutoff N * (cutoff N + (Real.log 4 + 4)) :=
  (atomicDiagonal_le N).trans
    (mul_le_mul_of_nonneg_left (sum_vonMangoldt_div_le_cutoff_add N) (cutoff_nonneg N))

theorem atomicSecondMoment_le_cutoff_mul (N : ℕ) :
    atomicSecondMoment N ≤ cutoff N * ((Real.log 4 + 4) * ((N + 2 : ℕ) : ℝ)) :=
  (atomicSecondMoment_le N).trans
    (mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self (by positivity)) (cutoff_nonneg N))

/-! ## The band frequency `√(N+2) = e^{L/2}` -/

/-- The band frequency `ξ₀ = √(N+2)`. -/
def bandFrequency (N : ℕ) : ℝ := Real.sqrt ((N + 2 : ℕ) : ℝ)

theorem bandFrequency_pos (N : ℕ) : 0 < bandFrequency N := Real.sqrt_pos.2 (by positivity)

theorem one_le_bandFrequency (N : ℕ) : 1 ≤ bandFrequency N :=
  Real.one_le_sqrt.2 (by exact_mod_cast (show 1 ≤ N + 2 by omega))

theorem bandFrequency_sq (N : ℕ) : bandFrequency N ^ 2 = ((N + 2 : ℕ) : ℝ) :=
  Real.sq_sqrt (by positivity)

theorem exp_half_cutoff_eq_bandFrequency (N : ℕ) :
    Real.exp (cutoff N / 2) = bandFrequency N := by
  unfold cutoff bandFrequency
  rw [← Real.log_sqrt (by positivity), Real.exp_log (Real.sqrt_pos.2 (by positivity))]

theorem cutoff_eq_two_mul_log_bandFrequency (N : ℕ) :
    cutoff N = 2 * Real.log (bandFrequency N) := by
  unfold cutoff bandFrequency
  rw [Real.log_sqrt (by positivity)]; ring

/-- `L ≤ 4 √(bandFrequency N)`. -/
theorem cutoff_le_four_mul_sqrt_bandFrequency (N : ℕ) :
    cutoff N ≤ 4 * Real.sqrt (bandFrequency N) := by
  rw [cutoff_eq_two_mul_log_bandFrequency]
  have h := Real.log_le_rpow_div (bandFrequency_pos N).le (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at h
  linarith

theorem cutoff_sq_le_sixteen_mul_bandFrequency (N : ℕ) :
    cutoff N ^ 2 ≤ 16 * bandFrequency N := by
  have h := cutoff_le_four_mul_sqrt_bandFrequency N
  have h0 := cutoff_nonneg N
  have hs := Real.sq_sqrt (bandFrequency_pos N).le
  nlinarith [Real.sqrt_nonneg (bandFrequency N)]

theorem cutoff_le_four_mul_bandFrequency (N : ℕ) : cutoff N ≤ 4 * bandFrequency N := by
  have h := cutoff_le_four_mul_sqrt_bandFrequency N
  have hb := one_le_bandFrequency N
  have : Real.sqrt (bandFrequency N) ≤ bandFrequency N :=
    (Real.sqrt_le_left (bandFrequency_pos N).le).2 (by nlinarith)
  linarith

/-! ## The band theorem -/

/-- **The band theorem, explicit form.** -/
theorem laplaceEnergy_le_band_add_explicit (N : ℕ) :
    laplaceEnergy N ≤ (∫ ξ in Icc (-bandFrequency N) (bandFrequency N), spectralDensity N ξ) +
      (2 * (cutoff N * (cutoff N + (Real.log 4 + 4))) / (π ^ 2 * bandFrequency N) +
        52 * (cutoff N * ((Real.log 4 + 4) * ((N + 2 : ℕ) : ℝ))) / (π ^ 3 * bandFrequency N ^ 2) +
        4 * (bandFrequency N + 3) ^ 2 / (3 * (2 * π) ^ 4 * bandFrequency N ^ 3)) := by
  have hb := bandFrequency_pos N
  have h := laplaceEnergy_le_band_add_remainder N hb
  rw [exp_half_cutoff_eq_bandFrequency] at h
  refine h.trans (add_le_add le_rfl (add_le_add (add_le_add ?_ ?_) le_rfl))
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (atomicDiagonal_le_cutoff_mul N) (by norm_num)) (by positivity)
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (atomicSecondMoment_le_cutoff_mul N) (by norm_num)) (by positivity)

/-- The explicit remainder is `(52(log 4 + 4)/π³) L + (32 + 8(log 4 + 4))/π² + 4/(3π⁴)`. -/
theorem band_remainder_le (N : ℕ) :
    2 * (cutoff N * (cutoff N + (Real.log 4 + 4))) / (π ^ 2 * bandFrequency N) +
        52 * (cutoff N * ((Real.log 4 + 4) * ((N + 2 : ℕ) : ℝ))) / (π ^ 3 * bandFrequency N ^ 2) +
        4 * (bandFrequency N + 3) ^ 2 / (3 * (2 * π) ^ 4 * bandFrequency N ^ 3) ≤
      52 * (Real.log 4 + 4) / π ^ 3 * cutoff N + (32 + 8 * (Real.log 4 + 4)) / π ^ 2 +
        4 / (3 * π ^ 4) := by
  set b := bandFrequency N with hbdef
  set L := cutoff N with hLdef
  set c : ℝ := Real.log 4 + 4 with hc
  have hb : 0 < b := bandFrequency_pos N
  have hb1 : 1 ≤ b := one_le_bandFrequency N
  have hL0 : 0 ≤ L := cutoff_nonneg N
  have hc0 : 0 < c := by rw [hc]; positivity
  have hπ : 0 < π := Real.pi_pos
  have hL2 : L ^ 2 ≤ 16 * b := cutoff_sq_le_sixteen_mul_bandFrequency N
  have hLb : L ≤ 4 * b := cutoff_le_four_mul_bandFrequency N
  -- first term
  have h1 : 2 * (L * (L + c)) / (π ^ 2 * b) ≤ (32 + 8 * c) / π ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 * (L * (L + c)) ≤ (32 + 8 * c) * b := by nlinarith
    nlinarith [sq_nonneg π]
  -- second term: exact cancellation `b² = N + 2`
  have h2 : 52 * (L * (c * ((N + 2 : ℕ) : ℝ))) / (π ^ 3 * b ^ 2) = 52 * c / π ^ 3 * L := by
    rw [← bandFrequency_sq N]
    field_simp
    ring
  -- third term
  have h3 : 4 * (b + 3) ^ 2 / (3 * (2 * π) ^ 4 * b ^ 3) ≤ 4 / (3 * π ^ 4) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hb3 : (b + 3) ^ 2 ≤ 16 * b ^ 2 := by nlinarith
    have hb4 : b ^ 2 ≤ b ^ 3 := by nlinarith [sq_nonneg b]
    have hπ4 : 0 < π ^ 4 := by positivity
    nlinarith [mul_pos hπ4 hb, mul_nonneg hπ4.le (sub_nonneg.2 hb4),
      mul_nonneg hπ4.le (sub_nonneg.2 hb3)]
  rw [h2]
  linarith

/-- **The band theorem:** `laplaceEnergy N ≤ ∫_{|ξ|≤√(N+2)} S_N + (52(log 4+4)/π³) L + C₀`. -/
theorem laplaceEnergy_le_band_add_linear (N : ℕ) :
    laplaceEnergy N ≤ (∫ ξ in Icc (-bandFrequency N) (bandFrequency N), spectralDensity N ξ) +
      (52 * (Real.log 4 + 4) / π ^ 3 * cutoff N + (32 + 8 * (Real.log 4 + 4)) / π ^ 2 +
        4 / (3 * π ^ 4)) :=
  (laplaceEnergy_le_band_add_explicit N).trans (add_le_add le_rfl (band_remainder_le N))

/-- The band energy never exceeds the Laplace energy. -/
theorem band_le_laplaceEnergy (N : ℕ) {ξ₀ : ℝ} :
    (∫ ξ in Icc (-ξ₀) ξ₀, spectralDensity N ξ) ≤ laplaceEnergy N := by
  rw [laplaceEnergy_eq_integral_spectralDensity]
  exact setIntegral_le_integral (integrable_spectralDensity N)
    (Eventually.of_forall fun ξ => spectralDensity_nonneg N ξ)

/-! ## Wall 1 in the field: mean-square Chebyshev error ⟺ band energy -/

/-- **The mean-square Chebyshev error is controlled by the band energy up to `O(L)`.** -/
theorem chebyshev_mean_square_le_band_add_linear (N : ℕ) :
    (∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2) ≤
      2 * (∫ ξ in Icc (-bandFrequency N) (bandFrequency N), spectralDensity N ξ) +
        (104 * (Real.log 4 + 4) / π ^ 3 * cutoff N +
          (2 * (32 + 8 * (Real.log 4 + 4)) / π ^ 2 + 8 / (3 * π ^ 4) + 2)) := by
  have h1 := chebyshev_mean_square_le_laplaceEnergy N
  have h2 := laplaceEnergy_le_band_add_linear N
  have e : 2 * (52 * (Real.log 4 + 4) / π ^ 3 * cutoff N + (32 + 8 * (Real.log 4 + 4)) / π ^ 2 +
      4 / (3 * π ^ 4)) + 2 = 104 * (Real.log 4 + 4) / π ^ 3 * cutoff N +
        (2 * (32 + 8 * (Real.log 4 + 4)) / π ^ 2 + 8 / (3 * π ^ 4) + 2) := by ring
  linarith

/-- **The band energy is controlled by the mean-square Chebyshev error up to `O(1)`.** -/
theorem band_le_chebyshev_mean_square (N : ℕ) :
    (∫ ξ in Icc (-bandFrequency N) (bandFrequency N), spectralDensity N ξ) ≤
      2 * (∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2) + 2 +
        (normalizedLogError (cutoff N) + (1 - cutoff N) * Real.exp (-cutoff N / 2)) ^ 2 :=
  (band_le_laplaceEnergy N).trans (laplaceEnergy_le_chebyshev_mean_square N)

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
