import GaloisForLFunctions.RHTower.ChiCubicMovingProfileFourier
import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeKernel

/-!
# Cancellation of every complete continuous prime-pair row

Every q in the original band is retained in the literal density integral.
The endpoint-window defect cancels the dangerous first inverse frequency;
the remaining inverse-square gap is summable over the actual prime pairs.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set Filter
open scoped Topology
open GaloisForLFunctions.RHTower

/-- The literal full-band continuous q-row. No hyperbolic or ordering cutoff. -/
def chiCubicPrimeFullPairIntegral (N : ℝ) (p r : ℕ) : ℂ :=
  ∫ x in N..(2 * N), chiCubicHyperbolicPrimeAmplitude N (p, r) x

private def rowCoefficient (N : ℝ) (p r : ℕ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) * smoothAFECutoff ((p : ℝ) / N) *
    (starRingEnd ℂ) (smoothAFECutoff ((r : ℝ) / N)) / (r : ℂ) / (Real.log N : ℂ)

private theorem amplitude_factor {N x : ℝ} (hN : 1 < N)
    (hx : x ∈ Icc N (2 * N)) (p r : ℕ) :
    chiCubicHyperbolicPrimeAmplitude N (p, r) x =
      rowCoefficient N p r * primeGaussianScaledLogProfile ((p : ℝ) / r) (1 / Real.log N) (x / N) *
        bourgainOscillation (2 * Real.pi * (((p : ℝ) - r) * (x - r) / r)) := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < x := hN0.trans_le hx.1
  have hL : (Real.log N : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hN).ne'
  unfold chiCubicHyperbolicPrimeAmplitude rowCoefficient
    primeGaussianScaledLogProfile primeGaussianScaledProfile
  rw [show (p : ℝ) / r * (x / N) = (p : ℝ) * x / ((r : ℝ) * N) by ring,
    Real.log_div hx0.ne' hN0.ne']
  push_cast only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one]
  have hden : 1 + 1 / (Real.log N : ℂ) * ((Real.log x : ℂ) - (Real.log N : ℂ)) =
      (Real.log x : ℂ) / (Real.log N : ℂ) := by field_simp; ring
  rw [hden, inv_div]
  field_simp [hL]

private theorem coefficient_norm {N : ℝ} (hN : 1 < N) {p r : ℕ}
    (hp : p ∈ primeProfileBand N) (hr : r ∈ primeProfileBand N) :
    ‖rowCoefficient N p r‖ ≤ 2 * Real.pi / (N * Real.log N) := by
  have hN0 : 0 < N := by linarith
  have hpN := (primeProfileBand_mem hN0.le hp).2.1
  have hrN := (primeProfileBand_mem hN0.le hr).2.1
  have hL := Real.log_pos hN
  have hpV := norm_smoothAFECutoff_le_one (div_pos (hN0.trans hpN) hN0)
  have hrV := norm_smoothAFECutoff_le_one (div_pos (hN0.trans hrN) hN0)
  simp only [rowCoefficient, norm_div, norm_mul, Complex.norm_conj, Complex.norm_natCast]
  rw [Complex.norm_of_nonneg (show 0 ≤ 2 * Real.pi by positivity),
    Complex.norm_of_nonneg hL.le]
  calc
    _ ≤ 2 * Real.pi * 1 * 1 / N / Real.log N := by gcongr
    _ = _ := by ring

private theorem full_integral_norm {N : ℝ} (hN : 1 < N) (p r : ℕ) :
    ‖chiCubicPrimeFullPairIntegral N p r‖ = N * ‖rowCoefficient N p r‖ *
      ‖∫ x in (1 : ℝ)..2, primeGaussianScaledLogProfile ((p : ℝ) / r) (1 / Real.log N) x *
        bourgainOscillation ((2 * Real.pi * N * ((p : ℝ) - r) / r) * x)‖ := by
  have hN0 : 0 < N := by linarith
  let a := chiCubicHyperbolicPrimeAmplitude N (p, r)
  have hi := intervalIntegral.integral_comp_mul_left (a := 1) (b := 2) a hN0.ne'
  simp only [mul_one, mul_comm N 2] at hi
  have hid : chiCubicPrimeFullPairIntegral N p r = N • (∫ x in (1 : ℝ)..2, a (N * x)) := by
    rw [hi, smul_smul, mul_inv_cancel₀ hN0.ne', one_smul]
    rfl
  have hfactor (x : ℝ) (hx : x ∈ uIcc (1 : ℝ) 2) :
      a (N * x) = (rowCoefficient N p r * bourgainOscillation (-2 * Real.pi * ((p : ℝ) - r))) *
        (primeGaussianScaledLogProfile ((p : ℝ) / r) (1 / Real.log N) x *
          bourgainOscillation ((2 * Real.pi * N * ((p : ℝ) - r) / r) * x)) := by
    have hx' : x ∈ Icc (1 : ℝ) 2 := by simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hx
    have hNx : N * x ∈ Icc N (2 * N) := by
      constructor <;> nlinarith [hx'.1, hx'.2]
    rw [show a (N * x) = chiCubicHyperbolicPrimeAmplitude N (p, r) (N * x) from rfl,
      amplitude_factor hN hNx p r, mul_div_cancel_left₀ x hN0.ne']
    by_cases hr : r = 0
    · subst r
      simp [rowCoefficient]
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    have he : 2 * Real.pi * (((p : ℝ) - r) * (N * x - r) / r) =
        -2 * Real.pi * ((p : ℝ) - r) + (2 * Real.pi * N * ((p : ℝ) - r) / r) * x := by
      field_simp
      ring
    rw [he]
    simp only [bourgainOscillation, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos hN0,
    intervalIntegral.integral_congr hfactor, intervalIntegral.integral_const_mul,
    norm_mul, norm_mul, norm_bourgainOscillation, mul_one]
  ring

/-- A single source constant pays EVERY complete continuous q-row, at ALL
nonzero prime gaps. Both moving band boundaries are retained. -/
theorem exists_chiCubicPrimeFullPairIntegral_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℝ, 1 < N → 1 ≤ Real.log N →
      ∀ p ∈ primeProfileBand N, ∀ r ∈ primeProfileBand N, p ≠ r →
        ‖chiCubicPrimeFullPairIntegral N p r‖ ≤
          K * (1 / (|(p : ℝ) - r| ^ 2 * Real.log N) + 1 / (N * Real.log N)) := by
  obtain ⟨C, hC, hfourier⟩ := exists_primeGaussianScaledLogProfile_fourier_bound
  let K := C + 2 * C / Real.pi
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro N hN hlog p hp r hr hne
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos hN
  have hpN := (primeProfileBand_mem hN0.le hp).2
  have hrN := (primeProfileBand_mem hN0.le hr).2
  have hr0 : (0 : ℝ) < r := hN0.trans hrN.1
  let d := |(p : ℝ) - r|
  have hd : 0 < d := abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast hne))
  let τ := 2 * Real.pi * N * ((p : ℝ) - r) / r
  have hτ : τ ≠ 0 := div_ne_zero (mul_ne_zero (by positivity)
    (sub_ne_zero.2 (by exact_mod_cast hne))) hr0.ne'
  have hξ : (p : ℝ) / r ∈ Icc (1 / 2 : ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hr0).2
      linarith [hpN.1, hrN.2]
    · apply (div_le_iff₀ hr0).2
      linarith [hpN.2, hrN.1]
  have hl : 1 / Real.log N ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hL).2 hlog⟩
  have hτabs : |τ| = 2 * Real.pi * N * d / r := by
    dsimp [τ, d]
    rw [abs_div, abs_mul, abs_of_pos hr0, abs_of_pos (by positivity : 0 < 2 * Real.pi * N)]
  have hξabs : |(p : ℝ) / r - 1| = d / r := by
    rw [← div_self hr0.ne', ← sub_div, abs_div, abs_of_pos hr0]
  have hratio : |(p : ℝ) / r - 1| / |τ| = 1 / (2 * Real.pi * N) := by
    rw [hτabs, hξabs]
    field_simp
  have hsecond : 1 / τ ^ 2 ≤ 1 / (Real.pi ^ 2 * d ^ 2) := by
    rw [← sq_abs τ, hτabs]
    calc
      _ = (r : ℝ) ^ 2 / (2 * Real.pi * N * d) ^ 2 := by field_simp
      _ ≤ (2 * N) ^ 2 / (2 * Real.pi * N * d) ^ 2 := by
        gcongr
        exact hrN.2
      _ = _ := by field_simp
  have hf := hfourier ((p : ℝ) / r) hξ (1 / Real.log N) hl τ hτ
  rw [full_integral_norm hN p r]
  calc
    _ ≤ N * (2 * Real.pi / (N * Real.log N)) *
        (C * (|(p : ℝ) / r - 1| / |τ| + 1 / τ ^ 2)) := by
      gcongr
      exact coefficient_norm hN hp hr
    _ ≤ N * (2 * Real.pi / (N * Real.log N)) *
        (C * (1 / (2 * Real.pi * N) + 1 / (Real.pi ^ 2 * d ^ 2))) := by
      rw [hratio]
      gcongr
    _ = C / (N * Real.log N) + (2 * C / Real.pi) / (d ^ 2 * Real.log N) := by
      field_simp
    _ ≤ K * (1 / (d ^ 2 * Real.log N) + 1 / (N * Real.log N)) := by
      have hcoeff : 0 < 2 * C / Real.pi := by positivity
      calc
        _ = C * (1 / (N * Real.log N)) + (2 * C / Real.pi) * (1 / (d ^ 2 * Real.log N)) := by ring
        _ ≤ K * (1 / (N * Real.log N)) + K * (1 / (d ^ 2 * Real.log N)) := by
          gcongr <;> dsimp [K] <;> linarith
        _ = _ := by ring

end RHTower
