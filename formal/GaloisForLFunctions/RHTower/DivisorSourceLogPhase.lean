import GaloisForLFunctions.RHTower.DivisorSourceEntire
import GaloisForLFunctions.HTGeometry.ShiftSpectrumFirstIndex

/-!
# The arithmetic phase of the literal divisor source

The first nonconstant Dirichlet coefficient fixes the logarithmic
derivative uniformly in height. This retains the vertical phase needed
when testing a signed Tatuzawa--Iseki response; no source passivity or
critical-energy admission is assumed.
-/

noncomputable section
open Complex Filter Topology
namespace RHTower

private abbrev sourceCoeff (n : ℕ) : ℂ := (primeFreeDivisorIncrement n : ℂ)

private theorem first_coefficient_pos : 0 < primeFreeDivisorIncrement 1 := by
  simp only [primeFreeDivisorIncrement, Nat.cast_one, Real.log_one,
    Nat.divisors_one, Finset.card_singleton]
  have h := Real.one_half_lt_eulerMascheroniConstant
  norm_num only [Nat.cast_one]
  linarith

private theorem second_coefficient_neg : primeFreeDivisorIncrement 2 < 0 := by
  have h := (harmonic_mascheroni_half_bounds (n := 2) (by norm_num)).1
  have hl : (2 / 3 : ℝ) < Real.log 2 := by
    convert Real.lt_log_one_add_of_pos (x := 1) (by norm_num) using 1 <;> norm_num
  norm_num [harmonic, Finset.sum_range_succ] at h
  norm_num [primeFreeDivisorIncrement, Nat.prime_two.divisors]
  linarith

/-- Exact, strictly positive amplitude of the first logarithmic source mode. -/
def divisorSourceLogPhaseCoefficient : ℝ :=
  -primeFreeDivisorIncrement 2 * Real.log 2 / primeFreeDivisorIncrement 1

theorem divisorSourceLogPhaseCoefficient_pos : 0 < divisorSourceLogPhaseCoefficient :=
  div_pos (mul_pos (neg_pos.mpr second_coefficient_neg) (Real.log_pos (by norm_num)))
    first_coefficient_pos

private theorem source_abscissa_le :
    LSeries.abscissaOfAbsConv sourceCoeff ≤ (1 : ℝ) :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_primeFreeDivisorIncrement_right (by simpa using hy)

private theorem source_deriv_eq {s : ℂ} (hs : 1 < s.re) :
    deriv divisorSourceEntire s = -LSeries (LSeries.logMul sourceCoeff) s := by
  have he : divisorSourceEntire =ᶠ[𝓝 s] LSeries sourceCoeff := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with z hz
    exact divisorSourceEntire_eq_LSeries hz
  rw [he.deriv_eq, LSeries_deriv (source_abscissa_le.trans_lt (by exact_mod_cast hs))]

/-- The literal entire source tends to its first coefficient uniformly in height. -/
theorem divisorSourceEntire_right_limit :
    Tendsto divisorSourceEntire (comap Complex.re atTop)
      (𝓝 (primeFreeDivisorIncrement 1 : ℂ)) := by
  have h := GaloisForLFunctions.HTGeometry.tendsto_LSeries_of_re_atTop
    (LSeriesSummable_primeFreeDivisorIncrement_right (s := 2) (by norm_num)).norm
    (w := fun s : ℂ => s) tendsto_comap
  apply h.congr'
  filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (1 : ℝ))] with s hs
  exact (divisorSourceEntire_eq_LSeries hs).symm

/-- The first nonconstant coefficient controls the derivative without restricting height. -/
theorem divisorSourceEntire_deriv_first_mode :
    Tendsto (fun s : ℂ => (2 : ℂ)^s * deriv divisorSourceEntire s)
      (comap Complex.re atTop)
      (𝓝 (-((primeFreeDivisorIncrement 2 : ℂ) * (Real.log 2 : ℂ)))) := by
  have habs : LSeries.abscissaOfAbsConv sourceCoeff < (2 : ℂ).re :=
    source_abscissa_le.trans_lt (by exact_mod_cast (show (1 : ℝ) < 2 by norm_num))
  have h := GaloisForLFunctions.HTGeometry.tendsto_cpow_mul_LSeries_of_re_atTop
    (LSeriesSummable_logMul_of_lt_re habs).norm (m := 2) (by norm_num)
    (by
      intro n hn hn2
      have : n = 1 := by omega
      simp [this, LSeries.logMul])
    (w := fun s : ℂ => s) tendsto_comap
  have hneg := h.neg
  have he : -(LSeries.logMul sourceCoeff 2) =
      -((primeFreeDivisorIncrement 2 : ℂ) * (Real.log 2 : ℂ)) := by
    simp [LSeries.logMul, mul_comm]
  rw [he] at hneg
  apply hneg.congr'
  filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (1 : ℝ))] with s hs
  rw [source_deriv_eq hs, mul_neg]
  norm_num only [Nat.cast_ofNat]

/-- Uniform arithmetic phase law for the actual logarithmic source response. -/
theorem divisorSourceEntire_logarithmic_first_mode :
    Tendsto (fun s : ℂ => (2 : ℂ)^s *
      (deriv divisorSourceEntire s / divisorSourceEntire s))
      (comap Complex.re atTop) (𝓝 (divisorSourceLogPhaseCoefficient : ℂ)) := by
  have hn : (primeFreeDivisorIncrement 1 : ℂ) ≠ 0 := by
    exact_mod_cast first_coefficient_pos.ne'
  have h := divisorSourceEntire_deriv_first_mode.div divisorSourceEntire_right_limit hn
  have he : -((primeFreeDivisorIncrement 2 : ℂ) * (Real.log 2 : ℂ)) /
      (primeFreeDivisorIncrement 1 : ℂ) = (divisorSourceLogPhaseCoefficient : ℂ) := by
    simp [divisorSourceLogPhaseCoefficient]
  rw [he] at h
  exact h.congr fun s => by
    change ((2 : ℂ)^s * deriv divisorSourceEntire s) / divisorSourceEntire s = _
    ring

end RHTower
