import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeTraceAtAPrimaryPrimeReadsTheDilateCorrelation

/-!
# The twisted cosets of the Hecke trace read the dilate correlation

The phased low–low cosets of the Hecke trace at a primary prime `p` carry, at the frequency `k`, the weight

`C(k) = Σ_{y≢0} (3y/p)₃ e(−ξ_k·3β_y/p)`   (`twistedCoeff`),

with `9yβ_y ≡ −1 mod p`. Substituting `u = (81y)⁻¹` (so that `(3y/p)₃ = χ(u)²` and `e(−ξ_k·3β_y/p) = ψ_{9k}(u)`)
turns it into the quadratic-character Gauss sum `C(k) = g(χ², 9k)` (`twistedCoeff_eq_gauss`). Patterson's relation
at `p`, `T(kp) = g(χ², 9k)T(k)/|p|`, then reads the twisted cosets as the **dilate correlation**
(`twistedCoeff_mul_sq`):

`C(k) T(k)² = |p| T(k) T(kp)` for `p ∤ k`,  `C(k) = 0` for `p ∣ k`.

Hence (`integral_sourceHeckeTrace_bessel`) the constant term of the Hecke trace is

`∫_P Tr_pθ_s = N(p)|P| (2c²v^{4/3} + 2|p|^{−2}R_{p²}(|p|v) + |p| R_{dil}(v/|p|))`,

`R_{p²}` the Bessel series of `T(h)T(−p²h)` and `R_{dil}` that of `T(k)T(kp)` (`p ∤ k`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### The Gauss sum of the twisted cosets -/

/-- The cubic character `χ_p` of `O/p`. -/
abbrev chi : MulChar P.Res ℂ := primeCubicMulChar P.p P.prime P.primary

/-- The trace character `ψ_h` of `O/p` at the frequency `h`. -/
abbrev psi (h : O) : AddChar P.Res ℂ := residueTraceQuotientChar h P.p P.ne_zero

theorem chi_res (d : O) : P.chi (P.res d) = ringComplex (symbol d P.p) :=
  primeCubicMulChar_mk P.p P.prime P.primary d

theorem chi_cube (u : P.Res) (hu : u ≠ 0) : P.chi u ^ 3 = 1 := by
  have h : (P.chi ^ 3) u = (1 : MulChar P.Res ℂ) u := by rw [primeCubicMulChar_cube]
  rwa [MulChar.pow_apply' _ (by norm_num), MulChar.one_apply hu.isUnit] at h

theorem eightyOne_ne_zero' : (81 : P.Res) ≠ 0 := by
  have := pow_ne_zero 4 P.three_ne_zero'
  norm_num at this
  exact this

theorem phase_eq_psi (k β : O) :
    tracePhase (cuspFrequency k * (-(3 * ringComplex β) / ringComplex P.p)) = P.psi k (P.res (-β)) := by
  rw [psi, residueTraceQuotientChar_mk]
  unfold residueAdditive
  congr 1
  simp only [cuspFrequency, map_mul, map_neg, map_ofNat]
  ring

theorem res_neg_lowBeta (y : O) (hy : ¬ P.p ∣ y) : P.res (-P.lowBeta y) = (9 * P.res y)⁻¹ := by
  have h := congrArg P.res (P.low_det y hy)
  simp only [map_sub, map_mul, map_one, P.res_p, zero_mul, zero_sub, res_nine] at h
  apply eq_inv_of_mul_eq_one_left
  rw [map_neg]
  linear_combination h

theorem psi_nine (k : O) (r : P.Res) : P.psi k r = P.psi (9 * k) (r / 9) := by
  rw [psi, psi, residueTraceQuotientChar_mulShift, residueTraceQuotientChar_mulShift (9 * k),
    AddChar.mulShift_apply, AddChar.mulShift_apply]
  congr 1
  have h9 := P.nine_ne_zero'
  rw [map_mul, show (Ideal.Quotient.mk (Ideal.span {P.p})) (9 : O) = 9 from map_ofNat _ 9]
  field_simp

/-- The weight `C(k) = Σ_{y≢0} (3y/p)₃ e(−ξ_k·3β_y/p)` of the twisted cosets. -/
def twistedCoeff (k : O) : ℂ :=
  ∑ y : {y : P.Res // y ≠ 0}, ringComplex (symbol (3 * P.lift y.1) P.p) *
    tracePhase (cuspFrequency k * (-(3 * ringComplex (P.lowBeta (P.lift y.1))) / ringComplex P.p))

theorem chi_three_mul (y : P.Res) (hy : y ≠ 0) : P.chi (3 * y) = (P.chi ^ 2) ((81 * y)⁻¹) := by
  have h3 := P.three_ne_zero'
  have h81 : (81 : P.Res) * y ≠ 0 := mul_ne_zero (by
    have := pow_ne_zero 4 h3
    norm_num at this
    exact this) hy
  rw [MulChar.pow_apply' _ (by norm_num), ← map_pow]
  have h1 : P.chi (3 * y) * P.chi ((81 * y) ^ 2) = 1 := by
    rw [← map_mul, show 3 * y * (81 * y) ^ 2 = (27 * y) ^ 3 by ring, map_pow,
      P.chi_cube _ (mul_ne_zero (by
        have := pow_ne_zero 3 h3
        norm_num at this
        exact this) hy)]
  have h81' := P.eightyOne_ne_zero'
  have h2 : P.chi (((81 * y)⁻¹) ^ 2) * P.chi ((81 * y) ^ 2) = 1 := by
    rw [← map_mul, show ((81 * y)⁻¹) ^ 2 * (81 * y) ^ 2 = 1 by field_simp, MulChar.map_one]
  have hne : P.chi ((81 * y) ^ 2) ≠ 0 := right_ne_zero_of_mul_eq_one h1
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

/-- **The twisted cosets carry the Gauss sum of `χ²`.** `C(k) = g(χ², 9k)`. -/
theorem twistedCoeff_eq_gauss (k : O) :
    P.twistedCoeff k = primeCubicGauss P.p P.prime P.primary 2 (9 * k) := by
  rw [primeCubicGauss_eq_gaussSum, gaussSum]
  have h9 := P.nine_ne_zero'
  have h81 := P.eightyOne_ne_zero'
  have hterm : ∀ y : {y : P.Res // y ≠ 0}, ringComplex (symbol (3 * P.lift y.1) P.p) *
      tracePhase (cuspFrequency k * (-(3 * ringComplex (P.lowBeta (P.lift y.1))) / ringComplex P.p)) =
      (P.chi ^ 2) ((81 * y.1)⁻¹) * P.psi (9 * k) ((81 * y.1)⁻¹) := by
    intro y
    rw [← P.chi_res, map_mul, res_lift, res_three, P.phase_eq_psi,
      P.res_neg_lowBeta _ (P.not_dvd_lift y), res_lift, P.psi_nine, P.chi_three_mul _ y.2]
    congr 2
    field_simp
    ring
  unfold twistedCoeff
  simp_rw [hterm]
  let e : {y : P.Res // y ≠ 0} ≃ {u : P.Res // u ≠ 0} :=
    { toFun := fun y => ⟨(81 * y.1)⁻¹, inv_ne_zero (mul_ne_zero (by
          have := pow_ne_zero 4 P.three_ne_zero'
          norm_num at this
          exact this) y.2)⟩
      invFun := fun u => ⟨(81 * u.1)⁻¹, inv_ne_zero (mul_ne_zero (by
          have := pow_ne_zero 4 P.three_ne_zero'
          norm_num at this
          exact this) u.2)⟩
      left_inv := fun y => by
        apply Subtype.ext
        have h81 : (81 : P.Res) ≠ 0 := by
          have := pow_ne_zero 4 P.three_ne_zero'
          norm_num at this
          exact this
        simp only
        field_simp
      right_inv := fun u => by
        apply Subtype.ext
        have h81 : (81 : P.Res) ≠ 0 := by
          have := pow_ne_zero 4 P.three_ne_zero'
          norm_num at this
          exact this
        simp only
        field_simp }
  rw [Fintype.sum_equiv e (fun y => (P.chi ^ 2) ((81 * y.1)⁻¹) * P.psi (9 * k) ((81 * y.1)⁻¹))
    (fun u => (P.chi ^ 2) u.1 * P.psi (9 * k) u.1) (fun y => rfl)]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun u : P.Res => u ≠ 0)) (by simp)
    (fun u => (P.chi ^ 2) u * P.psi (9 * k) u)]
  refine Finset.sum_filter_of_ne fun u _ hu => ?_
  intro h0
  rw [h0, MulChar.map_zero, zero_mul] at hu
  exact hu rfl

/-- **Patterson at `p` reads the twisted cosets as the dilate correlation.** -/
theorem twistedCoeff_mul (k : O) (hk : ¬ P.p ∣ k) :
    P.twistedCoeff k * rationalSourceResidualFourierCoefficient k =
      (‖ringComplex P.p‖ : ℂ) * rationalSourceResidualFourierCoefficient (k * P.p) := by
  have hP : (‖ringComplex P.p‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr P.norm_pos.ne'
  rw [P.twistedCoeff_eq_gauss, rationalSourceResidualFourierCoefficient_prime_factor P.p P.prime P.primary k hk]
  field_simp

theorem twistedCoeff_of_dvd (k : O) (hk : P.p ∣ k) : P.twistedCoeff k = 0 := by
  rw [P.twistedCoeff_eq_gauss, primeCubicGauss_of_dvd P.p P.prime P.primary 2 (9 * k) (hk.mul_left 9)]
  norm_num

/-- The dilate correlation coefficient `T(k)T(kp)` (`0` for `p ∣ k`). -/
def dilateCoeff (k : O) : ℂ :=
  if P.p ∣ k then 0 else rationalSourceResidualFourierCoefficient k * rationalSourceResidualFourierCoefficient (k * P.p)

theorem twistedCoeff_mul_sq (k : O) :
    P.twistedCoeff k * rationalSourceResidualFourierCoefficient k ^ 2 = (‖ringComplex P.p‖ : ℂ) * P.dilateCoeff k := by
  by_cases hk : P.p ∣ k
  · rw [P.twistedCoeff_of_dvd k hk, dilateCoeff, if_pos hk]
    ring
  · rw [dilateCoeff, if_neg hk, pow_two, ← mul_assoc, P.twistedCoeff_mul k hk]
    ring

end PrimaryPrime


namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### The constant term as Bessel series -/

/-- The shifted square `T(h) T(−p²h)`. -/
def shiftSqCoeff (h : O) : ℂ :=
  rationalSourceResidualFourierCoefficient h * rationalSourceResidualFourierCoefficient (-(h * P.p) * P.p)

theorem sum_twisted_conv (v : ℝ) (hv : 0 < v) :
    ∑ y : {y : P.Res // y ≠ 0}, ringComplex (symbol (3 * P.lift y.1) P.p) *
        cuspConv (P.shiftedLow v (P.lowBeta (P.lift y.1))) (rationalSourceModeAmplitude (v / ‖ringComplex P.p‖)) 0 =
      ∑' k : O, P.twistedCoeff k * (rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) k *
        rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-k)) := by
  have hb : Summable (fun h => ‖rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) h‖) :=
    rationalSourceModeAmplitude_summable _ (div_pos hv P.norm_pos)
  have hs : ∀ y : {y : P.Res // y ≠ 0}, Summable (fun k => ringComplex (symbol (3 * P.lift y.1) P.p) *
      (P.shiftedLow v (P.lowBeta (P.lift y.1)) k * rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (0 - k))) := by
    intro y
    refine Summable.mul_left _ (Summable.of_norm_bounded
      (hb.mul_right (∑' j, ‖rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) j‖)) fun k => ?_)
    rw [norm_mul, shiftedLow, norm_mul, tracePhase_norm, mul_one]
    exact mul_le_mul_of_nonneg_left (hb.le_tsum _ fun j _ => norm_nonneg _) (norm_nonneg _)
  simp only [cuspConv, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun y _ => hs y)]
  refine tsum_congr fun k => ?_
  simp only [twistedCoeff, Finset.sum_mul, shiftedLow, zero_sub]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **The twisted cosets are the dilate correlation.** -/
theorem twisted_series_eq (v : ℝ) (hv : 0 < v) :
    ∑' k : O, P.twistedCoeff k * (rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) k *
        rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-k)) =
      (‖ringComplex P.p‖ : ℂ) * besselRemainder P.dilateCoeff (v / ‖ringComplex P.p‖) := by
  rw [besselRemainder, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · rw [if_pos hk, hk, P.twistedCoeff_of_dvd 0 (dvd_zero _)]
    ring
  · rw [if_neg hk, sourceAmplitude_mul_neg _ (div_pos hv P.norm_pos) k hk, besselSq,
      show P.twistedCoeff k * (rationalSourceResidualFourierCoefficient k ^ 2 * ((v / ‖ringComplex P.p‖ : ℝ) : ℂ) ^ 2 *
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency k‖ * (v / ‖ringComplex P.p‖)) ^ 2) =
        (P.twistedCoeff k * rationalSourceResidualFourierCoefficient k ^ 2) *
          (((v / ‖ringComplex P.p‖ : ℝ) : ℂ) ^ 2 *
            schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency k‖ * (v / ‖ringComplex P.p‖)) ^ 2) by ring,
      P.twistedCoeff_mul_sq]
    ring

theorem cpow_mul_mul_cpow_div (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    ((a * v : ℝ) : ℂ) ^ (2 / 3 : ℂ) * ((v / a : ℝ) : ℂ) ^ (2 / 3 : ℂ) = (v : ℂ) ^ (4 / 3 : ℂ) := by
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    show ((a * v : ℝ) : ℂ) * ((v / a : ℝ) : ℂ) = (v : ℂ) * (v : ℂ) by
      push_cast; field_simp [Complex.ofReal_ne_zero.mpr ha.ne'],
    Complex.mul_cpow_ofReal_nonneg hv.le hv.le, ← Complex.cpow_add _ _ hv0]
  norm_num

theorem norm_cuspFrequency_dilate (h : O) :
    ‖cuspFrequency (-(h * P.p) * P.p)‖ = ‖cuspFrequency h‖ * ‖ringComplex P.p‖ ^ 2 := by
  rw [cuspFrequency_mul_right, cuspFrequency_neg, norm_mul, norm_neg, cuspFrequency_mul_right, norm_mul]
  ring

/-- **The dilate terms are the shifted square at `p²`.** -/
theorem shift_series_eq (v : ℝ) (hv : 0 < v) :
    ∑' h : O, rationalSourceModeAmplitude (‖ringComplex P.p‖ * v) h *
        rationalSourceModeAmplitude (v / ‖ringComplex P.p‖) (-(h * P.p) * P.p) =
      thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) +
        ((‖ringComplex P.p‖ : ℂ) ^ 2)⁻¹ * besselRemainder P.shiftSqCoeff (‖ringComplex P.p‖ * v) := by
  have hp := P.norm_pos
  have hpc : (‖ringComplex P.p‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hs := summable_amplitude_mul (rationalSourceModeAmplitude_summable (‖ringComplex P.p‖ * v) (mul_pos hp hv))
    (rationalSourceModeAmplitude_summable (v / ‖ringComplex P.p‖) (div_pos hv hp)) (fun h => -(h * P.p) * P.p)
  rw [hs.tsum_eq_add_tsum_ite 0, besselRemainder, ← tsum_mul_left]
  congr 1
  · rw [zero_mul, neg_zero, zero_mul, rationalSourceModeAmplitude_zero, rationalSourceModeAmplitude_zero,
      ← cpow_mul_mul_cpow_div _ v hp hv]
    push_cast
    ring
  · refine tsum_congr fun h => ?_
    by_cases hh : h = 0
    · simp [hh]
    · have hh' : -(h * P.p) * P.p ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hh P.ne_zero)) P.ne_zero
      rw [if_neg hh, if_neg hh, rationalSourceModeAmplitude_bessel _ (mul_pos hp hv) h hh,
        rationalSourceModeAmplitude_bessel _ (div_pos hv hp) _ hh', P.norm_cuspFrequency_dilate, shiftSqCoeff,
        besselSq]
      have e : 4 * Real.pi * (‖cuspFrequency h‖ * ‖ringComplex P.p‖ ^ 2) * (v / ‖ringComplex P.p‖) =
          4 * Real.pi * ‖cuspFrequency h‖ * (‖ringComplex P.p‖ * v) := by
        field_simp
      rw [e]
      push_cast
      field_simp

/-- **The constant term of the Hecke trace at `p` in Bessel form.** -/
theorem integral_sourceHeckeTrace_bessel (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.sourceHeckeTrace (upperPoint z v hv) =
      (Fintype.card P.Res : ℂ) * periodArea *
        (2 * (thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) +
            ((‖ringComplex P.p‖ : ℂ) ^ 2)⁻¹ * besselRemainder P.shiftSqCoeff (‖ringComplex P.p‖ * v)) +
          (‖ringComplex P.p‖ : ℂ) * besselRemainder P.dilateCoeff (v / ‖ringComplex P.p‖)) := by
  rw [P.integral_sourceHeckeTrace v hv, P.sum_twisted_conv v hv, P.twisted_series_eq v hv, P.shift_series_eq v hv]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
