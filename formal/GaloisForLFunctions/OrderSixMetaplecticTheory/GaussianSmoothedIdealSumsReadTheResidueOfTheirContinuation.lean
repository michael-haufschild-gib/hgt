import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUntwistedThetaSeriesHasASmoothedMainTerm

/-!
# Gaussian-smoothed ideal sums read the residue of their continuation

Let `a` be a coefficient on the ideals of `ℤ[ω]`, of norm at most one and zero on the ideals without a
primary generator. The sum `Σ_A a(A) g(log(N(A)/X))`, `g(x) = e^{−x²/4}/(2√π)`, is the inverse Mellin
integral of `X^w e^{w²} Σ_A a(A)N(A)^{−w}` on every line `Re w = c > 1` (`gaussianSmoothedSum_eq_integral`).
If the series continues to the closed strip `a₀ ≤ Re w ≤ 2` with one simple pole at `2/3` of residue `R`,
and `e^{w²}` times the continuation is `O((1 + Im² w)^{−1})`, the contour moves to `Re w = a₀`: the sum is
`e^{4/9} R X^{2/3} + O(X^{a₀})` (`gaussianSmoothedSum_main_term`). Growth `(1 + |w|)^k e^{4π|Im w|}` is
absorbed by the Gaussian (`gaussian_bound_of_exp_growth`).
-/

noncomputable section
open MeasureTheory Filter Topology Complex

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
  SpectralTheoryOfTheCubicCover

/-- `Σ_A N(A)^{−w} a(A)` over the ideals with a primary generator. -/
def idealSeries (a : Ideal O → ℂ) (w : ℂ) : ℂ := ∑' A : Ideal O, unramifiedNormWeight w A * a A

/-- `Σ_A a(A) g(log(N(A)/X))` with the logarithmic Gaussian `g`. -/
def gaussianSmoothedSum (a : Ideal O → ℂ) (X : ℝ) : ℂ :=
  ∑' A : Ideal O, a A * (RHTower.smoothAFELogGaussian (Real.log ((Ideal.absNorm A : ℝ) / X)) : ℂ)

/-- A coefficient of norm at most one, zero on the ideals without a primary generator. -/
structure BoundedIdealCoefficient (a : Ideal O → ℂ) : Prop where
  norm_le : ∀ A, ‖a A‖ ≤ 1
  of_bad : ∀ A, primaryIdealGenerator A = 0 → a A = 0

private def lineTerm (a : Ideal O → ℂ) (c X : ℝ) (A : Ideal O) (t : ℝ) : ℂ :=
  ((X : ℂ) ^ ((c : ℂ) + t * I) * Complex.exp (((c : ℂ) + t * I) ^ 2)) *
    (unramifiedNormWeight ((c : ℂ) + t * I) A * a A)

private def perron (L : ℂ → ℂ) (X : ℝ) (w : ℂ) : ℂ := (X : ℂ) ^ w * (Complex.exp (w ^ 2) * L w)

private theorem gaussian_majorant : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
  simpa only [neg_one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)

private theorem cpow_scale (s : ℂ) {N X : ℝ} (hN : 0 < N) (hX : 0 < X) :
    (X : ℂ) ^ s * (N : ℂ) ^ (-s) = ((N / X : ℝ) : ℂ) ^ (-s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hX).ne'),
    ← Complex.ofReal_log hX.le, ← Complex.ofReal_log hN.le,
    ← Complex.ofReal_log (div_pos hN hX).le, Real.log_div hN.ne' hX.ne',
    Complex.ofReal_sub, ← Complex.exp_add]
  congr 1
  ring

/-- Growth `(1 + |w|)^k e^{4π|Im w|}` on a strip `0 ≤ a ≤ Re w ≤ B` is absorbed by `e^{w²}`. -/
theorem gaussian_bound_of_exp_growth {f : ℂ → ℂ} {a B C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (k : ℕ)
    (hf : ∀ w : ℂ, a ≤ w.re → w.re ≤ B → 1 ≤ |w.im| →
      ‖f w‖ ≤ C * (1 + ‖w‖) ^ k * Real.exp (4 * Real.pi * |w.im|)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ B → 1 ≤ |w.im| →
      ‖Complex.exp (w ^ 2) * f w‖ ≤ C' * (1 + w.im ^ 2)⁻¹ := by
  let B' : ℝ := max B 0
  have hB0 : 0 ≤ B' := le_max_right _ _
  let E : ℝ := B' ^ 2 + (4 * Real.pi + ((k + 2 : ℕ) : ℝ)) ^ 2 / 4
  refine ⟨C * (1 + B') ^ k * Real.exp E,
    mul_nonneg (mul_nonneg hC (pow_nonneg (by linarith) _)) (Real.exp_pos _).le, ?_⟩
  intro w hwa hwb hwi
  have hwb' : w.re ≤ B' := hwb.trans (le_max_left _ _)
  let t : ℝ := |w.im|
  have ht : 0 ≤ t := abs_nonneg _
  have ht2 : t ^ 2 = w.im ^ 2 := sq_abs _
  have hw0 : 0 ≤ w.re := ha.trans hwa
  have hn : 1 + ‖w‖ ≤ (1 + B') * (1 + t) := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    rw [abs_of_nonneg hw0] at h
    nlinarith only [h, hwb', mul_nonneg hB0 ht]
  have hsq : w.re ^ 2 ≤ B' ^ 2 := by nlinarith only [hw0, hwb']
  have htwo : 1 + t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith only [ht]
  have hnorm : ‖Complex.exp (w ^ 2)‖ = Real.exp (w.re ^ 2 - t ^ 2) := by
    rw [Complex.norm_exp, ht2]
    congr 1
    simp only [pow_two, Complex.mul_re]
  have hgeom : (1 + t) ^ (k + 2) * Real.exp (4 * Real.pi * t) *
      Real.exp (w.re ^ 2 - t ^ 2) ≤ Real.exp E := by
    calc
      _ ≤ Real.exp (((k + 2 : ℕ) : ℝ) * t) * Real.exp (4 * Real.pi * t) *
          Real.exp (w.re ^ 2 - t ^ 2) := by
        gcongr
        exact GaloisForLFunctions.one_add_pow_le_exp ht (k + 2)
      _ = Real.exp (w.re ^ 2 - t ^ 2 + (4 * Real.pi + ((k + 2 : ℕ) : ℝ)) * t) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp E := by
        apply Real.exp_le_exp.mpr
        dsimp only [E]
        linarith only [hsq, GaloisForLFunctions.neg_sq_add_mul_le t (4 * Real.pi + ((k + 2 : ℕ) : ℝ))]
  have hser : ‖f w‖ ≤ C * ((1 + B') * (1 + t)) ^ k * Real.exp (4 * Real.pi * t) :=
    (hf w hwa hwb hwi).trans (by gcongr)
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + w.im ^ 2), ← ht2, norm_mul, hnorm]
  calc
    _ ≤ Real.exp (w.re ^ 2 - t ^ 2) *
        (C * ((1 + B') * (1 + t)) ^ k * Real.exp (4 * Real.pi * t)) * (1 + t) ^ 2 := by
      gcongr
    _ = C * (1 + B') ^ k * ((1 + t) ^ (k + 2) * Real.exp (4 * Real.pi * t) *
        Real.exp (w.re ^ 2 - t ^ 2)) := by rw [mul_pow]; ring
    _ ≤ C * (1 + B') ^ k * Real.exp E :=
      mul_le_mul_of_nonneg_left hgeom (mul_nonneg hC (pow_nonneg (by linarith) _))

namespace BoundedIdealCoefficient

variable {a : Ideal O → ℂ} (ha : BoundedIdealCoefficient a)
include ha

/-- The series is holomorphic on `Re w > 1`. -/
theorem idealSeries_differentiableAt (w : ℂ) (hw : 1 < w.re) :
    DifferentiableAt ℂ (idealSeries a) w := by
  let c : ℝ := (1 + w.re) / 2
  have hc : 1 < c := by dsimp only [c]; linarith
  have hcw : c < w.re := by dsimp only [c]; linarith
  have hopen : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsum := unramifiedNormWeight_summable_norm (c : ℂ) (by simpa using hc)
  have hd : DifferentiableOn ℂ (fun z => ∑' A : Ideal O, unramifiedNormWeight z A * a A)
      {z : ℂ | c < z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun A => ((unramifiedNormWeight_differentiable A).mul_const _).differentiableOn) hopen
    intro A z hz
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (ha.norm_le A)).trans
      (unramifiedNormWeight_norm_mono c z hz.le A)
  exact (hd w hcw).differentiableAt (hopen.mem_nhds hcw)

private theorem norm_lineTerm_le (c : ℝ) {X : ℝ} (hX : 0 < X) (A : Ideal O) (t : ℝ) :
    ‖lineTerm a c X A t‖ ≤
      ‖unramifiedNormWeight (c : ℂ) A‖ * (X ^ c * Real.exp (c ^ 2)) * Real.exp (-(t ^ 2)) := by
  have hs : ((c : ℂ) + t * I).re = c := by simp
  have hsq : (((c : ℂ) + t * I) ^ 2).re = c ^ 2 - t ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hw := unramifiedNormWeight_norm_mono c ((c : ℂ) + t * I) hs.ge A
  rw [lineTerm, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX,
    hs, Complex.norm_exp, hsq, Real.exp_sub]
  have he : (Real.exp (t ^ 2))⁻¹ = Real.exp (-(t ^ 2)) := (Real.exp_neg _).symm
  rw [div_eq_mul_inv, he]
  calc
    _ ≤ X ^ c * (Real.exp (c ^ 2) * Real.exp (-(t ^ 2))) *
        (‖unramifiedNormWeight (c : ℂ) A‖ * 1) := by
      gcongr
      exact ha.norm_le A
    _ = _ := by ring

private theorem integrable_lineTerm (c : ℝ) {X : ℝ} (hX : 0 < X) (A : Ideal O) :
    Integrable (lineTerm a c X A) := by
  refine Integrable.mono'
    (gaussian_majorant.const_mul (‖unramifiedNormWeight (c : ℂ) A‖ * (X ^ c * Real.exp (c ^ 2)))) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hs : Continuous (fun t : ℝ => (c : ℂ) + t * I) := by fun_prop
    exact (((hs.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).mul
      (Complex.continuous_exp.comp (hs.pow 2))).mul
        (((unramifiedNormWeight_differentiable A).continuous.comp hs).mul continuous_const))
  · filter_upwards with t
    exact ha.norm_lineTerm_le c hX A t

private theorem integral_lineTerm (c : ℝ) {X : ℝ} (hX : 0 < X) (A : Ideal O) :
    (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ, lineTerm a c X A t) =
      a A * (RHTower.smoothAFELogGaussian (Real.log ((Ideal.absNorm A : ℝ) / X)) : ℂ) := by
  by_cases hA : primaryIdealGenerator A = 0
  · simp only [lineTerm, unramifiedNormWeight_of_bad _ A hA, ha.of_bad A hA, zero_mul, mul_zero,
      integral_zero, smul_zero]
  · have hN : 0 < (Ideal.absNorm A : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (primaryIdealGenerator_ne_zero_ideal A hA)))
    have he (t : ℝ) : lineTerm a c X A t = a A *
        ((((Ideal.absNorm A : ℝ) / X : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) *
          Complex.exp (((c : ℂ) + t * I) ^ 2)) := by
      rw [lineTerm, unramifiedNormWeight_of_good _ A hA, ← cpow_scale _ hN hX]
      simp only [Complex.ofReal_natCast]
      ring
    simp_rw [he]
    rw [integral_const_mul, Complex.real_smul, mul_left_comm, ← Complex.real_smul,
      integral_logGaussian_line c (div_pos hN hX)]

/-- **Mellin inversion.** For `c > 1`, the smoothed sum is `(2π)^{−1}∫ X^w e^{w²} Σ_A a(A)N(A)^{−w}` on
`Re w = c`. -/
theorem gaussianSmoothedSum_eq_integral (c : ℝ) (hc : 1 < c) {X : ℝ} (hX : 0 < X) :
    gaussianSmoothedSum a X =
      (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
        (X : ℂ) ^ ((c : ℂ) + t * I) * Complex.exp (((c : ℂ) + t * I) ^ 2) *
          idealSeries a ((c : ℂ) + t * I)) := by
  letI : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
  letI : Countable (Ideal O) := cubicIdealGenerator_injective.countable
  let K : ℝ := (X ^ c * Real.exp (c ^ 2)) * ∫ t : ℝ, Real.exp (-(t ^ 2))
  have hsum : Summable (fun A : Ideal O => ∫ t : ℝ, ‖lineTerm a c X A t‖) := by
    refine Summable.of_nonneg_of_le (fun A => integral_nonneg fun t => norm_nonneg _) (fun A => ?_)
      ((unramifiedNormWeight_summable_norm (c : ℂ) (by simpa using hc)).mul_right K)
    calc
      _ ≤ ∫ t : ℝ, ‖unramifiedNormWeight (c : ℂ) A‖ *
          (X ^ c * Real.exp (c ^ 2)) * Real.exp (-(t ^ 2)) := by
        apply integral_mono_ae (ha.integrable_lineTerm c hX A).norm
          (gaussian_majorant.const_mul _)
        filter_upwards with t
        exact ha.norm_lineTerm_le c hX A t
      _ = _ := by rw [integral_const_mul]; dsimp only [K]; ring
  have hi := (hasSum_integral_of_summable_integral_norm
    (fun A => ha.integrable_lineTerm c hX A) hsum).const_smul (1 / (2 * Real.pi) : ℝ)
  simp only [ha.integral_lineTerm c hX] at hi
  rw [gaussianSmoothedSum, hi.tsum_eq]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [lineTerm, idealSeries, tsum_mul_left]

/-- **The main term from a continuation.** If `L` continues `Σ_A a(A)N(A)^{−w}` from the line `Re w = 2` to
`a₀ ≤ Re w ≤ 2` with one simple pole at `2/3` of residue `R`, and `e^{w²}L(w) = O((1 + Im² w)^{−1})`, then
`Σ_A a(A) g(log(N(A)/X)) = e^{4/9} R X^{2/3} + O(X^{a₀})` for `X ≥ 1`. -/
theorem gaussianSmoothedSum_main_term {L : ℂ → ℂ} {R : ℂ} {a₀ C : ℝ} (ha₀ : a₀ < 2 / 3)
    (hL : ∀ w : ℂ, a₀ ≤ w.re → w.re ≤ 2 → w ≠ 2 / 3 → DifferentiableAt ℂ L w)
    (hres : Tendsto (fun w => (w - 2 / 3) * L w) (𝓝[≠] (2 / 3 : ℂ)) (𝓝 R))
    (hbd : ∀ w : ℂ, a₀ ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| →
      ‖Complex.exp (w ^ 2) * L w‖ ≤ C * (1 + w.im ^ 2)⁻¹)
    (hser : ∀ t : ℝ, L (2 + t * I) = idealSeries a (2 + t * I)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      ‖gaussianSmoothedSum a X - (X : ℂ) ^ (2 / 3 : ℂ) * (Complex.exp ((2 / 3 : ℂ) ^ 2) * R)‖ ≤
        K * X ^ a₀ := by
  have hres' : ∀ {X : ℝ}, 0 < X → Tendsto (fun w => (w - 2 / 3) * perron L X w) (𝓝[≠] (2 / 3 : ℂ))
      (𝓝 ((X : ℂ) ^ (2 / 3 : ℂ) * (Complex.exp ((2 / 3 : ℂ) ^ 2) * R))) := by
    intro X hX
    have hcont : ContinuousAt (fun w : ℂ => (X : ℂ) ^ w * Complex.exp (w ^ 2)) (2 / 3 : ℂ) :=
      (continuousAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).mul
        ((continuousAt_id.pow 2).cexp)
    have hlim := (hcont.tendsto.mono_left
      (show 𝓝[≠] (2 / 3 : ℂ) ≤ 𝓝 (2 / 3 : ℂ) from nhdsWithin_le_nhds)).mul hres
    rw [mul_assoc] at hlim
    exact hlim.congr fun w => by simp only [perron]; ring
  have hshift : ∀ {X : ℝ}, 1 ≤ X → (∫ t : ℝ, perron L X (2 + t * I)) -
      ∫ t : ℝ, perron L X ((a₀ : ℂ) + t * I) =
        2 * Real.pi * ((X : ℂ) ^ (2 / 3 : ℂ) * (Complex.exp ((2 / 3 : ℂ) ^ 2) * R)) := by
    intro X hX
    have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
    apply HTGeometry.integral_line_sub_integral_line_eq (a := a₀) (b := 2) (p := (2 / 3 : ℂ))
      (T₀ := 1) (C := X ^ (2 : ℝ) * C) (by simpa using ha₀) (by norm_num)
    · intro w hwa hw2 hp
      exact (differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX0.ne'))).mul
        (((differentiableAt_id.pow 2).cexp).mul (hL w hwa hw2 hp))
    · exact hres' hX0
    · intro w hwa hw2 hwi
      rw [perron, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      calc
        _ ≤ X ^ (2 : ℝ) * (C * (1 + w.im ^ 2)⁻¹) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le hX hw2) (hbd w hwa hw2 hwi)
            (norm_nonneg _) (Real.rpow_nonneg hX0.le _)
        _ = _ := by ring
  have hcontour : ∀ {X : ℝ}, 1 ≤ X → gaussianSmoothedSum a X -
      (X : ℂ) ^ (2 / 3 : ℂ) * (Complex.exp ((2 / 3 : ℂ) ^ 2) * R) =
        (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, perron L X ((a₀ : ℂ) + t * I) := by
    intro X hX
    have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
    have hinv := ha.gaussianSmoothedSum_eq_integral 2 (by norm_num) hX0
    have hright : (∫ t : ℝ, (X : ℂ) ^ ((2 : ℂ) + t * I) *
        Complex.exp (((2 : ℂ) + t * I) ^ 2) * idealSeries a ((2 : ℂ) + t * I)) =
        ∫ t : ℝ, perron L X (2 + t * I) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [perron, hser t]
      ring
    norm_num only [Complex.ofReal_ofNat] at hinv
    rw [hright, Complex.real_smul] at hinv
    rw [hinv, Complex.real_smul]
    have hsh := hshift hX
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have halg (A B M : ℂ) (h : A - B = 2 * Real.pi * M) :
        (1 / (2 * Real.pi) : ℂ) * A - M = (1 / (2 * Real.pi) : ℂ) * B := by
      field_simp
      linear_combination h
    simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one,
      Complex.ofReal_ofNat] using halg _ _ _ hsh
  have hκ : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
  refine ⟨(1 / (2 * Real.pi)) * ∫ t : ℝ,
      ‖Complex.exp (((a₀ : ℂ) + t * I) ^ 2) * L ((a₀ : ℂ) + t * I)‖,
    mul_nonneg hκ (integral_nonneg fun t => norm_nonneg _), fun X hX => ?_⟩
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  rw [hcontour hX, norm_smul, Real.norm_of_nonneg hκ]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖perron L X ((a₀ : ℂ) + t * I)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hκ
    _ = (1 / (2 * Real.pi)) * (X ^ a₀ * ∫ t : ℝ,
        ‖Complex.exp (((a₀ : ℂ) + t * I) ^ 2) * L ((a₀ : ℂ) + t * I)‖) := by
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      rw [perron, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      simp
    _ = _ := by ring

end BoundedIdealCoefficient

end GaloisForLFunctions.OrderSixMetaplecticTheory
