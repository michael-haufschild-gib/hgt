import GaloisForLFunctions.OrderSixMetaplecticTheory.TheSquarefreeRemainderReadsTheZerosOfTheCubeZeta
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheThetaGaussianSmoothingIsAnArithmeticSum

/-!
# The smoothed remainder reads the zeros of `ζ_K`

SpectralTheoryOfTheCubicCover proves, for the Gaussian smoothing `W(y) = exp(−y²/4)/(2√π)` in logarithmic
scale, the signed asymptotic

`Σ_A σ(A) W(log(N(A)/X)) = M X^{2/3} + O(X^a)`   for every `5/8 < a < 2/3`

(`gaussianSmoothedUntwistedTheta_main_term`), where `5/8 = (1 + 7/8)/3` comes from the `7/8` zero-free seed for
`ζ_K` at `3w − 1`. This module proves the converse direction for the same smoothed sum:

* `integral_logSmoothedTheta_mul_exp`: the Laplace transform in `x = log X` is `exp(w²) S₁(w)` on `Re w > 1`;
* `smoothedRemainder_forces_thetaSquare_zero`: if `Σ σ(A) W(log(N(A)/X)) = c X^{2/3} + O(X^β)` (`X ≥ 1`), then every
  zero `ρ` of `ζ · L(·, χ₋₃)` with `Re ρ > max(½, 3β − 1)`, `Im ρ > 0` is a zero of the completed unramified
  theta square at `2(1 + ρ)/3`;
* `smoothedRemainderExponent_ge`: a zero with `Λ₀(2(1 + ρ)/3) ≠ 0` bounds every smoothed remainder exponent below by
  `(1 + Re ρ)/3`.

So the exponent `a` of the smoothed main-term theorem is the zero-free region of `ζ_K` read at `3w − 1` from
both sides: the seed gives `a > (1 + Θ)/3`, and nothing below `(1 + Re ρ)/3` is possible at a zero `ρ` unless
the theta square vanishes there.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
  SpectralTheoryOfTheCubicCover FamilyContinuationTheory FamilyContinuationTheory.EisensteinNorm

/-- The logarithmic Gaussian `W(y) = exp(−y²/4)/(2√π)`. -/
local notation "W" => RHTower.smoothAFELogGaussian

theorem logGaussian_nonneg (y : ℝ) : 0 ≤ W y := by
  unfold RHTower.smoothAFELogGaussian
  positivity

/-! ### The Laplace transform of a shifted Gaussian -/

/-- `∫ W(ℓ − x) e^{−wx} dx = e^{−wℓ} e^{w²}`. -/
theorem integral_logGaussian_shift (ℓ : ℝ) (w : ℂ) :
    ∫ x : ℝ, (W (ℓ - x) : ℂ) * Complex.exp (-w * x) = Complex.exp (-w * ℓ) * Complex.exp (w ^ 2) := by
  have h := integral_sub_left_eq_self
    (fun y : ℝ => (W y : ℂ) * Complex.exp (-w * ((ℓ - y : ℝ) : ℂ))) (μ := volume) ℓ
  simp only [sub_sub_cancel] at h
  rw [h]
  have he : ∀ y : ℝ, (W y : ℂ) * Complex.exp (-w * ((ℓ - y : ℝ) : ℂ)) =
      Complex.exp (-w * ℓ) * ((W y : ℂ) * Complex.exp (w * y)) := by
    intro y
    rw [show -w * ((ℓ - y : ℝ) : ℂ) = -w * ℓ + w * y by push_cast; ring, Complex.exp_add]
    ring
  simp_rw [he]
  rw [integral_const_mul, RHTower.integral_smoothAFELogGaussian_mul_exp]

theorem integrable_logGaussian_shift (ℓ : ℝ) (w : ℂ) :
    Integrable (fun x : ℝ => (W (ℓ - x) : ℂ) * Complex.exp (-w * x)) := by
  have h := ((RHTower.integrable_smoothAFELogGaussian_mul_exp w).const_mul
    (Complex.exp (-w * ℓ))).comp_sub_left ℓ
  refine h.congr (Eventually.of_forall fun x => ?_)
  show Complex.exp (-w * ℓ) * ((W (ℓ - x) : ℂ) * Complex.exp (w * ((ℓ - x : ℝ) : ℂ))) =
    (W (ℓ - x) : ℂ) * Complex.exp (-w * x)
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ### The smoothed sum in logarithmic scale -/

/-- The smoothed sum at `X = eˣ`: `h(x) = Σ σ(A) W(log N(A) − x)`. -/
def logSmoothedTheta (x : ℝ) : ℂ := gaussianSmoothedUntwistedTheta (Real.exp x)

/-- The term `σ(A) W(log N(A) − x)`. -/
def logTerm (A : Ideal O) (x : ℝ) : ℂ :=
  untwistedSquarefreeCoefficient A * (W (Real.log (Ideal.absNorm A : ℝ) - x) : ℂ)

theorem absNorm_pos_of_good {A : Ideal O} (hA : primaryIdealGenerator A ≠ 0) :
    0 < (Ideal.absNorm A : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (primaryIdealGenerator_ne_zero_ideal A hA)))

theorem logSmoothedTheta_eq (x : ℝ) : logSmoothedTheta x = ∑' A : Ideal O, logTerm A x := by
  unfold logSmoothedTheta gaussianSmoothedUntwistedTheta
  refine tsum_congr fun A => ?_
  by_cases hA : primaryIdealGenerator A = 0
  · simp only [logTerm, untwistedSquarefreeCoefficient_of_bad A hA, zero_mul]
  · rw [logTerm, Real.log_div (absNorm_pos_of_good hA).ne' (Real.exp_pos x).ne', Real.log_exp]

theorem logTerm_eq_zero_of_bad {A : Ideal O} (hA : primaryIdealGenerator A = 0) (x : ℝ) :
    logTerm A x = 0 := by
  simp only [logTerm, untwistedSquarefreeCoefficient_of_bad A hA, zero_mul]

theorem norm_logTerm_le (A : Ideal O) (x : ℝ) :
    ‖logTerm A x‖ ≤ (if primaryIdealGenerator A = 0 then 0 else W (Real.log (Ideal.absNorm A : ℝ) - x)) := by
  split_ifs with hA
  · rw [logTerm_eq_zero_of_bad hA, norm_zero]
  · rw [logTerm, norm_mul, Complex.norm_real, Real.norm_of_nonneg (logGaussian_nonneg _)]
    exact mul_le_of_le_one_left (logGaussian_nonneg _) (norm_untwistedSquarefreeCoefficient_le A)

/-- `W(ℓ − x) ≤ e⁴/(2√π) · e^{−2ℓ} · e^{−x²/4}` for `ℓ ≥ 0 ≥ x`. -/
theorem logGaussian_left_bound {ℓ x : ℝ} (hℓ : 0 ≤ ℓ) (hx : x ≤ 0) :
    W (ℓ - x) ≤ Real.exp 4 / (2 * Real.sqrt Real.pi) * Real.exp (-2 * ℓ) * Real.exp (-x ^ 2 / 4) := by
  unfold RHTower.smoothAFELogGaussian
  have hpi : 0 < 2 * Real.sqrt Real.pi := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpi, ← Real.exp_add,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (ℓ / 2 - 2), mul_nonneg hℓ (neg_nonneg.mpr hx)]

theorem good_norm_weight (A : Ideal O) (hA : primaryIdealGenerator A ≠ 0) :
    Real.exp (-2 * Real.log (Ideal.absNorm A : ℝ)) = ‖unramifiedNormWeight 2 A‖ := by
  rw [unramifiedNormWeight_of_good _ A hA, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.rpow_def_of_pos (absNorm_pos_of_good hA)]
  ring_nf

/-- **Gaussian decay to the left.** `‖h(x)‖ ≤ C₀ e^{−x²/4}` for `x ≤ 0`. -/
theorem logSmoothedTheta_left_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x ≤ 0 → ‖logSmoothedTheta x‖ ≤ C * Real.exp (-x ^ 2 / 4) := by
  letI : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
  letI : Countable (Ideal O) := cubicIdealGenerator_injective.countable
  have hs := unramifiedNormWeight_summable_norm (2 : ℂ) (by norm_num)
  set κ : ℝ := Real.exp 4 / (2 * Real.sqrt Real.pi)
  have hκ : 0 ≤ κ := by positivity
  refine ⟨κ * ∑' A : Ideal O, ‖unramifiedNormWeight 2 A‖, mul_nonneg hκ (tsum_nonneg fun _ => norm_nonneg _),
    fun x hx => ?_⟩
  have hterm : ∀ A : Ideal O, ‖logTerm A x‖ ≤ κ * ‖unramifiedNormWeight 2 A‖ * Real.exp (-x ^ 2 / 4) := by
    intro A
    refine (norm_logTerm_le A x).trans ?_
    split_ifs with hA
    · positivity
    · have hℓ : 0 ≤ Real.log (Ideal.absNorm A : ℝ) := Real.log_nonneg (by
        have := absNorm_pos_of_good hA
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne'))
      rw [← good_norm_weight A hA]
      exact logGaussian_left_bound hℓ hx
  have hsum : Summable (fun A : Ideal O => κ * ‖unramifiedNormWeight 2 A‖ * Real.exp (-x ^ 2 / 4)) :=
    (hs.mul_left κ).mul_right _
  rw [logSmoothedTheta_eq]
  calc ‖∑' A, logTerm A x‖ ≤ ∑' A, ‖logTerm A x‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum)
    _ ≤ ∑' A, κ * ‖unramifiedNormWeight 2 A‖ * Real.exp (-x ^ 2 / 4) :=
        Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum) hsum
    _ = κ * (∑' A, ‖unramifiedNormWeight 2 A‖) * Real.exp (-x ^ 2 / 4) := by
        rw [tsum_mul_right, tsum_mul_left]

theorem logSmoothedTheta_measurable : Measurable logSmoothedTheta := by
  letI : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
  letI : Countable (Ideal O) := cubicIdealGenerator_injective.countable
  have : logSmoothedTheta = fun x => ∑' A : Ideal O, logTerm A x := funext logSmoothedTheta_eq
  rw [this]
  refine Measurable.tsum fun A => ?_
  unfold logTerm RHTower.smoothAFELogGaussian
  fun_prop

/-! ### The Laplace transform -/

/-- **The Laplace transform of the smoothed sum.** For `Re w > 1`:
`∫ h(x) e^{−wx} dx = e^{w²} S₁(w)`. -/
theorem integral_logSmoothedTheta_mul_exp (w : ℂ) (hw : 1 < w.re) :
    ∫ x : ℝ, logSmoothedTheta x * Complex.exp (-w * x) =
      Complex.exp (w ^ 2) * twistedSquarefreeSeries 1 w := by
  letI : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
  letI : Countable (Ideal O) := cubicIdealGenerator_injective.countable
  set f : Ideal O → ℝ → ℂ := fun A x => logTerm A x * Complex.exp (-w * x) with hf
  have hint : ∀ A, Integrable (f A) := by
    intro A
    simp only [hf, logTerm, mul_assoc]
    exact (integrable_logGaussian_shift _ w).const_mul _
  -- each term integrates to `σ(A) N(A)^{−w} e^{w²}`
  have hval : ∀ A, ∫ x, f A x = Complex.exp (w ^ 2) *
      (unramifiedNormWeight w A * untwistedSquarefreeCoefficient A) := by
    intro A
    by_cases hA : primaryIdealGenerator A = 0
    · simp [hf, logTerm_eq_zero_of_bad hA, untwistedSquarefreeCoefficient_of_bad A hA]
    · simp only [hf, logTerm, mul_assoc]
      rw [integral_const_mul, integral_logGaussian_shift, unramifiedNormWeight_of_good _ A hA]
      have hN := absNorm_pos_of_good hA
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hN.ne'), ← Complex.ofReal_natCast,
        ← Complex.ofReal_log hN.le]
      ring_nf
  -- the norms are summable
  have hnorm : ∀ A, ∫ x, ‖f A x‖ = Real.exp (w.re ^ 2) * ‖unramifiedNormWeight (w.re : ℂ) A‖ *
      ‖untwistedSquarefreeCoefficient A‖ := by
    intro A
    by_cases hA : primaryIdealGenerator A = 0
    · simp [hf, logTerm_eq_zero_of_bad hA, untwistedSquarefreeCoefficient_of_bad A hA]
    · have hN := absNorm_pos_of_good hA
      have hpt : ∀ x : ℝ, ‖f A x‖ = ‖untwistedSquarefreeCoefficient A‖ *
          (W (Real.log (Ideal.absNorm A : ℝ) - x) * Real.exp (-w.re * x)) := by
        intro x
        simp only [hf, logTerm]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (logGaussian_nonneg _),
          Complex.norm_exp]
        have hre : (-w * (x : ℂ)).re = -w.re * x := by simp
        rw [hre]
        ring
      simp_rw [hpt]
      rw [integral_const_mul]
      have hr := integral_logGaussian_shift (Real.log (Ideal.absNorm A : ℝ)) (w.re : ℂ)
      have hre : ∫ x : ℝ, W (Real.log (Ideal.absNorm A : ℝ) - x) * Real.exp (-w.re * x) =
          Real.exp (-w.re * Real.log (Ideal.absNorm A : ℝ)) * Real.exp (w.re ^ 2) := by
        have hc : ∀ x : ℝ, (W (Real.log (Ideal.absNorm A : ℝ) - x) : ℂ) * Complex.exp (-(w.re : ℂ) * x) =
            ((W (Real.log (Ideal.absNorm A : ℝ) - x) * Real.exp (-w.re * x) : ℝ) : ℂ) := by
          intro x
          push_cast
          ring_nf
        simp_rw [hc] at hr
        rw [integral_complex_ofReal] at hr
        apply Complex.ofReal_injective
        rw [hr]
        push_cast
        ring_nf
      rw [hre, unramifiedNormWeight_of_good _ A hA, ← Complex.ofReal_natCast,
        ← Complex.ofReal_neg, ← Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), Real.rpow_def_of_pos hN]
      ring_nf
  have hsum : Summable (fun A => ∫ x, ‖f A x‖) := by
    simp_rw [hnorm]
    exact ((unramifiedNormWeight_summable_norm (w.re : ℂ) (by simpa using hw)).mul_left
      (Real.exp (w.re ^ 2))).of_nonneg_of_le (fun _ => by positivity)
      (fun A => mul_le_of_le_one_right (by positivity) (norm_untwistedSquarefreeCoefficient_le A)) |>.congr
      (fun A => rfl)
  have hHS := hasSum_integral_of_summable_integral_norm hint hsum
  simp only [hval] at hHS
  have hlhs : (fun x => logSmoothedTheta x * Complex.exp (-w * x)) = fun x => ∑' A, f A x := by
    funext x
    rw [logSmoothedTheta_eq, hf, tsum_mul_right]
  rw [hlhs, ← hHS.tsum_eq, tsum_mul_left, twistedSquarefreeSeries_one_eq]

/-! ### One-sided Laplace transforms are holomorphic -/

/-- If `‖f x‖ ≤ K e^{βx}` for `x > 0`, then `w ↦ ∫_{x>0} f(x) e^{−wx} dx` is holomorphic on `Re w > β`. -/
theorem laplace_Ioi_differentiableAt {f : ℝ → ℂ} (hfm : Measurable f) {β K : ℝ}
    (hb : ∀ x : ℝ, 0 < x → ‖f x‖ ≤ K * Real.exp (β * x)) {w₀ : ℂ} (hw : β < w₀.re) :
    DifferentiableAt ℂ (fun w : ℂ => ∫ x in Ioi (0 : ℝ), f x * Complex.exp (-w * x)) w₀ := by
  set δ := (w₀.re - β) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hK : 0 ≤ K := by
    have h1 := hb 1 one_pos
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h1) (Real.exp_pos _)
  have hball : ∀ w ∈ Metric.ball w₀ δ, β + δ < w.re := by
    intro w hw'
    have h1 : |w.re - w₀.re| < δ := by
      have := Complex.abs_re_le_norm (w - w₀)
      rw [Metric.mem_ball, dist_eq_norm] at hw'
      simp only [Complex.sub_re] at this
      linarith
    rw [abs_lt] at h1
    rw [hδ] at h1 ⊢
    linarith
  have hexp_meas : ∀ w : ℂ, Measurable (fun x : ℝ => Complex.exp (-w * x)) := fun w => by fun_prop
  have hderiv_bound : ∀ x : ℝ, 0 < x → ∀ w ∈ Metric.ball w₀ δ,
      ‖f x * (Complex.exp (-w * x) * -(x : ℂ))‖ ≤ K * (2 / δ) * Real.exp (-(δ / 2) * x) := by
    intro x hx w hw'
    have hwre := hball w hw'
    rw [norm_mul, norm_mul, Complex.norm_exp, norm_neg, Complex.norm_real, Real.norm_of_nonneg hx.le]
    have hre : (-w * (x : ℂ)).re = -w.re * x := by simp
    rw [hre]
    have hx2 : x ≤ 2 / δ * Real.exp (δ / 2 * x) := by
      have := Real.add_one_le_exp (δ / 2 * x)
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]
      nlinarith [Real.exp_pos (δ / 2 * x)]
    calc ‖f x‖ * (Real.exp (-w.re * x) * x)
        ≤ K * Real.exp (β * x) * (Real.exp (-(β + δ) * x) * (2 / δ * Real.exp (δ / 2 * x))) := by
          gcongr
          exact hb x hx
      _ = K * (2 / δ) * Real.exp (-(δ / 2) * x) := by
          rw [show K * Real.exp (β * x) * (Real.exp (-(β + δ) * x) * (2 / δ * Real.exp (δ / 2 * x))) =
            K * (2 / δ) * (Real.exp (β * x) * Real.exp (-(β + δ) * x) * Real.exp (δ / 2 * x)) by ring,
            ← Real.exp_add, ← Real.exp_add]
          congr 2
          ring
  have hval_bound : ∀ x : ℝ, 0 < x → ‖f x * Complex.exp (-w₀ * x)‖ ≤ K * Real.exp (-(2 * δ) * x) := by
    intro x hx
    rw [norm_mul, Complex.norm_exp]
    have hre : (-w₀ * (x : ℂ)).re = -w₀.re * x := by simp
    rw [hre]
    calc ‖f x‖ * Real.exp (-w₀.re * x) ≤ K * Real.exp (β * x) * Real.exp (-w₀.re * x) := by
          gcongr
          exact hb x hx
      _ = K * Real.exp (-(2 * δ) * x) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          rw [hδ]
          ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun w x => f x * Complex.exp (-w * x)) (F' := fun w x => f x * (Complex.exp (-w * x) * -(x : ℂ)))
    (x₀ := w₀) (s := Metric.ball w₀ δ) (bound := fun x => K * (2 / δ) * Real.exp (-(δ / 2) * x))
    (Metric.ball_mem_nhds w₀ hδ0)
    (Eventually.of_forall fun w => (hfm.mul (hexp_meas w)).aestronglyMeasurable)
    (((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < 2 * δ)).const_mul K).mono'
      (hfm.mul (hexp_meas w₀)).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => hval_bound x hx)))
    ((hfm.mul ((hexp_meas w₀).mul (Complex.measurable_ofReal.neg))).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx w hw' =>
      hderiv_bound x hx w hw'))
    ((exp_neg_integrableOn_Ioi 0 (by linarith : 0 < δ / 2)).const_mul _)
    (Eventually.of_forall fun x w _ => by
      have h1 : HasDerivAt (fun w : ℂ => -w * (x : ℂ)) (-(x : ℂ)) w := by
        simpa using ((hasDerivAt_id w).neg.mul_const (x : ℂ))
      exact h1.cexp.const_mul (f x))
  exact key.2.differentiableAt

/-! ### The converse of the smoothed main term -/

/-- **A smoothed power remainder forces the zeros of `ζ_K` into the theta square.** If
`Σ σ(A) W(log(N(A)/X)) = c X^{2/3} + O(X^β)` for `X ≥ 1`, then every zero `ρ` of `ζ · L(·, χ₋₃)` with `Re ρ > 1/2`,
`Re ρ > 3β − 1`, `Im ρ > 0` is a zero of the completed unramified theta square at `2(1 + ρ)/3`. -/
theorem smoothedRemainder_forces_thetaSquare_zero {c : ℂ} {β K : ℝ}
    (hE : ∀ X : ℝ, 1 ≤ X →
      ‖gaussianSmoothedUntwistedTheta X - c * (X : ℂ) ^ (2 / 3 : ℂ)‖ ≤ K * X ^ β)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0 ∨ DirichletCharacter.LFunction chi3D ρ = 0)
    (hρ1 : 1 / 2 < ρ.re) (hρβ : 3 * β - 1 < ρ.re) (hρi : 0 < ρ.im) :
    completedUnramified (2 * (1 + ρ) / 3) = 0 := by
  have hρlt := re_lt_one_of_zero hρ
  have hβ23 : β < 2 / 3 := by linarith
  -- the remainder in logarithmic scale
  set E : ℝ → ℂ := fun x => logSmoothedTheta x - c * Complex.exp ((2 / 3 : ℂ) * x) with hEdef
  have hEm : Measurable E := logSmoothedTheta_measurable.sub (measurable_const.mul (by fun_prop))
  have hEb : ∀ x : ℝ, 0 < x → ‖E x‖ ≤ K * Real.exp (β * x) := by
    intro x hx
    have h := hE (Real.exp x) (Real.one_le_exp hx.le)
    have hcp : ((Real.exp x : ℝ) : ℂ) ^ (2 / 3 : ℂ) = Complex.exp ((2 / 3 : ℂ) * x) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
        ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
      ring_nf
    have hrp : Real.exp x ^ β = Real.exp (β * x) := by
      rw [← Real.exp_mul]
      ring_nf
    rw [hcp, hrp] at h
    exact h
  obtain ⟨C₀, hC₀, hleft⟩ := logSmoothedTheta_left_bound
  -- the left half, reflected
  set g : ℝ → ℂ := fun y => logSmoothedTheta (-y) with hg
  have hgm : Measurable g := logSmoothedTheta_measurable.comp measurable_neg
  have hgb : ∀ M : ℝ, ∀ y : ℝ, 0 < y → ‖g y‖ ≤ C₀ * Real.exp (M ^ 2) * Real.exp (M * y) := by
    intro M y hy
    calc ‖g y‖ ≤ C₀ * Real.exp (-(-y) ^ 2 / 4) := hleft (-y) (by linarith)
      _ ≤ C₀ * (Real.exp (M ^ 2) * Real.exp (M * y)) := by
          gcongr
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (y / 2 + M)])
      _ = _ := by ring
  set I : ℂ → ℂ := fun w => ∫ y in Ioi (0 : ℝ), g y * Complex.exp (-(-w) * y) with hI
  set J : ℂ → ℂ := fun w => ∫ x in Ioi (0 : ℝ), E x * Complex.exp (-w * x) with hJ
  set F : ℂ → ℂ := fun w => Complex.exp (-(w ^ 2)) * (I w + c / (w - 2 / 3) + J w) with hF
  have hId : ∀ w₀ : ℂ, DifferentiableAt ℂ I w₀ := by
    intro w₀
    have hL := laplace_Ioi_differentiableAt hgm (hgb (-w₀.re - 1)) (w₀ := -w₀) (by simp)
    exact hL.comp w₀ differentiableAt_id.neg
  have hFd : ∀ w : ℂ, β < w.re → w ≠ 2 / 3 → DifferentiableAt ℂ F w := by
    intro w hw hw23
    have hc : DifferentiableAt ℂ (fun w : ℂ => c / (w - 2 / 3)) w :=
      (differentiableAt_const c).div (differentiableAt_id.sub_const (2 / 3 : ℂ)) (sub_ne_zero.mpr hw23)
    exact (differentiableAt_id.pow 2).neg.cexp.mul (((hId w).add hc).add
      (laplace_Ioi_differentiableAt hEm hEb hw))
  -- the Laplace transform splits
  have hFS : ∀ w : ℂ, 2 < w.re → twistedSquarefreeSeries 1 w = F w := by
    intro w hw
    have hσ : 1 < w.re := by linarith
    have hfull := integral_logSmoothedTheta_mul_exp w hσ
    -- integrability on the two halves
    have hleftInt : IntegrableOn (fun x : ℝ => logSmoothedTheta x * Complex.exp (-w * x)) (Iic 0) := by
      refine (((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 8)).const_mul
        (C₀ * Real.exp (2 * w.re ^ 2))).integrableOn).mono' ((logSmoothedTheta_measurable.mul
          (by fun_prop)).aestronglyMeasurable)
        ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun x hx => ?_))
      rw [norm_mul, Complex.norm_exp]
      have hre : (-w * (x : ℂ)).re = -w.re * x := by simp
      rw [hre]
      calc ‖logSmoothedTheta x‖ * Real.exp (-w.re * x)
          ≤ C₀ * Real.exp (-x ^ 2 / 4) * Real.exp (-w.re * x) := by
            gcongr
            exact hleft x hx
        _ = C₀ * Real.exp (-x ^ 2 / 4 + -w.re * x) := by rw [mul_assoc, ← Real.exp_add]
        _ ≤ C₀ * Real.exp (2 * w.re ^ 2 + -(1 / 8) * x ^ 2) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (x + 4 * w.re)])) hC₀
        _ = C₀ * Real.exp (2 * w.re ^ 2) * Real.exp (-(1 / 8) * x ^ 2) := by rw [mul_assoc, ← Real.exp_add]
    have hpos : 0 < w.re - max β (2 / 3) := by
      have : max β (2 / 3) < w.re := max_lt (by linarith) (by linarith)
      linarith
    have hK : 0 ≤ K := by
      have h1 := hEb 1 one_pos
      exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h1) (Real.exp_pos _)
    have hrightInt : IntegrableOn (fun x : ℝ => logSmoothedTheta x * Complex.exp (-w * x)) (Ioi 0) := by
      refine ((exp_neg_integrableOn_Ioi 0 hpos).const_mul (K + ‖c‖)).mono'
        ((logSmoothedTheta_measurable.mul (by fun_prop)).aestronglyMeasurable)
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_))
      have hx : (0 : ℝ) < x := hx
      rw [norm_mul, Complex.norm_exp]
      have hre : (-w * (x : ℂ)).re = -w.re * x := by simp
      rw [hre]
      have hsplit : logSmoothedTheta x = E x + c * Complex.exp ((2 / 3 : ℂ) * x) := by
        rw [hEdef]; ring
      have hmax1 : Real.exp (β * x) ≤ Real.exp (max β (2 / 3) * x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hx.le)
      have hmax2 : Real.exp (2 / 3 * x) ≤ Real.exp (max β (2 / 3) * x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hx.le)
      have hn : ‖logSmoothedTheta x‖ ≤ (K + ‖c‖) * Real.exp (max β (2 / 3) * x) := by
        rw [hsplit]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_exp]
        have hre2 : ((2 / 3 : ℂ) * x).re = 2 / 3 * x := by simp
        rw [hre2]
        nlinarith [hEb x hx, norm_nonneg c, Real.exp_pos (2 / 3 * x)]
      calc ‖logSmoothedTheta x‖ * Real.exp (-w.re * x)
          ≤ (K + ‖c‖) * Real.exp (max β (2 / 3) * x) * Real.exp (-w.re * x) := by gcongr
        _ = (K + ‖c‖) * Real.exp (-(w.re - max β (2 / 3)) * x) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            ring
    have hunion : ∫ x : ℝ, logSmoothedTheta x * Complex.exp (-w * x) =
        (∫ x in Iic (0 : ℝ), logSmoothedTheta x * Complex.exp (-w * x)) +
          ∫ x in Ioi (0 : ℝ), logSmoothedTheta x * Complex.exp (-w * x) := by
      rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hleftInt hrightInt,
        Set.Iic_union_Ioi, setIntegral_univ]
    rw [hunion] at hfull
    -- the left half is `I(w)`
    have hIeq : ∫ x in Iic (0 : ℝ), logSmoothedTheta x * Complex.exp (-w * x) = I w := by
      rw [hI]
      have := integral_comp_neg_Ioi 0 (fun x : ℝ => logSmoothedTheta x * Complex.exp (-w * x))
      rw [neg_zero] at this
      rw [← this]
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
      simp only [hg]
      push_cast
      ring_nf
    -- the right half is `c/(w − 2/3) + J(w)`
    have hJeq : ∫ x in Ioi (0 : ℝ), logSmoothedTheta x * Complex.exp (-w * x) = c / (w - 2 / 3) + J w := by
      have hmain : IntegrableOn (fun x : ℝ => c * Complex.exp ((2 / 3 - w) * x)) (Ioi 0) :=
        (integrableOn_exp_mul_complex_Ioi (by simp; linarith) 0).const_mul c
      have hrem : IntegrableOn (fun x : ℝ => E x * Complex.exp (-w * x)) (Ioi 0) := by
        have h := hrightInt.sub (hmain)
        refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
        show logSmoothedTheta x * Complex.exp (-w * x) - c * Complex.exp ((2 / 3 - w) * x) =
          (logSmoothedTheta x - c * Complex.exp ((2 / 3 : ℂ) * x)) * Complex.exp (-w * x)
        rw [show (2 / 3 - w) * (x : ℂ) = (2 / 3 : ℂ) * x + -w * x by ring, Complex.exp_add]
        ring
      have hpt : ∀ x : ℝ, logSmoothedTheta x * Complex.exp (-w * x) =
          c * Complex.exp ((2 / 3 - w) * x) + E x * Complex.exp (-w * x) := by
        intro x
        simp only [hEdef]
        rw [show (2 / 3 - w) * (x : ℂ) = (2 / 3 : ℂ) * x + -w * x by ring, Complex.exp_add]
        ring
      simp_rw [hpt]
      rw [integral_add hmain hrem, integral_const_mul,
        integral_exp_mul_complex_Ioi (by simp; linarith) 0]
      have hne : w - 2 / 3 ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have hne' : (2 / 3 : ℂ) - w ≠ 0 := by
        intro h
        apply hne
        linear_combination -h
      have hA : c * (-Complex.exp ((2 / 3 - w) * ((0 : ℝ) : ℂ)) / (2 / 3 - w)) = c / (w - 2 / 3) := by
        rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, show (2 / 3 : ℂ) - w = -(w - 2 / 3) by ring,
          div_neg, neg_div, neg_neg, mul_one_div]
      rw [hA]
    rw [hIeq, hJeq] at hfull
    rw [hF]
    simp only
    rw [show I w + c / (w - 2 / 3) + J w = I w + (c / (w - 2 / 3) + J w) by ring, hfull, ← mul_assoc,
      ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  exact thetaSquare_zero_of_extension F hFd hFS hρ hρ1 hρβ hρi

/-- **The smoothed remainder exponent is at least `(1 + Re ρ)/3`** at every zero `ρ` of `ζ · L(·, χ₋₃)` with
`Re ρ > 1/2`, `Im ρ > 0` where the theta square does not vanish. -/
theorem smoothedRemainderExponent_ge {c : ℂ} {β K : ℝ}
    (hE : ∀ X : ℝ, 1 ≤ X →
      ‖gaussianSmoothedUntwistedTheta X - c * (X : ℂ) ^ (2 / 3 : ℂ)‖ ≤ K * X ^ β)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0 ∨ DirichletCharacter.LFunction chi3D ρ = 0)
    (hρ1 : 1 / 2 < ρ.re) (hρi : 0 < ρ.im) (hΛ : completedUnramified (2 * (1 + ρ) / 3) ≠ 0) :
    (1 + ρ.re) / 3 ≤ β := by
  by_contra h
  push Not at h
  exact hΛ (smoothedRemainder_forces_thetaSquare_zero hE hρ hρ1 (by linarith) hρi)

end GaloisForLFunctions.OrderSixMetaplecticTheory
