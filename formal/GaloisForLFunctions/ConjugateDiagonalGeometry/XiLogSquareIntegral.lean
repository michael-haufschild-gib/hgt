import GaloisForLFunctions.ConjugateDiagonalGeometry.XiCanonicalLogBound
import GaloisForLFunctions.HTGeometry.PlanarLogSquareMass
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# A polynomial planar log-square bound for actual xi

Canonical factorization bounds the logarithm on an inner disc by its analytic
residual and a finite positive logarithmic potential. Weighted Cauchy–Schwarz
and planar kernel integration retain every zero multiplicity without any
separation assumption. The actual theta growth bound then gives one constant
`C` with integral at most `C (n+1)^6` on every source disc of radius `n+2`.
-/

open Complex MeasureTheory MeromorphicOn Metric Set
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open RiemannGaussian HTGeometry

/-- Finite support of the canonical xi divisor, with multiplicities retained separately. -/
def xiCanonicalDivisorSupport (n : ℕ) : Finset ℂ :=
  ((riemannXiCanonicalResidual_decomp n).meromorphicOn.divisor_ball_support_finite).toFinset

/-- The canonical potential is a finite sum over its exact divisor support. -/
lemma xiCanonicalLogMass_eq_sum (n : ℕ) (z : ℂ) :
    xiCanonicalLogMass n z = ∑ i ∈ xiCanonicalDivisorSupport n,
      (divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i : ℝ) *
        planarLogKernel (2 * xiCanonicalRadius n) (z - i) := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro i hi
  change i ∈ ((riemannXiCanonicalResidual_decomp n).meromorphicOn.divisor_ball_support_finite).toFinset
  rw [Set.Finite.mem_toFinset]
  intro hzero
  apply hi
  dsimp only at hzero ⊢
  rw [hzero, Int.cast_zero, zero_mul]

/-- Finite-support enumeration preserves the full canonical multiplicity. -/
lemma xiCanonicalDivisor_sum_eq (n : ℕ) :
    (∑ i ∈ xiCanonicalDivisorSupport n,
      (divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i : ℝ)) =
      ((∑ᶠ i : ℂ, divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i : ℤ) : ℝ) := by
  classical
  have he : (∑ᶠ i : ℂ, divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i : ℤ) =
      ∑ i ∈ xiCanonicalDivisorSupport n,
        divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    change i ∈ ((riemannXiCanonicalResidual_decomp n).meromorphicOn.divisor_ball_support_finite).toFinset
    simpa only [Set.Finite.mem_toFinset] using hi
  rw [he, Int.cast_sum]

/-- Arbitrary multiplicities still give a square-integrable canonical potential. -/
lemma integrable_xiCanonicalLogMass_sq (n : ℕ) :
    Integrable (fun z : ℂ => xiCanonicalLogMass n z ^ 2) := by
  simp_rw [xiCanonicalLogMass_eq_sum]
  apply integrable_sum_planarLogKernel_sq
  · intro i _
    exact_mod_cast (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg i
  · exact mul_pos (by norm_num) (xiCanonicalRadius_pos n)

/-- Total canonical multiplicity bounds the squared potential on every disc. -/
lemma integral_xiCanonicalLogMass_sq_le (n : ℕ) (c : ℂ) (r : ℝ) :
    (∫ z in closedBall c r, xiCanonicalLogMass n z ^ 2) ≤
      ((∑ᶠ i : ℂ, divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i : ℤ) : ℝ) ^ 2 *
        (8 * Real.pi * (2 * xiCanonicalRadius n) ^ 2) := by
  simp_rw [xiCanonicalLogMass_eq_sum]
  have h := integral_sum_planarLogKernel_sq_on_disc_le (xiCanonicalDivisorSupport n)
    (fun i => (divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i : ℝ))
    (fun i => i) (fun i _ => by
      exact_mod_cast (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg i)
    (S := 2 * xiCanonicalRadius n)
    (mul_pos (by norm_num : (0 : ℝ) < 2) (xiCanonicalRadius_pos n)) c r
  simpa only [xiCanonicalDivisor_sum_eq] using h

/-- Passing to standard xi normalization adds at most `log 2` to the majorant. -/
lemma abs_log_norm_xi_le_canonical {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖RiemannGaussian.riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ xiCanonicalRadius n / 4) :
    |Real.log ‖_root_.RHTower.xi z‖| ≤
      (2 * A * (xiCanonicalRadius n + 1) ^ 2 + Real.log 2) + xiCanonicalLogMass n z := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmass := xiCanonicalLogMass_nonneg n z
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  by_cases hx : _root_.RHTower.xi z = 0
  · rw [hx, norm_zero, Real.log_zero, abs_zero]
    positivity
  have hnorm : ‖RiemannGaussian.riemannXi z‖ = 2 * ‖_root_.RHTower.xi z‖ := by
    rw [gaussianXi_eq_neg_two_mul_xi, norm_mul]
    norm_num
  have hlog : Real.log ‖RiemannGaussian.riemannXi z‖ =
      Real.log 2 + Real.log ‖_root_.RHTower.xi z‖ := by
    rw [hnorm, Real.log_mul (by norm_num) (norm_ne_zero_iff.mpr hx)]
  calc
    |Real.log ‖_root_.RHTower.xi z‖| =
        |Real.log ‖RiemannGaussian.riemannXi z‖ - Real.log 2| := by rw [hlog]; congr 1; ring
    _ ≤ |Real.log ‖RiemannGaussian.riemannXi z‖| + |Real.log 2| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_of_nonneg hlog2]
      linarith only [abs_log_norm_gaussianXi_le hA hbound n hz]


private lemma volume_real_closedBall_complex (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall c r) = Real.pi * r ^ 2 := by
  rw [measureReal_def, Complex.volume_closedBall]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

/-- The residual and divisor estimates combine into an inner-disc log-square bound. -/
lemma xi_log_sq_canonical_integrable_bound {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖RiemannGaussian.riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (hrR : r ≤ xiCanonicalRadius n / 4) :
    IntegrableOn (fun z : ℂ => Real.log ‖_root_.RHTower.xi z‖ ^ 2) (closedBall 0 r) ∧
    (∫ z in closedBall 0 r, Real.log ‖_root_.RHTower.xi z‖ ^ 2) ≤
      2 * (2 * A * (xiCanonicalRadius n + 1) ^ 2 + Real.log 2) ^ 2 * (Real.pi * r ^ 2) +
      2 * (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) ^ 2 *
        (8 * Real.pi * (2 * xiCanonicalRadius n) ^ 2) := by
  let B : ℝ := 2 * A * (xiCanonicalRadius n + 1) ^ 2 + Real.log 2
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hp (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) :
      Real.log ‖_root_.RHTower.xi z‖ ^ 2 ≤ 2 * B ^ 2 + 2 * xiCanonicalLogMass n z ^ 2 := by
    have hznorm : ‖z‖ ≤ xiCanonicalRadius n / 4 :=
      (by simpa only [mem_closedBall, dist_zero_right] using hz : ‖z‖ ≤ r).trans hrR
    have habs := abs_log_norm_xi_le_canonical hA hbound n hznorm
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hsq
    change Real.log ‖_root_.RHTower.xi z‖ ^ 2 ≤ (B + xiCanonicalLogMass n z) ^ 2 at hsq
    nlinarith only [hsq, sq_nonneg (B - xiCanonicalLogMass n z)]
  have hconst : IntegrableOn (fun _ : ℂ => 2 * B ^ 2) (closedBall 0 r) :=
    continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)
  have hmass : IntegrableOn (fun z : ℂ => 2 * xiCanonicalLogMass n z ^ 2) (closedBall 0 r) :=
    (integrable_xiCanonicalLogMass_sq n).integrableOn.const_mul 2
  have hmajor := hconst.add hmass
  have hmeas : Measurable (fun z : ℂ => Real.log ‖_root_.RHTower.xi z‖ ^ 2) :=
    (Real.measurable_log.comp _root_.RHTower.xi_differentiable.continuous.norm.measurable).pow_const 2
  have hxi : IntegrableOn (fun z : ℂ => Real.log ‖_root_.RHTower.xi z‖ ^ 2) (closedBall 0 r) := by
    apply MeasureTheory.Integrable.mono hmajor hmeas.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (hp z hz).trans (le_abs_self _)
  refine ⟨hxi, ?_⟩
  have hmassbound := integral_xiCanonicalLogMass_sq_le n 0 r
  have hcount := sum_divisor_riemannXi_ball_le_of_growth hA hbound n
  have hcount0 : 0 ≤
      ((∑ᶠ i : ℂ, divisor RiemannGaussian.riemannXi (ball 0 (xiCanonicalRadius n)) i : ℤ) : ℝ) := by
    exact_mod_cast finsum_nonneg (fun i =>
      (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg i)
  have hcountsq := pow_le_pow_left₀ hcount0 hcount 2
  have hmassfinal : (∫ z in closedBall 0 r, xiCanonicalLogMass n z ^ 2) ≤
      (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) ^ 2 *
        (8 * Real.pi * (2 * xiCanonicalRadius n) ^ 2) :=
    hmassbound.trans (mul_le_mul_of_nonneg_right hcountsq (by positivity))
  calc
    (∫ z in closedBall 0 r, Real.log ‖_root_.RHTower.xi z‖ ^ 2) ≤
        ∫ z in closedBall 0 r, 2 * B ^ 2 + 2 * xiCanonicalLogMass n z ^ 2 :=
      setIntegral_mono_on hxi hmajor measurableSet_closedBall hp
    _ = 2 * B ^ 2 * (Real.pi * r ^ 2) + 2 * ∫ z in closedBall 0 r, xiCanonicalLogMass n z ^ 2 := by
      rw [integral_add hconst hmass, integral_const, integral_const_mul]
      simp only [measureReal_restrict_apply_univ, smul_eq_mul, volume_real_closedBall_complex 0 hr]
      ring
    _ ≤ _ := by
      calc
        2 * B ^ 2 * (Real.pi * r ^ 2) +
            2 * (∫ z in closedBall 0 r, xiCanonicalLogMass n z ^ 2) ≤
          2 * B ^ 2 * (Real.pi * r ^ 2) +
            2 * ((A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) ^ 2 *
              (8 * Real.pi * (2 * xiCanonicalRadius n) ^ 2)) :=
          add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hmassfinal (by norm_num : (0 : ℝ) ≤ 2))
        _ = _ := by dsimp only [B]; ring


/-- One polynomial controls the logarithmic square of actual xi on every source disc. -/
theorem exists_xi_log_square_polynomial_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      IntegrableOn (fun z : ℂ => Real.log ‖_root_.RHTower.xi z‖ ^ 2)
        (closedBall 0 ((n : ℝ) + 2)) ∧
      (∫ z in closedBall 0 ((n : ℝ) + 2), Real.log ‖_root_.RHTower.xi z‖ ^ 2) ≤
        C * ((n : ℝ) + 1) ^ 6 := by
  obtain ⟨A, hA, hgrowth⟩ := riemannXi_quadraticGrowth
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let b : ℝ := 2 * A * 14 ^ 2 + Real.log 2
  let d : ℝ := A * 27 ^ 2 / Real.log 2
  let C : ℝ := 2 * b ^ 2 * (Real.pi * 2 ^ 2) +
    2 * d ^ 2 * (8 * Real.pi * (2 * 13) ^ 2)
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hd0 : 0 ≤ d := by dsimp only [d]; positivity
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C + 1, by positivity, fun n => ?_⟩
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ht0 : 0 ≤ (n : ℝ) + 1 := by positivity
  have ht1 : 1 ≤ (n : ℝ) + 1 := by linarith only [hn]
  have ht2 : 1 ≤ ((n : ℝ) + 1) ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one ht1 2
  have hR0 := xiCanonicalRadius_pos n
  have hR : xiCanonicalRadius n ≤ 13 * ((n : ℝ) + 1) := by
    linarith only [(xiCanonicalRadius_spec n).2.1, hn]
  have hR1 : xiCanonicalRadius n + 1 ≤ 14 * ((n : ℝ) + 1) := by
    linarith only [hR, hn]
  have hR2 : 2 * xiCanonicalRadius n + 1 ≤ 27 * ((n : ℝ) + 1) := by
    linarith only [hR, hn]
  have hr0 : 0 ≤ (n : ℝ) + 2 := by positivity
  have hr : (n : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) := by linarith only [hn]
  have hrR : (n : ℝ) + 2 ≤ xiCanonicalRadius n / 4 := by
    linarith only [(xiCanonicalRadius_spec n).1]
  obtain ⟨hi, hraw⟩ := xi_log_sq_canonical_integrable_bound hA hgrowth n hr0 hrR
  refine ⟨hi, ?_⟩
  have hB0 : 0 ≤ 2 * A * (xiCanonicalRadius n + 1) ^ 2 + Real.log 2 := by positivity
  have hB : 2 * A * (xiCanonicalRadius n + 1) ^ 2 + Real.log 2 ≤
      b * ((n : ℝ) + 1) ^ 2 := by
    calc
      2 * A * (xiCanonicalRadius n + 1) ^ 2 + Real.log 2 ≤
          2 * A * (14 * ((n : ℝ) + 1)) ^ 2 + Real.log 2 * ((n : ℝ) + 1) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hR1 2) (by positivity))
          (le_mul_of_one_le_right hlog2.le ht2)
      _ = _ := by dsimp only [b]; ring
  have hD0 : 0 ≤ A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2 := by positivity
  have hD : A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2 ≤
      d * ((n : ℝ) + 1) ^ 2 := by
    calc
      A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2 ≤
          A * (27 * ((n : ℝ) + 1)) ^ 2 / Real.log 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hR2 2) hA0) hlog2.le
      _ = _ := by dsimp only [d]; ring
  have hfirst := mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0 hB 2) (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr 2) Real.pi_pos.le)
    (by positivity : 0 ≤ Real.pi * ((n : ℝ) + 2) ^ 2)
    (by positivity : 0 ≤ 2 * (b * ((n : ℝ) + 1) ^ 2) ^ 2)
  have hsecond := mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD0 hD 2) (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (by positivity : 0 ≤ 2 * xiCanonicalRadius n)
      (mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 2)) 2)
      (by positivity : 0 ≤ 8 * Real.pi))
    (by positivity : 0 ≤ 8 * Real.pi * (2 * xiCanonicalRadius n) ^ 2)
    (by positivity : 0 ≤ 2 * (d * ((n : ℝ) + 1) ^ 2) ^ 2)
  calc
    (∫ z in closedBall 0 ((n : ℝ) + 2), Real.log ‖_root_.RHTower.xi z‖ ^ 2) ≤
        2 * (b * ((n : ℝ) + 1) ^ 2) ^ 2 * (Real.pi * (2 * ((n : ℝ) + 1)) ^ 2) +
        2 * (d * ((n : ℝ) + 1) ^ 2) ^ 2 *
          (8 * Real.pi * (2 * (13 * ((n : ℝ) + 1))) ^ 2) :=
      hraw.trans (add_le_add hfirst hsecond)
    _ = C * ((n : ℝ) + 1) ^ 6 := by dsimp only [C]; ring
    _ ≤ (C + 1) * ((n : ℝ) + 1) ^ 6 :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg ht0 _)

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_xi_log_square_polynomial_bound
