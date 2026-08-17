import GaloisForLFunctions.RHTower.XiMassPolynomialArchUniform
import GaloisForLFunctions.RHTower.XiMassBottomPrimeAtomization
import GaloisForLFunctions.HTGeometry.PolynomialSpectralWeight

/-!
# Atomization of the filtered prime bottom integral

The even polynomial weight is entire, so the atomwise horizontal shift that erases the contour depth
survives it: a fixed polynomial factor is absorbed by half of the exponential decay rate, which is
exactly the hypothesis the strip-transport theorem needs.  Hence the filtered von-Mangoldt Euler-line
integral is the absolutely convergent sum of depth-free filtered Fourier atoms at the prime
logarithms.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- The absorption constant of `1 + t^D` into half of the rate-`r` exponential. -/
def polyShiftConst (D : ℕ) (r : ℝ) : ℝ :=
  2 * ((Nat.factorial D : ℝ) / (r / 2) ^ D * Real.exp (r / 2))

theorem polyShiftConst_nonneg (D : ℕ) {r : ℝ} (hr : 0 < r) : 0 ≤ polyShiftConst D r := by
  rw [polyShiftConst]
  have hden : (0 : ℝ) < (r / 2) ^ D := by positivity
  have h1 : (0 : ℝ) ≤ (Nat.factorial D : ℝ) / (r / 2) ^ D := div_nonneg (by positivity) hden.le
  positivity

theorem one_add_pow_mul_exp_le (D : ℕ) {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    (1 + t ^ D) * Real.exp (-(r * t)) ≤
      polyShiftConst D r * Real.exp (-(r / 2 * t)) := by
  have h1 : (1 : ℝ) ≤ (1 + t) ^ D := one_le_pow₀ (by linarith)
  have h2 : t ^ D ≤ (1 + t) ^ D := pow_le_pow_left₀ ht (by linarith) D
  have hsplit : 1 + t ^ D ≤ 2 * (1 + t) ^ D := by linarith
  have hgrow := HTGeometry.one_add_pow_le_const_mul_exp ht (half_pos hr) D
  have hcol : Real.exp (r / 2 * t) * Real.exp (-(r * t)) = Real.exp (-(r / 2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (1 + t ^ D) * Real.exp (-(r * t))
      ≤ (2 * (1 + t) ^ D) * Real.exp (-(r * t)) :=
        mul_le_mul_of_nonneg_right hsplit (Real.exp_pos _).le
    _ ≤ (2 * ((Nat.factorial D : ℝ) / (r / 2) ^ D * Real.exp (r / 2) *
          Real.exp (r / 2 * t))) * Real.exp (-(r * t)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact hgrow
    _ = polyShiftConst D r * (Real.exp (r / 2 * t) * Real.exp (-(r * t))) := by
        rw [polyShiftConst]; ring
    _ = polyShiftConst D r * Real.exp (-(r / 2 * t)) := by rw [hcol]

theorem norm_bottomPoint_le {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    ‖((x : ℂ) - c * I)‖ ≤ |x| + c := by
  have hbound := norm_sub_le ((x : ℂ)) ((c : ℂ) * I)
  have h1 : ‖((x : ℂ))‖ = |x| := by simp
  have h2 : ‖((c : ℂ) * I)‖ = |c| := by simp
  rw [h1, h2, abs_of_nonneg hc] at hbound
  exact hbound

/-! ## The filtered atoms -/

/-- One filtered von-Mangoldt atom on the mass bottom edge. -/
def xiMassPolyBottomPrimeAtomIntegrand (P : Polynomial ℝ) (a c : ℝ) (τ : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  evalRealPolynomial P (((x : ℂ) - c * I) ^ 2) ^ 2 *
    xiMassBottomPrimeAtomIntegrand a c τ n x

/-- Depth-free filtered Fourier atom at the logarithmic frequency of `n`. -/
def xiMassPolyCenteredPrimeAtom (P : Polynomial ℝ) (a : ℝ) (τ : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (1 / 2 : ℂ) n *
    stripFourier (xiMassPolyAnalyticTest P a τ) (Real.log n : ℂ)

/-- **Atomwise depth erasure for the filtered test.** -/
theorem integral_xiMassPolyBottomPrimeAtom_eq_centered (P : Polynomial ℝ)
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (n : ℕ) :
    (∫ x : ℝ, xiMassPolyBottomPrimeAtomIntegrand P a c τ n x) =
      xiMassPolyCenteredPrimeAtom P a τ n := by
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hhalf).le
  have ha : 0 < a := lt_trans (lt_trans (by norm_num) hhalf) hca
  rcases eq_or_ne n 0 with rfl | hn
  · simp [xiMassPolyBottomPrimeAtomIntegrand, xiMassBottomPrimeAtomIntegrand,
      xiMassPolyCenteredPrimeAtom, LSeries.term_zero]
  · set D : ℕ := (xiMassPolySquare P).natDegree with hD
    set G : ℝ := xiMassPolyWeightConstant P c with hG
    have hG0 : 0 ≤ G := by rw [hG]; exact xiMassPolyWeightConstant_nonneg P hc0
    let F : ℂ → ℂ := fun z =>
      evalRealPolynomial P (z ^ 2) ^ 2 *
        (xiMassAnalyticTest a τ z * Complex.exp (-(I * (Real.log n : ℂ) * z)))
    have hdiff : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ F z := by
      intro z hz
      have hmem : z ∈ xiMassStrip a := lt_of_le_of_lt hz hca
      have hW : DifferentiableAt ℂ (fun w : ℂ => evalRealPolynomial P (w ^ 2) ^ 2) z := by
        have hQ : DifferentiableAt ℂ (evalRealPolynomial (xiMassPolySquare P)) z :=
          (hasDerivAt_evalRealPolynomial (xiMassPolySquare P) z).differentiableAt
        exact hQ.congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun w => (evalRealPolynomial_xiMassPolySquare P w).symm))
      exact hW.mul ((hasDerivAt_xiMassAnalyticTest ha τ hmem).differentiableAt.mul (by fun_prop))
    have hbound : ∀ z : ℂ, |z.im| ≤ c →
        ‖F z‖ ≤ (G * polyShiftConst D τ.re *
            Real.exp ((|τ.im| + |Real.log n|) * c)) *
          Real.exp (-(τ.re / 2 * |z.re|)) := by
      intro z hz
      have hznorm : ‖z‖ ≤ |z.re| + c := by
        have h1 := Complex.abs_re_le_norm z
        have h2 := Complex.abs_im_le_norm z
        have h3 : ‖z‖ ≤ |z.re| + |z.im| := by
          have := Complex.norm_le_abs_re_add_abs_im z
          linarith
        linarith [hz]
      have hw := norm_xiMassPolySquare_weight_le P (r := z.re) hc0 hznorm
      have hk := norm_xiMassFourierKernel_le hca hτ (Real.log n) hz
      have habs : (0 : ℝ) ≤ |z.re| := abs_nonneg _
      have hcol := one_add_pow_mul_exp_le D hτ habs
      rw [show F z = evalRealPolynomial P (z ^ 2) ^ 2 *
          (xiMassAnalyticTest a τ z * Complex.exp (-(I * (Real.log n : ℂ) * z))) from rfl,
        norm_mul]
      calc ‖evalRealPolynomial P (z ^ 2) ^ 2‖ *
            ‖xiMassAnalyticTest a τ z * Complex.exp (-(I * (Real.log n : ℂ) * z))‖
          ≤ (G * (1 + |z.re| ^ D)) *
              (Real.exp ((|τ.im| + |Real.log n|) * c) * Real.exp (-(τ.re * |z.re|))) := by
            refine mul_le_mul hw hk (norm_nonneg _) ?_
            have : (0 : ℝ) ≤ 1 + |z.re| ^ D := by positivity
            exact mul_nonneg hG0 this
        _ = (G * Real.exp ((|τ.im| + |Real.log n|) * c)) *
              ((1 + |z.re| ^ D) * Real.exp (-(τ.re * |z.re|))) := by ring
        _ ≤ (G * Real.exp ((|τ.im| + |Real.log n|) * c)) *
              (polyShiftConst D τ.re * Real.exp (-(τ.re / 2 * |z.re|))) := by
            refine mul_le_mul_of_nonneg_left hcol ?_
            exact mul_nonneg hG0 (Real.exp_pos _).le
        _ = (G * polyShiftConst D τ.re *
              Real.exp ((|τ.im| + |Real.log n|) * c)) *
            Real.exp (-(τ.re / 2 * |z.re|)) := by ring
    have hshift := integral_horizontal_shift_neg_of_decay hc0 (half_pos hτ) hdiff hbound
    have hpoint : ∀ x : ℝ,
        xiMassPolyBottomPrimeAtomIntegrand P a c τ n x =
          LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
              (1 / 2 : ℂ) n * F ((x : ℂ) - (c : ℂ) * I) := by
      intro x
      rw [xiMassPolyBottomPrimeAtomIntegrand, xiMassBottomPrimeAtomIntegrand, xiMassBottomTest,
        xiMassBottomLSeriesTerm_eq_centered_mul_fourierPhase hn]
      dsimp only [F]
      ring
    rw [show (∫ x : ℝ, xiMassPolyBottomPrimeAtomIntegrand P a c τ n x) =
        ∫ x : ℝ,
          LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
              (1 / 2 : ℂ) n * F ((x : ℂ) - (c : ℂ) * I) from
      integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [MeasureTheory.integral_const_mul, hshift]
    rw [xiMassPolyCenteredPrimeAtom, stripFourier]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [xiMassPolyAnalyticTest, F]
    ring

/-! ## Absolute convergence of the filtered atomization -/

theorem continuous_xiMassPolyBottomPrimeAtomIntegrand (P : Polynomial ℝ)
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (τ : ℂ) (n : ℕ) :
    Continuous (xiMassPolyBottomPrimeAtomIntegrand P a c τ n) :=
  (continuous_xiMassPolyWeight_shift P c).mul
    (continuous_xiMassBottomPrimeAtomIntegrand hhalf hca τ n)

theorem norm_xiMassPolyBottomPrimeAtomIntegrand_le (P : Polynomial ℝ)
    {a c : ℝ} {x : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) (n : ℕ) :
    ‖xiMassPolyBottomPrimeAtomIntegrand P a c τ n x‖ ≤
      (xiMassPolyWeightConstant P c * polyShiftConst (xiMassPolySquare P).natDegree τ.re *
          (Real.exp (|τ.im| * c) * xiMassBottomPrimeAtomWeight c n)) *
        Real.exp (-(τ.re / 2 * |x|)) := by
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hhalf).le
  set D : ℕ := (xiMassPolySquare P).natDegree with hD
  set G : ℝ := xiMassPolyWeightConstant P c with hG
  set E : ℝ := Real.exp (|τ.im| * c) with hE
  set W : ℝ := xiMassBottomPrimeAtomWeight c n with hW
  have hG0 : 0 ≤ G := by rw [hG]; exact xiMassPolyWeightConstant_nonneg P hc0
  have hW0 : 0 ≤ W := by rw [hW, xiMassBottomPrimeAtomWeight]; positivity
  have hw := norm_xiMassPolySquare_weight_le P (r := x) hc0 (norm_bottomPoint_le hc0 x)
  have hbase := norm_xiMassBottomPrimeAtomIntegrand_le hhalf hca hτ.le (x := x) n
  have hcol := one_add_pow_mul_exp_le D hτ (abs_nonneg x)
  rw [xiMassPolyBottomPrimeAtomIntegrand, norm_mul]
  calc ‖evalRealPolynomial P (((x : ℂ) - c * I) ^ 2) ^ 2‖ *
        ‖xiMassBottomPrimeAtomIntegrand a c τ n x‖
      ≤ (G * (1 + |x| ^ D)) * ((E * W) * Real.exp (-(τ.re * |x|))) := by
        refine mul_le_mul hw hbase (norm_nonneg _) ?_
        have : (0 : ℝ) ≤ 1 + |x| ^ D := by positivity
        exact mul_nonneg hG0 this
    _ = (G * (E * W)) * ((1 + |x| ^ D) * Real.exp (-(τ.re * |x|))) := by ring
    _ ≤ (G * (E * W)) * (polyShiftConst D τ.re * Real.exp (-(τ.re / 2 * |x|))) := by
        refine mul_le_mul_of_nonneg_left hcol ?_
        have hE0 : (0 : ℝ) ≤ E := by rw [hE]; positivity
        exact mul_nonneg hG0 (mul_nonneg hE0 hW0)
    _ = (G * polyShiftConst D τ.re * (E * W)) * Real.exp (-(τ.re / 2 * |x|)) := by ring

theorem integrable_xiMassPolyBottomPrimeAtomIntegrand (P : Polynomial ℝ)
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) (n : ℕ) :
    Integrable (xiMassPolyBottomPrimeAtomIntegrand P a c τ n) :=
  Integrable.mono'
    ((integrable_exp_neg_mul_abs (half_pos hτ)).const_mul
      (xiMassPolyWeightConstant P c * polyShiftConst (xiMassPolySquare P).natDegree τ.re *
        (Real.exp (|τ.im| * c) * xiMassBottomPrimeAtomWeight c n)))
    (continuous_xiMassPolyBottomPrimeAtomIntegrand P hhalf hca τ n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ =>
      norm_xiMassPolyBottomPrimeAtomIntegrand_le P hhalf hca hτ n)

theorem summable_integral_norm_xiMassPolyBottomPrimeAtomIntegrand (P : Polynomial ℝ)
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun n : ℕ =>
      ∫ x : ℝ, ‖xiMassPolyBottomPrimeAtomIntegrand P a c τ n x‖) := by
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hhalf).le
  set D : ℕ := (xiMassPolySquare P).natDegree with hD
  set G : ℝ := xiMassPolyWeightConstant P c with hG
  set E : ℝ := Real.exp (|τ.im| * c) with hE
  set J : ℝ := ∫ x : ℝ, Real.exp (-(τ.re / 2 * |x|)) with hJ
  have hG0 : 0 ≤ G := by rw [hG]; exact xiMassPolyWeightConstant_nonneg P hc0
  have hbound : ∀ n : ℕ,
      (∫ x : ℝ, ‖xiMassPolyBottomPrimeAtomIntegrand P a c τ n x‖) ≤
        (G * polyShiftConst D τ.re * E * J) * xiMassBottomPrimeAtomWeight c n := by
    intro n
    have hmajor : Integrable (fun x : ℝ =>
        (G * polyShiftConst D τ.re * (E * xiMassBottomPrimeAtomWeight c n)) *
          Real.exp (-(τ.re / 2 * |x|))) :=
      (integrable_exp_neg_mul_abs (half_pos hτ)).const_mul _
    calc (∫ x : ℝ, ‖xiMassPolyBottomPrimeAtomIntegrand P a c τ n x‖)
        ≤ ∫ x : ℝ, (G * polyShiftConst D τ.re *
            (E * xiMassBottomPrimeAtomWeight c n)) * Real.exp (-(τ.re / 2 * |x|)) :=
          integral_mono
            (integrable_xiMassPolyBottomPrimeAtomIntegrand P hhalf hca hτ n).norm
            hmajor
            (fun x => norm_xiMassPolyBottomPrimeAtomIntegrand_le P hhalf hca hτ n)
      _ = (G * polyShiftConst D τ.re * E * J) * xiMassBottomPrimeAtomWeight c n := by
          rw [MeasureTheory.integral_const_mul, hJ]
          ring
  exact Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _)
    hbound
    ((summable_xiMassBottomPrimeAtomWeight hhalf).mul_left _)

/-- The filtered depth-free prime-log Fourier atoms are absolutely summable. -/
theorem summable_xiMassPolyCenteredPrimeAtom (P : Polynomial ℝ)
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (xiMassPolyCenteredPrimeAtom P a τ) := by
  have hnorm : Summable (fun n : ℕ =>
      ‖∫ x : ℝ, xiMassPolyBottomPrimeAtomIntegrand P a c τ n x‖) :=
    Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun _ => norm_integral_le_integral_norm _)
      (summable_integral_norm_xiMassPolyBottomPrimeAtomIntegrand P hhalf hca hτ)
  have hint : Summable (fun n : ℕ =>
      ∫ x : ℝ, xiMassPolyBottomPrimeAtomIntegrand P a c τ n x) :=
    summable_norm_iff.mp hnorm
  exact hint.congr (fun n => integral_xiMassPolyBottomPrimeAtom_eq_centered P hhalf hca hτ n)

theorem xiMassPolyBottomPrimeIntegrand_eq_tsum_atom (P : Polynomial ℝ)
    (a c : ℝ) (τ : ℂ) (x : ℝ) :
    xiMassPolyBottomPrimeIntegrand P a c τ x =
      ∑' n : ℕ, xiMassPolyBottomPrimeAtomIntegrand P a c τ n x := by
  rw [xiMassPolyBottomPrimeIntegrand, xiMassBottomPrimeIntegrand_eq_tsum_atom,
    ← tsum_mul_left]
  rfl

/-- **Complete atomization of the filtered prime bottom integral.** -/
theorem integral_xiMassPolyBottomPrimeIntegrand_eq_tsum_centeredAtom (P : Polynomial ℝ)
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    (∫ x : ℝ, xiMassPolyBottomPrimeIntegrand P a c τ x) =
      ∑' n : ℕ, xiMassPolyCenteredPrimeAtom P a τ n := by
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun n => integrable_xiMassPolyBottomPrimeAtomIntegrand P hhalf hca hτ n)
    (summable_integral_norm_xiMassPolyBottomPrimeAtomIntegrand P hhalf hca hτ)
  calc (∫ x : ℝ, xiMassPolyBottomPrimeIntegrand P a c τ x)
      = ∫ x : ℝ, ∑' n : ℕ, xiMassPolyBottomPrimeAtomIntegrand P a c τ n x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x =>
          xiMassPolyBottomPrimeIntegrand_eq_tsum_atom P a c τ x)
    _ = ∑' n : ℕ, ∫ x : ℝ, xiMassPolyBottomPrimeAtomIntegrand P a c τ n x := hswap.symm
    _ = ∑' n : ℕ, xiMassPolyCenteredPrimeAtom P a τ n :=
        tsum_congr (fun n => integral_xiMassPolyBottomPrimeAtom_eq_centered P hhalf hca hτ n)

end

end RHTower
