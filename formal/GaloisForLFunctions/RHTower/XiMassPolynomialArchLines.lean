import GaloisForLFunctions.RHTower.XiMassPolynomialArchVertical

/-!
# The filtered archimedean bottom and centred lines

The even polynomial weight multiplies the archimedean edge integrands; on both the depth-`c` bottom
line and the centred real line it is dominated by a shifted power of the real part, so the base
majorants survive with polynomial factors that the strip exponential still absorbs.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section


/-- Polynomial-filtered archimedean integrand on the bottom edge. -/
def xiMassPolyBottomArchIntegrand (P : Polynomial ℝ) (a c : ℝ) (τ : ℂ) (x : ℝ) : ℂ :=
  evalRealPolynomial P (((x : ℂ) - c * I) ^ (2 : ℕ)) ^ (2 : ℕ) * xiMassBottomArchIntegrand a c τ x

/-- Polynomial-filtered archimedean integrand on the centred real line. -/
def xiMassPolyCenteredArchIntegrand (P : Polynomial ℝ) (a : ℝ) (τ : ℂ) (x : ℝ) : ℂ :=
  evalRealPolynomial P ((x : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) * xiMassCenteredArchIntegrand a τ x

theorem continuous_xiMassPolyWeight_shift (P : Polynomial ℝ) (c : ℝ) :
    Continuous (fun x : ℝ => evalRealPolynomial P (((x : ℂ) - c * I) ^ (2 : ℕ)) ^ (2 : ℕ)) := by
  have hQ : Continuous (fun x : ℝ =>
      evalRealPolynomial (xiMassPolySquare P) ((x : ℂ) - c * I)) :=
    (continuous_evalRealPolynomial (xiMassPolySquare P)).comp (by fun_prop)
  exact hQ.congr fun x => evalRealPolynomial_xiMassPolySquare P _

theorem continuous_xiMassPolyWeight_centered (P : Polynomial ℝ) :
    Continuous (fun x : ℝ => evalRealPolynomial P ((x : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ)) := by
  have hQ : Continuous (fun x : ℝ => evalRealPolynomial (xiMassPolySquare P) (x : ℂ)) :=
    (continuous_evalRealPolynomial (xiMassPolySquare P)).comp (by fun_prop)
  exact hQ.congr fun x => evalRealPolynomial_xiMassPolySquare P _

theorem continuous_xiMassPolyBottomArchIntegrand (P : Polynomial ℝ) {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (τ : ℂ) :
    Continuous (xiMassPolyBottomArchIntegrand P a c τ) :=
  (continuous_xiMassPolyWeight_shift P c).mul
    (continuous_xiMassBottomArchIntegrand hhalf hca τ)

theorem continuous_xiMassPolyCenteredArchIntegrand (P : Polynomial ℝ) {a : ℝ}
    (ha : 0 < a) (τ : ℂ) :
    Continuous (xiMassPolyCenteredArchIntegrand P a τ) :=
  (continuous_xiMassPolyWeight_centered P).mul
    (continuous_xiMassCenteredArchIntegrand ha τ)

/-- The filtered archimedean bottom edge is absolutely integrable at every legal depth. -/
theorem integrable_xiMassPolyBottomArchIntegrand (P : Polynomial ℝ) {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Integrable (xiMassPolyBottomArchIntegrand P a c τ) := by
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hhalf).le
  set D : ℕ := (xiMassPolySquare P).natDegree with hDEq
  set G : ℝ := xiMassPolyWeightConstant P c with hGEq
  set E : ℝ := Real.exp (|τ.im| * c) with hEEq
  set A : ℝ := xiMassBottomArchGrowthConstant c with hAEq
  let T : ℝ := max 2 (1 / 2 + c)
  let S : Set ℝ := {x : ℝ | T ≤ |x|}
  have hG : 0 ≤ G := xiMassPolyWeightConstant_nonneg P hc0
  have hE : 0 < E := Real.exp_pos _
  have hmajor : Integrable (fun x : ℝ =>
      (G * E * A) * (|x| ^ (0 : ℕ) * Real.exp (-τ.re * |x|)) +
      (G * E / 2) * (|x| ^ (1 : ℕ) * Real.exp (-τ.re * |x|)) +
      (G * E * A) * (|x| ^ D * Real.exp (-τ.re * |x|)) +
      (G * E / 2) * (|x| ^ (D + 1) * Real.exp (-τ.re * |x|))) :=
    ((((HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hτ).const_mul (G * E * A)).add
      ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs 1 hτ).const_mul (G * E / 2))).add
      ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs D hτ).const_mul (G * E * A))).add
      ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs (D + 1) hτ).const_mul (G * E / 2))
  have hS : MeasurableSet S := by
    dsimp only [S]
    exact measurableSet_le measurable_const continuous_abs.measurable
  have htail : IntegrableOn (xiMassPolyBottomArchIntegrand P a c τ) S := by
    refine hmajor.integrableOn.mono'
      (continuous_xiMassPolyBottomArchIntegrand P hhalf hca τ).aestronglyMeasurable.restrict ?_
    filter_upwards [self_mem_ae_restrict hS] with x hx
    have hxT : T ≤ |x| := hx
    have hznorm : ‖((x : ℂ) - c * I)‖ ≤ |x| + c := by
      have hbound := norm_sub_le ((x : ℂ)) ((c : ℂ) * I)
      have h1 : ‖((x : ℂ))‖ = |x| := by simp
      have h2 : ‖((c : ℂ) * I)‖ = |c| := by simp
      rw [h1, h2, abs_of_nonneg hc0] at hbound
      exact hbound
    have hw := norm_xiMassPolySquare_weight_le P (r := x) hc0 hznorm
    have hm := norm_xiMassBottomTest_le hhalf hca hτ.le (x := x)
    have harch := norm_logDeriv_archFactor_xiMassBottom_le hhalf hxT
    have hbase : ‖xiMassBottomArchIntegrand a c τ x‖
        ≤ (E * Real.exp (-(τ.re * |x|))) * (A + |x| / 2) := by
      rw [xiMassBottomArchIntegrand, norm_mul]
      exact mul_le_mul hm harch (norm_nonneg _) (by positivity)
    have hexpEq : Real.exp (-(τ.re * |x|)) = Real.exp (-τ.re * |x|) := by
      rw [show -(τ.re * |x|) = -τ.re * |x| by ring]
    rw [xiMassPolyBottomArchIntegrand, norm_mul]
    calc ‖evalRealPolynomial P (((x : ℂ) - c * I) ^ (2 : ℕ)) ^ (2 : ℕ)‖ *
          ‖xiMassBottomArchIntegrand a c τ x‖
        ≤ (G * (1 + |x| ^ D)) * ((E * Real.exp (-(τ.re * |x|))) * (A + |x| / 2)) := by
          refine mul_le_mul hw hbase (norm_nonneg _) ?_
          positivity
      _ = (G * E * A) * (|x| ^ (0 : ℕ) * Real.exp (-τ.re * |x|)) +
          (G * E / 2) * (|x| ^ (1 : ℕ) * Real.exp (-τ.re * |x|)) +
          (G * E * A) * (|x| ^ D * Real.exp (-τ.re * |x|)) +
          (G * E / 2) * (|x| ^ (D + 1) * Real.exp (-τ.re * |x|)) := by
          rw [hexpEq, pow_succ]
          ring
  have hcompact : IntegrableOn (xiMassPolyBottomArchIntegrand P a c τ) (Icc (-T) T) :=
    (continuous_xiMassPolyBottomArchIntegrand P hhalf hca τ).integrableOn_Icc
  have hcover : Icc (-T) T ∪ S = univ := by
    ext x
    simp only [mem_union, mem_Icc, mem_univ, iff_true, S, mem_setOf_eq]
    by_cases h : |x| ≤ T
    · exact Or.inl (abs_le.mp h)
    · exact Or.inr (by linarith)
  rw [← integrableOn_univ, ← hcover]
  exact hcompact.union htail

/-- The filtered archimedean centred line is absolutely integrable. -/
theorem integrable_xiMassPolyCenteredArchIntegrand (P : Polynomial ℝ) {a σ u : ℝ}
    (ha : 0 < a) (hσ : 0 < σ) :
    Integrable (xiMassPolyCenteredArchIntegrand P a (σ + u * I)) := by
  set D : ℕ := (xiMassPolySquare P).natDegree with hDEq
  set G : ℝ := xiMassPolyWeightConstant P 0 with hGEq
  set C : ℝ := xiMassArchVerticalGrowthConstant with hCEq
  let S : Set ℝ := {x : ℝ | 2 ≤ |x|}
  have hG : 0 ≤ G := xiMassPolyWeightConstant_nonneg P le_rfl
  have hC : 0 ≤ C := xiMassArchVerticalGrowthConstant_nonneg
  have hσre : ((σ : ℂ) + u * I).re = σ := by simp [Complex.mul_re]
  have hmajor : Integrable (fun x : ℝ =>
      (G * C) * (|x| ^ (0 : ℕ) * Real.exp (-σ * |x|)) +
      (G / 2) * (|x| ^ (1 : ℕ) * Real.exp (-σ * |x|)) +
      (G * C) * (|x| ^ D * Real.exp (-σ * |x|)) +
      (G / 2) * (|x| ^ (D + 1) * Real.exp (-σ * |x|))) := by
    have hτ : (0 : ℝ) < ((σ : ℂ) + u * I).re := by rw [hσre]; exact hσ
    have h := ((((HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hτ).const_mul (G * C)).add
      ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs 1 hτ).const_mul (G / 2))).add
      ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs D hτ).const_mul (G * C))).add
      ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs (D + 1) hτ).const_mul (G / 2))
    rw [hσre] at h
    exact h
  have hS : MeasurableSet S := by
    dsimp only [S]
    exact measurableSet_le measurable_const continuous_abs.measurable
  have htail : IntegrableOn (xiMassPolyCenteredArchIntegrand P a (σ + u * I)) S := by
    refine hmajor.integrableOn.mono'
      (continuous_xiMassPolyCenteredArchIntegrand P ha _).aestronglyMeasurable.restrict ?_
    filter_upwards [self_mem_ae_restrict hS] with x hx
    have hx2 : (2 : ℝ) ≤ |x| := hx
    have hznorm : ‖((x : ℂ))‖ ≤ |x| + 0 := by simp
    have hw := norm_xiMassPolySquare_weight_le P (r := x) le_rfl hznorm
    have hbase := norm_xiMassCenteredArchIntegrand_le (u := u) ha hσ hx2
    have hexpEq : Real.exp (-(σ * |x|)) = Real.exp (-σ * |x|) := by
      rw [show -(σ * |x|) = -σ * |x| by ring]
    rw [xiMassPolyCenteredArchIntegrand, norm_mul]
    calc ‖evalRealPolynomial P ((x : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ)‖ *
          ‖xiMassCenteredArchIntegrand a (σ + u * I) x‖
        ≤ (G * (1 + |x| ^ D)) * (Real.exp (-(σ * |x|)) * (C + |x| / 2)) := by
          refine mul_le_mul hw hbase (norm_nonneg _) ?_
          positivity
      _ = (G * C) * (|x| ^ (0 : ℕ) * Real.exp (-σ * |x|)) +
          (G / 2) * (|x| ^ (1 : ℕ) * Real.exp (-σ * |x|)) +
          (G * C) * (|x| ^ D * Real.exp (-σ * |x|)) +
          (G / 2) * (|x| ^ (D + 1) * Real.exp (-σ * |x|)) := by
          rw [hexpEq, pow_succ]
          ring
  have hcompact : IntegrableOn (xiMassPolyCenteredArchIntegrand P a (σ + u * I))
      (Icc (-2) 2) :=
    (continuous_xiMassPolyCenteredArchIntegrand P ha _).integrableOn_Icc
  have hcover : Icc (-2 : ℝ) 2 ∪ S = univ := by
    ext x
    simp only [mem_union, mem_Icc, mem_univ, iff_true, S, mem_setOf_eq]
    by_cases h : |x| ≤ 2
    · exact Or.inl (abs_le.mp h)
    · exact Or.inr (by linarith)
  rw [← integrableOn_univ, ← hcover]
  exact hcompact.union htail

/-- On the centred line the filtered modulus does not depend on the vertical time. -/
theorem norm_xiMassPolyCenteredArchIntegrand_verticalTime_eq (P : Polynomial ℝ)
    {a σ u x : ℝ} (ha : 0 < a) :
    ‖xiMassPolyCenteredArchIntegrand P a (σ + u * I) x‖ =
      ‖xiMassPolyCenteredArchIntegrand P a (σ : ℂ) x‖ := by
  rw [xiMassPolyCenteredArchIntegrand, xiMassPolyCenteredArchIntegrand, norm_mul, norm_mul,
    norm_xiMassCenteredArchIntegrand_verticalTime_eq ha]

theorem tendsto_integral_xiMassPolyBottomArchIntegrand_atTop (P : Polynomial ℝ)
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (fun R : ℝ => ∫ x in -R..R, xiMassPolyBottomArchIntegrand P a c τ x)
      atTop (𝓝 (∫ x : ℝ, xiMassPolyBottomArchIntegrand P a c τ x)) :=
  intervalIntegral_tendsto_integral
    (integrable_xiMassPolyBottomArchIntegrand P hhalf hca hτ)
    (tendsto_neg_atBot_iff.mpr tendsto_id) tendsto_id

theorem tendsto_integral_xiMassPolyCenteredArchIntegrand_atTop (P : Polynomial ℝ)
    {a σ u : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    Tendsto (fun R : ℝ => ∫ x in -R..R,
      xiMassPolyCenteredArchIntegrand P a (σ + u * I) x)
      atTop (𝓝 (∫ x : ℝ, xiMassPolyCenteredArchIntegrand P a (σ + u * I) x)) :=
  intervalIntegral_tendsto_integral
    (integrable_xiMassPolyCenteredArchIntegrand P ha hσ)
    (tendsto_neg_atBot_iff.mpr tendsto_id) tendsto_id

end

end RHTower
