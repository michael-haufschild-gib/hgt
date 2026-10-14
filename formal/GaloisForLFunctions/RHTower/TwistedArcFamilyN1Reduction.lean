import GaloisForLFunctions.RHTower.SingleTwistArcGenerator
import GaloisForLFunctions.RHTower.TwistedArcMomentN1Reduction
import GaloisForLFunctions.RHTower.ModularTwoArcWitnessMass

/-!
# The twist family: decay-class (N1) line witnesses from any `a ∈ [0, ¼)`

For `a ∈ ℝ` the `a`-twisted arc vector is `g_u − a s_u`, where `g_u` is the twisted arc vector
(log profile `√(y/2)(¼ − ∂²)² 𝒦_u`) and `s_u` the single-twisted one (`√(y/2)(¼ − ∂²) 𝒦_u`).  On the
arc this is the operator `𝔐(𝔐 − a)`; its spectral multiplier is `(¼ + τ²)(¼ + τ² − a)`, positive on
`ℝ` for `a < ¼`.  The mass is `∫ (g_u − a s_u) = −4a √y_u` (`integral_swArcVector`), negative for
`a > 0`.

For a finite measure `ν` on the arc and a bounded signed density `g`, put
`m_j = ∫ g(u) √(y_u/2) u^{2j} dν` and `h_a = ∫ g(u)(g_u − a s_u) dν(u)` (`famWitness`).

* `integral_cos_mul_famWitnessProfile_eq`: the log-profile spectrum of `h_a` is
  `(¼ + τ²)(¼ + τ² − a) Σ_j 2 C(−½, 2j) C_j(τ) m_j`.
* `integral_famWitness`: `∫ h_a = −4√2 a m_0`.

**Theorem** (`exists_decayClass_fullLineWitness_of_familyMomentPositive`).  If for some
`a ∈ [0, ¼)` the density annihilates every `a`-twisted integer moment
`∫ (g_u − a s_u)(x) cos(2π(n+2)x) dx`, all `m_j ≥ 0` and `m_0 > 0`, then there is a decay-class
(N1) line witness blind at every integer `m ≥ 2`.

Proof.  `h_a` is even, self-reciprocal, blind at every `m ≥ 2`, strictly positive definite and of
mass `−4√2 a m_0 ≤ 0`.  The two-arc witness `h₊` (`exists_twoArcWitness_mass`) is blind at every
`m ≥ 1`, strictly positive definite, has log profile `O((cosh v)^{−5/2})` and positive mass.  The
combination `(∫ h₊) h_a + 4√2 a m_0 h₊` has mass zero and keeps every other property.  At `a = 0`
this is the twisted arc reduction; for `a ∈ (0, ¼)` the negative mass of `h_a` is cancelled by
`h₊`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

section Weighted

variable {ν : Measure ArcParam} [IsFiniteMeasure ν] {g : ArcParam → ℝ} {B : ℝ}

/-- The weighted single-twisted superposition `∫ g(u) s_u dν(u)`. -/
def swWitnessW (ν : Measure ArcParam) (g : ArcParam → ℝ) (x : ℝ) : ℝ :=
  ∫ u, g u * swArcVector u x ∂ν

/-- Its derivative. -/
def swWitnessWDeriv (ν : Measure ArcParam) (g : ArcParam → ℝ) (x : ℝ) : ℝ :=
  ∫ u, g u * swArcDeriv u x ∂ν

theorem hasDerivAt_swWitnessW (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) (x : ℝ) :
    HasDerivAt (swWitnessW ν g) (swWitnessWDeriv ν g x) x := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun (x : ℝ) (u : ArcParam) => g u * swArcVector u x)
    (F' := fun x u => g u * swArcDeriv u x) (x₀ := x) (bound := fun _ => B * 900)
    (s := univ) Filter.univ_mem
    (Eventually.of_forall fun x' =>
      (hg.mul (continuous_swArcVector_at x').measurable).aestronglyMeasurable)
    (integrable_g_mul_of_bound hg hgB (continuous_swArcVector_at x)
      (C := 60) fun u => (abs_swArcVector_le u x).trans (by
        have : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
        nlinarith))
    (hg.mul (continuous_swArcDeriv_at x).measurable).aestronglyMeasurable
    (Eventually.of_forall fun u x' _ => by
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul (hgB u) ((abs_swArcDeriv_le u x').trans ?_) (abs_nonneg _) hB0
      have : (1 + x' ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x'])
      nlinarith)
    (integrable_const _)
    (Eventually.of_forall fun u x' _ => (hasDerivAt_swArcVector u x').const_mul (g u))
  exact key.2

theorem abs_swWitnessW_le (hgB : ∀ u, |g u| ≤ B) (x : ℝ) :
    |swWitnessW ν g x| ≤ B * ν.real univ * 60 * (1 + x ^ 2)⁻¹ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun u => g u * swArcVector u x) (C := B * (60 * (1 + x ^ 2)⁻¹))
    (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgB u) (abs_swArcVector_le u x) (abs_nonneg _) hB0)
  rw [Real.norm_eq_abs] at h
  unfold swWitnessW
  calc _ ≤ B * (60 * (1 + x ^ 2)⁻¹) * ν.real univ := h
    _ = _ := by ring

theorem abs_swWitnessWDeriv_le (hgB : ∀ u, |g u| ≤ B) (x : ℝ) :
    |swWitnessWDeriv ν g x| ≤ B * ν.real univ * 900 * (1 + x ^ 2)⁻¹ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun u => g u * swArcDeriv u x) (C := B * (900 * (1 + x ^ 2)⁻¹))
    (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgB u) (abs_swArcDeriv_le u x) (abs_nonneg _) hB0)
  rw [Real.norm_eq_abs] at h
  unfold swWitnessWDeriv
  calc _ ≤ B * (900 * (1 + x ^ 2)⁻¹) * ν.real univ := h
    _ = _ := by ring

theorem continuous_swWitnessW (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    Continuous (swWitnessW ν g) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_swWitnessW hg hgB x).continuousAt

theorem continuous_swWitnessWDeriv (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    Continuous (swWitnessWDeriv ν g) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  unfold swWitnessWDeriv
  refine continuous_of_dominated (bound := fun _ => B * 900) (fun x => ?_)
    (fun x => Eventually.of_forall fun u => ?_) (integrable_const _)
    (Eventually.of_forall fun u => ?_)
  · exact (hg.mul (continuous_swArcDeriv_at x).measurable).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (hgB u) ((abs_swArcDeriv_le u x).trans ?_) (abs_nonneg _) hB0
    have : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
    nlinarith
  · exact continuous_const.mul (continuous_swArcDeriv u)

omit [IsFiniteMeasure ν] in
theorem swWitnessW_neg (x : ℝ) : swWitnessW ν g (-x) = swWitnessW ν g x := by
  unfold swWitnessW; simp_rw [swArcVector_neg]

omit [IsFiniteMeasure ν] in
theorem swWitnessW_inv {x : ℝ} (hx : x ≠ 0) :
    swWitnessW ν g (1 / x) = |x| * swWitnessW ν g x := by
  unfold swWitnessW
  simp_rw [swArcVector_inv _ hx]
  rw [← integral_const_mul]
  congr 1; funext u; ring

/-- `∫ ∫ g(u) s_u dν = 4 ∫ g(u) √y_u dν`. -/
theorem integral_swWitnessW (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    ∫ x, swWitnessW ν g x = 4 * ∫ u, g u * Real.sqrt (modularArcHeight u) ∂ν := by
  unfold swWitnessW
  rw [integral_integral_swap (integrable_prod_g_mul (ν := ν) hg hgB
    (F := fun x u => swArcVector u x) continuous_swArcVector_param
    (fun x u => abs_swArcVector_le u x))]
  simp_rw [integral_const_mul, integral_swArcVector]
  rw [← integral_const_mul]
  congr 1; funext u; ring

theorem integral_swWitnessWDeriv_mul_sin (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) (ω : ℝ) :
    ∫ x, swWitnessWDeriv ν g x * Real.sin (ω * x) =
      -(ω * ∫ u, g u * (∫ x, swArcVector u x * Real.cos (ω * x)) ∂ν) := by
  unfold swWitnessWDeriv
  simp_rw [← integral_mul_const]
  have hsw := integral_integral_swap (integrable_prod_g_mul (ν := ν) hg hgB
    (F := fun x u => swArcDeriv u x * Real.sin (ω * x)) (C := 900)
    (continuous_swArcDeriv_param.mul (by fun_prop))
    (fun x u => by
      rw [abs_mul]
      exact (mul_le_mul (abs_swArcDeriv_le u x) (Real.abs_sin_le_one _) (abs_nonneg _)
        (by positivity)).trans (by rw [mul_one])))
  simp only [mul_assoc] at hsw ⊢
  rw [hsw]
  simp_rw [integral_const_mul, integral_swArcDeriv_mul_sin]
  rw [← integral_const_mul, ← integral_neg]
  congr 1; funext u; ring

/-- The weighted moment series `Σ_j 2 C(−½, 2j) C_j(τ) m_j`. -/
def arcMomentSeries (ν : Measure ArcParam) (g : ArcParam → ℝ) (τ : ℝ) : ℝ :=
  ∑' j, 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * coshPowerTransform j τ *
    ∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν

/-- The moment series of a moment-positive density is positive. -/
theorem arcMomentSeries_pos (hgB : ∀ u, |g u| ≤ B)
    (hmom : ∀ j : ℕ, 0 ≤ ∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν)
    (hmass : 0 < ∫ u, g u * Real.sqrt (modularArcHeight u / 2) ∂ν) (τ : ℝ) :
    0 < arcMomentSeries ν g τ := by
  set t : ℕ → ℝ := fun j => 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * coshPowerTransform j τ *
    ∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν with ht
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have ht0 : ∀ j, 0 ≤ t j := fun j =>
    mul_nonneg (mul_nonneg (mul_nonneg two_pos.le (choose_neg_half_even_pos j).le)
      (coshPowerTransform_pos j τ).le) (hmom j)
  have hmj : ∀ j, |∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν| ≤
      B * ν.real univ * (1 / 4 : ℝ) ^ j := fun j => by
    have h := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun u => g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)))
      (C := B * (1 / 4 : ℝ) ^ j)
      (Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)| ≤ (1 / 4 : ℝ) ^ j := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          have hs : Real.sqrt (modularArcHeight u / 2) ≤ 1 := by
            rw [Real.sqrt_le_one]
            have : modularArcHeight u ≤ 1 := by
              unfold modularArcHeight; rw [Real.sqrt_le_one]; nlinarith [sq_nonneg (u : ℝ)]
            linarith
          have hp : |(u : ℝ) ^ (2 * j)| ≤ (1 / 4 : ℝ) ^ j := by
            rw [abs_pow, pow_mul]
            refine pow_le_pow_left₀ (by positivity) ?_ j
            have := abs_arcParam_le u
            nlinarith [abs_nonneg (u : ℝ), sq_abs (u : ℝ)]
          calc Real.sqrt (modularArcHeight u / 2) * |(u : ℝ) ^ (2 * j)| ≤ 1 * (1 / 4 : ℝ) ^ j :=
                mul_le_mul hs hp (abs_nonneg _) zero_le_one
            _ = (1 / 4 : ℝ) ^ j := one_mul _
        exact mul_le_mul (hgB u) h1 (abs_nonneg _) hB0)
    rw [Real.norm_eq_abs] at h
    calc _ ≤ B * (1 / 4 : ℝ) ^ j * ν.real univ := h
      _ = _ := by ring
  have hsum : Summable t := by
    refine Summable.of_nonneg_of_le ht0 (fun j => ?_)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).mul_left
        (2 * (∫ v, Real.cosh v ^ (-(1 / 2) : ℝ)) * (B * ν.real univ)))
    calc t j ≤ |t j| := le_abs_self _
      _ = 2 * |Ring.choose (-1 / 2 : ℝ) (2 * j)| * |coshPowerTransform j τ| *
          |∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν| := by
        simp only [ht]; rw [abs_mul, abs_mul, abs_mul, abs_two]
      _ ≤ 2 * 1 * (∫ v, Real.cosh v ^ (-(1 / 2) : ℝ)) * (B * ν.real univ * (1 / 4 : ℝ) ^ j) := by
        gcongr
        · exact abs_choose_neg_half_le_one _
        · exact abs_coshPowerTransform_le j τ
        · exact hmj j
      _ = _ := by ring
  exact hsum.tsum_pos ht0 0 (by
    simp only [ht]
    refine mul_pos (mul_pos (by simp) (coshPowerTransform_pos 0 τ)) ?_
    simpa using hmass)

/-- The cosine transform of the single-twisted witness profile:
`∫ cos(τv) e^{v/2} h(e^v) dv = (¼+τ²) Σ_j 2 C(−½, 2j) C_j(τ) m_j`. -/
theorem integral_cos_mul_swWitnessWProfile_eq (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B)
    (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * swWitnessW ν g (Real.exp v)) =
      (1 / 4 + τ ^ 2) * arcMomentSeries ν g τ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have hbound : ∀ u : ArcParam, ∀ v : ℝ,
      |Real.cos (τ * v) * (Real.exp (v / 2) * swArcVector u (Real.exp v))| ≤
        60 * Real.exp (-(3 / 2 * |v|)) := fun u v => by
    rw [abs_mul]
    refine (mul_le_mul (Real.abs_cos_le_one _) (abs_exp_half_mul_swArcVector_le u v)
      (abs_nonneg _) zero_le_one).trans ?_
    rw [one_mul]; apply le_of_eq; congr 2; ring
  have hcont : Continuous fun p : ℝ × ArcParam =>
      Real.cos (τ * p.1) * (Real.exp (p.1 / 2) * swArcVector p.2 (Real.exp p.1)) := by
    have := continuous_swArcVector_param.comp
      ((Real.continuous_exp.comp continuous_fst).prodMk continuous_snd)
    exact (by fun_prop : Continuous fun p : ℝ × ArcParam => Real.cos (τ * p.1)).mul
      ((by fun_prop : Continuous fun p : ℝ × ArcParam => Real.exp (p.1 / 2)).mul this)
  have hprod : Integrable (Function.uncurry fun v (u : ArcParam) =>
      g u * (Real.cos (τ * v) * (Real.exp (v / 2) * swArcVector u (Real.exp v))))
      ((volume : Measure ℝ).prod ν) := by
    have hI : Integrable (fun z : ℝ × ArcParam =>
        (B * 60 * Real.exp (-(3 / 2 * |z.1|))) * (1 : ℝ)) ((volume : Measure ℝ).prod ν) :=
      ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 3 / 2)).const_mul (B * 60)).mul_prod
        (integrable_const _)
    refine hI.mono' ((hg.comp measurable_snd).mul hcont.measurable).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, mul_one]
    simp only [Function.uncurry]
    rw [abs_mul]
    calc |g z.2| * |Real.cos (τ * z.1) * (Real.exp (z.1 / 2) * swArcVector z.2 (Real.exp z.1))|
        ≤ B * (60 * Real.exp (-(3 / 2 * |z.1|))) :=
          mul_le_mul (hgB z.2) (hbound z.2 z.1) (abs_nonneg _) hB0
      _ = _ := by ring
  have e : ∀ v, Real.cos (τ * v) * (Real.exp (v / 2) * swWitnessW ν g (Real.exp v)) =
      ∫ u, g u * (Real.cos (τ * v) * (Real.exp (v / 2) * swArcVector u (Real.exp v))) ∂ν :=
    fun v => by
      unfold swWitnessW
      rw [← integral_const_mul, ← integral_const_mul]
      congr 1; funext u; ring
  simp_rw [e]
  rw [integral_integral_swap hprod]
  simp_rw [integral_const_mul]
  have hspec : ∀ u : ArcParam,
      ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * swArcVector u (Real.exp v)) =
      (1 / 4 + τ ^ 2) * (Real.sqrt (modularArcHeight u / 2) *
        ∑' j, 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * (u : ℝ) ^ (2 * j) *
          coshPowerTransform j τ) := by
    intro u
    rw [integral_cos_mul_swArcProfile,
      (hasSum_integral_cos_mul_symCoshKernel (abs_arcParam_lt u) τ).tsum_eq]
    ring
  simp_rw [hspec]
  set I₀ := ∫ v, Real.cosh v ^ (-(1 / 2) : ℝ) with hI₀
  set G : ℕ → ArcParam → ℝ := fun j u => g u * (Real.sqrt (modularArcHeight u / 2) *
    (2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * (u : ℝ) ^ (2 * j) * coshPowerTransform j τ)) with hG
  have hsqrt : ∀ u : ArcParam, Real.sqrt (modularArcHeight u / 2) ≤ 1 := fun u => by
    rw [Real.sqrt_le_one]
    have : modularArcHeight u ≤ 1 := by
      unfold modularArcHeight; rw [Real.sqrt_le_one]; nlinarith [sq_nonneg (u : ℝ)]
    linarith
  have hu2 : ∀ (j : ℕ) (u : ArcParam), |(u : ℝ) ^ (2 * j)| ≤ (1 / 4 : ℝ) ^ j := fun j u => by
    rw [abs_pow, pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ j
    have := abs_arcParam_le u
    rw [sq_abs]; nlinarith [abs_nonneg (u : ℝ), sq_abs (u : ℝ)]
  have hGbound : ∀ j u, |G j u| ≤ B * (2 * (1 / 4 : ℝ) ^ j * I₀) := by
    intro j u
    simp only [hG]
    rw [abs_mul, abs_mul]
    refine mul_le_mul (hgB u) ?_ (by positivity) hB0
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (modularArcHeight u / 2) *
          |2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * (u : ℝ) ^ (2 * j) * coshPowerTransform j τ|
        ≤ 1 * (2 * (1 / 4 : ℝ) ^ j * I₀) := by
          refine mul_le_mul (hsqrt u) ?_ (abs_nonneg _) zero_le_one
          rw [abs_mul, abs_mul, abs_mul, abs_two]
          calc 2 * |Ring.choose (-1 / 2 : ℝ) (2 * j)| * |(u : ℝ) ^ (2 * j)| *
                |coshPowerTransform j τ| ≤ 2 * 1 * (1 / 4 : ℝ) ^ j * I₀ := by
                gcongr
                · exact abs_choose_neg_half_le_one _
                · exact hu2 j u
                · exact abs_coshPowerTransform_le j τ
            _ = 2 * (1 / 4 : ℝ) ^ j * I₀ := by ring
      _ = _ := one_mul _
  have hGint : ∀ j, Integrable (G j) ν := fun j =>
    Integrable.of_bound (by
      simp only [hG]
      exact (hg.mul ((Real.continuous_sqrt.comp (continuous_modularArcHeight_param.div_const 2)).mul
        (continuous_const.mul (by fun_prop : Continuous fun u : ArcParam => (u : ℝ) ^ (2 * j))
          |>.mul continuous_const)).measurable).aestronglyMeasurable)
      _ (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hGbound j u)
  have hgeom : Summable fun j : ℕ => (1 / 4 : ℝ) ^ j :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hnormsum : Summable fun j => ∫ u, ‖G j u‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun u => norm_nonneg _)
      (fun j => ?_) ((hgeom.mul_left (B * 2 * I₀ * ν.real univ)))
    calc ∫ u, ‖G j u‖ ∂ν ≤ ∫ _u, B * (2 * (1 / 4 : ℝ) ^ j * I₀) ∂ν :=
          integral_mono (hGint j).norm (integrable_const _) fun u => by
            rw [Real.norm_eq_abs]; exact hGbound j u
      _ = B * 2 * I₀ * ν.real univ * (1 / 4 : ℝ) ^ j := by
          rw [integral_const, smul_eq_mul]; ring
  have hswap := integral_tsum_of_summable_integral_norm hGint hnormsum
  have hpt : ∀ u : ArcParam, g u * ((1 / 4 + τ ^ 2) * (Real.sqrt (modularArcHeight u / 2) *
      ∑' j, 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * (u : ℝ) ^ (2 * j) * coshPowerTransform j τ)) =
      (1 / 4 + τ ^ 2) * ∑' j, G j u := by
    intro u
    simp only [hG]
    conv_rhs => rw [tsum_mul_left, tsum_mul_left]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, ← hswap]
  unfold arcMomentSeries
  congr 1
  congr 1
  funext j
  simp only [hG]
  rw [← integral_const_mul]
  congr 1; funext u; ring

end Weighted

/-! ### The `a`-twisted witness -/

/-- The single-twisted integer moment `∫ s_u(x) cos(2π(n+2)x) dx`. -/
def swArcMoment (n : ℕ) (u : ArcParam) : ℝ :=
  ∫ x, swArcVector u x * Real.cos (arcFreq (n + 1) * x)

/-- The `a`-twisted witness `h_a = ∫ g(u)(g_u − a s_u) dν(u)`. -/
def famWitness (a : ℝ) (ν : Measure ArcParam) (g : ArcParam → ℝ) (x : ℝ) : ℝ :=
  twWitnessW ν g x - a * swWitnessW ν g x

/-- Its derivative. -/
def famWitnessDeriv (a : ℝ) (ν : Measure ArcParam) (g : ArcParam → ℝ) (x : ℝ) : ℝ :=
  twWitnessWDeriv ν g x - a * swWitnessWDeriv ν g x

section Family

variable {a : ℝ} {ν : Measure ArcParam} [IsFiniteMeasure ν] {g : ArcParam → ℝ} {B : ℝ}

theorem hasDerivAt_famWitness (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) (x : ℝ) :
    HasDerivAt (famWitness a ν g) (famWitnessDeriv a ν g x) x :=
  (hasDerivAt_twWitnessW hg hgB x).sub ((hasDerivAt_swWitnessW hg hgB x).const_mul a)

theorem abs_famWitness_le (hgB : ∀ u, |g u| ≤ B) (x : ℝ) :
    |famWitness a ν g x| ≤ B * ν.real univ * (9000 + |a| * 60) * (1 + x ^ 2)⁻¹ := by
  have h1 := abs_twWitnessW_le (ν := ν) hgB x
  have h2 := abs_swWitnessW_le (ν := ν) hgB x
  unfold famWitness
  calc |twWitnessW ν g x - a * swWitnessW ν g x|
      ≤ |twWitnessW ν g x| + |a| * |swWitnessW ν g x| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ B * ν.real univ * 9000 * (1 + x ^ 2)⁻¹ +
        |a| * (B * ν.real univ * 60 * (1 + x ^ 2)⁻¹) := by gcongr
    _ = _ := by ring

theorem abs_famWitnessDeriv_le (hgB : ∀ u, |g u| ≤ B) (x : ℝ) :
    |famWitnessDeriv a ν g x| ≤ B * ν.real univ * (260000 + |a| * 900) * (1 + x ^ 2)⁻¹ := by
  have h1 := abs_twWitnessWDeriv_le (ν := ν) hgB x
  have h2 := abs_swWitnessWDeriv_le (ν := ν) hgB x
  unfold famWitnessDeriv
  calc |twWitnessWDeriv ν g x - a * swWitnessWDeriv ν g x|
      ≤ |twWitnessWDeriv ν g x| + |a| * |swWitnessWDeriv ν g x| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ B * ν.real univ * 260000 * (1 + x ^ 2)⁻¹ +
        |a| * (B * ν.real univ * 900 * (1 + x ^ 2)⁻¹) := by gcongr
    _ = _ := by ring

theorem continuous_famWitness (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    Continuous (famWitness a ν g) :=
  (continuous_twWitnessW hg hgB).sub (continuous_const.mul (continuous_swWitnessW hg hgB))

theorem continuous_famWitnessDeriv (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    Continuous (famWitnessDeriv a ν g) :=
  (continuous_twWitnessWDeriv hg hgB).sub (continuous_const.mul (continuous_swWitnessWDeriv hg hgB))

omit [IsFiniteMeasure ν] in
theorem famWitness_neg (x : ℝ) : famWitness a ν g (-x) = famWitness a ν g x := by
  unfold famWitness; rw [twWitnessW_neg, swWitnessW_neg]

omit [IsFiniteMeasure ν] in
theorem famWitness_inv {x : ℝ} (hx : x ≠ 0) :
    famWitness a ν g (1 / x) = |x| * famWitness a ν g x := by
  unfold famWitness; rw [twWitnessW_inv hx, swWitnessW_inv hx]; ring

theorem integrable_famWitness (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    Integrable (famWitness a ν g) :=
  integrable_of_le_inv_one_add_sq (continuous_famWitness hg hgB) (abs_famWitness_le hgB)

theorem integrable_famWitnessDeriv (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    Integrable (famWitnessDeriv a ν g) :=
  integrable_of_le_inv_one_add_sq (continuous_famWitnessDeriv hg hgB) (abs_famWitnessDeriv_le hgB)

/-- **The mass of the `a`-twisted witness**: `∫ h_a = −4a ∫ g(u) √y_u dν`. -/
theorem integral_famWitness (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    ∫ x, famWitness a ν g x = -(4 * a * ∫ u, g u * Real.sqrt (modularArcHeight u) ∂ν) := by
  have i1 := integrable_of_le_inv_one_add_sq (continuous_twWitnessW (ν := ν) hg hgB)
    (abs_twWitnessW_le hgB)
  have i2 := integrable_of_le_inv_one_add_sq (continuous_swWitnessW (ν := ν) hg hgB)
    (abs_swWitnessW_le hgB)
  unfold famWitness
  rw [integral_sub i1 (i2.const_mul a), integral_const_mul, integral_twWitnessW_eq_zero hg hgB,
    integral_swWitnessW hg hgB]
  ring

theorem abs_swArcMoment_le (n : ℕ) (u : ArcParam) : |swArcMoment n u| ≤ 60 * Real.pi := by
  unfold swArcMoment
  have hb : ∀ x, ‖swArcVector u x * Real.cos (arcFreq (n + 1) * x)‖ ≤ 60 * (1 + x ^ 2)⁻¹ :=
    fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (abs_swArcVector_le u x) (Real.abs_cos_le_one _) (abs_nonneg _)
        (by positivity)).trans (by rw [mul_one])
  have h := norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul 60)
    (Eventually.of_forall hb)
  rw [integral_const_mul, integral_univ_inv_one_add_sq, Real.norm_eq_abs] at h
  exact h

theorem abs_twArcMoment_le (n : ℕ) (u : ArcParam) : |twArcMoment n u| ≤ 9000 * Real.pi := by
  unfold twArcMoment
  have h := norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul 9000)
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_twArcVector_mul_cos_le (arcFreq (n + 1)) u x)
  rw [integral_const_mul, integral_univ_inv_one_add_sq, Real.norm_eq_abs] at h
  exact h

theorem continuous_swArcMoment (n : ℕ) : Continuous (swArcMoment n) := by
  unfold swArcMoment
  refine continuous_of_dominated (bound := fun x => 60 * (1 + x ^ 2)⁻¹) (fun u => ?_)
    (fun u => Eventually.of_forall fun x => ?_) (integrable_inv_one_add_sq.const_mul _)
    (Eventually.of_forall fun x => ?_)
  · exact ((continuous_swArcVector u).mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (abs_swArcVector_le u x) (Real.abs_cos_le_one _) (abs_nonneg _)
      (by positivity)).trans (by rw [mul_one])
  · exact (continuous_swArcVector_at x).mul continuous_const

/-- **Blindness of the `a`-twisted witness.** -/
theorem integral_famWitnessDeriv_mul_sin (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B)
    (hblind : ∀ n : ℕ, ∫ u, g u * (twArcMoment n u - a * swArcMoment n u) ∂ν = 0) (n : ℕ) :
    ∫ x, famWitnessDeriv a ν g x * Real.sin (arcFreq (n + 1) * x) = 0 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have hν := measureReal_nonneg (μ := ν) (s := univ)
  have hs : Continuous fun x => Real.sin (arcFreq (n + 1) * x) := by fun_prop
  have i1 : Integrable fun x => twWitnessWDeriv ν g x * Real.sin (arcFreq (n + 1) * x) :=
    integrable_of_le_inv_one_add_sq ((continuous_twWitnessWDeriv hg hgB).mul hs)
      (C := B * ν.real univ * 260000) fun x => by
        rw [abs_mul]
        exact (mul_le_mul (abs_twWitnessWDeriv_le hgB x) (Real.abs_sin_le_one _) (abs_nonneg _)
          (by positivity)).trans (by rw [mul_one])
  have i2 : Integrable fun x => swWitnessWDeriv ν g x * Real.sin (arcFreq (n + 1) * x) :=
    integrable_of_le_inv_one_add_sq ((continuous_swWitnessWDeriv hg hgB).mul hs)
      (C := B * ν.real univ * 900) fun x => by
        rw [abs_mul]
        exact (mul_le_mul (abs_swWitnessWDeriv_le hgB x) (Real.abs_sin_le_one _) (abs_nonneg _)
          (by positivity)).trans (by rw [mul_one])
  have e : (fun x => famWitnessDeriv a ν g x * Real.sin (arcFreq (n + 1) * x)) = fun x =>
      twWitnessWDeriv ν g x * Real.sin (arcFreq (n + 1) * x) -
        a * (swWitnessWDeriv ν g x * Real.sin (arcFreq (n + 1) * x)) := by
    funext x; unfold famWitnessDeriv; ring
  have hm1 : Integrable (fun u => g u * twArcMoment n u) ν :=
    integrable_g_mul_of_bound hg hgB (continuous_twArcMoment n) (abs_twArcMoment_le n)
  have hm2 : Integrable (fun u => g u * swArcMoment n u) ν :=
    integrable_g_mul_of_bound hg hgB (continuous_swArcMoment n) (abs_swArcMoment_le n)
  rw [e, integral_sub i1 (i2.const_mul a), integral_const_mul,
    integral_twWitnessWDeriv_mul_sin hg hgB, integral_swWitnessWDeriv_mul_sin hg hgB]
  have hb := hblind n
  have e2 : (fun u => g u * (twArcMoment n u - a * swArcMoment n u)) =
      fun u => g u * twArcMoment n u - a * (g u * swArcMoment n u) := by funext u; ring
  rw [e2, integral_sub hm1 (hm2.const_mul a), integral_const_mul] at hb
  unfold twArcMoment swArcMoment at hb
  linear_combination (-arcFreq (n + 1)) * hb

theorem integrable_cos_mul_profile_of_le {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C * (1 + x ^ 2)⁻¹) (hinv : ∀ x, x ≠ 0 → f (1 / x) = |x| * f x) (τ : ℝ) :
    Integrable fun v => Real.cos (τ * v) * (Real.exp (v / 2) * f (Real.exp v)) := by
  have hI := (integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 3 / 2)).const_mul C
  refine hI.mono' (by fun_prop) (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h := abs_exp_half_mul_le_of_inv hC hinv v
  calc |Real.cos (τ * v)| * |Real.exp (v / 2) * f (Real.exp v)|
      ≤ 1 * (C * Real.exp (-(3 * |v| / 2))) :=
        mul_le_mul (Real.abs_cos_le_one _) h (abs_nonneg _) zero_le_one
    _ = C * Real.exp (-(3 / 2 * |v|)) := by ring_nf

/-- **The spectrum of the `a`-twisted witness**:
`(¼ + τ²)(¼ + τ² − a) Σ_j 2 C(−½, 2j) C_j(τ) m_j`. -/
theorem integral_cos_mul_famWitnessProfile_eq (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B)
    (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * famWitness a ν g (Real.exp v)) =
      (1 / 4 + τ ^ 2) * (1 / 4 + τ ^ 2 - a) * arcMomentSeries ν g τ := by
  have i1 := integrable_cos_mul_profile_of_le (continuous_twWitnessW (ν := ν) hg hgB)
    (abs_twWitnessW_le hgB) (fun _ hx => twWitnessW_inv hx) τ
  have i2 := integrable_cos_mul_profile_of_le (continuous_swWitnessW (ν := ν) hg hgB)
    (abs_swWitnessW_le hgB) (fun _ hx => swWitnessW_inv hx) τ
  have e : (fun v => Real.cos (τ * v) * (Real.exp (v / 2) * famWitness a ν g (Real.exp v))) =
      fun v => Real.cos (τ * v) * (Real.exp (v / 2) * twWitnessW ν g (Real.exp v)) -
        a * (Real.cos (τ * v) * (Real.exp (v / 2) * swWitnessW ν g (Real.exp v))) := by
    funext v; unfold famWitness; ring
  rw [e, integral_sub i1 (i2.const_mul a), integral_const_mul,
    integral_cos_mul_twWitnessWProfile_eq hg hgB, integral_cos_mul_swWitnessWProfile_eq hg hgB]
  unfold arcMomentSeries
  ring

/-- **Strict positive definiteness of the `a`-twisted witness**, for `a < ¼` and a
moment-positive density. -/
theorem integral_cos_mul_famWitnessProfile_pos (ha : a < 1 / 4) (hg : Measurable g)
    (hgB : ∀ u, |g u| ≤ B)
    (hmom : ∀ j : ℕ, 0 ≤ ∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν)
    (hmass : 0 < ∫ u, g u * Real.sqrt (modularArcHeight u / 2) ∂ν) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * famWitness a ν g (Real.exp v)) := by
  rw [integral_cos_mul_famWitnessProfile_eq hg hgB]
  have h1 : 0 < 1 / 4 + τ ^ 2 := by positivity
  have h2 : 0 < 1 / 4 + τ ^ 2 - a := by nlinarith [sq_nonneg τ]
  exact mul_pos (mul_pos h1 h2) (arcMomentSeries_pos hgB hmom hmass τ)

end Family

/-! ### The family reduction -/

theorem cosh_rpow_neg_five_halves_le (v : ℝ) :
    Real.cosh v ^ (-(5 / 2) : ℝ) ≤ 2 ^ (3 / 2 : ℝ) * Real.exp (-(3 * |v| / 2)) := by
  have hc1 := Real.one_le_cosh v
  have he : Real.exp |v| / 2 ≤ Real.cosh v := by
    rw [← Real.cosh_abs, Real.cosh_eq]; linarith [Real.exp_pos (-|v|)]
  have h1 : Real.cosh v ^ (-(5 / 2) : ℝ) ≤ Real.cosh v ^ (-(3 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have h2 : Real.cosh v ^ (-(3 / 2) : ℝ) ≤ (Real.exp |v| / 2) ^ (-(3 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) he (by norm_num)
  have h3 : (Real.exp |v| / 2) ^ (-(3 / 2) : ℝ) = 2 ^ (3 / 2 : ℝ) * Real.exp (-(3 * |v| / 2)) := by
    rw [Real.div_rpow (Real.exp_pos _).le (by norm_num), ← Real.exp_mul,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
    ring_nf
  linarith

/-- **Decay-class (N1) line witnesses from the twist family.**  Let `0 ≤ a < ¼`, `ν` a finite
measure on the arc and `g` a bounded measurable density whose `a`-twisted integer moments vanish,
with nonnegative weighted even moments and positive weighted mass.  Then there is a decay-class
line witness blind at every integer `m ≥ 2`: an even `h` with `h(1/x) = |x| h(x)`, `∫ h = 0`, log
profile `O(e^{−3|v|/2})`, vanishing sine moments of `h′` at `2π(n+2)` and strictly positive definite
log profile. -/
theorem exists_decayClass_fullLineWitness_of_familyMomentPositive {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1 / 4) {ν : Measure ArcParam} [IsFiniteMeasure ν] {g : ArcParam → ℝ}
    (hg : Measurable g) {B : ℝ} (hgB : ∀ u, |g u| ≤ B)
    (hblind : ∀ n : ℕ, ∫ u, g u * (twArcMoment n u - a * swArcMoment n u) ∂ν = 0)
    (hmom : ∀ j : ℕ, 0 ≤ ∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν)
    (hmass : 0 < ∫ u, g u * Real.sqrt (modularArcHeight u / 2) ∂ν) :
    ∃ h h' : ℝ → ℝ, (∀ x, HasDerivAt h (h' x) x) ∧ Integrable h ∧ Integrable h' ∧
      (∀ x, h (-x) = h x) ∧ (∀ x, x ≠ 0 → h (1 / x) = |x| * h x) ∧ ∫ x, h x = 0 ∧
      (∃ C, ∀ v, |Real.exp (v / 2) * h (Real.exp v)| ≤ C * Real.exp (-(3 * |v| / 2))) ∧
      (∀ n : ℕ, ∫ x, h' x * Real.sin (arcFreq (n + 1) * x) = 0) ∧
      ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * h (Real.exp v)) := by
  obtain ⟨μA, μS, hnegP, hinvP, hderP, hintP, hintdP, hblP, hpdP, ⟨Cp, hdecP⟩, hmassP⟩ :=
    exists_twoArcWitness_mass
  set H := twoArcLine (μA : Measure ArcParam) μS with hH
  set H' := twoArcDeriv (μA : Measure ArcParam) μS with hH'
  -- the mass of `h₊`
  have heven : ∀ x, H |x| = H x := fun x => by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, hnegP]
  have hP : ∫ x, H x = 2 * ∫ x in Ioi 0, H x := by
    rw [← integral_comp_abs (f := H)]
    exact integral_congr_ae (Eventually.of_forall fun x => (heven x).symm)
  set P := ∫ x, H x with hPdef
  have hP0 : 0 < P := by rw [hP]; linarith
  set Q := 4 * a * ∫ u, g u * Real.sqrt (modularArcHeight u) ∂ν with hQdef
  have hQ0 : 0 ≤ Q := by
    have hm : 0 ≤ ∫ u, g u * Real.sqrt (modularArcHeight u) ∂ν := by
      have e : (fun u : ArcParam => g u * Real.sqrt (modularArcHeight u)) =
          fun u => Real.sqrt 2 * (g u * Real.sqrt (modularArcHeight u / 2)) := by
        funext u
        rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
      rw [e, integral_const_mul]
      positivity
    positivity
  -- the combination
  set F := famWitness a ν g with hF
  set F' := famWitnessDeriv a ν g with hF'
  have hFint := integrable_famWitness (a := a) (ν := ν) hg hgB
  have hFdint := integrable_famWitnessDeriv (a := a) (ν := ν) hg hgB
  refine ⟨fun x => P * F x + Q * H x, fun x => P * F' x + Q * H' x, fun x => ?_,
    (hFint.const_mul P).add (hintP.const_mul Q), (hFdint.const_mul P).add (hintdP.const_mul Q),
    fun x => ?_, fun x hx => ?_, ?_, ?_, fun n => ?_, fun τ => ?_⟩
  · exact ((hasDerivAt_famWitness hg hgB x).const_mul P).add ((hderP x).const_mul Q)
  · simp only [hF, famWitness_neg, hnegP]
  · simp only [hF]; rw [famWitness_inv hx, hinvP x hx]; ring
  · rw [integral_add (hFint.const_mul P) (hintP.const_mul Q), integral_const_mul,
      integral_const_mul, integral_famWitness hg hgB, ← hPdef, hQdef]
    ring
  · obtain ⟨C, hC⟩ : ∃ C, ∀ v, |Real.exp (v / 2) * F (Real.exp v)| ≤
        C * Real.exp (-(3 * |v| / 2)) :=
      ⟨_, abs_exp_half_mul_le_of_inv (abs_famWitness_le hgB) (fun _ hx => famWitness_inv hx)⟩
    refine ⟨P * C + Q * (Cp * 2 ^ (3 / 2 : ℝ)), fun v => ?_⟩
    have h1 := hC v
    have h2 := hdecP v
    have h3 := cosh_rpow_neg_five_halves_le v
    have hCp : 0 ≤ Cp := (abs_nonneg _).trans ((hdecP 0).trans (by simp))
    have e : Real.exp (v / 2) * (P * F (Real.exp v) + Q * H (Real.exp v)) =
        P * (Real.exp (v / 2) * F (Real.exp v)) + Q * (Real.exp (v / 2) * H (Real.exp v)) := by
      ring
    rw [e]
    calc |P * (Real.exp (v / 2) * F (Real.exp v)) + Q * (Real.exp (v / 2) * H (Real.exp v))|
        ≤ P * |Real.exp (v / 2) * F (Real.exp v)| + Q * |Real.exp (v / 2) * H (Real.exp v)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul P, abs_mul Q, abs_of_pos hP0, abs_of_nonneg hQ0]
      _ ≤ P * (C * Real.exp (-(3 * |v| / 2))) +
          Q * (Cp * (2 ^ (3 / 2 : ℝ) * Real.exp (-(3 * |v| / 2)))) := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_left h3 hCp)
      _ = _ := by ring
  · have hs : ∀ x, |Real.sin (arcFreq (n + 1) * x)| ≤ 1 := fun x => Real.abs_sin_le_one _
    have hsc : Continuous fun x => Real.sin (arcFreq (n + 1) * x) := by fun_prop
    have i1 : Integrable fun x => F' x * Real.sin (arcFreq (n + 1) * x) :=
      hFdint.norm.mono' (hFdint.aestronglyMeasurable.mul hsc.aestronglyMeasurable)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
          exact mul_le_of_le_one_right (abs_nonneg _) (hs x))
    have i2 : Integrable fun x => H' x * Real.sin (arcFreq (n + 1) * x) :=
      hintdP.norm.mono' (hintdP.aestronglyMeasurable.mul hsc.aestronglyMeasurable)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
          exact mul_le_of_le_one_right (abs_nonneg _) (hs x))
    have e : (fun x => (P * F' x + Q * H' x) * Real.sin (arcFreq (n + 1) * x)) = fun x =>
        P * (F' x * Real.sin (arcFreq (n + 1) * x)) +
          Q * (H' x * Real.sin (arcFreq (n + 1) * x)) := by funext x; ring
    rw [e, integral_add (i1.const_mul P) (i2.const_mul Q), integral_const_mul, integral_const_mul,
      hF', integral_famWitnessDeriv_mul_sin hg hgB hblind n, (hblP (n + 1)).1]
    ring
  · have i1 := integrable_cos_mul_profile_of_le (continuous_famWitness (a := a) (ν := ν) hg hgB)
      (abs_famWitness_le hgB) (fun _ hx => famWitness_inv hx) τ
    have i2 : Integrable fun v => Real.cos (τ * v) * (Real.exp (v / 2) * H (Real.exp v)) := by
      by_contra hni
      have := hpdP τ
      rw [integral_undef hni] at this
      exact lt_irrefl _ this
    have e : (fun v => Real.cos (τ * v) * (Real.exp (v / 2) *
        (P * F (Real.exp v) + Q * H (Real.exp v)))) = fun v =>
        P * (Real.cos (τ * v) * (Real.exp (v / 2) * F (Real.exp v))) +
          Q * (Real.cos (τ * v) * (Real.exp (v / 2) * H (Real.exp v))) := by funext v; ring
    simp only
    rw [e, integral_add (i1.const_mul P) (i2.const_mul Q), integral_const_mul, integral_const_mul]
    have hF0 := integral_cos_mul_famWitnessProfile_pos ha hg hgB hmom hmass (a := a) τ
    have hH0 := hpdP τ
    rw [← hF] at hF0
    positivity

end

end RHTower
