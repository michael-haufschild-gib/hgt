import GaloisForLFunctions.HilbertMetric.ThreePointCorrelationLocal
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCenterMixedThreePoint
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltedSchwartz

/-!
# Cofinal chambers in Hedenmalm's three-point wall

For the actual center-mixed theta density, this module proves a source-derived part of the open
near-center three-point chamber.  When the second adjacent gap is sufficiently large, every
sufficiently small positive first gap gives a positive-definite three-point matrix while still
lying strictly outside the previously proved far chamber.

The proof uses only global theta-source derivative bounds, strict source log-concavity,
differentiation under the integral, and the exact local determinant theorem.  There is no zero
computation and no RH assumption.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- One weighted derivative product in the center-mixed radial integral. -/
def thetaCuspCenterMixedDerivativeProduct
    (m n : ℕ) (a r t : ℝ) : ℝ :=
  r * Real.sinh (a * r) *
    (iteratedDeriv m thetaCuspFullSource (r / 2 + t) *
      iteratedDeriv n thetaCuspFullSource (r / 2 - t))

/-- Integral of one weighted derivative product. -/
def thetaCuspCenterMixedDerivativeProductIntegral
    (m n : ℕ) (a t : ℝ) : ℝ :=
  ∫ r : ℝ in Ioi 0, thetaCuspCenterMixedDerivativeProduct m n a r t

/-- At the reflection center, exchanging the two derivative orders leaves the weighted product
integral unchanged. -/
theorem thetaCuspCenterMixedDerivativeProductIntegral_zero_comm
    (m n : ℕ) (a : ℝ) :
    thetaCuspCenterMixedDerivativeProductIntegral m n a 0 =
      thetaCuspCenterMixedDerivativeProductIntegral n m a 0 := by
  unfold thetaCuspCenterMixedDerivativeProductIntegral
  apply integral_congr_ae
  filter_upwards with r
  unfold thetaCuspCenterMixedDerivativeProduct
  simp only [add_zero, sub_zero]
  ring

/-- First center derivative of the center-mixed density. -/
def thetaCuspCenterMixedDensityFirstJet (a t : ℝ) : ℝ :=
  thetaCuspCenterMixedDerivativeProductIntegral 1 0 a t -
    thetaCuspCenterMixedDerivativeProductIntegral 0 1 a t

/-- Second center derivative of the center-mixed density. -/
def thetaCuspCenterMixedDensitySecondJet (a t : ℝ) : ℝ :=
  thetaCuspCenterMixedDerivativeProductIntegral 2 0 a t -
    2 * thetaCuspCenterMixedDerivativeProductIntegral 1 1 a t +
      thetaCuspCenterMixedDerivativeProductIntegral 0 2 a t

private theorem hasDerivAt_iteratedDeriv_thetaCuspFullSource
    (m : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv m thetaCuspFullSource)
      (iteratedDeriv (m + 1) thetaCuspFullSource x) x := by
  have h := hasDerivAt_thetaCuspFullDerivative m x
  rw [← iteratedDeriv_thetaCuspFullSource m,
    ← iteratedDeriv_thetaCuspFullSource (m + 1)] at h
  exact h

theorem hasDerivAt_thetaCuspCenterMixedDerivativeProduct
    (m n : ℕ) (a r t : ℝ) :
    HasDerivAt (thetaCuspCenterMixedDerivativeProduct m n a r)
      (thetaCuspCenterMixedDerivativeProduct (m + 1) n a r t -
        thetaCuspCenterMixedDerivativeProduct m (n + 1) a r t) t := by
  let w := r * Real.sinh (a * r)
  have hplus := (hasDerivAt_iteratedDeriv_thetaCuspFullSource m (r / 2 + t)).comp t
    ((hasDerivAt_const t (r / 2)).add (hasDerivAt_id t))
  have hminus := (hasDerivAt_iteratedDeriv_thetaCuspFullSource n (r / 2 - t)).comp t
    ((hasDerivAt_const t (r / 2)).sub (hasDerivAt_id t))
  have h := (hplus.mul hminus).const_mul w
  unfold thetaCuspCenterMixedDerivativeProduct
  refine h.congr_deriv ?_
  dsimp [w]
  ring

/-- Uniform radial-and-center majorant for every derivative product. -/
theorem abs_thetaCuspCenterMixedDerivativeProduct_le
    {a r t : ℝ} (m n : ℕ) (hr : 0 < r) (ha0 : 0 ≤ a) :
    |thetaCuspCenterMixedDerivativeProduct m n a r t| ≤
      (thetaCuspDerivativeExpConstant m * thetaCuspDerivativeExpConstant n) * r *
        Real.exp (-(1 / 2 - a) * r) * Real.exp (-|t|) := by
  let Cm := thetaCuspDerivativeExpConstant m
  let Cn := thetaCuspDerivativeExpConstant n
  have hCm : 0 ≤ Cm := thetaCuspDerivativeExpConstant_nonneg m
  have hCn : 0 ≤ Cn := thetaCuspDerivativeExpConstant_nonneg n
  have hsinh0 : 0 ≤ Real.sinh (a * r) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg ha0 hr.le)
  have hsinh : Real.sinh (a * r) ≤ Real.exp (a * r) := by
    rw [Real.sinh_eq]
    nlinarith [Real.exp_pos (a * r), Real.exp_pos (-(a * r))]
  have hk1 := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs m (r / 2 + t)
  have hk2 := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs n (r / 2 - t)
  have hmix := abs_add_half_add_abs_half_sub_ge_mix r t hr.le
  have hexp :
      Real.exp (-|r / 2 + t|) * Real.exp (-|r / 2 - t|) ≤
        Real.exp (-r / 2) * Real.exp (-|t|) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [thetaCuspCenterMixedDerivativeProduct, abs_mul, abs_mul, abs_mul,
    abs_of_pos hr, abs_of_nonneg hsinh0]
  calc
    r * Real.sinh (a * r) *
        (|iteratedDeriv m thetaCuspFullSource (r / 2 + t)| *
          |iteratedDeriv n thetaCuspFullSource (r / 2 - t)|) ≤
      r * Real.exp (a * r) *
        ((Cm * Real.exp (-|r / 2 + t|)) *
          (Cn * Real.exp (-|r / 2 - t|))) := by gcongr
    _ = (Cm * Cn) * r * Real.exp (a * r) *
        (Real.exp (-|r / 2 + t|) * Real.exp (-|r / 2 - t|)) := by ring
    _ ≤ (Cm * Cn) * r * Real.exp (a * r) *
        (Real.exp (-r / 2) * Real.exp (-|t|)) := by gcongr
    _ = (thetaCuspDerivativeExpConstant m * thetaCuspDerivativeExpConstant n) * r *
        Real.exp (-(1 / 2 - a) * r) * Real.exp (-|t|) := by
      have he : Real.exp (a * r) * Real.exp (-r / 2) =
          Real.exp (-(1 / 2 - a) * r) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        (Cm * Cn) * r * Real.exp (a * r) *
            (Real.exp (-r / 2) * Real.exp (-|t|)) =
          (Cm * Cn) * r *
            (Real.exp (a * r) * Real.exp (-r / 2)) * Real.exp (-|t|) := by ring
        _ = (Cm * Cn) * r * Real.exp (-(1 / 2 - a) * r) *
            Real.exp (-|t|) := by rw [he]
        _ = _ := by rfl

theorem integrable_thetaCuspCenterMixedDerivativeProduct
    {a t : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (m n : ℕ) :
    IntegrableOn (thetaCuspCenterMixedDerivativeProduct m n a · t) (Ioi 0) := by
  let c : ℝ := 1 / 2 - a
  let C : ℝ := thetaCuspDerivativeExpConstant m * thetaCuspDerivativeExpConstant n *
    Real.exp (-|t|)
  have hc : 0 < c := by dsimp [c]; linarith
  have hdom : IntegrableOn (fun r : ℝ => C * (r ^ (1 : ℝ) * Real.exp (-c * r ^ (1 : ℝ))))
      (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := c) (by norm_num) (by norm_num) hc).const_mul C
  apply Integrable.mono hdom
  · have hk (j : ℕ) : Continuous (iteratedDeriv j thetaCuspFullSource) := by
      rw [iteratedDeriv_thetaCuspFullSource]
      exact continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspFullDerivative j x).continuousAt
    have hcont : Continuous (thetaCuspCenterMixedDerivativeProduct m n a · t) := by
      unfold thetaCuspCenterMixedDerivativeProduct
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs]
    calc
      |thetaCuspCenterMixedDerivativeProduct m n a r t| ≤
          (thetaCuspDerivativeExpConstant m * thetaCuspDerivativeExpConstant n) * r *
            Real.exp (-c * r) * Real.exp (-|t|) := by
        simpa only [c] using
          abs_thetaCuspCenterMixedDerivativeProduct_le m n hr ha0
      _ = ‖C * (r ^ (1 : ℝ) * Real.exp (-c * r ^ (1 : ℝ)))‖ := by
        have hC : 0 ≤ C := by
          dsimp [C]
          exact mul_nonneg
            (mul_nonneg
              (thetaCuspDerivativeExpConstant_nonneg m)
              (thetaCuspDerivativeExpConstant_nonneg n))
            (Real.exp_pos _).le
        have hnonneg : 0 ≤ C * (r ^ (1 : ℝ) * Real.exp (-c * r ^ (1 : ℝ))) := by
          exact mul_nonneg hC
            (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le)
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.rpow_one]
        dsimp [C]
        ring

theorem hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (m n : ℕ) (t : ℝ) :
    HasDerivAt (thetaCuspCenterMixedDerivativeProductIntegral m n a)
      (thetaCuspCenterMixedDerivativeProductIntegral (m + 1) n a t -
        thetaCuspCenterMixedDerivativeProductIntegral m (n + 1) a t) t := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let c : ℝ := 1 / 2 - a
  let C : ℝ :=
    thetaCuspDerivativeExpConstant (m + 1) * thetaCuspDerivativeExpConstant n +
      thetaCuspDerivativeExpConstant m * thetaCuspDerivativeExpConstant (n + 1)
  let bound : ℝ → ℝ := fun r => C * (r ^ (1 : ℝ) * Real.exp (-c * r ^ (1 : ℝ)))
  have hc : 0 < c := by dsimp [c]; linarith
  have hbound : Integrable bound mu := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := c) (by norm_num) (by norm_num) hc
    exact h.const_mul C
  let F : ℝ → ℝ → ℝ := fun z r => thetaCuspCenterMixedDerivativeProduct m n a r z
  let F' : ℝ → ℝ → ℝ := fun z r =>
    thetaCuspCenterMixedDerivativeProduct (m + 1) n a r z -
      thetaCuspCenterMixedDerivativeProduct m (n + 1) a r z
  have hFint : Integrable (F t) mu :=
    integrable_thetaCuspCenterMixedDerivativeProduct ha0 ha m n
  have hFmeas : ∀ z, AEStronglyMeasurable (F z) mu := fun z =>
    (integrable_thetaCuspCenterMixedDerivativeProduct ha0 ha m n).1
  have hF'meas : AEStronglyMeasurable (F' t) mu :=
    ((integrable_thetaCuspCenterMixedDerivativeProduct ha0 ha (m + 1) n).sub
      (integrable_thetaCuspCenterMixedDerivativeProduct ha0 ha m (n + 1))).1
  have hdom : ∀ᵐ r ∂mu, ∀ z ∈ Set.univ, ‖F' z r‖ ≤ bound r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr z hz
    have h1 := abs_thetaCuspCenterMixedDerivativeProduct_le
      (t := z) (m + 1) n hr ha0
    have h2 := abs_thetaCuspCenterMixedDerivativeProduct_le
      (t := z) m (n + 1) hr ha0
    rw [Real.norm_eq_abs]
    calc
      |F' z r| ≤
          |thetaCuspCenterMixedDerivativeProduct (m + 1) n a r z| +
            |thetaCuspCenterMixedDerivativeProduct m (n + 1) a r z| := abs_sub _ _
      _ ≤ C * r * Real.exp (-c * r) * Real.exp (-|z|) := by
        dsimp [F', C, c]
        nlinarith [h1, h2,
          thetaCuspDerivativeExpConstant_nonneg (m + 1),
          thetaCuspDerivativeExpConstant_nonneg n,
          thetaCuspDerivativeExpConstant_nonneg m,
          thetaCuspDerivativeExpConstant_nonneg (n + 1),
          Real.exp_pos (-|z|), Real.exp_pos (-(1 / 2 - a) * r)]
      _ ≤ C * r * Real.exp (-c * r) := by
        have hC : 0 ≤ C := by
          dsimp [C]
          exact add_nonneg
            (mul_nonneg
              (thetaCuspDerivativeExpConstant_nonneg (m + 1))
              (thetaCuspDerivativeExpConstant_nonneg n))
            (mul_nonneg
              (thetaCuspDerivativeExpConstant_nonneg m)
              (thetaCuspDerivativeExpConstant_nonneg (n + 1)))
        exact mul_le_of_le_one_right
          (mul_nonneg (mul_nonneg hC hr.le) (Real.exp_pos _).le)
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg z)))
      _ = bound r := by simp [bound, Real.rpow_one, mul_assoc]
  have hdiff : ∀ᵐ r ∂mu, ∀ z ∈ Set.univ,
      HasDerivAt (fun eta => F eta r) (F' z r) z := by
    filter_upwards with r z hz
    exact hasDerivAt_thetaCuspCenterMixedDerivativeProduct m n a r z
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := mu) (F := F) (F' := F') (x₀ := t) (s := Set.univ) (bound := bound)
    univ_mem (Filter.Eventually.of_forall hFmeas) hFint hF'meas hdom hbound hdiff
  have hsub :
      (∫ r : ℝ, F' t r ∂mu) =
        thetaCuspCenterMixedDerivativeProductIntegral (m + 1) n a t -
          thetaCuspCenterMixedDerivativeProductIntegral m (n + 1) a t := by
    rw [integral_sub
      (integrable_thetaCuspCenterMixedDerivativeProduct ha0 ha (m + 1) n)
      (integrable_thetaCuspCenterMixedDerivativeProduct ha0 ha m (n + 1))]
    rfl
  have h2 : HasDerivAt
      (fun s : ℝ => ∫ r : ℝ in Ioi 0, thetaCuspCenterMixedDerivativeProduct m n a r s)
      (∫ r : ℝ, F' t r ∂mu) t := hresult.2
  rw [hsub] at h2
  exact h2

theorem thetaCuspCenterMixedDensity_eq_derivativeProductIntegral (a t : ℝ) :
    thetaCuspCenterMixedDensity a t =
      thetaCuspCenterMixedDerivativeProductIntegral 0 0 a t := by
  rfl

theorem hasDerivAt_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    HasDerivAt (thetaCuspCenterMixedDensity a)
      (thetaCuspCenterMixedDensityFirstJet a t) t := by
  exact hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 0 0 t

theorem hasDerivAt_thetaCuspCenterMixedDensityFirstJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    HasDerivAt (thetaCuspCenterMixedDensityFirstJet a)
      (thetaCuspCenterMixedDensitySecondJet a t) t := by
  have h10 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 1 0 t
  have h01 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 0 1 t
  unfold thetaCuspCenterMixedDensityFirstJet thetaCuspCenterMixedDensitySecondJet
  exact (h10.sub h01).congr_deriv (by ring)

theorem continuous_thetaCuspCenterMixedDensitySecondJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Continuous (thetaCuspCenterMixedDensitySecondJet a) := by
  have hcont (m n : ℕ) :
      Continuous (thetaCuspCenterMixedDerivativeProductIntegral m n a) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha m n t).continuousAt
  unfold thetaCuspCenterMixedDensitySecondJet
  fun_prop

/-- Every derivative-product integral tends to zero at the positive center tail. -/
theorem thetaCuspCenterMixedDerivativeProductIntegral_tendsto_zero
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (m n : ℕ) :
    Tendsto (thetaCuspCenterMixedDerivativeProductIntegral m n a) atTop (𝓝 0) := by
  let c : ℝ := 1 / 2 - a
  let C : ℝ := thetaCuspDerivativeExpConstant m * thetaCuspDerivativeExpConstant n
  let K : ℝ := ∫ r : ℝ in Ioi 0, C * r * Real.exp (-c * r)
  have hc : 0 < c := by dsimp [c]; linarith
  have hrad : IntegrableOn (fun r : ℝ => C * r * Real.exp (-c * r)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := c) (by norm_num) (by norm_num) hc
    simpa [MeasureTheory.IntegrableOn, Real.rpow_one, mul_assoc] using h.const_mul C
  have hK : 0 ≤ K := by
    dsimp [K]
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (thetaCuspDerivativeExpConstant_nonneg m)
          (thetaCuspDerivativeExpConstant_nonneg n))
        hr.le)
      (Real.exp_pos _).le
  have hle : ∀ t : ℝ,
      ‖thetaCuspCenterMixedDerivativeProductIntegral m n a t‖ ≤
        K * Real.exp (-|t|) := by
    intro t
    rw [thetaCuspCenterMixedDerivativeProductIntegral]
    calc
      ‖∫ r : ℝ in Ioi 0, thetaCuspCenterMixedDerivativeProduct m n a r t‖ ≤
          ∫ r : ℝ in Ioi 0, ‖thetaCuspCenterMixedDerivativeProduct m n a r t‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ r : ℝ in Ioi 0,
          (C * r * Real.exp (-c * r)) * Real.exp (-|t|) := by
        apply setIntegral_mono_ae_restrict
        · exact (integrable_thetaCuspCenterMixedDerivativeProduct ha0 ha m n).norm
        · exact hrad.mul_const _
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          rw [Real.norm_eq_abs]
          simpa only [C, c, mul_assoc] using
            abs_thetaCuspCenterMixedDerivativeProduct_le m n hr ha0
      _ = K * Real.exp (-|t|) := by
        rw [← integral_mul_const]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) (Eventually.of_forall hle)
  have habs : Tendsto (fun t : ℝ => |t|) atTop atTop :=
    tendsto_abs_atTop_atTop
  simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp habs).const_mul K

theorem thetaCuspCenterMixedDensity_tendsto_zero
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Tendsto (thetaCuspCenterMixedDensity a) atTop (𝓝 0) := by
  exact thetaCuspCenterMixedDerivativeProductIntegral_tendsto_zero ha0 ha 0 0

theorem thetaCuspCenterMixedDensityFirstJet_tendsto_zero
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Tendsto (thetaCuspCenterMixedDensityFirstJet a) atTop (𝓝 0) := by
  unfold thetaCuspCenterMixedDensityFirstJet
  simpa using
    (thetaCuspCenterMixedDerivativeProductIntegral_tendsto_zero ha0 ha 1 0).sub
      (thetaCuspCenterMixedDerivativeProductIntegral_tendsto_zero ha0 ha 0 1)

theorem thetaCuspCenterMixedDensitySecondJet_tendsto_zero
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Tendsto (thetaCuspCenterMixedDensitySecondJet a) atTop (nhds 0) := by
  unfold thetaCuspCenterMixedDensitySecondJet
  have h20 := thetaCuspCenterMixedDerivativeProductIntegral_tendsto_zero ha0 ha 2 0
  have h11 := thetaCuspCenterMixedDerivativeProductIntegral_tendsto_zero ha0 ha 1 1
  have h02 := thetaCuspCenterMixedDerivativeProductIntegral_tendsto_zero ha0 ha 0 2
  convert (h20.sub (h11.const_mul 2)).add h02 using 1
  all_goals norm_num

theorem thetaCuspCenterMixedDensityFirstJet_zero
    (a : ℝ) :
    thetaCuspCenterMixedDensityFirstJet a 0 = 0 := by
  rw [thetaCuspCenterMixedDensityFirstJet,
    thetaCuspCenterMixedDerivativeProductIntegral_zero_comm 1 0, sub_self]

theorem thetaCuspCenterMixedDensitySecondJet_zero_neg
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    thetaCuspCenterMixedDensitySecondJet a 0 < 0 := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let g : ℝ → ℝ := fun r =>
    -2 * r * Real.sinh (a * r) * thetaCuspLogConcavityNumerator (r / 2)
  have hgint : Integrable g mu := by
    have h20 := integrable_thetaCuspCenterMixedDerivativeProduct
      (t := 0) ha0.le ha 2 0
    have h11 := integrable_thetaCuspCenterMixedDerivativeProduct
      (t := 0) ha0.le ha 1 1
    have h02 := integrable_thetaCuspCenterMixedDerivativeProduct
      (t := 0) ha0.le ha 0 2
    have hcombo := (h20.sub (h11.const_mul 2)).add h02
    apply hcombo.neg.congr
    filter_upwards with r
    simp [g, thetaCuspCenterMixedDerivativeProduct,
      thetaCuspLogConcavityNumerator]
    ring
  have hgnn : 0 ≤ᵐ[mu] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    dsimp [g]
    have hnum := thetaCuspLogConcavityNumerator_neg_all (r / 2)
    have hsinh : 0 < Real.sinh (a * r) :=
      (Real.sinh_pos_iff.mpr (mul_pos ha0 hr))
    exact mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hr.le) hsinh.le)
      hnum.le
  have hgpos : 0 < ∫ r : ℝ, g r ∂mu := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hgnn hgint).2
    have hgcont : Continuous g := by
      dsimp [g]
      have hnumcont : Continuous (fun r : ℝ =>
          thetaCuspLogConcavityNumerator (r / 2)) :=
        continuous_thetaCuspLogConcavityNumerator.comp (continuous_id.div_const 2)
      exact (((continuous_const.mul continuous_id).mul
        (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul hnumcont)
    have hopen : IsOpen (Function.support g ∩ Ioi (0 : ℝ)) :=
      hgcont.isOpen_support.inter isOpen_Ioi
    apply hopen.measure_pos (volume : Measure ℝ)
    refine ⟨1, ?_, by norm_num⟩
    change g 1 ≠ 0
    dsimp [g]
    have hnum := thetaCuspLogConcavityNumerator_neg_all (1 / 2)
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Real.sinh_ne_zero.mpr (by simpa using ha0.ne'))) hnum.ne
  have heq : -thetaCuspCenterMixedDensitySecondJet a 0 = ∫ r : ℝ, g r ∂mu := by
    unfold thetaCuspCenterMixedDensitySecondJet
      thetaCuspCenterMixedDerivativeProductIntegral
    let P20 : ℝ → ℝ := fun r => thetaCuspCenterMixedDerivativeProduct 2 0 a r 0
    let P11 : ℝ → ℝ := fun r => thetaCuspCenterMixedDerivativeProduct 1 1 a r 0
    let P02 : ℝ → ℝ := fun r => thetaCuspCenterMixedDerivativeProduct 0 2 a r 0
    have h20 : Integrable P20 mu :=
      integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0.le ha 2 0
    have h11 : Integrable P11 mu :=
      integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0.le ha 1 1
    have h02 : Integrable P02 mu :=
      integrable_thetaCuspCenterMixedDerivativeProduct (t := 0) ha0.le ha 0 2
    have hlinear :
        (∫ r, (-P20 r + 2 * P11 r - P02 r) ∂mu) =
          -(∫ r, P20 r ∂mu) + 2 * (∫ r, P11 r ∂mu) -
            ∫ r, P02 r ∂mu := by
      calc
        (∫ r, (-P20 r + 2 * P11 r - P02 r) ∂mu) =
            (∫ r, (-P20 r + 2 * P11 r) ∂mu) - ∫ r, P02 r ∂mu :=
          integral_sub (h20.neg.add (h11.const_mul 2)) h02
        _ = ((∫ r, -P20 r ∂mu) + ∫ r, 2 * P11 r ∂mu) -
            ∫ r, P02 r ∂mu := by
          congr 1
          exact integral_add h20.neg (h11.const_mul 2)
        _ = -(∫ r, P20 r ∂mu) + 2 * (∫ r, P11 r ∂mu) -
            ∫ r, P02 r ∂mu := by
          rw [integral_neg, integral_const_mul]
    calc
      -((∫ r, P20 r ∂mu) - 2 * (∫ r, P11 r ∂mu) + ∫ r, P02 r ∂mu) =
          ∫ r, (-P20 r + 2 * P11 r - P02 r) ∂mu := by
        rw [hlinear]
        ring
      _ = ∫ r, g r ∂mu := by
        apply integral_congr_ae
        filter_upwards with r
        simp [P20, P11, P02, g, thetaCuspCenterMixedDerivativeProduct,
          thetaCuspLogConcavityNumerator]
        ring
  rw [← heq] at hgpos
  linarith

/-- The surviving local determinant second-jet wall is eventually strictly positive. -/
theorem eventually_thetaCuspCenterMixedLocalThreePointWall_pos
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∀ᶠ y : ℝ in atTop,
      0 < (-thetaCuspCenterMixedDensitySecondJet a 0) *
          (thetaCuspCenterMixedDensity a 0 ^ 2 -
            thetaCuspCenterMixedDensity a y ^ 2) -
        thetaCuspCenterMixedDensity a 0 *
          thetaCuspCenterMixedDensityFirstJet a y ^ 2 := by
  let d := thetaCuspCenterMixedDensity a 0
  let h := thetaCuspCenterMixedDensitySecondJet a 0
  have hd : 0 < d := thetaCuspCenterMixedDensity_pos ha0 ha 0
  have hh : h < 0 := thetaCuspCenterMixedDensitySecondJet_zero_neg ha0 ha
  have hlim : Tendsto (fun y : ℝ =>
      (-h) * (d ^ 2 - thetaCuspCenterMixedDensity a y ^ 2) -
        d * thetaCuspCenterMixedDensityFirstJet a y ^ 2) atTop
      (𝓝 ((-h) * d ^ 2)) := by
    have hf2 := (thetaCuspCenterMixedDensity_tendsto_zero ha0.le ha).pow 2
    have hf'2 := (thetaCuspCenterMixedDensityFirstJet_tendsto_zero ha0.le ha).pow 2
    have hd2 : Tendsto (fun _ : ℝ => d ^ 2) atTop (nhds (d ^ 2)) :=
      tendsto_const_nhds
    have hleft := (hd2.sub hf2).const_mul (-h)
    have hright := hf'2.const_mul d
    convert hleft.sub hright using 1
    all_goals norm_num
  have htarget : 0 < (-h) * d ^ 2 := mul_pos (neg_pos.mpr hh) (sq_pos_of_pos hd)
  have hev := hlim.eventually (Ioi_mem_nhds htarget)
  simpa only [d, h] using hev

/-- **Source-level asymmetric near-center chamber.**  For every admissible positive aperture,
all sufficiently large second gaps admit a positive interval of first gaps on which the actual
theta three-point matrix is positive definite and the far-chamber inequality is strictly
reversed. -/
theorem eventually_exists_thetaCuspCenterMixed_nearCenter_posDef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∀ᶠ y : ℝ in atTop, ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, 0 < x → x < ε →
      thetaCuspCenterMixedDensity a 0 ^ 2 <
          thetaCuspCenterMixedDensity a x ^ 2 +
            thetaCuspCenterMixedDensity a y ^ 2 ∧
      Matrix.PosDef (thetaCuspCenterMixedThreePointMatrix a x y) := by
  filter_upwards [eventually_thetaCuspCenterMixedLocalThreePointWall_pos ha0 ha,
    eventually_ge_atTop (0 : ℝ)] with y hwall hy
  let f := thetaCuspCenterMixedDensity a
  let f' := thetaCuspCenterMixedDensityFirstJet a
  let f'' := thetaCuspCenterMixedDensitySecondJet a
  have hlocal := HilbertMetric.exists_threePointCorrelationDeterminantPath_pos_right
    (fun t => hasDerivAt_thetaCuspCenterMixedDensity ha0.le ha t)
    (fun t => hasDerivAt_thetaCuspCenterMixedDensityFirstJet ha0.le ha t)
    (continuous_thetaCuspCenterMixedDensitySecondJet ha0.le ha)
    (thetaCuspCenterMixedDensityFirstJet_zero a) hwall
  rcases hlocal with ⟨ε1, hε1, hdet⟩
  have hnear0 : f 0 ^ 2 < f 0 ^ 2 + f y ^ 2 := by
    have hfy := thetaCuspCenterMixedDensity_pos ha0 ha y
    nlinarith [sq_pos_of_pos hfy]
  have hopen : IsOpen {x : ℝ | f 0 ^ 2 < f x ^ 2 + f y ^ 2} :=
    isOpen_lt continuous_const
      (((continuous_thetaCuspCenterMixedDensity ha0.le ha).pow 2).add continuous_const)
  have hn := hopen.mem_nhds hnear0
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε2, hε2, hball⟩
  let ε := min ε1 ε2
  have hε : 0 < ε := lt_min hε1 hε2
  refine ⟨ε, hε, fun x hx hxε => ?_⟩
  have hxε1 : x < ε1 := lt_of_lt_of_le hxε (min_le_left _ _)
  have hxε2 : x < ε2 := lt_of_lt_of_le hxε (min_le_right _ _)
  have hnear : f 0 ^ 2 < f x ^ 2 + f y ^ 2 := hball (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hx.le]
    exact hxε2)
  have hdetpos : 0 < HilbertMetric.threePointCorrelationDeterminantPath f y x :=
    hdet x hx hxε1
  have hfx0 : 0 ≤ f x := (thetaCuspCenterMixedDensity_pos ha0 ha x).le
  have hfxlt : f x < f 0 := thetaCuspCenterMixedDensity_lt_zero ha0 ha hx
  have hposdef := (HilbertMetric.threePointCorrelationMatrix_posDef_iff
    (thetaCuspCenterMixedDensity_pos ha0 ha 0) hfx0 hfxlt).2 hdetpos
  exact ⟨hnear, by simpa [thetaCuspCenterMixedThreePointMatrix,
    HilbertMetric.threePointCorrelationDeterminantPath, f] using hposdef⟩

/-- **Cofinal closure of the complete order-three wall.**  Once the second adjacent gap is
sufficiently large, every positive first gap gives a positive-semidefinite matrix: the near-center
part follows from uniform determinant convexity and the complement is the far chamber. -/
theorem eventually_forall_thetaCuspCenterMixedThreePointMatrix_posSemidef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∀ᶠ y : ℝ in atTop, ∀ x : ℝ, 0 < x →
      Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y) := by
  let f := thetaCuspCenterMixedDensity a
  let f' := thetaCuspCenterMixedDensityFirstJet a
  let f'' := thetaCuspCenterMixedDensitySecondJet a
  rcases HilbertMetric.exists_uniform_threePointCorrelationDeterminantPath_pos_right_atTop
      (fun t => hasDerivAt_thetaCuspCenterMixedDensity ha0.le ha t)
      (fun t => hasDerivAt_thetaCuspCenterMixedDensityFirstJet ha0.le ha t)
      (continuous_thetaCuspCenterMixedDensitySecondJet ha0.le ha)
      (thetaCuspCenterMixedDensityFirstJet_zero a)
      (thetaCuspCenterMixedDensity_pos ha0 ha 0)
      (thetaCuspCenterMixedDensitySecondJet_zero_neg ha0 ha)
      (thetaCuspCenterMixedDensity_tendsto_zero ha0.le ha)
      (thetaCuspCenterMixedDensityFirstJet_tendsto_zero ha0.le ha)
      (thetaCuspCenterMixedDensitySecondJet_tendsto_zero ha0.le ha) with
    ⟨δ, hδ, hlocal⟩
  have hδlt : f δ < f 0 := by
    simpa [f] using thetaCuspCenterMixedDensity_lt_zero ha0 ha hδ
  have hδ0 : 0 ≤ f δ := by
    exact (thetaCuspCenterMixedDensity_pos ha0 ha δ).le
  have hd0 : 0 ≤ f 0 := by
    exact (thetaCuspCenterMixedDensity_pos ha0 ha 0).le
  have hgap : f δ ^ 2 < f 0 ^ 2 := (sq_lt_sq₀ hδ0 hd0).2 hδlt
  have htail_sq := (thetaCuspCenterMixedDensity_tendsto_zero ha0.le ha).pow 2
  have hsum : Tendsto (fun y : ℝ => f δ ^ 2 + f y ^ 2) atTop (nhds (f δ ^ 2)) := by
    have hconst : Tendsto (fun _ : ℝ => f δ ^ 2) atTop (nhds (f δ ^ 2)) :=
      tendsto_const_nhds
    convert hconst.add htail_sq using 1
    all_goals norm_num
  have hfar_at_delta : ∀ᶠ y : ℝ in atTop, f δ ^ 2 + f y ^ 2 < f 0 ^ 2 :=
    hsum.eventually (Iio_mem_nhds hgap)
  filter_upwards [hlocal, hfar_at_delta, eventually_gt_atTop (0 : ℝ)] with
    y hlocal_y hfar_y hy
  intro x hx
  by_cases hnear : f 0 ^ 2 < f x ^ 2 + f y ^ 2
  · have hxδ : x < δ := by
      by_contra hnot
      have hδx : δ ≤ x := le_of_not_gt hnot
      have hfx_le : f x ≤ f δ := by
        exact antitoneOn_thetaCuspCenterMixedDensity ha0.le ha hδ.le hx.le hδx
      have hfx0 : 0 ≤ f x := (thetaCuspCenterMixedDensity_pos ha0 ha x).le
      have hsquare : f x ^ 2 ≤ f δ ^ 2 := (sq_le_sq₀ hfx0 hδ0).2 hfx_le
      linarith
    have hdet : 0 < thetaCuspCenterMixedThreePointDeterminant a x y := by
      simpa [thetaCuspCenterMixedThreePointDeterminant,
        HilbertMetric.threePointCorrelationDeterminantPath, f] using
          hlocal_y x hx hxδ
    exact (thetaCuspCenterMixedThreePointMatrix_posSemidef_iff ha0 ha hx).2 hdet.le
  · exact thetaCuspCenterMixedThreePointMatrix_posSemidef_of_far_chamber
      ha0 ha hx.le hy.le (le_of_not_gt hnear)

theorem thetaCuspCenterMixedThreePointMatrix_posSemidef_comm
    {a x y : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (hx : 0 < x) (hy : 0 < y) :
    Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y) ↔
      Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a y x) := by
  rw [thetaCuspCenterMixedThreePointMatrix_posSemidef_iff ha0 ha hx,
    thetaCuspCenterMixedThreePointMatrix_posSemidef_iff ha0 ha hy]
  unfold thetaCuspCenterMixedThreePointDeterminant
    HilbertMetric.threePointCorrelationDeterminant
  rw [add_comm x y]
  ring_nf

/-- Symmetric threshold form: every ordered packet with at least one sufficiently large adjacent
gap is positive semidefinite. -/
theorem exists_thetaCuspCenterMixedThreePointMatrix_posSemidef_of_large_gap
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∃ Y : ℝ, ∀ x y : ℝ, 0 < x → 0 < y → Y ≤ x ∨ Y ≤ y →
      Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y) := by
  rcases eventually_atTop.1
      (eventually_forall_thetaCuspCenterMixedThreePointMatrix_posSemidef ha0 ha) with
    ⟨Y, hY⟩
  refine ⟨Y, fun x y hx hy hlarge => ?_⟩
  rcases hlarge with hxlarge | hylarge
  · exact (thetaCuspCenterMixedThreePointMatrix_posSemidef_comm ha0 ha hx hy).2
      (hY x hxlarge y hy)
  · exact hY y hylarge x hx

/-- For each aperture, the complete ordered three-point problem is now exactly a bounded two-gap
core: all packets outside one square are already positive semidefinite. -/
theorem exists_thetaCuspCenterMixedThreePointMatrix_compactCore_iff
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∃ Y : ℝ,
      (∀ x y : ℝ, 0 < x → 0 < y →
          Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y)) ↔
        (∀ x y : ℝ, 0 < x → 0 < y → x < Y → y < Y →
          Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y)) := by
  rcases exists_thetaCuspCenterMixedThreePointMatrix_posSemidef_of_large_gap ha0 ha with
    ⟨Y, hlarge⟩
  refine ⟨Y, ⟨fun hall x y hx hy _ _ => hall x y hx hy, ?_⟩⟩
  intro hcore x y hx hy
  by_cases hxY : x < Y
  · by_cases hyY : y < Y
    · exact hcore x y hx hy hxY hyY
    · exact hlarge x y hx hy (Or.inr (le_of_not_gt hyY))
  · exact hlarge x y hx hy (Or.inl (le_of_not_gt hxY))

end

end RHTower
