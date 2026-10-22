import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeWeightedConvergence
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceSpectrumExact
import GaloisForLFunctions.RHTower.ExpDecayFourierAnalytic
import GaloisForLFunctions.HTGeometry.LocallyUniformZeroCountTransfer
import GaloisForLFunctions.HTGeometry.BoundedDomainDivisorTransfer

/-!
# Entire transforms of finite-prime theta cusp screens

Arbitrary absolute exponential moments make a real-line Fourier--Laplace transform entire.  A
weighted `L¹` approximation at every real exponential rate then gives compact-open convergence of
the transforms.  This module packages that reusable analytic bridge and applies it to the literal
positive even finite-prime cusp screens.

The resulting screen transforms are entire, even, Schwarz-symmetric, and converge locally
uniformly to centered `XiC`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- A complex source has an integrable absolute exponential weight at every real rate. -/
def AllExpWeightIntegrable (g : ℝ → ℂ) : Prop :=
  ∀ A : ℝ, Integrable (fun x : ℝ => ‖g x‖ * Real.exp (A * |x|))

theorem AllExpWeightIntegrable.expWeightIntegrable
    {g : ℝ → ℂ} (hg : AllExpWeightIntegrable g) (ε : ℝ) :
    ExpWeightIntegrable g ε := by
  intro A _
  exact hg A

theorem differentiable_expFourier_of_allExpWeightIntegrable
    {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    (hg : AllExpWeightIntegrable g) :
    Differentiable ℂ (expFourier g) := by
  intro w
  have hw : |w.im| < |w.im| + 1 := by linarith
  exact (hasDerivAt_expFourier' hmeas
    (hg.expWeightIntegrable (|w.im| + 1)) hw).differentiableAt

theorem norm_expFourier_sub_le_weightedL1
    {g h : ℝ → ℂ} (hgmeas : AEStronglyMeasurable g volume)
    (hhmeas : AEStronglyMeasurable h volume)
    (hg : AllExpWeightIntegrable g)
    (hh : AllExpWeightIntegrable h) {w : ℂ} {A : ℝ}
    (hw : |w.im| ≤ A) :
    ‖expFourier g w - expFourier h w‖ ≤
      ∫ x : ℝ, Real.exp (A * |x|) * ‖g x - h x‖ := by
  have hgw : Integrable (fun x : ℝ => g x * Complex.exp (-(I * w * x))) :=
    integrable_expFourier_kernel' hgmeas
      (hg.expWeightIntegrable (|w.im| + 1)) (by linarith)
  have hhw : Integrable (fun x : ℝ => h x * Complex.exp (-(I * w * x))) :=
    integrable_expFourier_kernel' hhmeas
      (hh.expWeightIntegrable (|w.im| + 1)) (by linarith)
  have herr : Integrable (fun x : ℝ =>
      Real.exp (A * |x|) * ‖g x - h x‖) := by
    have hsub : AllExpWeightIntegrable (fun x => g x - h x) := by
      intro B
      refine Integrable.mono' ((hg B).add (hh B))
        ((hgmeas.sub hhmeas).norm.mul (by fun_prop)) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc
        ‖g x - h x‖ * Real.exp (B * |x|)
            ≤ (‖g x‖ + ‖h x‖) * Real.exp (B * |x|) := by gcongr; exact norm_sub_le _ _
        _ = ‖g x‖ * Real.exp (B * |x|) +
              ‖h x‖ * Real.exp (B * |x|) := by ring
    simpa [mul_comm] using hsub A
  rw [expFourier, expFourier, ← integral_sub hgw hhw]
  calc
    ‖∫ x : ℝ,
        g x * Complex.exp (-(I * w * x)) -
          h x * Complex.exp (-(I * w * x))‖
        ≤ ∫ x : ℝ, ‖g x * Complex.exp (-(I * w * x)) -
          h x * Complex.exp (-(I * w * x))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, Real.exp (A * |x|) * ‖g x - h x‖ := by
      refine integral_mono_ae (hgw.sub hhw).norm herr ?_
      filter_upwards with x
      rw [← sub_mul, norm_mul, Complex.norm_exp, re_neg_I_mul_mul_ofReal]
      have him : w.im * x ≤ A * |x| := by
        calc
          w.im * x ≤ |w.im * x| := le_abs_self _
          _ = |w.im| * |x| := abs_mul _ _
          _ ≤ A * |x| := mul_le_mul_of_nonneg_right hw (abs_nonneg x)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr him) (norm_nonneg _)

theorem tendstoLocallyUniformly_expFourier_of_weightedL1
    {gseq : ℕ → ℝ → ℂ} {g : ℝ → ℂ}
    (hgseqmeas : ∀ j, AEStronglyMeasurable (gseq j) volume)
    (hgmeas : AEStronglyMeasurable g volume)
    (hgseq : ∀ j, AllExpWeightIntegrable (gseq j))
    (hg : AllExpWeightIntegrable g)
    (hconv : ∀ A : ℝ, Tendsto (fun j : ℕ =>
      ∫ x : ℝ, Real.exp (A * |x|) * ‖gseq j x - g x‖) atTop (𝓝 0)) :
    TendstoLocallyUniformly (fun j => expFourier (gseq j)) (expFourier g) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε w₀
  let A : ℝ := |w₀.im| + 1
  refine ⟨Metric.ball w₀ 1, Metric.ball_mem_nhds w₀ one_pos, ?_⟩
  have hsmall : ∀ᶠ j : ℕ in atTop,
      (∫ x : ℝ, Real.exp (A * |x|) * ‖gseq j x - g x‖) < ε :=
    (hconv A).eventually (Iio_mem_nhds hε)
  filter_upwards [hsmall] with j hj
  intro w hw
  have hdist : ‖w - w₀‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have himdiff : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
    simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - w₀)
  have him : |w.im| ≤ A := by
    calc
      |w.im| = |w₀.im + (w.im - w₀.im)| := by ring_nf
      _ ≤ |w₀.im| + |w.im - w₀.im| := abs_add_le _ _
      _ ≤ |w₀.im| + 1 := by linarith
      _ = A := rfl
  calc
    dist (expFourier g w) (expFourier (gseq j) w) =
        ‖expFourier (gseq j) w - expFourier g w‖ := by
      rw [dist_eq_norm, norm_sub_rev]
    _ ≤ ∫ x : ℝ, Real.exp (A * |x|) * ‖gseq j x - g x‖ :=
      norm_expFourier_sub_le_weightedL1 (hgseqmeas j) hgmeas (hgseq j) hg him
    _ < ε := hj

theorem expFourier_neg_eq_of_even {g : ℝ → ℂ}
    (heven : ∀ x : ℝ, g (-x) = g x) (w : ℂ) :
    expFourier g (-w) = expFourier g w := by
  let q : ℝ → ℂ := fun x => g x * Complex.exp (-(I * w * x))
  have hreflect := (Measure.measurePreserving_neg volume).integral_comp
    (Homeomorph.neg ℝ).measurableEmbedding q
  rw [expFourier, expFourier]
  calc
    (∫ x : ℝ, g x * Complex.exp (-(I * -w * x))) =
        ∫ x : ℝ, q (-x) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [q]
      rw [heven]
      congr 2
      push_cast
      ring
    _ = ∫ x : ℝ, q x := hreflect

theorem expFourier_neg_conj_eq_conj_of_real {g : ℝ → ℂ}
    (hreal : ∀ x : ℝ, (starRingEnd ℂ) (g x) = g x) (w : ℂ) :
    expFourier g (-(starRingEnd ℂ) w) =
      (starRingEnd ℂ) (expFourier g w) := by
  unfold expFourier
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul, hreal]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp

def finitePrimeThetaCuspScreenTransform (j : ℕ) : ℂ → ℂ :=
  expFourier (fun x : ℝ => (finitePrimeThetaCuspEvenScreen j x : ℂ))

theorem allExpWeightIntegrable_finitePrimeThetaCuspEvenScreen (j : ℕ) :
    AllExpWeightIntegrable
      (fun x : ℝ => (finitePrimeThetaCuspEvenScreen j x : ℂ)) := by
  intro A
  have h := integrable_exp_abs_mul_abs_finitePrimeThetaCuspEvenScreen j A
  simpa only [Complex.norm_real, Real.norm_eq_abs, mul_comm] using h

theorem allExpWeightIntegrable_thetaCuspFullSource :
    AllExpWeightIntegrable (fun x : ℝ => (thetaCuspFullSource x : ℂ)) := by
  intro A
  have h := HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource A
  have hpos : ∀ x : ℝ, 0 ≤ thetaCuspFullSource x :=
    fun x => (HedenmalmThetaSource.thetaCuspFullSource_pos x).le
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos _), mul_comm] using h

theorem differentiable_finitePrimeThetaCuspScreenTransform (j : ℕ) :
    Differentiable ℂ (finitePrimeThetaCuspScreenTransform j) := by
  apply differentiable_expFourier_of_allExpWeightIntegrable
  · exact (Complex.continuous_ofReal.comp
      (continuous_finitePrimeThetaCuspEvenScreen j)).aestronglyMeasurable
  · exact allExpWeightIntegrable_finitePrimeThetaCuspEvenScreen j

theorem finitePrimeThetaCuspScreenTransform_neg (j : ℕ) (w : ℂ) :
    finitePrimeThetaCuspScreenTransform j (-w) =
      finitePrimeThetaCuspScreenTransform j w := by
  exact expFourier_neg_eq_of_even (fun x => by
    simp only [finitePrimeThetaCuspEvenScreen_neg]) w

theorem finitePrimeThetaCuspScreenTransform_conj (j : ℕ) (w : ℂ) :
    finitePrimeThetaCuspScreenTransform j ((starRingEnd ℂ) w) =
      (starRingEnd ℂ) (finitePrimeThetaCuspScreenTransform j w) := by
  rw [← finitePrimeThetaCuspScreenTransform_neg j ((starRingEnd ℂ) w)]
  exact expFourier_neg_conj_eq_conj_of_real
    (fun x => by simp) w

theorem tendstoLocallyUniformly_finitePrimeThetaCuspScreenTransform_XiC :
    TendstoLocallyUniformly finitePrimeThetaCuspScreenTransform XiC atTop := by
  have hconv : TendstoLocallyUniformly finitePrimeThetaCuspScreenTransform
      (expFourier (fun x : ℝ => (thetaCuspFullSource x : ℂ))) atTop := by
    apply tendstoLocallyUniformly_expFourier_of_weightedL1
    · intro j
      exact (Complex.continuous_ofReal.comp
        (continuous_finitePrimeThetaCuspEvenScreen j)).aestronglyMeasurable
    · exact (Complex.continuous_ofReal.comp
        contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable
    · exact allExpWeightIntegrable_finitePrimeThetaCuspEvenScreen
    · exact allExpWeightIntegrable_thetaCuspFullSource
    · intro A
      have heq : (fun j : ℕ => ∫ x : ℝ,
          Real.exp (A * |x|) *
            ‖(finitePrimeThetaCuspEvenScreen j x : ℂ) -
              (thetaCuspFullSource x : ℂ)‖) =
          (fun j : ℕ => ∫ x : ℝ,
            finitePrimeThetaCuspWeightedScreenError A j x) := by
        funext j
        apply integral_congr_ae
        filter_upwards with x
        rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rfl
      rw [heq]
      exact tendsto_integral_finitePrimeThetaCuspWeightedScreenError A
  have hident : expFourier (fun x : ℝ => (thetaCuspFullSource x : ℂ)) = XiC := by
    funext w
    rw [← HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all]
    unfold expFourier thetaCuspFourierLaplace thetaCuspFourierLaplaceIntegrand
    apply integral_congr_ae
    filter_upwards with x
    ring
  rwa [hident] at hconv

/-- On every zero-free circle, selected finite-prime screen transforms eventually carry exactly
the centered-Xi divisor multiplicity enclosed by that circle. -/
theorem eventually_finitePrimeThetaCuspScreenTransform_zeroSumBall_eq_XiC
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hne : ∀ z ∈ Metric.sphere c r, XiC z ≠ 0) :
    ∀ᶠ j : ℕ in atTop,
      GaloisForLFunctions.HTGeometry.zeroSumBall
          (finitePrimeThetaCuspScreenTransform j) c r =
        GaloisForLFunctions.HTGeometry.zeroSumBall XiC c r := by
  exact GaloisForLFunctions.HTGeometry.eventually_zeroSumBall_eq_of_tendstoLocallyUniformly
      differentiable_finitePrimeThetaCuspScreenTransform XiC_differentiable
      tendstoLocallyUniformly_finitePrimeThetaCuspScreenTransform_XiC hr hrR hne

/-- Full Rouché transfer on an arbitrary bounded domain: if centered Xi has no zero on the
frontier, the selected finite-prime screen transform eventually has the same complete divisor
inside, including analytic multiplicity. -/
theorem eventually_exists_finitePrimeThetaCuspScreenTransform_zeroSet_boundedOpen
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hfrontier : ∀ z ∈ frontier Ω, XiC z ≠ 0) :
    ∃ A : Finset ℂ,
      (∀ z ∈ Ω, XiC z = 0 ↔ z ∈ A) ∧
      ∀ᶠ j : ℕ in atTop, ∃ Z : Finset ℂ,
        (∀ z ∈ Ω, finitePrimeThetaCuspScreenTransform j z = 0 ↔ z ∈ Z) ∧
        (∑ z ∈ Z,
            GaloisForLFunctions.HTGeometry.zeroMult
              (finitePrimeThetaCuspScreenTransform j) z) =
          ∑ a ∈ A, GaloisForLFunctions.HTGeometry.zeroMult XiC a := by
  have hXiWitness : XiC (2 * I) ≠ 0 := by
    intro hzero
    have hstrip := abs_im_lt_one_of_XiC_eq_zero hzero
    norm_num at hstrip
  exact GaloisForLFunctions.HTGeometry.eventually_exists_zeroSet_boundedOpen_of_tendstoLocallyUniformly
      differentiable_finitePrimeThetaCuspScreenTransform XiC_differentiable
      tendstoLocallyUniformly_finitePrimeThetaCuspScreenTransform_XiC
      hXiWitness hΩopen hΩbounded hfrontier

end RHTower
