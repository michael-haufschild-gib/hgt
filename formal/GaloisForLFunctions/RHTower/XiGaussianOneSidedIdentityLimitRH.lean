import GaloisForLFunctions.RHTower.XiGaussianOneSidedIdentityRH
import GaloisForLFunctions.RHTower.CCMEvenGroundXiStripConvergenceRH

/-!
# Limits of real-rooted weights with asymptotic one-sided Gaussian identities

Let `F_j` be holomorphic and uniformly bounded on the strip `|Im z| < 1/2 + η`, each with only real
zeros there, converging locally uniformly on the strip to a function that is not identically zero.
If for every positive frequency `u` the one-sided Gaussian zero-side identity holds asymptotically,

`∑_q F_j(γ_q) e^{-σγ_q²} e^{-iuγ_q} - κ_j ∫ F_j(t) e^{-σt²} e^{-iut} dt → 0`,  `κ_j → κ`,

then the Riemann hypothesis holds.

This is the limit form needed for eigenvectors of restricted Weil forms at growing apertures: the
transforms `F_j` are the approximants, and the Euler–Lagrange equation tested against Gaussian
modulations, with the cutoff error at the aperture edge, is the asymptotic identity.

**Proof.** Hurwitz's theorem on the strip keeps the zeros of the limit real. Dominated convergence
over the Xi zeros (Gaussian weights against `∑ 1/|γ|² < ∞`) and over the line (the Gaussian `e^{-σt²}`)
passes the identity to the limit, and the exact receiver applies.
-/

open Complex MeasureTheory Set Filter Topology Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The strip `|Im z| < 1/2 + η`. -/
def xiOneSidedStrip (η : ℝ) : Set ℂ := {z : ℂ | |z.im| < 1 / 2 + η}

theorem isOpen_xiOneSidedStrip (η : ℝ) : IsOpen (xiOneSidedStrip η) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem convex_xiOneSidedStrip (η : ℝ) : Convex ℝ (xiOneSidedStrip η) := by
  have hset : xiOneSidedStrip η =
      {z : ℂ | -(1 / 2 + η) < z.im} ∩ {z : ℂ | z.im < 1 / 2 + η} := by
    ext z
    simp [xiOneSidedStrip, abs_lt]
  rw [hset]
  exact (convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)

/-- The Gaussian-weighted value at a centered Xi zero is dominated by an inverse square. -/
theorem norm_gaussModulated_xiSpectralPoint_le {F : ℂ → ℂ} {M σ u : ℝ} (hσ : 0 < σ)
    (hM : 0 ≤ M) (q : XiZeroCopy) (hF : ‖F (xiSpectralPoint q)‖ ≤ M) :
    ‖gaussModulated F σ u (xiSpectralPoint q)‖ ≤
      M * Real.exp (σ / 4) * (1 / σ + 1) * Real.exp (|u| / 2) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  set z := xiSpectralPoint q with hzdef
  have hz : |z.im| < 1 / 2 := by
    have := xiSpectralPoint_im_mem_openHalf q
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]
  have hz0 : z ≠ 0 := xiSpectralPoint_ne_zero q
  have h1 := norm_mul_cexp_neg_mul_sq_le (F := F) (M := M) (A := 0) (σ := σ) le_rfl hσ
    (by rw [zero_mul, Real.exp_zero, mul_one]; exact hF) hz.le
  rw [sub_zero] at h1
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hpos : 0 < ‖z‖ ^ 2 := by positivity
  have hy2 : z.im ^ 2 ≤ 1 / 4 := by
    have := sq_abs z.im
    nlinarith [abs_nonneg z.im]
  have h2 := exp_neg_mul_sq_mul_add_quarter_le hσ z.re
  have h3 : Real.exp (-(σ * z.re ^ 2)) ≤ (1 / σ + 1) * (1 / ‖z‖ ^ 2) := by
    rw [← div_eq_mul_one_div, le_div_iff₀ hpos]
    calc Real.exp (-(σ * z.re ^ 2)) * ‖z‖ ^ 2
        ≤ Real.exp (-(σ * z.re ^ 2)) * (z.re ^ 2 + 1 / 4) := by
          gcongr; rw [hnorm]; linarith
      _ ≤ 1 / σ + 1 := h2
  have h4 : ‖cexp (-(I * z) * u)‖ ≤ Real.exp (|u| / 2) := by
    rw [norm_cexp_neg_I_mul_ofReal]
    apply Real.exp_le_exp.mpr
    calc u * z.im ≤ |u * z.im| := le_abs_self _
      _ = |u| * |z.im| := abs_mul _ _
      _ ≤ |u| * (1 / 2) := by gcongr
      _ = |u| / 2 := by ring
  rw [gaussModulated, norm_mul]
  calc ‖F z * cexp (-(σ : ℂ) * z ^ 2)‖ * ‖cexp (-(I * z) * u)‖
      ≤ (M * Real.exp (σ / 4) * Real.exp (-(σ * z.re ^ 2))) * Real.exp (|u| / 2) := by
        gcongr
    _ ≤ (M * Real.exp (σ / 4) * ((1 / σ + 1) * (1 / ‖z‖ ^ 2))) * Real.exp (|u| / 2) := by
        gcongr
    _ = M * Real.exp (σ / 4) * (1 / σ + 1) * Real.exp (|u| / 2) * (1 / ‖z‖ ^ (2 : ℕ)) := by
        ring

/-- **Limit form of the receiver.** Locally uniform limits of uniformly bounded strip-holomorphic
weights with only real zeros, satisfying the one-sided Gaussian zero-side identity asymptotically,
force the Riemann hypothesis. -/
theorem riemannHypothesis_of_tendsto_gaussianOneSidedIdentity
    {η M σ : ℝ} (hη : 0 < η) (hσ : 0 < σ)
    {Fs : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {κs : ℕ → ℂ} {κ : ℂ}
    (hFs : ∀ j, DifferentiableOn ℂ (Fs j) (xiOneSidedStrip η))
    (hbound : ∀ j, ∀ z ∈ xiOneSidedStrip η, ‖Fs j z‖ ≤ M)
    (hreal : ∀ j, ∀ z ∈ xiOneSidedStrip η, Fs j z = 0 → z.im = 0)
    (hconv : TendstoLocallyUniformlyOn Fs F atTop (xiOneSidedStrip η))
    {a : ℂ} (ha : a ∈ xiOneSidedStrip η) (haF : F a ≠ 0)
    (hκ : Tendsto κs atTop (𝓝 κ))
    (hid : ∀ u : ℝ, 0 < u →
      Tendsto (fun j => (∑' q : XiZeroCopy, gaussModulated (Fs j) σ u (xiSpectralPoint q)) -
        κs j * ∫ t : ℝ, gaussModulated (Fs j) σ u (t : ℂ)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  set U := xiOneSidedStrip η with hUdef
  have hUopen : IsOpen U := isOpen_xiOneSidedStrip η
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hbound 0 a ha)
  have hFdiff : DifferentiableOn ℂ F U :=
    hconv.differentiableOn (Eventually.of_forall hFs) hUopen
  have hpt : ∀ z ∈ U, Tendsto (fun j => Fs j z) atTop (𝓝 (F z)) :=
    fun z hz => hconv.tendsto_at hz
  have hFbound : ∀ z ∈ U, ‖F z‖ ≤ M := by
    intro z hz
    exact le_of_tendsto' ((hpt z hz).norm) fun j => hbound j z hz
  have hFreal : ∀ z ∈ U, F z = 0 → z.im = 0 := by
    intro z hz hFz
    have hS : IsClosed {w : ℂ | w.im = 0} := isClosed_eq Complex.continuous_im continuous_const
    have := CCMXiStrip.zero_mem_closed_of_tendstoLocallyUniformlyOn (S := {w : ℂ | w.im = 0})
      hUopen (convex_xiOneSidedStrip η).isPreconnected hconv (hFdiff.analyticOnNhd hUopen)
      (Eventually.of_forall hFs) hS (Eventually.of_forall fun j w hw hzero => hreal j w hw hzero)
      ha haF hz hFz
    exact this
  have hγU : ∀ q : XiZeroCopy, xiSpectralPoint q ∈ U := by
    intro q
    have := xiSpectralPoint_im_mem_openHalf q
    show |(xiSpectralPoint q).im| < 1 / 2 + η
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]
  have hlineU : ∀ t : ℝ, (t : ℂ) ∈ U := by
    intro t
    show |((t : ℂ)).im| < 1 / 2 + η
    simp only [ofReal_im, abs_zero]
    linarith
  -- the limit identity
  have hlim : ∀ u : ℝ, 0 < u →
      ∑' q : XiZeroCopy, gaussModulated F σ u (xiSpectralPoint q) =
        κ * ∫ t : ℝ, gaussModulated F σ u (t : ℂ) := by
    intro u hu
    set C : ℝ := M * Real.exp (σ / 4) * (1 / σ + 1) * Real.exp (|u| / 2) with hC
    have hsum : Tendsto (fun j => ∑' q : XiZeroCopy, gaussModulated (Fs j) σ u (xiSpectralPoint q))
        atTop (𝓝 (∑' q : XiZeroCopy, gaussModulated F σ u (xiSpectralPoint q))) := by
      refine tendsto_tsum_of_dominated_convergence
        (bound := fun q : XiZeroCopy => C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))
        (xiSpectralPoint_inv_sq_summable.mul_left C) (fun q => ?_)
        (Eventually.of_forall fun j q => ?_)
      · unfold gaussModulated
        exact ((hpt _ (hγU q)).mul_const _).mul_const _
      · exact norm_gaussModulated_xiSpectralPoint_le hσ hM q (hbound j _ (hγU q))
    have hint : Tendsto (fun j => ∫ t : ℝ, gaussModulated (Fs j) σ u (t : ℂ)) atTop
        (𝓝 (∫ t : ℝ, gaussModulated F σ u (t : ℂ))) := by
      have hcontj : ∀ j, Continuous fun t : ℝ => gaussModulated (Fs j) σ u (t : ℂ) := by
        intro j
        rw [continuous_iff_continuousAt]
        intro t
        have hFc : ContinuousAt (Fs j) (t : ℂ) :=
          ((hFs j).differentiableAt (hUopen.mem_nhds (hlineU t))).continuousAt
        have hcomp : ContinuousAt (fun t : ℝ => Fs j (t : ℂ)) t :=
          ContinuousAt.comp (g := Fs j) hFc Complex.continuous_ofReal.continuousAt
        have he1 : Continuous fun t : ℝ => cexp (-(σ : ℂ) * (t : ℂ) ^ 2) := by fun_prop
        have he2 : Continuous fun t : ℝ => cexp (-(I * (t : ℂ)) * u) := by fun_prop
        unfold gaussModulated
        exact (hcomp.mul he1.continuousAt).mul he2.continuousAt
      refine tendsto_integral_of_dominated_convergence
        (fun t : ℝ => M * Real.exp (-σ * t ^ 2)) (fun j => (hcontj j).aestronglyMeasurable)
        ((integrable_exp_neg_mul_sq hσ).const_mul M) (fun j => ae_of_all _ fun t => ?_)
        (ae_of_all _ fun t => ?_)
      · rw [gaussModulated, norm_mul, norm_mul, norm_cexp_neg_ofReal_mul_sq,
          norm_cexp_neg_I_mul_ofReal]
        simp only [ofReal_re, ofReal_im, mul_zero, Real.exp_zero, mul_one]
        have : Real.exp (-(σ * (t ^ 2 - 0 ^ 2))) = Real.exp (-σ * t ^ 2) := by ring_nf
        rw [this]
        gcongr
        exact hbound j _ (hlineU t)
      · unfold gaussModulated
        exact ((hpt _ (hlineU t)).mul_const _).mul_const _
    have hcomb := hsum.sub (hκ.mul hint)
    exact sub_eq_zero.mp (tendsto_nhds_unique hcomb (hid u hu))
  -- apply the exact receiver with `A = 0`
  refine riemannHypothesis_of_gaussianOneSidedZeroIdentity (η := η) (M := M) (A := 0) (σ := σ)
    hη le_rfl hσ (F := F) (fun z hz => hFdiff.differentiableAt (hUopen.mem_nhds hz))
    (fun z hz => ?_) (fun z hz hFz => hFreal z hz hFz) κ hlim
  rw [zero_mul, Real.exp_zero, mul_one]
  exact hFbound z hz

end

end RHTower
