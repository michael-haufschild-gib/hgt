import GaloisForLFunctions.RHTower.STCFlatGapPrimeLogReaderNoGo
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.L2Space

/-!
# No bounded spectral reader of the grade current on prime features

Let `μ` be a finite measure on the spectral line and `w` a density.  The bilateral Laplace
transform `L(z) = ∫ w(u) e^{uz} dμ(u)` is entire whenever `|w|` has all exponential moments; its
imaginary-axis trace is bounded by `∫ |w| dμ`.

* **Compact band (card (7)).** If `μ` is carried by `[-b,b]`, then `L` has exponential type, so by
  prime-log uniqueness it cannot equal `c (log p) sinh(g log p)` (`c ≠ 0`, `g ≠ 0`) at every prime:
  on the imaginary axis the grade current `z sinh(gz)` is unbounded.  Consequently no bounded
  functional on `L²(μ)` maps every prime exponential feature to its grade charge.
* **Gaussian carrier (card (8)).** For centered Gaussian `μ_σ` and `w ∈ L²(μ_σ)`,
  `|F_w(z)| ≤ ‖w‖₂ exp(σ²(Re z)²) ≤ ‖w‖₂ exp(σ²|z|²)` and `|F_w(it)| ≤ ‖w‖₂`; `F_w` is entire of
  finite order, and again no bounded functional on `L²(μ_σ)` reads the grade current on all prime
  features.
-/

open Complex Filter Topology MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal

namespace RHTower

noncomputable section

/-! ### Laplace transforms of densities with exponential moments -/

/-- The bilateral Laplace transform `z ↦ ∫ w(u) e^{uz} dμ(u)`. -/
def spectralLaplace (μ : Measure ℝ) (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ u, w u * cexp ((u : ℂ) * z) ∂μ

private theorem norm_cexp_ofReal_mul (u : ℝ) (z : ℂ) :
    ‖cexp ((u : ℂ) * z)‖ = Real.exp (u * z.re) := by
  rw [Complex.norm_exp]; simp

private theorem norm_cexp_ofReal_mul_le (u : ℝ) (z : ℂ) :
    ‖cexp ((u : ℂ) * z)‖ ≤ Real.exp (|u| * ‖z‖) := by
  rw [norm_cexp_ofReal_mul]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg u)))

/-- **Entire Laplace transform.** If `|w|` has every exponential moment, `spectralLaplace μ w` is
entire. -/
theorem differentiable_spectralLaplace {μ : Measure ℝ} {w : ℝ → ℂ} (hw : AEStronglyMeasurable w μ)
    (hmom : ∀ c : ℝ, Integrable (fun u => ‖w u‖ * Real.exp (c * |u|)) μ) :
    Differentiable ℂ (spectralLaplace μ w) := by
  intro z₀
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun u : ℝ => w u * cexp ((u : ℂ) * z)) μ :=
    fun z => hw.mul (by fun_prop : Continuous fun u : ℝ => cexp ((u : ℂ) * z)).aestronglyMeasurable
  have hint : Integrable (fun u : ℝ => w u * cexp ((u : ℂ) * z₀)) μ := by
    refine (hmom ‖z₀‖).mono' (hmeas z₀) (Eventually.of_forall fun u => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_cexp_ofReal_mul_le u z₀).trans
      (by rw [mul_comm])) (norm_nonneg _)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun z u => w u * cexp ((u : ℂ) * z)) (F' := fun z u => w u * ((u : ℂ) * cexp ((u : ℂ) * z)))
    (x₀ := z₀) (bound := fun u => ‖w u‖ * Real.exp ((‖z₀‖ + 2) * |u|))
    (Metric.ball_mem_nhds z₀ one_pos) (Eventually.of_forall hmeas) hint
    (hw.mul (by fun_prop : Continuous fun u : ℝ => (u : ℂ) * cexp ((u : ℂ) * z₀)).aestronglyMeasurable)
    (Eventually.of_forall fun u z hz => ?_) (hmom _) (Eventually.of_forall fun u z _ => ?_)
  · exact hderiv.2.differentiableAt
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_le_of_mem_closedBall (Metric.ball_subset_closedBall hz)
      have h2 := norm_sub_norm_le z z₀
      rw [Metric.mem_ball, dist_eq_norm] at hz
      linarith
    have h1 := norm_cexp_ofReal_mul_le u z
    have h2 : |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|]
    calc |u| * ‖cexp ((u : ℂ) * z)‖ ≤ Real.exp |u| * Real.exp (|u| * ‖z‖) :=
          mul_le_mul h2 h1 (norm_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (|u| + |u| * ‖z‖) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((‖z₀‖ + 2) * |u|) := Real.exp_le_exp.mpr (by nlinarith [abs_nonneg u])
  · have := ((hasDerivAt_id z).const_mul (u : ℂ)).cexp.const_mul (w u)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this

theorem norm_spectralLaplace_le {μ : Measure ℝ} {w : ℝ → ℂ} (z : ℂ) :
    ‖spectralLaplace μ w z‖ ≤ ∫ u, ‖w u‖ * Real.exp (u * z.re) ∂μ := by
  unfold spectralLaplace
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [norm_mul, norm_cexp_ofReal_mul]

/-- On the imaginary axis the Laplace transform is bounded by the total variation. -/
theorem norm_spectralLaplace_imag_le {μ : Measure ℝ} {w : ℝ → ℂ} (t : ℝ) :
    ‖spectralLaplace μ w (I * (t : ℂ))‖ ≤ ∫ u, ‖w u‖ ∂μ := by
  refine (norm_spectralLaplace_le _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp

/-- **Abstract reader no-go.** An entire function of finite order with bounded imaginary trace does
not equal `c (log p) sinh(g log p)` at every prime, for `c ≠ 0` and `g ≠ 0`. -/
theorem no_finiteOrder_reader_gradeCharge {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {A B ρ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 1 ≤ ρ)
    (hgrowth : ∀ z : ℂ, ‖F z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ))
    (himag : ∃ M : ℝ, ∀ t : ℝ, ‖F (I * (t : ℂ))‖ ≤ M) {g : ℝ} (hg : g ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    ¬ ∀ p : ℕ, p.Prime → F (Real.log p) = c * ((Real.log p * Real.sinh (g * Real.log p) : ℝ) : ℂ) := by
  intro hprime
  set a := |g| with hadef
  have ha : 0 < a := abs_pos.mpr hg
  set s : ℂ := ((Real.sign g : ℝ) : ℂ)
  have hs : s ≠ 0 := by
    rcases lt_or_gt_of_ne hg with h | h <;> simp [s, Real.sign_of_neg, Real.sign_of_pos, h]
  have hsinh : ∀ x : ℝ, Real.sinh (g * x) = Real.sign g * Real.sinh (a * x) := by
    intro x
    rcases lt_or_gt_of_ne hg with h | h
    · rw [hadef, abs_of_neg h, Real.sign_of_neg h, show -g * x = -(g * x) by ring, Real.sinh_neg]
      ring
    · rw [hadef, abs_of_pos h, Real.sign_of_pos h, one_mul]
  set G : ℂ → ℂ := fun z => (c * s)⁻¹ * F z
  have hG : Differentiable ℂ G := hF.const_mul _
  refine stc_no_finiteOrder_boundedImaginary_gradeCurrent a ha G hG
    (‖(c * s)⁻¹‖ * A + Real.exp (a + 1)) (B + a + 1) ρ
    (le_add_of_nonneg_of_le (by positivity) (Real.one_le_exp (by linarith)))
    (by positivity) (by linarith) (fun z => ?_) ?_ ?_
  · -- growth
    have hz1 : ‖z * Complex.sinh ((a : ℂ) * z)‖ ≤ Real.exp ((a + 1) * ‖z‖) := by
      rw [norm_mul, Complex.sinh]
      have hsh : ‖(cexp ((a : ℂ) * z) - cexp (-((a : ℂ) * z))) / 2‖ ≤ Real.exp (a * ‖z‖) := by
        rw [norm_div, RCLike.norm_ofNat]
        have e1 : ‖cexp ((a : ℂ) * z)‖ ≤ Real.exp (a * ‖z‖) := by
          have := norm_cexp_ofReal_mul_le a z; rwa [abs_of_pos ha] at this
        have e2 : ‖cexp (-((a : ℂ) * z))‖ ≤ Real.exp (a * ‖z‖) := by
          have := norm_cexp_ofReal_mul_le (-a) z
          rw [abs_neg, abs_of_pos ha] at this
          simpa [neg_mul] using this
        have := norm_sub_le (cexp ((a : ℂ) * z)) (cexp (-((a : ℂ) * z)))
        linarith
      have hzexp : ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
      calc ‖z‖ * ‖(cexp ((a : ℂ) * z) - cexp (-((a : ℂ) * z))) / 2‖
          ≤ Real.exp ‖z‖ * Real.exp (a * ‖z‖) := mul_le_mul hzexp hsh (norm_nonneg _)
            (Real.exp_nonneg _)
        _ = Real.exp ((a + 1) * ‖z‖) := by rw [← Real.exp_add]; ring_nf
    have hzρ : ‖z‖ ≤ ‖z‖ ^ ρ + 1 := by
      rcases le_or_gt ‖z‖ 1 with h | h
      · have := Real.rpow_nonneg (norm_nonneg z) ρ; linarith
      · have := Real.self_le_rpow_of_one_le h.le hρ; linarith
    have hGz : ‖G z‖ ≤ ‖(c * s)⁻¹‖ * A * Real.exp (B * ‖z‖ ^ ρ) := by
      simp only [G, norm_mul]
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hgrowth z) (norm_nonneg _)
    have hE1 : Real.exp (B * ‖z‖ ^ ρ) ≤ Real.exp ((B + a + 1) * ‖z‖ ^ ρ) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.rpow_nonneg (norm_nonneg z) ρ])
    have hE2 : Real.exp ((a + 1) * ‖z‖) ≤ Real.exp ((B + a + 1) * ‖z‖ ^ ρ) * Real.exp (a + 1) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.rpow_nonneg (norm_nonneg z) ρ])
    have hsub := norm_sub_le (G z) (z * Complex.sinh ((a : ℂ) * z))
    have hK : 0 ≤ ‖(c * s)⁻¹‖ * A := by positivity
    calc ‖G z - z * Complex.sinh ((a : ℂ) * z)‖
        ≤ ‖G z‖ + ‖z * Complex.sinh ((a : ℂ) * z)‖ := hsub
      _ ≤ ‖(c * s)⁻¹‖ * A * Real.exp ((B + a + 1) * ‖z‖ ^ ρ) +
          Real.exp ((B + a + 1) * ‖z‖ ^ ρ) * Real.exp (a + 1) := by
          gcongr
          · exact hGz.trans (mul_le_mul_of_nonneg_left hE1 hK)
          · exact hz1.trans hE2
      _ = (‖(c * s)⁻¹‖ * A + Real.exp (a + 1)) * Real.exp ((B + a + 1) * ‖z‖ ^ ρ) := by ring
  · obtain ⟨M, hM⟩ := himag
    exact ⟨‖(c * s)⁻¹‖ * M, fun t => by
      simp only [G, norm_mul]; exact mul_le_mul_of_nonneg_left (hM t) (norm_nonneg _)⟩
  · intro p hp
    simp only [G]
    rw [hprime p hp, hsinh]
    push_cast
    field_simp
    simp only [s]
    ring

/-! ### Compactly supported spectral measures -/

/-- **(7) Compact band.** For a finite measure carried by `[-b,b]` and an integrable density `w`,
the Laplace transform does not equal `c (log p) sinh(g log p)` at every prime (`c, g ≠ 0`). -/
theorem no_compact_spectral_measure_gradeCharge {μ : Measure ℝ} [IsFiniteMeasure μ] {w : ℝ → ℂ}
    (hw : Integrable w μ) {b : ℝ} (hb : ∀ᵐ u ∂μ, |u| ≤ b) {g : ℝ} (hg : g ≠ 0) {c : ℂ}
    (hc : c ≠ 0) :
    ¬ ∀ p : ℕ, p.Prime → spectralLaplace μ w (Real.log p) =
      c * ((Real.log p * Real.sinh (g * Real.log p) : ℝ) : ℂ) := by
  set B := max b 0
  have hbB : ∀ᵐ u ∂μ, |u| ≤ B := hb.mono fun u hu => hu.trans (le_max_left _ _)
  have hmom : ∀ c : ℝ, Integrable (fun u => ‖w u‖ * Real.exp (c * |u|)) μ := by
    intro c'
    refine (hw.norm.mul_const (Real.exp (|c'| * B))).mono'
      (hw.norm.aestronglyMeasurable.mul (by fun_prop : Continuous fun u : ℝ =>
        Real.exp (c' * |u|)).aestronglyMeasurable) ?_
    filter_upwards [hbB] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    calc c' * |u| ≤ |c'| * |u| := mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
      _ ≤ |c'| * B := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
  refine no_finiteOrder_reader_gradeCharge (differentiable_spectralLaplace hw.aestronglyMeasurable
    hmom) (A := ∫ u, ‖w u‖ ∂μ) (B := B) (ρ := 1) (integral_nonneg fun u => norm_nonneg _)
    (le_max_right _ _) le_rfl (fun z => ?_) ⟨_, norm_spectralLaplace_imag_le⟩ hg hc
  have hle : ∀ u : ℝ, |u| ≤ B → u * z.re ≤ B * ‖z‖ := by
    intro u hu
    have h1 : u * z.re ≤ |u| * ‖z‖ :=
      calc u * z.re ≤ |u * z.re| := le_abs_self _
        _ = |u| * |z.re| := abs_mul _ _
        _ ≤ |u| * ‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg u)
    exact h1.trans (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
  refine (norm_spectralLaplace_le z).trans ?_
  rw [Real.rpow_one, ← integral_mul_const]
  refine integral_mono_ae ?_ (hw.norm.mul_const _) ?_
  · refine (hw.norm.mul_const (Real.exp (B * ‖z‖))).mono'
      (hw.norm.aestronglyMeasurable.mul (by fun_prop : Continuous fun u : ℝ =>
        Real.exp (u * z.re)).aestronglyMeasurable) ?_
    filter_upwards [hbB] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hle u hu)) (norm_nonneg _)
  · filter_upwards [hbB] with u hu
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hle u hu)) (norm_nonneg _)

/-- The exponential spectral feature `u ↦ e^{ux}` of a finite measure carried by `[-b,b]`. -/
def compactSpectralFeature (μ : Measure ℝ) [IsFiniteMeasure μ] {b : ℝ} (hb : ∀ᵐ u ∂μ, |u| ≤ b)
    (x : ℝ) : Lp ℂ 2 μ :=
  MemLp.toLp (fun u : ℝ => cexp ((u : ℂ) * x))
    (MemLp.of_bound (by fun_prop : Continuous fun u : ℝ => cexp ((u : ℂ) * x)).aestronglyMeasurable
      (Real.exp (|x| * max b 0)) (hb.mono fun u hu => by
        refine (norm_cexp_ofReal_mul_le u x).trans (Real.exp_le_exp.mpr ?_)
        rw [Complex.norm_real, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_left (hu.trans (le_max_left _ _)) (abs_nonneg _)))

/-- Riesz readout of a bounded functional on an exponential feature. -/
private theorem riesz_readout_feature {μ : Measure ℝ} (φ : Lp ℂ 2 μ →L[ℂ] ℂ) (x : ℝ)
    (hf : MemLp (fun u : ℝ => cexp ((u : ℂ) * x)) 2 μ) :
    φ (MemLp.toLp _ hf) = spectralLaplace μ
      (fun u => conj ((((InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm φ : Lp ℂ 2 μ) :
        ℝ → ℂ) u)) x := by
  rw [← InnerProductSpace.toDual_symm_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hf] with u hu
  rw [hu]
  simp [mul_comm]

/-- The conjugated Riesz vector of a bounded functional on `L²(μ)`, `μ` finite, is integrable. -/
private theorem integrable_conj_riesz {μ : Measure ℝ} [IsFiniteMeasure μ]
    (φ : Lp ℂ 2 μ →L[ℂ] ℂ) :
    Integrable (fun u => conj ((((InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm φ : Lp ℂ 2 μ) :
      ℝ → ℂ) u)) μ := by
  have hW := (Lp.memLp ((InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm φ)).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine hW.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
    hW.aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  simp

/-- **Hilbert corollary (compact band).** No bounded functional on `L²(μ)`, `μ` a finite measure
carried by `[-b,b]`, sends every prime exponential feature `e^{u log p}` to `c (log p) sinh(g log p)`
(`c, g ≠ 0`); common nonzero factors (half-density, vertical phase) on both sides do not help. -/
theorem no_bounded_compact_reader_gradeCharge {μ : Measure ℝ} [IsFiniteMeasure μ] {b : ℝ}
    (hb : ∀ᵐ u ∂μ, |u| ≤ b) {g : ℝ} (hg : g ≠ 0) {c : ℂ} (hc : c ≠ 0) (lam : ℕ → ℂ)
    (hlam : ∀ p, lam p ≠ 0) :
    ¬ ∃ φ : Lp ℂ 2 μ →L[ℂ] ℂ, ∀ p : ℕ, p.Prime →
      φ (lam p • compactSpectralFeature μ hb (Real.log p)) =
        lam p * (c * ((Real.log p * Real.sinh (g * Real.log p) : ℝ) : ℂ)) := by
  rintro ⟨φ, hφ⟩
  refine no_compact_spectral_measure_gradeCharge (integrable_conj_riesz φ) hb hg hc fun p hp => ?_
  have h := hφ p hp
  rw [map_smul, smul_eq_mul] at h
  have h' := mul_left_cancel₀ (hlam p) h
  rw [compactSpectralFeature, riesz_readout_feature] at h'
  exact h'

/-! ### Gaussian spectral carriers -/

/-- Gaussian exponential features are square integrable. -/
theorem memLp_gaussian_feature (v : ℝ≥0) (z : ℂ) :
    MemLp (fun u : ℝ => cexp ((u : ℂ) * z)) 2 (ProbabilityTheory.gaussianReal 0 v) := by
  have hmeas : AEStronglyMeasurable (fun u : ℝ => cexp ((u : ℂ) * z))
      (ProbabilityTheory.gaussianReal 0 v) :=
    (by fun_prop : Continuous fun u : ℝ => cexp ((u : ℂ) * z)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := v) (2 * z.re)).congr
    (Eventually.of_forall fun u => ?_)
  simp only
  rw [norm_cexp_ofReal_mul, sq, ← Real.exp_add]
  ring_nf

/-- The Gaussian exponential feature `E_z` in `L²(μ_σ)`. -/
def gaussianFeature (v : ℝ≥0) (z : ℂ) : Lp ℂ 2 (ProbabilityTheory.gaussianReal 0 v) :=
  MemLp.toLp _ (memLp_gaussian_feature v z)

/-- `‖E_z‖ = exp(σ² (Re z)²)` (Gaussian moment generating function). -/
theorem norm_gaussianFeature (v : ℝ≥0) (z : ℂ) :
    ‖gaussianFeature v z‖ = Real.exp (v * z.re ^ 2) := by
  have hsq : ‖gaussianFeature v z‖ ^ 2 = Real.exp (2 * v * z.re ^ 2) := by
    have h1 : ‖gaussianFeature v z‖ ^ 2 =
        RCLike.re ⟪gaussianFeature v z, gaussianFeature v z⟫_ℂ := (inner_self_eq_norm_sq _).symm
    rw [L2.inner_def] at h1
    have h2 : ∫ u, ⟪(gaussianFeature v z : ℝ → ℂ) u, (gaussianFeature v z : ℝ → ℂ) u⟫_ℂ
        ∂(ProbabilityTheory.gaussianReal 0 v) =
        ((ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 v) (2 * z.re) : ℝ) : ℂ) := by
      rw [ProbabilityTheory.mgf, ← integral_complex_ofReal]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_gaussian_feature v z)] with u hu
      simp only [gaussianFeature] at hu ⊢
      rw [hu, inner_self_eq_norm_sq_to_K, norm_cexp_ofReal_mul]
      simp only [id]
      norm_cast
      rw [← Real.exp_nat_mul]
      ring_nf
      rfl
    rw [h2, ProbabilityTheory.mgf_id_gaussianReal, RCLike.re_to_complex, Complex.ofReal_re] at h1
    rw [h1]
    ring_nf
  have hpos := Real.exp_pos (v * z.re ^ 2)
  have h := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), show 2 * (v : ℝ) * z.re ^ 2 = 2 * (v * z.re ^ 2) by ring,
    show Real.exp (2 * (v * z.re ^ 2)) = Real.exp (v * z.re ^ 2) ^ 2 by
      rw [← Real.exp_nat_mul]; ring_nf, Real.sqrt_sq hpos.le] at h
  exact h

/-- The readout `R_w(z) = ⟪w, E_z⟫` of an `L²(μ_σ)` vector. -/
def gaussianReadout (v : ℝ≥0) (w : Lp ℂ 2 (ProbabilityTheory.gaussianReal 0 v)) (z : ℂ) : ℂ :=
  ⟪w, gaussianFeature v z⟫_ℂ

/-- **(8)** `|R_w(z)| ≤ ‖w‖₂ exp(σ²(Re z)²) ≤ ‖w‖₂ exp(σ²|z|²)` and `|R_w(it)| ≤ ‖w‖₂`. -/
theorem norm_gaussianReadout_le (v : ℝ≥0) (w : Lp ℂ 2 (ProbabilityTheory.gaussianReal 0 v))
    (z : ℂ) :
    ‖gaussianReadout v w z‖ ≤ ‖w‖ * Real.exp (v * z.re ^ 2) ∧
      ‖w‖ * Real.exp (v * z.re ^ 2) ≤ ‖w‖ * Real.exp (v * ‖z‖ ^ 2) := by
  refine ⟨(norm_inner_le_norm _ _).trans (le_of_eq (by rw [norm_gaussianFeature])), ?_⟩
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ v.2
  have := Complex.abs_re_le_norm z
  nlinarith [abs_nonneg z.re, sq_abs z.re]

theorem norm_gaussianReadout_imag_le (v : ℝ≥0) (w : Lp ℂ 2 (ProbabilityTheory.gaussianReal 0 v))
    (t : ℝ) : ‖gaussianReadout v w (I * (t : ℂ))‖ ≤ ‖w‖ := by
  have := (norm_gaussianReadout_le v w (I * (t : ℂ))).1
  simpa using this

/-- The readout is the Laplace transform of the conjugated density. -/
theorem gaussianReadout_eq_spectralLaplace (v : ℝ≥0)
    (w : Lp ℂ 2 (ProbabilityTheory.gaussianReal 0 v)) (z : ℂ) :
    gaussianReadout v w z = spectralLaplace (ProbabilityTheory.gaussianReal 0 v)
      (fun u => conj ((w : ℝ → ℂ) u)) z := by
  unfold gaussianReadout gaussianFeature
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_gaussian_feature v z)] with u hu
  rw [hu]
  simp [mul_comm]

/-- The readout is entire. -/
theorem differentiable_gaussianReadout (v : ℝ≥0)
    (w : Lp ℂ 2 (ProbabilityTheory.gaussianReal 0 v)) :
    Differentiable ℂ (gaussianReadout v w) := by
  have heq : gaussianReadout v w = spectralLaplace (ProbabilityTheory.gaussianReal 0 v)
      (fun u => conj ((w : ℝ → ℂ) u)) := funext (gaussianReadout_eq_spectralLaplace v w)
  rw [heq]
  refine differentiable_spectralLaplace (Complex.continuous_conj.comp_aestronglyMeasurable
    (Lp.memLp w).aestronglyMeasurable) fun c => ?_
  -- `|w| ∈ L²` and `e^{c|u|} ∈ L²`, so the product is integrable
  have hw2 : MemLp (fun u => ‖(w : ℝ → ℂ) u‖) 2 (ProbabilityTheory.gaussianReal 0 v) :=
    (Lp.memLp w).norm
  have hmeas : AEStronglyMeasurable (fun u : ℝ => Real.exp (c * |u|))
      (ProbabilityTheory.gaussianReal 0 v) :=
    (by fun_prop : Continuous fun u : ℝ => Real.exp (c * |u|)).aestronglyMeasurable
  have he2 : MemLp (fun u : ℝ => Real.exp (c * |u|)) 2 (ProbabilityTheory.gaussianReal 0 v) := by
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    refine ((ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := v) (2 * c)).add
      (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-(2 * c)))).mono'
      (hmeas.norm.pow 2) (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), sq, ← Real.exp_add, Pi.add_apply]
    have h1 := Real.exp_pos (2 * c * u)
    have h2 := Real.exp_pos (-(2 * c) * u)
    rcases le_or_gt 0 u with hu | hu
    · rw [abs_of_nonneg hu, show c * u + c * u = 2 * c * u by ring]; linarith
    · rw [abs_of_neg hu, show c * -u + c * -u = -(2 * c) * u by ring]; linarith
  exact (hw2.integrable_mul he2).congr (Eventually.of_forall fun u => by simp)

/-- **Gaussian carrier no-go.** No bounded functional on `L²(μ_σ)` sends every prime exponential
feature to `c (log p) sinh(g log p)` (`c, g ≠ 0`), even after common nonzero factors. -/
theorem no_bounded_gaussian_reader_gradeCharge (v : ℝ≥0) {g : ℝ} (hg : g ≠ 0) {c : ℂ}
    (hc : c ≠ 0) (lam : ℕ → ℂ) (hlam : ∀ p, lam p ≠ 0) :
    ¬ ∃ φ : Lp ℂ 2 (ProbabilityTheory.gaussianReal 0 v) →L[ℂ] ℂ, ∀ p : ℕ, p.Prime →
      φ (lam p • gaussianFeature v (Real.log p)) =
        lam p * (c * ((Real.log p * Real.sinh (g * Real.log p) : ℝ) : ℂ)) := by
  rintro ⟨φ, hφ⟩
  set W := (InnerProductSpace.toDual ℂ (Lp ℂ 2 (ProbabilityTheory.gaussianReal 0 v))).symm φ
  have hread : ∀ z, φ (gaussianFeature v z) = gaussianReadout v W z := by
    intro z
    rw [gaussianReadout, InnerProductSpace.toDual_symm_apply]
  refine no_finiteOrder_reader_gradeCharge (differentiable_gaussianReadout v W)
    (A := ‖W‖) (B := v) (ρ := 2) (norm_nonneg _) v.2 (by norm_num) (fun z => ?_)
    ⟨‖W‖, norm_gaussianReadout_imag_le v W⟩ hg hc fun p hp => ?_
  · have h := norm_gaussianReadout_le v W z
    rw [show ‖z‖ ^ (2 : ℝ) = ‖z‖ ^ 2 by norm_cast]
    exact h.1.trans h.2
  · have h := hφ p hp
    rw [map_smul, smul_eq_mul, hread] at h
    exact mul_left_cancel₀ (hlam p) h

end

end RHTower
