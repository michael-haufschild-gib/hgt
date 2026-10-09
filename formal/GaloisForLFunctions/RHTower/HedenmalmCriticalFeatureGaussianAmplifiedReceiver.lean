import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureHolomorphicSectorCoercivity
import GaloisForLFunctions.RHTower.SuzukiV0WeilForm
import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric
import GaloisForLFunctions.HTGeometry.GaussianLightConeAmplification

/-!
# Gaussian-amplified critical-feature diagonal: one off-line zero is cofinally visible

The HCF diagonal `Σ_γ F_t(γ)²`, `F_t(z) = 2/(1 + (z - t)²)`, weighs every Xi multiplicity copy by
a bounded amount, so it can only detect off-line zeros through a ceiling below one quantum.  Here
the critical feature is amplified by the real-on-real Gaussian `exp(-σ (z - t)²)`:

`𝒜(t, σ) = Σ_γ F_t(γ)² exp(-σ (γ - t)²)`   (`criticalFeatureGaussianAmplifiedTrace`).

For a spectral point `γ = x + iy` the amplifier has modulus `exp(-σ((x - t)² - y²))`.  It is at most
one exactly on the closed cone `|y| ≤ |x - t|` and grows exponentially in `σ` on the open light cone
`|x - t| < |y|` over the height `t`.

* **Local law** (`criticalFeatureGaussianAmplifiedTrace_bounded_iff`): `σ ↦ 𝒜(t, σ)` is bounded on
  `[0, ∞)` iff no Xi zero copy lies in the open light cone over `t`.  On the cone side every term is
  dominated by the Hermitian feature energy.  Otherwise the coefficient `(2/(1 + W))²` depends only
  on the exponent `W = (γ - t)²`, and the light-cone amplification lemma
  (`HTGeometry.exists_lt_norm_tsum_mul_exp_neg_of_re_neg`) makes the trace unbounded.
* **Global receiver** (`riemannHypothesis_iff_forall_criticalFeatureGaussianAmplifiedTrace_bounded`):
  RH holds iff `𝒜(t, ·)` is bounded for every real `t`.  Under RH the bound is the Hermitian
  feature energy, uniformly in `σ`.  An off-line copy `γ₀` lies in the cone over its own height.

So a ceiling of any size, at the right heights, already forces every zero onto the line: the
sub-quantum exactness barrier of the unamplified lattice budget disappears under amplification.
-/

open Complex Filter Topology Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The squared real-centred critical feature amplified by the Gaussian `exp(-σ (z - t)²)`. -/
def criticalFeatureGaussianAmplifiedTerm (t σ : ℝ) (z : ℂ) : ℂ :=
  criticalFeatureCauchyKernelTest t z ^ 2 * Complex.exp (-(σ : ℂ) * (z - t) ^ 2)

/-- Gaussian-amplified HCF diagonal over the multiplicity-exact Xi divisor. -/
def criticalFeatureGaussianAmplifiedTrace (t σ : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, criticalFeatureGaussianAmplifiedTerm t σ (xiSpectralPoint q)

/-- Inside the critical strip the critical feature is the Cauchy kernel `2 / (1 + (z - t)²)`. -/
theorem criticalFeatureCauchyKernelTest_eq_div {t : ℝ} {z : ℂ} (hz : |z.im| < 1 / 2) :
    criticalFeatureCauchyKernelTest t z = 2 / (1 + (z - t) ^ 2) := by
  have hl : z ≠ (t : ℂ) - I := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.I_im, zero_sub] at him
    rw [him] at hz
    norm_num at hz
  have hu : z ≠ (t : ℂ) + I := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add] at him
    rw [him] at hz
    norm_num at hz
  rw [criticalFeatureCauchyKernelTest, ← criticalKernel_eq_hardyCauchySum hl hu]

theorem norm_criticalFeatureGaussianAmplifiedTerm (t σ : ℝ) (z : ℂ) :
    ‖criticalFeatureGaussianAmplifiedTerm t σ z‖ =
      Complex.normSq (criticalFeatureCauchyKernelTest t z) *
        Real.exp (-(σ * ((z.re - t) ^ 2 - z.im ^ 2))) := by
  rw [criticalFeatureGaussianAmplifiedTerm, norm_mul, norm_pow, norm_exp_neg_mul_sub_sq,
    Complex.normSq_eq_norm_sq]

/-- In the strip the amplifier costs at most `exp(σ/4)`. -/
theorem norm_criticalFeatureGaussianAmplifiedTerm_le {t σ : ℝ} (hσ : 0 ≤ σ) {z : ℂ}
    (hz : |z.im| < 1 / 2) :
    ‖criticalFeatureGaussianAmplifiedTerm t σ z‖ ≤
      Real.exp (σ / 4) * Complex.normSq (criticalFeatureCauchyKernelTest t z) := by
  rw [norm_criticalFeatureGaussianAmplifiedTerm, mul_comm]
  have hy : z.im ^ 2 ≤ 1 / 4 := by
    have := sq_le_sq' (abs_le.1 hz.le).1 (abs_le.1 hz.le).2
    linarith
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.2 (by nlinarith [sq_nonneg (z.re - t)])) (Complex.normSq_nonneg _)

/-- On the closed cone `|Im z| ≤ |Re z - t|` the amplifier is at most one. -/
theorem norm_criticalFeatureGaussianAmplifiedTerm_le_of_cone {t σ : ℝ} (hσ : 0 ≤ σ) {z : ℂ}
    (hcone : z.im ^ 2 ≤ (z.re - t) ^ 2) :
    ‖criticalFeatureGaussianAmplifiedTerm t σ z‖ ≤
      Complex.normSq (criticalFeatureCauchyKernelTest t z) := by
  rw [norm_criticalFeatureGaussianAmplifiedTerm]
  refine mul_le_of_le_one_right (Complex.normSq_nonneg _) ?_
  rw [Real.exp_le_one_iff]
  nlinarith

theorem summable_norm_criticalFeatureGaussianAmplifiedTerm (t : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    Summable (fun q : XiZeroCopy =>
      ‖criticalFeatureGaussianAmplifiedTerm t σ (xiSpectralPoint q)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun q => norm_criticalFeatureGaussianAmplifiedTerm_le hσ (abs_xiSpectralPoint_im_lt_half q))
    ((criticalFeatureHermitianEnergy_summable t).mul_left _)

/-- **Cone side.**  If no zero copy lies in the open light cone over `t`, the amplified diagonal is
bounded by the Hermitian feature energy, uniformly in `σ ≥ 0`. -/
theorem norm_criticalFeatureGaussianAmplifiedTrace_le_of_cone {t : ℝ}
    (hcone : ∀ q : XiZeroCopy,
      |(xiSpectralPoint q).im| ≤ |(xiSpectralPoint q).re - t|)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤ criticalFeatureHermitianEnergyTrace t :=
  (norm_tsum_le_tsum_norm (summable_norm_criticalFeatureGaussianAmplifiedTerm t hσ)).trans
    ((summable_norm_criticalFeatureGaussianAmplifiedTerm t hσ).tsum_le_tsum
      (fun q => norm_criticalFeatureGaussianAmplifiedTerm_le_of_cone hσ
        (sq_le_sq.2 (hcone q)))
      (criticalFeatureHermitianEnergy_summable t))

/-- **Off-cone side.**  A zero copy in the open light cone over `t` makes the amplified diagonal
unbounded in `σ`: light-cone amplification of the exponential sum with exponents `(γ - t)²` and
coefficients `(2/(1 + (γ - t)²))²`, which depend only on the exponent. -/
theorem exists_lt_norm_criticalFeatureGaussianAmplifiedTrace {t : ℝ}
    (hoff : ∃ q₀ : XiZeroCopy,
      |(xiSpectralPoint q₀).re - t| < |(xiSpectralPoint q₀).im|) (C : ℝ) :
    ∃ σ : ℝ, 0 ≤ σ ∧ C < ‖criticalFeatureGaussianAmplifiedTrace t σ‖ := by
  have hWre : ∀ q : XiZeroCopy, ((xiSpectralPoint q - t) ^ 2).re =
      ((xiSpectralPoint q).re - t) ^ 2 - (xiSpectralPoint q).im ^ 2 := fun q =>
    re_sub_ofReal_sq _ t
  have hcW : ∀ q : XiZeroCopy, criticalFeatureCauchyKernelTest t (xiSpectralPoint q) ^ 2 =
      (2 / (1 + (xiSpectralPoint q - t) ^ 2)) ^ 2 := fun q => by
    rw [criticalFeatureCauchyKernelTest_eq_div (abs_xiSpectralPoint_im_lt_half q)]
  have hone : ∀ q : XiZeroCopy, 1 + (xiSpectralPoint q - t) ^ 2 ≠ 0 := fun q h => by
    have hre := congrArg Complex.re h
    rw [Complex.add_re, Complex.one_re, hWre, Complex.zero_re] at hre
    have him := abs_xiSpectralPoint_im_lt_half q
    have hy : (xiSpectralPoint q).im ^ 2 < 1 / 4 := by
      have := sq_lt_sq' (abs_lt.1 him).1 (abs_lt.1 him).2
      linarith
    nlinarith [sq_nonneg ((xiSpectralPoint q).re - t)]
  have hfin : {q : XiZeroCopy | ((xiSpectralPoint q - t) ^ 2).re < 0}.Finite := by
    refine (finite_xiSpectralPoint_norm_le (|t| + 1)).subset fun q hq => ?_
    simp only [Set.mem_setOf_eq] at hq ⊢
    have him := abs_xiSpectralPoint_im_lt_half q
    rw [hWre] at hq
    have hy : (xiSpectralPoint q).im ^ 2 < (1 / 2) ^ 2 := by
      have := sq_lt_sq' (abs_lt.1 him).1 (abs_lt.1 him).2
      linarith
    have hre : |(xiSpectralPoint q).re - t| < 1 / 2 := by
      have h1 : ((xiSpectralPoint q).re - t) ^ 2 < (1 / 2) ^ 2 := by linarith
      rw [sq_lt_sq, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1
      exact h1
    have hret : |(xiSpectralPoint q).re| ≤ |t| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub (xiSpectralPoint q).re t
      linarith
    calc ‖xiSpectralPoint q‖
        ≤ |(xiSpectralPoint q).re| + |(xiSpectralPoint q).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ (|t| + 1 / 2) + 1 / 2 := add_le_add hret him.le
      _ = |t| + 1 := by ring
  obtain ⟨q₀, hq₀⟩ := hoff
  exact GaloisForLFunctions.HTGeometry.exists_lt_norm_tsum_mul_exp_neg_of_re_neg le_rfl
    (w := fun q => (xiSpectralPoint q - t) ^ 2)
    (c := fun q => criticalFeatureCauchyKernelTest t (xiSpectralPoint q) ^ 2)
    (fun i j h => by rw [hcW, hcW, h])
    (fun i _ => by
      rw [hcW]
      exact pow_ne_zero _ (div_ne_zero two_ne_zero (hone i)))
    hfin (m := fun q => Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)))
    (fun _ => Complex.normSq_nonneg _) (criticalFeatureHermitianEnergy_summable t)
    (fun q hq σ hσ => norm_criticalFeatureGaussianAmplifiedTerm_le_of_cone hσ
      (by rw [hWre] at hq; linarith))
    (fun σ hσ => summable_norm_criticalFeatureGaussianAmplifiedTerm t hσ)
    ⟨q₀, by rw [hWre]; have := sq_lt_sq.2 hq₀; linarith⟩ C

/-- **Local light-cone law.**  The amplified diagonal at height `t` is bounded in `σ ≥ 0` iff no Xi
zero copy lies in the open light cone `|Re γ - t| < |Im γ|` over `t`. -/
theorem criticalFeatureGaussianAmplifiedTrace_bounded_iff (t : ℝ) :
    (∃ C : ℝ, ∀ σ : ℝ, 0 ≤ σ → ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤ C) ↔
      ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ |(xiSpectralPoint q).re - t| := by
  constructor
  · intro ⟨C, hC⟩ q
    by_contra hcon
    push Not at hcon
    obtain ⟨σ, hσ, hlt⟩ := exists_lt_norm_criticalFeatureGaussianAmplifiedTrace ⟨q, hcon⟩ C
    exact absurd (hC σ hσ) (not_le.2 hlt)
  · intro hcone
    exact ⟨criticalFeatureHermitianEnergyTrace t, fun σ hσ =>
      norm_criticalFeatureGaussianAmplifiedTrace_le_of_cone hcone hσ⟩

/-- **Uniform ceiling under RH.**  Every zero on the line keeps the amplified diagonal below the
Hermitian feature energy for every amplification. -/
theorem norm_criticalFeatureGaussianAmplifiedTrace_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) (t : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤ criticalFeatureHermitianEnergyTrace t :=
  norm_criticalFeatureGaussianAmplifiedTrace_le_of_cone (fun q => by
    rw [xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q, abs_zero]
    exact abs_nonneg _) hσ

/-- **Gaussian-amplified HCF receiver.**  RH holds iff the amplified critical-feature diagonal is
bounded in the amplification at every real height. -/
theorem riemannHypothesis_iff_forall_criticalFeatureGaussianAmplifiedTrace_bounded :
    RiemannHypothesis ↔
      ∀ t : ℝ, ∃ C : ℝ, ∀ σ : ℝ, 0 ≤ σ → ‖criticalFeatureGaussianAmplifiedTrace t σ‖ ≤ C := by
  constructor
  · intro hRH t
    exact ⟨_, fun σ hσ => norm_criticalFeatureGaussianAmplifiedTrace_le_of_riemannHypothesis hRH t hσ⟩
  · intro hbdd
    refine riemannHypothesis_of_xiSpectralPoint_real fun q => ?_
    have hcone := (criticalFeatureGaussianAmplifiedTrace_bounded_iff
      (xiSpectralPoint q).re).1 (hbdd _) q
    rw [sub_self, abs_zero, abs_nonpos_iff] at hcone
    exact ⟨(xiSpectralPoint q).re, Complex.ext (by simp) (by simp [hcone])⟩

end

end RHTower
