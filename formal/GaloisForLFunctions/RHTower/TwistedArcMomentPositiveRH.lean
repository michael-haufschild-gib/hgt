import GaloisForLFunctions.RHTower.ArcGammaMultiplier
import GaloisForLFunctions.RHTower.TwistedArcWitnessFourierDecay
import GaloisForLFunctions.RHTower.DivisorKernelFourierIdentification

/-!
# RH is prime-blind positivity for every moment-positive twisted arc density

Let `ν` be a finite measure on the modular bottom arc `u ∈ [−½, ½]` and `g` a bounded measurable
density such that `g ν` annihilates every twisted integer moment
`M_n(u) = ∫ g_u(x) cos(2π(n+2)x) dx` (`twArcMoment`), whose weighted even moments
`m_j = ∫ g(u) √(y_u/2) u^{2j} dν(u)` (`twArcEvenMoment`) are nonnegative, with some `m_{j₀} > 0`.

**Theorem** (`riemannHypothesis_iff_primeBlindPositive_of_twistedArc_momentPositive`).
Then the Riemann hypothesis is equivalent to prime-blind positivity.

**Proof.**  Put `w_j = 4√2 · 4^j m_j/(2j)!` (`arcGammaWeight`).  These weights are nonnegative,
`w_{j₀} > 0`,
and `Σ w_j (j!)²(9/4)^j < ∞` because `|m_j| ≤ 4^{−j} B ν(arc)`.  By
`riemannHypothesis_iff_primeBlindPositive_of_shiftedGamma_weights_of_pos` it remains to show that
`Σ_j w_j ∫ |Ξ(r) Q_j(r)|² cos(r log n) dr = 0` for every `n ≥ 2`.

* With `R(s) = Σ_j w_j Q_j(z) Q_j(−z)`, `z = −i(s − ½)` (`arcGammaMultiplier`), one has
  `ξ(½+it)² R(½+it) = Σ_j w_j |Ξ(t) Q_j(t)|²`, so the required sum is the real part of
  `∫ ξ(½+it)² R(½+it) n^{−it} dt`.
* On the critical line `|G(½+iτ)|² R(½+iτ) = Σ_j w_j λ_j (¼+τ²)² C_j(τ) = (¼+τ²)² Σ_j 2C(−½,2j) C_j(τ) m_j`,
  which is the cosine transform of the log profile of the witness `h = ∫ g g_u dν`, i.e. `𝓜h(½ − iτ)`
  (`mellin_twWitnessW_criticalLine`).  Hence `G(s)² R(s) = (Γ_ℝ(s)/Γ_ℝ(1−s)) 𝓜h(1−s)` there
  (`archXi_sq_mul_arcGammaMultiplier_criticalLine`).
* `R` is holomorphic with `‖ξ²R‖, ‖G²R‖ ≤ C/(1+(Im s)²)` on `½ ≤ Re s ≤ 5/4` (`ArcGammaMultiplier`),
  `h` is `C²` with integrable Fourier transform (`TwistedArcWitnessFourierDecay`), and
  `𝓕h(N) = ∫ g M_{N−2} dν = 0` for every integer `N ≥ 2` (`fourier_twWitnessW_natCast_eq_zero`).
  The divisor transfer at the abscissa `5/4` with the kernel identification
  (`logNode_blind_of_fourier_vanishes`) gives `∫ ξ(½+it)² R(½+it) n^{−it} dt = 0`.

**Corollary** (`riemannHypothesis_iff_primeBlindPositive_of_twistedArcMinimumPrinciple`).  Under the
twisted minimum principle (no finite combination of the `M_n` is strictly positive on the arc) the
Riemann hypothesis is equivalent to prime-blind positivity.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Nat ComplexConjugate FourierTransform

noncomputable section

namespace RHTower.WeilSpectral

/-- `Q_j` has no real zeros: every factor `k + ¼ + ir/2` has real part `k + ¼ > 0`. -/
theorem shiftedGammaPoly_ofReal_ne_zero (j : ℕ) (r : ℝ) : shiftedGammaPoly j r ≠ 0 := by
  unfold shiftedGammaPoly
  rw [Finset.prod_ne_zero_iff]
  intro k _ h
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- Every `F̂_j = Ξ Q_j` vanishes on the real line only at critical ordinates. -/
theorem riemannZeta_eq_zero_of_paperFT_xiShiftedGammaTest_zero_of (j : ℕ) {r : ℝ}
    (hr : Zeta23.paperFT (fun u => (xiShiftedGammaTest j u : ℂ)) r = 0) :
    riemannZeta ((1 / 2 : ℂ) + r * I) = 0 := by
  rw [paperFT_xiShiftedGammaTest j (by simp)] at hr
  have hX : RHTower.XiC r = 0 :=
    (mul_eq_zero.mp hr).resolve_right (shiftedGammaPoly_ofReal_ne_zero j r)
  have hre : 0 < ((1 / 2 : ℂ) + r * I).re := by simp
  have hne : (1 / 2 : ℂ) + r * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  exact (RHTower.xi_eq_zero_iff hre hne).mp hX

/-- **The shifted-Gamma (N1) criterion with any positive weight.**  As
`riemannHypothesis_iff_primeBlindPositive_of_shiftedGamma_weights`, with `w_0 > 0` replaced by
`w_{j₀} > 0` for some `j₀`. -/
theorem riemannHypothesis_iff_primeBlindPositive_of_shiftedGamma_weights_of_pos {w : ℕ → ℝ}
    (hw : ∀ j, 0 ≤ w j) {j₀ : ℕ} (hj₀ : 0 < w j₀)
    (hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2)
    (hblind : ∀ n : ℕ, 2 ≤ n →
      ∑' j, w j * ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n) = 0) :
    RiemannHypothesis ↔ WeilOneSided.PrimeBlindPositive := by
  obtain ⟨C, hC, hF⟩ := exists_decayBound_xiShiftedGammaTest
  refine riemannHypothesis_iff_primeBlindPositive_of_xiDivisibleBlindFamily
    (by norm_num : (0 : ℝ) < 1 / 4) hF hw ?_ (fun j ρ => paperFT_xiShiftedGammaTest_gammaOf j ρ) ?_
    hj₀ (fun r hr => riemannZeta_eq_zero_of_paperFT_xiShiftedGammaTest_zero_of j₀ hr)
  · refine (hsum.mul_left (C ^ 2)).congr fun j => ?_
    ring
  · intro n hn
    simp_rw [crossCorr_xiShiftedGammaTest]
    have e : ∀ j, w j * (1 / (2 * Real.pi) *
        ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) =
        1 / (2 * Real.pi) * (w j *
          ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) := fun j => by ring
    simp_rw [e]
    rw [tsum_mul_left, hblind n hn, mul_zero]

section Arc

variable {ν : Measure ArcParam} [IsFiniteMeasure ν] {g : ArcParam → ℝ} {B : ℝ}

/-- The weighted even moments `m_j = ∫ g(u) √(y_u/2) u^{2j} dν(u)`. -/
def twArcEvenMoment (ν : Measure ArcParam) (g : ArcParam → ℝ) (j : ℕ) : ℝ :=
  ∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν

theorem sqrt_modularArcHeight_half_le_one (u : ArcParam) :
    Real.sqrt (modularArcHeight u / 2) ≤ 1 := by
  rw [Real.sqrt_le_one]
  have := modularArcHeight_le_one u
  linarith

theorem twArcEvenMoment_le (hgB : ∀ u, |g u| ≤ B) (j : ℕ) :
    twArcEvenMoment ν g j ≤ B * ν.real univ * (1 / 4 : ℝ) ^ j := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  unfold twArcEvenMoment
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := B * (1 / 4 : ℝ) ^ j)
    (Eventually.of_forall fun u => ?_)).trans (le_of_eq (by ring))
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hu : (u : ℝ) ^ (2 * j) ≤ (1 / 4 : ℝ) ^ j := by
    rw [pow_mul]
    refine pow_le_pow_left₀ (sq_nonneg _) ?_ j
    have := abs_arcParam_le u
    rw [← sq_abs]; nlinarith [abs_nonneg (u : ℝ)]
  have hu0 : 0 ≤ (u : ℝ) ^ (2 * j) := by rw [pow_mul]; positivity
  rw [abs_of_nonneg hu0]
  calc |g u| * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ≤
      B * (1 * (1 / 4 : ℝ) ^ j) :=
        mul_le_mul (hgB u) (mul_le_mul (sqrt_modularArcHeight_half_le_one u) hu hu0 zero_le_one)
          (by positivity) hB0
    _ = _ := by ring

/-! ### The log profile of the witness -/

omit [IsFiniteMeasure ν] in
theorem twWitnessW_exp_neg (v : ℝ) :
    twWitnessW ν g (Real.exp (-v)) = Real.exp v * twWitnessW ν g (Real.exp v) := by
  have h := twWitnessW_inv (ν := ν) (g := g) (x := Real.exp v) (Real.exp_pos v).ne'
  rw [one_div, ← Real.exp_neg, abs_of_pos (Real.exp_pos v)] at h
  exact h

omit [IsFiniteMeasure ν] in
theorem exp_half_mul_twWitnessW_neg (v : ℝ) :
    Real.exp (-v / 2) * twWitnessW ν g (Real.exp (-v)) =
      Real.exp (v / 2) * twWitnessW ν g (Real.exp v) := by
  rw [twWitnessW_exp_neg, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem abs_exp_half_mul_twWitnessW_le (hgB : ∀ u, |g u| ≤ B) (v : ℝ) :
    |Real.exp (v / 2) * twWitnessW ν g (Real.exp v)| ≤
      B * ν.real univ * 9000 * Real.exp (-(3 * |v| / 2)) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  unfold twWitnessW
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := B * (9000 * Real.exp (-(3 * |v| / 2))))
    (Eventually.of_forall fun u => ?_)).trans (le_of_eq (by ring))
  rw [Real.norm_eq_abs, show Real.exp (v / 2) * (g u * twArcVector u (Real.exp v)) =
    g u * (Real.exp (v / 2) * twArcVector u (Real.exp v)) by ring, abs_mul]
  exact mul_le_mul (hgB u) (abs_exp_half_mul_twArcVector_le u v) (abs_nonneg _) hB0

theorem continuous_exp_half_mul_twWitnessW (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    Continuous fun v : ℝ => Real.exp (v / 2) * twWitnessW ν g (Real.exp v) :=
  (by fun_prop : Continuous fun v : ℝ => Real.exp (v / 2)).mul
    ((continuous_twWitnessW hg hgB).comp Real.continuous_exp)

/-- `𝓜h(½ − iτ) = ∫ cos(τv) e^{v/2} h(e^v) dv` for the weighted witness `h`. -/
theorem mellin_twWitnessW_criticalLine (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) (τ : ℝ) :
    mellin (fun x => (twWitnessW ν g x : ℂ)) (1 - (1 / 2 + (τ : ℂ) * I)) =
      ((∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * twWitnessW ν g (Real.exp v)) : ℝ) : ℂ) := by
  set P : ℝ → ℝ := fun v => Real.exp (v / 2) * twWitnessW ν g (Real.exp v) with hP
  have hPeven : ∀ v, P (-v) = P v := fun v => by
    simp only [hP]; rw [show -v / 2 = -v / 2 from rfl]; exact exp_half_mul_twWitnessW_neg v
  have hPc : Continuous P := continuous_exp_half_mul_twWitnessW hg hgB
  have hPi : Integrable P := by
    refine ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 3 / 2)).const_mul
      (B * ν.real univ * 9000)).mono' hPc.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_exp_half_mul_twWitnessW_le hgB v).trans (le_of_eq ?_)
    ring_nf
  rw [mellin_eq_fourier, Real.fourier_eq]
  have hre : (1 - (1 / 2 + (τ : ℂ) * I)).re = 1 / 2 := by simp; norm_num
  have him : (1 - (1 / 2 + (τ : ℂ) * I)).im = -τ := by simp
  rw [hre, him]
  set F : ℝ → ℂ := fun u => Complex.exp (((τ * u : ℝ) : ℂ) * I) * (P u : ℂ) with hF
  have e1 : (fun u : ℝ => 𝐞 (-(inner ℝ u (-τ / (2 * Real.pi)))) •
      (Real.exp (-(1 / 2) * u) • (twWitnessW ν g (Real.exp (-u)) : ℂ))) = F := by
    funext u
    simp only [hF, hP]
    rw [show (Real.exp (-(1 / 2) * u) • (twWitnessW ν g (Real.exp (-u)) : ℂ)) =
      ((Real.exp (-u / 2) * twWitnessW ν g (Real.exp (-u)) : ℝ) : ℂ) by
        rw [Complex.real_smul]; push_cast; ring_nf,
      exp_half_mul_twWitnessW_neg, Circle.smul_def, Real.fourierChar_apply, RCLike.inner_apply,
      conj_trivial, smul_eq_mul]
    congr 2
    push_cast
    field_simp
  rw [e1]
  have hFi : Integrable F := by
    refine hPi.abs.mono' (by
      simp only [hF]
      exact ((by fun_prop : Continuous fun u : ℝ => Complex.exp (((τ * u : ℝ) : ℂ) * I)).mul
        (Complex.continuous_ofReal.comp hPc)).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    simp only [hF, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact le_rfl
  have hreF : ∀ u, (F u).re = Real.cos (τ * u) * P u := fun u => by
    simp only [hF]
    rw [Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
  have himF : ∀ u, (F u).im = Real.sin (τ * u) * P u := fun u => by
    simp only [hF]
    rw [Complex.im_mul_ofReal, Complex.exp_ofReal_mul_I_im]
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re, ← integral_re hFi]
    simp only [RCLike.re_eq_complex_re, hreF, Complex.ofReal_re, hP]
  · rw [← RCLike.im_eq_complex_im, ← integral_im hFi]
    simp only [RCLike.im_eq_complex_im, himF, Complex.ofReal_im]
    have hodd := integral_neg_eq_self (fun u : ℝ => Real.sin (τ * u) * P u) volume
    have e2 : (fun u : ℝ => Real.sin (τ * -u) * P (-u)) = fun u => -(Real.sin (τ * u) * P u) := by
      funext u; rw [mul_neg, Real.sin_neg, hPeven]; ring
    rw [e2, integral_neg] at hodd
    linarith

omit [IsFiniteMeasure ν] in
/-- The Fourier transform of an integrable continuous even real function is its cosine transform. -/
theorem fourier_ofReal_eq_cos_of_even {f : ℝ → ℝ} (hf : Integrable f) (hc : Continuous f)
    (heven : ∀ x, f (-x) = f x) (w : ℝ) :
    𝓕 (fun x => (f x : ℂ)) w = ((∫ x, f x * Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set F : ℝ → ℂ := fun v => Complex.exp (((-2 * Real.pi * v * w : ℝ) : ℂ) * I) • (f v : ℂ) with hF
  change ∫ v, F v = _
  have hFi : Integrable F := by
    refine hf.abs.mono' (by
      simp only [hF]
      exact ((by fun_prop : Continuous fun v : ℝ =>
        Complex.exp (((-2 * Real.pi * v * w : ℝ) : ℂ) * I)).smul
          (Complex.continuous_ofReal.comp hc)).aestronglyMeasurable)
      (Eventually.of_forall fun v => ?_)
    simp only [hF, smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact le_rfl
  have hreF : ∀ v, (F v).re = f v * Real.cos (2 * Real.pi * w * v) := fun v => by
    simp only [hF, smul_eq_mul]
    rw [Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re,
      show -2 * Real.pi * v * w = -(2 * Real.pi * w * v) by ring, Real.cos_neg, mul_comm]
  have himF : ∀ v, (F v).im = -(f v * Real.sin (2 * Real.pi * w * v)) := fun v => by
    simp only [hF, smul_eq_mul]
    rw [Complex.im_mul_ofReal, Complex.exp_ofReal_mul_I_im,
      show -2 * Real.pi * v * w = -(2 * Real.pi * w * v) by ring, Real.sin_neg]
    ring
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re, ← integral_re hFi]
    simp only [RCLike.re_eq_complex_re, hreF, Complex.ofReal_re]
  · rw [← RCLike.im_eq_complex_im, ← integral_im hFi]
    simp only [RCLike.im_eq_complex_im, himF, Complex.ofReal_im, integral_neg, neg_eq_zero]
    have hodd := integral_neg_eq_self (fun v : ℝ => f v * Real.sin (2 * Real.pi * w * v)) volume
    have e2 : (fun v : ℝ => f (-v) * Real.sin (2 * Real.pi * w * -v)) =
        fun v => -(f v * Real.sin (2 * Real.pi * w * v)) := by
      funext v; rw [mul_neg, Real.sin_neg, heven]; ring
    rw [e2, integral_neg] at hodd
    linarith

/-- `𝓕h(N) = ∫ g M_{N−2} dν = 0` at every integer `N ≥ 2` for a blind density `g`. -/
theorem fourier_twWitnessW_natCast_eq_zero (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B)
    (hblind : ∀ n : ℕ, ∫ u, g u * twArcMoment n u ∂ν = 0) {N : ℕ} (hN : 2 ≤ N) :
    𝓕 (fun x => (twWitnessW ν g x : ℂ)) N = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hN
  rw [fourier_ofReal_eq_cos_of_even (integrable_of_le_inv_one_add_sq (continuous_twWitnessW hg hgB)
    (abs_twWitnessW_le hgB)) (continuous_twWitnessW hg hgB) twWitnessW_neg, Complex.ofReal_eq_zero]
  have hω : 2 * Real.pi * ((n + 2 : ℕ) : ℝ) = arcFreq (n + 1) := by unfold arcFreq; push_cast; ring
  have e : ∀ x, twWitnessW ν g x * Real.cos (2 * Real.pi * ((n + 2 : ℕ) : ℝ) * x) =
      ∫ u, g u * (twArcVector u x * Real.cos (arcFreq (n + 1) * x)) ∂ν := fun x => by
    unfold twWitnessW; rw [hω, ← integral_mul_const]; congr 1; funext u; ring
  simp_rw [e]
  rw [integral_integral_swap (integrable_prod_g_mul (ν := ν) hg hgB
    (F := fun x u => twArcVector u x * Real.cos (arcFreq (n + 1) * x))
    (continuous_twArcVector_param.mul (by fun_prop)) (fun x u => abs_twArcVector_mul_cos_le _ u x))]
  simp_rw [integral_const_mul]
  exact hblind n

/-- On the critical line `G(s)² R(s) = (Γ_ℝ(s)/Γ_ℝ(1−s)) 𝓜h(1−s)` for the arc-moment weights
`w_j = 4√2 · 4^j m_j/(2j)!`: both sides reduce to `(Γ_ℝ(s)/Γ_ℝ(1−s)) (¼+τ²)² Σ_j 2C(−½,2j) C_j(τ) m_j`. -/
theorem archXi_sq_mul_arcGammaMultiplier_criticalLine (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B)
    {s : ℂ} (hs : s.re = 1 / 2) :
    ExactNullDivisorTransfer.archXi s ^ 2 *
        arcGammaMultiplier (fun j => arcGammaWeight (twArcEvenMoment ν g j) j) s =
      Gammaℝ s / Gammaℝ (1 - s) * mellin (fun x => (twWitnessW ν g x : ℂ)) (1 - s) := by
  obtain ⟨τ, rfl⟩ : ∃ τ : ℝ, s = 1 / 2 + (τ : ℂ) * I :=
    ⟨s.im, Complex.ext (by simp [hs]) (by simp)⟩
  set s : ℂ := 1 / 2 + (τ : ℂ) * I with hsdef
  set A := ExactNullDivisorTransfer.archXi s
  have hconj : conj s = 1 - s := Complex.ext (by simp [hsdef]; norm_num) (by simp [hsdef])
  have hG1 : Gammaℝ (1 - s) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp [hsdef]; norm_num)
  have hA : A = Gammaℝ s / Gammaℝ (1 - s) * conj A := by
    simp only [A, ExactNullDivisorTransfer.archXi]
    rw [map_mul, map_div₀, map_mul, map_sub, map_one, ← RHTower.Gammaℝ_conj, hconj,
      show conj (2 : ℂ) = 2 from Complex.conj_ofNat 2]
    field_simp
    ring
  have hsq : A ^ 2 = Gammaℝ s / Gammaℝ (1 - s) * ((‖A‖ ^ 2 : ℝ) : ℂ) := by
    rw [sq, Complex.ofReal_pow, ← mul_conj', ← mul_assoc,
      mul_comm (Gammaℝ s / Gammaℝ (1 - s)) A, mul_assoc, ← hA]
  rw [hsq, mul_assoc]
  congr 1
  rw [hsdef, arcGammaMultiplier_criticalLine, mellin_twWitnessW_criticalLine hg hgB,
    integral_cos_mul_twWitnessWProfile_eq hg hgB, ← Complex.ofReal_tsum, ← Complex.ofReal_mul]
  congr 1
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  have h1 := norm_archXi_sq_mul_norm_shiftedGammaPoly_sq j τ
  have h2 := arcGammaWeight_mul_lambda (twArcEvenMoment ν g j) j
  unfold twArcEvenMoment at h2
  calc ‖A‖ ^ 2 * (arcGammaWeight (twArcEvenMoment ν g j) j * ‖shiftedGammaPoly j τ‖ ^ 2)
      = arcGammaWeight (twArcEvenMoment ν g j) j * (‖A‖ ^ 2 * ‖shiftedGammaPoly j τ‖ ^ 2) := by ring
    _ = (arcGammaWeight (twArcEvenMoment ν g j) j * (Real.pi ^ (-(1 / 2 : ℝ)) *
          Real.Gamma (1 / 2 + 2 * j) / (4 * (2 : ℝ) ^ ((1 / 2 + 2 * j : ℝ) - 1)))) *
          ((1 / 4 + τ ^ 2) ^ 2 * coshPowerTransform j τ) := by rw [h1]; ring
    _ = _ := by unfold twArcEvenMoment; rw [h2]; ring

omit [IsFiniteMeasure ν] in
/-- `‖f t‖ t^{−½}` is integrable on `(0, ∞)` when `‖f t‖ ≤ K (1+t²)⁻¹`. -/
theorem integrableOn_norm_mul_rpow_neg_half {f : ℝ → ℂ} (hf : Continuous f) {K : ℝ}
    (hK : ∀ t, ‖f t‖ ≤ K * (1 + t ^ 2)⁻¹) :
    IntegrableOn (fun t : ℝ => ‖f t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0) := by
  have hK0 : 0 ≤ K := by have := (norm_nonneg _).trans (hK 0); simpa using this
  have hcont : ContinuousOn (fun t : ℝ => ‖f t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0) :=
    hf.norm.continuousOn.mul fun t ht =>
      (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))).continuousWithinAt
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun t : ℝ => K * t ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num))).const_mul K
    refine h1.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hr : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.1.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hr)]
    refine mul_le_mul_of_nonneg_right ((hK t).trans ?_) hr
    exact mul_le_of_le_one_right hK0 (inv_le_one_of_one_le₀ (by nlinarith))
  · have h1 : IntegrableOn (fun t : ℝ => K * t ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul K
    refine h1.mono' ((hcont.mono fun t (ht : 1 < t) => (zero_lt_one.trans ht : 0 < t)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 1 < t)
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hr : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0.le _
    have hr1 : t ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht.le (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hr)]
    have h2 : (1 + t ^ 2)⁻¹ ≤ t ^ (-2 : ℝ) := by
      rw [Real.rpow_neg ht0.le, Real.rpow_two]
      exact inv_anti₀ (by positivity) (by linarith)
    calc ‖f t‖ * t ^ (-(1 / 2 : ℝ)) ≤ ‖f t‖ * 1 := mul_le_mul_of_nonneg_left hr1 (norm_nonneg _)
      _ ≤ K * t ^ (-2 : ℝ) := by rw [mul_one]; exact (hK t).trans (mul_le_mul_of_nonneg_left h2 hK0)


/-- **The arc Gamma weights of a moment-positive twisted-blind arc density are jointly blind.**
For a bounded measurable `g` annihilating every twisted integer moment with nonnegative weighted
even moments, the weights `w_j = arcGammaWeight m_j j` satisfy
`Σ_j w_j ∫ |Ξ(r) Q_j(r)|² cos(r log n) dr = 0` for every `n ≥ 2`. -/
theorem shiftedGamma_blind_of_twistedArc (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B)
    (hblind : ∀ n : ℕ, ∫ u, g u * twArcMoment n u ∂ν = 0)
    (hmom : ∀ j, 0 ≤ twArcEvenMoment ν g j) :
    ∀ n : ℕ, 2 ≤ n → ∑' j, arcGammaWeight (twArcEvenMoment ν g j) j *
      ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n) = 0 := by
  set w : ℕ → ℝ := fun j => arcGammaWeight (twArcEvenMoment ν g j) j with hw_def
  have hw : ∀ j, 0 ≤ w j := fun j => arcGammaWeight_nonneg (hmom j) j
  have hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2 :=
    summable_arcGammaWeight hmom (twArcEvenMoment_le hgB)
  intro n hn
  have hc0 := continuous_twWitnessW (ν := ν) hg hgB
  have hi : Integrable fun x => (twWitnessW ν g x : ℂ) :=
    (integrable_of_le_inv_one_add_sq hc0 (abs_twWitnessW_le hgB)).ofReal
  have hFc : Continuous (𝓕 fun x => (twWitnessW ν g x : ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  obtain ⟨C, hC⟩ := exists_norm_xi_sq_mul_arcGammaMultiplier_le hw hsum
  obtain ⟨C', hC'⟩ := exists_norm_archXi_sq_mul_arcGammaMultiplier_le hw hsum
  have hI := logNode_blind_of_fourier_vanishes hi (integrable_fourier_twWitnessW hg hgB)
    (fun t => by simp only [twWitnessW_neg])
    (integrableOn_norm_mul_rpow_neg_half (f := fun x => (twWitnessW ν g x : ℂ))
      (Complex.continuous_ofReal.comp hc0) (K := B * ν.real univ * 9000) fun t => by
        simp only [Complex.norm_real, Real.norm_eq_abs]; exact abs_twWitnessW_le hgB t)
    (integrableOn_norm_mul_rpow_neg_half hFc (norm_fourier_twWitnessW_le hg hgB)) hFc
    (c := 5 / 4) (by norm_num)
    (fun s hs1 hs2 => differentiableAt_arcGammaMultiplier hw hsum
      (by rw [abs_lt]; constructor <;> linarith))
    hC hC' (fun s hs => archXi_sq_mul_arcGammaMultiplier_criticalLine hg hgB hs)
    (fun N hN => fourier_twWitnessW_natCast_eq_zero hg hgB hblind hN) n hn
  obtain ⟨K, hK0, hK⟩ := exists_stripDecay_xiShiftedGamma
  set ε := xiShiftedGammaRate
  have hε : 0 < ε := xiShiftedGammaRate_pos
  have he1 : ∀ t : ℝ, Real.exp (-(ε * |t|)) ≤ 1 := fun t =>
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hε.le (abs_nonneg t)))
  have hΦc : ∀ j, Continuous fun t : ℝ => xiShiftedGamma j t := fun j =>
    continuous_iff_continuousAt.mpr fun t =>
      ((hK j).diff (t : ℂ) (by norm_num)).continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hterm : ∀ j (t : ℝ), w j * ‖xiShiftedGamma j t‖ ^ 2 ≤
      K ^ 2 * (w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) * Real.exp (-(ε * |t|)) := fun j t => by
    have hΦ : ‖xiShiftedGamma j t‖ ≤ K * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) * Real.exp (-(ε * |t|)) := by
      simpa using (hK j).bound (t : ℂ) (by norm_num)
    have hsq : ‖xiShiftedGamma j t‖ ^ 2 ≤
        (K * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j)) ^ 2 * Real.exp (-(ε * |t|)) := by
      calc ‖xiShiftedGamma j t‖ ^ 2 ≤ (K * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) * Real.exp (-(ε * |t|))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hΦ 2
        _ = (K * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j)) ^ 2 * Real.exp (-(ε * |t|)) *
            Real.exp (-(ε * |t|)) := by ring
        _ ≤ (K * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j)) ^ 2 * Real.exp (-(ε * |t|)) * 1 :=
            mul_le_mul_of_nonneg_left (he1 t) (by positivity)
        _ = _ := mul_one _
    calc w j * ‖xiShiftedGamma j t‖ ^ 2 ≤
        w j * ((K * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j)) ^ 2 * Real.exp (-(ε * |t|))) :=
          mul_le_mul_of_nonneg_left hsq (hw j)
      _ = _ := by ring
  have hc0j : ∀ j, 0 ≤ K ^ 2 * (w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) := fun j =>
    mul_nonneg (sq_nonneg K) (mul_nonneg (hw j) (sq_nonneg _))
  have hSsum : Summable fun j => K ^ 2 * (w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) :=
    hsum.mul_left _
  set S : ℝ → ℝ := fun t => ∑' j, w j * ‖xiShiftedGamma j t‖ ^ 2 with hS
  have hScont : Continuous S :=
    continuous_tsum (fun j => continuous_const.mul ((hΦc j).norm.pow 2)) hSsum fun j t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw j) (sq_nonneg _))]
      exact (hterm j t).trans (mul_le_of_le_one_right (hc0j j) (he1 t))
  have hxR : ∀ t : ℝ, RHTower.xi (1 / 2 + (t : ℂ) * I) ^ 2 * arcGammaMultiplier w (1 / 2 + (t : ℂ) * I) =
      (S t : ℂ) := fun t => by
    rw [xi_sq_mul_arcGammaMultiplier]
    simp only [hS]
    rw [Complex.ofReal_tsum]
    have e1 : -I * (1 / 2 + (t : ℂ) * I - 1 / 2) = (t : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
    have e2 : I * (1 / 2 + (t : ℂ) * I - 1 / 2) = -(t : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
    rw [e1, e2]
    refine tsum_congr fun j => ?_
    rw [xiShiftedGamma_neg_ofReal, mul_conj']
    push_cast
    ring
  have hcp : ∀ t : ℝ, (n : ℂ) ^ (-((t : ℂ) * I)) =
      Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * I) := fun t => by
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.ofReal_natCast,
      ← Complex.ofReal_log (Nat.cast_nonneg n)]
    congr 1
    push_cast
    ring
  have hI' : ∫ t : ℝ, (S t : ℂ) * Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * I) = 0 := by
    refine Eq.trans ?_ hI
    congr 1
    funext t
    rw [hxR, hcp]
  have hGi : Integrable fun t : ℝ => (S t : ℂ) * Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * I) := by
    refine (_root_.integrable_inv_one_add_sq.const_mul C).mono'
      ((Complex.continuous_ofReal.comp hScont).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, ← hxR, ← div_eq_mul_inv]
    simpa using hC (1 / 2 + (t : ℂ) * I) (by simp) (by norm_num)
  have hre : ∫ t : ℝ, S t * Real.cos (t * Real.log n) = 0 := by
    have h0 := congrArg Complex.re hI'
    rw [Complex.zero_re, ← RCLike.re_eq_complex_re, ← integral_re hGi] at h0
    refine Eq.trans ?_ h0
    congr 1
    funext t
    simp only [RCLike.re_eq_complex_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
      Real.cos_neg]
  set F : ℕ → ℝ → ℝ := fun j t => w j * (‖xiShiftedGamma j t‖ ^ 2 * Real.cos (t * Real.log n))
    with hFdef
  have hFb : ∀ j t, ‖F j t‖ ≤ K ^ 2 * (w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) *
      Real.exp (-(ε * |t|)) := fun j t => by
    simp only [hFdef, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (hw j), abs_of_nonneg (sq_nonneg _)]
    calc w j * (‖xiShiftedGamma j t‖ ^ 2 * |Real.cos (t * Real.log n)|) ≤
        w j * (‖xiShiftedGamma j t‖ ^ 2 * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (sq_nonneg _)) (hw j)
      _ ≤ _ := by rw [mul_one]; exact hterm j t
  have hFint : ∀ j, Integrable (F j) := fun j =>
    ((integrable_rexp_neg_mul_abs hε).const_mul _).mono'
      (continuous_const.mul (((hΦc j).norm.pow 2).mul (by fun_prop))).aestronglyMeasurable
      (Eventually.of_forall fun t => hFb j t)
  have hFsum : Summable fun j => ∫ t, ‖F j t‖ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun t => norm_nonneg _) (fun j => ?_)
      (hSsum.mul_right (∫ t, Real.exp (-(ε * |t|))))
    rw [← integral_const_mul]
    exact integral_mono (hFint j).norm ((integrable_rexp_neg_mul_abs hε).const_mul _) (hFb j)
  have hSF : ∀ t, ∑' j, F j t = S t * Real.cos (t * Real.log n) := fun t => by
    simp only [hFdef, hS]
    rw [← tsum_mul_right]
    exact tsum_congr fun j => by ring
  calc ∑' j, w j * ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n) =
      ∑' j, ∫ t, F j t := tsum_congr fun j => by simp only [hFdef]; rw [integral_const_mul]
    _ = ∫ t, ∑' j, F j t := integral_tsum_of_summable_integral_norm hFint hFsum
    _ = ∫ t, S t * Real.cos (t * Real.log n) := by simp_rw [hSF]
    _ = 0 := hre

/-- **RH is prime-blind positivity for every moment-positive twisted arc density.**  If the bounded
measurable density `g` on the modular bottom arc annihilates every twisted integer moment
`M_n = ∫ g_u(x) cos(2π(n+2)x) dx`, its weighted even moments `m_j = ∫ g(u) √(y_u/2) u^{2j} dν(u)` are
nonnegative and some `m_{j₀}` is positive, then the Riemann hypothesis is equivalent to prime-blind
positivity. -/
theorem riemannHypothesis_iff_primeBlindPositive_of_twistedArc_momentPositive
    (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B)
    (hblind : ∀ n : ℕ, ∫ u, g u * twArcMoment n u ∂ν = 0)
    (hmom : ∀ j, 0 ≤ twArcEvenMoment ν g j) (hmass : ∃ j₀, 0 < twArcEvenMoment ν g j₀) :
    RiemannHypothesis ↔ WeilOneSided.PrimeBlindPositive := by
  set w : ℕ → ℝ := fun j => arcGammaWeight (twArcEvenMoment ν g j) j with hw_def
  have hw : ∀ j, 0 ≤ w j := fun j => arcGammaWeight_nonneg (hmom j) j
  obtain ⟨j₀, hj₀⟩ := hmass
  have hw0 : 0 < w j₀ := by
    simp only [hw_def, arcGammaWeight]
    exact div_pos (mul_pos (by positivity) hj₀) (by exact_mod_cast Nat.factorial_pos _)
  have hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2 :=
    summable_arcGammaWeight hmom (twArcEvenMoment_le hgB)
  exact riemannHypothesis_iff_primeBlindPositive_of_shiftedGamma_weights_of_pos hw hw0 hsum
    (shiftedGamma_blind_of_twistedArc hg hgB hblind hmom)

/-- **RH is prime-blind positivity under the twisted minimum principle.**  If no finite combination of
the twisted moments `M_n` is strictly positive on the whole arc, a probability measure annihilating
every `M_n` exists, and its constant density is moment-positive. -/
theorem riemannHypothesis_iff_primeBlindPositive_of_twistedArcMinimumPrinciple
    (hM : TwistedArcMinimumPrinciple) : RiemannHypothesis ↔ WeilOneSided.PrimeBlindPositive := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_twArc_annihilating hM
  have hc : Continuous fun u : ArcParam => Real.sqrt (modularArcHeight u / 2) :=
    (continuous_modularArcHeight_param.div_const 2).sqrt
  refine riemannHypothesis_iff_primeBlindPositive_of_twistedArc_momentPositive
    (ν := (μ : Measure ArcParam)) (g := fun _ => 1) (B := 1) measurable_const
    (fun _ => by norm_num) (fun n => by simpa using hμ n) (fun j => ?_) ?_
  · unfold twArcEvenMoment
    refine integral_nonneg fun u => mul_nonneg zero_le_one
      (mul_nonneg (Real.sqrt_nonneg _) ?_)
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  · refine ⟨0, ?_⟩
    unfold twArcEvenMoment
    simp only [one_mul, mul_zero, pow_zero, mul_one]
    have hi : Integrable (fun u : ArcParam => Real.sqrt (modularArcHeight u / 2))
        (μ : Measure ArcParam) :=
      (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable (Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact sqrt_modularArcHeight_half_le_one u)
    have hle := integral_mono (integrable_const (1 / 2 : ℝ)) hi fun u =>
      Real.le_sqrt_of_sq_le (by linarith [modularArcHeight_ge_half u] : (1 / 2 : ℝ) ^ 2 ≤ _)
    simp only [integral_const, probReal_univ, one_smul] at hle
    linarith

end Arc

end RHTower.WeilSpectral
