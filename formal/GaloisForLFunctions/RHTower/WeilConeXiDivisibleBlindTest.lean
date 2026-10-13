import GaloisForLFunctions.RHTower.WeilConeCriticalZeroCarriedRigidity
import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSummatory
import GaloisForLFunctions.RHTower.PrimeMassSharpUpper
import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# A prime-blind test divisible by `Ξ` forces every Weil-positive system to be `Λ`

Let `F : ℝ → ℝ` be `C²` with `|F|, |F'| ≤ C e^{−(1/2+δ)|x|}` for some `δ > 0` (`ExpDecayTest`), and
suppose:

* its autocorrelation is prime-blind: `(F ⋆ F̃)(log n) = 0` for every `n ≥ 2`;
* its Fourier transform `F̂(z) = ∫ F(u) e^{izu} du` vanishes at the spectral coordinate
  `γ_ρ = −i(ρ − ½)` of every nontrivial zero `ρ` of `ζ`, on or off the critical line;
* `F̂(r) ≠ 0` at every real `r` with `ζ(½ + ir) ≠ 0`.

**Theorem** (`eq_vonMangoldt_of_xiDivisibleBlindTest`).  Then every full-cone Weil-positive
system `lam` equals `Λ` on `n ≥ 2`.  With prime-blind positivity, i.e. a nonempty Weil cone, the
Riemann hypothesis follows (`riemannHypothesis_of_primeBlindPositive_of_xiDivisibleBlindTest`), and
RH is equivalent to prime-blind positivity
(`riemannHypothesis_iff_primeBlindPositive_of_xiDivisibleBlindTest`).

Such an `F` is the (N1) object of route HF: `F̂ = Ξ·g` with `g` zero-free on `ℝ`, so
`|F̂|² = Ξ² R` with `R = |g|² > 0` a prime-blind radical multiplier.  The theorem formalizes
the reduction "RH ⟸ PBAP + (N1)" for multipliers analytic in a strip of half-width above `½`,
the strip on which the explicit formula is evaluated.

**Proof.**  Truncate, `F_L = F χ_L`.  For the compactly supported `F_L` the corpus identity reads
`∫ |F̂_L|² dμ_lam = Re W_ζ(F_L, F_L) − T_{lam−Λ}(F_L ⋆ F̃_L)`.
* *Zero side.*  On `|Im z| ≤ ½`, `(1 + |Re z|)|F̂_L(z) − F̂(z)| ≤ η(L)`, a tail integral of
  `(|F| + |F'|)e^{|u|/2}` beyond `L − 1` (`one_add_abs_re_mul_norm_paperFT_truncTest_sub_le`).
  Since `F̂` vanishes at the zeros, `‖W_ζ(F_L, F_L)‖ ≤ (5/4) S η(L)² → 0`.
* *Prime side.*  The partial sums of `lam − Λ` are `O(N)`: the corpus gives
  `Σ_{n≤N} lam(n) = N + O(N^{1/2+ε})`, and Chebyshev gives `ψ(N) ≤ 7N`.  Summation by parts
  moves the weights onto these partial sums.  The profile `ψ_L(n) = 2(F_L ⋆ F̃_L)(log n)/√n` has
  increments `O(n^{−2−δ/2})` uniformly in `L`, by the mean value theorem inside the
  autocorrelation.  Tannery's theorem and blindness give `T(F_L ⋆ F̃_L) → 0`.
* *Fatou.*  `∫ |F̂|² dμ_lam = 0`, so `μ_lam` is carried by the critical zeros of `ζ`, and the
  critical-zero rigidity `eq_vonMangoldt_of_boundaryMeasure_criticalZeros` gives `lam = Λ`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate ENNReal NNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

/-- A `C²` real test which, with its derivative, decays like `e^{−(1/2+δ)|x|}`. -/
def ExpDecayTest (F : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 F ∧ ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ x : ℝ,
    |F x| ≤ C * Real.exp (-((1 / 2 + δ) * |x|)) ∧
      |deriv F x| ≤ C * Real.exp (-((1 / 2 + δ) * |x|))

/-- The truncation `F χ_L`. -/
def truncTest (F : ℝ → ℝ) (L u : ℝ) : ℝ := F u * bulkCutoff L u

/-! ### The truncation -/

theorem contDiff_truncTest {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L : ℝ) :
    ContDiff ℝ 2 (truncTest F L) :=
  hF.mul (contDiff_bulkCutoff L)

theorem contDiff_ofReal_truncTest {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L : ℝ) :
    ContDiff ℝ 2 fun u => (truncTest F L u : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_truncTest hF L)

theorem truncTest_eq_zero {F : ℝ → ℝ} {L u : ℝ} (h : L ≤ |u|) : truncTest F L u = 0 := by
  simp [truncTest, bulkCutoff_eq_zero h]

theorem hasCompactSupport_truncTest (F : ℝ → ℝ) (L : ℝ) : HasCompactSupport (truncTest F L) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L)) fun u hu => ?_
  apply truncTest_eq_zero
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with h | h
  · linarith [neg_le_abs u]
  · linarith [le_abs_self u]

theorem abs_truncTest_le (F : ℝ → ℝ) (L u : ℝ) : |truncTest F L u| ≤ |F u| := by
  unfold truncTest
  rw [abs_mul, abs_of_nonneg (bulkCutoff_nonneg L u)]
  exact mul_le_of_le_one_right (abs_nonneg _) (bulkCutoff_le_one L u)

theorem truncTest_eq_self {F : ℝ → ℝ} {L u : ℝ} (h : |u| ≤ L - 1) : truncTest F L u = F u := by
  simp [truncTest, bulkCutoff_eq_one h]

/-- The derivative of the truncation. -/
def truncTestDeriv (F : ℝ → ℝ) (L u : ℝ) : ℝ :=
  deriv F u * bulkCutoff L u + F u * bulkCutoffDeriv L u

theorem hasDerivAt_truncTest {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L u : ℝ) :
    HasDerivAt (truncTest F L) (truncTestDeriv F L u) u :=
  ((hF.differentiable (by norm_num)) u).hasDerivAt.mul (hasDerivAt_bulkCutoff L u)

theorem continuous_truncTestDeriv {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L : ℝ) :
    Continuous (truncTestDeriv F L) := by
  have hd : Continuous (deriv F) := hF.continuous_deriv (by norm_num)
  have hc : Continuous (bulkCutoffDeriv L) := by
    unfold bulkCutoffDeriv
    have h := (Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by norm_num)
    fun_prop
  exact (hd.mul (contDiff_bulkCutoff L (n := 0)).continuous).add (hF.continuous.mul hc)

theorem deriv_truncTest {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L u : ℝ) :
    deriv (truncTest F L) u = truncTestDeriv F L u :=
  (hasDerivAt_truncTest hF L u).deriv

theorem abs_truncTestDeriv_le {F : ℝ → ℝ} {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) (L u : ℝ) :
    |truncTestDeriv F L u| ≤ |deriv F u| + 2 * Λ * |F u| := by
  unfold truncTestDeriv
  have h1 : |deriv F u * bulkCutoff L u| ≤ |deriv F u| := by
    rw [abs_mul, abs_of_nonneg (bulkCutoff_nonneg L u)]
    exact mul_le_of_le_one_right (abs_nonneg _) (bulkCutoff_le_one L u)
  have h2 : |F u * bulkCutoffDeriv L u| ≤ 2 * Λ * |F u| := by
    rw [abs_mul, mul_comm (2 * Λ)]
    exact mul_le_mul_of_nonneg_left (abs_bulkCutoffDeriv_le hΛ L u) (abs_nonneg _)
  calc |deriv F u * bulkCutoff L u + F u * bulkCutoffDeriv L u|
      ≤ |deriv F u * bulkCutoff L u| + |F u * bulkCutoffDeriv L u| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

/-! ### The zero side -/

private theorem integrable_exp_neg_mul_abs_aux {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun u : ℝ => Real.exp (-(κ * |u|))) := by
  have h := (RHTower.integrable_exp_neg_abs).comp_mul_left' hκ.ne'
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [abs_mul, abs_of_pos hκ]

/-- The tail majorant `(|F| + 2(|F'| + 2Λ|F|)) e^{|u|/2}`. -/
def tailMajorant (F : ℝ → ℝ) (Λ u : ℝ) : ℝ :=
  (|F u| + 2 * (|deriv F u| + 2 * Λ * |F u|)) * Real.exp (1 / 2 * |u|)

theorem tailMajorant_nonneg (F : ℝ → ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (u : ℝ) : 0 ≤ tailMajorant F Λ u := by
  unfold tailMajorant; positivity

theorem integrable_tailMajorant {F : ℝ → ℝ} (hF : ExpDecayTest F) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    Integrable (tailMajorant F Λ) := by
  obtain ⟨hF2, δ, C, hδ, hC, hb⟩ := hF
  have hint := (integrable_exp_neg_mul_abs_aux (κ := δ) hδ).const_mul
    ((3 + 4 * Λ) * C)
  have hcont : Continuous (tailMajorant F Λ) := by
    have hd : Continuous (deriv F) := hF2.continuous_deriv (by norm_num)
    have hF0 : Continuous F := hF2.continuous
    unfold tailMajorant
    fun_prop
  refine hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tailMajorant_nonneg F hΛ u)]
  obtain ⟨h1, h2⟩ := hb u
  have he : Real.exp (-((1 / 2 + δ) * |u|)) * Real.exp (1 / 2 * |u|) =
      Real.exp (-(δ * |u|)) := by
    rw [← Real.exp_add]; ring_nf
  have hE := Real.exp_pos (1 / 2 * |u|)
  have hsum : |F u| + 2 * (|deriv F u| + 2 * Λ * |F u|) ≤
      (3 + 4 * Λ) * (C * Real.exp (-((1 / 2 + δ) * |u|))) := by nlinarith
  calc tailMajorant F Λ u ≤ (3 + 4 * Λ) * (C * Real.exp (-((1 / 2 + δ) * |u|))) *
        Real.exp (1 / 2 * |u|) := mul_le_mul_of_nonneg_right hsum hE.le
    _ = (3 + 4 * Λ) * C * Real.exp (-(δ * |u|)) := by rw [← he]; ring

/-- The tail of the majorant beyond `L − 1`. -/
def tailBound (F : ℝ → ℝ) (Λ L : ℝ) : ℝ :=
  ∫ u, {u : ℝ | L - 1 ≤ |u|}.indicator (tailMajorant F Λ) u

theorem tailBound_nonneg (F : ℝ → ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (L : ℝ) : 0 ≤ tailBound F Λ L :=
  integral_nonneg fun u => Set.indicator_nonneg (fun v _ => tailMajorant_nonneg F hΛ v) u

theorem tendsto_tailBound {F : ℝ → ℝ} (hF : ExpDecayTest F) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    Tendsto (tailBound F Λ) atTop (𝓝 0) := by
  have h := (tendsto_integral_indicator_abs_ge (integrable_tailMajorant hF hΛ)).comp
    (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
  refine h.congr fun L => ?_
  simp only [Function.comp, id, tailBound, sub_eq_add_neg]

/-- Pointwise domination of a truncation difference by the tail majorant. -/
theorem weighted_truncTest_sub_le_indicator (F : ℝ → ℝ) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) {L M : ℝ} (hLM : L ≤ M)
    (u : ℝ) :
    ‖((truncTest F L u - truncTest F M u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) +
        ‖((truncTestDeriv F L u - truncTestDeriv F M u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) ≤
      {u : ℝ | L - 1 ≤ |u|}.indicator (tailMajorant F Λ) u := by
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases hu : L - 1 ≤ |u|
  · rw [Set.indicator_of_mem (show u ∈ {u : ℝ | L - 1 ≤ |u|} from hu)]
    have hA : |truncTest F L u - truncTest F M u| ≤ |F u| := by
      unfold truncTest
      rw [← mul_sub, abs_mul]
      refine mul_le_of_le_one_right (abs_nonneg _) ?_
      rw [abs_le]
      constructor <;> linarith [bulkCutoff_nonneg L u, bulkCutoff_le_one L u,
        bulkCutoff_nonneg M u, bulkCutoff_le_one M u]
    have hB : |truncTestDeriv F L u - truncTestDeriv F M u| ≤
        2 * (|deriv F u| + 2 * Λ * |F u|) := by
      have h1 := abs_truncTestDeriv_le (F := F) hΛ L u
      have h2 := abs_truncTestDeriv_le (F := F) hΛ M u
      have := abs_sub (truncTestDeriv F L u) (truncTestDeriv F M u)
      linarith
    unfold tailMajorant
    have hE := Real.exp_pos (1 / 2 * |u|)
    nlinarith
  · rw [Set.indicator_of_notMem (show u ∉ {u : ℝ | L - 1 ≤ |u|} from hu)]
    rw [not_le] at hu
    have hL : |u| ≤ L - 1 := hu.le
    have hM : |u| ≤ M - 1 := by linarith
    have hA : truncTest F L u - truncTest F M u = 0 := by
      rw [truncTest_eq_self hL, truncTest_eq_self hM, sub_self]
    have hB : truncTestDeriv F L u - truncTestDeriv F M u = 0 := by
      unfold truncTestDeriv
      rw [bulkCutoff_eq_one hL, bulkCutoff_eq_one hM, bulkCutoffDeriv_eq_zero hu,
        bulkCutoffDeriv_eq_zero (by linarith : |u| < M - 1)]
      ring
    rw [hA, hB, abs_zero, zero_mul, add_zero]

theorem hasCompactSupport_truncTestDeriv {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L : ℝ) :
    HasCompactSupport (truncTestDeriv F L) := by
  have h := (hasCompactSupport_truncTest F L).deriv
  have e : deriv (truncTest F L) = truncTestDeriv F L := funext (deriv_truncTest hF L)
  rwa [e] at h

/-- The weighted `L¹` energy of a truncation difference is bounded by the tail bound. -/
theorem integral_weighted_truncTest_sub_le {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    (hint : Integrable (tailMajorant F Λ)) {L M : ℝ} (hLM : L ≤ M) :
    (∫ u : ℝ, ‖((truncTest F L u - truncTest F M u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|)) +
        ∫ u : ℝ, ‖((truncTestDeriv F L u - truncTestDeriv F M u : ℝ) : ℂ)‖ *
          Real.exp (1 / 2 * |u|) ≤ tailBound F Λ L := by
  have hpt := weighted_truncTest_sub_le_indicator F hΛ hLM
  have hind : Integrable ({u : ℝ | L - 1 ≤ |u|}.indicator (tailMajorant F Λ)) :=
    hint.indicator (measurableSet_le measurable_const continuous_abs.measurable)
  have hAc : Continuous fun u : ℝ =>
      ‖((truncTest F L u - truncTest F M u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) := by
    have h1 := (contDiff_truncTest hF L).continuous
    have h2 := (contDiff_truncTest hF M).continuous
    fun_prop
  have hBc : Continuous fun u : ℝ =>
      ‖((truncTestDeriv F L u - truncTestDeriv F M u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) := by
    have h1 := continuous_truncTestDeriv hF L
    have h2 := continuous_truncTestDeriv hF M
    fun_prop
  have hA : Integrable fun u : ℝ =>
      ‖((truncTest F L u - truncTest F M u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) := by
    refine hind.mono' hAc.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := hpt u
    have : 0 ≤ ‖((truncTestDeriv F L u - truncTestDeriv F M u : ℝ) : ℂ)‖ *
      Real.exp (1 / 2 * |u|) := by positivity
    linarith
  have hB : Integrable fun u : ℝ =>
      ‖((truncTestDeriv F L u - truncTestDeriv F M u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) := by
    refine hind.mono' hBc.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := hpt u
    have : 0 ≤ ‖((truncTest F L u - truncTest F M u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) := by
      positivity
    linarith
  rw [← integral_add hA hB]
  exact integral_mono (hA.add hB) hind hpt

/-- **Fourier transform of a truncation difference in the critical strip.** -/
theorem one_add_abs_re_mul_norm_paperFT_truncTest_sub_le {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {Λ : ℝ} (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    (hint : Integrable (tailMajorant F Λ)) {L M : ℝ} (hLM : L ≤ M) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    (1 + |z.re|) * ‖paperFT (fun u => (truncTest F L u : ℂ)) z -
        paperFT (fun u => (truncTest F M u : ℂ)) z‖ ≤ tailBound F Λ L := by
  set H : ℝ → ℝ := fun u => truncTest F L u - truncTest F M u with hHdef
  set H' : ℝ → ℝ := fun u => truncTestDeriv F L u - truncTestDeriv F M u with hH'def
  have hHc : Continuous H :=
    (contDiff_truncTest hF L).continuous.sub (contDiff_truncTest hF M).continuous
  have hHs : HasCompactSupport H :=
    (hasCompactSupport_truncTest F L).sub (hasCompactSupport_truncTest F M)
  have hH'c : Continuous H' := (continuous_truncTestDeriv hF L).sub (continuous_truncTestDeriv hF M)
  have hH's : HasCompactSupport H' :=
    (hasCompactSupport_truncTestDeriv hF L).sub (hasCompactSupport_truncTestDeriv hF M)
  have hd : ∀ x, HasDerivAt (fun u => (H u : ℂ)) ((H' x : ℝ) : ℂ) x := fun x =>
    ((hasDerivAt_truncTest hF L x).sub (hasDerivAt_truncTest hF M x)).ofReal_comp
  have hsplit : paperFT (fun u => (H u : ℂ)) z =
      paperFT (fun u => (truncTest F L u : ℂ)) z - paperFT (fun u => (truncTest F M u : ℂ)) z := by
    unfold paperFT
    rw [← integral_sub
      (integrable_ofReal_mul_cexp_of_hasCompactSupport (contDiff_truncTest hF L).continuous
        (hasCompactSupport_truncTest F L) z)
      (integrable_ofReal_mul_cexp_of_hasCompactSupport (contDiff_truncTest hF M).continuous
        (hasCompactSupport_truncTest F M) z)]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hHdef]
    push_cast
    ring
  have h := one_add_abs_re_mul_norm_paperFT_le (superExpDecay_ofReal hHc hHs)
    (superExpDecay_ofReal hH'c hH's) hd hz
  rw [hsplit] at h
  exact h.trans (integral_weighted_truncTest_sub_le hF hΛ hint hLM)

/-- `|e^{izu}| ≤ e^{|u|/2}` in the critical strip. -/
theorem norm_cexp_I_mul_ofReal_le_of_strip {z : ℂ} (hz : |z.im| ≤ 1 / 2) (u : ℝ) :
    ‖Complex.exp (I * z * u)‖ ≤ Real.exp (1 / 2 * |u|) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre : (I * z * (u : ℂ)).re = -(z.im * u) := by simp [Complex.mul_re]
  rw [hre]
  have h1 : -(z.im * u) ≤ |z.im| * |u| := by
    have := neg_abs_le (z.im * u); rw [abs_mul] at this; linarith
  nlinarith [abs_nonneg u]

/-- **Truncations converge in Fourier transform throughout the critical strip.** -/
theorem tendsto_paperFT_truncTest {F : ℝ → ℝ} (hF : ExpDecayTest F) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    Tendsto (fun M : ℝ => paperFT (fun u => (truncTest F M u : ℂ)) z) atTop
      (𝓝 (paperFT (fun u => (F u : ℂ)) z)) := by
  obtain ⟨hF2, δ, C, hδ, hC, hb⟩ := hF
  have hmaj : Integrable fun u : ℝ => |F u| * Real.exp (1 / 2 * |u|) := by
    have hint := (integrable_exp_neg_mul_abs_aux (κ := δ) hδ).const_mul C
    have hcont : Continuous fun u : ℝ => |F u| * Real.exp (1 / 2 * |u|) := by
      have := hF2.continuous; fun_prop
    refine hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have he : Real.exp (-((1 / 2 + δ) * |u|)) * Real.exp (1 / 2 * |u|) =
        Real.exp (-(δ * |u|)) := by rw [← Real.exp_add]; ring_nf
    calc |F u| * Real.exp (1 / 2 * |u|) ≤ C * Real.exp (-((1 / 2 + δ) * |u|)) *
          Real.exp (1 / 2 * |u|) := mul_le_mul_of_nonneg_right (hb u).1 (by positivity)
      _ = C * Real.exp (-(δ * |u|)) := by rw [mul_assoc, he]
  unfold paperFT
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => |F u| * Real.exp (1 / 2 * |u|)) ?_ ?_ hmaj ?_
  · refine Eventually.of_forall fun M => ?_
    have := (contDiff_truncTest hF2 M).continuous
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine Eventually.of_forall fun M => Eventually.of_forall fun u => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (abs_truncTest_le F M u) (norm_cexp_I_mul_ofReal_le_of_strip hz u)
      (norm_nonneg _) (abs_nonneg _)
  · refine Eventually.of_forall fun u => tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (|u| + 1)] with M hM
    rw [truncTest_eq_self (by linarith)]

/-- **The truncations approximate `F̂` uniformly in the critical strip.** -/
theorem one_add_abs_re_mul_norm_paperFT_truncTest_sub_self_le {F : ℝ → ℝ} (hF : ExpDecayTest F)
    {Λ : ℝ} (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) (hΛ0 : 0 ≤ Λ) (L : ℝ) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    (1 + |z.re|) * ‖paperFT (fun u => (truncTest F L u : ℂ)) z -
        paperFT (fun u => (F u : ℂ)) z‖ ≤ tailBound F Λ L := by
  have hlim := tendsto_paperFT_truncTest hF hz
  have h2 : Tendsto (fun M : ℝ => (1 + |z.re|) * ‖paperFT (fun u => (truncTest F L u : ℂ)) z -
      paperFT (fun u => (truncTest F M u : ℂ)) z‖) atTop
      (𝓝 ((1 + |z.re|) * ‖paperFT (fun u => (truncTest F L u : ℂ)) z -
        paperFT (fun u => (F u : ℂ)) z‖)) :=
    ((tendsto_const_nhds.sub hlim).norm).const_mul _
  exact le_of_tendsto h2 (eventually_atTop.mpr ⟨L, fun M hM =>
    one_add_abs_re_mul_norm_paperFT_truncTest_sub_le hF.1 hΛ (integrable_tailMajorant hF hΛ0)
      hM hz⟩)

private theorem gammaOf_reflect_eq (ρ : ℂ) : gammaOf (reflect ρ) = (starRingEnd ℂ) (gammaOf ρ) := by
  unfold gammaOf reflect
  apply Complex.ext
  · simp
  · simp; ring

/-- **The zero side of a truncated `Ξ`-divisible test is small.** -/
theorem norm_W_truncTest_le {F : ℝ → ℝ} (hF : ExpDecayTest F) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) (hΛ0 : 0 ≤ Λ)
    (hzero : ∀ ρ : zetaZeroConfig.carrier, paperFT (fun u => (F u : ℂ)) (gammaOf ρ) = 0)
    (L : ℝ) :
    ‖zetaZeroConfig.W (fun u => (truncTest F L u : ℂ)) (fun u => (truncTest F L u : ℂ))‖ ≤
      (5 / 4) * zetaInvSqSum * tailBound F Λ L ^ 2 := by
  refine norm_W_le_of_zero_bound (tailBound_nonneg F hΛ0 L) fun ρ => ?_
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hstrip : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ⟨hmem.2.1, hmem.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip).le
  have hre : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
  constructor
  · have h := one_add_abs_re_mul_norm_paperFT_truncTest_sub_self_le hF hΛ hΛ0 L hIm
    rwa [hzero ρ, sub_zero, hre] at h
  · set ρ' : zetaZeroConfig.carrier := ⟨reflect (ρ : ℂ), zeta_reflect_zero _ hmem⟩
    have hg : gammaOf (ρ' : ℂ) = (starRingEnd ℂ) (gammaOf (ρ : ℂ)) := gammaOf_reflect_eq _
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    have h := one_add_abs_re_mul_norm_paperFT_truncTest_sub_self_le hF hΛ hΛ0 L hIm'
    rw [← hg, hzero ρ', sub_zero, hg, Complex.conj_re, hre] at h
    exact h

/-! ### The prime side -/

/-- The pointwise bound behind the autocorrelation decay:
`(1/2+δ)(|t| + |t − y|) ≥ (1/2 + δ/2)|y| + (δ/2)|t|`. -/
private theorem exp_decay_product_le {δ : ℝ} (hδ : 0 < δ) (t y : ℝ) :
    Real.exp (-((1 / 2 + δ) * |t|)) * Real.exp (-((1 / 2 + δ) * |t - y|)) ≤
      Real.exp (-((1 / 2 + δ / 2) * |y|)) * Real.exp (-(δ / 2 * |t|)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have htri : |y| ≤ |t| + |t - y| := by
    have := abs_sub (t) (t - y)
    rw [show t - (t - y) = y by ring] at this
    linarith
  nlinarith [abs_nonneg t, abs_nonneg (t - y)]

/-- **Uniform exponential decay of the truncated autocorrelations.** -/
theorem abs_crossCorr_truncTest_le {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hb : ∀ x : ℝ, |F x| ≤ C * Real.exp (-((1 / 2 + δ) * |x|))) (L y : ℝ) :
    |crossCorr (truncTest F L) (truncTest F L) y| ≤
      C ^ 2 * (∫ t : ℝ, Real.exp (-(δ / 2 * |t|))) * Real.exp (-((1 / 2 + δ / 2) * |y|)) := by
  unfold crossCorr
  have hint := (integrable_exp_neg_mul_abs_aux (κ := δ / 2) (by positivity)).const_mul
    (C ^ 2 * Real.exp (-((1 / 2 + δ / 2) * |y|)))
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun t => ?_)).trans
    (le_of_eq ?_)
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := (abs_truncTest_le F L t).trans (hb t)
    have h2 := (abs_truncTest_le F L (t - y)).trans (hb (t - y))
    have hp := exp_decay_product_le hδ t y
    calc |truncTest F L t| * |truncTest F L (t - y)|
        ≤ (C * Real.exp (-((1 / 2 + δ) * |t|))) * (C * Real.exp (-((1 / 2 + δ) * |t - y|))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = C ^ 2 * (Real.exp (-((1 / 2 + δ) * |t|)) * Real.exp (-((1 / 2 + δ) * |t - y|))) := by
          ring
      _ ≤ C ^ 2 * (Real.exp (-((1 / 2 + δ / 2) * |y|)) * Real.exp (-(δ / 2 * |t|))) :=
          mul_le_mul_of_nonneg_left hp (sq_nonneg C)
      _ = _ := by ring
  · rw [integral_const_mul]; ring

/-- The truncated autocorrelations converge pointwise. -/
theorem tendsto_crossCorr_truncTest {F : ℝ → ℝ} (hF : ExpDecayTest F) (y : ℝ) :
    Tendsto (fun L : ℝ => crossCorr (truncTest F L) (truncTest F L) y) atTop
      (𝓝 (crossCorr F F y)) := by
  obtain ⟨hF2, δ, C, hδ, hC, hb⟩ := hF
  unfold crossCorr
  have hint := (integrable_exp_neg_mul_abs_aux (κ := δ / 2) (by positivity)).const_mul
    (C ^ 2 * Real.exp (-((1 / 2 + δ / 2) * |y|)))
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hint ?_
  · refine Eventually.of_forall fun L => ?_
    have := (contDiff_truncTest hF2 L).continuous
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine Eventually.of_forall fun L => Eventually.of_forall fun t => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := (abs_truncTest_le F L t).trans (hb t).1
    have h2 := (abs_truncTest_le F L (t - y)).trans (hb (t - y)).1
    have hp := exp_decay_product_le hδ t y
    calc |truncTest F L t| * |truncTest F L (t - y)|
        ≤ (C * Real.exp (-((1 / 2 + δ) * |t|))) * (C * Real.exp (-((1 / 2 + δ) * |t - y|))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = C ^ 2 * (Real.exp (-((1 / 2 + δ) * |t|)) * Real.exp (-((1 / 2 + δ) * |t - y|))) := by
          ring
      _ ≤ C ^ 2 * (Real.exp (-((1 / 2 + δ / 2) * |y|)) * Real.exp (-(δ / 2 * |t|))) :=
          mul_le_mul_of_nonneg_left hp (sq_nonneg C)
      _ = _ := by ring
  · refine Eventually.of_forall fun t => tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (max |t| |t - y| + 1)] with L hL
    rw [truncTest_eq_self (by linarith [le_max_left |t| |t - y|]),
      truncTest_eq_self (by linarith [le_max_right |t| |t - y|])]

/-- The autocorrelation of a real test is even. -/
theorem crossCorr_self_neg (F : ℝ → ℝ) (y : ℝ) : crossCorr F F (-y) = crossCorr F F y := by
  unfold crossCorr
  have h := integral_sub_right_eq_self (μ := volume) (fun t : ℝ => F t * F (t - -y)) y
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [sub_neg_eq_add, sub_add_cancel]
  ring

/-- The truncated autocorrelation vanishes beyond twice the cutoff. -/
theorem crossCorr_truncTest_eq_zero (F : ℝ → ℝ) {L y : ℝ} (hy : 2 * L ≤ |y|) :
    crossCorr (truncTest F L) (truncTest F L) y = 0 := by
  unfold crossCorr
  have h0 : (fun t => truncTest F L t * truncTest F L (t - y)) = fun _ => (0 : ℝ) := by
    funext t
    by_cases ht : L ≤ |t|
    · rw [truncTest_eq_zero ht, zero_mul]
    · rw [not_le] at ht
      have h1 : L ≤ |t - y| := by
        have := abs_sub_abs_le_abs_sub y t
        rw [abs_sub_comm] at this
        linarith
      rw [truncTest_eq_zero h1, mul_zero]
  rw [h0, integral_zero]

/-- The prime profile `(g(log n) + g(−log n))/√n` of a kernel. -/
def primeLogProfile (g : ℝ → ℝ) (n : ℕ) : ℝ := (g (Real.log n) + g (-Real.log n)) / Real.sqrt n

/-- The partial sums `Σ_{2 ≤ m ≤ n} w(m)`. -/
def primeWeightPartialSum (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), if 2 ≤ m then w m else 0

theorem primeWeightPartialSum_eq_zero (w : ℕ → ℝ) {n : ℕ} (hn : n < 2) :
    primeWeightPartialSum w n = 0 := by
  interval_cases n <;> simp [primeWeightPartialSum, Finset.sum_range_succ]

/-- Summation by parts. -/
theorem sum_range_mul_eq_sum_partialSum_mul_sub (c ψ : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), c n * ψ n =
      ∑ n ∈ Finset.range (N + 1), (∑ m ∈ Finset.range (n + 1), c m) * (ψ n - ψ (n + 1)) +
        (∑ m ∈ Finset.range (N + 1), c m) * ψ (N + 1) := by
  induction N with
  | zero => simp only [zero_add, Finset.sum_range_one]; ring
  | succ N ih =>
    rw [Finset.sum_range_succ _ (N + 1), ih,
      Finset.sum_range_succ (fun n => (∑ m ∈ Finset.range (n + 1), c m) * (ψ n - ψ (n + 1)))
        (N + 1),
      Finset.sum_range_succ c (N + 1)]
    ring

/-- **Summation by parts for the prime pairing** of a kernel with bounded support. -/
theorem atomPairing_eq_tsum_primeWeightPartialSum (w : ℕ → ℝ) (g : ℝ → ℝ) {N : ℕ}
    (hg : ∀ n : ℕ, N < n → primeLogProfile g n = 0) :
    atomPairing w g =
      ∑' n : ℕ, primeWeightPartialSum w n * (primeLogProfile g n - primeLogProfile g (n + 1)) := by
  have h1 : atomPairing w g = ∑' n : ℕ, (if 2 ≤ n then w n else 0) * primeLogProfile g n := by
    unfold atomPairing primeLogProfile
    refine tsum_congr fun n => ?_
    split_ifs <;> ring
  rw [h1, tsum_eq_sum (s := Finset.range (N + 1)) (fun n hn => by
      rw [Finset.mem_range, not_lt] at hn; rw [hg n (by omega), mul_zero]),
    tsum_eq_sum (s := Finset.range (N + 1)) (fun n hn => by
      rw [Finset.mem_range, not_lt] at hn
      rw [hg n (by omega), hg (n + 1) (by omega), sub_self, mul_zero]),
    sum_range_mul_eq_sum_partialSum_mul_sub, hg (N + 1) (by omega), mul_zero, add_zero]
  rfl

/-- **Mean-value increments of the truncated autocorrelations.** -/
theorem abs_crossCorr_truncTest_add_sub_le {F : ℝ → ℝ} (hF2 : ContDiff ℝ 2 F) {δ C C₁ : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hb : ∀ x : ℝ, |F x| ≤ C * Real.exp (-((1 / 2 + δ) * |x|))) (L : ℝ)
    (hb' : ∀ x : ℝ, |truncTestDeriv F L x| ≤ C₁ * Real.exp (-((1 / 2 + δ) * |x|)))
    (y : ℝ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    |crossCorr (truncTest F L) (truncTest F L) (y + η) -
        crossCorr (truncTest F L) (truncTest F L) y| ≤
      η * (C * C₁ * Real.exp (1 / 2 + δ) * ∫ t : ℝ, Real.exp (-(δ / 2 * |t|))) *
        Real.exp (-((1 / 2 + δ / 2) * |y|)) := by
  have hXc : Continuous (truncTest F L) := (contDiff_truncTest hF2 L).continuous
  have hint : ∀ s : ℝ, Integrable fun t => truncTest F L t * truncTest F L (t - s) := fun s =>
    (hXc.mul (hXc.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      (hasCompactSupport_truncTest F L).mul_right
  unfold crossCorr
  rw [← integral_sub (hint _) (hint _)]
  have hmaj := (integrable_exp_neg_mul_abs_aux (κ := δ / 2) (by positivity)).const_mul
    (η * (C * C₁ * Real.exp (1 / 2 + δ)) * Real.exp (-((1 / 2 + δ / 2) * |y|)))
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hmaj (Eventually.of_forall fun t => ?_)).trans
    (le_of_eq ?_)
  · rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
    have hmv : |truncTest F L (t - (y + η)) - truncTest F L (t - y)| ≤
        η * (C₁ * Real.exp (1 / 2 + δ) * Real.exp (-((1 / 2 + δ) * |t - y|))) := by
      rcases eq_or_lt_of_le hη0 with h0 | hpos
      · rw [← h0, add_zero, sub_self, abs_zero, zero_mul]
      · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (truncTest F L) (truncTestDeriv F L)
          (a := t - (y + η)) (b := t - y) (by linarith) hXc.continuousOn
          (fun x _ => hasDerivAt_truncTest hF2 L x)
        have hba : (t - y) - (t - (y + η)) = η := by ring
        rw [hba] at hcd
        have hdiff : truncTest F L (t - (y + η)) - truncTest F L (t - y) =
            -(η * truncTestDeriv F L c) := by
          rw [hcd]; field_simp; ring
        rw [hdiff, abs_neg, abs_mul, abs_of_nonneg hη0]
        refine mul_le_mul_of_nonneg_left ?_ hη0
        have hcl : |t - y| ≤ |c| + 1 := by
          have h1 := hc.1
          have h2 := hc.2
          have : |t - y - c| ≤ η := by rw [abs_le]; constructor <;> linarith
          calc |t - y| = |c + (t - y - c)| := by ring_nf
            _ ≤ |c| + |t - y - c| := abs_add_le _ _
            _ ≤ |c| + 1 := by linarith
        have hexp : Real.exp (-((1 / 2 + δ) * |c|)) ≤
            Real.exp (1 / 2 + δ) * Real.exp (-((1 / 2 + δ) * |t - y|)) := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          nlinarith [mul_le_mul_of_nonneg_left hcl (show (0 : ℝ) ≤ 1 / 2 + δ by linarith)]
        calc |truncTestDeriv F L c| ≤ C₁ * Real.exp (-((1 / 2 + δ) * |c|)) := hb' c
          _ ≤ C₁ * (Real.exp (1 / 2 + δ) * Real.exp (-((1 / 2 + δ) * |t - y|))) :=
              mul_le_mul_of_nonneg_left hexp hC₁
          _ = _ := by ring
    have h1 : |truncTest F L t| ≤ C * Real.exp (-((1 / 2 + δ) * |t|)) :=
      (abs_truncTest_le F L t).trans (hb t)
    have hp := exp_decay_product_le hδ t y
    calc |truncTest F L t| * |truncTest F L (t - (y + η)) - truncTest F L (t - y)|
        ≤ (C * Real.exp (-((1 / 2 + δ) * |t|))) *
            (η * (C₁ * Real.exp (1 / 2 + δ) * Real.exp (-((1 / 2 + δ) * |t - y|)))) :=
          mul_le_mul h1 hmv (abs_nonneg _) (by positivity)
      _ = η * (C * C₁ * Real.exp (1 / 2 + δ)) *
            (Real.exp (-((1 / 2 + δ) * |t|)) * Real.exp (-((1 / 2 + δ) * |t - y|))) := by ring
      _ ≤ η * (C * C₁ * Real.exp (1 / 2 + δ)) *
            (Real.exp (-((1 / 2 + δ / 2) * |y|)) * Real.exp (-(δ / 2 * |t|))) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  · rw [integral_const_mul]; ring

/-- `0 ≤ 1/√n − 1/√(n+1) ≤ 1/(n√n)`. -/
private theorem inv_sqrt_sub_inv_sqrt_succ_bounds {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ 1 / Real.sqrt n - 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ∧
      1 / Real.sqrt n - 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ 1 / (n * Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set a := Real.sqrt n with ha
  set b := Real.sqrt ((n + 1 : ℕ) : ℝ) with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr hn0
  have hab : a ≤ b := Real.sqrt_le_sqrt (by push_cast; linarith)
  have hb0 : 0 < b := ha0.trans_le hab
  have ha2 : a ^ 2 = n := Real.sq_sqrt hn0.le
  have hb2 : b ^ 2 = n + 1 := by rw [hb, Real.sq_sqrt (by positivity)]; push_cast; ring
  constructor
  · rw [sub_nonneg]; exact one_div_le_one_div_of_le ha0 hab
  · rw [div_sub_div _ _ ha0.ne' hb0.ne', div_le_div_iff₀ (by positivity) (by positivity), ← ha2]
    have h1 : (b - a) * a ^ 2 ≤ (b - a) * ((b + a) * b) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    have h2 : (b - a) * ((b + a) * b) = b := by
      have : b ^ 2 - a ^ 2 = 1 := by rw [hb2, ha2]; ring
      calc (b - a) * ((b + a) * b) = (b ^ 2 - a ^ 2) * b := by ring
        _ = b := by rw [this, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2.le) ha0.le]

/-- **Increments of the prime profile of a truncated autocorrelation**, uniformly in the
cutoff. -/
theorem abs_primeLogProfile_truncTest_sub_le {F : ℝ → ℝ} (hF2 : ContDiff ℝ 2 F) {δ C C₁ : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (hb : ∀ x : ℝ, |F x| ≤ C * Real.exp (-((1 / 2 + δ) * |x|))) (L : ℝ)
    (hb' : ∀ x : ℝ, |truncTestDeriv F L x| ≤ C₁ * Real.exp (-((1 / 2 + δ) * |x|)))
    {n : ℕ} (hn : 1 ≤ n) :
    |primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) n -
        primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) (n + 1)| ≤
      2 * ((C ^ 2 + C * C₁ * Real.exp (1 / 2 + δ)) * ∫ t : ℝ, Real.exp (-(δ / 2 * |t|))) *
        Real.exp (-((1 / 2 + δ / 2) * Real.log n)) / (n * Real.sqrt n) := by
  set k := crossCorr (truncTest F L) (truncTest F L) with hk
  set I := ∫ t : ℝ, Real.exp (-(δ / 2 * |t|)) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun t => (Real.exp_pos _).le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set y := Real.log n with hy
  set y' := Real.log ((n + 1 : ℕ) : ℝ) with hy'
  have hy0 : 0 ≤ y := Real.log_nonneg hn1
  set η := y' - y with hη
  have hη0 : 0 ≤ η := by
    rw [hη, sub_nonneg]; exact Real.log_le_log hn0 (by push_cast; linarith)
  have hηn : η ≤ 1 / n := by
    rw [hη, hy', hy, ← Real.log_div (by positivity) hn0.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    push_cast; field_simp; ring
  have hη1 : η ≤ 1 := hηn.trans (by rw [div_le_one hn0]; exact hn1)
  set E := Real.exp (-((1 / 2 + δ / 2) * y)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have heven : ∀ z, k (-z) = k z := fun z => crossCorr_self_neg _ z
  have hp : |k y| ≤ C ^ 2 * I * E := by
    have := abs_crossCorr_truncTest_le hδ hC hb L y
    rwa [abs_of_nonneg hy0] at this
  have hpq : |k y' - k y| ≤ η * (C * C₁ * Real.exp (1 / 2 + δ) * I) * E := by
    have := abs_crossCorr_truncTest_add_sub_le hF2 hδ hC hC₁ hb L hb' y hη0 hη1
    rwa [abs_of_nonneg hy0, show y + η = y' by rw [hη]; ring] at this
  obtain ⟨hs0, hs1⟩ := inv_sqrt_sub_inv_sqrt_succ_bounds hn
  set a := Real.sqrt n with ha
  set b := Real.sqrt ((n + 1 : ℕ) : ℝ) with hb2
  have ha0 : 0 < a := Real.sqrt_pos.mpr hn0
  have hab : a ≤ b := Real.sqrt_le_sqrt (by push_cast; linarith)
  have hb0 : 0 < b := ha0.trans_le hab
  have hprof : primeLogProfile k n - primeLogProfile k (n + 1) =
      2 * k y * (1 / a - 1 / b) + 2 * (k y - k y') / b := by
    unfold primeLogProfile
    rw [heven, heven]
    field_simp
    ring
  rw [hprof]
  have hK : 0 ≤ C * C₁ * Real.exp (1 / 2 + δ) * I := by positivity
  calc |2 * k y * (1 / a - 1 / b) + 2 * (k y - k y') / b|
      ≤ |2 * k y * (1 / a - 1 / b)| + |2 * (k y - k y') / b| := abs_add_le _ _
    _ = 2 * |k y| * (1 / a - 1 / b) + 2 * |k y' - k y| / b := by
        rw [abs_mul, abs_mul, abs_of_nonneg hs0, abs_div, abs_mul, abs_of_pos hb0, abs_sub_comm]
        norm_num
    _ ≤ 2 * (C ^ 2 * I * E) * (1 / (n * a)) +
          2 * (1 / n * (C * C₁ * Real.exp (1 / 2 + δ) * I) * E) / a := by
        gcongr
        · exact hpq.trans (by gcongr)
    _ = 2 * ((C ^ 2 + C * C₁ * Real.exp (1 / 2 + δ)) * I) * E / (n * a) := by
        field_simp

/-- **The Abel form of the prime pairing**
`Σ_n S_w(n) (ψ(n) − ψ(n+1))`, with `S_w` the partial sums of `w` and `ψ` the prime profile
`(k(log n) + k(−log n))/√n` of `k = F ⋆ F̃`.  For compactly supported `F` it is the prime pairing
itself (`atomPairing_eq_tsum_primeWeightPartialSum`); for the decay class it is the limit of the
prime pairings of the truncations (`tendsto_atomPairing_truncTest_abelPrimePairing`). -/
def abelPrimePairing (w : ℕ → ℝ) (F : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, primeWeightPartialSum w n *
    (primeLogProfile (crossCorr F F) n - primeLogProfile (crossCorr F F) (n + 1))

/-- The Abel prime pairing of a prime-blind test vanishes. -/
theorem abelPrimePairing_eq_zero_of_blind (w : ℕ → ℝ) {F : ℝ → ℝ}
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0) : abelPrimePairing w F = 0 := by
  unfold abelPrimePairing
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rcases lt_or_ge n 2 with hn | hn
  · rw [primeWeightPartialSum_eq_zero w hn, zero_mul]
  · have hz : ∀ m : ℕ, 2 ≤ m → primeLogProfile (crossCorr F F) m = 0 := fun m hm => by
      unfold primeLogProfile
      rw [crossCorr_self_neg, hblind m hm]
      simp
    rw [hz n hn, hz (n + 1) (by omega), sub_self, mul_zero]

/-- **The prime pairings of the truncations converge to the Abel prime pairing.**  If the
partial sums of `w` grow at most linearly, then `T_w(F_L ⋆ F̃_L) → Σ_n S_w(n)(ψ(n) − ψ(n+1))`.
Summation by parts moves the weights onto their partial sums and the increments of the profile,
which are `O(n^{−2−δ/2})` uniformly in `L`. -/
theorem tendsto_atomPairing_truncTest_abelPrimePairing {F : ℝ → ℝ} (hF : ExpDecayTest F)
    {w : ℕ → ℝ} {A : ℝ} (hA : ∀ N : ℕ, |primeWeightPartialSum w N| ≤ A * (N + 1)) :
    Tendsto (fun L : ℝ => atomPairing w (crossCorr (truncTest F L) (truncTest F L))) atTop
      (𝓝 (abelPrimePairing w F)) := by
  have hF' := hF
  obtain ⟨hF2, δ, C, hδ, hC, hb⟩ := hF'
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  set C₁ : ℝ := (1 + 2 * Λ) * C with hC₁def
  have hC₁ : 0 ≤ C₁ := by positivity
  have hb' : ∀ L x : ℝ, |truncTestDeriv F L x| ≤ C₁ * Real.exp (-((1 / 2 + δ) * |x|)) := by
    intro L x
    have h := abs_truncTestDeriv_le (F := F) hΛ L x
    have h1 := (hb x).1
    have h2 := (hb x).2
    calc |truncTestDeriv F L x| ≤ |deriv F x| + 2 * Λ * |F x| := h
      _ ≤ C * Real.exp (-((1 / 2 + δ) * |x|)) +
            2 * Λ * (C * Real.exp (-((1 / 2 + δ) * |x|))) := by gcongr
      _ = C₁ * Real.exp (-((1 / 2 + δ) * |x|)) := by rw [hC₁def]; ring
  have hA0 : 0 ≤ A := by
    have := hA 0
    rw [primeWeightPartialSum_eq_zero w (by norm_num)] at this
    simpa using this
  set K : ℝ := (C ^ 2 + C * C₁ * Real.exp (1 / 2 + δ)) * ∫ t : ℝ, Real.exp (-(δ / 2 * |t|))
    with hKdef
  have hK : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (by positivity) (integral_nonneg fun t => (Real.exp_pos _).le)
  set p : ℝ := 1 + δ / 2 with hp
  set M : ℝ := 4 * A * K with hM
  have hsum : Summable fun n : ℕ => M * ((n : ℝ) ^ p)⁻¹ :=
    (Real.summable_nat_rpow_inv.mpr (by rw [hp]; linarith)).mul_left M
  -- summation by parts for each cutoff
  have hrewrite : ∀ L : ℝ, atomPairing w (crossCorr (truncTest F L) (truncTest F L)) =
      ∑' n : ℕ, primeWeightPartialSum w n *
        (primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) n -
          primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) (n + 1)) := by
    intro L
    refine atomPairing_eq_tsum_primeWeightPartialSum w _ (N := ⌈Real.exp (2 * L)⌉₊) fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by
      have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
      exact_mod_cast this
    have hlog : 2 * L < Real.log n := by
      rw [Real.lt_log_iff_exp_lt hn0]
      exact (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
    have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by
      have : 1 ≤ n := lt_of_le_of_lt (Nat.zero_le _) hn
      exact_mod_cast this)
    unfold primeLogProfile
    rw [crossCorr_truncTest_eq_zero F (by rw [abs_of_nonneg hl0]; linarith),
      crossCorr_truncTest_eq_zero F (by rw [abs_neg, abs_of_nonneg hl0]; linarith)]
    simp
  -- pointwise limits
  have hprof : ∀ m : ℕ, Tendsto
      (fun L : ℝ => primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) m) atTop
      (𝓝 (primeLogProfile (crossCorr F F) m)) := fun m =>
    ((tendsto_crossCorr_truncTest hF (Real.log m)).add
      (tendsto_crossCorr_truncTest hF (-Real.log m))).div_const _
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) hsum
    (f := fun L n => primeWeightPartialSum w n *
      (primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) n -
        primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) (n + 1)))
    (g := fun n => primeWeightPartialSum w n *
      (primeLogProfile (crossCorr F F) n - primeLogProfile (crossCorr F F) (n + 1)))
    (fun n => ((hprof n).sub (hprof (n + 1))).const_mul _)
    (Eventually.of_forall fun L n => ?_)
  · exact h.congr fun L => (hrewrite L).symm
  · rw [Real.norm_eq_abs, abs_mul]
    have hMp : 0 ≤ M * ((n : ℝ) ^ p)⁻¹ := by rw [hM]; positivity
    rcases lt_or_ge n 2 with hn | hn
    · rw [primeWeightPartialSum_eq_zero w hn, abs_zero, zero_mul]
      exact hMp
    · have hn1 : 1 ≤ n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hΔ := abs_primeLogProfile_truncTest_sub_le hF2 hδ hC hC₁ (fun x => (hb x).1) L (hb' L)
        hn1
      rw [← hKdef] at hΔ
      set E := Real.exp (-((1 / 2 + δ / 2) * Real.log n)) with hE
      have hEp : E / Real.sqrt n = ((n : ℝ) ^ p)⁻¹ := by
        rw [hE, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0,
          ← Real.exp_sub, ← Real.exp_neg, hp]
        congr 1
        ring
      have hratio : ((n : ℝ) + 1) / n ≤ 2 := by
        rw [div_le_iff₀ hn0]
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        linarith
      calc |primeWeightPartialSum w n| *
            |primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) n -
              primeLogProfile (crossCorr (truncTest F L) (truncTest F L)) (n + 1)|
          ≤ (A * (n + 1)) * (2 * K * E / (n * Real.sqrt n)) :=
            mul_le_mul (hA n) hΔ (abs_nonneg _) (by positivity)
        _ = 2 * A * K * (((n : ℝ) + 1) / n) * (E / Real.sqrt n) := by
            field_simp
        _ ≤ 2 * A * K * 2 * (E / Real.sqrt n) := by gcongr
        _ = M * ((n : ℝ) ^ p)⁻¹ := by rw [hEp, hM]; ring

/-- **The prime pairing of the truncations tends to `0` for a prime-blind test.** -/
theorem tendsto_atomPairing_truncTest {F : ℝ → ℝ} (hF : ExpDecayTest F) {w : ℕ → ℝ} {A : ℝ}
    (hA : ∀ N : ℕ, |primeWeightPartialSum w N| ≤ A * (N + 1))
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0) :
    Tendsto (fun L : ℝ => atomPairing w (crossCorr (truncTest F L) (truncTest F L))) atTop
      (𝓝 0) := by
  have h := tendsto_atomPairing_truncTest_abelPrimePairing hF hA
  rwa [abelPrimePairing_eq_zero_of_blind w hblind] at h

/-- **Linear growth of the partial sums of `lam − Λ`** for a Weil-positive system: the corpus
bound `Σ_{n ≤ N} lam(n) = N + O(N^{1/2+ε})` and Chebyshev's `ψ(N) ≤ 7N`. -/
theorem exists_abs_primeWeightPartialSum_sub_vonMangoldt_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ A : ℝ, ∀ N : ℕ,
      |primeWeightPartialSum (fun n => lam n - ArithmeticFunction.vonMangoldt n) N| ≤
        A * (N + 1) := by
  obtain ⟨C, hC, hS⟩ := WeilSingularArithmetic.exists_sharp_source_sum_le hW
    (ε := 1 / 2) (by norm_num)
  refine ⟨C + 8, fun N => ?_⟩
  have h1 := hS N
  rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one] at h1
  have hc : (∑ n ∈ Finset.range (N + 1), ((if 2 ≤ n then lam n else 0 : ℝ) : ℂ)) - (N : ℂ) =
      (((∑ n ∈ Finset.range (N + 1), (if 2 ≤ n then lam n else 0)) - N : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_natCast]
  rw [hc, Complex.norm_real, Real.norm_eq_abs] at h1
  have hsplit : primeWeightPartialSum (fun n => lam n - ArithmeticFunction.vonMangoldt n) N =
      (∑ m ∈ Finset.range (N + 1), (if 2 ≤ m then lam m else 0)) -
        ∑ m ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt m := by
    unfold primeWeightPartialSum
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hm
    · rfl
    · have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl <;> simp
  have hpsi := RHTower.sum_range_vonMangoldt_eq_chebyshevPsi N
  have hpsi7 := RHTower.chebyshevPsi_le_seven N
  have hpsi0 : 0 ≤ ∑ m ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt m :=
    Finset.sum_nonneg fun m _ => ArithmeticFunction.vonMangoldt_nonneg
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [hsplit, abs_le]
  have := abs_le.mp h1
  constructor <;> nlinarith

/-! ### Assembly -/

/-- The `L²(μ_lam)` energy of a truncation is its zeta side minus its prime perturbation. -/
theorem toReal_lintegral_specDensity_truncTest_eq {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (L : ℝ) :
    (∫⁻ r, (specDensity (fun u => (truncTest F L u : ℂ)) r : ℝ≥0∞) ∂boundaryMeasure hW) < ⊤ ∧
    (∫⁻ r, (specDensity (fun u => (truncTest F L u : ℂ)) r : ℝ≥0∞) ∂boundaryMeasure hW).toReal =
      (zetaZeroConfig.W (fun u => (truncTest F L u : ℂ)) (fun u => (truncTest F L u : ℂ))).re -
        atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n)
          (crossCorr (truncTest F L) (truncTest F L)) := by
  have hFL := contDiff_ofReal_truncTest hF L
  have hFLc : HasCompactSupport fun u => (truncTest F L u : ℂ) :=
    (hasCompactSupport_truncTest F L).comp_left Complex.ofReal_zero
  obtain ⟨hfin, hrep⟩ := weilFullFunctional_weilTest_eq_lintegral hW hFL hFLc
  have hadd := re_weilFullFunctional_add_eq (fun n => lam n - ArithmeticFunction.vonMangoldt n)
    hFL (hasCompactSupport_truncTest F L)
  have hlam : (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) +
      (lam n - ArithmeticFunction.vonMangoldt n)) = lam := funext fun n => by ring
  rw [hlam, hrep, Complex.ofReal_re] at hadd
  exact ⟨hfin, hadd⟩

/-- **The spectral energy of a `Ξ`-divisible prime-blind test vanishes.** -/
theorem lintegral_specDensity_eq_zero_of_xiDivisibleBlindTest {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0)
    (hzero : ∀ ρ : zetaZeroConfig.carrier, paperFT (fun u => (F u : ℂ)) (gammaOf ρ) = 0)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    (∫⁻ r, (specDensity (fun u => (F u : ℂ)) r : ℝ≥0∞) ∂boundaryMeasure hW) = 0 := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨A, hA⟩ := exists_abs_primeWeightPartialSum_sub_vonMangoldt_le hW
  set μ := boundaryMeasure hW
  set e : ℝ → ℝ≥0∞ := fun L =>
    ∫⁻ r, (specDensity (fun u => (truncTest F L u : ℂ)) r : ℝ≥0∞) ∂μ with he
  -- the energies of the truncations tend to `0`
  have hzeta : Tendsto (fun L : ℝ =>
      (zetaZeroConfig.W (fun u => (truncTest F L u : ℂ)) (fun u => (truncTest F L u : ℂ))).re)
      atTop (𝓝 0) := by
    have hb : Tendsto (fun L => (5 / 4) * zetaInvSqSum * tailBound F Λ L ^ 2) atTop (𝓝 0) := by
      simpa using ((tendsto_tailBound hF hΛ0).pow 2).const_mul ((5 / 4) * zetaInvSqSum)
    refine squeeze_zero_norm (fun L => ?_) hb
    exact (Complex.abs_re_le_norm _).trans (norm_W_truncTest_le hF hΛ hΛ0 hzero L)
  have hprime := tendsto_atomPairing_truncTest hF hA hblind
  have hreal : Tendsto (fun L => (e L).toReal) atTop (𝓝 0) := by
    have h := hzeta.sub hprime
    rw [sub_zero] at h
    exact h.congr fun L => (toReal_lintegral_specDensity_truncTest_eq hF.1 hW L).2.symm
  have hlim : Tendsto e atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hreal
    rw [ENNReal.ofReal_zero] at h
    exact h.congr fun L =>
      ENNReal.ofReal_toReal (toReal_lintegral_specDensity_truncTest_eq hF.1 hW L).1.ne
  -- Fatou along `L = k`
  have hmeas : ∀ k : ℕ, Measurable fun r =>
      (specDensity (fun u => (truncTest F (k : ℝ) u : ℂ)) r : ℝ≥0∞) := fun k =>
    (measurable_specDensity
      ((contDiff_ofReal_truncTest hF.1 _).continuous.integrable_of_hasCompactSupport
        ((hasCompactSupport_truncTest F _).comp_left Complex.ofReal_zero))).coe_nnreal_ennreal
  have hpt : ∀ r : ℝ, Tendsto (fun k : ℕ =>
      (specDensity (fun u => (truncTest F (k : ℝ) u : ℂ)) r : ℝ≥0∞)) atTop
      (𝓝 (specDensity (fun u => (F u : ℂ)) r : ℝ≥0∞)) := by
    intro r
    have hz : |((r : ℂ)).im| ≤ 1 / 2 := by simp
    have h := (tendsto_paperFT_truncTest hF hz).comp tendsto_natCast_atTop_atTop
    have hc : Continuous fun z : ℂ => ((‖z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.continuous_coe.comp (continuous_nnnorm.pow 2)
    exact (hc.tendsto _).comp h
  have hfatou := lintegral_liminf_le (μ := μ) (u := (atTop : Filter ℕ)) hmeas
  have hliminf : liminf (fun k : ℕ => ∫⁻ r,
      (specDensity (fun u => (truncTest F (k : ℝ) u : ℂ)) r : ℝ≥0∞) ∂μ) atTop = 0 :=
    (hlim.comp tendsto_natCast_atTop_atTop).liminf_eq
  rw [hliminf] at hfatou
  exact le_antisymm (le_of_eq_of_le (lintegral_congr fun r => (hpt r).liminf_eq.symm) hfatou)
    (zero_le)

/-- **A `Ξ`-divisible prime-blind test confines the boundary measure to the critical zeros.** -/
theorem boundaryMeasure_zeta_ne_zero_of_xiDivisibleBlindTest {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0)
    (hzero : ∀ ρ : zetaZeroConfig.carrier, paperFT (fun u => (F u : ℂ)) (gammaOf ρ) = 0)
    (hreal : ∀ r : ℝ, paperFT (fun u => (F u : ℂ)) r = 0 → riemannZeta ((1 / 2 : ℂ) + r * I) = 0)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    boundaryMeasure hW {r : ℝ | riemannZeta ((1 / 2 : ℂ) + r * I) ≠ 0} = 0 := by
  have h0 := lintegral_specDensity_eq_zero_of_xiDivisibleBlindTest hF hblind hzero hW
  have hFint : Integrable fun u => (F u : ℂ) := by
    obtain ⟨hF2, δ, C, hδ, hC, hb⟩ := hF
    have hint := (integrable_exp_neg_mul_abs_aux (κ := 1 / 2 + δ) (by positivity)).const_mul C
    refine hint.mono' (Complex.continuous_ofReal.comp hF2.continuous).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hb u).1
  rw [lintegral_eq_zero_iff (measurable_specDensity hFint).coe_nnreal_ennreal] at h0
  have hnull : boundaryMeasure hW {r : ℝ | (specDensity (fun u => (F u : ℂ)) r : ℝ≥0∞) ≠ 0} = 0 :=
    ae_iff.mp h0
  refine measure_mono_null (fun r hr => ?_) hnull
  simp only [Set.mem_setOf_eq] at hr ⊢
  intro hs
  apply hr
  apply hreal
  simpa [specDensity] using hs

/-- **Rigidity from a `Ξ`-divisible prime-blind test.**  Every full-cone Weil-positive system is
`Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_xiDivisibleBlindTest {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0)
    (hzero : ∀ ρ : zetaZeroConfig.carrier, paperFT (fun u => (F u : ℂ)) (gammaOf ρ) = 0)
    (hreal : ∀ r : ℝ, paperFT (fun u => (F u : ℂ)) r = 0 → riemannZeta ((1 / 2 : ℂ) + r * I) = 0)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  eq_vonMangoldt_of_boundaryMeasure_criticalZeros hW
    (boundaryMeasure_zeta_ne_zero_of_xiDivisibleBlindTest hF hblind hzero hreal hW)

/-- **RH from prime-blind positivity and a `Ξ`-divisible prime-blind test.** -/
theorem riemannHypothesis_of_primeBlindPositive_of_xiDivisibleBlindTest
    (hP : WeilOneSided.PrimeBlindPositive) {F : ℝ → ℝ} (hF : ExpDecayTest F)
    (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0)
    (hzero : ∀ ρ : zetaZeroConfig.carrier, paperFT (fun u => (F u : ℂ)) (gammaOf ρ) = 0)
    (hreal : ∀ r : ℝ, paperFT (fun u => (F u : ℂ)) r = 0 →
      riemannZeta ((1 / 2 : ℂ) + r * I) = 0) :
    RiemannHypothesis := by
  obtain ⟨lam, hW⟩ := WeilOneSided.exists_weilPositiveFull_iff_primeBlindPositive.mpr hP
  exact riemannHypothesis_of_boundaryMeasure_criticalZeros hW
    (boundaryMeasure_zeta_ne_zero_of_xiDivisibleBlindTest hF hblind hzero hreal hW)

/-- **Given a `Ξ`-divisible prime-blind test, RH is prime-blind positivity.** -/
theorem riemannHypothesis_iff_primeBlindPositive_of_xiDivisibleBlindTest {F : ℝ → ℝ}
    (hF : ExpDecayTest F) (hblind : ∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0)
    (hzero : ∀ ρ : zetaZeroConfig.carrier, paperFT (fun u => (F u : ℂ)) (gammaOf ρ) = 0)
    (hreal : ∀ r : ℝ, paperFT (fun u => (F u : ℂ)) r = 0 →
      riemannZeta ((1 / 2 : ℂ) + r * I) = 0) :
    RiemannHypothesis ↔ WeilOneSided.PrimeBlindPositive :=
  ⟨fun hRH => WeilOneSided.exists_weilPositiveFull_iff_primeBlindPositive.mp
      ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH⟩,
    fun hP => riemannHypothesis_of_primeBlindPositive_of_xiDivisibleBlindTest hP hF hblind hzero
      hreal⟩

/-! ### The (N1) object in factorized form -/

/-- **A `Ξ`-divisible prime-blind test**: a test of the decay class whose Fourier transform is
`Ξ·g` on the critical strip, with `g` zero-free on the real line, and whose autocorrelation
vanishes at every `log n`, `n ≥ 2`.  Then `|F̂|² = Ξ²|g|²` with `|g|² > 0` on `ℝ`. -/
def XiDivisibleBlindTest (F : ℝ → ℝ) : Prop :=
  ExpDecayTest F ∧ (∀ n : ℕ, 2 ≤ n → crossCorr F F (Real.log n) = 0) ∧
    ∃ g : ℂ → ℂ, (∀ z : ℂ, |z.im| ≤ 1 / 2 →
      paperFT (fun u => (F u : ℂ)) z = RHTower.XiC z * g z) ∧ ∀ r : ℝ, g r ≠ 0

/-- The factorization puts the zeros of `F̂` at the spectral points of the zeros of `ζ`. -/
theorem paperFT_gammaOf_eq_zero_of_xiDivisibleBlindTest {F : ℝ → ℝ}
    (hF : XiDivisibleBlindTest F) (ρ : zetaZeroConfig.carrier) :
    paperFT (fun u => (F u : ℂ)) (gammaOf ρ) = 0 := by
  obtain ⟨-, -, g, hg, -⟩ := hF
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 :=
    (WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩).le
  rw [hg _ hIm]
  have hpt : (1 / 2 : ℂ) + gammaOf (ρ : ℂ) * I = ρ := by
    unfold gammaOf
    field_simp
    ring
  have hne : (ρ : ℂ) ≠ 1 := by
    intro h
    have := hmem.2.2
    rw [h, Complex.one_re] at this
    exact lt_irrefl 1 this
  have hxi : RHTower.xi (ρ : ℂ) = 0 := (RHTower.xi_eq_zero_iff hmem.2.1 hne).mpr hmem.1
  rw [show RHTower.XiC (gammaOf (ρ : ℂ)) = RHTower.xi (ρ : ℂ) by
    rw [RHTower.XiC, hpt], hxi, zero_mul]

/-- On the real line the factorization vanishes only at the critical zeros of `ζ`. -/
theorem riemannZeta_eq_zero_of_xiDivisibleBlindTest {F : ℝ → ℝ} (hF : XiDivisibleBlindTest F)
    {r : ℝ} (hr : paperFT (fun u => (F u : ℂ)) r = 0) :
    riemannZeta ((1 / 2 : ℂ) + r * I) = 0 := by
  obtain ⟨-, -, g, hg, hg0⟩ := hF
  rw [hg _ (by simp)] at hr
  have hX : RHTower.XiC r = 0 := (mul_eq_zero.mp hr).resolve_right (hg0 r)
  have hre : 0 < ((1 / 2 : ℂ) + r * I).re := by simp
  have hne : (1 / 2 : ℂ) + r * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  exact (RHTower.xi_eq_zero_iff hre hne).mp hX

/-- **(N1) pins the Weil cone to `Λ`.**  If a `Ξ`-divisible prime-blind test exists, every
full-cone Weil-positive system equals `Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_exists_xiDivisibleBlindTest (hN1 : ∃ F, XiDivisibleBlindTest F)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨F, hF⟩ := hN1
  exact eq_vonMangoldt_of_xiDivisibleBlindTest hF.1 hF.2.1
    (paperFT_gammaOf_eq_zero_of_xiDivisibleBlindTest hF)
    (fun r hr => riemannZeta_eq_zero_of_xiDivisibleBlindTest hF hr) hW

/-- **RH ⟺ PBAP under (N1).**  If a `Ξ`-divisible prime-blind test exists, the Riemann hypothesis
is equivalent to prime-blind positivity, a statement about the archimedean place and the
positions `log n` alone. -/
theorem riemannHypothesis_iff_primeBlindPositive_of_exists_xiDivisibleBlindTest
    (hN1 : ∃ F, XiDivisibleBlindTest F) :
    RiemannHypothesis ↔ WeilOneSided.PrimeBlindPositive := by
  obtain ⟨F, hF⟩ := hN1
  exact riemannHypothesis_iff_primeBlindPositive_of_xiDivisibleBlindTest hF.1 hF.2.1
    (paperFT_gammaOf_eq_zero_of_xiDivisibleBlindTest hF)
    (fun r hr => riemannZeta_eq_zero_of_xiDivisibleBlindTest hF hr)

/-! ### (N1) makes the archimedean and pole energy vanish -/

/-- **The pole and archimedean energy** of a real test in spectral form,
`2 Re(F̂(i/2) · conj F̂(−i/2)) + (1/2π) ∫ |F̂(r)|² G(r) dr`, with `G` the Gamma bracket.  For a
compactly supported test it is the pole and archimedean part of the Weil functional of `F ⋆ F̃`
(`weilArchRe_weilTest_truncTest_eq`); it involves no prime and no zero of `ζ`. -/
def archPoleEnergy (F : ℝ → ℝ) : ℝ :=
  2 * (paperFT (fun u => (F u : ℂ)) (I / 2) * conj (paperFT (fun u => (F u : ℂ)) (-I / 2))).re +
    1 / (2 * π) * ∫ r : ℝ, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 * EF.gammaBracket r

theorem weilArchRe_weilTest_truncTest_eq {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L : ℝ) :
    WeilOneSided.weilArchRe
        (EF.weilTest (fun u => (truncTest F L u : ℂ)) (fun u => (truncTest F L u : ℂ))) =
      archPoleEnergy (truncTest F L) := by
  set f : ℝ → ℂ := fun u => (truncTest F L u : ℂ) with hf
  have hfc : Continuous f := (contDiff_ofReal_truncTest hF L).continuous
  have hfs : HasCompactSupport f := (hasCompactSupport_truncTest F L).comp_left Complex.ofReal_zero
  have hp : paperFT (EF.weilTest f f) (I / 2) + paperFT (EF.weilTest f f) (-I / 2) =
      ((2 * (paperFT f (I / 2) * conj (paperFT f (-I / 2))).re : ℝ) : ℂ) := by
    rw [EF.paperFT_weilTest hfc hfc hfs hfs, EF.paperFT_weilTest hfc hfc hfs hfs]
    have h1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
    have h2 : conj (-I / 2) = I / 2 := by rw [map_div₀, map_neg, Complex.conj_I, map_ofNat, neg_neg]
    rw [h1, h2]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hint : (∫ r : ℝ, paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ)) =
      ((∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    rw [EF.paperFT_weilTest hfc hfc hfs hfs, Complex.conj_ofReal, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  unfold WeilOneSided.weilArchRe archPoleEnergy
  rw [← hf, hp, hint]
  simp only [Complex.add_re, Complex.ofReal_re]
  rw [show ((1 / (2 * π) : ℂ) * ((∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ)) =
      (((1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

/-- On a compactly supported test the pole and archimedean energy is the zeta side plus the prime
pairing with `Λ`. -/
theorem archPoleEnergy_truncTest_eq {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (L : ℝ) :
    archPoleEnergy (truncTest F L) =
      (zetaZeroConfig.W (fun u => (truncTest F L u : ℂ)) (fun u => (truncTest F L u : ℂ))).re +
        atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (crossCorr (truncTest F L) (truncTest F L)) := by
  set f : ℝ → ℂ := fun u => (truncTest F L u : ℂ) with hf
  have hfd : ContDiff ℝ 2 f := contDiff_ofReal_truncTest hF L
  have hfs : HasCompactSupport f := (hasCompactSupport_truncTest F L).comp_left Complex.ofReal_zero
  have hk : EF.weilTest f f = fun y => ((crossCorr (truncTest F L) (truncTest F L) y : ℝ) : ℂ) :=
    funext fun y => weilTest_ofReal_eq (truncTest F L) y
  rw [← weilArchRe_weilTest_truncTest_eq hF L, zeta_W_eq_weilFullFunctional hfd hfs]
  have hsum : (∑' n : ℕ, ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
      else 0 : ℝ) : ℂ) * (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))) =
      ((atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (truncTest F L) (truncTest F L)) : ℝ) : ℂ) := by
    rw [atomPairing, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [hk]
    push_cast
    ring
  unfold WeilOneSided.weilArchRe weilFullFunctional
  rw [hsum]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  ring

/-- Chebyshev: the partial sums of `Λ` grow at most linearly. -/
theorem abs_primeWeightPartialSum_vonMangoldt_le (N : ℕ) :
    |primeWeightPartialSum (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) N| ≤ 7 * (N + 1) := by
  have hsplit : primeWeightPartialSum (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) N =
      ∑ m ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt m := by
    unfold primeWeightPartialSum
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with hm
    · rfl
    · have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl <;> simp
  have hpsi := RHTower.sum_range_vonMangoldt_eq_chebyshevPsi N
  have hpsi7 := RHTower.chebyshevPsi_le_seven N
  have hpsi0 : 0 ≤ ∑ m ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt m :=
    Finset.sum_nonneg fun m _ => ArithmeticFunction.vonMangoldt_nonneg
  rw [hsplit, abs_of_nonneg hpsi0]
  linarith

/-- **For a `Ξ`-divisible prime-blind test the truncated pole and archimedean energies tend to
`0`.** -/
theorem tendsto_archPoleEnergy_truncTest_of_xiDivisibleBlindTest {F : ℝ → ℝ}
    (hF : XiDivisibleBlindTest F) :
    Tendsto (fun L : ℝ => archPoleEnergy (truncTest F L)) atTop (𝓝 0) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hzeta : Tendsto (fun L : ℝ =>
      (zetaZeroConfig.W (fun u => (truncTest F L u : ℂ)) (fun u => (truncTest F L u : ℂ))).re)
      atTop (𝓝 0) := by
    have hb : Tendsto (fun L => (5 / 4) * zetaInvSqSum * tailBound F Λ L ^ 2) atTop (𝓝 0) := by
      simpa using ((tendsto_tailBound hF.1 hΛ0).pow 2).const_mul ((5 / 4) * zetaInvSqSum)
    refine squeeze_zero_norm (fun L => ?_) hb
    exact (Complex.abs_re_le_norm _).trans (norm_W_truncTest_le hF.1 hΛ hΛ0
      (paperFT_gammaOf_eq_zero_of_xiDivisibleBlindTest hF) L)
  have hprime := tendsto_atomPairing_truncTest hF.1 (A := 7)
    (fun N => abs_primeWeightPartialSum_vonMangoldt_le N) hF.2.1
  have h := hzeta.add hprime
  rw [add_zero] at h
  exact h.congr fun L => (archPoleEnergy_truncTest_eq hF.1.1 L).symm

/-- `log(2 + x) ≤ 2√(1 + x)` for `x ≥ 0`. -/
private theorem log_two_add_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log (2 + x) ≤ 2 * Real.sqrt (1 + x) := by
  have h2 : 0 < 2 + x := by linarith
  have hs : Real.sqrt (2 + x) ^ 2 = 2 + x := Real.sq_sqrt h2.le
  have hs1 : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt (by linarith)
  have hspos : 0 < Real.sqrt (2 + x) := Real.sqrt_pos.mpr h2
  have hlog : Real.log (2 + x) = 2 * Real.log (Real.sqrt (2 + x)) := by
    calc Real.log (2 + x) = Real.log (Real.sqrt (2 + x) ^ 2) := by rw [hs]
      _ = 2 * Real.log (Real.sqrt (2 + x)) := by rw [Real.log_pow]; norm_num
  have h1 : Real.log (Real.sqrt (2 + x)) ≤ Real.sqrt (2 + x) - 1 :=
    Real.log_le_sub_one_of_pos hspos
  have h3 : Real.sqrt (2 + x) ≤ 1 + Real.sqrt (1 + x) := by
    have h0 : 0 ≤ Real.sqrt (1 + x) := Real.sqrt_nonneg _
    nlinarith [Real.sqrt_nonneg (2 + x)]
  linarith

/-- The Gamma bracket grows at most like `√|r|`. -/
theorem abs_gammaBracket_le_sqrt (r : ℝ) :
    |EF.gammaBracket r| ≤ (digammaVerticalGrowthConst (1 / 4) + Real.log π) +
      2 * Real.sqrt (1 + |r|) := by
  rw [WeilHerglotz.gammaBracket_eq]
  have h1 := RHTower.abs_re_digamma_vertical_le (c := 1 / 4) (by norm_num) (r / 2)
  have hr2 : |r / 2| ≤ |r| := by
    rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]; linarith [abs_nonneg r]
  have hlog : Real.log (2 + |r / 2|) ≤ 2 * Real.sqrt (1 + |r|) :=
    (Real.log_le_log (by positivity) (by linarith)).trans (log_two_add_le_two_sqrt (abs_nonneg r))
  have hpi : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hab := abs_sub (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re
    (Real.log π)
  rw [abs_of_nonneg hpi] at hab
  linarith

/-- Uniform decay of the transforms of the truncations on the real line. -/
theorem one_add_abs_mul_norm_paperFT_truncTest_le {F : ℝ → ℝ} (hF : ExpDecayTest F) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) (hΛ0 : 0 ≤ Λ) (L r : ℝ) :
    (1 + |r|) * ‖paperFT (fun u => (truncTest F L u : ℂ)) r‖ ≤ ∫ u, tailMajorant F Λ u := by
  set L₀ : ℝ := min L 0 with hL₀
  have hz : |((r : ℂ)).im| ≤ 1 / 2 := by simp
  have h := one_add_abs_re_mul_norm_paperFT_truncTest_sub_le hF.1 hΛ
    (integrable_tailMajorant hF hΛ0) (min_le_left L 0) hz
  have h0 : (fun u => (truncTest F L₀ u : ℂ)) = fun _ => 0 := by
    funext u
    rw [truncTest_eq_zero (le_trans (min_le_right L 0) (abs_nonneg u))]
    simp
  have hft0 : paperFT (fun u => (truncTest F L₀ u : ℂ)) r = 0 := by
    rw [h0]; unfold paperFT; simp
  have htail : tailBound F Λ L₀ = ∫ u, tailMajorant F Λ u := by
    unfold tailBound
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have hu : u ∈ {u : ℝ | L₀ - 1 ≤ |u|} := by
      show L₀ - 1 ≤ |u|
      linarith [min_le_right L 0, abs_nonneg u]
    exact Set.indicator_of_mem hu _
  rw [hft0, zero_sub, norm_neg, htail, Complex.ofReal_re] at h
  exact h

/-- **The pole and archimedean energy is continuous under truncation.** -/
theorem tendsto_archPoleEnergy_truncTest {F : ℝ → ℝ} (hF : ExpDecayTest F) :
    Tendsto (fun L : ℝ => archPoleEnergy (truncTest F L)) atTop (𝓝 (archPoleEnergy F)) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  -- the pole part
  have hp : |((I / 2 : ℂ)).im| ≤ 1 / 2 := by simp
  have hm : |((-I / 2 : ℂ)).im| ≤ 1 / 2 := by simp [abs_div]
  have hpole := ((tendsto_paperFT_truncTest hF hp).mul
    ((Complex.continuous_conj.tendsto _).comp (tendsto_paperFT_truncTest hF hm)))
  have hpole' := ((Complex.continuous_re.tendsto _).comp hpole).const_mul 2
  -- the Gamma part, by dominated convergence
  set M : ℝ := ∫ u, tailMajorant F Λ u with hM
  set K : ℝ := digammaVerticalGrowthConst (1 / 4) + Real.log π with hK
  have hM0 : 0 ≤ M := integral_nonneg fun u => tailMajorant_nonneg F hΛ0 u
  have hK0 : 0 ≤ K := by
    have hpi : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have : 0 ≤ digammaVerticalGrowthConst (1 / 4) := by
      unfold digammaVerticalGrowthConst; positivity
    linarith
  have hbound_int : Integrable fun r : ℝ => M ^ 2 * (K + 2) * (1 + ‖r‖) ^ (-(3 / 2 : ℝ)) :=
    (integrable_one_add_norm (E := ℝ) (r := 3 / 2) (by norm_num)).const_mul _
  have hint := tendsto_integral_filter_of_dominated_convergence (l := atTop)
    (F := fun L (r : ℝ) => ‖paperFT (fun u => (truncTest F L u : ℂ)) (r : ℂ)‖ ^ 2 *
      EF.gammaBracket r)
    (f := fun r : ℝ => ‖paperFT (fun u => (F u : ℂ)) (r : ℂ)‖ ^ 2 * EF.gammaBracket r)
    (fun r : ℝ => M ^ 2 * (K + 2) * (1 + ‖r‖) ^ (-(3 / 2 : ℝ))) ?_ ?_ hbound_int ?_
  · unfold archPoleEnergy
    exact hpole'.add (hint.const_mul (1 / (2 * π)))
  · refine Eventually.of_forall fun L => ?_
    have hc : Continuous fun r : ℝ => paperFT (fun u => (truncTest F L u : ℂ)) r :=
      WeilHerglotz.continuous_paperFT_real
        ((contDiff_ofReal_truncTest hF.1 L).continuous.integrable_of_hasCompactSupport
          ((hasCompactSupport_truncTest F L).comp_left Complex.ofReal_zero))
    exact ((hc.norm.pow 2).mul WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable
  · refine Eventually.of_forall fun L => Eventually.of_forall fun r => ?_
    have hr0 : 0 < 1 + |r| := by positivity
    have hu := one_add_abs_mul_norm_paperFT_truncTest_le hF hΛ hΛ0 L r
    have hn : ‖paperFT (fun u => (truncTest F L u : ℂ)) r‖ ≤ M / (1 + |r|) := by
      rw [le_div_iff₀ hr0, mul_comm]; exact hu
    have hn2 : ‖paperFT (fun u => (truncTest F L u : ℂ)) r‖ ^ 2 ≤ M ^ 2 / (1 + |r|) ^ 2 := by
      rw [← div_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hg := abs_gammaBracket_le_sqrt r
    rw [← hK] at hg
    have hsq1 : 1 ≤ Real.sqrt (1 + |r|) := Real.one_le_sqrt.mpr (by linarith [abs_nonneg r])
    have hg' : |EF.gammaBracket r| ≤ (K + 2) * Real.sqrt (1 + |r|) := by nlinarith
    have hrpow : Real.sqrt (1 + |r|) / (1 + |r|) ^ 2 = (1 + ‖r‖) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.norm_eq_abs, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub hr0]
      norm_num
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    calc ‖paperFT (fun u => (truncTest F L u : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|
        ≤ M ^ 2 / (1 + |r|) ^ 2 * ((K + 2) * Real.sqrt (1 + |r|)) :=
          mul_le_mul hn2 hg' (abs_nonneg _) (by positivity)
      _ = M ^ 2 * (K + 2) * (Real.sqrt (1 + |r|) / (1 + |r|) ^ 2) := by ring
      _ = _ := by rw [hrpow]
  · refine Eventually.of_forall fun r => ?_
    have hz : |((r : ℂ)).im| ≤ 1 / 2 := by simp
    exact (((tendsto_paperFT_truncTest hF hz).norm.pow 2).mul_const _)

/-- **(N1) is a null vector of the zeta-free energy.**  A `Ξ`-divisible prime-blind test has
vanishing pole and archimedean energy.  So prime-blind positivity, if true, is attained on the
(N1) object, and strict positivity of `archPoleEnergy` on nonzero prime-blind tests of the decay
class would rule (N1) out. -/
theorem archPoleEnergy_eq_zero_of_xiDivisibleBlindTest {F : ℝ → ℝ}
    (hF : XiDivisibleBlindTest F) : archPoleEnergy F = 0 :=
  tendsto_nhds_unique (tendsto_archPoleEnergy_truncTest hF.1)
    (tendsto_archPoleEnergy_truncTest_of_xiDivisibleBlindTest hF)

end RHTower.WeilSpectral
