import GaloisForLFunctions.ArithmeticPolarization.TheCollidedFormIsAPolarization
import GaloisForLFunctions.RHTower.LittlewoodShortWindowZeroCount
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon
import GaloisForLFunctions.RHTower.RiemannKernelStripLPMaximality

/-!
# The collided form samples high frequencies

For a `C²` test supported in `[−A, A]` Weil's form of `ζ` is the integral of `|f̂(τ)|²` against the
density `ν_X = μ + Π_X + P_X`, `X = e^{2A}` (the explicit formula, `Zeta23.paperInputs_zeta`), and
`|ν_X − μ| ≤ 3X²`. The archimedean density `μ` grows like `log|τ|/2π`.

* **Gårding inequality** (`re_W_ge_sub_lowMass`, `collidedForm_ge_sub_lowMass`): for every aperture
  `A` there are `T₀` and `K` with `Re W(f) ≥ 2π‖f‖₂² − K ∫_{−T₀}^{T₀} |f̂|²` for every such test,
  hence the same for `D ≥ Re W`. Above `T₀` the density exceeds `1`.

The collided form therefore controls the `L²` norm up to the low-frequency mass, a compact
functional of the test: the polarization is coercive modulo a compact term at every aperture.
-/

open Complex MeasureTheory Set Filter Topology Real
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

/-- The low-frequency mass `∫_{−T}^{T} |f̂(τ)|² dτ`. -/
def lowMass (T : ℝ) (f : ℝ → ℂ) : ℝ := ∫ τ in Icc (-T) T, ‖paperFT f τ‖ ^ 2

theorem lowMass_nonneg (T : ℝ) (f : ℝ → ℂ) : 0 ≤ lowMass T f :=
  setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _

theorem integrable_norm_sq_paperFT_of_tests {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 :=
  RHTower.KernelStrip.integrable_norm_sq_paperFT (hf.continuous.integrable_of_hasCompactSupport hfc)
    (hf.continuous.memLp_of_hasCompactSupport hfc)

/-- **Weil's form as a density integral.** -/
theorem re_W_eq_integral_nuX {A : ℝ} (hA : 0 < A) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-A) A) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * nuX (Real.exp (2 * A)) τ) ∧
      (zetaZeroConfig.W f f).re = ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * nuX (Real.exp (2 * A)) τ := by
  have hfs' : tsupport f ⊆ Icc (-(2 * A / 2)) (2 * A / 2) := by
    rwa [show 2 * A / 2 = A by ring]
  obtain ⟨-, hi, he⟩ := paperInputs_zeta.EF (2 * A) (by positivity) f f hf hf hfs' hfs'
  have hpt : (fun τ : ℝ => paperFT f τ * conj (paperFT f τ) * (nuX (Real.exp (2 * A)) τ : ℂ)) =
      fun τ : ℝ => ((‖paperFT f τ‖ ^ 2 * nuX (Real.exp (2 * A)) τ : ℝ) : ℂ) := by
    funext τ
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [hpt] at hi he
  refine ⟨hi.re, ?_⟩
  rw [he, integral_complex_ofReal, Complex.ofReal_re]

/-- **Gårding inequality for Weil's form.** -/
theorem re_W_ge_sub_lowMass {A : ℝ} (hA : 0 < A) :
    ∃ T₀ K : ℝ, 1 ≤ T₀ ∧ 0 ≤ K ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-A) A →
      2 * π * (∫ u, ‖f u‖ ^ 2) - K * lowMass T₀ f ≤ (zetaZeroConfig.W f f).re := by
  set X := Real.exp (2 * A) with hXdef
  have hX : 1 ≤ X := Real.one_le_exp (by positivity)
  obtain ⟨C, hC0, hC⟩ := RHTower.Littlewood.exists_stirling
  set T₀ := 2 * π * Real.exp (2 * π * (3 * X ^ 2 + 1 + C)) with hT₀def
  have hπ := Real.pi_pos
  have hT₀ : 1 ≤ T₀ := by
    have h1 : 1 ≤ Real.exp (2 * π * (3 * X ^ 2 + 1 + C)) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
    nlinarith
  -- the archimedean density at `T₀`
  have hμT₀ : 3 * X ^ 2 + 1 ≤ mu T₀ := by
    have h := hC T₀ (by rw [abs_of_pos (by linarith)]; exact hT₀)
    have hlog : (1 / (2 * π)) * Real.log (|T₀| / (2 * π)) = 3 * X ^ 2 + 1 + C := by
      rw [abs_of_pos (by linarith), hT₀def, mul_div_cancel_left₀ _ (by positivity),
        Real.log_exp]
      field_simp
    rw [hlog] at h
    have hCT : C / T₀ ^ 2 ≤ C := div_le_self hC0 (by nlinarith)
    linarith [(abs_le.mp h).1]
  set m₀ := mu T₀ - 3 * X ^ 2 with hm₀
  set K := mu T₀ + 1 with hK
  have hm₀1 : 1 ≤ m₀ := by linarith
  have hX2 : 0 ≤ 3 * X ^ 2 := by positivity
  refine ⟨T₀, K, hT₀, by linarith, fun f hf hfs => ?_⟩
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  obtain ⟨hint, hre⟩ := re_W_eq_integral_nuX hA hf hfs
  rw [← hXdef] at hint hre
  have hF := integrable_norm_sq_paperFT_of_tests hf hfc
  -- the density is at least `m₀` above `T₀` and at least `m₀ − K` below
  set ind : ℝ → ℝ := (Icc (-T₀) T₀).indicator fun _ => (1 : ℝ) with hind
  have hpt : ∀ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (m₀ - K * ind τ) ≤
      ‖paperFT f τ‖ ^ 2 * nuX X τ := by
    intro τ
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hν := (abs_le.mp (RHTower.Littlewood.abs_nuX_sub_mu_le hX τ)).1
    by_cases hτ : τ ∈ Icc (-T₀) T₀
    · rw [hind, Set.indicator_of_mem hτ, mul_one]
      have := RHTower.Littlewood.neg_one_lt_mu τ
      linarith
    · rw [hind, Set.indicator_of_notMem hτ, mul_zero, sub_zero]
      have hT : |T₀| ≤ |τ| := by
        rw [abs_of_pos (by linarith)]
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hτ
        rcases hτ with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h.le
      have := RHTower.Littlewood.mu_le_of_abs_le hT
      linarith
  have hindInt : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * ind τ := by
    have : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * ind τ) =
        (Icc (-T₀) T₀).indicator fun τ => ‖paperFT f τ‖ ^ 2 := by
      funext τ; rw [hind]
      by_cases hτ : τ ∈ Icc (-T₀) T₀
      · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ, mul_one]
      · rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hτ, mul_zero]
    rw [this]; exact hF.indicator measurableSet_Icc
  have hlow : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * ind τ = lowMass T₀ f := by
    have : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * ind τ) =
        (Icc (-T₀) T₀).indicator fun τ => ‖paperFT f τ‖ ^ 2 := by
      funext τ; rw [hind]
      by_cases hτ : τ ∈ Icc (-T₀) T₀
      · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ, mul_one]
      · rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hτ, mul_zero]
    rw [this, integral_indicator measurableSet_Icc, lowMass]
  have hlower : m₀ * (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2) - K * lowMass T₀ f ≤
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * nuX X τ := by
    have hsplit : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (m₀ - K * ind τ) =
        m₀ * (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2) - K * lowMass T₀ f := by
      have : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * (m₀ - K * ind τ)) =
          fun τ : ℝ => m₀ * ‖paperFT f τ‖ ^ 2 - K * (‖paperFT f τ‖ ^ 2 * ind τ) := by
        funext τ; ring
      rw [this, integral_sub (hF.const_mul _) (hindInt.const_mul _), integral_const_mul,
        integral_const_mul, hlow]
    rw [← hsplit]
    exact integral_mono ((hF.const_mul m₀).sub (hindInt.const_mul K) |>.congr
      (Filter.Eventually.of_forall fun τ => by simp only [Pi.sub_apply]; ring)) hint hpt
  have hplan := RHTower.integral_norm_sq_paperFT_eq hf hfs
  have htot : 0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 ≤ m₀ * (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2) :=
    le_mul_of_one_le_left htot hm₀1
  linarith [hplan]

/-- **Gårding inequality for the collided form.** -/
theorem collidedForm_ge_sub_lowMass {A : ℝ} (hA : 0 < A) :
    ∃ T₀ K : ℝ, 1 ≤ T₀ ∧ 0 ≤ K ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-A) A →
      2 * π * (∫ u, ‖f u‖ ^ 2) - K * lowMass T₀ f ≤ collidedForm zetaZeroConfig f := by
  obtain ⟨T₀, K, hT₀, hK, h⟩ := re_W_ge_sub_lowMass hA
  refine ⟨T₀, K, hT₀, hK, fun f hf hfs => (h f hf hfs).trans ?_⟩
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  exact re_W_le_collided (zeta_summable_collided hf hfc)

end GaloisForLFunctions.ArithmeticPolarization
