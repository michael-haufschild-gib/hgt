import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheDilationQuotientReadsTheInnerMass
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheEulerColumnsOfTheInnerField
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheFixedBaseConeAndCriticalBernstein
import GaloisForLFunctions.HTGeometry.HalfPlanePoissonBoundedReproduction
import GaloisForLFunctions.RHTower.ZetaCriticalLineWeightedSecondMoment

/-!
# Mollified log-dilation bridges and prime-side Selberg–Hankel defect at fixed shift

`TheDilationQuotientReadsTheInnerMass` proves that every single horizontal shift `δ ∈ (0, ½)`
decides the Riemann Hypothesis via the logarithmic Poisson mean of `|ζ(½ + iτ) / ζ(½ + δ + iτ)|`.
This module couples that macroscopic single-shift bridge with Szegő mollifiers, outer Euler-prefix
mollifiers, Dirichlet-polynomial Poisson Gram matrices, and prime-side `dirichletHankelForm`
quadratic forms on `Re s = ½ + δ`:

1. **Shifted Plancherel second moment, shifted Szegő infimum, and variational dilation ratio
   (`integrable_norm_sq_zeta_shifted_poisson`, `isGLB_shiftedBudget_innerField`,
   `exp_two_dilation_drop_eq_szego_ratio`, `riemannHypothesis_iff_szego_budget_ratio_eq`).**
   Plancherel on `φ_δ(u) = e^{−(1/2 + δ)u} {e^u}` proves `ζ(½ + δ + iτ) ∈ L²(P_w dτ)` for every
   `δ ∈ (−½, ½)` and `Re w > ½`. Applying `isGLB_circleAverage` on `Re s = ½ + δ` (`δ ∈ (0, ½)`)
   identifies `exp(2(I(1) − I_δ(1)))` as the normalized ratio of critical-to-shifted Szegő second-moment
   budget infima, yielding an unconditional single-shift `L²` variational RH criterion.

2. **Outer Euler-prefix mollification and prime cancellation
   (`eulerMollifier_ne_zero`, `integral_log_eulerMollifier_shifted`,
   `eulerMollified_log_dilation_quotient_eq`).**
   Every finite Euler prefix `∏_{p ∈ S} (1 − p^{−s})` (`p ≥ 2`) is outer and nonvanishing on
   `Re s ≥ ½`, reproduces its centre value under `P_w` on both `Re s = ½` and `Re s = ½ + δ`, and
   cancels prime factors identically inside the log-dilation bridge while leaving `I(1) − I_δ(1)`
   completely invariant.

3. **Shifted Poisson Gram matrix and Abel partial-sum coercivity of Dirichlet polynomials
   (`integral_cos_mul_halfPlanePoissonKernel_one`, `integral_dirichletPoly_norm_sq_poisson`,
   `dirichletGram_eq_abel_squares`).**
   Against `P₁(τ) = (2π)⁻¹ / (¼ + τ²)`, `∫ cos(ξτ) P₁(τ) dτ = e^{−|ξ|/2}`, so every Dirichlet
   polynomial `∑_{m=1}^M b_m m^{−s}` on `Re s = ½ + δ` has exact Poisson second moment
   `∑_{m,n=1}^M (b_m m^{−δ})(b_n n^{−δ}) / max(m, n)`, which equals the strictly positive-definite
   Abel sum of partial-sum squares.

4. **Prime-side Selberg–Cholesky diagonalization and the `δ → 0⁺` cancellation defect
   (`dirichletHankel_eulerAmpl_eq_sum_sq`, `dirichletHankel_eulerAmpl_ge_selberg`,
   `dirichletHankel_selbergArray_eq`, `eulerHankel_pos_floor_of_pos`,
   `exists_eulerHankel_lt_of_critical`, `hasDerivAt_log_eulerHankel_min`,
   `not_summable_primes_log_div_add_one`).**
   For the multiplicative Euler amplitude `eulerAmpl p σ k = ∏_i (p_i^{−σ})^{k_i}`,
   `dirichletHankelForm (eulerAmpl p σ) N c` diagonalizes into a sum of squares whose exact minimum
   over `{c | supp c ⊆ piBox n N, c 0 = 1}` (`N ≥ 2`) is `∏_i (1 + p_i^{−2σ})⁻¹`, attained on the
   squarefree Selberg sieve array already at `N = 2`. At `σ = ½ + δ` (`δ > 0`) this minimum has the
   prime-independent floor `exp(−∑'_m m^{−(1+2δ)}) > 0`; at `δ = 0` its infimum over finite prime
   sets collapses to `0`, and the logarithmic slope at `δ = 0` is `2 ∑_i log p_i / (p_i + 1)`, whose
   series over `Nat.Primes` diverges.
-/

open Filter Topology MeasureTheory Set Finset Complex
open scoped Real ENNReal ComplexConjugate FourierTransform

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GaloisForLFunctions.HTGeometry
open _root_.RHTower

noncomputable section

local notation "𝕋" => AddCircle (2 * π)

/-! ### 1. Shifted Plancherel second moment, shifted Szegő infimum, and variational ratio -/

/-- Shifted fractional-part pullback `φ_δ(u) = e^{−(1/2 + δ)u} {e^u}` on `ℝ`. -/
def shiftedFractLogPull (δ u : ℝ) : ℂ :=
  ((Real.exp (-(1 / 2 + δ) * u) * Int.fract (Real.exp u) : ℝ) : ℂ)

theorem norm_shiftedFractLogPull (δ u : ℝ) :
    ‖shiftedFractLogPull δ u‖ = Real.exp (-(1 / 2 + δ) * u) * Int.fract (Real.exp u) := by
  rw [shiftedFractLogPull, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _))]

theorem norm_shiftedFractLogPull_le (δ u : ℝ) :
    ‖shiftedFractLogPull δ u‖ ≤ Real.exp (-min (1 / 2 + δ) (1 / 2 - δ) * |u|) := by
  rw [norm_shiftedFractLogPull]
  set η : ℝ := min (1 / 2 + δ) (1 / 2 - δ)
  have h1 := (Int.fract_lt_one (Real.exp u)).le
  have h2 : Int.fract (Real.exp u) ≤ Real.exp u := by
    have hf := Int.floor_nonneg.mpr (Real.exp_pos u).le
    unfold Int.fract
    have : (0 : ℝ) ≤ (⌊Real.exp u⌋ : ℝ) := by exact_mod_cast hf
    linarith
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    have hη1 : η ≤ 1 / 2 + δ := min_le_left _ _
    calc Real.exp (-(1 / 2 + δ) * u) * Int.fract (Real.exp u)
        ≤ Real.exp (-(1 / 2 + δ) * u) * 1 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ ≤ Real.exp (-η * u) := by rw [mul_one]; exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [abs_of_neg hu]
    have hη2 : η ≤ 1 / 2 - δ := min_le_right _ _
    calc Real.exp (-(1 / 2 + δ) * u) * Int.fract (Real.exp u)
        ≤ Real.exp (-(1 / 2 + δ) * u) * Real.exp u :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = Real.exp ((1 / 2 - δ) * u) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-η * -u) := Real.exp_le_exp.mpr (by nlinarith)

theorem measurable_shiftedFractLogPull (δ : ℝ) : Measurable (shiftedFractLogPull δ) :=
  Complex.measurable_ofReal.comp
    ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (measurable_fract.comp Real.measurable_exp))

theorem integrable_shiftedFractLogPull {δ : ℝ} (hδ_lo : -1 / 2 < δ) (hδ_hi : δ < 1 / 2) :
    Integrable (shiftedFractLogPull δ) := by
  set η : ℝ := min (1 / 2 + δ) (1 / 2 - δ)
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have h : Integrable (fun u : ℝ => Real.exp (-η * |u|)) :=
    (_root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hη).congr
      (Eventually.of_forall fun u => by simp)
  exact h.mono' (measurable_shiftedFractLogPull δ).aestronglyMeasurable
    (Eventually.of_forall fun u => norm_shiftedFractLogPull_le δ u)

theorem memLp_two_shiftedFractLogPull {δ : ℝ} (hδ_lo : -1 / 2 < δ) (hδ_hi : δ < 1 / 2) :
    MemLp (shiftedFractLogPull δ) 2 := by
  rw [memLp_two_iff_integrable_sq_norm (measurable_shiftedFractLogPull δ).aestronglyMeasurable]
  refine (integrable_shiftedFractLogPull hδ_lo hδ_hi).norm.mono'
    ((measurable_shiftedFractLogPull δ).norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  have hub : ‖shiftedFractLogPull δ u‖ ≤ 1 := by
    refine (norm_shiftedFractLogPull_le δ u).trans (Real.exp_le_one_iff.mpr ?_)
    have hη : 0 < min (1 / 2 + δ) (1 / 2 - δ) := lt_min (by linarith) (by linarith)
    have := abs_nonneg u
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg (shiftedFractLogPull δ u)]

theorem integral_norm_sq_shiftedFractLogPull_pos {δ : ℝ} (hδ_lo : -1 / 2 < δ)
    (hδ_hi : δ < 1 / 2) :
    0 < ∫ u : ℝ, ‖shiftedFractLogPull δ u‖ ^ 2 := by
  have hint_sq : Integrable (fun u : ℝ => ‖shiftedFractLogPull δ u‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (measurable_shiftedFractLogPull δ).aestronglyMeasurable).mp
      (memLp_two_shiftedFractLogPull hδ_lo hδ_hi)
  have hnn : 0 ≤ ∫ u : ℝ, ‖shiftedFractLogPull δ u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  refine lt_of_le_of_ne hnn fun h0 => ?_
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
    hint_sq).mp h0.symm
  have hvol0 : volume {u : ℝ | ‖shiftedFractLogPull δ u‖ ^ 2 ≠ 0} = 0 := ae_iff.mp hae
  set a : ℝ := Real.log (3 / 2)
  set b : ℝ := Real.log (7 / 4)
  have hab : a < b := Real.log_lt_log (by norm_num) (by norm_num)
  have hsub : Ioo a b ⊆ {u : ℝ | ‖shiftedFractLogPull δ u‖ ^ 2 ≠ 0} := fun u hu => by
    have hexp_lo : (3 / 2 : ℝ) < Real.exp u := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]; exact Real.exp_lt_exp.mpr hu.1
    have hexp_hi : Real.exp u < 7 / 4 := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 7 / 4)]; exact Real.exp_lt_exp.mpr hu.2
    have hfl : ⌊Real.exp u⌋ = 1 :=
      Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    have hfr_pos : 0 < Int.fract (Real.exp u) := by
      unfold Int.fract; rw [hfl]; push_cast; linarith
    have hn_pos : 0 < ‖shiftedFractLogPull δ u‖ := by
      rw [norm_shiftedFractLogPull]; positivity
    exact (pow_pos hn_pos 2).ne'
  have hvol_pos : 0 < volume (Ioo a b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  have hle0 : volume (Ioo a b) ≤ 0 := (measure_mono hsub).trans_eq hvol0
  exact lt_irrefl (0 : ℝ≥0∞) (hvol_pos.trans_le hle0)

/-- **Shifted Mellin–Fourier identity inside the critical strip (`δ ∈ (−½, ½)`).** -/
theorem fourier_shiftedFractLogPull {δ : ℝ} (hδ_lo : -1 / 2 < δ) (hδ_hi : δ < 1 / 2) (t : ℝ) :
    𝓕 (shiftedFractLogPull δ) (t / (2 * π)) =
      -(riemannZeta (1 / 2 + (δ : ℂ) + t * I) / (1 / 2 + (δ : ℂ) + t * I)) := by
  set s : ℂ := 1 / 2 + (δ : ℂ) + t * I with hs
  have hre : s.re = 1 / 2 + δ := by simp [hs]
  have him : s.im = t := by simp [hs]
  have h := mellin_eq_fourier (fun y : ℝ => ((Int.fract y⁻¹ : ℝ) : ℂ)) (s := s)
  rw [hre, him] at h
  have hfun : (fun u : ℝ => Real.exp (-(1 / 2 + δ) * u) • ((Int.fract (Real.exp (-u))⁻¹ : ℝ) : ℂ)) =
      shiftedFractLogPull δ := by
    funext u
    rw [shiftedFractLogPull, Complex.real_smul, ← Real.exp_neg, neg_neg]
    push_cast; ring_nf
  rw [hfun] at h
  rw [← h]
  have hm := mellin_comp_inv (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) s
  rw [hm, mellin, ← integral_Ioi_zero_fract_cpow (w := s) (by rw [hre]; linarith)
    (by rw [hre]; linarith)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [smul_eq_mul]
  rw [show (-s - 1 : ℂ) = -(s + 1) by ring, mul_comm]

/-- Plancherel weighted second moment of `ζ` on every vertical line `Re s = ½ + δ` inside the
critical strip (`δ ∈ (−½, ½)`). -/
theorem integrable_norm_sq_zeta_shiftedLine {δ : ℝ} (hδ_lo : -1 / 2 < δ) (hδ_hi : δ < 1 / 2) :
    Integrable (fun τ : ℝ =>
      ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ ^ 2 / ((1 / 2 + δ) ^ 2 + τ ^ 2)) := by
  have hπ : 0 < 2 * π := by positivity
  have hP := GaloisForLFunctions.HTGeometry.integral_norm_sq_fourier
    (integrable_shiftedFractLogPull hδ_lo hδ_hi) (memLp_two_shiftedFractLogPull hδ_lo hδ_hi)
  have hFint : Integrable (fun ξ : ℝ => ‖𝓕 (shiftedFractLogPull δ) ξ‖ ^ 2) := by
    by_contra hni
    rw [integral_undef hni] at hP
    exact (integral_norm_sq_shiftedFractLogPull_pos hδ_lo hδ_hi).ne' hP.symm
  have hpt : ∀ τ : ℝ,
      ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ ^ 2 / ((1 / 2 + δ) ^ 2 + τ ^ 2) =
        ‖𝓕 (shiftedFractLogPull δ) (τ / (2 * π))‖ ^ 2 := fun τ => by
    rw [fourier_shiftedFractLogPull hδ_lo hδ_hi, norm_neg, norm_div, div_pow]
    congr 1
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp; ring
  simp_rw [hpt]
  exact hFint.comp_div hπ.ne'

/-- **Shifted Poisson second-moment integrability (`δ ∈ (−½, ½)`, `Re w > ½`).** -/
theorem integrable_norm_sq_zeta_shifted_poisson {δ : ℝ} (hδ_lo : -1 / 2 < δ) (hδ_hi : δ < 1 / 2)
    {w : ℂ} (hw : 1 / 2 < w.re) :
    Integrable (fun τ : ℝ =>
      ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ ^ 2 * halfPlanePoissonKernel w τ) := by
  obtain ⟨C, hC0, hC⟩ := exists_poissonKernel_le_one hw
  set K_δ : ℝ := max 1 (4 * (1 / 2 + δ) ^ 2)
  have h1 := (integrable_norm_sq_zeta_shiftedLine hδ_lo hδ_hi).mul_const (C * (2 * π)⁻¹ * K_δ)
  refine h1.mono' ?_ (Eventually.of_forall fun τ => ?_)
  · have hk : Measurable (fun τ : ℝ => halfPlanePoissonKernel w τ) := by
      unfold halfPlanePoissonKernel; fun_prop
    have hz : Measurable (fun τ : ℝ => ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖) :=
      (measurable_riemannZeta.comp (by fun_prop)).norm
    exact ((hz.pow_const 2).mul hk).aestronglyMeasurable
  · have hP := hC τ
    have hP0 := (halfPlanePoissonKernel_pos hw τ).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hP0)]
    rw [halfPlanePoissonKernel_one] at hP
    have hden_cmp : (1 / 2 + δ) ^ 2 + τ ^ 2 ≤ K_δ * (1 / 4 + τ ^ 2) := by
      have hK1 : 1 ≤ K_δ := le_max_left _ _
      have hK2 : 4 * (1 / 2 + δ) ^ 2 ≤ K_δ := le_max_right _ _
      nlinarith [sq_nonneg τ]
    have hinv_cmp : 1 / (1 / 4 + τ ^ 2) ≤ K_δ / ((1 / 2 + δ) ^ 2 + τ ^ 2) := by
      have hd1 : 0 < 1 / 4 + τ ^ 2 := by positivity
      have h12 : 0 < 1 / 2 + δ := by linarith
      have hd2 : 0 < (1 / 2 + δ) ^ 2 + τ ^ 2 := by positivity
      rw [div_le_div_iff₀ hd1 hd2, one_mul]
      exact hden_cmp
    calc ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ ^ 2 * halfPlanePoissonKernel w τ
        ≤ ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ ^ 2 *
            (C * ((2 * π)⁻¹ * (1 / (1 / 4 + τ ^ 2)))) :=
          mul_le_mul_of_nonneg_left hP (sq_nonneg _)
      _ ≤ ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ ^ 2 *
            (C * ((2 * π)⁻¹ * (K_δ / ((1 / 2 + δ) ^ 2 + τ ^ 2)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hinv_cmp (by positivity)) hC0) (sq_nonneg _)
      _ = ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ ^ 2 / ((1 / 2 + δ) ^ 2 + τ ^ 2) *
            (C * (2 * π)⁻¹ * K_δ) := by ring

/-- Shifted mollifier budget on `Re s = ½ + δ` against `exp Q(φ_w(½ + iτ))`. -/
def shiftedBudget (δ : ℝ) (w : ℂ) (Q : Polynomial ℂ) : ℝ :=
  ∫ τ : ℝ, ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ ^ 2 *
    ‖Complex.exp (Q.eval (blaschkeCoord w (1 / 2 + τ * I)))‖ ^ 2 * halfPlanePoissonKernel w τ

/-- Shifted boundary weight in the disc chart of `w`. -/
def shiftedChartWeight (δ : ℝ) (w z : ℂ) : ℝ :=
  ‖riemannZeta (discChart w z + (δ : ℂ))‖ ^ 2

theorem measurable_shiftedChartWeight (δ : ℝ) (w : ℂ) :
    Measurable (shiftedChartWeight δ w) :=
  (measurable_riemannZeta.comp ((measurable_discChart w).add measurable_const)).norm.pow_const 2

theorem ae_shiftedChartWeight_pos (δ : ℝ) {w : ℂ} (hw : 1 / 2 < w.re) :
    ∀ᵐ x : 𝕋 ∂AddCircle.haarAddCircle, 0 < shiftedChartWeight δ w (circleZ x) := by
  have hinj : Function.Injective (fun s : ℂ => s + (δ : ℂ)) := fun a b hab => add_right_cancel hab
  have hzeros : {s : ℂ | riemannZeta (s + (δ : ℂ)) = 0}.Countable :=
    countable_zeta_zeros.preimage hinj
  have hA : ((blaschkeCoord w '' {s : ℂ | riemannZeta (s + (δ : ℂ)) = 0}) ∪ {1}).Countable :=
    (hzeros.image _).union (countable_singleton _)
  filter_upwards [ae_circleZ_notMem_of_countable hA] with x hx
  have hz1 : circleZ x ≠ 1 := fun h => hx (Or.inr h)
  have hne : riemannZeta (discChart w (circleZ x) + (δ : ℂ)) ≠ 0 := fun h0 =>
    hx (Or.inl ⟨_, h0, blaschkeCoord_discChart hw hz1⟩)
  exact pow_pos (norm_pos_iff.mpr hne) 2

/-- **Shifted Szegő infimum on `Re s = ½ + δ` (`0 ≤ δ < ½`).** -/
theorem isGLB_shiftedBudget {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) {w : ℂ} (hw : 1 / 2 < w.re)
    (h0 : zetaEntire (w + (δ : ℂ)) ≠ 0) :
    IsGLB (shiftedBudget δ w '' {Q | Q.coeff 0 = 0})
      (Real.exp (2 * ∫ τ : ℝ,
        Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ * halfPlanePoissonKernel w τ)) := by
  have hline_pt : ∀ t : ℝ,
      discChart w (circleMap 0 1 (criticalLineAngle t)) + (δ : ℂ) =
        1 / 2 + (δ : ℂ) + (((2 * w.re - 1) * t + w.im : ℝ) : ℂ) * I := fun t => by
    rw [discChart_circleMap]; ring
  have hinte := circleAverage_shift_eq_poisson hw
    (fun τ => ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ ^ 2) (shiftedChartWeight δ w)
    (fun t => by simp only [shiftedChartWeight, hline_pt])
  have hloge := circleAverage_shift_eq_poisson hw
    (fun τ => 2 * Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖)
    (fun z => Real.log (shiftedChartWeight δ w z))
    (fun t => by simp only [shiftedChartWeight, hline_pt, Real.log_pow]; norm_num)
  have hlogi : Integrable (fun τ : ℝ =>
      (2 * Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖) * halfPlanePoissonKernel w τ) := by
    have := ((hasSum_shiftedInnerField hδ0 hδ1.le hw h0).1).const_mul 2
    exact this.congr (Eventually.of_forall fun τ => by simp only; ring)
  have h := isGLB_circleAverage (measurable_shiftedChartWeight δ w)
    (ae_shiftedChartWeight_pos δ hw)
    (hinte.1.mpr (integrable_norm_sq_zeta_shifted_poisson (by linarith) hδ1 hw))
    (hloge.1.mpr hlogi)
  have e1 : Real.circleAverage (fun z => Real.log (shiftedChartWeight δ w z)) 0 1 =
      2 * ∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ * halfPlanePoissonKernel w τ := by
    rw [hloge.2, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun τ => by simp only; ring)
  have e2 : (fun Q : Polynomial ℂ =>
      Real.circleAverage (fun z => shiftedChartWeight δ w z * ‖Complex.exp (Q.eval z)‖ ^ 2) 0 1) =
        shiftedBudget δ w := by
    funext Q
    have hQ := circleAverage_shift_eq_poisson hw
      (fun τ => ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ ^ 2 *
        ‖Complex.exp (Q.eval (blaschkeCoord w (1 / 2 + τ * I)))‖ ^ 2)
      (fun z => shiftedChartWeight δ w z * ‖Complex.exp (Q.eval z)‖ ^ 2)
      (fun t => by simp only [shiftedChartWeight, hline_pt, blaschkeCoord_line hw])
    rw [hQ.2, shiftedBudget]
  rwa [e1, e2] at h

/-- **Shifted Szegő infimum in terms of `shiftedInnerField δ w`.** -/
theorem isGLB_shiftedBudget_innerField {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2)
    {w : ℂ} (hw : 1 / 2 < w.re) (h0 : zetaEntire (w + (δ : ℂ)) ≠ 0) :
    IsGLB (shiftedBudget δ w '' {Q | Q.coeff 0 = 0})
      (Real.exp (2 * shiftedInnerField δ w) * (‖zetaEntire (w + (δ : ℂ))‖ / ‖w - (δ : ℂ)‖) ^ 2) := by
  have hwδ_ne : w - (δ : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h := isGLB_shiftedBudget hδ0 hδ1 hw h0
  have hint_eq : (∫ τ : ℝ,
      Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖ * halfPlanePoissonKernel w τ) =
      shiftedInnerField δ w + (Real.log ‖zetaEntire (w + (δ : ℂ))‖ - Real.log ‖w - (δ : ℂ)‖) := by
    rw [shiftedInnerField]; ring
  rw [hint_eq] at h
  convert h using 1
  have hE : 0 < ‖zetaEntire (w + (δ : ℂ))‖ := norm_pos_iff.mpr h0
  have hw' : 0 < ‖w - (δ : ℂ)‖ := norm_pos_iff.mpr hwδ_ne
  rw [mul_add, Real.exp_add, mul_sub, Real.exp_sub]
  congr 1
  rw [show (2 : ℝ) * Real.log ‖zetaEntire (w + (δ : ℂ))‖ =
      Real.log (‖zetaEntire (w + (δ : ℂ))‖ ^ 2) by rw [Real.log_pow]; norm_num,
    show (2 : ℝ) * Real.log ‖w - (δ : ℂ)‖ =
      Real.log (‖w - (δ : ℂ)‖ ^ 2) by rw [Real.log_pow]; norm_num,
    Real.exp_log (by positivity), Real.exp_log (by positivity), div_pow]

/-- Shifted Szegő infimum at `w = 1` for `δ ∈ (0, ½)`. -/
theorem isGLB_shiftedBudget_one {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    IsGLB (shiftedBudget δ 1 '' {Q | Q.coeff 0 = 0})
      (Real.exp (2 * shiftedInnerField δ 1) *
        (δ * ‖riemannZeta (1 + (δ : ℂ))‖ / (1 - δ)) ^ 2) := by
  have hw1 : (1 / 2 : ℝ) < (1 : ℂ).re := by simp; norm_num
  have h1δ_re : 1 ≤ ((1 : ℂ) + (δ : ℂ)).re := by simp; linarith
  have hzeta_ne : riemannZeta (1 + (δ : ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1δ_re
  have hE_ne : zetaEntire ((1 : ℂ) + (δ : ℂ)) ≠ 0 := zetaEntire_ne_zero_of_zeta_ne_zero hzeta_ne
  have h := isGLB_shiftedBudget_innerField hδ0.le hδ1 hw1 hE_ne
  have h1_sub : ‖(1 : ℂ) - (δ : ℂ)‖ = 1 - δ := by
    have hc : (1 : ℂ) - (δ : ℂ) = ((1 - δ : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hE_val : ‖zetaEntire ((1 : ℂ) + (δ : ℂ))‖ = δ * ‖riemannZeta (1 + (δ : ℂ))‖ := by
    have hne1 : (1 : ℂ) + (δ : ℂ) ≠ 1 := by
      intro heq; have := congrArg Complex.re heq; simp at this; linarith
    rw [zetaEntire_eq hne1, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hδ0.le]
  rwa [h1_sub, hE_val] at h

/-- **Exact Szegő variational representation of the inner-mass drop `exp(2(I(1) − I_δ(1)))`.** -/
theorem exp_two_dilation_drop_eq_szego_ratio {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    Real.exp (2 * (innerField 1 - shiftedInnerField δ 1)) =
      (δ * ‖riemannZeta (1 + (δ : ℂ))‖ / (1 - δ)) ^ 2 *
        (sInf (budget 1 '' {Q | Q.coeff 0 = 0}) /
          sInf (shiftedBudget δ 1 '' {Q | Q.coeff 0 = 0})) := by
  have hne0 : (budget 1 '' {Q | Q.coeff 0 = 0}).Nonempty := ⟨_, 0, by simp, rfl⟩
  have hneδ : (shiftedBudget δ 1 '' {Q | Q.coeff 0 = 0}).Nonempty := ⟨_, 0, by simp, rfl⟩
  have hs0 := isGLB_budget_one.csInf_eq hne0
  have hsδ := (isGLB_shiftedBudget_one hδ0 hδ1).csInf_eq hneδ
  have h1δ_re : 1 ≤ ((1 : ℂ) + (δ : ℂ)).re := by simp; linarith
  have hzeta_pos : 0 < ‖riemannZeta (1 + (δ : ℂ))‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re h1δ_re)
  have h1δ_ne : 1 - δ ≠ 0 := by linarith
  have hfac_pos : 0 < (δ * ‖riemannZeta (1 + (δ : ℂ))‖ / (1 - δ)) ^ 2 :=
    pow_pos (div_pos (mul_pos hδ0 hzeta_pos) (by linarith)) 2
  have hexpδ_pos : 0 < Real.exp (2 * shiftedInnerField δ 1) := Real.exp_pos _
  rw [hs0, hsδ, mul_sub, Real.exp_sub]
  field_simp [hfac_pos.ne', hexpδ_pos.ne', h1δ_ne]

/-- **Single-shift Szegő `L²` variational RH equivalence (`δ ∈ (0, ½)`).** -/
theorem riemannHypothesis_iff_szego_budget_ratio_eq {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    RiemannHypothesis ↔
      sInf (budget 1 '' {Q | Q.coeff 0 = 0}) /
        sInf (shiftedBudget δ 1 '' {Q | Q.coeff 0 = 0}) =
          ((1 - δ) / (δ * ‖riemannZeta (1 + (δ : ℂ))‖)) ^ 2 := by
  obtain ⟨hnn, hRH_iff⟩ := riemannHypothesis_iff_log_dilation_quotient_eq hδ0 hδ1
  obtain ⟨hid_int, -⟩ := integral_log_dilation_quotient_eq hδ0 hδ1.le
  rw [hid_int] at hRH_iff
  have hRH_drop : RiemannHypothesis ↔ innerField 1 - shiftedInnerField δ 1 = 0 :=
    ⟨fun h => by have := hRH_iff.mp h; linarith, fun h => hRH_iff.mpr (by linarith)⟩
  rw [hRH_drop]
  have hratio := exp_two_dilation_drop_eq_szego_ratio hδ0 hδ1
  have h1δ_re : 1 ≤ ((1 : ℂ) + (δ : ℂ)).re := by simp; linarith
  have hzeta_pos : 0 < ‖riemannZeta (1 + (δ : ℂ))‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re h1δ_re)
  have ha_pos : 0 < δ * ‖riemannZeta (1 + (δ : ℂ))‖ := mul_pos hδ0 hzeta_pos
  have hb_pos : 0 < 1 - δ := by linarith
  constructor
  · intro h0
    rw [h0, mul_zero, Real.exp_zero] at hratio
    have hsq_inv : (δ * ‖riemannZeta (1 + (δ : ℂ))‖ / (1 - δ)) ^ 2 *
        ((1 - δ) / (δ * ‖riemannZeta (1 + (δ : ℂ))‖)) ^ 2 = 1 := by
      field_simp [ha_pos.ne', hb_pos.ne']
    have hc_ne : (δ * ‖riemannZeta (1 + (δ : ℂ))‖ / (1 - δ)) ^ 2 ≠ 0 := by positivity
    exact mul_left_cancel₀ hc_ne (hratio.symm.trans hsq_inv.symm)
  · intro heq
    rw [heq] at hratio
    have hprod_one : (δ * ‖riemannZeta (1 + (δ : ℂ))‖ / (1 - δ)) ^ 2 *
        ((1 - δ) / (δ * ‖riemannZeta (1 + (δ : ℂ))‖)) ^ 2 = 1 := by
      field_simp [ha_pos.ne', hb_pos.ne']
    rw [hprod_one] at hratio
    have h2 : 2 * (innerField 1 - shiftedInnerField δ 1) = 0 :=
      Real.exp_injective (hratio.trans Real.exp_zero.symm)
    linarith

/-! ### 2. Outer Euler-prefix mollification and prime cancellation -/

/-- Finite Euler-prefix mollifier `∏_{p ∈ S} (1 − p^{−s})`. -/
def eulerMollifier (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ S, (1 - (p : ℂ) ^ (-s))

private theorem euler_factor_eq_column {p : ℕ} (hp2 : 2 ≤ p) (δ : ℝ) (s : ℂ) :
    1 - (p : ℂ) ^ (-(s + (δ : ℂ))) = column (p : ℝ) (((p : ℝ) ^ (-δ) : ℝ) : ℂ) s := by
  have hp_pos : (0 : ℝ) < p := by positivity
  have hp_ne : (p : ℂ) ≠ 0 := by exact_mod_cast hp_pos.ne'
  unfold column
  congr 1
  rw [show -(s + (δ : ℂ)) = ((-δ : ℝ) : ℂ) + (-s) by push_cast; ring,
    Complex.cpow_add _ _ hp_ne, ← Complex.ofReal_natCast,
    Complex.ofReal_cpow hp_pos.le (-δ)]

/-- Every finite Euler prefix (`p ≥ 2`) is strictly nonvanishing on `Re s ≥ ½`. -/
theorem eulerMollifier_ne_zero {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    eulerMollifier S s ≠ 0 := by
  unfold eulerMollifier
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  have hp2 := hS p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp2
  have hcol := euler_factor_eq_column hp2 0 s
  simp only [Complex.ofReal_zero, add_zero, neg_zero, Real.rpow_zero, Complex.ofReal_one] at hcol
  rw [hcol]
  refine column_ne_zero_of_small hp1 ?_ hs
  rw [norm_one, one_mul]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)

/-- Outer Poisson reproduction of `log ‖eulerMollifier S‖` along `Re s = ½ + δ` (`δ ≥ 0`). -/
theorem integral_log_eulerMollifier_shifted {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p)
    {δ : ℝ} (hδ : 0 ≤ δ) {w : ℂ} (hw : 1 / 2 < w.re) :
    Integrable (fun τ : ℝ =>
      Real.log ‖eulerMollifier S (1 / 2 + (δ : ℂ) + τ * I)‖ * halfPlanePoissonKernel w τ) ∧
      (∫ τ : ℝ, Real.log ‖eulerMollifier S (1 / 2 + (δ : ℂ) + τ * I)‖ *
          halfPlanePoissonKernel w τ) =
        Real.log ‖eulerMollifier S (w + (δ : ℂ))‖ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [eulerMollifier, Finset.prod_empty, norm_one, Real.log_one, zero_mul]
    exact ⟨integrable_zero _ _ _, integral_zero _ _⟩
  | @insert p S hp_not ih =>
    have hp2 : 2 ≤ p := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, 2 ≤ q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    obtain ⟨hint_S, hval_S⟩ := ih hS'
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp2
    set c_p : ℂ := (((p : ℝ) ^ (-δ) : ℝ) : ℂ)
    have hsmall : ‖c_p‖ * (p : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
      simp only [c_p, Complex.norm_real]
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 : (p : ℝ) ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by linarith)
      have h2 : (p : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
      nlinarith [Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < p) (-(1 / 2 : ℝ))]
    have hcol_ne : ∀ s : ℂ, 1 / 2 ≤ s.re → column (p : ℝ) c_p s ≠ 0 :=
      fun s hs => column_ne_zero_of_small hp1 hsmall hs
    obtain ⟨hint_p, hval_p⟩ := integrable_and_integral_log_of_no_right_zeros
      (isHalfPlaneDatum_column hp1 c_p) (isCentre_column hp1 c_p hw (hcol_ne w hw.le))
      (fun ρ hρ => hcol_ne ρ hρ.le)
    have hpt_line : ∀ τ : ℝ,
        Real.log ‖eulerMollifier (insert p S) (1 / 2 + (δ : ℂ) + τ * I)‖ *
            halfPlanePoissonKernel w τ =
          Real.log ‖column (p : ℝ) c_p (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ +
            Real.log ‖eulerMollifier S (1 / 2 + (δ : ℂ) + τ * I)‖ * halfPlanePoissonKernel w τ := by
      intro τ
      simp only [eulerMollifier, Finset.prod_insert hp_not, norm_mul]
      have harg : (1 / 2 + (δ : ℂ) + τ * I) = (1 / 2 + τ * I) + (δ : ℂ) := by ring
      have hf1 : 1 - (p : ℂ) ^ (-(1 / 2 + (δ : ℂ) + τ * I)) = column (p : ℝ) c_p (1 / 2 + τ * I) := by
        rw [harg]; exact euler_factor_eq_column hp2 δ (1 / 2 + τ * I)
      have hf1_ne : ‖column (p : ℝ) c_p (1 / 2 + τ * I)‖ ≠ 0 :=
        norm_ne_zero_iff.mpr (hcol_ne _ (by simp))
      have hf2_ne : ‖∏ x ∈ S, (1 - (x : ℂ) ^ (-(1 / 2 + (δ : ℂ) + τ * I)))‖ ≠ 0 :=
        norm_ne_zero_iff.mpr (eulerMollifier_ne_zero hS' (by simp; linarith))
      rw [hf1, Real.log_mul hf1_ne hf2_ne, add_mul]
    simp_rw [hpt_line]
    refine ⟨hint_p.add hint_S, ?_⟩
    rw [integral_add hint_p hint_S, hval_p, hval_S]
    simp only [eulerMollifier, Finset.prod_insert hp_not, norm_mul]
    have hfw : 1 - (p : ℂ) ^ (-(w + (δ : ℂ))) = column (p : ℝ) c_p w :=
      euler_factor_eq_column hp2 δ w
    have hfw_ne : ‖column (p : ℝ) c_p w‖ ≠ 0 := norm_ne_zero_iff.mpr (hcol_ne w hw.le)
    have hfS_ne : ‖∏ x ∈ S, (1 - (x : ℂ) ^ (-(w + (δ : ℂ))))‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (eulerMollifier_ne_zero hS' (by simp; linarith))
    rw [hfw, Real.log_mul hfw_ne hfS_ne]

/-- **Outer Euler-prefix mollification of the log-dilation identity (`w = 1`, `δ ∈ (0, ½]`).**
Multiplying `ζ` by any finite Euler prefix `∏_{p ∈ S} (1 − p^{−s})` cancels the prime factors
identically while preserving the exact inner-mass drop `I(1) − I_δ(1)`. -/
theorem eulerMollified_log_dilation_quotient_eq {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    (∫ τ : ℝ, (Real.log ‖riemannZeta (1 / 2 + τ * I) * eulerMollifier S (1 / 2 + τ * I)‖ -
        Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I) *
          eulerMollifier S (1 / 2 + (δ : ℂ) + τ * I)‖) * halfPlanePoissonKernel 1 τ) =
      (innerField 1 - shiftedInnerField δ 1) +
        Real.log (((1 - δ) * ∏ p ∈ S, (1 - (p : ℝ)⁻¹)) /
          (δ * ‖riemannZeta (1 + (δ : ℂ)) * eulerMollifier S (1 + (δ : ℂ))‖)) := by
  have hw1 : (1 / 2 : ℝ) < (1 : ℂ).re := by simp; norm_num
  obtain ⟨hid_zeta, -⟩ := integral_log_dilation_quotient_eq hδ0 hδ1
  obtain ⟨hint_M0, hval_M0⟩ := integral_log_eulerMollifier_shifted hS (le_rfl : (0 : ℝ) ≤ 0) hw1
  obtain ⟨hint_Mδ, hval_Mδ⟩ := integral_log_eulerMollifier_shifted hS hδ0.le hw1
  simp only [Complex.ofReal_zero, add_zero] at hint_M0 hval_M0
  -- A.e. splitting of `log ‖ζ * eulerMollifier S‖` on both lines
  have hae_line : ∀ σ_sh : ℝ, 0 ≤ σ_sh →
      ∀ᵐ τ : ℝ, riemannZeta (1 / 2 + (σ_sh : ℂ) + τ * I) ≠ 0 := fun σ_sh _ => by
    have hinj : Function.Injective (fun τ : ℝ => (1 / 2 : ℂ) + (σ_sh : ℂ) + τ * I) := fun a b hab => by
      have := congrArg Complex.im hab; simpa using this
    have hcnt : {τ : ℝ | riemannZeta (1 / 2 + (σ_sh : ℂ) + τ * I) = 0}.Countable :=
      countable_zeta_zeros.preimage hinj
    exact measure_eq_zero_iff_ae_notMem.mp (hcnt.measure_zero _)
  have hae_congr :
      (fun τ : ℝ => (Real.log ‖riemannZeta (1 / 2 + τ * I) * eulerMollifier S (1 / 2 + τ * I)‖ -
          Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I) *
            eulerMollifier S (1 / 2 + (δ : ℂ) + τ * I)‖) * halfPlanePoissonKernel 1 τ) =ᵐ[volume]
      fun τ : ℝ =>
        ((Real.log ‖riemannZeta (1 / 2 + τ * I)‖ -
            Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖) * halfPlanePoissonKernel 1 τ) +
        (Real.log ‖eulerMollifier S (1 / 2 + τ * I)‖ * halfPlanePoissonKernel 1 τ -
          Real.log ‖eulerMollifier S (1 / 2 + (δ : ℂ) + τ * I)‖ * halfPlanePoissonKernel 1 τ) := by
    filter_upwards [hae_line 0 le_rfl, hae_line δ hδ0.le] with τ hτ0 hτδ
    simp only [Complex.ofReal_zero, add_zero] at hτ0
    have hm0 : ‖eulerMollifier S (1 / 2 + τ * I)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (eulerMollifier_ne_zero hS (by simp))
    have hmδ : ‖eulerMollifier S (1 / 2 + (δ : ℂ) + τ * I)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (eulerMollifier_ne_zero hS (by simp; linarith))
    rw [norm_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hτ0) hm0,
      Real.log_mul (norm_ne_zero_iff.mpr hτδ) hmδ]
    ring
  have h1δ_re : 1 ≤ ((1 : ℂ) + (δ : ℂ)).re := by simp; linarith
  have hzeta_ne : riemannZeta (1 + (δ : ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1δ_re
  have hint_Z0 := integrable_log_zeta_poisson hw1
  have hint_Zδ := (hasSum_shiftedInnerField hδ0.le hδ1 hw1
    (zetaEntire_ne_zero_of_zeta_ne_zero hzeta_ne)).1
  have hint_Zdiff : Integrable (fun τ : ℝ =>
      (Real.log ‖riemannZeta (1 / 2 + τ * I)‖ -
        Real.log ‖riemannZeta (1 / 2 + (δ : ℂ) + τ * I)‖) * halfPlanePoissonKernel 1 τ) :=
    (hint_Z0.sub hint_Zδ).congr (Eventually.of_forall fun _ => (sub_mul _ _ _).symm)
  have hint_Mdiff : Integrable (fun τ : ℝ =>
      Real.log ‖eulerMollifier S (1 / 2 + τ * I)‖ * halfPlanePoissonKernel 1 τ -
        Real.log ‖eulerMollifier S (1 / 2 + (δ : ℂ) + τ * I)‖ * halfPlanePoissonKernel 1 τ) :=
    hint_M0.sub hint_Mδ
  rw [integral_congr_ae hae_congr, integral_add hint_Zdiff hint_Mdiff,
    integral_sub hint_M0 hint_Mδ, hid_zeta, hval_M0, hval_Mδ]
  -- Evaluate `‖eulerMollifier S 1‖ = ∏_{p ∈ S} (1 − p⁻¹)` and combine logarithms
  have hnorm_M1 : ‖eulerMollifier S 1‖ = ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
    simp only [eulerMollifier, norm_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp2 := hS p hp
    have hp_pos : (0 : ℝ) < p := by positivity
    have hinv_le : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ p))
    rw [Complex.cpow_neg_one, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hM1_pos : 0 < ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
    refine Finset.prod_pos fun p hp => ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hS p hp)
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hMδ_pos : 0 < ‖eulerMollifier S (1 + (δ : ℂ))‖ :=
    norm_pos_iff.mpr (eulerMollifier_ne_zero hS (by simp; linarith))
  have hzδ_pos : 0 < ‖riemannZeta (1 + (δ : ℂ))‖ := norm_pos_iff.mpr hzeta_ne
  rw [hnorm_M1, norm_mul,
    Real.log_div (mul_pos (by linarith) hM1_pos).ne' (mul_pos hδ0 (mul_pos hzδ_pos hMδ_pos)).ne',
    Real.log_mul (by linarith) hM1_pos.ne',
    Real.log_mul hδ0.ne' (mul_pos hzδ_pos hMδ_pos).ne',
    Real.log_mul hzδ_pos.ne' hMδ_pos.ne',
    Real.log_div (by linarith) (mul_pos hδ0 hzδ_pos).ne',
    Real.log_mul hδ0.ne' hzδ_pos.ne']
  ring

/-! ### 3. Shifted Poisson Gram matrix and Abel partial-sum coercivity of Dirichlet polynomials -/

/-- Exact cosine transform of the critical-line Poisson kernel `P₁(τ) = (2π)⁻¹ / (¼ + τ²)`. -/
theorem integral_cos_mul_halfPlanePoissonKernel_one (ξ : ℝ) :
    ∫ τ : ℝ, Real.cos (ξ * τ) * halfPlanePoissonKernel 1 τ = Real.exp (-|ξ| / 2) := by
  set y : ℝ := |ξ| / 2
  have hy0 : 0 ≤ y := by positivity
  let F : ℂ → ℂ := fun z => Complex.exp (I * (y : ℂ) * z)
  have hF_diff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ F z := fun z _ => by
    dsimp only [F]; fun_prop
  have hF_bd : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ 1 := fun z hz => by
    dsimp only [F]
    rw [Complex.norm_exp]
    have hre : (I * (y : ℂ) * z).re = -y * z.im := by
      simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.mul_im,
        Complex.I_im, Complex.ofReal_im]
      ring
    rw [hre]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hrep := integral_halfPlanePoisson_one_mul_eq_apply_I hF_diff hF_bd
  have hFI : F I = (Real.exp (-y) : ℂ) := by
    dsimp only [F]
    have he : I * (y : ℂ) * I = ((-y : ℝ) : ℂ) := by
      calc I * (y : ℂ) * I = (y : ℂ) * (I * I) := by ring
        _ = (y : ℂ) * (-1) := by rw [Complex.I_mul_I]
        _ = ((-y : ℝ) : ℂ) := by push_cast; ring
    rw [he, ← Complex.ofReal_exp]
  rw [hFI] at hrep
  have hPF_int : Integrable (fun x : ℝ => (halfPlanePoisson 1 x : ℂ) * F x) := by
    have hP : Integrable (fun x : ℝ => (halfPlanePoisson 1 x : ℂ)) :=
      (integrable_halfPlanePoisson one_pos).ofReal
    have hFc : Continuous (fun x : ℝ => F x) := by dsimp only [F]; fun_prop
    exact (hP.bdd_mul (c := 1) hFc.aestronglyMeasurable
      (Eventually.of_forall fun x => hF_bd x (by simp))).congr
      (Eventually.of_forall fun x => mul_comm _ _)
  have hre_uhp : ∫ x : ℝ, halfPlanePoisson 1 x * Real.cos (y * x) = Real.exp (-y) := by
    have hre := (Complex.reCLM.integral_comp_comm hPF_int).symm
    rw [hrep, Complex.reCLM_apply, Complex.ofReal_re] at hre
    rw [hre]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [Complex.reCLM_apply]
    symm
    dsimp only [F]
    have hexp_x : I * (y : ℂ) * (x : ℂ) = (((y * x : ℝ) : ℂ) * I) := by push_cast; ring
    rw [hexp_x, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  -- Rescale `x = 2 * τ` using `halfPlanePoissonKernel 1 τ = 2 * halfPlanePoisson 1 (2 * τ)`
  have hscale := Measure.integral_comp_mul_left
    (fun x : ℝ => halfPlanePoisson 1 x * Real.cos (y * x)) (2 : ℝ)
  rw [hre_uhp, show |(2 : ℝ)⁻¹| = 1 / 2 by norm_num, smul_eq_mul] at hscale
  have hkern_eq : ∀ τ : ℝ,
      Real.cos (ξ * τ) * halfPlanePoissonKernel 1 τ =
        2 * (halfPlanePoisson 1 (2 * τ) * Real.cos (y * (2 * τ))) := fun τ => by
    have hcos_eq : Real.cos (ξ * τ) = Real.cos (y * (2 * τ)) := by
      have hy2 : y * (2 * τ) = |ξ| * τ := by simp only [y]; ring
      rw [hy2]
      rcases le_or_gt 0 ξ with h0 | h0
      · rw [abs_of_nonneg h0]
      · rw [abs_of_neg h0, show (-ξ) * τ = -(ξ * τ) by ring, Real.cos_neg]
    have hk : halfPlanePoissonKernel 1 τ = 2 * halfPlanePoisson 1 (2 * τ) := by
      rw [halfPlanePoissonKernel_one, halfPlanePoisson]
      have h1 : (0 : ℝ) < 1 / 4 + τ ^ 2 := by positivity
      have h2 : (0 : ℝ) < 1 ^ (2 : ℕ) + (2 * τ) ^ (2 : ℕ) := by positivity
      have hπ : (0 : ℝ) < π := Real.pi_pos
      field_simp; ring
    rw [hcos_eq, hk]; ring
  simp_rw [hkern_eq]
  rw [integral_const_mul, hscale, show -y = -|ξ| / 2 by simp only [y]; ring]
  ring

/-- Finite real-coefficient Dirichlet polynomial `∑_{m=1}^M b_m m^{−s}`. -/
def realDirichletPoly (M : ℕ) (b : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, (b m : ℂ) * (m : ℂ) ^ (-s)

/-- **Exact shifted Poisson Gram matrix of a Dirichlet polynomial (`Re s = ½ + δ`).** -/
theorem integral_dirichletPoly_norm_sq_poisson (M : ℕ) (b : ℕ → ℝ) (δ : ℝ) :
    (∫ τ : ℝ, ‖realDirichletPoly M b (1 / 2 + (δ : ℂ) + τ * I)‖ ^ 2 *
        halfPlanePoissonKernel 1 τ) =
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        (b m * (m : ℝ) ^ (-δ)) * (b n * (n : ℝ) ^ (-δ)) / (max m n : ℝ) := by
  have hP_int : Integrable (halfPlanePoissonKernel 1) := by
    refine (integrable_halfPlanePoisson (by norm_num : (0 : ℝ) < 1 / 2)).congr
      (Eventually.of_forall fun τ => ?_)
    rw [halfPlanePoissonKernel_one, halfPlanePoisson]
    have h1 : (0 : ℝ) < 1 / 4 + τ ^ 2 := by positivity
    have h2 : (0 : ℝ) < (1 / 2) ^ (2 : ℕ) + τ ^ (2 : ℕ) := by positivity
    have hπ : (0 : ℝ) < π := Real.pi_pos
    field_simp; ring
  -- Pointwise expansion of `‖realDirichletPoly M b (1/2 + δ + iτ)‖²`
  have hpt_sq : ∀ τ : ℝ,
      ‖realDirichletPoly M b (1 / 2 + (δ : ℂ) + τ * I)‖ ^ 2 * halfPlanePoissonKernel 1 τ =
        ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
          ((b m * (m : ℝ) ^ (-δ)) * (b n * (n : ℝ) ^ (-δ)) *
            ((m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)))) *
            (Real.cos ((Real.log n - Real.log m) * τ) * halfPlanePoissonKernel 1 τ) := by
    intro τ
    let w_m : ℕ → ℝ := fun m => b m * (m : ℝ) ^ (-δ) * (m : ℝ) ^ (-(1 / 2 : ℝ))
    have hdir_eq : realDirichletPoly M b (1 / 2 + (δ : ℂ) + τ * I) =
        ∑ m ∈ Finset.Icc 1 M, (w_m m : ℂ) * Complex.exp (((-Real.log m * τ : ℝ) : ℂ) * I) := by
      unfold realDirichletPoly
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm_pos : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have hm_ne : (m : ℂ) ≠ 0 := by exact_mod_cast hm_pos.ne'
      rw [Complex.cpow_def_of_ne_zero hm_ne, ← Complex.ofReal_natCast,
        ← Complex.ofReal_log hm_pos.le]
      have hexp_arg : (Real.log m : ℂ) * -(1 / 2 + (δ : ℂ) + τ * I) =
          (((Real.log m * (-δ) + Real.log m * (-(1 / 2 : ℝ))) : ℝ) : ℂ) +
            ((-Real.log m * τ : ℝ) : ℂ) * I := by push_cast; ring
      rw [hexp_arg, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_add,
        ← Real.rpow_def_of_pos hm_pos, ← Real.rpow_def_of_pos hm_pos]
      dsimp only [w_m]; push_cast; ring
    have hnorm_re : ‖realDirichletPoly M b (1 / 2 + (δ : ℂ) + τ * I)‖ ^ 2 =
        (realDirichletPoly M b (1 / 2 + (δ : ℂ) + τ * I) *
          conj (realDirichletPoly M b (1 / 2 + (δ : ℂ) + τ * I))).re := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    rw [hnorm_re, hdir_eq, map_sum, Finset.sum_mul_sum, Complex.re_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.re_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    have hconj_e : conj (((-Real.log n * τ : ℝ) : ℂ) * I) = (((Real.log n * τ : ℝ) : ℂ) * I) := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I,
        show (-Real.log n * τ : ℝ) = -(Real.log n * τ) by ring, Complex.ofReal_neg]
      ring
    rw [hconj_e]
    have hmul_c : ((w_m m : ℂ) * Complex.exp (((-Real.log m * τ : ℝ) : ℂ) * I)) *
        ((w_m n : ℂ) * Complex.exp (((Real.log n * τ : ℝ) : ℂ) * I)) =
        ((w_m m * w_m n : ℝ) : ℂ) *
          Complex.exp ((((Real.log n - Real.log m) * τ : ℝ) : ℂ) * I) := by
      rw [show ((w_m m : ℂ) * Complex.exp (((-Real.log m * τ : ℝ) : ℂ) * I)) *
          ((w_m n : ℂ) * Complex.exp (((Real.log n * τ : ℝ) : ℂ) * I)) =
          ((w_m m : ℂ) * (w_m n : ℂ)) *
            (Complex.exp (((-Real.log m * τ : ℝ) : ℂ) * I) *
              Complex.exp (((Real.log n * τ : ℝ) : ℂ) * I)) by ring,
        ← Complex.exp_add]
      push_cast; congr 2; ring
    rw [hmul_c, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    dsimp only [w_m]; ring
  simp_rw [hpt_sq]
  have hint_pair : ∀ (ξ : ℝ),
      Integrable (fun τ : ℝ => Real.cos (ξ * τ) * halfPlanePoissonKernel 1 τ) := fun ξ => by
    refine hP_int.bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  rw [integral_finsetSum _ fun m _ =>
    integrable_finsetSum _ fun n _ => (hint_pair _).const_mul _]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [integral_finsetSum _ fun n _ => (hint_pair _).const_mul _]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_const_mul, integral_cos_mul_halfPlanePoissonKernel_one]
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hkern_mn : (m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-|Real.log n - Real.log m| / 2) = (max m n : ℝ)⁻¹ := by
    rw [Real.rpow_def_of_pos hm_pos, Real.rpow_def_of_pos hn_pos, ← Real.exp_add, ← Real.exp_add]
    rcases le_total m n with hmn | hnm
    · have hlog_le : Real.log m ≤ Real.log n := Real.log_le_log hm_pos (by exact_mod_cast hmn)
      rw [max_eq_right (by exact_mod_cast hmn), abs_of_nonneg (sub_nonneg.mpr hlog_le)]
      have he : Real.log m * -(1 / 2 : ℝ) + Real.log n * -(1 / 2 : ℝ) +
          -(Real.log n - Real.log m) / 2 = -Real.log n := by ring
      rw [he, Real.exp_neg, Real.exp_log hn_pos]
    · have hlog_le : Real.log n ≤ Real.log m := Real.log_le_log hn_pos (by exact_mod_cast hnm)
      rw [max_eq_left (by exact_mod_cast hnm), abs_of_nonpos (sub_nonpos.mpr hlog_le)]
      have he : Real.log m * -(1 / 2 : ℝ) + Real.log n * -(1 / 2 : ℝ) +
          -(-(Real.log n - Real.log m)) / 2 = -Real.log m := by ring
      rw [he, Real.exp_neg, Real.exp_log hm_pos]
  calc ((b m * (m : ℝ) ^ (-δ)) * (b n * (n : ℝ) ^ (-δ)) *
          ((m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)))) *
        Real.exp (-|Real.log n - Real.log m| / 2)
      = (b m * (m : ℝ) ^ (-δ)) * (b n * (n : ℝ) ^ (-δ)) *
          ((m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
            Real.exp (-|Real.log n - Real.log m| / 2)) := by ring
    _ = (b m * (m : ℝ) ^ (-δ)) * (b n * (n : ℝ) ^ (-δ)) / (max m n : ℝ) := by
        rw [hkern_mn, div_eq_mul_inv]

/-- **Abel partial-sum diagonalization of the `1 / max(m, n)` Dirichlet Gram matrix (`M ≥ 1`).**
Every nonzero Dirichlet polynomial has strictly positive shifted Poisson second moment. -/
theorem dirichletGram_eq_abel_squares : ∀ {M : ℕ} (_ : 1 ≤ M) (w : ℕ → ℝ),
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M, w m * w n / (max m n : ℝ)) =
      (∑ m ∈ Finset.Icc 1 M, w m) ^ 2 / (M : ℝ) +
        ∑ k ∈ Finset.Icc 1 (M - 1),
          (((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹) * (∑ m ∈ Finset.Icc 1 k, w m) ^ 2)
  | 0, hM, _ => absurd hM (by decide)
  | 1, _, w => by
    have h10 : Finset.Icc 1 (1 - 1) = ∅ := by decide
    rw [h10, Finset.Icc_self, Finset.sum_singleton, Finset.sum_singleton, Finset.sum_empty]
    simp [sq]
  | M + 2, _, w => by
    set M' : ℕ := M + 1
    have hM'1 : 1 ≤ M' := Nat.succ_pos M
    have ih := dirichletGram_eq_abel_squares hM'1 w
    have hmem_top : M' + 1 ∉ Finset.Icc 1 M' := by simp
    have hins_top : Finset.Icc 1 (M' + 1) = insert (M' + 1) (Finset.Icc 1 M') := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hmem_k : M' ∉ Finset.Icc 1 (M' - 1) := by simp [M']
    have hins_k : Finset.Icc 1 M' = insert M' (Finset.Icc 1 (M' - 1)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert, M']; omega
    change (∑ m ∈ Finset.Icc 1 (M' + 1), ∑ n ∈ Finset.Icc 1 (M' + 1),
        w m * w n / (max m n : ℝ)) =
      (∑ m ∈ Finset.Icc 1 (M' + 1), w m) ^ 2 / ((M' + 1 : ℕ) : ℝ) +
        ∑ k ∈ Finset.Icc 1 M',
          (((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹) * (∑ m ∈ Finset.Icc 1 k, w m) ^ 2)
    set S_M : ℝ := ∑ m ∈ Finset.Icc 1 M', w m
    have hborder_r : (∑ m ∈ Finset.Icc 1 M',
          w m * w (M' + 1) / max (m : ℝ) ((M' + 1 : ℕ) : ℝ)) =
        S_M * w (M' + 1) / ((M' + 1 : ℕ) : ℝ) := by
      have hcongr : ∀ m ∈ Finset.Icc 1 M',
          w m * w (M' + 1) / max (m : ℝ) ((M' + 1 : ℕ) : ℝ) =
            w m * (w (M' + 1) / ((M' + 1 : ℕ) : ℝ)) := fun m hm => by
        have hm_le : (m : ℝ) ≤ ((M' + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ_of_le (Finset.mem_Icc.mp hm).2
        rw [max_eq_right hm_le]; ring
      rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul, mul_div_assoc]
    have hborder_l : (∑ n ∈ Finset.Icc 1 M',
          w (M' + 1) * w n / max ((M' + 1 : ℕ) : ℝ) (n : ℝ)) =
        w (M' + 1) * S_M / ((M' + 1 : ℕ) : ℝ) := by
      have hcongr : ∀ n ∈ Finset.Icc 1 M',
          w (M' + 1) * w n / max ((M' + 1 : ℕ) : ℝ) (n : ℝ) =
            (w (M' + 1) / ((M' + 1 : ℕ) : ℝ)) * w n := fun n hn => by
        have hn_le : (n : ℝ) ≤ ((M' + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ_of_le (Finset.mem_Icc.mp hn).2
        rw [max_eq_left hn_le]; ring
      rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum]; ring
    have hgrid : (∑ m ∈ Finset.Icc 1 (M' + 1), ∑ n ∈ Finset.Icc 1 (M' + 1),
          w m * w n / (max m n : ℝ)) =
        (∑ m ∈ Finset.Icc 1 M', ∑ n ∈ Finset.Icc 1 M', w m * w n / (max m n : ℝ)) +
          (2 * S_M * w (M' + 1) + w (M' + 1) ^ 2) / ((M' + 1 : ℕ) : ℝ) := by
      rw [hins_top, Finset.sum_insert hmem_top]
      have hin_split : ∀ m ∈ Finset.Icc 1 M',
          (∑ n ∈ insert (M' + 1) (Finset.Icc 1 M'), w m * w n / max (m : ℝ) (n : ℝ)) =
            w m * w (M' + 1) / max (m : ℝ) ((M' + 1 : ℕ) : ℝ) +
              ∑ n ∈ Finset.Icc 1 M', w m * w n / max (m : ℝ) (n : ℝ) :=
        fun _ _ => Finset.sum_insert hmem_top
      rw [Finset.sum_insert hmem_top, Finset.sum_congr rfl hin_split, Finset.sum_add_distrib,
        max_self, hborder_l, hborder_r]
      ring
    rw [hgrid, ih]
    have hsum_top : (∑ m ∈ Finset.Icc 1 (M' + 1), w m) = w (M' + 1) + S_M := by
      rw [hins_top, Finset.sum_insert hmem_top]
    rw [hsum_top, hins_k, Finset.sum_insert hmem_k,
      show (∑ m ∈ Finset.Icc 1 M', w m) = S_M from rfl]
    have hM'_pos : (0 : ℝ) < M' := by exact_mod_cast hM'1
    have hM'1_pos : (0 : ℝ) < ((M' + 1 : ℕ) : ℝ) := by positivity
    have halg : S_M ^ 2 / (M' : ℝ) + (2 * S_M * w (M' + 1) + w (M' + 1) ^ 2) / ((M' + 1 : ℕ) : ℝ) =
        (w (M' + 1) + S_M) ^ 2 / ((M' + 1 : ℕ) : ℝ) +
          ((M' : ℝ)⁻¹ - ((M' + 1 : ℕ) : ℝ)⁻¹) * S_M ^ 2 := by
      have hc1 : ((M' + 1 : ℕ) : ℝ) = (M' : ℝ) + 1 := by push_cast; ring
      field_simp [hM'_pos.ne', hM'1_pos.ne']
      rw [hc1]; ring
    linarith

/-! ### 4. Prime-side Selberg–Cholesky diagonalization and the `δ → 0⁺` defect -/

/-- Multiplicative Euler amplitude `k ↦ exp(−σ ∑_i k_i log p_i) = ∏_i (p_i^{−σ})^{k_i}` at `x = 0`. -/
def eulerAmpl {n : ℕ} (p : Fin n → ℕ) (σ : ℝ) : (Fin n → ℕ) → ℝ :=
  ampl (fun y => Real.exp (-σ * y)) (fun i => Real.log (p i)) 0

theorem eulerAmpl_zero {n : ℕ} (p : Fin n → ℕ) (σ : ℝ) :
    eulerAmpl p σ 0 = 1 := by
  simp [eulerAmpl, ampl]

theorem eulerAmpl_add {n : ℕ} (p : Fin n → ℕ) (σ : ℝ) (u v : Fin n → ℕ) :
    eulerAmpl p σ (u + v) = eulerAmpl p σ u * eulerAmpl p σ v := by
  simp only [eulerAmpl, ampl, zero_add, Pi.add_apply, Nat.cast_add, add_mul,
    Finset.sum_add_distrib, mul_add, Real.exp_add]

theorem eulerAmpl_eq_prod {n : ℕ} {p : Fin n → ℕ} (hp : ∀ i, 0 < p i) (σ : ℝ) (k : Fin n → ℕ) :
    eulerAmpl p σ k = ∏ i, ((p i : ℝ) ^ (-σ)) ^ (k i) := by
  simp only [eulerAmpl, ampl, zero_add, mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hp0 : (0 : ℝ) < p i := by exact_mod_cast hp i
  rw [Real.rpow_def_of_pos hp0, ← Real.exp_nat_mul]
  congr 1; ring

/-- **Sum-of-squares factorization of `dirichletHankelForm` on `eulerAmpl`.** -/
theorem dirichletHankel_eulerAmpl_eq_sum_sq {n : ℕ} (p : Fin n → ℕ) (σ : ℝ) (N : ℕ)
    (c : (Fin n → ℕ) → ℝ) :
    dirichletHankelForm (eulerAmpl p σ) N c =
      ∑ d ∈ piBox n N, (∑ u ∈ piBox n N, c (d + u) * eulerAmpl p σ u) ^ 2 := by
  unfold dirichletHankelForm
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [eulerAmpl_add]; ring

/-- Squarefree Selberg sieve array attaining the exact minimum of `dirichletHankelForm` for all
`N ≥ 2`. -/
def selbergArray {n : ℕ} (p : Fin n → ℕ) (σ : ℝ) (k : Fin n → ℕ) : ℝ :=
  if k ∈ piBox n 2 then
    ∏ i, (if k i = 0 then 1 else -(p i : ℝ) ^ (-σ) / (1 + (p i : ℝ) ^ (-2 * σ)))
  else 0

theorem selbergArray_zero {n : ℕ} (p : Fin n → ℕ) (σ : ℝ) :
    selbergArray p σ 0 = 1 := by
  have h0 : (0 : Fin n → ℕ) ∈ piBox n 2 := mem_piBox.mpr fun _ => by simp
  simp [selbergArray, h0]

theorem selbergArray_eq_zero_of_not_mem {n : ℕ} (p : Fin n → ℕ) (σ : ℝ) {N : ℕ} (hN : 2 ≤ N)
    {k : Fin n → ℕ} (hk : k ∉ piBox n N) :
    selbergArray p σ k = 0 := by
  have hk2 : k ∉ piBox n 2 := fun h2 =>
    hk (mem_piBox.mpr fun i => lt_of_lt_of_le (mem_piBox.mp h2 i) hN)
  simp [selbergArray, hk2]

/-- Möbius orthogonality on `piBox n 2`: `∑_{d ∈ piBox n 2, d ≤ m} (−1)^{∑ d_i}` equals `1` at
`m = 0` and `0` otherwise. -/
private theorem sum_mobius_piBox_two {n : ℕ} (m : Fin n → ℕ) :
    (∑ d ∈ (piBox n 2).filter (fun d => ∀ i, d i ≤ m i),
        ∏ i : Fin n, ((-1 : ℝ) ^ (d i))) =
      if m = 0 then 1 else 0 := by
  classical
  let S_coord : Fin n → Finset ℕ := fun i => (Finset.range 2).filter (fun r => r ≤ m i)
  have hbox_eq : (piBox n 2).filter (fun d => ∀ i, d i ≤ m i) = Fintype.piFinset S_coord := by
    ext d
    simp only [Finset.mem_filter, mem_piBox, Fintype.mem_piFinset, S_coord, Finset.mem_range]
    exact ⟨fun ⟨h1, h2⟩ i => ⟨h1 i, h2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  rw [hbox_eq, ← Finset.prod_univ_sum]
  split_ifs with hm0
  · subst hm0
    refine Finset.prod_eq_one fun i _ => ?_
    have hS0 : S_coord i = {0} := by
      ext r; simp only [S_coord, Pi.zero_apply, Finset.mem_filter, Finset.mem_range,
        Finset.mem_singleton]; omega
    simp [hS0]
  · have hex : ∃ i : Fin n, m i ≠ 0 := by
      by_contra hall; push Not at hall; exact hm0 (funext hall)
    obtain ⟨i₀, hi₀⟩ := hex
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
    have hS2 : S_coord i₀ = ({0, 1} : Finset ℕ) := by
      ext r; simp only [S_coord, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton]
      have : 1 ≤ m i₀ := Nat.pos_of_ne_zero hi₀
      omega
    rw [hS2, Finset.sum_pair (by decide)]; norm_num

private theorem sum_sq_eulerAmpl_piBox_two {n : ℕ} {p : Fin n → ℕ} (hp : ∀ i, 0 < p i) (σ : ℝ) :
    (∑ d ∈ piBox n 2, eulerAmpl p σ d ^ 2) = ∏ i, (1 + (p i : ℝ) ^ (-2 * σ)) := by
  have hpt : ∀ d : Fin n → ℕ,
      eulerAmpl p σ d ^ 2 = ∏ i, (((p i : ℝ) ^ (-2 * σ)) ^ (d i)) := fun d => by
    rw [eulerAmpl_eq_prod hp σ d, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hp0 : (0 : ℝ) < p i := by exact_mod_cast hp i
    rw [← pow_mul, mul_comm (d i) 2, pow_mul, ← Real.rpow_natCast ((p i : ℝ) ^ (-σ)) 2,
      ← Real.rpow_mul hp0.le]
    congr 2; push_cast; ring
  simp_rw [hpt]
  unfold piBox
  rw [← Finset.prod_univ_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]

/-- **Universal Selberg–Cholesky lower bound on `dirichletHankelForm (eulerAmpl p σ)`.**
For every box height `N ≥ 2` and every array `c` supported in `piBox n N` with `c 0 = 1`,
`∏_i (1 + p_i^{−2σ})⁻¹ ≤ dirichletHankelForm (eulerAmpl p σ) N c`. -/
theorem dirichletHankel_eulerAmpl_ge_selberg {n : ℕ} {p : Fin n → ℕ} (hp : ∀ i, 0 < p i)
    (σ : ℝ) {N : ℕ} (hN : 2 ≤ N) {c : (Fin n → ℕ) → ℝ}
    (hc : ∀ k, k ∉ piBox n N → c k = 0) (hc0 : c 0 = 1) :
    (∏ i, (1 + (p i : ℝ) ^ (-2 * σ))⁻¹) ≤ dirichletHankelForm (eulerAmpl p σ) N c := by
  classical
  set L : (Fin n → ℕ) → ℝ := fun d => ∑ u ∈ piBox n N, c (d + u) * eulerAmpl p σ u
  let w : (Fin n → ℕ) → ℝ := fun d => (∏ i, ((-1 : ℝ) ^ (d i))) * eulerAmpl p σ d
  -- Linear functional identity `∑_{d ∈ piBox n 2} w d * L d = 1`
  have hlin_one : (∑ d ∈ piBox n 2, w d * L d) = 1 := by
    have hterm_d : ∀ d ∈ piBox n 2,
        w d * L d = ∑ m ∈ piBox n N,
          if ∀ i, d i ≤ m i then (∏ i, ((-1 : ℝ) ^ (d i))) * (c m * eulerAmpl p σ m) else 0 := by
      intro d _
      dsimp only [w, L]
      rw [Finset.mul_sum]
      have h1 : (∑ u ∈ piBox n N, ((∏ i, (-1 : ℝ) ^ d i) * eulerAmpl p σ d) *
            (c (d + u) * eulerAmpl p σ u)) =
          ∑ u ∈ (piBox n N).filter (fun u => d + u ∈ piBox n N),
            (∏ i, (-1 : ℝ) ^ d i) * (c (d + u) * eulerAmpl p σ (d + u)) := by
        rw [← Finset.sum_subset (Finset.filter_subset _ _) fun u huB hnot => by
          have hnot' : d + u ∉ piBox n N := fun h => hnot (Finset.mem_filter.mpr ⟨huB, h⟩)
          rw [hc _ hnot', zero_mul, mul_zero]]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [eulerAmpl_add]; ring
      rw [h1, ← Finset.sum_filter]
      refine Finset.sum_nbij' (fun u => d + u) (fun m => fun i => m i - d i) ?_ ?_ ?_ ?_ ?_
      · intro u hu
        obtain ⟨_, hdu⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨hdu, fun i => Nat.le_add_right _ _⟩
      · intro m hm
        obtain ⟨hmB, hdm⟩ := Finset.mem_filter.mp hm
        have hadd : (d + fun i => m i - d i) = m := funext fun i => by
          have := hdm i; simp only [Pi.add_apply]; omega
        refine Finset.mem_filter.mpr ⟨mem_piBox.mpr fun i => ?_, hadd.symm ▸ hmB⟩
        exact lt_of_le_of_lt (Nat.sub_le _ _) (mem_piBox.mp hmB i)
      · intro u _; ext i; simp
      · intro m hm
        obtain ⟨_, hdm⟩ := Finset.mem_filter.mp hm
        ext i; have := hdm i; simp only [Pi.add_apply]; omega
      · intro _ _; rfl
    rw [Finset.sum_congr rfl hterm_d, Finset.sum_comm]
    have hinner : ∀ m ∈ piBox n N,
        (∑ d ∈ piBox n 2,
          if ∀ i, d i ≤ m i then (∏ i, (-1 : ℝ) ^ d i) * (c m * eulerAmpl p σ m) else 0) =
          if m = 0 then c 0 * eulerAmpl p σ 0 else 0 := fun m _ => by
      rw [← Finset.sum_filter, ← Finset.sum_mul, sum_mobius_piBox_two m]
      split_ifs with hm0
      · subst hm0; ring
      · ring
    rw [Finset.sum_congr rfl hinner]
    have h0_mem : (0 : Fin n → ℕ) ∈ piBox n N := mem_piBox.mpr fun _ => by simp; omega
    rw [Finset.sum_ite_eq' _ _ (fun _ => c 0 * eulerAmpl p σ 0), if_pos h0_mem, hc0,
      eulerAmpl_zero, mul_one]
  -- Cauchy–Schwarz on `piBox n 2 ⊆ piBox n N`
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (piBox n 2) w L
  rw [hlin_one, one_pow] at hcs
  have hw_sq : (∑ d ∈ piBox n 2, w d ^ 2) = ∏ i, (1 + (p i : ℝ) ^ (-2 * σ)) := by
    have hw2 : ∀ d : Fin n → ℕ, w d ^ 2 = eulerAmpl p σ d ^ 2 := fun d => by
      dsimp only [w]
      rw [mul_pow, ← Finset.prod_pow]
      have h1 : (∏ x : Fin n, ((-1 : ℝ) ^ d x) ^ 2) = 1 :=
        Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [h1, one_mul]
    simp_rw [hw2]
    exact sum_sq_eulerAmpl_piBox_two hp σ
  rw [hw_sq] at hcs
  have hsub_box : piBox n 2 ⊆ piBox n N := fun d hd =>
    mem_piBox.mpr fun i => lt_of_lt_of_le (mem_piBox.mp hd i) hN
  have hL_mono : (∑ d ∈ piBox n 2, L d ^ 2) ≤ dirichletHankelForm (eulerAmpl p σ) N c := by
    rw [dirichletHankel_eulerAmpl_eq_sum_sq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub_box fun _ _ _ => sq_nonneg _
  have hprod_pos : 0 < ∏ i : Fin n, (1 + (p i : ℝ) ^ (-2 * σ)) :=
    Finset.prod_pos fun i _ => by
      have hp0 : (0 : ℝ) < p i := by exact_mod_cast hp i
      positivity
  rw [Finset.prod_inv_distrib, inv_le_iff_one_le_mul₀' hprod_pos]
  exact hcs.trans (mul_le_mul_of_nonneg_left hL_mono hprod_pos.le)

/-- **Exact Selberg attainment at every height `N ≥ 2`.** -/
theorem dirichletHankel_selbergArray_eq {n : ℕ} {p : Fin n → ℕ} (hp : ∀ i, 0 < p i)
    (σ : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    dirichletHankelForm (eulerAmpl p σ) N (selbergArray p σ) =
      ∏ i, (1 + (p i : ℝ) ^ (-2 * σ))⁻¹ := by
  classical
  rw [dirichletHankel_eulerAmpl_eq_sum_sq]
  have hsub_box : piBox n 2 ⊆ piBox n N := fun d hd =>
    mem_piBox.mpr fun i => lt_of_lt_of_le (mem_piBox.mp hd i) hN
  -- Outside `piBox n 2`, `d + u ∉ piBox n 2` for every `u`, so the inner sum vanishes
  have hzero_out : ∀ d ∈ piBox n N, d ∉ piBox n 2 →
      (∑ u ∈ piBox n N, selbergArray p σ (d + u) * eulerAmpl p σ u) ^ 2 = 0 := by
    intro d _ hd_not
    have hsum0 : (∑ u ∈ piBox n N, selbergArray p σ (d + u) * eulerAmpl p σ u) = 0 := by
      refine Finset.sum_eq_zero fun u _ => ?_
      have hdu_not : d + u ∉ piBox n 2 := fun hdu =>
        hd_not (mem_piBox.mpr fun i => lt_of_le_of_lt (Nat.le_add_right _ _) (mem_piBox.mp hdu i))
      simp [selbergArray, hdu_not]
    rw [hsum0, sq, mul_zero]
  rw [← Finset.sum_subset hsub_box hzero_out]
  -- On `d ∈ piBox n 2`, the inner sum restricts to `u ∈ piBox n 2` with `d + u ∈ piBox n 2`
  have hinner_d : ∀ d ∈ piBox n 2,
      (∑ u ∈ piBox n N, selbergArray p σ (d + u) * eulerAmpl p σ u) =
        ((∏ i, ((-1 : ℝ) ^ (d i))) * eulerAmpl p σ d) *
          ∏ i, (1 + (p i : ℝ) ^ (-2 * σ))⁻¹ := by
    intro d hd
    have hrest : (∑ u ∈ piBox n N, selbergArray p σ (d + u) * eulerAmpl p σ u) =
        ∑ u ∈ piBox n 2, selbergArray p σ (d + u) * eulerAmpl p σ u := by
      refine (Finset.sum_subset hsub_box fun u _ hu_not => ?_).symm
      have hdu_not : d + u ∉ piBox n 2 := fun hdu =>
        hu_not (mem_piBox.mpr fun i => lt_of_le_of_lt (Nat.le_add_left _ _) (mem_piBox.mp hdu i))
      simp [selbergArray, hdu_not]
    rw [hrest]
    let F_d : Fin n → ℕ → ℝ := fun i r =>
      (if d i + r < 2 then
          if d i + r = 0 then (1 : ℝ)
          else -(p i : ℝ) ^ (-σ) / (1 + (p i : ℝ) ^ (-2 * σ))
        else 0) * ((p i : ℝ) ^ (-σ)) ^ r
    have hpt : ∀ u ∈ piBox n 2,
        selbergArray p σ (d + u) * eulerAmpl p σ u =
          ∏ i : Fin n, F_d i (u i) := by
      intro u _
      rw [eulerAmpl_eq_prod hp σ u]
      unfold selbergArray
      split_ifs with hdu
      · rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        dsimp only [F_d, Pi.add_apply]
        have hdui : d i + u i < 2 := mem_piBox.mp hdu i
        rw [if_pos hdui]
      · have hex : ∃ i₀ : Fin n, ¬ (d i₀ + u i₀ < 2) := by
          by_contra hall; push Not at hall
          exact hdu (mem_piBox.mpr hall)
        obtain ⟨i₀, hi₀⟩ := hex
        rw [zero_mul]
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i₀)
          (by dsimp only [F_d]; rw [if_neg hi₀, zero_mul])
    rw [Finset.sum_congr rfl hpt]
    unfold piBox
    rw [← Finset.prod_univ_sum, eulerAmpl_eq_prod hp σ d,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only [F_d]
    have hp0 : (0 : ℝ) < p i := by exact_mod_cast hp i
    have hd_lt : d i < 2 := mem_piBox.mp hd i
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    set a : ℝ := (p i : ℝ) ^ (-σ)
    set b : ℝ := (p i : ℝ) ^ (-2 * σ)
    have hab : a * a = b := by
      dsimp only [a, b]; rw [← Real.rpow_add hp0]; congr 1; ring
    have hb_ne : 1 + b ≠ 0 := by dsimp only [b]; positivity
    have hdi_cases : d i = 0 ∨ d i = 1 := by omega
    rcases hdi_cases with h0 | h1
    · rw [h0, if_pos (by decide : 0 + 0 < 2), if_pos (rfl : 0 + 0 = 0),
        if_pos (by decide : 0 + 1 < 2), if_neg (by decide : ¬ (0 + 1 = 0)),
        pow_zero, pow_one]
      field_simp [hb_ne]
      nlinarith [hab]
    · rw [h1, if_pos (by decide : 1 + 0 < 2), if_neg (by decide : ¬ (1 + 0 = 0)),
        if_neg (by decide : ¬ (1 + 1 < 2)),
        pow_zero, pow_one, div_eq_mul_inv]
      ring
  have hsq_d : ∀ d ∈ piBox n 2,
      (∑ u ∈ piBox n N, selbergArray p σ (d + u) * eulerAmpl p σ u) ^ 2 =
        eulerAmpl p σ d ^ 2 * (∏ i, (1 + (p i : ℝ) ^ (-2 * σ))⁻¹) ^ 2 := fun d hd => by
    rw [hinner_d d hd, mul_pow, mul_pow, ← Finset.prod_pow]
    have h1 : (∏ x : Fin n, ((-1 : ℝ) ^ d x) ^ 2) = 1 :=
      Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h1, one_mul]
  rw [Finset.sum_congr rfl hsq_d, ← Finset.sum_mul, sum_sq_eulerAmpl_piBox_two hp σ]
  have hprod_ne : (∏ i : Fin n, (1 + (p i : ℝ) ^ (-2 * σ))) ≠ 0 :=
    (Finset.prod_pos fun i _ => by
      have hp0 : (0 : ℝ) < p i := by exact_mod_cast hp i
      positivity).ne'
  rw [Finset.prod_inv_distrib, sq, ← mul_assoc, mul_inv_cancel₀ hprod_ne, one_mul]

/-- **Uniform positive Selberg–Hankel floor at fixed shift `δ > 0`.**
For every `δ > 0`, `exp(−∑'_m m^{−(1+2δ)}) > 0` bounds `dirichletHankelForm (eulerAmpl p (½ + δ)) N c`
below uniformly across all finite tuples of distinct primes, all `N ≥ 2`, and all `c` supported in
`piBox n N` with `c 0 = 1`. -/
theorem eulerHankel_pos_floor_of_pos {δ : ℝ} (hδ : 0 < δ) {n : ℕ} {p : Fin n → ℕ}
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) {N : ℕ} (hN : 2 ≤ N)
    {c : (Fin n → ℕ) → ℝ} (hc : ∀ k, k ∉ piBox n N → c k = 0) (hc0 : c 0 = 1) :
    Real.exp (-∑' m : ℕ, ((m : ℝ) ^ (1 + 2 * δ))⁻¹) ≤
      dirichletHankelForm (eulerAmpl p (1 / 2 + δ)) N c := by
  have h12δ : 1 < 1 + 2 * δ := by linarith
  have hsum : Summable (fun m : ℕ => ((m : ℝ) ^ (1 + 2 * δ))⁻¹) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using Real.summable_nat_rpow_inv.mpr h12δ
  refine le_trans ?_ (dirichletHankel_eulerAmpl_ge_selberg (fun i => (hp i).pos)
    (1 / 2 + δ) hN hc hc0)
  have hfac : ∀ i : Fin n,
      Real.exp (-(((p i : ℝ) ^ (1 + 2 * δ))⁻¹)) ≤
        (1 + (p i : ℝ) ^ (-2 * (1 / 2 + δ)))⁻¹ := fun i => by
    have hp0 : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
    have hexp_eq : (p i : ℝ) ^ (-2 * (1 / 2 + δ)) = ((p i : ℝ) ^ (1 + 2 * δ))⁻¹ := by
      rw [← Real.rpow_neg hp0.le]; congr 1; ring
    rw [hexp_eq, Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (((p i : ℝ) ^ (1 + 2 * δ))⁻¹)])
  have hprod_ge : Real.exp (-∑ i : Fin n, ((p i : ℝ) ^ (1 + 2 * δ))⁻¹) ≤
      ∏ i, (1 + (p i : ℝ) ^ (-2 * (1 / 2 + δ)))⁻¹ := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun i _ => hfac i
  have hsum_le : (∑ i : Fin n, ((p i : ℝ) ^ (1 + 2 * δ))⁻¹) ≤
      ∑' m : ℕ, ((m : ℝ) ^ (1 + 2 * δ))⁻¹ := by
    rw [(Finset.sum_image (f := fun m : ℕ => ((m : ℝ) ^ (1 + 2 * δ))⁻¹)
      fun i _ j _ hij => hinj hij).symm]
    exact hsum.sum_le_tsum (Finset.univ.image p) fun _ _ => by positivity
  exact (Real.exp_le_exp.mpr (by linarith)).trans hprod_ge

/-- **Critical-line collapse of the Selberg–Hankel minimum (`δ = 0`).**
At `σ = ½`, finite sets of distinct primes drive the exact Selberg minimum arbitrarily close to `0`. -/
theorem exists_eulerHankel_lt_of_critical {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (p : Fin n → ℕ), (∀ i, (p i).Prime) ∧ Function.Injective p ∧
      dirichletHankelForm (eulerAmpl p (1 / 2)) 2 (selbergArray p (1 / 2)) < ε := by
  classical
  have hdiv : ¬ Summable (fun q : Nat.Primes => (1 / (q : ℝ))) := Nat.Primes.not_summable_one_div
  have hunb : ∃ T : Finset Nat.Primes, 2 * (|Real.log ε| + 1) < ∑ q ∈ T, (1 / (q : ℝ)) := by
    by_contra hle; push Not at hle
    exact hdiv (summable_of_sum_le (fun _ => by positivity) hle)
  obtain ⟨T, hT⟩ := hunb
  let e : Fin T.card ≃ T := T.equivFin.symm
  let p : Fin T.card → ℕ := fun i => (e i : ℕ)
  have hp : ∀ i, (p i).Prime := fun i => (e i).1.2
  have hinj : Function.Injective p := fun i j hij => e.injective (Subtype.ext (Subtype.ext hij))
  refine ⟨T.card, p, hp, hinj, ?_⟩
  rw [dirichletHankel_selbergArray_eq (fun i => (hp i).pos) (1 / 2) le_rfl]
  have hfac_le : ∀ i : Fin T.card,
      (1 + (p i : ℝ) ^ (-2 * (1 / 2 : ℝ)))⁻¹ ≤ Real.exp (-((p i : ℝ)⁻¹ / 2)) := fun i => by
    have hp0 : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
    have hp1 : (1 : ℝ) ≤ p i := by exact_mod_cast (hp i).pos
    have hexp_eq : (p i : ℝ) ^ (-2 * (1 / 2 : ℝ)) = (p i : ℝ)⁻¹ := by
      rw [show (-2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    rw [hexp_eq, Real.exp_neg]
    refine inv_anti₀ (Real.exp_pos _) ?_
    set u : ℝ := (p i : ℝ)⁻¹ / 2
    have hu_le : u ≤ 1 / 2 := by
      simp only [u]; have : (p i : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1; linarith
    have hu_nn : 0 ≤ u := by positivity
    have h1 : Real.exp u ≤ (1 - u)⁻¹ := by
      rw [← inv_inv (Real.exp u), ← Real.exp_neg]
      exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp (-u)])
    have h2 : (1 - u)⁻¹ ≤ 1 + (p i : ℝ)⁻¹ := by
      have : 1 + (p i : ℝ)⁻¹ = 1 + 2 * u := by simp only [u]; ring
      rw [this, inv_le_iff_one_le_mul₀' (by linarith)]
      nlinarith
    exact h1.trans h2
  have hprod_le : (∏ i, (1 + (p i : ℝ) ^ (-2 * (1 / 2 : ℝ)))⁻¹) ≤
      Real.exp (-(1 / 2) * ∑ i : Fin T.card, (p i : ℝ)⁻¹) := by
    have he : Real.exp (-(1 / 2) * ∑ i : Fin T.card, (p i : ℝ)⁻¹) =
        ∏ i : Fin T.card, Real.exp (-((p i : ℝ)⁻¹ / 2)) := by
      rw [← Real.exp_sum, Finset.mul_sum]
      exact congrArg Real.exp (Finset.sum_congr rfl fun i _ => by ring)
    rw [he]
    exact Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => hfac_le i
  have hsum_T : (∑ i : Fin T.card, (p i : ℝ)⁻¹) = ∑ q ∈ T, (1 / (q : ℝ)) := by
    rw [Equiv.sum_comp e (fun z : T => ((z.1 : ℕ) : ℝ)⁻¹),
      Finset.sum_coe_sort T (fun q : Nat.Primes => (q : ℝ)⁻¹)]
    exact Finset.sum_congr rfl fun q _ => (one_div (q : ℝ)).symm
  rw [hsum_T] at hprod_le
  have hexp_lt : Real.exp (-(1 / 2) * ∑ q ∈ T, (1 / (q : ℝ))) < ε := by
    rw [← Real.exp_log hε]
    refine Real.exp_lt_exp.mpr ?_
    have := neg_le_abs (Real.log ε)
    linarith
  exact hprod_le.trans_lt hexp_lt

/-- **Exact logarithmic slope of the Selberg–Hankel minimum at `δ = 0`.** -/
theorem hasDerivAt_log_eulerHankel_min {n : ℕ} {p : Fin n → ℕ} (hp : ∀ i, 0 < p i) :
    HasDerivAt
      (fun δ : ℝ =>
        Real.log (dirichletHankelForm (eulerAmpl p (1 / 2 + δ)) 2 (selbergArray p (1 / 2 + δ))))
      (2 * ∑ i : Fin n, Real.log (p i) / ((p i : ℝ) + 1)) 0 := by
  have hfun : (fun δ : ℝ =>
      Real.log (dirichletHankelForm (eulerAmpl p (1 / 2 + δ)) 2 (selbergArray p (1 / 2 + δ)))) =
      fun δ : ℝ => ∑ i : Fin n, -Real.log (1 + Real.exp (-(1 + 2 * δ) * Real.log (p i))) := by
    funext δ
    rw [dirichletHankel_selbergArray_eq hp (1 / 2 + δ) le_rfl,
      Real.log_prod fun i _ => by
        have hp0 : (0 : ℝ) < p i := by exact_mod_cast hp i
        positivity]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp0 : (0 : ℝ) < p i := by exact_mod_cast hp i
    rw [Real.log_inv, Real.rpow_def_of_pos hp0]
    congr 3; ring
  rw [hfun, Finset.mul_sum]
  refine HasDerivAt.fun_sum fun i _ => ?_
  set L : ℝ := Real.log (p i)
  have hp0 : (0 : ℝ) < p i := by exact_mod_cast hp i
  have h1 : HasDerivAt (fun δ : ℝ => -(1 + 2 * δ) * L) (-2 * L) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul 2).const_add 1).neg.mul_const L
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun δ : ℝ => 1 + Real.exp (-(1 + 2 * δ) * L))
      (Real.exp (-(1 + 2 * (0 : ℝ)) * L) * (-2 * L)) 0 := by
    simpa [Function.comp_def] using ((Real.hasDerivAt_exp _).comp 0 h1).const_add 1
  have h3 := (h2.log (by positivity)).neg
  refine h3.congr_deriv ?_
  have hexp0 : Real.exp (-(1 + 2 * (0 : ℝ)) * L) = (p i : ℝ)⁻¹ := by
    simp only [L, mul_zero, add_zero, neg_one_mul, Real.exp_neg, Real.exp_log hp0]
  rw [hexp0]
  have hd1 : (1 + (p i : ℝ)⁻¹) ≠ 0 := by positivity
  have hd2 : ((p i : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hp0.ne', hd1, hd2]

/-- **Divergence of the prime logarithmic cancellation-defect slope `∑_p log p / (p + 1) = ∞`.** -/
theorem not_summable_primes_log_div_add_one :
    ¬ Summable (fun q : Nat.Primes => Real.log (q : ℝ) / ((q : ℝ) + 1)) := by
  intro hsum
  refine Nat.Primes.not_summable_one_div ?_
  have hmaj : Summable (fun q : Nat.Primes => 2 * (Real.log (q : ℝ) / ((q : ℝ) + 1))) :=
    hsum.mul_left 2
  let g : Nat.Primes → ℝ := fun q =>
    2 * (Real.log (q : ℝ) / ((q : ℝ) + 1)) + if q.1 = 2 then 1 else 0
  have hg_sum : Summable g :=
    hmaj.add (summable_of_ne_finset_zero (s := {⟨2, Nat.prime_two⟩}) fun q hq => by
      have hne : q.1 ≠ 2 := fun h2 => hq (Finset.mem_singleton.mpr (Subtype.ext h2))
      simp [hne])
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun q => ?_) hg_sum
  dsimp only [g]
  set x : ℝ := (q : ℝ)
  have hx_eq : x = (q.1 : ℝ) := rfl
  split_ifs with hq2
  · have hx2 : x = 2 := by rw [hx_eq, hq2]; norm_num
    have hlog2_nn : 0 ≤ Real.log x := by rw [hx2]; exact Real.log_nonneg (by norm_num)
    have hdiv_nn : 0 ≤ Real.log x / (x + 1) := div_nonneg hlog2_nn (by linarith)
    have h12 : 1 / x ≤ 1 := by rw [hx2]; norm_num
    linarith
  · have hq3 : 3 ≤ q.1 := by have := q.2.two_le; omega
    have hx3 : (3 : ℝ) ≤ x := by rw [hx_eq]; exact_mod_cast hq3
    have hx_pos : 0 < x := by linarith
    have hx1_pos : 0 < x + 1 := by linarith
    have hlog_gt1 : 1 ≤ Real.log x := by
      have he3 : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
      have := Real.log_le_log (Real.exp_pos 1) he3
      rwa [Real.log_exp] at this
    have h1 : 1 / x ≤ 2 * (1 / (x + 1)) := by
      rw [mul_one_div, div_le_div_iff₀ hx_pos hx1_pos]
      linarith
    have h2 : 1 / (x + 1) ≤ Real.log x / (x + 1) :=
      div_le_div_of_nonneg_right hlog_gt1 hx1_pos.le
    linarith

#print axioms integrable_norm_sq_zeta_shifted_poisson
#print axioms isGLB_shiftedBudget_innerField
#print axioms exp_two_dilation_drop_eq_szego_ratio
#print axioms riemannHypothesis_iff_szego_budget_ratio_eq
#print axioms eulerMollified_log_dilation_quotient_eq
#print axioms integral_cos_mul_halfPlanePoissonKernel_one
#print axioms integral_dirichletPoly_norm_sq_poisson
#print axioms dirichletGram_eq_abel_squares
#print axioms dirichletHankel_eulerAmpl_ge_selberg
#print axioms dirichletHankel_selbergArray_eq
#print axioms eulerHankel_pos_floor_of_pos
#print axioms exists_eulerHankel_lt_of_critical
#print axioms hasDerivAt_log_eulerHankel_min
#print axioms not_summable_primes_log_div_add_one

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
