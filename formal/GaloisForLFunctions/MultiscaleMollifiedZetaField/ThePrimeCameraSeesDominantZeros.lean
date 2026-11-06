import Zeta23.Final
import Zeta23.Poisson.PaperFT
import GaloisForLFunctions.ArithmeticPolarization.ThePriceOfEllipticLocalization
import GaloisForLFunctions.RHTower.VonMangoldtMollifierPolynomialMeanSquare
import GaloisForLFunctions.RHTower.ChebyshevSquareWeight

/-!
# The prime camera sees the dominant zeros

Fix a nonnegative `C²` profile `v` on `[−1, 1]`. With `K(u) = δ⁻¹ v((u − y)/δ)` the explicit formula of
the twist `e^{−itu} K` reads

`Z(t) := Σ_ρ m_ρ K̂(γ_ρ − t − i b_ρ) = −Σ_n Λ(n) K(log n) n^{−1/2−it} + small`, `b_ρ = β_ρ − ½`,

so a Dirichlet polynomial supported on `log n ∈ [y − δ, y + δ]` photographs the zeros near height `t`
with resolution `1/δ` (`exists_norm_zeroField_add_cameraPoly_le`). A zero of depth `b ≥ 0` has amplitude
`≥ ½ (∫v) e^{b(y−δ)}` on its window `|t − γ| ≤ 1/(10δ)` (`norm_paperFT_camera_ge`).

The mean value theorem gives the polynomial mean square `≪ T (log N/δ)²`. At `δ = cL`, `y = (1−2c)L`,
`L = log T` this is `O(T/c²)`, independent of the depth, so the zero field obeys a Chebyshev bound
with exponent two, uniformly in `c` and in the centre (`exists_volume_zeroField_ge_le_uniform`).

A zero **dominates its window** when the whole field there has at least half the size of its own term
(`DominatesWindow`). Separated dominant zeros at depth `≥ α/L` number `≪ T L e^{−2(1−3c)α}`
(`exists_card_dominant_zeros_le`): the Density Hypothesis rate `2`, up to the free parameter `c`, against
the rate `22/25` of the mollified second moment. With the camera tuned to the depth, `δ = L/(4+α)`, the rate
is exactly two: `≪ T L (4+α) e^{−2α}` (`exists_card_dominant_zeros_le_rate_two`). Their unit windows are sparse
from depth `(½ + ε) log log T / log T` on (`exists_card_dominant_zeros_le_threshold`). No mollifier enters: the
camera is prime-only.

Dominance follows from a statement about zeros alone: the companions' weighted mass at the window stays
below a quarter of the amplitude (`IsolatedAt`, `dominatesWindow_of_isolated`). A deep zero outside the
theorem therefore has deep or numerous companions at scale `1/δ`: clusters are the exact obstruction.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Real
open RHTower Zeta23
open GaloisForLFunctions.ArithmeticPolarization
  (twist paperFT_twist literatureRHS_twist contDiff_twist hasCompactSupport_twist)

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

variable {v : ℝ → ℝ}

/-! ### The camera test -/

/-- The complex profile of a real function. -/
def cplx (v : ℝ → ℝ) : ℝ → ℂ := fun u => (v u : ℂ)

theorem contDiff_cplx (hv : ContDiff ℝ 2 v) : ContDiff ℝ 2 (cplx v) :=
  Complex.ofRealCLM.contDiff.comp hv

theorem cplx_support (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (u : ℝ) (h : cplx v u ≠ 0) : |u| ≤ 1 := by
  refine hsupp u fun h0 => h ?_
  simp [cplx, h0]

/-- The camera test `K(u) = δ⁻¹ v((u − y)/δ)`, of mass `∫v` and width `δ`. -/
def cameraTest (v : ℝ → ℝ) (δ y : ℝ) : ℝ → ℂ := fun u => ((v ((u - y) / δ) / δ : ℝ) : ℂ)

/-- `K̂(z) = e^{izy} v̂(zδ)`. -/
theorem paperFT_cameraTest {δ : ℝ} (hδ : 0 < δ) (y : ℝ) (z : ℂ) :
    paperFT (cameraTest v δ y) z = cexp (I * z * y) * paperFT (cplx v) (z * δ) := by
  have hδ0 : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  set g : ℝ → ℂ := fun x => cplx v x * cexp (I * (z * δ) * x) with hg
  have e : ∀ u : ℝ, cameraTest v δ y u * cexp (I * z * u) =
      (cexp (I * z * y) * (δ : ℂ)⁻¹) * g ((u - y) / δ) := by
    intro u
    simp only [cameraTest, hg, cplx]
    have h : I * z * (u : ℂ) = I * z * y + I * (z * δ) * (((u - y) / δ : ℝ) : ℂ) := by
      push_cast
      field_simp
      ring
    rw [h, Complex.exp_add]
    push_cast
    ring
  have h1 : (∫ u : ℝ, g ((u - y) / δ)) = ∫ u : ℝ, g (u / δ) :=
    integral_sub_right_eq_self (fun x : ℝ => g (x / δ)) y
  have hg' : paperFT (cplx v) (z * δ) = ∫ x, g x := rfl
  rw [paperFT_def, hg']
  simp_rw [e]
  rw [integral_const_mul, h1, Measure.integral_comp_div g δ, abs_of_pos hδ, Complex.real_smul]
  field_simp

theorem cameraTest_eq_zero (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) {δ y u : ℝ} (hδ : 0 < δ)
    (h : δ < |u - y|) : cameraTest v δ y u = 0 := by
  have h0 : v ((u - y) / δ) = 0 := by
    by_contra hne
    have h1 := hsupp _ hne
    rw [abs_div, abs_of_pos hδ, div_le_one hδ] at h1
    linarith
  simp [cameraTest, h0]

theorem cameraTest_contDiff (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    ContDiff ℝ 2 (cameraTest v δ y) ∧ HasCompactSupport (cameraTest v δ y) := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ 2 fun u : ℝ => v ((u - y) / δ) / δ :=
      (hv.comp ((contDiff_id.sub contDiff_const).div_const δ)).div_const δ
    exact Complex.ofRealCLM.contDiff.comp h1
  · refine hasCompactSupport_of_support_subset_abs (Λ := |y| + δ) fun u hu => ?_
    by_contra hlt
    apply hu
    apply cameraTest_eq_zero hsupp hδ
    have := abs_sub_abs_le_abs_sub u y
    linarith [not_le.mp hlt]

/-! ### The explicit formula and the camera polynomial -/

/-- **The twisted explicit formula of the camera test.** -/
theorem camera_explicit_formula (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) {δ y : ℝ} (hδ : 0 < δ) (hyδ : δ < y) (t : ℝ) :
    (Summable fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℂ) *
        paperFT (cameraTest v δ y) (gammaOf ρ - t)) ∧
    ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
        paperFT (cameraTest v δ y) (gammaOf ρ - t) =
      paperFT (cameraTest v δ y) (I / 2 - t) + paperFT (cameraTest v δ y) (-I / 2 - t)
      - ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
          (cexp (-(t * I * Real.log n)) * cameraTest v δ y (Real.log n))
      + ∫ r : ℝ, paperFT (cameraTest v δ y) r * (mu (r + t) : ℂ) := by
  obtain ⟨hK, hKc⟩ := cameraTest_contDiff hv hsupp hδ y
  obtain ⟨hs, he⟩ := WeilEF.EF_lit_zetaZeroConfig (twist t (cameraTest v δ y))
    (contDiff_twist hK t) (hasCompactSupport_twist hKc t)
  simp_rw [paperFT_twist] at hs he
  rw [literatureRHS_twist] at he
  refine ⟨hs, he.trans ?_⟩
  have hneg : ∀ n : ℕ, cameraTest v δ y (-Real.log n) = 0 := by
    intro n
    refine cameraTest_eq_zero hsupp hδ ?_
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hprime : (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (cexp (-(t * I * Real.log n)) * cameraTest v δ y (Real.log n) +
        cexp (t * I * Real.log n) * cameraTest v δ y (-Real.log n))) =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (cexp (-(t * I * Real.log n)) * cameraTest v δ y (Real.log n)) := by
    refine tsum_congr fun n => ?_
    rw [hneg n, mul_zero, add_zero]
  have hgamma : (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT (cameraTest v δ y) r *
      (EF.gammaBracket (r + t) : ℂ) = ∫ r : ℝ, paperFT (cameraTest v δ y) r * (mu (r + t) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [EF.gammaBracket, mu]
    push_cast
    ring
  rw [hprime, hgamma]

/-- The zero field `Z(t) = Σ_ρ m_ρ K̂(γ_ρ − t − i b_ρ)`. -/
def zeroField (v : ℝ → ℝ) (δ y t : ℝ) : ℂ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
    paperFT (cameraTest v δ y) (gammaOf ρ - t)

/-- The coefficients `Λ(n) K(log n)` of the camera polynomial. -/
def cameraCoeff (v : ℝ → ℝ) (δ y : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * cameraTest v δ y (Real.log n)

/-- The length `⌈e^{y+δ}⌉` of the camera polynomial. -/
def cameraLength (δ y : ℝ) : ℕ := ⌈Real.exp (y + δ)⌉₊

/-- The camera polynomial `Σ_n Λ(n) K(log n) n^{−1/2−it}`. -/
def cameraPoly (v : ℝ → ℝ) (δ y t : ℝ) : ℂ :=
  edPoly (cameraCoeff v δ y) (Finset.Icc 1 (cameraLength δ y)) (displacedLinePt 0 t)

theorem continuous_cameraPoly (δ y : ℝ) : Continuous (cameraPoly v δ y) := by
  have h1 : Continuous fun t : ℝ => displacedLinePt 0 t := by
    unfold displacedLinePt
    fun_prop
  exact (differentiable_edPoly _ fun n hn => (Finset.mem_Icc.mp hn).1).continuous.comp h1

theorem cpow_neg_line {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    ((n : ℝ) : ℂ) ^ (-displacedLinePt 0 t) =
      ((1 / Real.sqrt n : ℝ) : ℂ) * cexp (-(t * I * Real.log n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hs : ((1 / Real.sqrt n : ℝ) : ℂ) = cexp (((-(Real.log n / 2) : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_exp]
    congr 1
    rw [Real.exp_neg, ← Real.log_sqrt hn0.le, Real.exp_log (Real.sqrt_pos.2 hn0), one_div]
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hn0.le, hs, ← Complex.exp_add]
  congr 1
  simp only [displacedLinePt]
  push_cast
  ring

/-- The prime side of the explicit formula is the camera polynomial. -/
theorem tsum_camera_eq_cameraPoly (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) {δ y : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (cexp (-(t * I * Real.log n)) * cameraTest v δ y (Real.log n)) = cameraPoly v δ y t := by
  unfold cameraPoly edPoly
  rw [tsum_eq_sum (s := Finset.Icc 1 (cameraLength δ y))]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [cameraCoeff, cpow_neg_line (Finset.mem_Icc.mp hn).1 t]
    push_cast
    ring
  · intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · have hN : cameraLength δ y < n := by
        by_contra h
        exact hn (Finset.mem_Icc.mpr ⟨hn0, not_lt.mp h⟩)
      have h0 : cameraTest v δ y (Real.log n) = 0 := by
        apply cameraTest_eq_zero hsupp hδ
        have h1 : Real.exp (y + δ) < n :=
          lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
        have h2 : y + δ < Real.log n := (Real.lt_log_iff_exp_lt hnpos).2 h1
        rw [abs_of_pos (by linarith)]
        linarith
      rw [h0]
      simp

theorem zeroField_add_cameraPoly_eq (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ y : ℝ} (hδ : 0 < δ) (hyδ : δ < y) (t : ℝ) :
    zeroField v δ y t + cameraPoly v δ y t =
      paperFT (cameraTest v δ y) (I / 2 - t) + paperFT (cameraTest v δ y) (-I / 2 - t)
      + ∫ r : ℝ, paperFT (cameraTest v δ y) r * (mu (r + t) : ℂ) := by
  have h := (camera_explicit_formula hv hsupp hδ hyδ t).2
  rw [tsum_camera_eq_cameraPoly hsupp hδ t] at h
  unfold zeroField
  rw [h]
  ring

/-! ### Transform bounds -/

/-- The two integral norms of a profile. -/
def profileMass (v : ℝ → ℝ) : ℝ := (∫ u, ‖cplx v u‖) + ∫ u, ‖deriv (deriv (cplx v)) u‖

theorem profileMass_nonneg (v : ℝ → ℝ) : 0 ≤ profileMass v :=
  add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)

/-- `|v̂(w)|(1 + |w|²) ≤ e^{|Im w|}(‖v‖₁ + ‖v''‖₁)`. -/
theorem norm_paperFT_profile_le (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (w : ℂ) :
    ‖paperFT (cplx v) w‖ * (1 + ‖w‖ ^ 2) ≤ Real.exp |w.im| * profileMass v := by
  have hf := contDiff_cplx hv
  have hs := cplx_support hsupp
  have hfi : Integrable (cplx v) :=
    hf.continuous.integrable_of_hasCompactSupport (hasCompactSupport_of_support_subset_abs hs)
  have h0 := norm_paperFT_le hfi hs w
  have h2 := norm_paperFT_mul_sq_le hf hs w
  rw [mul_one] at h0 h2
  unfold profileMass
  rw [mul_add, mul_add, mul_one]
  linarith

/-- `|K̂(z)|(1 + δ²|z|²) ≤ e^{−y Im z + δ|Im z|} (‖v‖₁ + ‖v''‖₁)`. -/
theorem norm_paperFT_camera_le (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (y : ℝ) (z : ℂ) :
    ‖paperFT (cameraTest v δ y) z‖ * (1 + δ ^ 2 * ‖z‖ ^ 2) ≤
      Real.exp (-(z.im * y) + |z.im| * δ) * profileMass v := by
  have hw := norm_paperFT_profile_le hv hsupp (z * (δ : ℂ))
  have him : (z * (δ : ℂ)).im = z.im * δ := by simp
  have hnorm : ‖z * (δ : ℂ)‖ ^ 2 = δ ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    ring
  rw [him, hnorm, abs_mul, abs_of_pos hδ] at hw
  rw [paperFT_cameraTest hδ, norm_mul, norm_cexp_I_mul, Real.exp_add]
  have h := mul_le_mul_of_nonneg_left hw (Real.exp_pos (-(z.im * y))).le
  calc _ = Real.exp (-(z.im * y)) *
        (‖paperFT (cplx v) (z * δ)‖ * (1 + δ ^ 2 * ‖z‖ ^ 2)) := by ring
    _ ≤ _ := h
    _ = _ := by ring

/-- The pole terms are bounded once `e^{y+δ}` is below the height. -/
theorem norm_paperFT_camera_pole_le (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ y t : ℝ} (hδ1 : 1 ≤ δ) (hy : 0 ≤ y) (ht1 : 1 ≤ t) (hN : Real.exp (y + δ) ≤ t) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) (hzt : t ≤ ‖z‖) :
    ‖paperFT (cameraTest v δ y) z‖ ≤ profileMass v := by
  have hδ : 0 < δ := by linarith
  have h := norm_paperFT_camera_le hv hsupp hδ y z
  have hM := profileMass_nonneg v
  have hexp : Real.exp (-(z.im * y) + |z.im| * δ) ≤ t := by
    refine le_trans (Real.exp_le_exp.2 ?_) hN
    have h1 : 0 ≤ (|z.im| + z.im) * y := mul_nonneg (by linarith [neg_abs_le z.im]) hy
    have h2 : |z.im| * y ≤ 1 / 2 * y := mul_le_mul_of_nonneg_right hz hy
    have h3 : |z.im| * δ ≤ 1 / 2 * δ := mul_le_mul_of_nonneg_right hz hδ.le
    nlinarith
  have hfac : t ≤ 1 + δ ^ 2 * ‖z‖ ^ 2 := by
    have h1 : 1 ≤ δ ^ 2 := by nlinarith
    have h2 : t ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by linarith) hzt 2
    nlinarith [sq_nonneg ‖z‖]
  have h3 : ‖paperFT (cameraTest v δ y) z‖ * t ≤ t * profileMass v := by
    calc _ ≤ ‖paperFT (cameraTest v δ y) z‖ * (1 + δ ^ 2 * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hfac (norm_nonneg _)
      _ ≤ _ := h
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp hM
  have ht0 : 0 < t := by linarith
  nlinarith

/-- `|μ(τ)| ≤ A + log(2 + |τ|)`. -/
theorem exists_abs_mu_le : ∃ A : ℝ, ∀ τ : ℝ, |mu τ| ≤ A + Real.log (2 + |τ|) := by
  obtain ⟨C, hC⟩ := gammaFacts.stirling
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    gammaFacts.smooth.continuous.continuousOn
  refine ⟨max (|C| + Real.log (2 * π)) B, fun τ => ?_⟩
  have hlog0 : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
  rcases le_or_gt |τ| 1 with h | h
  · have hτ : τ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
    have := hB τ hτ
    rw [Real.norm_eq_abs] at this
    linarith [le_max_right (|C| + Real.log (2 * π)) B]
  · have h1 : 1 ≤ |τ| := h.le
    have hs := hC τ h1
    have hτ2 : (1 : ℝ) ≤ τ ^ 2 := by nlinarith [sq_abs τ]
    have hCτ : C / τ ^ 2 ≤ |C| := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [le_abs_self C, abs_nonneg C]
    have hpi : 0 < 2 * π := by positivity
    have hlogτ : 0 ≤ Real.log |τ| := Real.log_nonneg h1
    have hlogpi : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have habs : |Real.log (|τ| / (2 * π))| ≤ Real.log (2 + |τ|) + Real.log (2 * π) := by
      rw [Real.log_div (by linarith) hpi.ne']
      have : Real.log |τ| ≤ Real.log (2 + |τ|) := Real.log_le_log (by linarith) (by linarith)
      rw [abs_le]; constructor <;> linarith
    have hfac : |(1 / (2 * π)) * Real.log (|τ| / (2 * π))| ≤ |Real.log (|τ| / (2 * π))| := by
      rw [abs_mul, abs_of_pos (by positivity)]
      have : 1 / (2 * π) ≤ 1 := by rw [div_le_one hpi]; linarith [Real.pi_gt_three]
      nlinarith [abs_nonneg (Real.log (|τ| / (2 * π)))]
    have := abs_sub_abs_le_abs_sub (mu τ) ((1 / (2 * π)) * Real.log (|τ| / (2 * π)))
    linarith [le_max_left (|C| + Real.log (2 * π)) B]

theorem log_two_add_abs_add_le (r t : ℝ) :
    Real.log (2 + |r + t|) ≤ Real.log (2 + |t|) + Real.log (1 + |r|) := by
  have hr := abs_nonneg r
  have ht := abs_nonneg t
  rw [← Real.log_mul (by positivity) (by positivity)]
  refine Real.log_le_log (by positivity) ?_
  have := abs_add_le r t
  nlinarith [mul_nonneg hr ht]

/-- The logarithmic tail against the Lorentzian of width `1/δ`, uniformly in `δ ≥ 1`. -/
theorem inv_mul_log_le (r : ℝ) {δ : ℝ} (hδ : 1 ≤ δ) :
    (1 + (δ * r) ^ 2)⁻¹ * Real.log (1 + |r|) ≤ 8 * (1 + ‖r‖) ^ (-(7 / 4 : ℝ)) := by
  rw [Real.norm_eq_abs]
  have hr := abs_nonneg r
  set x := 1 + |r| with hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 4 by norm_num)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have ha : x ^ 2 ≤ 2 * (1 + (δ * r) ^ 2) := by
    have h1 : 1 ≤ δ ^ 2 := by nlinarith
    have h2 : r ^ 2 ≤ δ ^ 2 * r ^ 2 := le_mul_of_one_le_left (sq_nonneg r) h1
    have h3 : |r| ^ 2 = r ^ 2 := sq_abs r
    rw [mul_pow, hx]
    nlinarith [sq_nonneg (|r| - 1)]
  have hinv : (1 + (δ * r) ^ 2)⁻¹ ≤ 2 * (x ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, inv_eq_one_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hrpow : (x ^ 2)⁻¹ * x ^ (1 / 4 : ℝ) = x ^ (-(7 / 4 : ℝ)) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]
    norm_num
  calc (1 + (δ * r) ^ 2)⁻¹ * Real.log x
      ≤ (2 * (x ^ 2)⁻¹) * (x ^ (1 / 4 : ℝ) / (1 / 4)) :=
        mul_le_mul hinv hlog hlog0 (by positivity)
    _ = 8 * ((x ^ 2)⁻¹ * x ^ (1 / 4 : ℝ)) := by ring
    _ = 8 * x ^ (-(7 / 4 : ℝ)) := by rw [hrpow]

/-- **The Gamma term.** Its size is `≪ 1 + log t/δ`, bounded once the camera is as wide as `log t`. -/
theorem exists_norm_gamma_camera_le (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ y t : ℝ, 1 ≤ δ →
      ‖∫ r : ℝ, paperFT (cameraTest v δ y) r * (mu (r + t) : ℂ)‖ ≤
        C * (1 + Real.log (2 + |t|) / δ) := by
  obtain ⟨A, hA⟩ := exists_abs_mu_le
  have hM := profileMass_nonneg v
  set M := profileMass v with hMdef
  have hJi : Integrable (fun r : ℝ => (1 + ‖r‖) ^ (-(7 / 4 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  set J := ∫ r : ℝ, (1 + ‖r‖) ^ (-(7 / 4 : ℝ)) with hJdef
  have hJ : 0 ≤ J := integral_nonneg fun r => by positivity
  have hX : 0 ≤ M * π := by positivity
  have hY : 0 ≤ 8 * M * J := by positivity
  refine ⟨M * π * (|A| + 1) + 8 * M * J, by positivity, fun δ y t hδ => ?_⟩
  have hδ0 : 0 < δ := by linarith
  set P := Real.log (2 + |t|) with hPdef
  have hP : 0 ≤ P := Real.log_nonneg (by linarith [abs_nonneg t])
  have hLi : Integrable (fun r : ℝ => (1 + (δ * r) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' hδ0.ne'
  have hLint : ∫ r : ℝ, (1 + (δ * r) ^ 2)⁻¹ = π / δ := by
    rw [Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) δ,
      integral_univ_inv_one_add_sq, abs_of_pos (inv_pos.2 hδ0), smul_eq_mul]
    field_simp
  have hbound : ∀ r : ℝ, ‖paperFT (cameraTest v δ y) r * (mu (r + t) : ℂ)‖ ≤
      M * (|A| + P) * (1 + (δ * r) ^ 2)⁻¹ + 8 * M * (1 + ‖r‖) ^ (-(7 / 4 : ℝ)) := by
    intro r
    have ha : 0 < 1 + (δ * r) ^ 2 := by positivity
    have hK : ‖paperFT (cameraTest v δ y) r‖ ≤ M * (1 + (δ * r) ^ 2)⁻¹ := by
      have h := norm_paperFT_camera_le hv hsupp hδ0 y (r : ℂ)
      simp only [Complex.ofReal_im, zero_mul, neg_zero, abs_zero, add_zero, Real.exp_zero,
        one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
      rw [← mul_pow] at h
      rw [← div_eq_mul_inv, le_div_iff₀ ha]
      exact h
    have hmu : |mu (r + t)| ≤ |A| + P + Real.log (1 + |r|) := by
      have h1 := hA (r + t)
      have h2 := log_two_add_abs_add_le r t
      linarith [le_abs_self A]
    have hℓ0 : 0 ≤ Real.log (1 + |r|) := Real.log_nonneg (by linarith [abs_nonneg r])
    have htail := inv_mul_log_le r hδ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖paperFT (cameraTest v δ y) r‖ * |mu (r + t)|
        ≤ (M * (1 + (δ * r) ^ 2)⁻¹) * (|A| + P + Real.log (1 + |r|)) :=
          mul_le_mul hK hmu (abs_nonneg _) (by positivity)
      _ = M * (|A| + P) * (1 + (δ * r) ^ 2)⁻¹ +
            M * ((1 + (δ * r) ^ 2)⁻¹ * Real.log (1 + |r|)) := by ring
      _ ≤ M * (|A| + P) * (1 + (δ * r) ^ 2)⁻¹ + M * (8 * (1 + ‖r‖) ^ (-(7 / 4 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hLi' : Integrable (fun r : ℝ => M * (|A| + P) * (1 + (δ * r) ^ 2)⁻¹) := hLi.const_mul _
  have hJi' : Integrable (fun r : ℝ => 8 * M * (1 + ‖r‖) ^ (-(7 / 4 : ℝ))) := hJi.const_mul _
  have hgi : Integrable (fun r : ℝ => M * (|A| + P) * (1 + (δ * r) ^ 2)⁻¹ +
      8 * M * (1 + ‖r‖) ^ (-(7 / 4 : ℝ))) := hLi'.add hJi'
  have h := norm_integral_le_of_norm_le hgi (Eventually.of_forall hbound)
  refine h.trans ?_
  have hsum : (∫ r : ℝ, (M * (|A| + P) * (1 + (δ * r) ^ 2)⁻¹ +
      8 * M * (1 + ‖r‖) ^ (-(7 / 4 : ℝ)))) = M * (|A| + P) * (π / δ) + 8 * M * J := by
    rw [integral_add hLi' hJi', integral_const_mul, integral_const_mul, hLint]
  rw [hsum]
  have hq0 : 0 ≤ δ⁻¹ := (inv_pos.2 hδ0).le
  have hq1 : δ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hδ
  have ha1 := abs_nonneg A
  rw [div_eq_mul_inv, div_eq_mul_inv]
  nlinarith [mul_nonneg (mul_nonneg hX ha1) (sub_nonneg.2 hq1),
    mul_nonneg (mul_nonneg hX ha1) (mul_nonneg hP hq0), mul_nonneg hY (mul_nonneg hP hq0)]

/-- **The camera equation.** The zero field and the camera polynomial agree up to `≪ 1 + log t/δ`. -/
theorem exists_norm_zeroField_add_cameraPoly_le (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ y t : ℝ, 1 ≤ δ → δ < y → 1 ≤ t → Real.exp (y + δ) ≤ t →
      ‖zeroField v δ y t + cameraPoly v δ y t‖ ≤ C * (1 + Real.log (2 + t) / δ) := by
  obtain ⟨CG, hCG0, hCG⟩ := exists_norm_gamma_camera_le hv hsupp
  have hM := profileMass_nonneg v
  refine ⟨CG + 2 * profileMass v, by positivity, fun δ y t hδ1 hyδ ht1 hN => ?_⟩
  have hδ0 : 0 < δ := by linarith
  have hy0 : 0 ≤ y := by linarith
  have ht0 : 0 ≤ t := by linarith
  rw [zeroField_add_cameraPoly_eq hv hsupp hδ0 hyδ t]
  have hp1 : ‖paperFT (cameraTest v δ y) (I / 2 - t)‖ ≤ profileMass v := by
    refine norm_paperFT_camera_pole_le hv hsupp hδ1 hy0 ht1 hN ?_ ?_
    · have him : (I / 2 - (t : ℂ)).im = 1 / 2 := by simp
      rw [him, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    · have h := Complex.abs_re_le_norm (I / 2 - (t : ℂ))
      have hre : (I / 2 - (t : ℂ)).re = -t := by simp
      rw [hre, abs_neg, abs_of_nonneg ht0] at h
      exact h
  have hp2 : ‖paperFT (cameraTest v δ y) (-I / 2 - t)‖ ≤ profileMass v := by
    refine norm_paperFT_camera_pole_le hv hsupp hδ1 hy0 ht1 hN ?_ ?_
    · have him : (-I / 2 - (t : ℂ)).im = -(1 / 2) := by
        simp
        norm_num
      rw [him, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    · have h := Complex.abs_re_le_norm (-I / 2 - (t : ℂ))
      have hre : (-I / 2 - (t : ℂ)).re = -t := by simp
      rw [hre, abs_neg, abs_of_nonneg ht0] at h
      exact h
  have hG := hCG δ y t hδ1
  rw [abs_of_nonneg ht0] at hG
  have hq : 0 ≤ Real.log (2 + t) / δ := div_nonneg (Real.log_nonneg (by linarith)) hδ0.le
  have h3 := norm_add₃_le (a := paperFT (cameraTest v δ y) (I / 2 - t))
    (b := paperFT (cameraTest v δ y) (-I / 2 - t))
    (c := ∫ r : ℝ, paperFT (cameraTest v δ y) r * (mu (r + t) : ℂ))
  nlinarith [mul_nonneg hM hq]

/-! ### The mean square of the camera polynomial -/

theorem exists_abs_profile_le (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) :
    ∃ S : ℝ, 0 < S ∧ ∀ u, |v u| ≤ S := by
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    hv.continuous.continuousOn
  refine ⟨|B| + 1, by positivity, fun u => ?_⟩
  by_cases h : v u = 0
  · rw [h, abs_zero]
    positivity
  · have h1 := abs_le.mp (hsupp u h)
    have h2 := hB u ⟨h1.1, h1.2⟩
    rw [Real.norm_eq_abs] at h2
    linarith [le_abs_self B]

theorem sum_cameraCoeff_le {S : ℝ} (hS : ∀ u, |v u| ≤ S) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖cameraCoeff v δ y n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) ≤
      (S / δ) ^ 2 * ∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.vonMangoldt n) ^ (2 : ℕ) / (n : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hpow : (n : ℝ) ^ (2 * (0 : ℝ) - 1) = (n : ℝ)⁻¹ := by
    rw [show 2 * (0 : ℝ) - 1 = -1 by norm_num, Real.rpow_neg_one]
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hnorm : ‖cameraCoeff v δ y n‖ ≤ ArithmeticFunction.vonMangoldt n * (S / δ) := by
    rw [cameraCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ, cameraTest,
      Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hδ]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hS _) hδ.le) hΛ
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [hpow, div_eq_mul_inv]
  calc _ ≤ (ArithmeticFunction.vonMangoldt n * (S / δ)) ^ 2 * (n : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = _ := by ring

/-- **The mean square of the camera polynomial.** For `δ = cL` and any centre with `y + δ ≤ (1−c)L` it is
`≤ 8 S² T/c²`, uniformly in `c` and `y`: the mean value theorem at length `≤ T^{1−c}`, the diagonal
`log²N/δ²` being bounded. -/
theorem integral_cameraPoly_sq_le {S CΛ : ℝ} (hS : ∀ u, |v u| ≤ S)
    (hCΛ : ∀ N : ℕ, 1 ≤ N → ∑ k ∈ Finset.Icc 1 N,
      (ArithmeticFunction.vonMangoldt k) ^ (2 : ℕ) / (k : ℝ) ≤
        Real.log (N : ℝ) * (Real.log (N : ℝ) + CΛ))
    {c T y : ℝ} (hc0 : 0 < c) (hc : c < 1 / 3) (hT3 : 3 ≤ T) (hL2 : 2 ≤ Real.log T)
    (hLd : 64 / c ^ 2 ≤ Real.log T) (hLC : 1 + |CΛ| ≤ Real.log T)
    (hy0 : 0 ≤ y + c * Real.log T) (hy : y + c * Real.log T ≤ (1 - c) * Real.log T) :
    ∫ t in T..(2 * T), ‖cameraPoly v (c * Real.log T) y t‖ ^ 2 ≤ 8 * S ^ 2 / c ^ 2 * T := by
  set L := Real.log T with hLdef
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := by linarith
  have hTexp : T = Real.exp L := (Real.exp_log hT0).symm
  set δ := c * L with hδdef
  have hδ0 : 0 < δ := by positivity
  set X := Real.exp ((1 - c) * L) with hXdef
  have hX1 : 1 ≤ X := Real.one_le_exp (mul_nonneg (by linarith) hL0.le)
  set X' := Real.exp (y + δ) with hX'def
  have hX'1 : 1 ≤ X' := Real.one_le_exp hy0
  have hX'X : X' ≤ X := Real.exp_le_exp.2 hy
  set N := cameraLength δ y with hNdef
  have hN1 : X' ≤ N := by
    rw [hNdef, cameraLength]
    exact Nat.le_ceil _
  have hN2 : (N : ℝ) ≤ 2 * X := by
    have h := Nat.ceil_lt_add_one (a := X') (by linarith)
    have e : (N : ℝ) = (⌈X'⌉₊ : ℝ) := by rw [hNdef, cameraLength]
    rw [e]
    linarith
  have hNpos : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := hX'1.trans hN1
    exact_mod_cast this
  have hNR : (0 : ℝ) < N := by linarith
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (hX'1.trans hN1)
  have hlogN : Real.log (N : ℝ) ≤ L + 1 := by
    have h1 : Real.log (N : ℝ) ≤ Real.log (2 * X) := Real.log_le_log hNR hN2
    rw [Real.log_mul (by norm_num) (by positivity), hXdef, Real.log_exp] at h1
    have h2 := Real.log_two_lt_d9
    nlinarith
  -- the off-diagonal term of the mean value theorem is below `T`
  have hexp : 16 * (2 + L) ≤ Real.exp (c * L) := by
    have h1 := Real.quadratic_le_exp_of_nonneg (x := c * L) (by positivity)
    have h2 : 64 ≤ c ^ 2 * L := by
      rw [div_le_iff₀ (by positivity)] at hLd
      linarith
    have h3 : 64 * L ≤ c ^ 2 * L * L := mul_le_mul_of_nonneg_right h2 hL0.le
    nlinarith [mul_pos hc0 hL0]
  have hTX : T = X * Real.exp (c * L) := by
    rw [hTexp, hXdef, ← Real.exp_add]
    congr 1
    ring
  have hoff : 8 * (N : ℝ) * (1 + Real.log (N : ℝ)) ≤ T := by
    have h1 : 8 * (N : ℝ) * (1 + Real.log (N : ℝ)) ≤ 8 * (2 * X) * (2 + L) := by
      have : 1 + Real.log (N : ℝ) ≤ 2 + L := by linarith
      gcongr
    have hX0 : 0 < X := by linarith
    calc _ ≤ 8 * (2 * X) * (2 + L) := h1
      _ = X * (16 * (2 + L)) := by ring
      _ ≤ X * Real.exp (c * L) := mul_le_mul_of_nonneg_left hexp hX0.le
      _ = T := hTX.symm
  have hmv := integral_normSq_edPoly_displaced_le 0 (cameraCoeff v δ y) N T (2 * T)
  rw [show 2 * T - T = T by ring] at hmv
  have hE0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖cameraCoeff v δ y n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) :=
    Finset.sum_nonneg fun n _ => by positivity
  have hE : ∑ n ∈ Finset.Icc 1 N, ‖cameraCoeff v δ y n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) ≤
      4 * S ^ 2 / c ^ 2 := by
    refine (sum_cameraCoeff_le hS hδ0 y N).trans ?_
    have h1 := hCΛ N hNpos
    have h2 : Real.log (N : ℝ) * (Real.log (N : ℝ) + CΛ) ≤ (2 * L) * (2 * L) := by
      have h3 : Real.log (N : ℝ) + CΛ ≤ 2 * L := by linarith [le_abs_self CΛ]
      have h4 : Real.log (N : ℝ) ≤ 2 * L := by linarith
      calc _ ≤ Real.log (N : ℝ) * (2 * L) := mul_le_mul_of_nonneg_left h3 hlogN0
        _ ≤ _ := mul_le_mul_of_nonneg_right h4 (by positivity)
    calc (S / δ) ^ 2 * _ ≤ (S / δ) ^ 2 * ((2 * L) * (2 * L)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = 4 * S ^ 2 / c ^ 2 := by
          rw [hδdef]
          field_simp
          ring
  calc _ ≤ (T + 8 * (N : ℝ) * (1 + Real.log (N : ℝ))) *
        ∑ n ∈ Finset.Icc 1 N, ‖cameraCoeff v δ y n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) := hmv
    _ ≤ (T + T) * (4 * S ^ 2 / c ^ 2) := by
        refine mul_le_mul (by linarith) hE hE0 (by linarith)
    _ = _ := by ring

/-- Chebyshev on a dyadic range for a continuous function. -/
theorem volume_norm_ge_le {f : ℝ → ℂ} (hf : Continuous f) {T B lam : ℝ} (hT : 0 < T) (hlam : 0 < lam)
    (hB : ∫ t in T..(2 * T), ‖f t‖ ^ 2 ≤ B) :
    volume {t | t ∈ Ioc T (2 * T) ∧ lam ≤ ‖f t‖} ≤ ENNReal.ofReal (B / lam ^ 2) := by
  have hle : T ≤ 2 * T := by linarith
  have hM0 : ∀ t, 0 ≤ ‖f t‖ ^ 2 := fun t => by positivity
  have hMI : Integrable (fun t => ‖f t‖ ^ 2) (volume.restrict (Ioc T (2 * T))) :=
    (hf.norm.pow 2).integrableOn_Ioc
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Ioc T (2 * T)))
    (Eventually.of_forall hM0) hMI (lam ^ 2)
  rw [← intervalIntegral.integral_of_le hle, measureReal_def] at hmark
  have hfinite : volume.restrict (Ioc T (2 * T)) {t | lam ^ 2 ≤ ‖f t‖ ^ 2} ≠ ⊤ :=
    measure_ne_top_of_subset (Set.subset_univ _) (by
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hsub : {t | t ∈ Ioc T (2 * T) ∧ lam ≤ ‖f t‖} ⊆
      {t | lam ^ 2 ≤ ‖f t‖ ^ 2} ∩ Ioc T (2 * T) := fun t ht =>
    ⟨pow_le_pow_left₀ hlam.le ht.2 2, ht.1⟩
  calc volume {t | t ∈ Ioc T (2 * T) ∧ lam ≤ ‖f t‖}
      ≤ volume ({t | lam ^ 2 ≤ ‖f t‖ ^ 2} ∩ Ioc T (2 * T)) := measure_mono hsub
    _ = volume.restrict (Ioc T (2 * T)) {t | lam ^ 2 ≤ ‖f t‖ ^ 2} :=
        (Measure.restrict_apply' measurableSet_Ioc).symm
    _ = ENNReal.ofReal ((volume.restrict (Ioc T (2 * T)) {t | lam ^ 2 ≤ ‖f t‖ ^ 2}).toReal) :=
        (ENNReal.ofReal_toReal hfinite).symm
    _ ≤ ENNReal.ofReal (B / lam ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ (by positivity)]
        linarith

/-- **Chebyshev for the zero field, uniform in the camera.** For `δ = cL`, any centre with `δ < y`,
`y + δ ≤ (1−c)L`, and every `λ > 0`, the field exceeds `λ` on measure `≤ (C₀/c²) T/λ²` in `(T, 2T]`. -/
theorem exists_volume_zeroField_ge_le_uniform (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) :
    ∃ C₀ L₀ : ℝ, 0 < C₀ ∧ ∀ T c y lam : ℝ, 3 ≤ T → L₀ ≤ Real.log T → 0 < c → c < 1 / 3 →
      1 / c ≤ Real.log T → 64 / c ^ 2 ≤ Real.log T → c * Real.log T < y →
      y + c * Real.log T ≤ (1 - c) * Real.log T → 0 < lam →
      volume {t | t ∈ Ioc T (2 * T) ∧ lam ≤ ‖zeroField v (c * Real.log T) y t‖} ≤
        ENNReal.ofReal (C₀ / c ^ 2 * T / lam ^ 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_zeroField_add_cameraPoly_le hv hsupp
  obtain ⟨S, hS0, hS⟩ := exists_abs_profile_le hv hsupp
  obtain ⟨CΛ, hCΛ⟩ := exists_sum_vonMangoldt_sq_div_le
  refine ⟨32 * S ^ 2 + 36 * C₁ ^ 2 + 1, max 2 (1 + |CΛ|), by positivity, ?_⟩
  intro T c y lam hT3 hL₀ hc0 hc hLc hLd hyδ hyL hlam
  have hL2 : 2 ≤ Real.log T := (le_max_left _ _).trans hL₀
  have hLC : 1 + |CΛ| ≤ Real.log T := (le_max_right _ _).trans hL₀
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  set L := Real.log T with hLdef
  have hTexp : Real.exp L = T := Real.exp_log hT0
  have hδ1 : 1 ≤ c * L := by
    rw [div_le_iff₀ hc0] at hLc
    linarith
  have hδ0 : 0 < c * L := by linarith
  have hlamsq : 0 < lam ^ 2 := by positivity
  have hc2 : 0 < c ^ 2 := by positivity
  set E := C₁ * (1 + 2 / c) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hE3 : E ^ 2 ≤ 9 * C₁ ^ 2 / c ^ 2 := by
    have h1 : 1 + 2 / c ≤ 3 / c := by
      rw [le_div_iff₀ hc0]
      have : (1 + 2 / c) * c = c + 2 := by
        field_simp
      rw [this]
      linarith
    have h2 : E ≤ C₁ * (3 / c) := mul_le_mul_of_nonneg_left h1 hC₁0
    calc E ^ 2 ≤ (C₁ * (3 / c)) ^ 2 := pow_le_pow_left₀ hE0 h2 2
      _ = _ := by
        field_simp
        ring
  have hclose : ∀ t ∈ Ioc T (2 * T), ‖zeroField v (c * L) y t + cameraPoly v (c * L) y t‖ ≤ E := by
    intro t ht
    have ht1 : 1 ≤ t := by linarith [ht.1]
    have hN : Real.exp (y + c * L) ≤ t := by
      have h1 : Real.exp (y + c * L) ≤ Real.exp L := Real.exp_le_exp.2 (by nlinarith)
      linarith [ht.1]
    refine (hC₁ _ _ t hδ1 hyδ ht1 hN).trans (mul_le_mul_of_nonneg_left ?_ hC₁0)
    have hlog : Real.log (2 + t) ≤ 2 * L := by
      have h1 : 2 + t ≤ T ^ 2 := by nlinarith [ht.2]
      calc Real.log (2 + t) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) h1
        _ = 2 * L := by rw [Real.log_pow, ← hLdef]; norm_num
    have hq : Real.log (2 + t) / (c * L) ≤ 2 / c := by
      rw [div_le_div_iff₀ hδ0 hc0]
      nlinarith
    linarith
  have hfinal : ∀ B : ℝ, B ≤ (32 * S ^ 2 + 36 * C₁ ^ 2 + 1) / c ^ 2 →
      B * T / lam ^ 2 ≤ (32 * S ^ 2 + 36 * C₁ ^ 2 + 1) / c ^ 2 * T / lam ^ 2 := by
    intro B hB
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB hT0.le) hlamsq.le
  rcases le_or_gt (2 * E) lam with hbig | hsmall
  · have hhalf : 0 < lam / 2 := by linarith
    have hint := integral_cameraPoly_sq_le (v := v) (y := y) hS hCΛ hc0 hc hT3 hL2 hLd hLC
      (by linarith) hyL
    have hvol := volume_norm_ge_le (continuous_cameraPoly (v := v) (c * L) y) hT0 hhalf hint
    refine (measure_mono ?_).trans (hvol.trans (ENNReal.ofReal_le_ofReal ?_))
    · rintro t ⟨ht, hlt⟩
      refine ⟨ht, ?_⟩
      have h1 := hclose t ht
      have h2 := norm_sub_le (zeroField v (c * L) y t + cameraPoly v (c * L) y t)
        (cameraPoly v (c * L) y t)
      rw [add_sub_cancel_right] at h2
      linarith
    · have e : 8 * S ^ 2 / c ^ 2 * T / (lam / 2) ^ 2 = (32 * S ^ 2 / c ^ 2) * T / lam ^ 2 := by
        field_simp
        ring
      rw [e]
      refine hfinal _ ?_
      rw [div_le_div_iff_of_pos_right hc2]
      nlinarith [sq_nonneg C₁]
  · refine (measure_mono fun t ht => ht.1).trans ?_
    rw [Real.volume_Ioc]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : lam ^ 2 ≤ 4 * E ^ 2 := by nlinarith
    have h2 : 2 * T - T ≤ (4 * E ^ 2) * T / lam ^ 2 := by
      rw [le_div_iff₀ hlamsq]
      have : 2 * T - T = T := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left h1 hT0.le |>.trans (by nlinarith)
    refine h2.trans (hfinal _ ?_)
    have h3 : 4 * E ^ 2 ≤ 36 * C₁ ^ 2 / c ^ 2 := by
      have e : 36 * C₁ ^ 2 / c ^ 2 = 4 * (9 * C₁ ^ 2 / c ^ 2) := by ring
      rw [e]
      linarith
    refine h3.trans ?_
    rw [div_le_div_iff_of_pos_right hc2]
    nlinarith [sq_nonneg S]

/-! ### The amplitude of one zero -/

theorem gammaOf_sub_re (ρ : ℂ) (t : ℝ) : (gammaOf ρ - t).re = ρ.im - t := by
  simp [gammaOf, Complex.div_I]

theorem gammaOf_sub_im (ρ : ℂ) (t : ℝ) : (gammaOf ρ - t).im = -(ρ.re - 1 / 2) := by
  simp [gammaOf, Complex.div_I]

/-- **The amplitude of a zero.** On its window `|t − γ| ≤ 1/(10δ)` a zero of depth `b ≥ 0` has transform
at least `½ (∫v) e^{b(y−δ)}`: the phase of `v̂` turns by at most `1/10`, and `u ≥ y − δ` on the support. -/
theorem norm_paperFT_camera_ge (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {ρ : ℂ} {t : ℝ} (hb : 1 / 2 ≤ ρ.re)
    (ht : |t - ρ.im| ≤ 1 / (10 * δ)) :
    1 / 2 * (∫ u, v u) * Real.exp ((ρ.re - 1 / 2) * (y - δ)) ≤
      ‖paperFT (cameraTest v δ y) (gammaOf ρ - t)‖ := by
  set b := ρ.re - 1 / 2 with hbdef
  have hb0 : 0 ≤ b := by linarith
  set z : ℂ := gammaOf ρ - t with hz
  have hzre : z.re = ρ.im - t := gammaOf_sub_re ρ t
  have hzim : z.im = -b := gammaOf_sub_im ρ t
  set w : ℂ := z * (δ : ℂ) with hw
  have hwre : w.re = (ρ.im - t) * δ := by simp [hw, hzre]
  have hwim : w.im = -b * δ := by simp [hw, hzim]
  set f : ℝ → ℂ := fun u => cplx v u * cexp (I * w * u) with hf
  have hscs : HasCompactSupport (cplx v) :=
    hasCompactSupport_of_support_subset_abs (cplx_support hsupp)
  have hfc : Continuous f :=
    (contDiff_cplx hv).continuous.mul (by fun_prop)
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport hscs.mul_right
  have hvi : Integrable v :=
    hv.continuous.integrable_of_hasCompactSupport (hasCompactSupport_of_support_subset_abs hsupp)
  have hre : ∀ u : ℝ, (f u).re = v u * (Real.exp (b * δ * u) * Real.cos ((ρ.im - t) * δ * u)) := by
    intro u
    simp only [hf, cplx]
    rw [Complex.re_ofReal_mul, Complex.exp_re]
    have h1 : (I * w * (u : ℂ)).re = b * δ * u := by
      simp [hwim]
    have h2 : (I * w * (u : ℂ)).im = (ρ.im - t) * δ * u := by
      simp [hwre]
    rw [h1, h2]
  have hlow : ∀ u : ℝ, 1 / 2 * Real.exp (-(b * δ)) * v u ≤ (f u).re := by
    intro u
    rw [hre]
    by_cases hu : v u = 0
    · simp [hu]
    have hu1 := hsupp u hu
    have hu2 := abs_le.mp hu1
    have hexp : Real.exp (-(b * δ)) ≤ Real.exp (b * δ * u) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_nonneg (mul_nonneg hb0 hδ.le) (by linarith [hu2.1] : 0 ≤ 1 + u)
      nlinarith
    set x := (ρ.im - t) * δ * u with hx
    have hx1 : |x| ≤ 1 / 10 := by
      rw [hx, abs_mul, abs_mul, abs_sub_comm, abs_of_pos hδ]
      have h1 : |t - ρ.im| * δ ≤ 1 / 10 := by
        have h2 := mul_le_mul_of_nonneg_right ht hδ.le
        have e : 1 / (10 * δ) * δ = 1 / 10 := by field_simp
        linarith
      calc |t - ρ.im| * δ * |u| ≤ 1 / 10 * 1 :=
            mul_le_mul h1 hu1 (abs_nonneg _) (by norm_num)
        _ = 1 / 10 := by norm_num
    have hx2 : x ^ 2 ≤ 1 / 100 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg x]
    have hcos : 1 / 2 ≤ Real.cos x := by
      have := Real.one_sub_sq_div_two_le_cos (x := x)
      linarith
    calc 1 / 2 * Real.exp (-(b * δ)) * v u = v u * (Real.exp (-(b * δ)) * (1 / 2)) := by ring
      _ ≤ v u * (Real.exp (b * δ * u) * Real.cos x) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hexp hcos (by norm_num) (Real.exp_pos _).le) (hv0 u)
  have hreI : (∫ u, (f u).re) = (paperFT (cplx v) w).re :=
    Complex.reCLM.integral_comp_comm hfi
  have hge : 1 / 2 * Real.exp (-(b * δ)) * (∫ u, v u) ≤ (paperFT (cplx v) w).re := by
    rw [← hreI, ← integral_const_mul]
    exact integral_mono (hvi.const_mul _) hfi.re hlow
  have hnorm : (paperFT (cplx v) w).re ≤ ‖paperFT (cplx v) w‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  rw [paperFT_cameraTest hδ, ← hw, norm_mul, norm_cexp_I_mul, hzim]
  calc 1 / 2 * (∫ u, v u) * Real.exp (b * (y - δ))
      = Real.exp (b * y) * (1 / 2 * Real.exp (-(b * δ)) * ∫ u, v u) := by
        rw [show b * (y - δ) = b * y + -(b * δ) by ring, Real.exp_add]
        ring
    _ ≤ Real.exp (b * y) * ‖paperFT (cplx v) w‖ :=
        mul_le_mul_of_nonneg_left (hge.trans hnorm) (Real.exp_pos _).le
    _ = _ := by
        congr 2
        ring

/-! ### Dominant zeros -/

/-- `ρ` dominates its camera window: on `|t − γ| ≤ 1/(10δ)` the whole zero field has at least half the
size of the term of `ρ`. -/
def DominatesWindow (v : ℝ → ℝ) (δ y : ℝ) (ρ : ℂ) : Prop :=
  ∀ t : ℝ, |t - ρ.im| ≤ 1 / (10 * δ) →
    ‖paperFT (cameraTest v δ y) (gammaOf ρ - t)‖ ≤ 2 * ‖zeroField v δ y t‖

/-- A camera profile exists. -/
theorem exists_camera_profile :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ (∀ u, v u ≠ 0 → |u| ≤ 1) ∧ (∀ u, 0 ≤ v u) ∧ 0 < ∫ u, v u := by
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨f, f.contDiff, fun u hu => ?_, fun u => f.nonneg, f.integral_pos⟩
  have h : u ∈ Function.support f := hu
  rw [f.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at h
  exact h.le

/-- The pairwise disjoint windows of separated ordinates fill their measure. -/
theorem volume_biUnion_windows_eq {ι : Type*} (S : Finset ι) (g : ι → ℝ) {r : ℝ}
    (hsep : ∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 2 * r ≤ |g ρ - g ρ'|) :
    volume (⋃ ρ ∈ S, Ioo (g ρ - r) (g ρ + r)) = ENNReal.ofReal ((S.card : ℝ) * (2 * r)) := by
  classical
  have hdisj : (S : Set ι).PairwiseDisjoint fun ρ => Ioo (g ρ - r) (g ρ + r) := by
    intro ρ hρ ρ' hρ' hne
    refine Set.disjoint_left.2 fun t h1 h2 => ?_
    have hs := hsep ρ hρ ρ' hρ' hne
    have : |g ρ - g ρ'| < 2 * r := by
      rw [abs_lt]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    linarith
  rw [measure_biUnion_finset hdisj fun _ _ => measurableSet_Ioo]
  simp only [Real.volume_Ioo]
  have e : ∀ ρ : ι, g ρ + r - (g ρ - r) = 2 * r := fun ρ => by ring
  simp only [e, Finset.sum_const, nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (p := (S.card : ℝ)) (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- **The prime camera bounds separated dominant zeros, uniformly in the camera.** At `δ = cL`,
`y = (1−2c)L` the dominant zeros of depth `≥ α/L` in `[T+1, 2T−1]`, separated by `1/(5δ)`, number
`≤ (C₁/c) T L e^{−2(1−3c)α}`. -/
theorem exists_card_dominant_zeros_le_uniform (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) :
    ∃ C₁ L₀ : ℝ, 0 < C₁ ∧ ∀ (T c α : ℝ) (S : Finset ℂ), 3 ≤ T → L₀ ≤ Real.log T → 0 < c → c < 1 / 3 →
      1 / c ≤ Real.log T → 64 / c ^ 2 ≤ Real.log T → 0 ≤ α →
      (∀ ρ ∈ S, 1 / 2 + α / Real.log T ≤ ρ.re ∧ T + 1 ≤ ρ.im ∧ ρ.im ≤ 2 * T - 1 ∧
        DominatesWindow v (c * Real.log T) ((1 - 2 * c) * Real.log T) ρ) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (c * Real.log T)) ≤ |ρ.im - ρ'.im|) →
      (S.card : ℝ) ≤ C₁ / c * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) := by
  obtain ⟨C₀, L₁, hC₀0, hvol⟩ := exists_volume_zeroField_ge_le_uniform hv hsupp
  set Iv := ∫ u, v u with hIvdef
  refine ⟨80 * C₀ / Iv ^ 2, max 1 L₁, by positivity, ?_⟩
  intro T c α S hT3 hL₀ hc0 hc hLc hLd hα hS hsep
  have hL1 : 1 ≤ Real.log T := (le_max_left _ _).trans hL₀
  have hL₁ : L₁ ≤ Real.log T := (le_max_right _ _).trans hL₀
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  set L := Real.log T with hLdef
  have hδ1 : 1 ≤ c * L := by
    rw [div_le_iff₀ hc0] at hLc
    linarith
  have hδ0 : 0 < c * L := by linarith
  set r := 1 / (10 * (c * L)) with hrdef
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hrdef, div_le_one (by positivity)]
    linarith
  have h13 : 0 < 1 - 3 * c := by linarith
  set lam := 1 / 4 * Iv * Real.exp ((1 - 3 * c) * α) with hlamdef
  have hlam : 0 < lam := by positivity
  set D : Set ℝ := {t | t ∈ Ioc T (2 * T) ∧
    lam ≤ ‖zeroField v (c * L) ((1 - 2 * c) * L) t‖} with hD
  have hsubset : ∀ ρ ∈ S, Ioo (ρ.im - r) (ρ.im + r) ⊆ D := by
    intro ρ hρ t ht
    obtain ⟨hdepth, hlow, hhigh, hdom⟩ := hS ρ hρ
    have habs : |t - ρ.im| ≤ r := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    have hαL : 0 ≤ α / L := by positivity
    have hb : 1 / 2 ≤ ρ.re := by linarith
    have hamp := norm_paperFT_camera_ge hv hsupp hv0 hδ0 ((1 - 2 * c) * L) hb habs
    have hd := hdom t habs
    have hexp : (1 - 3 * c) * α ≤ (ρ.re - 1 / 2) * ((1 - 2 * c) * L - c * L) := by
      have h1 : α / L ≤ ρ.re - 1 / 2 := by linarith
      have h2 : (1 - 2 * c) * L - c * L = (1 - 3 * c) * L := by ring
      have h3 : 0 ≤ (1 - 3 * c) * L := by positivity
      have h4 := mul_le_mul_of_nonneg_right h1 h3
      have h5 : α / L * ((1 - 3 * c) * L) = (1 - 3 * c) * α := by
        field_simp
      rw [h2]
      linarith
    have hexp' := Real.exp_le_exp.2 hexp
    have hIv : 0 ≤ 1 / 2 * Iv := by positivity
    have h6 := mul_le_mul_of_nonneg_left hexp' hIv
    rw [hlamdef]
    nlinarith
  have hsep' : ∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 2 * r ≤ |ρ.im - ρ'.im| := by
    intro ρ hρ ρ' hρ' hne
    have e : 2 * r = 1 / (5 * (c * L)) := by
      rw [hrdef]
      field_simp
      norm_num
    rw [e]
    exact hsep ρ hρ ρ' hρ' hne
  have hunion := volume_biUnion_windows_eq S (fun ρ : ℂ => ρ.im) hsep'
  have hyδ : c * L < (1 - 2 * c) * L := mul_lt_mul_of_pos_right (by linarith) hL0
  have hyL : (1 - 2 * c) * L + c * L ≤ (1 - c) * L := by nlinarith
  have hle : volume (⋃ ρ ∈ S, Ioo (ρ.im - r) (ρ.im + r)) ≤
      ENNReal.ofReal (C₀ / c ^ 2 * T / lam ^ 2) :=
    (measure_mono (Set.iUnion₂_subset hsubset)).trans
      (hvol T c ((1 - 2 * c) * L) lam hT3 hL₁ hc0 hc hLc hLd hyδ hyL hlam)
  rw [hunion] at hle
  have hreal : (S.card : ℝ) * (2 * r) ≤ C₀ / c ^ 2 * T / lam ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
  have hlamsq : lam ^ 2 = Iv ^ 2 / 16 * Real.exp (2 * (1 - 3 * c) * α) := by
    rw [hlamdef, mul_pow, mul_pow, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  have he : Real.exp (-(2 * (1 - 3 * c) * α)) = (Real.exp (2 * (1 - 3 * c) * α))⁻¹ :=
    Real.exp_neg _
  have h2r : (2 * r)⁻¹ = 5 * (c * L) := by
    rw [hrdef]
    field_simp
    norm_num
  have h2r0 : 0 < 2 * r := by positivity
  calc (S.card : ℝ) = (S.card : ℝ) * (2 * r) * (2 * r)⁻¹ := by field_simp
    _ ≤ C₀ / c ^ 2 * T / lam ^ 2 * (2 * r)⁻¹ :=
        mul_le_mul_of_nonneg_right hreal (by positivity)
    _ = 80 * C₀ / Iv ^ 2 / c * T * L * Real.exp (-(2 * (1 - 3 * c) * α)) := by
        rw [hlamsq, h2r, he]
        field_simp
        ring

/-- **The prime camera bounds separated dominant zeros.** At fixed `c`, the dominant zeros of depth `≥ α/L` in
`[T+1, 2T−1]`, separated by `1/(5δ)`, number `≪ T L e^{−2(1−3c)α}`. -/
theorem exists_card_dominant_zeros_le (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α : ℝ, 0 ≤ α → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, 1 / 2 + α / Real.log T ≤ ρ.re ∧ T + 1 ≤ ρ.im ∧ ρ.im ≤ 2 * T - 1 ∧
        DominatesWindow v (c * Real.log T) ((1 - 2 * c) * Real.log T) ρ) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (c * Real.log T)) ≤ |ρ.im - ρ'.im|) →
      (S.card : ℝ) ≤ C * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) := by
  obtain ⟨C₁, L₀, hC₁, h⟩ := exists_card_dominant_zeros_le_uniform hv hsupp hv0 hI
  refine ⟨C₁ / c, by positivity, ?_⟩
  have hL : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop 3, hL.eventually_ge_atTop L₀,
    hL.eventually_ge_atTop (1 / c), hL.eventually_ge_atTop (64 / c ^ 2)]
    with T hT3 hL₀ hLc hLd α hα S hS hsep
  exact h T c α S hT3 hL₀ hc0 hc hLc hLd hα hS hsep

/-- **The rate is exactly two.** With the camera tuned to the depth, `δ = L/(4+α)`, the separated dominant
zeros of depth `≥ α/L` number `≪ T L (4+α) e^{−2α}`, uniformly for `(4+α)² ≤ L/64`. The width `L/(4+α)` is the
uncertainty scale of the depth: the weight `e^{bu}` concentrates in the last `L/α` of the range of `u`. -/
theorem exists_card_dominant_zeros_le_rate_two (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ (T α : ℝ) (S : Finset ℂ), 3 ≤ T → L₀ ≤ Real.log T → 0 ≤ α →
      64 * (4 + α) ^ 2 ≤ Real.log T →
      (∀ ρ ∈ S, 1 / 2 + α / Real.log T ≤ ρ.re ∧ T + 1 ≤ ρ.im ∧ ρ.im ≤ 2 * T - 1 ∧
        DominatesWindow v (1 / (4 + α) * Real.log T)
          ((1 - 2 * (1 / (4 + α))) * Real.log T) ρ) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (1 / (4 + α) * Real.log T)) ≤ |ρ.im - ρ'.im|) →
      (S.card : ℝ) ≤ C * T * Real.log T * (4 + α) * Real.exp (-(2 * α)) := by
  obtain ⟨C₁, L₀, hC₁, h⟩ := exists_card_dominant_zeros_le_uniform hv hsupp hv0 hI
  refine ⟨C₁ * Real.exp 6, L₀, by positivity, ?_⟩
  intro T α S hT3 hL₀ hα hLα hS hsep
  have h4 : 0 < 4 + α := by linarith
  have hc0 : 0 < 1 / (4 + α) := by positivity
  have hc : 1 / (4 + α) < 1 / 3 := one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  have h64 : 4 + α ≤ (4 + α) ^ 2 := by nlinarith
  have hLc : 1 / (1 / (4 + α)) ≤ Real.log T := by
    rw [one_div_one_div]
    nlinarith
  have hLd : 64 / (1 / (4 + α)) ^ 2 ≤ Real.log T := by
    have e : 64 / (1 / (4 + α)) ^ 2 = 64 * (4 + α) ^ 2 := by
      field_simp
    rw [e]
    exact hLα
  have hmain := h T (1 / (4 + α)) α S hT3 hL₀ hc0 hc hLc hLd hα hS hsep
  have hexp : -(2 * (1 - 3 * (1 / (4 + α))) * α) ≤ 6 - 2 * α := by
    have h5 : α / (4 + α) ≤ 1 := by
      rw [div_le_one h4]
      linarith
    have e : 2 * (1 - 3 * (1 / (4 + α))) * α = 2 * α - 6 * (α / (4 + α)) := by
      field_simp
      ring
    rw [e]
    linarith
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := by
    have : (0 : ℝ) < 64 * (4 + α) ^ 2 := by positivity
    linarith
  calc (S.card : ℝ)
      ≤ C₁ / (1 / (4 + α)) * T * Real.log T * Real.exp (-(2 * (1 - 3 * (1 / (4 + α))) * α)) := hmain
    _ ≤ C₁ / (1 / (4 + α)) * T * Real.log T * Real.exp (6 - 2 * α) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) (by positivity)
    _ = C₁ * Real.exp 6 * T * Real.log T * (4 + α) * Real.exp (-(2 * α)) := by
        rw [show 6 - 2 * α = 6 + -(2 * α) by ring, Real.exp_add]
        field_simp

/-- **The threshold for dominant zeros.** At `c = ε/(3(1+2ε))` the separated dominant zeros of depth
`≥ (½+ε) log log T / log T` number `≪ T (log T)^{−ε}`: their unit windows are sparse from depth
`(½+ε) log log T` in the scale `1/log T`, against `(25/22)(1+ε)` for all zeros. -/
theorem exists_card_dominant_zeros_le_threshold (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ S : Finset ℂ,
      (∀ ρ ∈ S, 1 / 2 + (1 / 2 + ε) * Real.log (Real.log T) / Real.log T ≤ ρ.re ∧
        T + 1 ≤ ρ.im ∧ ρ.im ≤ 2 * T - 1 ∧
        DominatesWindow v (ε / (3 * (1 + 2 * ε)) * Real.log T)
          ((1 - 2 * (ε / (3 * (1 + 2 * ε)))) * Real.log T) ρ) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' →
        1 / (5 * (ε / (3 * (1 + 2 * ε)) * Real.log T)) ≤ |ρ.im - ρ'.im|) →
      (S.card : ℝ) ≤ C * T * (Real.log T) ^ (-ε) := by
  have hden : 0 < 3 * (1 + 2 * ε) := by positivity
  set c := ε / (3 * (1 + 2 * ε)) with hcdef
  have hc0 : 0 < c := by positivity
  have hc : c < 1 / 3 := by
    rw [hcdef, div_lt_iff₀ hden]
    linarith
  obtain ⟨C, hC0, hC⟩ := exists_card_dominant_zeros_le hv hsupp hv0 hI hc0 hc
  refine ⟨C, hC0, ?_⟩
  have hLL : Tendsto (fun T : ℝ => Real.log (Real.log T)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hC, eventually_ge_atTop 1, hLL.eventually_ge_atTop 0,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hT hT1 hLL0 hL1 S hS hsep
  have hL0 : 0 < Real.log T := by linarith
  have hα : 0 ≤ (1 / 2 + ε) * Real.log (Real.log T) := by positivity
  have h := hT _ hα S hS hsep
  refine h.trans (le_of_eq ?_)
  have hkey : 2 * (1 - 3 * c) * ((1 / 2 + ε) * Real.log (Real.log T)) =
      (1 + ε) * Real.log (Real.log T) := by
    have e : 3 * c * (1 + 2 * ε) = ε := by
      rw [hcdef]
      field_simp
    have e2 : 2 * (1 - 3 * c) * (1 / 2 + ε) = 1 + ε := by
      nlinarith
    calc _ = (2 * (1 - 3 * c) * (1 / 2 + ε)) * Real.log (Real.log T) := by ring
      _ = _ := by rw [e2]
  have hexp : Real.exp (Real.log (Real.log T)) = Real.log T := Real.exp_log hL0
  rw [hkey, Real.rpow_def_of_pos hL0]
  calc C * T * Real.log T * Real.exp (-((1 + ε) * Real.log (Real.log T)))
      = C * T * (Real.exp (Real.log (Real.log T)) *
          Real.exp (-((1 + ε) * Real.log (Real.log T)))) := by
        rw [hexp]
        ring
    _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring

/-! ### Isolation implies dominance -/

/-- The signed weight `e^{b'y + |b'|δ}/(1 + δ²(γ' − t)²)` of a companion `ρ'`. A zero left of the line has
exponent `≤ 0`, so a reflected partner never competes with a deep zero. -/
def companionWeight (δ y t : ℝ) (ρ' : ℂ) : ℝ :=
  Real.exp ((ρ'.re - 1 / 2) * y + |ρ'.re - 1 / 2| * δ) / (1 + δ ^ 2 * (ρ'.im - t) ^ 2)

/-- `ρ` is isolated at `(δ, y)`: on its window the companions' weighted mass stays below a quarter of its
amplitude. This is a statement about the zeros alone. -/
def IsolatedAt (v : ℝ → ℝ) (δ y : ℝ) (ρ : zetaZeroConfig.carrier) : Prop :=
  ∀ t : ℝ, |t - (ρ : ℂ).im| ≤ 1 / (10 * δ) → ∀ F : Finset zetaZeroConfig.carrier, ρ ∉ F →
    profileMass v * ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) * companionWeight δ y t ρ' ≤
      1 / 4 * (∫ u, v u) * Real.exp (((ρ : ℂ).re - 1 / 2) * (y - δ))

theorem norm_paperFT_companion_le (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (y t : ℝ) (ρ' : ℂ) :
    ‖paperFT (cameraTest v δ y) (gammaOf ρ' - t)‖ ≤ profileMass v * companionWeight δ y t ρ' := by
  have h := norm_paperFT_camera_le hv hsupp hδ y (gammaOf ρ' - t)
  have him := gammaOf_sub_im ρ' t
  have hre := gammaOf_sub_re ρ' t
  rw [him, abs_neg] at h
  have hE : -(-(ρ'.re - 1 / 2) * y) = (ρ'.re - 1 / 2) * y := by ring
  rw [hE] at h
  have hz : (ρ'.im - t) ^ 2 ≤ ‖gammaOf ρ' - t‖ ^ 2 := by
    have h1 := Complex.abs_re_le_norm (gammaOf ρ' - t)
    rw [hre] at h1
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hden : 0 < 1 + δ ^ 2 * (ρ'.im - t) ^ 2 := by positivity
  have hmono : 1 + δ ^ 2 * (ρ'.im - t) ^ 2 ≤ 1 + δ ^ 2 * ‖gammaOf ρ' - t‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hz (sq_nonneg δ)
    linarith
  unfold companionWeight
  rw [mul_div_assoc', le_div_iff₀ hden, mul_comm (profileMass v)]
  exact (mul_le_mul_of_nonneg_left hmono (norm_nonneg _)).trans h

/-- **Isolation implies dominance.** A deep zero whose companions have small weighted mass dominates its
window, by splitting its term off the absolutely convergent zero field. -/
theorem dominatesWindow_of_isolated (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) {δ y : ℝ} (hδ : 0 < δ) (hyδ : δ < y) {ρ : zetaZeroConfig.carrier}
    (hb : 1 / 2 ≤ (ρ : ℂ).re) (hiso : IsolatedAt v δ y ρ) :
    DominatesWindow v δ y ρ := by
  classical
  intro t ht
  obtain ⟨hs, -⟩ := camera_explicit_formula hv hsupp hδ hyδ t
  set f : zetaZeroConfig.carrier → ℂ := fun ρ' => (zetaZeroConfig.mult ρ' : ℂ) *
    paperFT (cameraTest v δ y) (gammaOf ρ' - t) with hf
  set g : zetaZeroConfig.carrier → ℂ := fun ρ' => if ρ' = ρ then 0 else f ρ' with hg
  have hgn : Summable fun ρ' => ‖g ρ'‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ' => ?_) hs.norm
    by_cases h : ρ' = ρ
    · have h0 : g ρ' = 0 := if_pos h
      rw [h0, norm_zero]
      exact norm_nonneg _
    · have h0 : g ρ' = f ρ' := if_neg h
      rw [h0]
  have hsplit : zeroField v δ y t = f ρ + ∑' ρ', g ρ' := hs.tsum_eq_add_tsum_ite ρ
  have hother : ‖∑' ρ', g ρ'‖ ≤ 1 / 4 * (∫ u, v u) * Real.exp (((ρ : ℂ).re - 1 / 2) * (y - δ)) := by
    refine (norm_tsum_le_tsum_norm hgn).trans ?_
    refine Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) fun F => ?_
    have hF := hiso t ht (F.erase ρ) (Finset.notMem_erase ρ F)
    refine le_trans ?_ hF
    have hg0 : ‖g ρ‖ = 0 := by
      have h0 : g ρ = 0 := if_pos rfl
      rw [h0, norm_zero]
    rw [← Finset.sum_erase F hg0, Finset.mul_sum]
    refine Finset.sum_le_sum fun ρ' hρ' => ?_
    have hne : ρ' ≠ ρ := (Finset.mem_erase.mp hρ').1
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ' := Nat.cast_nonneg _
    have hk := norm_paperFT_companion_le hv hsupp hδ y t ρ'
    have hgρ : g ρ' = f ρ' := if_neg hne
    rw [hgρ]
    simp only [hf]
    rw [norm_mul, Complex.norm_natCast]
    calc (zetaZeroConfig.mult ρ' : ℝ) * ‖paperFT (cameraTest v δ y) (gammaOf ρ' - t)‖
        ≤ (zetaZeroConfig.mult ρ' : ℝ) * (profileMass v * companionWeight δ y t ρ') :=
          mul_le_mul_of_nonneg_left hk hm
      _ = _ := by ring
  have hamp := norm_paperFT_camera_ge hv hsupp hv0 hδ y hb ht
  have hm1 : (1 : ℝ) ≤ zetaZeroConfig.mult ρ := by
    exact_mod_cast zetaZeroConfig.one_le_mult ρ ρ.2
  have hterm : ‖paperFT (cameraTest v δ y) (gammaOf ρ - t)‖ ≤ ‖f ρ‖ := by
    simp only [hf]
    rw [norm_mul, Complex.norm_natCast]
    exact le_mul_of_one_le_left (norm_nonneg _) hm1
  have htri : ‖f ρ‖ ≤ ‖zeroField v δ y t‖ + ‖∑' ρ', g ρ'‖ := by
    have e : f ρ = zeroField v δ y t - ∑' ρ', g ρ' := by
      rw [hsplit]
      ring
    rw [e]
    exact norm_sub_le _ _
  linarith

/-- **The prime camera bounds separated isolated zeros.** The same count holds for zeros isolated in the
sense of `IsolatedAt`, a condition on the zeros alone. -/
theorem exists_card_isolated_zeros_le (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α : ℝ, 0 ≤ α → ∀ S : Finset zetaZeroConfig.carrier,
      (∀ ρ ∈ S, 1 / 2 + α / Real.log T ≤ (ρ : ℂ).re ∧ T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1 ∧
        IsolatedAt v (c * Real.log T) ((1 - 2 * c) * Real.log T) ρ) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (c * Real.log T)) ≤ |(ρ : ℂ).im - (ρ' : ℂ).im|) →
      (S.card : ℝ) ≤ C * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_card_dominant_zeros_le hv hsupp hv0 hI hc0 hc
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hC, Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT hL0 α hα S hS hsep
  have hδ : 0 < c * Real.log T := by positivity
  have hyδ : c * Real.log T < (1 - 2 * c) * Real.log T :=
    mul_lt_mul_of_pos_right (by linarith) hL0
  have hinj : Function.Injective (Subtype.val : zetaZeroConfig.carrier → ℂ) :=
    Subtype.val_injective
  have h := hT α hα (S.image Subtype.val) ?_ ?_
  · rwa [Finset.card_image_of_injective S hinj] at h
  · intro ρ hρ
    obtain ⟨ρ₀, hρ₀, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨h1, h2, h3, h4⟩ := hS ρ₀ hρ₀
    have hb : 1 / 2 ≤ (ρ₀ : ℂ).re := by
      have : 0 ≤ α / Real.log T := by positivity
      linarith
    exact ⟨h1, h2, h3, dominatesWindow_of_isolated hv hsupp hv0 hδ hyδ hb h4⟩
  · intro ρ hρ ρ' hρ' hne
    obtain ⟨ρ₀, hρ₀, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨ρ₁, hρ₁, rfl⟩ := Finset.mem_image.mp hρ'
    exact hsep ρ₀ hρ₀ ρ₁ hρ₁ fun e => hne (by rw [e])

end GaloisForLFunctions.MultiscaleMollifiedZetaField
