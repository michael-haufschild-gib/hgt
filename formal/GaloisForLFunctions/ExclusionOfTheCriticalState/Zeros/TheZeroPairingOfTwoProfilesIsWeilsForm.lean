import GaloisForLFunctions.ExclusionOfTheCriticalState.Collar.TheCollarWeakEquationIsSoftBeyondStar
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroPairingOfTheStateConvergesAbsolutely
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw
import GaloisForLFunctions.RHTower.RiemannKernelStripPlancherel
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# The zero pairing of two profiles is Weil's form

For a profile `F` of the energy domain whose unit tilt `e^{−u}F` lies in the domain and a profile `G` of
the domain vanishing below some `−T`, the zero pairing converges absolutely and is Weil's bare form:

  `Σ_z L F(z) L G(−z) = W(F, G)`   (`hasSum_bareMixedEnergy_of_unitTilt_of_bounded`),

the sum over the centred zeros with multiplicity. No smoothness of `G` and no equation for `F` is
needed; for smooth compactly supported `G` this is `hasSum_bareMixedEnergy_of_domain`.

Mechanism. Mollify `G` by bumps `φ_n` of mass one supported in `(−1/(n+1), −1/(2(n+1)))`: the profiles
`G_n = φ_n * G` are smooth, compactly supported in `u < 0`, and `(G_n)^(z) = φ̂_n(z) Ĝ(z)` for
`|Im z| ≤ 1`, with `|φ̂_n(z)| ≤ e^{|Im z|}` and `φ̂_n(z) → 1`. By dominated convergence
`D_n = G_n − G` tends to zero in the Gamma energy, in `L²` (Plancherel), and in the logarithmic energy
of its unit tilt, which bounds `Σ_z |L D_n(−z)|²`. Weil's form is continuous in the Gamma energy and the
weighted `L²` norm, and the zero pairing is continuous in `ℓ²` (Cauchy–Schwarz against the
square-summable values `L F(z)`).
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Zeta23
open scoped Convolution ContDiff

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The paper transform at complex points -/

theorem paperFT_sub {f g : ℝ → ℂ} {z : ℂ} (hf : Integrable fun u : ℝ => f u * cexp (I * z * u))
    (hg : Integrable fun u : ℝ => g u * cexp (I * z * u)) :
    paperFT (fun u => f u - g u) z = paperFT f z - paperFT g z := by
  unfold paperFT
  rw [← integral_sub hf hg]
  exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring)

/-- A profile of the domain against `e^{izu}` is integrable for `Im z ≤ 1`... for every `Im z < 4`. -/
theorem integrable_cx_mul_cexp_of_domain {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) {z : ℂ}
    (hz : z.im < 4) : Integrable fun u : ℝ => cx G u * cexp (I * z * u) := by
  refine (integrable_abs_mul_exp_of_domain hG (c := -z.im) (by linarith)).mono'
    ((Complex.measurable_ofReal.comp hG.meas).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul, Complex.norm_exp, cx, Complex.norm_real, Real.norm_eq_abs]
  apply le_of_eq
  congr 2
  simp [Complex.mul_re]

/-- The unit tilt is a shift of the transform by `i`. -/
theorem paperFT_cx_exp_mul (D : ℝ → ℝ) (t : ℝ) :
    paperFT (cx fun u => Real.exp (-(1 * u)) * D u) (t : ℂ) = paperFT (cx D) ((t : ℂ) + I) := by
  unfold paperFT
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [cx]
  push_cast
  rw [mul_comm (cexp _), mul_assoc, ← Complex.exp_add]
  congr 2
  ring_nf
  simp [Complex.I_sq]
  ring

/-! ### Mollifiers supported left of the wall -/

/-- The bump of radius `1/(4(n+1))` centred at `−3/(4(n+1))`. -/
def wallBump (n : ℕ) : ContDiffBump (-(3 / (4 * ((n : ℝ) + 1)))) where
  rIn := 1 / (8 * ((n : ℝ) + 1))
  rOut := 1 / (4 * ((n : ℝ) + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- The normalized mollifier `φ_n`: smooth, nonnegative, of mass one, supported in
`(−1/(n+1), −1/(2(n+1)))`. -/
def wallMollifier (n : ℕ) : ℝ → ℝ := (wallBump n).normed volume

theorem wallMollifier_nonneg (n : ℕ) (s : ℝ) : 0 ≤ wallMollifier n s :=
  (wallBump n).nonneg_normed s

theorem integral_wallMollifier (n : ℕ) : ∫ s, wallMollifier n s = 1 :=
  (wallBump n).integral_normed

theorem contDiff_wallMollifier (n : ℕ) : ContDiff ℝ ∞ (wallMollifier n) :=
  (wallBump n).contDiff_normed

theorem hasCompactSupport_wallMollifier (n : ℕ) : HasCompactSupport (wallMollifier n) :=
  (wallBump n).hasCompactSupport_normed

theorem support_wallMollifier (n : ℕ) :
    Function.support (wallMollifier n) ⊆ Ioo (-(1 / ((n : ℝ) + 1))) (-(1 / (2 * ((n : ℝ) + 1)))) := by
  intro s hs
  have h := (wallBump n).support_normed_eq (μ := volume) ▸ hs
  rw [Real.ball_eq_Ioo] at h
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  obtain ⟨h1, h2⟩ := h
  simp only [wallBump] at h1 h2
  constructor
  · have e : -(3 / (4 * ((n : ℝ) + 1))) - 1 / (4 * ((n : ℝ) + 1)) = -(1 / ((n : ℝ) + 1)) := by
      field_simp; ring
    linarith
  · have e : -(3 / (4 * ((n : ℝ) + 1))) + 1 / (4 * ((n : ℝ) + 1)) = -(1 / (2 * ((n : ℝ) + 1))) := by
      field_simp; ring
    linarith

theorem abs_lt_of_mem_support_wallMollifier {n : ℕ} {s : ℝ} (hs : wallMollifier n s ≠ 0) :
    |s| < 1 / ((n : ℝ) + 1) := by
  obtain ⟨h1, h2⟩ := support_wallMollifier n hs
  have hn : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  rw [abs_lt]; constructor <;> linarith

theorem integrable_wallMollifier (n : ℕ) : Integrable (wallMollifier n) :=
  (contDiff_wallMollifier n).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_wallMollifier n)

theorem integrable_cx_wallMollifier_mul_cexp (n : ℕ) (z : ℂ) :
    Integrable fun u : ℝ => cx (wallMollifier n) u * cexp (I * z * u) :=
  ((Complex.continuous_ofReal.comp (contDiff_wallMollifier n).continuous).mul
    (by fun_prop)).integrable_of_hasCompactSupport
      ((hasCompactSupport_wallMollifier n).comp_left Complex.ofReal_zero |>.mul_right)

/-- `|φ̂_n(z)| ≤ e^{|Im z|/(n+1)}`. -/
theorem norm_paperFT_wallMollifier_le (n : ℕ) (z : ℂ) :
    ‖paperFT (cx (wallMollifier n)) z‖ ≤ Real.exp (|z.im| / ((n : ℝ) + 1)) := by
  unfold paperFT
  calc ‖∫ u, cx (wallMollifier n) u * cexp (I * z * u)‖
      ≤ ∫ u, wallMollifier n u * Real.exp (|z.im| / ((n : ℝ) + 1)) :=
        norm_integral_le_of_norm_le ((integrable_wallMollifier n).mul_const _)
          (Eventually.of_forall fun u => ?_)
    _ = Real.exp (|z.im| / ((n : ℝ) + 1)) := by
        rw [integral_mul_const, integral_wallMollifier, one_mul]
  rw [norm_mul, cx, Complex.norm_real, Real.norm_of_nonneg (wallMollifier_nonneg n u),
    Complex.norm_exp]
  by_cases hu : wallMollifier n u = 0
  · rw [hu, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (wallMollifier_nonneg n u)
    have hs := abs_lt_of_mem_support_wallMollifier hu
    have e : (I * z * (u : ℂ)).re = -(z.im * u) := by simp [Complex.mul_re]
    rw [e]
    have h1 : |z.im * u| ≤ |z.im| * (1 / ((n : ℝ) + 1)) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hs.le (abs_nonneg _)
    have h2 := neg_abs_le (z.im * u)
    rw [div_eq_mul_one_div]
    linarith [neg_le_abs (z.im * u)]

/-- `φ̂_n(z) → 1`. -/
theorem tendsto_paperFT_wallMollifier (z : ℂ) :
    Tendsto (fun n : ℕ => paperFT (cx (wallMollifier n)) z) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN0⟩ := exists_nat_gt (2 * (‖z‖ + 1) / ε + ‖z‖)
  have hN : 2 * (‖z‖ + 1) / ε < N := by linarith [norm_nonneg z]
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hzn : ‖z‖ < (n : ℝ) + 1 := by
    have : 0 ≤ 2 * (‖z‖ + 1) / ε := by positivity
    linarith
  have hsmall : 2 * (‖z‖ + 1) / ((n : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hn1]
    rw [div_lt_iff₀ hε] at hN
    nlinarith
  have hone : (1 : ℂ) = ∫ u, cx (wallMollifier n) u := by
    rw [show (fun u => cx (wallMollifier n) u) = fun u => ((wallMollifier n u : ℝ) : ℂ) from rfl,
      integral_complex_ofReal, integral_wallMollifier, Complex.ofReal_one]
  rw [dist_eq_norm, hone]
  unfold paperFT
  have hint : Integrable fun u => cx (wallMollifier n) u := (integrable_wallMollifier n).ofReal
  rw [← integral_sub (integrable_cx_wallMollifier_mul_cexp n z) hint]
  calc ‖∫ u, (cx (wallMollifier n) u * cexp (I * z * u) - cx (wallMollifier n) u)‖
      ≤ ∫ u, wallMollifier n u * (2 * ‖z‖ / ((n : ℝ) + 1)) :=
        norm_integral_le_of_norm_le ((integrable_wallMollifier n).mul_const _)
          (Eventually.of_forall fun u => ?_)
    _ = 2 * ‖z‖ / ((n : ℝ) + 1) := by rw [integral_mul_const, integral_wallMollifier, one_mul]
    _ < ε := lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith) hn1.le) hsmall
  rw [show cx (wallMollifier n) u * cexp (I * z * u) - cx (wallMollifier n) u =
    cx (wallMollifier n) u * (cexp (I * z * u) - 1) by ring, norm_mul, cx, Complex.norm_real,
    Real.norm_of_nonneg (wallMollifier_nonneg n u)]
  by_cases hu : wallMollifier n u = 0
  · rw [hu, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left ?_ (wallMollifier_nonneg n u)
    have hs := abs_lt_of_mem_support_wallMollifier hu
    have hx : ‖I * z * (u : ℂ)‖ ≤ ‖z‖ / ((n : ℝ) + 1) := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hs.le (norm_nonneg _)
    have hx1 : ‖I * z * (u : ℂ)‖ ≤ 1 := by
      refine hx.trans ?_
      rw [div_le_one hn1]
      exact hzn.le
    calc ‖cexp (I * z * u) - 1‖ ≤ 2 * ‖I * z * (u : ℂ)‖ := Complex.norm_exp_sub_one_le hx1
      _ ≤ 2 * (‖z‖ / ((n : ℝ) + 1)) := by linarith
      _ = 2 * ‖z‖ / ((n : ℝ) + 1) := by ring

/-! ### The mollified profile -/

/-- The mollification `G_n = φ_n * G`. -/
def wallMollify (n : ℕ) (G : ℝ → ℝ) : ℝ → ℝ :=
  wallMollifier n ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] G

theorem contDiff_wallMollify (n : ℕ) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    ContDiff ℝ ∞ (wallMollify n G) :=
  (hasCompactSupport_wallMollifier n).contDiff_convolution_left _ (contDiff_wallMollifier n)
    hG.integrable.locallyIntegrable

theorem wallMollify_eq_zero_of_nonneg (n : ℕ) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    {u : ℝ} (hu : 0 ≤ u) : wallMollify n G u = 0 := by
  by_contra h
  obtain ⟨s, hs, v, hv, rfl⟩ := support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ) h
  have h1 := (support_wallMollifier n hs).2
  have h2 : v < 0 := by
    by_contra hv0
    exact hv (hG.support v (not_lt.mp hv0))
  have : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  simp only at hu
  linarith

theorem wallMollify_eq_zero_of_lt (n : ℕ) {G : ℝ → ℝ} {T : ℝ} (hT : ∀ u, u < -T → G u = 0)
    {u : ℝ} (hu : u < -T - 1) : wallMollify n G u = 0 := by
  by_contra h
  obtain ⟨s, hs, v, hv, rfl⟩ := support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ) h
  have h1 := (support_wallMollifier n hs).1
  have h2 : -T ≤ v := by
    by_contra hv0
    exact hv (hT v (lt_of_not_ge hv0))
  have : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
  simp only at hu
  linarith

theorem hasCompactSupport_wallMollify (n : ℕ) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    {T : ℝ} (hT : ∀ u, u < -T → G u = 0) : HasCompactSupport (wallMollify n G) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -T - 1) (b := 0)) fun u hu => ?_
  rcases lt_or_ge u (-T - 1) with h | h
  · exact wallMollify_eq_zero_of_lt n hT h
  · exact wallMollify_eq_zero_of_nonneg n hG (not_lt.mp fun h' => hu ⟨h, h'.le⟩)

theorem criticalHalfLineEnergyDomain_wallMollify (n : ℕ) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {T : ℝ} (hT : ∀ u, u < -T → G u = 0) :
    CriticalHalfLineEnergyDomain (wallMollify n G) :=
  criticalHalfLineEnergyDomain_of_compact_negative
    ((contDiff_wallMollify n hG).of_le (WithTop.coe_le_coe.mpr le_top))
    (hasCompactSupport_wallMollify n hG hT) fun u hu => wallMollify_eq_zero_of_nonneg n hG hu

theorem cx_wallMollify (n : ℕ) (G : ℝ → ℝ) :
    cx (wallMollify n G) =
      cx (wallMollifier n) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] cx G := by
  funext u
  simp only [cx, wallMollify, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal]
  push_cast
  rfl

/-- **The transform of the mollified profile** is `φ̂_n(z) Ĝ(z)` for `Im z < 4`. -/
theorem paperFT_wallMollify (n : ℕ) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) {z : ℂ}
    (hz : z.im < 4) :
    paperFT (cx (wallMollify n G)) z = paperFT (cx (wallMollifier n)) z * paperFT (cx G) z := by
  rw [cx_wallMollify]
  exact paperFT_convolution (integrable_cx_wallMollifier_mul_cexp n z)
    (integrable_cx_mul_cexp_of_domain hG hz)

/-! ### The difference `D_n = G_n − G` -/

/-- `D_n = G_n − G`. -/
def wallDefect (n : ℕ) (G : ℝ → ℝ) : ℝ → ℝ := fun u => wallMollify n G u - G u

theorem criticalHalfLineEnergyDomain_wallDefect (n : ℕ) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {T : ℝ} (hT : ∀ u, u < -T → G u = 0) :
    CriticalHalfLineEnergyDomain (wallDefect n G) := by
  show CriticalHalfLineEnergyDomain fun u => wallMollify n G u - G u
  simpa only [neg_one_mul, ← sub_eq_add_neg] using
    (criticalHalfLineEnergyDomain_wallMollify n hG hT).add_const_mul hG (-1)

theorem wallDefect_eq_zero_of_lt (n : ℕ) {G : ℝ → ℝ} {T : ℝ} (hT0 : 0 ≤ T)
    (hT : ∀ u, u < -T → G u = 0) {u : ℝ} (hu : u < -T - 1) : wallDefect n G u = 0 := by
  simp only [wallDefect, wallMollify_eq_zero_of_lt n hT hu, hT u (by linarith), sub_zero]

/-- The transform of the defect: `D̂_n(z) = (φ̂_n(z) − 1) Ĝ(z)` for `Im z < 4`. -/
theorem paperFT_wallDefect (n : ℕ) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) {T : ℝ}
    (hT : ∀ u, u < -T → G u = 0) {z : ℂ} (hz : z.im < 4) :
    paperFT (cx (wallDefect n G)) z = (paperFT (cx (wallMollifier n)) z - 1) * paperFT (cx G) z := by
  have e : cx (wallDefect n G) = fun u => cx (wallMollify n G) u - cx G u := by
    funext u; simp only [cx, wallDefect]; push_cast; rfl
  rw [e, paperFT_sub (integrable_cx_mul_cexp_of_domain
      (criticalHalfLineEnergyDomain_wallMollify n hG hT) hz) (integrable_cx_mul_cexp_of_domain hG hz),
    paperFT_wallMollify n hG hz]
  ring

/-! ### The defect vanishes in the three energies -/

theorem norm_paperFT_wallMollifier_sub_one_le (n : ℕ) {z : ℂ} (hz : |z.im| ≤ 1) :
    ‖paperFT (cx (wallMollifier n)) z - 1‖ ≤ Real.exp 1 + 1 := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  refine add_le_add ((norm_paperFT_wallMollifier_le n z).trans (Real.exp_le_exp.mpr ?_)) le_rfl
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n, abs_nonneg z.im]

/-- A dominated sequence `‖m_n − 1‖² B` with `m_n → 1` integrates to zero. -/
theorem tendsto_integral_multiplier {B : ℝ → ℝ} (hB : Integrable B) {m : ℕ → ℝ → ℂ}
    (hm : ∀ n, AEStronglyMeasurable (fun r => ‖m n r - 1‖ ^ 2 * B r) volume)
    {K : ℝ} (hK : ∀ n r, ‖m n r - 1‖ ≤ K) (hlim : ∀ r, Tendsto (fun n => m n r) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ r, ‖m n r - 1‖ ^ 2 * B r) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun r => K ^ 2 * ‖B r‖) hm (hB.norm.const_mul _)
    (fun n => Eventually.of_forall fun r => by
      rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hK n r) 2) (norm_nonneg _))
    (Eventually.of_forall fun r => by
      have h1 : Tendsto (fun n => ‖m n r - 1‖) atTop (𝓝 0) := by
        have := ((hlim r).sub_const 1).norm
        rwa [sub_self, norm_zero] at this
      simpa using (h1.pow 2).mul_const (B r))
  simpa using h

/-- **Gamma energy of the defect.** `∫ ‖D̂_n‖² |γ| → 0`. -/
theorem tendsto_gammaEnergy_wallDefect {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) {T : ℝ}
    (hT : ∀ u, u < -T → G u = 0) :
    Tendsto (fun n => ∫ r : ℝ, ‖paperFT (cx (wallDefect n G)) r‖ ^ 2 * |EF.gammaBracket r|)
      atTop (𝓝 0) := by
  have hB : Integrable fun r : ℝ => ‖paperFT (cx G) r‖ ^ 2 * |EF.gammaBracket r| := by
    refine hG.gamma.norm.congr (Eventually.of_forall fun r => ?_)
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖paperFT (cx G) (r : ℂ)‖)]
  have h := tendsto_integral_multiplier hB (m := fun n (r : ℝ) => paperFT (cx (wallMollifier n)) r)
    (fun n => (((((continuous_paperFT_cx (integrable_wallMollifier n)).sub continuous_const).norm.pow
      2).mul (((continuous_paperFT_cx hG.integrable).norm.pow 2).mul
        WeilHerglotz.continuous_gammaBracket.abs))).aestronglyMeasurable)
    (K := Real.exp 1 + 1) (fun n r => norm_paperFT_wallMollifier_sub_one_le n (by simp))
    (fun r => tendsto_paperFT_wallMollifier r)
  refine h.congr fun n => integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [paperFT_wallDefect n hG hT (by simp), norm_mul, mul_pow]
  ring

/-- **`L²` mass of the defect.** `∫ D_n² → 0` (Plancherel). -/
theorem tendsto_integral_sq_wallDefect {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) {T : ℝ}
    (hT : ∀ u, u < -T → G u = 0) :
    Tendsto (fun n => ∫ u, wallDefect n G u ^ 2) atTop (𝓝 0) := by
  have h := tendsto_integral_multiplier (B := fun r : ℝ => ‖paperFT (cx G) r‖ ^ 2)
    (integrable_norm_sq_paperFT_cx hG.integrable hG.sq)
    (m := fun n (r : ℝ) => paperFT (cx (wallMollifier n)) r)
    (fun n => ((((continuous_paperFT_cx (integrable_wallMollifier n)).sub continuous_const).norm.pow
      2).mul ((continuous_paperFT_cx hG.integrable).norm.pow 2)).aestronglyMeasurable)
    (K := Real.exp 1 + 1) (fun n r => norm_paperFT_wallMollifier_sub_one_le n (by simp))
    (fun r => tendsto_paperFT_wallMollifier r)
  have hP : ∀ n, ∫ u, wallDefect n G u ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ r : ℝ, ‖paperFT (cx (wallMollifier n)) r - 1‖ ^ 2 *
        ‖paperFT (cx G) r‖ ^ 2 := by
    intro n
    have hD := criticalHalfLineEnergyDomain_wallDefect n hG hT
    have hpl := KernelStrip.integral_norm_sq_paperFT_of_memLp (hD.integrable.ofReal (𝕜 := ℂ))
      (memLp_cx_of_sq hD.integrable hD.sq)
    have hpl' : (∫ r : ℝ, ‖paperFT (cx (wallDefect n G)) r‖ ^ 2) =
        2 * Real.pi * ∫ u : ℝ, ‖((wallDefect n G u : ℝ) : ℂ)‖ ^ 2 := hpl
    have e1 : (∫ r : ℝ, ‖paperFT (cx (wallDefect n G)) r‖ ^ 2) =
        ∫ r : ℝ, ‖paperFT (cx (wallMollifier n)) r - 1‖ ^ 2 * ‖paperFT (cx G) r‖ ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only
      rw [paperFT_wallDefect n hG hT (by simp), norm_mul, mul_pow]
    have e2 : (∫ u : ℝ, ‖((wallDefect n G u : ℝ) : ℂ)‖ ^ 2) = ∫ u, wallDefect n G u ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [e1, e2] at hpl'
    rw [hpl']
    field_simp
  rw [show (0 : ℝ) = (2 * Real.pi)⁻¹ * 0 by ring]
  exact (h.const_mul (2 * Real.pi)⁻¹).congr fun n => (hP n).symm

/-- The tilted mollifier: `(e^{−u} φ_n)^(t) = φ̂_n(t + i)`. -/
theorem tilted_paperFT_wallMollifier (n : ℕ) (t : ℝ) :
    paperFT (cx fun u => Real.exp (-(1 * u)) * wallMollifier n u) (t : ℂ) =
      paperFT (cx (wallMollifier n)) ((t : ℂ) + I) := paperFT_cx_exp_mul _ t

/-- **Logarithmic energy of the tilted defect**, which controls the reflected zero values. -/
theorem tendsto_logEnergy_tilt_wallDefect {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    {T : ℝ} (hT : ∀ u, u < -T → G u = 0) :
    Tendsto (fun n => ∫ t : ℝ, (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
      ‖paperFT (cx fun u => Real.exp (-(1 * u)) * wallDefect n G u) (t : ℂ)‖ ^ 2) atTop (𝓝 0) := by
  have hG1 := criticalHalfLineEnergyDomain_exp_mul_of_bounded hG hT (c := 1) zero_le_one
  have hlog := integrable_log_mul_norm_sq_paperFT hG1
  have hφ1 (n : ℕ) : Integrable fun u => Real.exp (-(1 * u)) * wallMollifier n u :=
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(1 * u))).mul
      (contDiff_wallMollifier n).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_wallMollifier n).mul_left
  have hcG1 := continuous_paperFT_cx hG1.integrable
  have hcont : Continuous fun t : ℝ => xiLineTwoLogDerivConstant + Real.log (|t| + 4) :=
    continuous_const.add ((by fun_prop : Continuous fun t : ℝ => |t| + 4).log fun t => by positivity)
  have h := tendsto_integral_multiplier hlog
    (m := fun n (t : ℝ) => paperFT (cx fun u => Real.exp (-(1 * u)) * wallMollifier n u) (t : ℂ))
    (fun n => ((((continuous_paperFT_cx (hφ1 n)).sub continuous_const).norm.pow 2).mul
      (hcont.mul (hcG1.norm.pow 2))).aestronglyMeasurable)
    (K := Real.exp 1 + 1)
    (fun n t => by rw [tilted_paperFT_wallMollifier]; exact norm_paperFT_wallMollifier_sub_one_le n (by simp))
    (fun t => by
      simp_rw [tilted_paperFT_wallMollifier]
      exact tendsto_paperFT_wallMollifier _)
  refine h.congr fun n => integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [tilted_paperFT_wallMollifier, paperFT_cx_exp_mul (wallDefect n G) t,
    paperFT_wallDefect n hG hT (by simp), ← paperFT_cx_exp_mul G t, norm_mul, mul_pow]
  ring

/-- The reflected zero values of the defect are controlled by its tilted logarithmic energy. -/
theorem tsum_norm_sq_laplace_neg_wallDefect_le (n : ℕ) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {T : ℝ} (hT0 : 0 ≤ T) (hT : ∀ u, u < -T → G u = 0) :
    ∑' q : XiZeroCopy, ‖negativeHalfLineLaplace (cx (wallDefect n G)) (-centredZero q)‖ ^ 2 ≤
      16 / Real.pi * ∫ t : ℝ, (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
        ‖paperFT (cx fun u => Real.exp (-(1 * u)) * wallDefect n G u) (t : ℂ)‖ ^ 2 := by
  have hD1 := criticalHalfLineEnergyDomain_exp_mul_of_bounded
    (criticalHalfLineEnergyDomain_wallDefect n hG hT) (T := T + 1)
    (fun u hu => wallDefect_eq_zero_of_lt n hT0 hT (by linarith)) (c := 1) zero_le_one
  have h := tsum_norm_sq_laplace_zeros_le hD1 (ε := -1) (Or.inr rfl)
    (fun q => -centredZero q + ((1 : ℝ) : ℂ))
    (fun q => by
      have := abs_lt.mp (abs_re_centredZero_lt q)
      rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
      linarith [this.2])
    (fun q => by
      have := abs_lt.mp (abs_re_centredZero_lt q)
      rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
      linarith [this.1])
    (fun q => by
      rw [Complex.add_im, Complex.neg_im, Complex.ofReal_im, add_zero, im_centredZero,
        neg_one_mul])
  refine le_of_eq_of_le (tsum_congr fun q => ?_) h
  rw [laplace_eq_laplace_exp_mul (wallDefect n G) 1 (-centredZero q)]

/-! ### Weil's form is continuous in the energies -/

theorem abs_integral_mul_le_sqrt_massMul {f g : ℝ → ℝ} (hfm : AEStronglyMeasurable f volume)
    (hgm : AEStronglyMeasurable g volume) (hf2 : Integrable fun x => f x ^ 2)
    (hg2 : Integrable fun x => g x ^ 2) :
    |∫ x, f x * g x| ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  rw [← Real.sqrt_mul (integral_nonneg fun x => sq_nonneg _)]
  exact Real.abs_le_sqrt (sq_integral_mul_le hfm hgm hf2 hg2)

theorem abs_gammaFourierPair_le_mul (f g : ℝ → ℝ) (r : ℝ) :
    |gammaFourierPair f g r| ≤ ‖paperFT (cx f) r‖ * ‖paperFT (cx g) r‖ := by
  have h : gammaFourierPair f g r ^ 2 ≤ (‖paperFT (cx f) r‖ * ‖paperFT (cx g) r‖) ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    unfold gammaFourierPair
    nlinarith [sq_nonneg ((paperFT (cx f) r).re * (paperFT (cx g) r).im -
      (paperFT (cx f) r).im * (paperFT (cx g) r).re)]
  have := Real.abs_le_sqrt h
  rwa [Real.sqrt_sq (by positivity)] at this

/-- **The Gamma pairing is bounded by the Gamma energies.** -/
theorem abs_gammaMixedForm_le {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hγf : Integrable fun r : ℝ => ‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r)
    (hγg : Integrable fun r : ℝ => ‖paperFT (cx g) r‖ ^ 2 * EF.gammaBracket r) :
    |gammaMixedForm f g| ≤ (2 * Real.pi)⁻¹ *
      (Real.sqrt (∫ r : ℝ, ‖paperFT (cx f) r‖ ^ 2 * |EF.gammaBracket r|) *
        Real.sqrt (∫ r : ℝ, ‖paperFT (cx g) r‖ ^ 2 * |EF.gammaBracket r|)) := by
  have hsq : ∀ (h : ℝ → ℝ) (r : ℝ), (‖paperFT (cx h) r‖ * Real.sqrt |EF.gammaBracket r|) ^ 2 =
      ‖paperFT (cx h) r‖ ^ 2 * |EF.gammaBracket r| := fun h r => by
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
  have hint : ∀ (h : ℝ → ℝ), Integrable (fun r : ℝ => ‖paperFT (cx h) r‖ ^ 2 * EF.gammaBracket r) →
      Integrable fun r : ℝ => (‖paperFT (cx h) r‖ * Real.sqrt |EF.gammaBracket r|) ^ 2 :=
    fun h hh => hh.norm.congr (Eventually.of_forall fun r => by
      simp only
      rw [hsq, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])
  have ham : AEStronglyMeasurable (fun r : ℝ => ‖paperFT (cx f) r‖ * Real.sqrt |EF.gammaBracket r|)
      volume :=
    ((continuous_paperFT_cx hf).norm.mul
      (Real.continuous_sqrt.comp WeilHerglotz.continuous_gammaBracket.abs)).aestronglyMeasurable
  have hbm : AEStronglyMeasurable (fun r : ℝ => ‖paperFT (cx g) r‖ * Real.sqrt |EF.gammaBracket r|)
      volume :=
    ((continuous_paperFT_cx hg).norm.mul
      (Real.continuous_sqrt.comp WeilHerglotz.continuous_gammaBracket.abs)).aestronglyMeasurable
  have hab := integrable_mul_of_sq_integrable ham hbm (hint f hγf) (hint g hγg)
  have hcs := abs_integral_mul_le_sqrt_massMul ham hbm (hint f hγf) (hint g hγg)
  simp only [hsq] at hcs
  unfold gammaMixedForm
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)), one_div]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (abs_integral_le_integral_abs).trans (le_trans (integral_mono_of_nonneg
    (Eventually.of_forall fun r => abs_nonneg _) hab (Eventually.of_forall fun r => ?_)) ?_)
  · show |gammaFourierPair f g r * EF.gammaBracket r| ≤
      ‖paperFT (cx f) r‖ * Real.sqrt |EF.gammaBracket r| *
        (‖paperFT (cx g) r‖ * Real.sqrt |EF.gammaBracket r|)
    rw [abs_mul, show ‖paperFT (cx f) r‖ * Real.sqrt |EF.gammaBracket r| *
        (‖paperFT (cx g) r‖ * Real.sqrt |EF.gammaBracket r|) =
        ‖paperFT (cx f) r‖ * ‖paperFT (cx g) r‖ *
          (Real.sqrt |EF.gammaBracket r| * Real.sqrt |EF.gammaBracket r|) by ring,
      Real.mul_self_sqrt (abs_nonneg _)]
    exact mul_le_mul_of_nonneg_right (abs_gammaFourierPair_le_mul f g r) (abs_nonneg _)
  · exact (le_abs_self _).trans hcs

/-- **Weil's bare form is continuous in the energies.** -/
theorem abs_bareMixedEnergy_le {F D : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hD : CriticalHalfLineEnergyDomain D) :
    |bareMixedEnergy F D| ≤
      (2 * Real.pi)⁻¹ * (Real.sqrt (∫ r : ℝ, ‖paperFT (cx F) r‖ ^ 2 * |EF.gammaBracket r|) *
          Real.sqrt (∫ r : ℝ, ‖paperFT (cx D) r‖ ^ 2 * |EF.gammaBracket r|)) +
        2 * vonMangoldtThreeHalvesMass *
          (Real.sqrt (exponentialSourceMass F) * Real.sqrt (exponentialSourceMass D)) +
        2 * (|coshHalfMoment F| + |sinhHalfMoment F|) *
          (Real.sqrt (exponentialSourceMass D) * Real.sqrt (∫ u, Real.exp (-|u|))) := by
  have hg := abs_gammaMixedForm_le hF.integrable hD.integrable hF.gamma hD.gamma
  have hp1 := abs_primeMixedForm_le hF.weighted hD.weighted
  have hp2 := abs_primeMixedForm_le hD.weighted hF.weighted
  have hc := (abs_integral_mul_kernel_le hD.weighted (k := fun u => Real.cosh (u / 2))
    (by fun_prop) abs_cosh_half_le_exp).2
  have hs := (abs_integral_mul_kernel_le hD.weighted (k := fun u => Real.sinh (u / 2))
    (by fun_prop) abs_sinh_half_le_exp).2
  change |coshHalfMoment D| ≤ _ at hc
  change |sinhHalfMoment D| ≤ _ at hs
  set X := Real.sqrt (exponentialSourceMass D) * Real.sqrt (∫ u, Real.exp (-|u|))
  have hp : |(primeMixedForm F D + primeMixedForm D F) / 2| ≤ 2 * vonMangoldtThreeHalvesMass *
      (Real.sqrt (exponentialSourceMass F) * Real.sqrt (exponentialSourceMass D)) := by
    rw [abs_div, abs_two]
    have := abs_add_le (primeMixedForm F D) (primeMixedForm D F)
    rw [mul_comm (Real.sqrt (exponentialSourceMass D))] at hp2
    linarith
  have hm : |2 * coshHalfMoment F * coshHalfMoment D - 2 * sinhHalfMoment F * sinhHalfMoment D| ≤
      2 * (|coshHalfMoment F| + |sinhHalfMoment F|) * X := by
    have h1 := abs_sub (2 * coshHalfMoment F * coshHalfMoment D) (2 * sinhHalfMoment F * sinhHalfMoment D)
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two] at h1
    have h2 : |coshHalfMoment F| * |coshHalfMoment D| ≤ |coshHalfMoment F| * X :=
      mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    have h3 : |sinhHalfMoment F| * |sinhHalfMoment D| ≤ |sinhHalfMoment F| * X :=
      mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    nlinarith
  unfold bareMixedEnergy
  calc |gammaMixedForm F D - (primeMixedForm F D + primeMixedForm D F) / 2 +
        (2 * coshHalfMoment F * coshHalfMoment D - 2 * sinhHalfMoment F * sinhHalfMoment D)|
      ≤ |gammaMixedForm F D| + |(primeMixedForm F D + primeMixedForm D F) / 2| +
          |2 * coshHalfMoment F * coshHalfMoment D - 2 * sinhHalfMoment F * sinhHalfMoment D| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := by linarith

/-! ### Linearity of Weil's form in the second profile -/

theorem gammaMixedForm_add_right {F G D : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (hD : CriticalHalfLineEnergyDomain D) :
    gammaMixedForm F (fun u => G u + D u) = gammaMixedForm F G + gammaMixedForm F D := by
  have hpair : ∀ r : ℝ, gammaFourierPair F (fun u => G u + D u) r =
      gammaFourierPair F G r + gammaFourierPair F D r := by
    intro r
    have h := paperFT_cx_add_const_mul hG.integrable hD.integrable 1 r
    simp only [one_mul, Complex.ofReal_one] at h
    unfold gammaFourierPair
    rw [h, Complex.add_re, Complex.add_im]
    ring
  unfold gammaMixedForm
  rw [← mul_add, ← integral_add
    (integrable_gammaFourierPair hF.integrable hG.integrable hF.gamma hG.gamma)
    (integrable_gammaFourierPair hF.integrable hD.integrable hF.gamma hD.gamma)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [hpair, add_mul]

theorem halfMoment_add_of_domain {G D : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    (hD : CriticalHalfLineEnergyDomain D) :
    coshHalfMoment (fun u => G u + D u) = coshHalfMoment G + coshHalfMoment D ∧
      sinhHalfMoment (fun u => G u + D u) = sinhHalfMoment G + sinhHalfMoment D := by
  constructor
  · unfold coshHalfMoment
    rw [← integral_add (abs_integral_mul_kernel_le hG.weighted (k := fun u => Real.cosh (u / 2))
        (by fun_prop) abs_cosh_half_le_exp).1 (abs_integral_mul_kernel_le hD.weighted
        (k := fun u => Real.cosh (u / 2)) (by fun_prop) abs_cosh_half_le_exp).1]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring)
  · unfold sinhHalfMoment
    rw [← integral_add (abs_integral_mul_kernel_le hG.weighted (k := fun u => Real.sinh (u / 2))
        (by fun_prop) abs_sinh_half_le_exp).1 (abs_integral_mul_kernel_le hD.weighted
        (k := fun u => Real.sinh (u / 2)) (by fun_prop) abs_sinh_half_le_exp).1]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring)

/-- Weil's bare form is additive in the second profile on the domain. -/
theorem bareMixedEnergy_add_right {F G D : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (hD : CriticalHalfLineEnergyDomain D) :
    bareMixedEnergy F (fun u => G u + D u) = bareMixedEnergy F G + bareMixedEnergy F D := by
  obtain ⟨hc, hs⟩ := halfMoment_add_of_domain hG hD
  unfold bareMixedEnergy
  rw [gammaMixedForm_add_right hF hG hD, primeMixedForm_add_right hF.weighted hG.weighted hD.weighted,
    primeMixedForm_add_left hG.weighted hD.weighted hF.weighted, hc, hs]
  ring

/-- The weighted mass of the defect is at most `e^{2(T+1)}` times its `L²` mass. -/
theorem exponentialSourceMass_wallDefect_le (n : ℕ) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {T : ℝ} (hT0 : 0 ≤ T) (hT : ∀ u, u < -T → G u = 0) :
    exponentialSourceMass (wallDefect n G) ≤ Real.exp (2 * (T + 1)) * ∫ u, wallDefect n G u ^ 2 := by
  have hD := criticalHalfLineEnergyDomain_wallDefect n hG hT
  unfold exponentialSourceMass
  rw [← integral_const_mul]
  refine integral_mono hD.weighted.sq (hD.sq.const_mul _) fun t => ?_
  show (Real.exp |t| * wallDefect n G t) ^ 2 ≤ Real.exp (2 * (T + 1)) * wallDefect n G t ^ 2
  rw [mul_pow]
  by_cases ht : t < -T - 1
  · rw [wallDefect_eq_zero_of_lt n hT0 hT ht]; simp
  · rcases le_or_gt 0 t with h0 | h0
    · rw [hD.support t h0]; simp
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [sq, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by rw [abs_of_neg h0]; linarith)

/-! ### The zero pairing -/

/-- Cauchy–Schwarz for the zero pairing of two square-summable families. -/
theorem summable_mul_and_norm_tsum_le {a b : XiZeroCopy → ℂ} (ha : Summable fun q => ‖a q‖ ^ 2)
    (hb : Summable fun q => ‖b q‖ ^ 2) :
    Summable (fun q => a q * b q) ∧
      ‖∑' q, a q * b q‖ ≤ Real.sqrt (∑' q, ‖a q‖ ^ 2) * Real.sqrt (∑' q, ‖b q‖ ^ 2) := by
  have hn : Summable fun q => ‖a q * b q‖ :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => by
      rw [norm_mul]; nlinarith [sq_nonneg (‖a q‖ - ‖b q‖)]) ((ha.add hb).div_const 2)
  refine ⟨hn.of_norm, (norm_tsum_le_tsum_norm hn).trans ?_⟩
  refine Real.tsum_le_of_sum_le (fun q => norm_nonneg _) fun s => ?_
  simp_rw [norm_mul]
  exact (Real.sum_mul_le_sqrt_mul_sqrt s (fun q => ‖a q‖) (fun q => ‖b q‖)).trans
    (mul_le_mul (Real.sqrt_le_sqrt (ha.sum_le_tsum s fun q _ => sq_nonneg _))
      (Real.sqrt_le_sqrt (hb.sum_le_tsum s fun q _ => sq_nonneg _)) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _))

/-- **The zero pairing of two profiles is Weil's form.** If the unit tilt of `F` lies in the energy
domain and `G ∈ H` vanishes below some `−T`, then `Σ_z L F(z) L G(−z) = W(F, G)`, absolutely
convergent. -/
theorem hasSum_bareMixedEnergy_of_unitTilt_of_bounded {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F)
    (hF1 : CriticalHalfLineEnergyDomain (fun u => Real.exp (-(1 * u)) * F u))
    (hG : CriticalHalfLineEnergyDomain G) {T : ℝ} (hT : ∀ u, u < -T → G u = 0) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
      negativeHalfLineLaplace (cx G) (-centredZero q)) ((bareMixedEnergy F G : ℝ) : ℂ) := by
  obtain ⟨T, hT0, hT⟩ : ∃ T' : ℝ, 0 ≤ T' ∧ ∀ u, u < -T' → G u = 0 :=
    ⟨max T 0, le_max_right _ _, fun u hu => hT u (by linarith [le_max_left T 0])⟩
  have hA := summable_norm_sq_laplace_centredZero hF1
  have hG1 := criticalHalfLineEnergyDomain_exp_mul_of_bounded hG hT (c := 1) zero_le_one
  have hB := summable_norm_sq_laplace_neg_centredZero hG1
  have hDd : ∀ n, CriticalHalfLineEnergyDomain (wallDefect n G) := fun n =>
    criticalHalfLineEnergyDomain_wallDefect n hG hT
  have hD1 : ∀ n, CriticalHalfLineEnergyDomain (fun u => Real.exp (-(1 * u)) * wallDefect n G u) :=
    fun n => criticalHalfLineEnergyDomain_exp_mul_of_bounded (hDd n) (T := T + 1)
      (fun u hu => wallDefect_eq_zero_of_lt n hT0 hT (by linarith)) zero_le_one
  have hDB : ∀ n, Summable fun q : XiZeroCopy =>
      ‖negativeHalfLineLaplace (cx (wallDefect n G)) (-centredZero q)‖ ^ 2 := fun n =>
    summable_norm_sq_laplace_neg_centredZero (hD1 n)
  have hGn : ∀ n, HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
      negativeHalfLineLaplace (cx (wallMollify n G)) (-centredZero q))
        ((bareMixedEnergy F (wallMollify n G) : ℝ) : ℂ) := fun n =>
    hasSum_bareMixedEnergy_of_domain hF (contDiff_wallMollify n hG)
      (hasCompactSupport_wallMollify n hG hT) fun u hu => wallMollify_eq_zero_of_nonneg n hG hu
  -- the transform of the defect is the difference of transforms
  have hLsub : ∀ n (q : XiZeroCopy), negativeHalfLineLaplace (cx G) (-centredZero q) =
      negativeHalfLineLaplace (cx (wallMollify n G)) (-centredZero q) -
        negativeHalfLineLaplace (cx (wallDefect n G)) (-centredZero q) := by
    intro n q
    have hre : (centredZero q).re < 4 := by
      linarith [(abs_lt.mp (abs_re_centredZero_lt q)).2]
    have h1 := integrable_cexp_neg_mul_cx (criticalHalfLineEnergyDomain_wallMollify n hG hT) hre
    have h2 := integrable_cexp_neg_mul_cx hG hre
    have e : negativeHalfLineLaplace (cx (wallDefect n G)) (-centredZero q) =
        negativeHalfLineLaplace (cx (wallMollify n G)) (-centredZero q) -
          negativeHalfLineLaplace (cx G) (-centredZero q) := by
      unfold negativeHalfLineLaplace
      rw [← integral_sub h1 h2]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only [cx, wallDefect]
      push_cast
      ring
    rw [e]; ring
  set S := ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
    negativeHalfLineLaplace (cx G) (-centredZero q)
  -- the discrepancy is a vanishing sequence
  have hconst : ∀ n, S - ((bareMixedEnergy F G : ℝ) : ℂ) =
      ((bareMixedEnergy F (wallDefect n G) : ℝ) : ℂ) -
        ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx (wallDefect n G)) (-centredZero q) := by
    intro n
    have hsD := (summable_mul_and_norm_tsum_le hA (hDB n)).1
    have hadd := bareMixedEnergy_add_right hF hG (hDd n)
    have hfun : (fun u => G u + wallDefect n G u) = wallMollify n G := by
      funext u; simp only [wallDefect]; ring
    rw [hfun] at hadd
    have hS : S = ((bareMixedEnergy F (wallMollify n G) : ℝ) : ℂ) -
        ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx (wallDefect n G)) (-centredZero q) := by
      rw [← (hGn n).tsum_eq, ← (hGn n).summable.tsum_sub hsD]
      exact tsum_congr fun q => by rw [hLsub n q]; ring
    rw [hS, hadd]
    push_cast
    ring
  -- both parts of the discrepancy vanish
  have hΓ := tendsto_gammaEnergy_wallDefect hG hT
  have hE : Tendsto (fun n => exponentialSourceMass (wallDefect n G)) atTop (𝓝 0) := by
    have h := (tendsto_integral_sq_wallDefect hG hT).const_mul (Real.exp (2 * (T + 1)))
    rw [mul_zero] at h
    exact squeeze_zero (fun n => exponentialSourceMass_nonneg _)
      (fun n => exponentialSourceMass_wallDefect_le n hG hT0 hT) h
  have hlog := tendsto_logEnergy_tilt_wallDefect hG hT
  set cF := Real.sqrt (∫ r : ℝ, ‖paperFT (cx F) r‖ ^ 2 * |EF.gammaBracket r|)
  set eF := Real.sqrt (exponentialSourceMass F)
  set J := Real.sqrt (∫ u, Real.exp (-|u|))
  set A := Real.sqrt (∑' q : XiZeroCopy, ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ ^ 2)
  set mF := |coshHalfMoment F| + |sinhHalfMoment F|
  have hsq0 : ∀ {f : ℕ → ℝ}, Tendsto f atTop (𝓝 0) → Tendsto (fun n => Real.sqrt (f n)) atTop (𝓝 0) :=
    fun {f} hf => by
      have h := (Real.continuous_sqrt.tendsto 0).comp hf
      rw [Real.sqrt_zero] at h
      exact h
  have hbound : Tendsto (fun n => (2 * Real.pi)⁻¹ * (cF * Real.sqrt
      (∫ r : ℝ, ‖paperFT (cx (wallDefect n G)) r‖ ^ 2 * |EF.gammaBracket r|)) +
      2 * vonMangoldtThreeHalvesMass * (eF * Real.sqrt (exponentialSourceMass (wallDefect n G))) +
      2 * mF * (Real.sqrt (exponentialSourceMass (wallDefect n G)) * J) +
      A * Real.sqrt (16 / Real.pi * ∫ t : ℝ, (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
        ‖paperFT (cx fun u => Real.exp (-(1 * u)) * wallDefect n G u) (t : ℂ)‖ ^ 2)) atTop (𝓝 0) := by
    have h1 := ((hsq0 hΓ).const_mul cF).const_mul (2 * Real.pi)⁻¹
    have h2 := ((hsq0 hE).const_mul eF).const_mul (2 * vonMangoldtThreeHalvesMass)
    have h3 := ((hsq0 hE).mul_const J).const_mul (2 * mF)
    have hlog' := hlog.const_mul (16 / Real.pi)
    rw [mul_zero] at hlog'
    have h4 := (hsq0 hlog').const_mul A
    simpa using ((h1.add h2).add h3).add h4
  have hlim : Tendsto (fun n => ((bareMixedEnergy F (wallDefect n G) : ℝ) : ℂ) -
      ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx (wallDefect n G)) (-centredZero q)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hbound
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_bareMixedEnergy_le hF (hDd n)
    · refine (summable_mul_and_norm_tsum_le hA (hDB n)).2.trans ?_
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
        (tsum_norm_sq_laplace_neg_wallDefect_le n hG hT0 hT)) (Real.sqrt_nonneg _)
  have hzero : S - ((bareMixedEnergy F G : ℝ) : ℂ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hlim.congr fun n => (hconst n).symm)
  have hSum := (summable_mul_and_norm_tsum_le hA hB).1
  rw [← sub_eq_zero.mp hzero]
  exact hSum.hasSum

end GaloisForLFunctions.ExclusionOfTheCriticalState
