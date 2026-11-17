import GaloisForLFunctions.ExclusionOfTheCriticalState.TheAveragedStateDecaysAtTheRateOfTheZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTransformOfTheStateIsMeromorphicInThePlane
import GaloisForLFunctions.RHTower.PrimeLagLandauWeights
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.XiHorizontalSlopeNearOne
import GaloisForLFunctions.RHTower.XiWardGlobalCapRightZeroSum
import GaloisForLFunctions.RHTower.HodgeNyquistExclusion

/-!
# The logarithmic derivative of zeta is sublogarithmic right of the zeros

Let `N = G'/G`, `G(s) = (s - 1) ζ(s)`, be the regular part of `ζ'/ζ`:
`ζ'/ζ(s) = N(s) - 1/(s - 1)`. If every centred zero has `Re z ≤ κ`, then `N` is holomorphic on
`Re s > 1/2 + κ` and

* `|N(s)| ≤ C log(|Im s| + 4)` on every half-plane `Re s ≥ a > 1/2 + κ`: the distance to the zeros
  high in the strip, the Dirichlet series right of `Re s = 2`, compactness in between;
* `|N(s₀ + iT)| ≤ C log(|T| + 4)^{(b - s₀)/(b - a)}` for `1/2 + κ < a < s₀ < b`, `1 < b`: three
  lines between the logarithm on `Re s = a` and the bounded Dirichlet series on `Re s = b`;
* `|N(1/2 + σ + it)|² ≤ C log(|t| + 4)` for `σ > κ`, `σ > 1/4 + κ/2`: the exponent `1/2`.

The interpolation at height `T` uses the gauge `exp((s - iT)² - c (b - s))` with the real constant
`c = log log(|T| + 4)/(b - a)`. A real `c` makes the modulus of the gauge exact, and the Gaussian
localises the logarithm on `Re s = a` at the height `T`.

On `Re p > 1/2` the Euler sum is `Σ Λ(n) n^{-1/2-p} = 1/(p - 1/2) - N(1/2 + p)`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The regular part of the logarithmic derivative -/

/-- The regular part of `ζ'/ζ`: the logarithmic derivative of `(s - 1) ζ(s)`. -/
def zetaRegularLogDeriv (s : ℂ) : ℂ := logDeriv zetaResidueUnit s

theorem zetaResidueUnit_of_ne {s : ℂ} (hs : s ≠ 1) :
    zetaResidueUnit s = (s - 1) * riemannZeta s := by
  unfold zetaResidueUnit
  exact Function.update_of_ne hs _ _

theorem zetaResidueUnit_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : zetaResidueUnit s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h1
  · rw [zetaResidueUnit_one]
    exact one_ne_zero
  · rw [zetaResidueUnit_of_ne h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs)

/-- `(s - 1) ζ(s)` has no zero to the right of the zeros of `ζ`. -/
theorem zetaResidueUnit_ne_zero_of_right_of_zeros {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {s : ℂ} (hs : 1 / 2 + κ < s.re) :
    zetaResidueUnit s ≠ 0 := by
  rcases le_or_gt 1 s.re with h1 | h1
  · exact zetaResidueUnit_ne_zero_of_one_le_re h1
  · have hs1 : s ≠ 1 := fun h => by
      rw [h, Complex.one_re] at h1
      exact lt_irrefl _ h1
    rw [zetaResidueUnit_of_ne hs1]
    refine mul_ne_zero (sub_ne_zero.mpr hs1) fun hζ => ?_
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_riemannZeta_eq_zero (by linarith) hs1 hζ
    have h2 := hzero q
    have h3 : (centredZero q).re = s.re - 1 / 2 := by
      unfold centredZero
      rw [hq]
      simp
    linarith

theorem differentiableAt_zetaRegularLogDeriv {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {s : ℂ} (hs : 1 / 2 + κ < s.re) :
    DifferentiableAt ℂ zetaRegularLogDeriv s := by
  have h1 : DifferentiableAt ℂ (deriv zetaResidueUnit) s :=
    (analyticAt_zetaResidueUnit s).deriv.differentiableAt
  show DifferentiableAt ℂ (fun y => deriv zetaResidueUnit y / zetaResidueUnit y) s
  exact h1.div (analyticAt_zetaResidueUnit s).differentiableAt
    (zetaResidueUnit_ne_zero_of_right_of_zeros hκ hzero hs)

/-- `N = ζ'/ζ + 1/(s - 1)` off the pole. -/
theorem zetaRegularLogDeriv_eq {s : ℂ} (hs : s ≠ 1) (hG : zetaResidueUnit s ≠ 0) :
    zetaRegularLogDeriv s = logDeriv riemannZeta s + (s - 1)⁻¹ := by
  unfold zetaRegularLogDeriv
  rw [logDeriv_zeta_eq hs hG]
  ring

/-- Right of `Re s = 1` the regular part is bounded by the Dirichlet series and the pole. -/
theorem norm_zetaRegularLogDeriv_le_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    ‖zetaRegularLogDeriv s‖ ≤ 2 / (s.re - 1) + 2 := by
  have hs1 : s ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  rw [zetaRegularLogDeriv_eq hs1 (zetaResidueUnit_ne_zero_of_one_le_re hs.le)]
  have h1 : ‖logDeriv riemannZeta s‖ ≤ 1 / (s.re - 1) + 2 := by
    have h := DeBruijn.norm_logDeriv_riemannZeta_le_inv_sub_one_add_two hs s.im
    rwa [Complex.re_add_im] at h
  have hpos : 0 < s.re - 1 := sub_pos.mpr hs
  have h2 : ‖(s - 1)⁻¹‖ ≤ 1 / (s.re - 1) := by
    rw [norm_inv, one_div]
    refine inv_anti₀ hpos ?_
    have := Complex.re_le_norm (s - 1)
    rwa [Complex.sub_re, Complex.one_re] at this
  have e : 2 / (s.re - 1) = 1 / (s.re - 1) + 1 / (s.re - 1) := by ring
  linarith [norm_add_le (logDeriv riemannZeta s) (s - 1)⁻¹]

theorem one_le_log_abs_add_four (t : ℝ) : 1 ≤ Real.log (|t| + 4) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h1 := Real.exp_one_lt_d9
  have h2 := abs_nonneg t
  norm_num at h1
  linarith

/-! ### The logarithmic bound right of the zeros -/

/-- **The logarithmic bound.** On a half-plane `Re s ≥ a` to the right of the zeros the regular
part of `ζ'/ζ` is at most a multiple of `log(|Im s| + 4)`. -/
theorem exists_norm_zetaRegularLogDeriv_le_log {κ a : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (ha : 1 / 2 + κ < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re →
      ‖zetaRegularLogDeriv s‖ ≤ C * Real.log (|s.im| + 4) := by
  have hK : IsCompact (Icc a 2 ×ℂ Icc (-4 : ℝ) 4) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn zetaRegularLogDeriv (Icc a 2 ×ℂ Icc (-4 : ℝ) 4) := fun s hs =>
    (differentiableAt_zetaRegularLogDeriv hκ hzero
      (by have := (Complex.mem_reProdIm.mp hs).1.1; linarith)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  obtain ⟨δ, hδ, hδ1, hδa⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ a - 1 / 2 - κ :=
    ⟨min (a - 1 / 2 - κ) 1, lt_min (by linarith) one_pos, min_le_right _ _, min_le_left _ _⟩
  have hCnn : 0 ≤ logDerivZetaConstant / δ := div_nonneg logDerivZetaConstant_nonneg hδ.le
  have hM0 : 0 ≤ |M| := abs_nonneg M
  refine ⟨4 + (logDerivZetaConstant / δ + 1) + |M|, by linarith, fun s hs => ?_⟩
  have hL := one_le_log_abs_add_four s.im
  rcases le_or_gt 2 s.re with h2 | h2
  · -- right of `Re s = 2`: the Dirichlet series
    have h := norm_zetaRegularLogDeriv_le_of_one_lt_re (s := s) (by linarith)
    have h3 : 2 / (s.re - 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ logDerivZetaConstant / δ + 1 + |M|)
      (by linarith : (0 : ℝ) ≤ Real.log (|s.im| + 4))]
  · rcases le_or_gt 4 |s.im| with h4 | h4
    · -- high in the strip: the distance to the zeros
      have hs1 : s ≠ 1 := fun h => by
        rw [h, Complex.one_im, abs_zero] at h4
        linarith
      have hall : ∀ q : XiZeroCopy, δ ≤ ‖((s.re : ℂ) + (s.im : ℂ) * I) - (q.1 : ℂ)‖ := fun q => by
        rw [Complex.re_add_im]
        have h1 := Complex.re_le_norm (s - (q.1 : ℂ))
        have h2' := hzero q
        have h3 : (centredZero q).re = (q.1 : ℂ).re - 1 / 2 := by
          unfold centredZero
          simp
        rw [Complex.sub_re] at h1
        linarith
      have hζ := norm_logDeriv_zeta_le_abs (σ := s.re) (t := s.im) (by linarith) h2.le h4 hδ hδ1
        hall
      rw [Complex.re_add_im] at hζ
      have hG := zetaResidueUnit_ne_zero_of_right_of_zeros hκ hzero (s := s) (by linarith)
      rw [zetaRegularLogDeriv_eq hs1 hG]
      have hinv : ‖(s - 1)⁻¹‖ ≤ 1 := by
        rw [norm_inv]
        refine inv_le_one_of_one_le₀ ?_
        have := Complex.abs_im_le_norm (s - 1)
        rw [Complex.sub_im, Complex.one_im, sub_zero] at this
        linarith
      have hlog : Real.log |s.im| ≤ Real.log (|s.im| + 4) :=
        Real.log_le_log (by linarith) (by linarith)
      have h5 : logDerivZetaConstant * Real.log |s.im| / δ ≤
          logDerivZetaConstant / δ * Real.log (|s.im| + 4) := by
        rw [mul_div_right_comm]
        exact mul_le_mul_of_nonneg_left hlog hCnn
      have h6 := norm_add_le (logDeriv riemannZeta s) (s - 1)⁻¹
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 + |M|)
        (by linarith : (0 : ℝ) ≤ Real.log (|s.im| + 4))]
    · -- the compact part
      have hmem : s ∈ Icc a 2 ×ℂ Icc (-4 : ℝ) 4 :=
        Complex.mem_reProdIm.mpr ⟨⟨hs, h2.le⟩, ⟨(abs_lt.mp h4).1.le, (abs_lt.mp h4).2.le⟩⟩
      have h := hM s hmem
      have h7 := le_abs_self M
      nlinarith [mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ Real.log (|s.im| + 4) - 1),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 4 + (logDerivZetaConstant / δ + 1))
          (by linarith : (0 : ℝ) ≤ Real.log (|s.im| + 4))]

/-! ### Two elementary inequalities for the Gaussian gauge -/

theorem one_add_abs_mul_exp_neg_sq_le (r : ℝ) : (1 + |r|) * Real.exp (-r ^ 2) ≤ Real.exp 1 := by
  have h1 : 1 + |r| ≤ Real.exp |r| := by linarith [Real.add_one_le_exp |r|]
  have h2 : Real.exp |r| * Real.exp (-r ^ 2) ≤ Real.exp 1 := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [sq_abs r, sq_nonneg (|r| - 1 / 2)]
  exact (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le).trans h2

/-- The logarithm at height `y` is the logarithm at height `T` up to the factor `1 + |y - T|`. -/
theorem log_abs_add_four_le (y T : ℝ) :
    Real.log (|y| + 4) ≤ Real.log (|T| + 4) * (1 + |y - T|) := by
  have hL := one_le_log_abs_add_four T
  have hd : 0 ≤ |y - T| := abs_nonneg _
  have hT : 0 ≤ |T| := abs_nonneg _
  have h1 : |y| + 4 ≤ (|T| + 4) * (1 + |y - T|) := by
    have h := abs_add_le (y - T) T
    rw [sub_add_cancel] at h
    nlinarith [mul_nonneg hT hd]
  have h2 : Real.log ((|T| + 4) * (1 + |y - T|)) =
      Real.log (|T| + 4) + Real.log (1 + |y - T|) :=
    Real.log_mul (by positivity) (by positivity)
  have h3 : Real.log (1 + |y - T|) ≤ |y - T| := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + |y - T|)
    linarith
  have h4 := Real.log_le_log (by positivity) h1
  nlinarith [mul_nonneg (sub_nonneg.mpr hL) hd]

/-! ### Three lines with a Gaussian gauge -/

/-- The gauged function of the three-lines argument at height `T`: a Gaussian centred at `iT`
times `e^{-c (b - s)}`. -/
def gaugedLogDeriv (b c T : ℝ) (s : ℂ) : ℂ :=
  zetaRegularLogDeriv s * cexp ((s - (T : ℂ) * I) ^ 2 - (c : ℂ) * ((b : ℂ) - s))

theorem norm_gaugedLogDeriv (b c T : ℝ) (s : ℂ) :
    ‖gaugedLogDeriv b c T s‖ = ‖zetaRegularLogDeriv s‖ *
      Real.exp (s.re ^ 2 - (s.im - T) ^ 2 - c * (b - s.re)) := by
  have e : ((s - (T : ℂ) * I) ^ 2 - (c : ℂ) * ((b : ℂ) - s)).re =
      s.re ^ 2 - (s.im - T) ^ 2 - c * (b - s.re) := by
    rw [Complex.sub_re, Complex.re_ofReal_mul, sq (s - (T : ℂ) * I), Complex.mul_re]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  unfold gaugedLogDeriv
  rw [norm_mul, Complex.norm_exp, e]

theorem differentiableAt_gaugedLogDeriv {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (b c T : ℝ) {s : ℂ}
    (hs : 1 / 2 + κ < s.re) : DifferentiableAt ℂ (gaugedLogDeriv b c T) s := by
  have h2 : DifferentiableAt ℂ
      (fun s : ℂ => cexp ((s - (T : ℂ) * I) ^ 2 - (c : ℂ) * ((b : ℂ) - s))) s := by fun_prop
  exact (differentiableAt_zetaRegularLogDeriv hκ hzero hs).mul h2

/-- **The sublogarithmic bound.** Between a line `Re s = a` to the right of the zeros and a line
`Re s = b > 1` the regular part of `ζ'/ζ` is at most `C log(|T| + 4)^θ` on `Re s = s₀`, with the
three-lines exponent `θ = (b - s₀)/(b - a)`. -/
theorem exists_norm_zetaRegularLogDeriv_le_rpow {κ a b s₀ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (ha : 1 / 2 + κ < a) (has : a < s₀)
    (hsb : s₀ < b) (hb : 1 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, ‖zetaRegularLogDeriv ((s₀ : ℂ) + (T : ℂ) * I)‖ ≤
      C * Real.log (|T| + 4) ^ ((b - s₀) / (b - a)) := by
  obtain ⟨C₁, hC₁, hlog⟩ := exists_norm_zetaRegularLogDeriv_le_log hκ hzero ha
  have hab : a < b := has.trans hsb
  have hba : 0 < b - a := sub_pos.mpr hab
  have ha0 : 0 ≤ a := by linarith
  have hb1 : 0 < b - 1 := sub_pos.mpr hb
  have hC₂ : 0 ≤ 2 / (b - 1) + 2 := by positivity
  have hE : 0 < Real.exp (b ^ 2 + 1) := Real.exp_pos _
  refine ⟨(C₁ + (2 / (b - 1) + 2)) * Real.exp (b ^ 2 + 1),
    mul_nonneg (by linarith) hE.le, fun T => ?_⟩
  have hL1 : 1 ≤ Real.log (|T| + 4) := one_le_log_abs_add_four T
  have hL0 : 0 < Real.log (|T| + 4) := by linarith
  have hℓ0 : 0 ≤ Real.log (Real.log (|T| + 4)) := Real.log_nonneg hL1
  set L : ℝ := Real.log (|T| + 4) with hLdef
  set c : ℝ := Real.log L / (b - a) with hcdef
  have hc0 : 0 ≤ c := div_nonneg hℓ0 hba.le
  have hcba : c * (b - a) = Real.log L := div_mul_cancel₀ _ hba.ne'
  -- the gauged function on the closed strip: the Gaussian absorbs the drift of the logarithm
  have hkey : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖gaugedLogDeriv b c T z‖ ≤
      C₁ * L * Real.exp (b ^ 2 + 1) * Real.exp (-(c * (b - z.re))) := by
    intro z hza hzb
    rw [norm_gaugedLogDeriv]
    have h4 : 0 ≤ 1 + |z.im - T| := by positivity
    have h1 : ‖zetaRegularLogDeriv z‖ ≤ C₁ * (L * (1 + |z.im - T|)) :=
      (hlog z hza).trans (mul_le_mul_of_nonneg_left (log_abs_add_four_le z.im T) hC₁)
    have h2 : Real.exp (z.re ^ 2 - (z.im - T) ^ 2 - c * (b - z.re)) ≤
        Real.exp (b ^ 2) * Real.exp (-(z.im - T) ^ 2) * Real.exp (-(c * (b - z.re))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have : z.re ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (ha0.trans hza) hzb 2
      linarith
    have h3 := one_add_abs_mul_exp_neg_sq_le (z.im - T)
    have hCL : 0 ≤ C₁ * L * Real.exp (b ^ 2) :=
      mul_nonneg (mul_nonneg hC₁ hL0.le) (Real.exp_pos _).le
    calc ‖zetaRegularLogDeriv z‖ * Real.exp (z.re ^ 2 - (z.im - T) ^ 2 - c * (b - z.re))
        ≤ (C₁ * (L * (1 + |z.im - T|))) * (Real.exp (b ^ 2) * Real.exp (-(z.im - T) ^ 2) *
            Real.exp (-(c * (b - z.re)))) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (mul_nonneg hC₁ (mul_nonneg hL0.le h4))
      _ = C₁ * L * Real.exp (b ^ 2) * ((1 + |z.im - T|) * Real.exp (-(z.im - T) ^ 2)) *
            Real.exp (-(c * (b - z.re))) := by ring
      _ ≤ C₁ * L * Real.exp (b ^ 2) * Real.exp 1 * Real.exp (-(c * (b - z.re))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hCL) (Real.exp_pos _).le
      _ = C₁ * L * Real.exp (b ^ 2 + 1) * Real.exp (-(c * (b - z.re))) := by
          rw [Real.exp_add]
          ring
  have hcl : closure (Complex.re ⁻¹' Ioo a b) ⊆ Complex.re ⁻¹' Icc a b :=
    closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩) (isClosed_Icc.preimage Complex.continuous_re)
  have hfd : DiffContOnCl ℂ (gaugedLogDeriv b c T) (Complex.re ⁻¹' Ioo a b) :=
    ⟨fun z hz => (differentiableAt_gaugedLogDeriv hκ hzero b c T
        (by have := hz.1; linarith)).differentiableWithinAt,
      fun z hz => (differentiableAt_gaugedLogDeriv hκ hzero b c T
        (by have := (hcl hz).1; linarith)).continuousAt.continuousWithinAt⟩
  have hE1 : Real.exp (-(c * (b - a))) * L = 1 := by
    rw [hcba, Real.exp_neg, Real.exp_log hL0, inv_mul_cancel₀ hL0.ne']
  have hbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖gaugedLogDeriv b c T z‖ ≤
      (C₁ + (2 / (b - 1) + 2)) * Real.exp (b ^ 2 + 1) := by
    intro z hza hzb
    refine PhragmenLindelof.vertical_strip hfd ?_ ?_ ?_ hza hzb
    · -- the gauged function is bounded on the strip
      refine ⟨0, div_pos Real.pi_pos hba, 0, Asymptotics.IsBigO.of_bound
        (C₁ * L * Real.exp (b ^ 2 + 1))
        (eventually_inf_principal.mpr (Eventually.of_forall fun w hw => ?_))⟩
      rw [zero_mul, Real.exp_zero, norm_one, mul_one]
      refine (hkey w hw.1.le hw.2.le).trans ?_
      refine mul_le_of_le_one_right (mul_nonneg (mul_nonneg hC₁ hL0.le) hE.le) ?_
      rw [Real.exp_le_one_iff]
      have := mul_nonneg hc0 (sub_nonneg.mpr hw.2.le)
      linarith
    · -- the line `Re s = a`: the gauge divides by `log(|T| + 4)`
      intro w hw
      have h := hkey w hw.ge (hw.le.trans hab.le)
      rw [hw] at h
      have e : C₁ * L * Real.exp (b ^ 2 + 1) * Real.exp (-(c * (b - a))) =
          C₁ * Real.exp (b ^ 2 + 1) := by
        calc C₁ * L * Real.exp (b ^ 2 + 1) * Real.exp (-(c * (b - a)))
            = C₁ * Real.exp (b ^ 2 + 1) * (Real.exp (-(c * (b - a))) * L) := by ring
          _ = C₁ * Real.exp (b ^ 2 + 1) := by rw [hE1, mul_one]
      rw [e] at h
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hE.le)
    · -- the line `Re s = b`: the Dirichlet series
      intro w hw
      rw [norm_gaugedLogDeriv, hw, sub_self, mul_zero, sub_zero]
      have h1 : ‖zetaRegularLogDeriv w‖ ≤ 2 / (b - 1) + 2 := by
        have h := norm_zetaRegularLogDeriv_le_of_one_lt_re (s := w) (by rw [hw]; exact hb)
        rwa [hw] at h
      have h2 : Real.exp (b ^ 2 - (w.im - T) ^ 2) ≤ Real.exp (b ^ 2 + 1) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (w.im - T)])
      exact (mul_le_mul h1 h2 (Real.exp_pos _).le hC₂).trans
        (mul_le_mul_of_nonneg_right (by linarith) hE.le)
  have hre : ((s₀ : ℂ) + (T : ℂ) * I).re = s₀ := by simp
  have him : ((s₀ : ℂ) + (T : ℂ) * I).im = T := by simp
  have h0 := hbound ((s₀ : ℂ) + (T : ℂ) * I) (by rw [hre]; exact has.le) (by rw [hre]; exact hsb.le)
  rw [norm_gaugedLogDeriv, hre, him, sub_self] at h0
  have hpow : L ^ ((b - s₀) / (b - a)) = Real.exp (c * (b - s₀)) := by
    rw [Real.rpow_def_of_pos hL0, hcdef]
    congr 1
    ring
  rw [hpow]
  have hexp : Real.exp (s₀ ^ 2 - 0 ^ 2 - c * (b - s₀)) * Real.exp (c * (b - s₀)) =
      Real.exp (s₀ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : (1 : ℝ) ≤ Real.exp (s₀ ^ 2) := Real.one_le_exp (sq_nonneg _)
  calc ‖zetaRegularLogDeriv ((s₀ : ℂ) + (T : ℂ) * I)‖
      ≤ ‖zetaRegularLogDeriv ((s₀ : ℂ) + (T : ℂ) * I)‖ * Real.exp (s₀ ^ 2) :=
        le_mul_of_one_le_right (norm_nonneg _) h1
    _ = (‖zetaRegularLogDeriv ((s₀ : ℂ) + (T : ℂ) * I)‖ *
          Real.exp (s₀ ^ 2 - 0 ^ 2 - c * (b - s₀))) * Real.exp (c * (b - s₀)) := by
        rw [← hexp]
        ring
    _ ≤ (C₁ + (2 / (b - 1) + 2)) * Real.exp (b ^ 2 + 1) * Real.exp (c * (b - s₀)) :=
        mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le

/-! ### The centred coordinate -/

theorem differentiableAt_zetaRegularLogDeriv_half_add {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {p : ℂ} (hp : κ < p.re) :
    DifferentiableAt ℂ (fun p : ℂ => zetaRegularLogDeriv (1 / 2 + p)) p := by
  have h := differentiableAt_zetaRegularLogDeriv hκ hzero (s := 1 / 2 + p)
    (by rw [re_one_half_add]; linarith)
  have h2 : DifferentiableAt ℂ (fun p : ℂ => (1 / 2 : ℂ) + p) p := by fun_prop
  exact h.comp p h2

/-- The logarithmic bound in the centred coordinate `p = s - 1/2`. -/
theorem exists_norm_zetaRegularLogDeriv_half_add_le_log {κ σ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hσ : κ < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ, σ ≤ p.re →
      ‖zetaRegularLogDeriv (1 / 2 + p)‖ ≤ C * Real.log (|p.im| + 4) := by
  obtain ⟨C, hC, h⟩ := exists_norm_zetaRegularLogDeriv_le_log hκ hzero
    (a := 1 / 2 + σ) (by linarith)
  refine ⟨C, hC, fun p hp => ?_⟩
  have h1 := h (1 / 2 + p) (by rw [re_one_half_add]; linarith)
  have him : ((1 : ℂ) / 2 + p).im = p.im := by simp
  rwa [him] at h1

/-- **The square of the regular part is at most logarithmic.** On a line `Re p = σ` with
`σ > κ` and `σ > 1/4 + κ/2` the three-lines exponent is `1/2`. -/
theorem exists_norm_sq_zetaRegularLogDeriv_line_le_log {κ σ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκσ : κ < σ) (hσ : 1 / 4 + κ / 2 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖zetaRegularLogDeriv (1 / 2 + ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤ C * Real.log (|t| + 4) := by
  obtain ⟨a, ha1, ha3, ha4⟩ : ∃ a : ℝ, 1 / 2 + κ < a ∧ a < 1 / 2 + σ ∧ a < 2 * σ := by
    refine ⟨(1 / 2 + κ + min (1 / 2 + σ) (2 * σ)) / 2, ?_, ?_, ?_⟩
    · have : 1 / 2 + κ < min (1 / 2 + σ) (2 * σ) := lt_min (by linarith) (by linarith)
      linarith
    · have h1 : 1 / 2 + κ < min (1 / 2 + σ) (2 * σ) := lt_min (by linarith) (by linarith)
      have h2 := min_le_left (1 / 2 + σ) (2 * σ)
      linarith
    · have h1 : 1 / 2 + κ < min (1 / 2 + σ) (2 * σ) := lt_min (by linarith) (by linarith)
      have h2 := min_le_right (1 / 2 + σ) (2 * σ)
      linarith
  obtain ⟨C, hC, h⟩ := exists_norm_zetaRegularLogDeriv_le_rpow hκ hzero ha1 ha3
    (b := 1 + 2 * σ - a) (by linarith) (by linarith)
  refine ⟨C ^ 2, sq_nonneg _, fun t => ?_⟩
  have hθ : (1 + 2 * σ - a - (1 / 2 + σ)) / (1 + 2 * σ - a - a) = 1 / 2 := by
    rw [div_eq_iff (ne_of_gt (by linarith))]
    ring
  have h1 := h t
  rw [hθ] at h1
  have e : (1 / 2 : ℂ) + ((σ : ℂ) + (t : ℂ) * I) = ((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * I := by
    push_cast
    ring
  rw [e]
  have hL0 : 0 ≤ Real.log (|t| + 4) := by linarith [one_le_log_abs_add_four t]
  calc ‖zetaRegularLogDeriv (((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ (C * Real.log (|t| + 4) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = C ^ 2 * Real.log (|t| + 4) := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hL0]

/-- The unconditional instance: every line `Re p = σ > 20999/48000`. -/
theorem exists_norm_sq_zetaRegularLogDeriv_line_le_log_seed {σ : ℝ}
    (hσ : 20999 / 48000 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖zetaRegularLogDeriv (1 / 2 + ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤ C * Real.log (|t| + 4) :=
  exists_norm_sq_zetaRegularLogDeriv_line_le_log (κ := 8999 / 24000) (by norm_num)
    re_centredZero_le_seed (by linarith) (by linarith)

/-! ### The Euler sum right of the pole -/

/-- On `Re p > 1/2` the Euler sum is the pole `1/(p - 1/2)` minus the regular part. -/
theorem tsum_vonMangoldtAtom_mul_cexp_neg {p : ℂ} (hp : 1 / 2 < p.re) :
    ∑' n : ℕ, (vonMangoldtAtom n : ℂ) * cexp (-(p * (Real.log n : ℂ))) =
      (p - 1 / 2)⁻¹ - zetaRegularLogDeriv (1 / 2 + p) := by
  have h := tsum_vonMangoldtAtom_mul_cexp (p := -p) (by rw [Complex.neg_re]; linarith)
  have hs : (1 : ℝ) < ((1 : ℂ) / 2 + p).re := by
    rw [re_one_half_add]
    linarith
  have hs1 : (1 / 2 + p : ℂ) ≠ 1 := fun h1 => by
    rw [h1, Complex.one_re] at hs
    exact lt_irrefl _ hs
  rw [zetaRegularLogDeriv_eq hs1 (zetaResidueUnit_ne_zero_of_one_le_re hs.le), logDeriv_apply]
  have e1 : (1 / 2 - -p : ℂ) = 1 / 2 + p := by ring
  have e2 : (1 / 2 + p - 1 : ℂ) = p - 1 / 2 := by ring
  rw [e1] at h
  simp only [neg_mul] at h
  rw [h, e2]
  ring

end GaloisForLFunctions.ExclusionOfTheCriticalState
