import GaloisForLFunctions.RHTower.ChiLogDerivHigherDerivatives
import GaloisForLFunctions.RHTower.Sieve.LogNormSegment

/-!
# Height jets of the chi-increment along Levinson lines

Along a vertical line `c + t i` inside an open set of analyticity, the real iterated derivatives
of a restriction are `i^n` times the complex ones (a local form of the corpus's line-restriction
law).  Applied to `χ'/χ`, which is analytic on the half-planes `Im z > 1` and `Im z < −1`, the
increment `L(c + w + t i) − L(c + t i)` has `j`-th height derivative bounded, for `t ≥ 4` and
`2|v| ≤ t`, `w = −(1 + i v)`, by

  `‖(d/dt)^j [L(c+w+ti) − L(c+ti)]‖ ≤ 5 (j+1)! 2^{j+1} (1+|v|) / t^{j+1}`,

by the segment mean-value inequality and the all-order bound on `L^{(j+1)}`.  The logarithmic
height derivative of the two-ratio product of the product AFE is the difference of two such
increments, so it inherits the bound with constant `10`.
-/

noncomputable section

namespace RHTower

open Complex GaloisForLFunctions GaloisForLFunctions.HTGeometry RHTower.Sieve

/-! ## Local vertical-line jets -/

theorem analyticOnNhd_iteratedDeriv_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (n : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv n f) U := by
  induction n generalizing f with
  | zero => simpa using hf
  | succ n ih =>
    rw [iteratedDeriv_succ']
    exact ih hf.deriv

/-- **Local vertical-line jets**: `(d/ds)^n f(c + s i) = i^n f^{(n)}(c + s i)` at every point of
an open set of analyticity. -/
theorem iteratedDeriv_line_of_analyticOnNhd {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (c : ℂ) :
    ∀ (n : ℕ) (t : ℝ), c + (t : ℂ) * I ∈ U →
      iteratedDeriv n (fun s : ℝ => f (c + (s : ℂ) * I)) t
        = I ^ n * iteratedDeriv n f (c + (t : ℂ) * I) := by
  intro n
  induction n with
  | zero =>
    intro t _
    simp
  | succ n ih =>
    intro t ht
    have hcont : Continuous fun s : ℝ => c + (s : ℂ) * I := by fun_prop
    have hopen : IsOpen {s : ℝ | c + (s : ℂ) * I ∈ U} := hU.preimage hcont
    have hev : iteratedDeriv n (fun s : ℝ => f (c + (s : ℂ) * I))
        =ᶠ[nhds t] fun s : ℝ => I ^ n * iteratedDeriv n f (c + (s : ℂ) * I) := by
      filter_upwards [hopen.mem_nhds ht] with s hs
      exact ih s hs
    have hanal := analyticOnNhd_iteratedDeriv_of_analyticOnNhd hf n
    have hdiff : DifferentiableAt ℂ (iteratedDeriv n f) (c + (t : ℂ) * I) :=
      (hanal _ ht).differentiableAt
    have hchain : HasDerivAt (fun s : ℝ => iteratedDeriv n f (c + (s : ℂ) * I))
        (deriv (iteratedDeriv n f) (c + (t : ℂ) * I) * I) t := by
      have hinner : HasDerivAt (fun u : ℂ => c + u * I) I (t : ℂ) := by
        simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).const_add c
      exact (hdiff.hasDerivAt.comp (t : ℂ) hinner).comp_ofReal
    have hmul := hchain.const_mul (I ^ n)
    rw [iteratedDeriv_succ, hev.deriv_eq, hmul.deriv, iteratedDeriv_succ]
    ring

/-! ## Analyticity of `χ'/χ` on the two half-planes -/

theorem analyticAt_chiLogDerivClosed {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ chiLogDerivClosed z := by
  have h1 := analyticAt_halfDigamma hz
  have h2 := analyticAt_digamma_reflectHalf hz
  show AnalyticAt ℂ (fun w => -(Complex.digamma (w / 2) / 2)
    - Complex.digamma ((1 - w) / 2) / 2 + (Real.log Real.pi : ℂ)) z
  exact ((h1.div_const.neg).sub h2.div_const).add analyticAt_const

theorem analyticAt_logDeriv_zetaChi {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ (logDeriv zetaChi) z :=
  (analyticAt_chiLogDerivClosed hz).congr (logDeriv_zetaChi_eventuallyEq hz).symm

theorem isOpen_upperHalf : IsOpen {z : ℂ | 1 < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

theorem isOpen_lowerHalf : IsOpen {z : ℂ | z.im < -1} :=
  isOpen_lt Complex.continuous_im continuous_const

theorem analyticOnNhd_logDeriv_zetaChi_upper :
    AnalyticOnNhd ℂ (logDeriv zetaChi) {z : ℂ | 1 < z.im} := fun z hz =>
  analyticAt_logDeriv_zetaChi (by have : 1 < z.im := hz; linarith)

theorem analyticOnNhd_logDeriv_zetaChi_lower :
    AnalyticOnNhd ℂ (logDeriv zetaChi) {z : ℂ | z.im < -1} := fun z hz =>
  analyticAt_logDeriv_zetaChi (by have : z.im < -1 := hz; linarith)

/-! ## The increment and its jets -/

/-- The set `1 < |Im z|` on which `χ'/χ` is analytic. -/
def offAxisSet : Set ℂ := {z | 1 < |z.im|}

theorem isOpen_offAxisSet : IsOpen offAxisSet :=
  isOpen_lt continuous_const (Complex.continuous_im.abs)

theorem analyticOnNhd_logDeriv_zetaChi_offAxis :
    AnalyticOnNhd ℂ (logDeriv zetaChi) offAxisSet := fun z hz =>
  analyticAt_logDeriv_zetaChi (by
    have h : 1 < |z.im| := hz
    intro h0
    rw [h0, abs_zero] at h
    linarith)

/-- The increment of `χ'/χ` across the shift `w`, as a function of the complex variable. -/
def chiIncrementC (w z : ℂ) : ℂ := logDeriv zetaChi (z + w) - logDeriv zetaChi z

/-- The increment along the vertical line through `c`. -/
def chiIncrement (c w : ℂ) (t : ℝ) : ℂ := chiIncrementC w (c + (t : ℂ) * I)

/-- The open set where both endpoints of the shift are off the axis. -/
def shiftSet (w : ℂ) : Set ℂ := {z | 1 < |z.im| ∧ 1 < |(z + w).im|}

theorem isOpen_shiftSet (w : ℂ) : IsOpen (shiftSet w) :=
  (isOpen_lt continuous_const Complex.continuous_im.abs).inter
    (isOpen_lt continuous_const ((Complex.continuous_im.comp (continuous_id.add continuous_const)).abs))

theorem analyticAt_logDeriv_zetaChi_add {w z : ℂ} (hz : 1 < |(z + w).im|) :
    AnalyticAt ℂ (fun z => logDeriv zetaChi (z + w)) z := by
  have h := analyticAt_logDeriv_zetaChi (z := z + w) (by
    intro h0
    rw [h0, abs_zero] at hz
    linarith)
  exact AnalyticAt.comp (g := logDeriv zetaChi) (f := fun z => z + w) h
    (analyticAt_id.add analyticAt_const)

theorem analyticOnNhd_chiIncrementC (w : ℂ) : AnalyticOnNhd ℂ (chiIncrementC w) (shiftSet w) := by
  intro z hz
  have h1 := analyticAt_logDeriv_zetaChi_add hz.2
  have h2 := analyticAt_logDeriv_zetaChi (z := z) (by
    intro h0
    have := hz.1
    rw [h0, abs_zero] at this
    linarith)
  exact h1.sub h2

theorem iteratedDeriv_chiIncrementC (w : ℂ) (j : ℕ) {z : ℂ} (hz : z ∈ shiftSet w) :
    iteratedDeriv j (chiIncrementC w) z =
      iteratedDeriv j (logDeriv zetaChi) (z + w) - iteratedDeriv j (logDeriv zetaChi) z := by
  have h1 : ContDiffAt ℂ j (fun z => logDeriv zetaChi (z + w)) z :=
    (analyticAt_logDeriv_zetaChi_add hz.2).contDiffAt
  have h2 : ContDiffAt ℂ j (logDeriv zetaChi) z :=
    (analyticAt_logDeriv_zetaChi (z := z) (by
      intro h0
      have := hz.1
      rw [h0, abs_zero] at this
      linarith)).contDiffAt
  show iteratedDeriv j ((fun z => logDeriv zetaChi (z + w)) - logDeriv zetaChi) z = _
  rw [iteratedDeriv_sub h1 h2, congrFun (iteratedDeriv_comp_add_const j (logDeriv zetaChi) w) z]

/-- **Jets of the increment along a vertical line.** -/
theorem iteratedDeriv_chiIncrement_eq (c w : ℂ) (j : ℕ) {t : ℝ}
    (ht : c + (t : ℂ) * I ∈ shiftSet w) :
    iteratedDeriv j (chiIncrement c w) t =
      I ^ j * (iteratedDeriv j (logDeriv zetaChi) (c + (t : ℂ) * I + w)
        - iteratedDeriv j (logDeriv zetaChi) (c + (t : ℂ) * I)) := by
  unfold chiIncrement
  rw [iteratedDeriv_line_of_analyticOnNhd (isOpen_shiftSet w) (analyticOnNhd_chiIncrementC w) c j t ht,
    iteratedDeriv_chiIncrementC w j ht]

/-! ## The segment bound on the Levinson lines -/

/-- The Levinson shift `w = −(1 + i v)`. -/
def levinsonShift (v : ℝ) : ℂ := -(1 + (v : ℂ) * I)

theorem norm_levinsonShift_le (v : ℝ) : ‖levinsonShift v‖ ≤ 1 + |v| := by
  unfold levinsonShift
  rw [norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem levinsonShift_im (v : ℝ) : (levinsonShift v).im = -v := by
  simp [levinsonShift]

theorem levinsonShift_re (v : ℝ) : (levinsonShift v).re = -1 := by
  simp [levinsonShift]

/-- **Increment bound along a Levinson line**: for `1/4 ≤ σ₀ ≤ 1/2`, `|τ| ≥ 4`, `2|v| ≤ |τ|`,
`‖(d/dt)^j [L(σ₀+w+ti) − L(σ₀+ti)]‖ ≤ 5 (j+1)! 2^{j+1} (1+|v|)/|τ|^{j+1}` at `t = τ`. -/
theorem norm_iteratedDeriv_chiIncrement_le {σ₀ : ℝ} (hσ₁ : 1 / 4 ≤ σ₀) (hσ₂ : σ₀ ≤ 1 / 2)
    {v τ : ℝ} (hτ : 4 ≤ |τ|) (hv : 2 * |v| ≤ |τ|) (j : ℕ) :
    ‖iteratedDeriv j (chiIncrement (σ₀ : ℂ) (levinsonShift v)) τ‖
      ≤ 5 * (j + 1).factorial * 2 ^ (j + 1) * (1 + |v|) / |τ| ^ (j + 1) := by
  set z : ℂ := (σ₀ : ℂ) + (τ : ℂ) * I with hz
  set w : ℂ := levinsonShift v with hw
  have hzim : z.im = τ := by simp [hz]
  have hzre : z.re = σ₀ := by simp [hz]
  have hwim : (z + w).im = τ - v := by rw [Complex.add_im, hzim, hw, levinsonShift_im]; ring
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  -- membership in the shift set
  have hmem : z ∈ shiftSet w := by
    refine ⟨?_, ?_⟩
    · show 1 < |z.im|
      rw [hzim]; linarith
    · show 1 < |(z + w).im|
      rw [hwim]
      have h1 := abs_sub_abs_le_abs_sub τ v
      have h2 : |v| ≤ |τ| / 2 := by linarith
      linarith [abs_nonneg (τ - v)]
  rw [iteratedDeriv_chiIncrement_eq (σ₀ : ℂ) w j hmem, norm_mul, norm_pow, Complex.norm_I, one_pow,
    one_mul]
  -- segment points
  have hseg : ∀ θ ∈ Set.Icc (0 : ℝ) 1, |(z + (θ : ℂ) * ((z + w) - z)).im| ≥ |τ| / 2 := by
    intro θ hθ
    have him : (z + (θ : ℂ) * ((z + w) - z)).im = τ - θ * v := by
      simp only [add_sub_cancel_left, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, hzim, hw, levinsonShift_im, levinsonShift_re, zero_mul]
      ring
    rw [him]
    have h1 := abs_sub_abs_le_abs_sub τ (θ * v)
    have h2 : |θ * v| ≤ |v| := by
      rw [abs_mul, abs_of_nonneg hθ.1]
      exact mul_le_of_le_one_left (abs_nonneg v) hθ.2
    linarith
  have hsegre : ∀ θ ∈ Set.Icc (0 : ℝ) 1, (z + (θ : ℂ) * ((z + w) - z)).re = σ₀ - θ := by
    intro θ _
    simp only [add_sub_cancel_left, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hzre, hw, levinsonShift_re, levinsonShift_im, zero_mul, sub_zero]
    ring
  have hM : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv (iteratedDeriv j (logDeriv zetaChi)) (z + (θ : ℂ) * ((z + w) - z))‖
        ≤ 5 * (j + 1).factorial / (|τ| / 2) ^ (j + 1) := by
    intro θ hθ
    rw [← iteratedDeriv_succ]
    have hre₁ : -2 < (z + (θ : ℂ) * ((z + w) - z)).re := by rw [hsegre θ hθ]; linarith [hθ.2]
    have hre₂ : (z + (θ : ℂ) * ((z + w) - z)).re < 3 := by rw [hsegre θ hθ]; linarith [hθ.1]
    have him2 : 2 ≤ |(z + (θ : ℂ) * ((z + w) - z)).im| := by linarith [hseg θ hθ]
    refine (norm_iteratedDeriv_logDeriv_zetaChi_le (by omega) hre₁ hre₂ him2).trans ?_
    have hf : (0 : ℝ) ≤ 5 * (j + 1).factorial := by positivity
    exact div_le_div_of_nonneg_left hf (by positivity)
      (pow_le_pow_left₀ (by positivity) (hseg θ hθ) _)
  have hdiff : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℂ (iteratedDeriv j (logDeriv zetaChi)) (z + (θ : ℂ) * ((z + w) - z)) := by
    intro θ hθ
    have hmemV : z + (θ : ℂ) * ((z + w) - z) ∈ offAxisSet := by
      show 1 < |(z + (θ : ℂ) * ((z + w) - z)).im|
      linarith [hseg θ hθ]
    exact ((analyticOnNhd_iteratedDeriv_of_analyticOnNhd analyticOnNhd_logDeriv_zetaChi_offAxis j)
      _ hmemV).differentiableAt
  have hsegbound := norm_sub_le_segment hdiff hM
  rw [add_sub_cancel_left] at hsegbound
  refine hsegbound.trans ?_
  have hwn := norm_levinsonShift_le v
  have hpow : (|τ| / 2) ^ (j + 1) = |τ| ^ (j + 1) / 2 ^ (j + 1) := div_pow _ _ _
  rw [hpow]
  have hM0 : (0 : ℝ) ≤ 5 * (j + 1).factorial / (|τ| ^ (j + 1) / 2 ^ (j + 1)) := by positivity
  calc 5 * (j + 1).factorial / (|τ| ^ (j + 1) / 2 ^ (j + 1)) * ‖w‖
      ≤ 5 * (j + 1).factorial / (|τ| ^ (j + 1) / 2 ^ (j + 1)) * (1 + |v|) :=
        mul_le_mul_of_nonneg_left hwn hM0
    _ = 5 * (j + 1).factorial * 2 ^ (j + 1) * (1 + |v|) / |τ| ^ (j + 1) := by
        field_simp

/-! ## The logarithmic height derivative of the two-ratio product -/

theorem contDiffAt_chiIncrement {c w : ℂ} {t : ℝ} (ht : c + (t : ℂ) * I ∈ shiftSet w) (n : ℕ) :
    ContDiffAt ℝ n (chiIncrement c w) t := by
  have hline : AnalyticAt ℝ (fun s : ℝ => c + (s : ℂ) * I) t :=
    analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  have hC : AnalyticAt ℝ (chiIncrementC w) (c + (t : ℂ) * I) :=
    ((analyticOnNhd_chiIncrementC w) _ ht).restrictScalars
  exact (AnalyticAt.comp (g := chiIncrementC w) (f := fun s : ℝ => c + (s : ℂ) * I) hC
    hline).contDiffAt

theorem levinsonLine_mem_shiftSet {σ₀ v τ : ℝ} (hτ : 4 ≤ |τ|) (hv : 2 * |v| ≤ |τ|) :
    (σ₀ : ℂ) + (τ : ℂ) * I ∈ shiftSet (levinsonShift v) := by
  refine ⟨?_, ?_⟩
  · show 1 < |((σ₀ : ℂ) + (τ : ℂ) * I).im|
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    linarith
  · show 1 < |((σ₀ : ℂ) + (τ : ℂ) * I + levinsonShift v).im|
    have him : ((σ₀ : ℂ) + (τ : ℂ) * I + levinsonShift v).im = τ - v := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, zero_add, levinsonShift_im]
      ring
    rw [him]
    have h1 := abs_sub_abs_le_abs_sub τ v
    linarith

/-- `D(t) = i·[L(σ₀+w+ti) − L(σ₀+ti)] − i·[L(σ₀+w−ti) − L(σ₀−ti)]`, the logarithmic height
derivative of the two-ratio product `χ(s₁+w)χ(s₂+w)/(χ(s₁)χ(s₂))` with `s₁ = σ₀+it`, `s₂ = σ₀−it`. -/
def chiIncrementDifference (σ₀ v : ℝ) (t : ℝ) : ℂ :=
  I * chiIncrement (σ₀ : ℂ) (levinsonShift v) t - I * chiIncrement (σ₀ : ℂ) (levinsonShift v) (-t)

/-- **All-order bound for `D`**: for `1/4 ≤ σ₀ ≤ 1/2`, `t ≥ 4`, `2|v| ≤ t`,
`‖D^{(j)}(t)‖ ≤ 10 (j+1)! 2^{j+1} (1+|v|)/t^{j+1}`. -/
theorem norm_iteratedDeriv_chiIncrementDifference_le {σ₀ : ℝ} (hσ₁ : 1 / 4 ≤ σ₀)
    (hσ₂ : σ₀ ≤ 1 / 2) {v t : ℝ} (ht : 4 ≤ t) (hv : 2 * |v| ≤ t) (j : ℕ) :
    ‖iteratedDeriv j (chiIncrementDifference σ₀ v) t‖
      ≤ 10 * (j + 1).factorial * 2 ^ (j + 1) * (1 + |v|) / t ^ (j + 1) := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hτ : 4 ≤ |t| := by rw [abs_of_nonneg ht0]; exact ht
  have hτ' : 4 ≤ |-t| := by rw [abs_neg]; exact hτ
  have hv' : 2 * |v| ≤ |t| := by rw [abs_of_nonneg ht0]; exact hv
  have hv'' : 2 * |v| ≤ |-t| := by rw [abs_neg]; exact hv'
  have hA : ContDiffAt ℝ j (chiIncrement (σ₀ : ℂ) (levinsonShift v)) t :=
    contDiffAt_chiIncrement (levinsonLine_mem_shiftSet hτ hv') j
  have hA' : ContDiffAt ℝ j (chiIncrement (σ₀ : ℂ) (levinsonShift v)) (-t) :=
    contDiffAt_chiIncrement (by
      have := levinsonLine_mem_shiftSet (σ₀ := σ₀) hτ' hv''
      simpa using this) j
  have hB : ContDiffAt ℝ j (fun s : ℝ => chiIncrement (σ₀ : ℂ) (levinsonShift v) (-s)) t :=
    hA'.comp t contDiffAt_id.neg
  have hfun : chiIncrementDifference σ₀ v =
      (fun s : ℝ => I * chiIncrement (σ₀ : ℂ) (levinsonShift v) s) -
        fun s : ℝ => I * chiIncrement (σ₀ : ℂ) (levinsonShift v) (-s) := rfl
  have e1 : iteratedDeriv j (fun s : ℝ => I * chiIncrement (σ₀ : ℂ) (levinsonShift v) s) t
      = I * iteratedDeriv j (chiIncrement (σ₀ : ℂ) (levinsonShift v)) t :=
    iteratedDeriv_const_mul I hA
  have e2 : iteratedDeriv j (fun s : ℝ => I * chiIncrement (σ₀ : ℂ) (levinsonShift v) (-s)) t
      = I * iteratedDeriv j (fun s : ℝ => chiIncrement (σ₀ : ℂ) (levinsonShift v) (-s)) t :=
    iteratedDeriv_const_mul I hB
  rw [hfun, iteratedDeriv_sub (contDiffAt_const.mul hA) (contDiffAt_const.mul hB), e1, e2,
    iteratedDeriv_comp_neg]
  have h1 := norm_iteratedDeriv_chiIncrement_le hσ₁ hσ₂ hτ hv' j
  have h2 := norm_iteratedDeriv_chiIncrement_le hσ₁ hσ₂ hτ' hv'' j
  rw [abs_of_nonneg ht0] at h1
  rw [abs_neg, abs_of_nonneg ht0] at h2
  have hn1 : ‖I * iteratedDeriv j (chiIncrement (σ₀ : ℂ) (levinsonShift v)) t‖
      = ‖iteratedDeriv j (chiIncrement (σ₀ : ℂ) (levinsonShift v)) t‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have hn2 : ‖I * ((-1 : ℝ) ^ j • iteratedDeriv j (chiIncrement (σ₀ : ℂ) (levinsonShift v)) (-t))‖
      = ‖iteratedDeriv j (chiIncrement (σ₀ : ℂ) (levinsonShift v)) (-t)‖ := by
    rw [norm_mul, Complex.norm_I, one_mul, norm_smul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
  refine (norm_sub_le _ _).trans ?_
  rw [hn1, hn2]
  calc ‖iteratedDeriv j (chiIncrement (σ₀ : ℂ) (levinsonShift v)) t‖
        + ‖iteratedDeriv j (chiIncrement (σ₀ : ℂ) (levinsonShift v)) (-t)‖
      ≤ 5 * (j + 1).factorial * 2 ^ (j + 1) * (1 + |v|) / t ^ (j + 1)
        + 5 * (j + 1).factorial * 2 ^ (j + 1) * (1 + |v|) / t ^ (j + 1) := add_le_add h1 h2
    _ = 10 * (j + 1).factorial * 2 ^ (j + 1) * (1 + |v|) / t ^ (j + 1) := by ring

end RHTower

end
