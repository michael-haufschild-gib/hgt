import GaloisForLFunctions.RHTower.ArithmeticRemainderLinearCutoff

/-!
# Signed Fourier orientation at the unit anchor

Integration by parts turns the actual anchored logarithmic sine integral into a strictly
positive integral of `reciprocalLogDissipation * (1 - cos phase)`. The phase derivative must
stay positive from the anchor onward. Total dissipation is the initial reciprocal weight.

For the literal Bernoulli unit source at nonnegative height, every positive frequency has
positive imaginary part. A negative frequency has negative imaginary part when its absolute
frequency exceeds the height. The excluded stationary frequencies form an explicit finite set.
The exact summation theorem retains both sectors and the negative Bernoulli mean; their combined
orientation, and RH, remain open. No zeta-zero premise or numerical certificate is used.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
namespace RHTower.DeletionMixedRefinement

/-- The actual logarithmic phase, with its value at the positive anchor removed. -/
def anchoredLogPhase (a γ ω x : ℝ) : ℝ := ω*(x-a)+γ*(Real.log x-Real.log a)
/-- The power amplitude divided by the logarithmic phase derivative. -/
def reciprocalLogWeight (β γ ω x : ℝ) : ℝ := x^(1-β)/(ω*x+γ)
/-- The negative derivative of the reciprocal phase weight. -/
def reciprocalLogDissipation (β γ ω x : ℝ) : ℝ :=
  x^(-β)*((β-1)*(ω*x+γ)+ω*x)/(ω*x+γ)^2

/-- The nonstationary denominator stays positive beyond the anchor. -/
theorem logPhase_den_pos {a γ ω : ℝ} (hω : 0 < ω) (hd : 0 < ω*a+γ)
    {x : ℝ} (hx : a ≤ x) : 0 < ω*x+γ := by nlinarith

/-- Derivative of the anchored logarithmic clock. -/
theorem hasDerivAt_anchoredLogPhase {a γ ω x : ℝ} (hx : 0 < x) :
    HasDerivAt (anchoredLogPhase a γ ω) (ω+γ/x) x := by
  unfold anchoredLogPhase
  convert! (((hasDerivAt_id x).sub_const a).const_mul ω).add
    (((Real.hasDerivAt_log hx.ne').sub_const (Real.log a)).const_mul γ) using 1
  ring

/-- Exact derivative with the original power amplitude retained. -/
theorem hasDerivAt_reciprocalLogWeight {β γ ω x : ℝ} (hx : 0 < x) (hd : ω*x+γ ≠ 0) :
    HasDerivAt (reciprocalLogWeight β γ ω) (-reciprocalLogDissipation β γ ω x) x := by
  have hp := Real.hasDerivAt_rpow_const (p := 1-β) (Or.inl hx.ne')
  have hq := (((hasDerivAt_id x).const_mul ω).add_const γ)
  convert! hp.div hq hd using 1
  dsimp only [reciprocalLogDissipation, id, mul_one]
  rw [show 1-β-1 = -β by ring]
  have he : x^(1-β) = x*x^(-β) := by
    calc
      x^(1-β) = x^(1+(-β)) := by congr 1
      _ = x^1*x^(-β) := Real.rpow_add hx _ _
      _ = x*x^(-β) := by rw [Real.rpow_one]
  rw [he]
  field_simp [hd]
  ring

/-- Strictly positive dissipation density on the complete half-line. -/
theorem reciprocalLogDissipation_pos {a β γ ω x : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hω : 0 < ω) (hd : 0 < ω*a+γ) (hx : a ≤ x) :
    0 < reciprocalLogDissipation β γ ω x := by
  have hx0 := ha.trans_le hx
  have hdx := logPhase_den_pos hω hd hx
  unfold reciprocalLogDissipation
  positivity

/-- The reciprocal phase weight vanishes at infinity. -/
theorem tendsto_reciprocalLogWeight {a β γ ω : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hω : 0 < ω) (hd : 0 < ω*a+γ) :
    Tendsto (reciprocalLogWeight β γ ω) atTop (𝓝 0) := by
  have hp := (tendsto_rpow_neg_atTop (by linarith : 0 < β-1)).div_const (ω*a+γ)
  have he : -(β-1) = 1-β := by ring
  rw [he, zero_div] at hp
  apply squeeze_zero' ?_ ?_ hp
  · filter_upwards [eventually_ge_atTop a] with x hx
    exact div_nonneg (Real.rpow_nonneg (ha.trans_le hx).le _) (logPhase_den_pos hω hd hx).le
  · filter_upwards [eventually_ge_atTop a] with x hx
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg (ha.trans_le hx).le _) hd (by nlinarith)

/-- Monotonicity and the finite endpoint limit give absolute integrability. -/
theorem integrable_reciprocalLogDissipation {a β γ ω : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hω : 0 < ω) (hd : 0 < ω*a+γ) :
    IntegrableOn (reciprocalLogDissipation β γ ω) (Ioi a) := by
  have hi := integrableOn_Ioi_deriv_of_nonpos'
    (fun x (hx : x ∈ Ici a) => hasDerivAt_reciprocalLogWeight (ha.trans_le hx)
      (logPhase_den_pos hω hd hx).ne')
    (fun x (hx : x ∈ Ioi a) => (neg_neg_of_pos (reciprocalLogDissipation_pos ha hβ hω hd hx.le)).le)
    (tendsto_reciprocalLogWeight ha hβ hω hd)
  exact integrable_neg_iff.mp hi

/-- Continuity of the anchored clock on its positive half-line. -/
theorem continuousOn_anchoredLogPhase {a γ ω : ℝ} (ha : 0 < a) :
    ContinuousOn (anchoredLogPhase a γ ω) (Ioi a) := by
  intro x hx
  exact (hasDerivAt_anchoredLogPhase (ha.trans hx)).continuousAt.continuousWithinAt

/-- The literal power amplitude dominates the sine integrand. -/
theorem integrable_anchoredLogSine {a β γ ω : ℝ} (ha : 0 < a) (hβ : 1 < β) :
    IntegrableOn (fun x => x^(-β)*Real.sin (anchoredLogPhase a γ ω x)) (Ioi a) := by
  apply (integrableOn_Ioi_rpow_of_lt (by linarith : -β < -1) ha).mul_bdd (c := 1)
    ((Real.continuous_sin.comp_continuousOn (continuousOn_anchoredLogPhase ha)).aestronglyMeasurable measurableSet_Ioi)
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, Function.comp_apply] using Real.abs_sin_le_one _)

/-- Integrability of the positive budget, whose trigonometric factor is bounded by two. -/
theorem integrable_reciprocalLogBudget {a β γ ω : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hω : 0 < ω) (hd : 0 < ω*a+γ) :
    IntegrableOn (fun x => reciprocalLogDissipation β γ ω x *
      (1-Real.cos (anchoredLogPhase a γ ω x))) (Ioi a) := by
  apply (integrable_reciprocalLogDissipation ha hβ hω hd).mul_bdd (c := 2)
    ((continuousOn_const.sub (Real.continuous_cos.comp_continuousOn (continuousOn_anchoredLogPhase ha))).aestronglyMeasurable measurableSet_Ioi)
  apply ae_of_all
  intro x
  dsimp only [Pi.sub_apply, Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
  linarith [Real.neg_one_le_cos (anchoredLogPhase a γ ω x)]

/-- The phase derivative recovers the literal amplitude. -/
theorem reciprocalLogWeight_mul_phase_deriv {β γ ω x : ℝ} (hx : 0 < x)
    (hd : ω*x+γ ≠ 0) : reciprocalLogWeight β γ ω x * (ω+γ/x) = x^(-β) := by
  have he : x^(1-β) = x*x^(-β) := by
    calc
      x^(1-β) = x^(1+(-β)) := by congr 1
      _ = x^1*x^(-β) := Real.rpow_add hx _ _
      _ = x*x^(-β) := by rw [Real.rpow_one]
  unfold reciprocalLogWeight
  rw [he]
  have heq : ω+γ/x = (ω*x+γ)/x := by field_simp
  rw [heq]
  field_simp [hd, hx.ne']
  simpa only [mul_comm] using div_self hd

/-- The boundary product in integration by parts vanishes at infinity. -/
theorem tendsto_reciprocalLogBoundary {a β γ ω : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hω : 0 < ω) (hd : 0 < ω*a+γ) :
    Tendsto (fun x => reciprocalLogWeight β γ ω x *
      (1-Real.cos (anchoredLogPhase a γ ω x))) atTop (𝓝 0) := by
  have ht := (tendsto_reciprocalLogWeight ha hβ hω hd).mul_const 2
  rw [zero_mul] at ht
  apply squeeze_zero' ?_ ?_ ht
  · filter_upwards [eventually_ge_atTop a] with x hx
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg (ha.trans_le hx).le _)
      (logPhase_den_pos hω hd hx).le) (sub_nonneg.mpr (Real.cos_le_one _))
  · filter_upwards [eventually_ge_atTop a] with x hx
    apply mul_le_mul_of_nonneg_left
    · linarith [Real.neg_one_le_cos (anchoredLogPhase a γ ω x)]
    · exact div_nonneg (Real.rpow_nonneg (ha.trans_le hx).le _) (logPhase_den_pos hω hd hx).le

/-- Exact positive-budget identity for every nonstationary anchored logarithmic mode. -/
theorem integral_anchoredLogSine_eq_budget {a β γ ω : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hω : 0 < ω) (hd : 0 < ω*a+γ) :
    (∫ x in Ioi a, x^(-β)*Real.sin (anchoredLogPhase a γ ω x)) =
    ∫ x in Ioi a, reciprocalLogDissipation β γ ω x *
      (1-Real.cos (anchoredLogPhase a γ ω x)) := by
  have hv (x : ℝ) (hx : x ∈ Ioi a) :
      HasDerivAt (fun x => 1-Real.cos (anchoredLogPhase a γ ω x))
        ((ω+γ/x)*Real.sin (anchoredLogPhase a γ ω x)) x := by
    convert! ((hasDerivAt_anchoredLogPhase (ha.trans hx)).cos).const_sub 1 using 1
    ring
  have he (x : ℝ) (hx : x ∈ Ioi a) :
      reciprocalLogWeight β γ ω x * ((ω+γ/x)*Real.sin (anchoredLogPhase a γ ω x)) =
      x^(-β)*Real.sin (anchoredLogPhase a γ ω x) := by
    rw [← mul_assoc, reciprocalLogWeight_mul_phase_deriv (ha.trans hx)
      (logPhase_den_pos hω hd hx.le).ne']
  have hb : Tendsto (fun x => reciprocalLogWeight β γ ω x *
      (1-Real.cos (anchoredLogPhase a γ ω x))) (𝓝[>] a) (𝓝 0) := by
    have hc : ContinuousAt (fun x => reciprocalLogWeight β γ ω x *
        (1-Real.cos (anchoredLogPhase a γ ω x))) a :=
      (hasDerivAt_reciprocalLogWeight ha hd.ne').continuousAt.mul
      (continuousAt_const.sub (Real.continuous_cos.continuousAt.comp (hasDerivAt_anchoredLogPhase ha).continuousAt))
    simpa [anchoredLogPhase] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hi := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x (hx : x ∈ Ioi a) => hasDerivAt_reciprocalLogWeight (ha.trans hx)
      (logPhase_den_pos hω hd hx.le).ne') hv
    ((integrable_anchoredLogSine ha hβ).congr_fun (fun x hx => (he x hx).symm) measurableSet_Ioi)
    ((integrable_reciprocalLogBudget ha hβ hω hd).neg.congr_fun
      (fun x _ => by simp) measurableSet_Ioi) hb
    (tendsto_reciprocalLogBoundary ha hβ hω hd)
  rw [setIntegral_congr_fun measurableSet_Ioi he] at hi
  simpa only [neg_mul, integral_neg, sub_self, zero_sub, neg_neg] using hi

/-- Continuity of the dissipation density on the nonstationary region. -/
theorem continuousOn_reciprocalLogDissipation {a β γ ω : ℝ} (ha : 0 < a)
    (hω : 0 < ω) (hd : 0 < ω*a+γ) :
    ContinuousOn (reciprocalLogDissipation β γ ω) (Ioi a) := by
  intro x hx
  unfold reciprocalLogDissipation
  have hp := (Real.hasDerivAt_rpow_const (p := -β) (Or.inl (ha.trans hx).ne')).continuousAt
  exact (hp.mul ((continuousAt_const.mul
    ((continuousAt_const.mul continuousAt_id).add continuousAt_const)).add
    (continuousAt_const.mul continuousAt_id))).div
    (((continuousAt_const.mul continuousAt_id).add continuousAt_const).pow 2)
    (pow_ne_zero _ (logPhase_den_pos hω hd hx.le).ne') |>.continuousWithinAt

/-- Strict orientation from the nonzero phase derivative near the anchor. -/
theorem integral_anchoredLogSine_pos {a β γ ω : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hω : 0 < ω) (hd : 0 < ω*a+γ) :
    0 < ∫ x in Ioi a, x^(-β)*Real.sin (anchoredLogPhase a γ ω x) := by
  rw [integral_anchoredLogSine_eq_budget ha hβ hω hd]
  have hn : ∀ᵐ x ∂volume.restrict (Ioi a), 0 ≤ reciprocalLogDissipation β γ ω x *
      (1-Real.cos (anchoredLogPhase a γ ω x)) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ (fun x hx => mul_nonneg
      (reciprocalLogDissipation_pos ha hβ hω hd hx.le).le (sub_nonneg.mpr (Real.cos_le_one _)))
  rw [setIntegral_pos_iff_support_of_nonneg_ae hn (integrable_reciprocalLogBudget ha hβ hω hd)]
  have hc : ContinuousOn (fun x => reciprocalLogDissipation β γ ω x *
      (1-Real.cos (anchoredLogPhase a γ ω x))) (Ioi a) :=
    (continuousOn_reciprocalLogDissipation ha hω hd).mul
    (continuousOn_const.sub (Real.continuous_cos.comp_continuousOn (continuousOn_anchoredLogPhase ha)))
  have ho := hc.isOpen_inter_preimage isOpen_Ioi (isClosed_singleton (x := (0 : ℝ))).isOpen_compl
  rw [Set.inter_comm] at ho
  apply ho.measure_pos volume
  have hder : Real.cos (anchoredLogPhase a γ ω a) * (ω+γ/a) ≠ 0 := by
    simp only [anchoredLogPhase, sub_self, mul_zero, add_zero, Real.cos_zero, one_mul]
    have he : ω+γ/a = (ω*a+γ)/a := by field_simp
    rw [he]
    exact (div_pos hd ha).ne'
  have hne := ((hasDerivAt_anchoredLogPhase (a := a) (γ := γ) (ω := ω) ha).sin).eventually_ne (c := 0) hder
  have hf : 𝓝[>] a ≤ 𝓝[≠] a := nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
  obtain ⟨x, hx, hsx⟩ := ((eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] a, x ∈ Ioi a).and (hne.filter_mono hf)).exists
  have hcos : Real.cos (anchoredLogPhase a γ ω x) < 1 := by
    apply lt_of_le_of_ne (Real.cos_le_one _)
    intro he
    have hs := Real.sin_sq_add_cos_sq (anchoredLogPhase a γ ω x)
    rw [he] at hs
    have hz : Real.sin (anchoredLogPhase a γ ω x) = 0 := by nlinarith [sq_nonneg (Real.sin (anchoredLogPhase a γ ω x))]
    exact hsx hz
  exact ⟨x, (mul_pos (reciprocalLogDissipation_pos ha hβ hω hd hx.le) (sub_pos.mpr hcos)).ne', hx⟩

/-- Total dissipation equals the initial reciprocal phase weight. -/
theorem integral_reciprocalLogDissipation {a β γ ω : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hω : 0 < ω) (hd : 0 < ω*a+γ) :
    (∫ x in Ioi a, reciprocalLogDissipation β γ ω x) = reciprocalLogWeight β γ ω a := by
  have hi := integral_Ioi_of_hasDerivAt_of_nonpos'
    (fun x (hx : x ∈ Ici a) => hasDerivAt_reciprocalLogWeight (β := β) (ha.trans_le hx)
      (logPhase_den_pos hω hd hx).ne')
    (fun x (hx : x ∈ Ioi a) => (neg_neg_of_pos (reciprocalLogDissipation_pos ha hβ hω hd hx.le)).le)
    (tendsto_reciprocalLogWeight ha hβ hω hd)
  simpa only [integral_neg, zero_sub, neg_inj] using hi

/-- The positive sine integral is bounded by twice the initial reciprocal phase weight. -/
theorem integral_anchoredLogSine_le {a β γ ω : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hω : 0 < ω) (hd : 0 < ω*a+γ) :
    (∫ x in Ioi a, x^(-β)*Real.sin (anchoredLogPhase a γ ω x)) ≤
      2 * reciprocalLogWeight β γ ω a := by
  rw [integral_anchoredLogSine_eq_budget ha hβ hω hd,
    ← integral_reciprocalLogDissipation ha hβ hω hd, ← integral_const_mul]
  apply setIntegral_mono_on (integrable_reciprocalLogBudget ha hβ hω hd)
    ((integrable_reciprocalLogDissipation ha hβ hω hd).const_mul 2) measurableSet_Ioi
  intro x hx
  have hn := (reciprocalLogDissipation_pos ha hβ hω hd hx.le).le
  nlinarith [Real.neg_one_le_cos (anchoredLogPhase a γ ω x)]

/-- The imaginary part is the actual power-weighted logarithmic sine. -/
theorem logarithmicFourierMode_im (β γ ω x : ℝ) :
    (logarithmicFourierMode β γ ω x).im = x^(-β)*Real.sin (ω*x+γ*Real.log x) := by
  simp only [logarithmicFourierMode, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]

/-- Integer frequency removes precisely the phase at the unit anchor. -/
theorem unit_logarithmicFourierMode_im_eq {β γ : ℝ} (hβ : 1 < β) (k : ℤ) :
    (∫ x in Ioi 1, logarithmicFourierMode β γ (2*Real.pi*k) x).im =
    ∫ x in Ioi 1, x^(-β)*Real.sin (anchoredLogPhase 1 γ (2*Real.pi*k) x) := by
  have hi : (∫ x in Ioi 1, (logarithmicFourierMode β γ (2*Real.pi*k) x).im) =
      (∫ x in Ioi 1, logarithmicFourierMode β γ (2*Real.pi*k) x).im :=
    integral_im (integrable_logarithmicFourierMode zero_lt_one hβ γ _)
  rw [← hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only
  rw [logarithmicFourierMode_im]
  congr 1
  have he : 2*Real.pi*(k:ℝ)*x+γ*Real.log x =
      anchoredLogPhase 1 γ (2*Real.pi*k) x + (k:ℝ)*(2*Real.pi) := by
    simp only [anchoredLogPhase, Real.log_one, sub_zero]
    ring
  rw [he, Real.sin_add_int_mul_two_pi]

/-- Strict unit orientation when the anchored phase derivative is positive. -/
theorem unit_logarithmicFourierMode_im_pos {β γ : ℝ} (hβ : 1 < β) {k : ℤ}
    (hk : 0 < k) (hd : 0 < 2*Real.pi*k+γ) :
    0 < (∫ x in Ioi 1, logarithmicFourierMode β γ (2*Real.pi*k) x).im := by
  rw [unit_logarithmicFourierMode_im_eq hβ k]
  exact integral_anchoredLogSine_pos zero_lt_one hβ (by positivity) (by simpa using hd)

/-- Negative frequencies are conjugate to opposite-height positive modes. -/
theorem unit_logarithmicFourierMode_neg_im_neg {β γ : ℝ} (hβ : 1 < β) {k : ℤ}
    (hk : 0 < k) (hd : 0 < 2*Real.pi*k-γ) :
    (∫ x in Ioi 1, logarithmicFourierMode β γ (2*Real.pi*(-k)) x).im < 0 := by
  have hp := unit_logarithmicFourierMode_im_pos hβ hk (γ := -γ) (by simpa using hd)
  have he (x : ℝ) : logarithmicFourierMode β γ (2*Real.pi*(-k)) x =
      star (logarithmicFourierMode β (-γ) (2*Real.pi*k) x) := by
    simpa only [neg_neg, Int.cast_neg, mul_neg] using logarithmicFourierMode_neg β (-γ) (2*Real.pi*k) x
  simp_rw [he, Complex.star_def, integral_conj, Complex.conj_im]
  exact neg_neg_of_pos hp

/-- The actual Bernoulli coefficient multiplies the literal mode integral. -/
theorem unit_bernoulliFourierTerm_im_eq_mode (s : ℂ) (k : ℤ) :
    (∫ x in Ioi 1, bernoulliFourierTerm k s x).im = bernoulliModeWeight k *
      (∫ x in Ioi 1, logarithmicFourierMode (s.re+2) (-s.im) (2*Real.pi*k) x).im := by
  have he : (∫ x in Ioi 1, bernoulliFourierTerm k s x) =
      (bernoulliModeWeight k : ℂ) *
        ∫ x in Ioi 1, logarithmicFourierMode (s.re+2) (-s.im) (2*Real.pi*k) x := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [bernoulliFourierTerm, fourier_mul_cpow_eq_mode k s (zero_lt_one.trans hx)]
  rw [he]
  simp

/-- Every nonzero Bernoulli Fourier coefficient is strictly positive. -/
theorem bernoulliModeWeight_pos {k : ℤ} (hk : k ≠ 0) : 0 < bernoulliModeWeight k := by
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  unfold bernoulliModeWeight
  positivity

/-- Every positive-frequency unit term is strictly positive at nonnegative height. -/
theorem unit_bernoulliFourierTerm_pos_im_pos {s : ℂ} (hs : 0 < s.re) (ht : 0 ≤ s.im)
    {k : ℤ} (hk : 0 < k) :
    0 < (∫ x in Ioi 1, bernoulliFourierTerm k (star s) x).im := by
  rw [unit_bernoulliFourierTerm_im_eq_mode]
  apply mul_pos (bernoulliModeWeight_pos hk.ne')
  apply unit_logarithmicFourierMode_im_pos (by simpa using (show 1 < s.re+2 by linarith)) hk
  simp only [Complex.star_def, Complex.conj_im, neg_neg]
  have hw : 0 < 2*Real.pi*(k:ℝ) := by positivity
  linarith

/-- A negative-frequency unit term is strictly negative when its frequency exceeds the height. -/
theorem unit_bernoulliFourierTerm_neg_im_neg {s : ℂ} (hs : 0 < s.re)
    {k : ℤ} (hk : 0 < k) (ht : s.im < 2*Real.pi*k) :
    (∫ x in Ioi 1, bernoulliFourierTerm (-k) (star s) x).im < 0 := by
  rw [unit_bernoulliFourierTerm_im_eq_mode]
  apply mul_neg_of_pos_of_neg (bernoulliModeWeight_pos (neg_ne_zero.mpr hk.ne'))
  simp only [Int.cast_neg]
  apply unit_logarithmicFourierMode_neg_im_neg (by simpa using (show 1 < s.re+2 by linarith)) hk
  simpa only [Complex.star_def, Complex.conj_im, neg_neg] using sub_pos.mpr ht

/-- The complete unit source retains both frequency sectors and its exact mean. -/
theorem hasSum_unit_bernoulliFourierTerm {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    HasSum (fun k : ℤ => ∫ x in Ioi 1, bernoulliFourierTerm k (star s) x)
      (normalizedWeightedRemainder s 1 + 1/(12*(star s+1))) := by
  have hs' : -1 < (star s).re := by simpa using (show -1 < s.re by linarith)
  have h := hasSum_integral_bernoulliFourierTerm zero_lt_one hs'
  have hc := centeredBernoulliTail_eq_sub_mean hs' (N := 1) (by rfl)
  have hg := normalizedWeightedRemainder_scaled_eq_tail hs hs1 (N := 1) (by rfl)
  simp only [Nat.cast_one, Real.one_rpow, Complex.ofReal_one, mul_one,
    Complex.one_cpow] at hc hg
  rw [← hg] at hc
  exact hc ▸ h

/-- Exact signed unit budget; separate mode signs do not decide this sum. -/
theorem hasSum_unit_bernoulliFourierTerm_im {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    HasSum (fun k : ℤ => (∫ x in Ioi 1, bernoulliFourierTerm k (star s) x).im)
      ((normalizedWeightedRemainder s 1).im + s.im/(12*Complex.normSq (s+1))) := by
  have hc : (1/(12*(star s+1))).im = s.im/(12*Complex.normSq (s+1)) := by
    rw [show (1:ℂ)/(12*(star s+1)) = (star s+1)⁻¹/12 by simp only [mul_inv_rev, div_eq_mul_inv, one_mul]]
    simp only [Complex.div_ofNat_im, Complex.inv_im, Complex.add_im, Complex.star_def,
      Complex.conj_im, Complex.one_im, add_zero, neg_neg]
    have he : Complex.normSq ((starRingEnd ℂ) s+1) = Complex.normSq (s+1) := by
      simp [Complex.normSq_apply]
    rw [he]
    ring
  simpa only [Complex.add_im, hc] using (Complex.hasSum_im (hasSum_unit_bernoulliFourierTerm hs hs1))

/-- The negative mode has a stationary point on the closed unit half-line exactly at this threshold. -/
theorem unit_negativeMode_stationary_iff {t : ℝ} {k : ℤ} (hk : 0 < k) :
    (∃ x : ℝ, 1 ≤ x ∧ -(2*Real.pi*k)+t/x = 0) ↔ 2*Real.pi*k ≤ t := by
  have hw : 0 < 2*Real.pi*(k:ℝ) := by positivity
  constructor
  · rintro ⟨x, hx, he⟩
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have htx : t = (2*Real.pi*(k:ℝ))*x := by
      apply (div_eq_iff hx0.ne').mp
      linarith
    rw [htx]
    nlinarith
  · intro ht
    refine ⟨t/(2*Real.pi*k), (le_div_iff₀ hw).mpr (by simpa using ht), ?_⟩
    have ht0 : 0 < t := hw.trans_le ht
    rw [div_div_cancel₀ ht0.ne']
    ring

/-- Only finitely many frequencies have stationary or boundary-stationary unit modes. -/
theorem unit_stationaryFrequencies_finite (t : ℝ) :
    Set.Finite {k : ℤ | 0 < k ∧ 2*Real.pi*k ≤ t} := by
  apply (Set.finite_Icc (1:ℤ) ⌊t/(2*Real.pi)⌋).subset
  intro k hk
  have hk0 := hk.1
  refine ⟨by omega, Int.le_floor.mpr ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
  nlinarith [hk.2]

end RHTower.DeletionMixedRefinement
