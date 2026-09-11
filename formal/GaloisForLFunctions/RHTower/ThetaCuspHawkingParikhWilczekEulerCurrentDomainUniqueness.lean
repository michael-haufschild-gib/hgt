import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekSingularSourceSquareShiftedModes
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# PW arithmetic-current admission and forced-response uniqueness

The literal von Mangoldt dilation current, pulled to log coordinates, detects
outgoing growth on every prime-power ray. Its necessary term-decay condition
excludes every nonzero homogeneous solution of the singular PW connection at
any complex shift. Consequently two complete forced responses satisfying that
condition at one prime and one base point agree.

The original Gamma profile satisfies every such term test, but its exact singular
reflection fails them all. Thus the arithmetic condition is nontrivial and is
not preserved by this reflection. It excludes critical-line homogeneous shifts
too: no Xi occurrence, physical operator domain, or RH conclusion is asserted.
-/

open Real MeasureTheory GaloisForLFunctions Filter Topology ArithmeticFunction

namespace RHTower

noncomputable section

/-- The literal von Mangoldt dilation-current term in logarithmic coordinates. -/
def pwEulerCurrentTerm (f : ℝ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  (vonMangoldt n : ℂ) * f (t + Real.log (n : ℝ))

/-- A necessary term test on one prime-power subfamily of the actual current. -/
def PWEulerPrimePowerDecay (p : ℕ) (t : ℝ) (f : ℝ → ℂ) : Prop :=
  Tendsto (fun j : ℕ => pwEulerCurrentTerm f t (p ^ (j + 1))) atTop (𝓝 0)

theorem pwEulerCurrentTerm_logPull (F : ℝ → ℂ) (t : ℝ) (n : ℕ) :
    pwEulerCurrentTerm (fun u => F (Real.exp u)) t n =
      (vonMangoldt n : ℂ) * F ((n : ℝ) * Real.exp t) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwEulerCurrentTerm]
  · unfold pwEulerCurrentTerm
    change (vonMangoldt n : ℂ) * F (Real.exp (t + Real.log (n : ℝ))) = _
    rw [Real.exp_add, Real.exp_log (by exact_mod_cast hn), mul_comm (Real.exp t)]

/-- The singular connection exponent dominates every linear tilt at the outgoing end. -/
theorem pwLogShiftedExponent_tendsto_atTop (b : ℝ) :
    Tendsto (fun u => pwLogSingularGaugePotential u + b * u) atTop atTop := by
  have hexp : Tendsto (fun u : ℝ => Real.exp u / u) atTop atTop := by
    simpa only [pow_one] using Real.tendsto_exp_div_pow_atTop 1
  refine tendsto_atTop_mono' _ ?_ tendsto_id
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hexp.eventually_ge_atTop (2 * (|b| + 2))] with u hu he
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have he' := (le_div_iff₀ hu0).mp he
  have hneg : Real.exp (-u) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr hu0.le)
  have hb : 0 ≤ (|b| + b) * u :=
    mul_nonneg (by linarith [neg_le_abs b]) hu0.le
  change u ≤ pwLogSingularGaugePotential u + b * u
  rw [pwLogSingularGaugePotential, Real.sinh_eq]
  nlinarith

theorem pwLogShiftedSourceMode_norm_tendsto_atTop (z : ℂ) {c : ℂ} (hc : c ≠ 0) :
    Tendsto (fun u => ‖c * pwLogShiftedSourceMode z u‖) atTop atTop := by
  have h := (Real.tendsto_exp_atTop.comp (pwLogShiftedExponent_tendsto_atTop z.re)).const_mul_atTop
    (norm_pos_iff.mpr hc)
  simpa only [Function.comp_apply, pwLogShiftedSourceMode, norm_mul, Complex.norm_exp, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] using h

theorem pwPrimePowerCoordinate_tendsto_atTop (t : ℝ) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun j : ℕ => t + Real.log ((p ^ (j + 1) : ℕ) : ℝ)) atTop atTop := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp'
  have hcast : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h : Tendsto (fun j : ℕ => t + ((j : ℝ) + 1) * Real.log (p : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop (hcast.atTop_mul_const hlog)
  convert h using 1
  ext j
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  rfl

/-- Outgoing norm growth is detected by every prime-power current subfamily. -/
theorem pwEulerCurrent_primePower_norm_tendsto_atTop (f : ℝ → ℂ)
    (hf : Tendsto (fun u => ‖f u‖) atTop atTop) (t : ℝ) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun j : ℕ => ‖pwEulerCurrentTerm f t (p ^ (j + 1))‖) atTop atTop := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have h := (hf.comp (pwPrimePowerCoordinate_tendsto_atTop t hp)).const_mul_atTop hlog
  simpa only [Function.comp_apply, pwEulerCurrentTerm, vonMangoldt_apply_pow (Nat.succ_ne_zero _),
    vonMangoldt_apply_prime hp, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hlog.le] using h

/-- Even a single prime-power subfamily has divergent term norms on a nonzero mode. -/
theorem pwEulerCurrent_shiftedMode_primePower_norm_tendsto_atTop
    (z : ℂ) {c : ℂ} (hc : c ≠ 0) (t : ℝ) {p : ℕ} (hp : p.Prime) :
    Tendsto (fun j : ℕ =>
      ‖pwEulerCurrentTerm (fun u => c * pwLogShiftedSourceMode z u) t (p ^ (j + 1))‖)
      atTop atTop := by
  exact pwEulerCurrent_primePower_norm_tendsto_atTop _
    (pwLogShiftedSourceMode_norm_tendsto_atTop z hc) t hp

/-- Summability of the whole current implies the necessary prime-power term test. -/
theorem pwEulerCurrent_summable_primePowerDecay (f : ℝ → ℂ) (t : ℝ)
    {p : ℕ} (hp : p.Prime) (hf : Summable (pwEulerCurrentTerm f t)) :
    PWEulerPrimePowerDecay p t f := by
  have hinj : Function.Injective (fun j : ℕ => p ^ (j + 1)) :=
    (pow_right_strictMono₀ hp.one_lt).injective.comp Nat.succ_injective
  exact (hf.comp_injective hinj).tendsto_atTop_zero

/-- Arithmetic term decay excludes the homogeneous solution, independently of its shift. -/
theorem pwEulerCurrent_decay_homogeneous_eq_zero (z : ℂ) (f : ℝ → ℂ)
    (hf : ∀ u, HasDerivAt f (((pwLogSingularConnectionPotential u : ℂ) + z) * f u) u)
    (t : ℝ) {p : ℕ} (hp : p.Prime) (hdec : PWEulerPrimePowerDecay p t f) : f = 0 := by
  obtain ⟨c, hc⟩ := (pwLogShiftedSourceMode_classification z f).mp hf
  have heq : f = fun u => c * pwLogShiftedSourceMode z u := funext hc
  by_cases hc0 : c = 0
  · funext u
    rw [hc u, hc0, zero_mul]
    rfl
  · have hgrow := pwEulerCurrent_shiftedMode_primePower_norm_tendsto_atTop z hc0 t hp
    rw [heq] at hdec
    exact False.elim (not_tendsto_nhds_of_tendsto_atTop hgrow 0
      (by simpa only [norm_zero] using hdec.norm))

theorem PWEulerPrimePowerDecay.sub {p : ℕ} {t : ℝ} {f g : ℝ → ℂ}
    (hf : PWEulerPrimePowerDecay p t f) (hg : PWEulerPrimePowerDecay p t g) :
    PWEulerPrimePowerDecay p t (fun u => f u - g u) := by
  unfold PWEulerPrimePowerDecay at *
  simpa only [pwEulerCurrentTerm, mul_sub, sub_zero] using Filter.Tendsto.sub hf hg

/-- The complete forced response is unique under one arithmetic term-decay test. -/
theorem pwEulerCurrent_forced_response_unique (z : ℂ) (r f g : ℝ → ℂ)
    (hf : ∀ u, HasDerivAt f (((pwLogSingularConnectionPotential u : ℂ) + z) * f u + r u) u)
    (hg : ∀ u, HasDerivAt g (((pwLogSingularConnectionPotential u : ℂ) + z) * g u + r u) u)
    (t : ℝ) {p : ℕ} (hp : p.Prime)
    (hfd : PWEulerPrimePowerDecay p t f) (hgd : PWEulerPrimePowerDecay p t g) : f = g := by
  have hh : ∀ u, HasDerivAt (fun v => f v - g v)
      (((pwLogSingularConnectionPotential u : ℂ) + z) * (f u - g u)) u := by
    intro u
    exact ((hf u).sub (hg u)).congr_deriv (by ring)
  have heq := pwEulerCurrent_decay_homogeneous_eq_zero z _ hh t hp (hfd.sub hgd)
  funext u
  exact sub_eq_zero.mp (congrFun heq u)

private theorem pwOriginalGammaProfile_tendsto_zero :
    Tendsto (expShift (1 / 2) 0) atTop (𝓝 0) := by
  have hexp : Tendsto (fun u : ℝ => Real.exp u / u) atTop atTop := by
    simpa only [pow_one] using Real.tendsto_exp_div_pow_atTop 1
  have hgrow : Tendsto (fun u : ℝ => Real.exp u - u / 2) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_ge_atTop (1 : ℝ), hexp.eventually_ge_atTop 2] with u hu he
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
    have he' := (le_div_iff₀ hu0).mp he
    change u ≤ Real.exp u - u / 2
    linarith
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hgrow using 1
  funext u
  unfold expShift
  congr 1
  simp only [Nat.cast_zero, add_zero]
  ring

/-- The actual original Gamma profile passes every prime-power current term test. -/
theorem pwOriginalGammaProfile_primePowerDecay (t : ℝ) {p : ℕ} (hp : p.Prime) :
    PWEulerPrimePowerDecay p t (fun u => (expShift (1 / 2) 0 u : ℂ)) := by
  have hq : Tendsto (fun u => (expShift (1 / 2) 0 u : ℂ)) atTop (𝓝 0) := by
    convert (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp
      pwOriginalGammaProfile_tendsto_zero using 1
    all_goals simp only [Function.comp_def, Complex.ofReal_zero]
  have h := (hq.comp (pwPrimePowerCoordinate_tendsto_atTop t hp)).const_mul
    (Real.log (p : ℝ) : ℂ)
  simpa only [Function.comp_apply, PWEulerPrimePowerDecay, pwEulerCurrentTerm,
    vonMangoldt_apply_pow (Nat.succ_ne_zero _), vonMangoldt_apply_prime hp, mul_zero] using h

/-- The original source leaves the arithmetic decay domain under singular reflection. -/
theorem pwOriginalGammaProfile_reflected_norm_tendsto_atTop :
    Tendsto (fun u => ‖pwLogSingularComplexReflection
      (fun v => (expShift (1 / 2) 0 v : ℂ)) u‖) atTop atTop := by
  have hgrow : Tendsto (fun u : ℝ =>
      2 * pwLogSingularGaugePotential u - u / 2 - Real.exp (-u)) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ (pwLogShiftedExponent_tendsto_atTop (-1))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hu0 : 0 ≤ u := le_trans zero_le_one hu
    have hs := HTGeometry.self_le_sinh_of_nonneg hu0
    have he : Real.exp (-u) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr hu0)
    change pwLogSingularGaugePotential u + (-1) * u ≤ _
    unfold pwLogSingularGaugePotential
    linarith
  convert Real.tendsto_exp_atTop.comp hgrow using 1
  funext u
  simp only [Function.comp_apply, pwLogSingularComplexReflection, norm_mul,
    Complex.norm_real, pwLogSingularGain, expShift, Nat.cast_zero, add_zero,
    Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  congr 1
  ring

theorem pwOriginalGammaProfile_reflected_not_primePowerDecay (t : ℝ)
    {p : ℕ} (hp : p.Prime) :
    ¬ PWEulerPrimePowerDecay p t (pwLogSingularComplexReflection
      (fun u => (expShift (1 / 2) 0 u : ℂ))) := by
  intro hdec
  have hgrow := pwEulerCurrent_primePower_norm_tendsto_atTop _
    pwOriginalGammaProfile_reflected_norm_tendsto_atTop t hp
  exact not_tendsto_nhds_of_tendsto_atTop hgrow 0
    (by simpa only [norm_zero] using hdec.norm)

/-- The arithmetic term-decay domain is nontrivial, but contains no nonzero homogeneous
mode of any shifted singular connection. This is not a selective Xi realization. -/
theorem pwEulerCurrentDomain_nontrivial_homogeneous_kernel_trivial :
    (∃ f : ℝ → ℂ, f ≠ 0 ∧ PWEulerPrimePowerDecay 2 0 f) ∧
    (∀ z : ℂ, ¬ ∃ f : ℝ → ℂ, f ≠ 0 ∧
      (∀ u, HasDerivAt f (((pwLogSingularConnectionPotential u : ℂ) + z) * f u) u) ∧
      PWEulerPrimePowerDecay 2 0 f) := by
  constructor
  · refine ⟨fun u => (expShift (1 / 2) 0 u : ℂ), ?_,
      pwOriginalGammaProfile_primePowerDecay 0 Nat.prime_two⟩
    intro hz
    have h0 := congrFun hz 0
    exact (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) h0
  · intro z
    rintro ⟨f, hf0, hf, hdec⟩
    exact hf0 (pwEulerCurrent_decay_homogeneous_eq_zero z f hf 0 Nat.prime_two hdec)

/-- The literal original source witnesses failure of reflection invariance at every prime
and every base point. -/
theorem pwEulerCurrentDomain_reflection_not_preserved :
    ∃ f : ℝ → ℂ, ∀ (p : ℕ), p.Prime → ∀ t : ℝ,
      PWEulerPrimePowerDecay p t f ∧
      ¬ PWEulerPrimePowerDecay p t (pwLogSingularComplexReflection f) := by
  refine ⟨fun u => (expShift (1 / 2) 0 u : ℂ), ?_⟩
  intro p hp t
  exact ⟨pwOriginalGammaProfile_primePowerDecay t hp,
    pwOriginalGammaProfile_reflected_not_primePowerDecay t hp⟩

end

end RHTower
