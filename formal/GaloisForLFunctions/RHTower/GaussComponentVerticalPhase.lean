import GaloisForLFunctions.RHTower.DigammaImaginaryVerticalAsymptotic
import GaloisForLFunctions.RHTower.GaussComponentVerticalMagnitude
import GaloisForLFunctions.RHTower.LateralWindingFloor
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly

/-!
# Vertical phase of an archimedean Gauss component

The magnitude asymptotic of a Gauss component is not enough for the paired-channel
Hankel calculation: the moving Fourier phase is load-bearing.  This file supplies the
missing complex vertical asymptotic of the lower Gamma factor and combines the two
digamma phases into the exact logarithmic clock of the Gauss component.
-/

namespace RHTower

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

/-- The lower-half-plane vertical digamma asymptotic, obtained by conjugating the
upper-half-plane theorem. -/
theorem digamma_lower_vertical_sub_log_I_tendsto_zero (σ : ℝ) (hσ : 0 ≤ σ) :
    Tendsto (fun t : ℝ =>
      Complex.digamma ((σ : ℂ) - (t : ℂ) * Complex.I) -
        ((Real.log t : ℂ) - (Real.pi / 2 : ℂ) * Complex.I))
      atTop (nhds 0) := by
  have hupper := digamma_vertical_sub_log_I_tendsto_zero σ hσ
  have hconj := (Complex.continuous_conj.continuousAt.tendsto.comp hupper)
  have hconj' : Tendsto (fun t : ℝ => conj
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) -
        ((Real.log t : ℂ) + (Real.pi / 2 : ℂ) * Complex.I)))
      atTop (nhds 0) := by
    simpa only [Function.comp_apply, map_zero] using! hconj
  refine hconj'.congr' ?_
  filter_upwards with t
  rw [map_sub]
  rw [← ReflectedDigammaAnomaly.digamma_conj]
  apply congrArg₂ (· - ·)
  · congr 1
    apply Complex.ext <;> simp
  · apply Complex.ext <;> (simp [Complex.div_re, Complex.div_im] <;> ring)

/-- Upper Gamma argument of the vertical Gauss component. -/
def gaussComponentVerticalUpperArg {m : ℕ} (k : Fin m) (z : ℂ) : ℂ :=
  (gaussComponentOffset k : ℂ) + Complex.I / (2 * (m : ℂ)) * z

/-- Lower Gamma argument of the vertical Gauss component. -/
def gaussComponentVerticalLowerArg {m : ℕ} (k : Fin m) (z : ℂ) : ℂ :=
  ((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) -
    Complex.I / (2 * (m : ℂ)) * z

/-- The actual vertical archimedean Gauss component, including its positive-base
power and its conjugate Gamma ratio. -/
def gaussComponentVerticalCarrier {m : ℕ} (k : Fin m) (z : ℂ) : ℂ :=
  Complex.exp
      (-(Complex.I / (m : ℂ)) *
        (Real.log (Real.pi / (m : ℝ)) : ℂ) * z) *
    Complex.Gamma (gaussComponentVerticalUpperArg k z) /
      Complex.Gamma (gaussComponentVerticalLowerArg k z)

/-- Real-height restriction of the actual vertical Gauss component. -/
def gaussComponentVerticalValue {m : ℕ} (k : Fin m) (t : ℝ) : ℂ :=
  gaussComponentVerticalCarrier k (t : ℂ)

/-- Logarithmic derivative of the vertical `m`-fold Gauss component. -/
def gaussComponentVerticalLogDeriv {m : ℕ} (k : Fin m) (t : ℝ) : ℂ :=
  -(Complex.I / (m : ℂ)) * (Real.log (Real.pi / (m : ℝ)) : ℂ) +
    Complex.I / (2 * (m : ℂ)) *
      (Complex.digamma (gaussComponentVerticalUpperArg k (t : ℂ)) +
        Complex.digamma (gaussComponentVerticalLowerArg k (t : ℂ)))

/-- The phase clock of a Gauss component is universal: its logarithmic derivative is
asymptotic to `i/m * log (t/(2π))`, independently of the component label `k`. -/
theorem gaussComponentVerticalLogDeriv_sub_clock_tendsto_zero
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) :
    Tendsto (fun t : ℝ =>
      gaussComponentVerticalLogDeriv k t -
        Complex.I / (m : ℂ) * (Real.log (t / (2 * Real.pi)) : ℂ))
      atTop (nhds 0) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hc : (0 : ℝ) < 2 * (m : ℝ) := mul_pos (by norm_num) hmR
  have ha : 0 ≤ gaussComponentOffset k := by
    rw [gaussComponentOffset]
    positivity
  have hδ : 0 ≤ gaussComponentDelta m := by
    rw [gaussComponentDelta]
    positivity
  have hu := (digamma_vertical_sub_log_I_tendsto_zero
    (gaussComponentOffset k) ha).comp (tendsto_id.atTop_div_const hc)
  have hl := (digamma_lower_vertical_sub_log_I_tendsto_zero
    (gaussComponentOffset k + gaussComponentDelta m) (add_nonneg ha hδ)).comp
      (tendsto_id.atTop_div_const hc)
  have hsum := hu.add hl
  have hscaled := hsum.const_mul (Complex.I / (2 * (m : ℂ)))
  have hscaled' : Tendsto (fun t : ℝ =>
      Complex.I / (2 * (m : ℂ)) *
        ((Complex.digamma
            ((gaussComponentOffset k : ℂ) +
              (t / (2 * (m : ℝ)) : ℂ) * Complex.I) -
            ((Real.log (t / (2 * (m : ℝ))) : ℂ) +
              (Real.pi / 2 : ℂ) * Complex.I)) +
          (Complex.digamma
            (((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) -
              (t / (2 * (m : ℝ)) : ℂ) * Complex.I) -
            ((Real.log (t / (2 * (m : ℝ))) : ℂ) -
              (Real.pi / 2 : ℂ) * Complex.I))))
      atTop (nhds 0) := by simpa using hscaled
  refine hscaled'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have htau : 0 < t / (2 * (m : ℝ)) := div_pos ht hc
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlogscale :
      Real.log (t / (2 * (m : ℝ))) - Real.log (Real.pi / (m : ℝ)) =
        Real.log (t / (2 * Real.pi)) := by
    rw [← Real.log_div (div_ne_zero ht.ne' hc.ne')
      (div_ne_zero hpi.ne' hmR.ne')]
    congr 1
    field_simp
  have huarg : gaussComponentVerticalUpperArg k (t : ℂ) =
      (gaussComponentOffset k : ℂ) +
        (t / (2 * (m : ℝ)) : ℂ) * Complex.I := by
    simp only [gaussComponentVerticalUpperArg]
    push_cast
    ring
  have hlarg : gaussComponentVerticalLowerArg k (t : ℂ) =
      ((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) -
        (t / (2 * (m : ℝ)) : ℂ) * Complex.I := by
    simp only [gaussComponentVerticalLowerArg]
    push_cast
    ring
  simp only [gaussComponentVerticalLogDeriv]
  rw [huarg, hlarg]
  push_cast
  rw [← hlogscale]
  rw [Complex.ofReal_sub]
  ring

/-- A function vanishing at `+∞` has vanishing integral over every fixed forward window. -/
theorem intervalIntegral_add_tendsto_zero_of_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Tendsto f atTop (nhds 0)) {h : ℝ} (hh : 0 ≤ h) :
    Tendsto (fun t : ℝ => ∫ x in t..(t + h), f x) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hf ⊢
  intro ε hε
  have hh1 : 0 < h + 1 := by linarith
  obtain ⟨T, hT⟩ := hf (ε / (h + 1)) (div_pos hε hh1)
  refine ⟨T, fun t ht => ?_⟩
  rw [dist_zero_right]
  have hab : t ≤ t + h := le_add_of_nonneg_right hh
  calc
    ‖∫ x in t..(t + h), f x‖ ≤ (ε / (h + 1)) * |t + h - t| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      have hTx : T ≤ x := ht.trans (le_trans le_rfl hx.1.le)
      have hxlt : ‖f x‖ < ε / (h + 1) := by
        simpa [dist_zero_right] using hT x hTx
      exact hxlt.le
    _ = (ε / (h + 1)) * h := by rw [show t + h - t = h by ring, abs_of_nonneg hh]
    _ < ε := by
      calc
        (ε / (h + 1)) * h < (ε / (h + 1)) * (h + 1) :=
          mul_lt_mul_of_pos_left (by linarith) (div_pos hε hh1)
        _ = ε := div_mul_cancel₀ ε hh1.ne'

/-- Universal logarithmic phase clock of an `m`-fold Gauss component. -/
def gaussComponentVerticalClock (m : ℕ) (t : ℝ) : ℂ :=
  Complex.I / (m : ℂ) * (Real.log (t / (2 * Real.pi)) : ℂ)

/-- Difference between the exact Gauss logarithmic derivative and its universal clock. -/
def gaussComponentVerticalLogDerivError {m : ℕ} (k : Fin m) (t : ℝ) : ℂ :=
  gaussComponentVerticalLogDeriv k t - gaussComponentVerticalClock m t

/-- The accumulated complex error on a forward window, in the real/imaginary decomposition used
by `path_transport_exp_logDeriv`. -/
def gaussComponentVerticalAccumulatedError {m : ℕ}
    (k : Fin m) (t h : ℝ) : ℂ :=
  ((∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).re : ℝ) : ℂ) +
    ((∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).im : ℝ) : ℂ) *
      Complex.I

/-- The exact-minus-clock error accumulated on a fixed forward window vanishes at infinity. -/
theorem gaussComponentVerticalAccumulatedError_tendsto_zero
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) {h : ℝ} (hh : 0 ≤ h) :
    Tendsto (fun t : ℝ => gaussComponentVerticalAccumulatedError k t h)
      atTop (nhds 0) := by
  have herr : Tendsto (gaussComponentVerticalLogDerivError k) atTop (nhds 0) := by
    simpa [gaussComponentVerticalLogDerivError, gaussComponentVerticalClock] using!
      gaussComponentVerticalLogDeriv_sub_clock_tendsto_zero hm k
  have hre : Tendsto (fun t : ℝ => (gaussComponentVerticalLogDerivError k t).re)
      atTop (nhds 0) := by
    simpa using! Complex.continuous_re.continuousAt.tendsto.comp herr
  have him : Tendsto (fun t : ℝ => (gaussComponentVerticalLogDerivError k t).im)
      atTop (nhds 0) := by
    simpa using! Complex.continuous_im.continuousAt.tendsto.comp herr
  have hreInt := intervalIntegral_add_tendsto_zero_of_tendsto_zero hre hh
  have himInt := intervalIntegral_add_tendsto_zero_of_tendsto_zero him hh
  have hreCast : Tendsto (fun t : ℝ =>
      ((∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).re : ℝ) : ℂ))
      atTop (nhds 0) := by
    simpa using! Complex.continuous_ofReal.continuousAt.tendsto.comp hreInt
  have himCast : Tendsto (fun t : ℝ =>
      ((∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).im : ℝ) : ℂ) *
        Complex.I) atTop (nhds 0) := by
    have hcast : Tendsto (fun t : ℝ =>
        ((∫ x in t..(t + h), (gaussComponentVerticalLogDerivError k x).im : ℝ) : ℂ))
        atTop (nhds 0) := by
      simpa using! Complex.continuous_ofReal.continuousAt.tendsto.comp himInt
    simpa using hcast.mul_const Complex.I
  simpa [gaussComponentVerticalAccumulatedError] using hreCast.add himCast

lemma gaussComponentVerticalUpperArg_ne_neg_nat
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    gaussComponentVerticalUpperArg k (t : ℂ) ≠ -(n : ℂ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  intro h
  have himpos : 0 < (gaussComponentVerticalUpperArg k (t : ℂ)).im := by
    simp [gaussComponentVerticalUpperArg, Complex.div_im, Complex.div_re]
    positivity
  rw [h] at himpos
  simp at himpos

lemma gaussComponentVerticalLowerArg_ne_neg_nat
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    gaussComponentVerticalLowerArg k (t : ℂ) ≠ -(n : ℂ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  intro h
  have himneg : (gaussComponentVerticalLowerArg k (t : ℂ)).im < 0 := by
    simp [gaussComponentVerticalLowerArg, Complex.div_im, Complex.div_re]
    positivity
  rw [h] at himneg
  simp at himneg

private theorem deriv_Gamma_eq_mul_digamma {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -(n : ℂ)) :
    deriv Complex.Gamma z = Complex.Gamma z * Complex.digamma z := by
  rw [Complex.digamma_def, logDeriv_apply]
  field_simp [Complex.Gamma_ne_zero hz]

/-- Exact logarithmic-derivative equation for the actual vertical Gauss component. -/
theorem hasDerivAt_gaussComponentVerticalValue
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussComponentVerticalValue k)
      (gaussComponentVerticalValue k t * gaussComponentVerticalLogDeriv k t) t := by
  let α : ℂ := -(Complex.I / (m : ℂ)) *
    (Real.log (Real.pi / (m : ℝ)) : ℂ)
  let β : ℂ := Complex.I / (2 * (m : ℂ))
  let γ : ℂ := -Complex.I / (2 * (m : ℂ))
  let u : ℂ := gaussComponentVerticalUpperArg k (t : ℂ)
  let v : ℂ := gaussComponentVerticalLowerArg k (t : ℂ)
  have huPole : ∀ n : ℕ, u ≠ -(n : ℂ) := by
    intro n
    exact gaussComponentVerticalUpperArg_ne_neg_nat hm k ht n
  have hvPole : ∀ n : ℕ, v ≠ -(n : ℂ) := by
    intro n
    exact gaussComponentVerticalLowerArg_ne_neg_nat hm k ht n
  have hu' : HasDerivAt (gaussComponentVerticalUpperArg k) β (t : ℂ) := by
    simpa [gaussComponentVerticalUpperArg, β] using!
      (hasDerivAt_const (t : ℂ) (gaussComponentOffset k : ℂ)).add
        ((hasDerivAt_id (t : ℂ)).const_mul β)
  have hv' : HasDerivAt (gaussComponentVerticalLowerArg k) γ (t : ℂ) := by
    have hraw :=
      (hasDerivAt_const (t : ℂ)
        ((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ)).sub
          ((hasDerivAt_id (t : ℂ)).const_mul
            (Complex.I / (2 * (m : ℂ))))
    change HasDerivAt
      (fun z : ℂ =>
        ((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) -
          Complex.I / (2 * (m : ℂ)) * z)
      (-Complex.I / (2 * (m : ℂ))) (t : ℂ)
    convert! hraw using 1
    ring
  have hΓu : HasDerivAt
      (fun z => Complex.Gamma (gaussComponentVerticalUpperArg k z))
      (Complex.Gamma u * Complex.digamma u * β) (t : ℂ) := by
    have h := (Complex.differentiableAt_Gamma u huPole).hasDerivAt.comp (t : ℂ) hu'
    simpa [deriv_Gamma_eq_mul_digamma huPole] using! h
  have hΓv : HasDerivAt
      (fun z => Complex.Gamma (gaussComponentVerticalLowerArg k z))
      (Complex.Gamma v * Complex.digamma v * γ) (t : ℂ) := by
    have h := (Complex.differentiableAt_Gamma v hvPole).hasDerivAt.comp (t : ℂ) hv'
    simpa [deriv_Gamma_eq_mul_digamma hvPole] using! h
  have hlin : HasDerivAt (fun z : ℂ => α * z) α (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).const_mul α
  have hE : HasDerivAt (fun z : ℂ => Complex.exp (α * z))
      (Complex.exp (α * (t : ℂ)) * α) (t : ℂ) := hlin.cexp
  have hv0 : Complex.Gamma v ≠ 0 := Complex.Gamma_ne_zero hvPole
  have hv0' : Complex.Gamma
      (gaussComponentVerticalLowerArg k (t : ℂ)) ≠ 0 := by
    simpa [v] using hv0
  have hcarrier : HasDerivAt (gaussComponentVerticalCarrier k)
      (gaussComponentVerticalCarrier k (t : ℂ) *
        (α + β * (Complex.digamma u + Complex.digamma v))) (t : ℂ) := by
    have hquot := (hE.mul hΓu).div hΓv hv0
    convert! hquot using 1
    · simp only [gaussComponentVerticalCarrier, α, β, γ, u, v]
      simp only [Pi.mul_apply]
      field_simp [hv0']
      ring
  have hreal : HasDerivAt (fun s : ℝ =>
      gaussComponentVerticalCarrier k (s : ℂ))
      (gaussComponentVerticalCarrier k (t : ℂ) *
        (α + β * (Complex.digamma u + Complex.digamma v))) t :=
    by simpa [Function.comp_def] using!
      hcarrier.comp t (hasDerivAt_id t).ofReal_comp
  simpa only [gaussComponentVerticalValue, gaussComponentVerticalLogDeriv,
    α, β, u, v] using! hreal

/-- The actual vertical Gauss component has no zero at positive height. -/
theorem gaussComponentVerticalValue_ne_zero
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) {t : ℝ} (ht : 0 < t) :
    gaussComponentVerticalValue k t ≠ 0 := by
  have hu : ∀ n : ℕ,
      gaussComponentVerticalUpperArg k (t : ℂ) ≠ -(n : ℂ) :=
    gaussComponentVerticalUpperArg_ne_neg_nat hm k ht
  have hv : ∀ n : ℕ,
      gaussComponentVerticalLowerArg k (t : ℂ) ≠ -(n : ℂ) :=
    gaussComponentVerticalLowerArg_ne_neg_nat hm k ht
  unfold gaussComponentVerticalValue gaussComponentVerticalCarrier
  exact div_ne_zero
    (mul_ne_zero (Complex.exp_ne_zero _)
      (Complex.Gamma_ne_zero hu))
    (Complex.Gamma_ne_zero hv)

/-- The Gauss-component logarithmic derivative is continuous on the positive-height axis. -/
theorem continuousOn_gaussComponentVerticalLogDeriv_pos
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) :
    ContinuousOn (gaussComponentVerticalLogDeriv k) (Set.Ioi 0) := by
  intro t ht
  have huArg : ContinuousAt
      (fun s : ℝ => gaussComponentVerticalUpperArg k (s : ℂ)) t := by
    unfold gaussComponentVerticalUpperArg
    fun_prop
  have hvArg : ContinuousAt
      (fun s : ℝ => gaussComponentVerticalLowerArg k (s : ℂ)) t := by
    unfold gaussComponentVerticalLowerArg
    fun_prop
  have huPole : ∀ n : ℕ,
      gaussComponentVerticalUpperArg k (t : ℂ) ≠ -(n : ℂ) :=
    fun n => gaussComponentVerticalUpperArg_ne_neg_nat hm k ht n
  have hvPole : ∀ n : ℕ,
      gaussComponentVerticalLowerArg k (t : ℂ) ≠ -(n : ℂ) :=
    fun n => gaussComponentVerticalLowerArg_ne_neg_nat hm k ht n
  have hu : ContinuousAt (fun s : ℝ =>
      Complex.digamma (gaussComponentVerticalUpperArg k (s : ℂ))) t :=
    ContinuousAt.comp
      (f := fun s : ℝ => gaussComponentVerticalUpperArg k (s : ℂ))
      (GaloisForLFunctions.continuousAt_digamma _ huPole) huArg
  have hv : ContinuousAt (fun s : ℝ =>
      Complex.digamma (gaussComponentVerticalLowerArg k (s : ℂ))) t :=
    ContinuousAt.comp
      (f := fun s : ℝ => gaussComponentVerticalLowerArg k (s : ℂ))
      (GaloisForLFunctions.continuousAt_digamma _ hvPole) hvArg
  exact (continuousAt_const.add (continuousAt_const.mul (hu.add hv))).continuousWithinAt

/-- Exact finite-shift transport of the actual Gauss component by its logarithmic derivative. -/
theorem gaussComponentVerticalValue_add_eq_exp_integral_logDeriv
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) {a h : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) :
    gaussComponentVerticalValue k (a + h) =
      gaussComponentVerticalValue k a *
        Complex.exp
          (((∫ t in a..(a + h), (gaussComponentVerticalLogDeriv k t).re : ℝ) : ℂ) +
            ((∫ t in a..(a + h), (gaussComponentVerticalLogDeriv k t).im : ℝ) : ℂ) *
              Complex.I) := by
  have hab : a ≤ a + h := le_add_of_nonneg_right hh
  have hsub : Set.Icc a (a + h) ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_lt_of_le ha ht.1
  have htransport := path_transport_exp_logDeriv
    (G := gaussComponentVerticalValue k)
    (ω := gaussComponentVerticalLogDeriv k)
    (U := Set.Ioi (0 : ℝ))
    isOpen_Ioi hsub
    (fun t ht => hasDerivAt_gaussComponentVerticalValue hm k (hsub ht))
    (continuousOn_gaussComponentVerticalLogDeriv_pos hm k)
    (a + h) ⟨hab, le_rfl⟩
  exact htransport

/-- Quotient form of the exact finite-shift transport. -/
theorem gaussComponentVerticalValue_add_div_eq_exp_integral_logDeriv
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) {a h : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) :
    gaussComponentVerticalValue k (a + h) /
        gaussComponentVerticalValue k a =
      Complex.exp
        (((∫ t in a..(a + h), (gaussComponentVerticalLogDeriv k t).re : ℝ) : ℂ) +
          ((∫ t in a..(a + h), (gaussComponentVerticalLogDeriv k t).im : ℝ) : ℂ) *
            Complex.I) := by
  rw [gaussComponentVerticalValue_add_eq_exp_integral_logDeriv hm k ha hh]
  field_simp [gaussComponentVerticalValue_ne_zero hm k ha]

end

end RHTower
