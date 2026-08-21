/-
# Chen--Gupta--Li Mellin phase jets

The CGL kernel uses the unit-modulus Mellin phase `x ↦ x^(it)`.  This module
gives its exact all-order derivatives at every certified nonzero real input,
and bounds their coefficient by a factorial times `(1 + |t|)^n`.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiMellinPhase

noncomputable section

namespace RHTower

/-- Coefficient of the `n`th derivative of the CGL Mellin phase. -/
def cglPhaseJetCoeff (t : ℝ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => cglPhaseJetCoeff t n * ((t : ℂ) * Complex.I - n)

/-- The exact `n`th Mellin-phase derivative on the nonzero real axis. -/
def cglPhaseJet (n : ℕ) (t x : ℝ) : ℂ :=
  cglPhaseJetCoeff t n * (x⁻¹ : ℂ) ^ n * cglMellinPhase t x

/-- One derivative advances the phase jet by its literal recurrence. -/
theorem hasDerivAt_cglPhaseJet (n : ℕ) (t : ℝ) (x : CGLMellinPhaseInput) :
    HasDerivAt (cglPhaseJet n t)
      (cglPhaseJet (n + 1) t x.value) x.value := by
  unfold cglPhaseJet
  rw [show cglPhaseJetCoeff t (n + 1) =
      cglPhaseJetCoeff t n * ((t : ℂ) * Complex.I - n) by rfl]
  have hinv : HasDerivAt (fun y : ℝ => (y⁻¹ : ℂ)) (-(x.value⁻¹ : ℂ) ^ 2) x.value := by
    apply HasDerivAt.of_isLittleO
    have hraw := (((hasDerivAt_id x.value).inv x.nonzero).ofReal_comp).isLittleO
    have hvalue : (-(x.value⁻¹ : ℂ) ^ 2) = ((-1 / x.value ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    convert hraw using 1
    ext y
    simp only [Pi.inv_apply, id_eq, Complex.ofReal_inv, hvalue]
  have hp : HasDerivAt (fun y : ℝ => (y⁻¹ : ℂ) ^ n)
      ((n : ℂ) * (x.value⁻¹ : ℂ) ^ (n - 1) * (-(x.value⁻¹ : ℂ) ^ 2)) x.value := by
    apply HasDerivAt.of_isLittleO
    have hpow := (hinv.pow n).isLittleO
    convert hpow using 1
    all_goals simp only [Pi.pow_apply]
  have hphase := hasDerivAt_cglMellinPhase t x
  have hcalc := (hp.const_mul (cglPhaseJetCoeff t n)).mul hphase
  change HasDerivAt
    (fun y : ℝ => cglPhaseJetCoeff t n * (y⁻¹ : ℂ) ^ n * cglMellinPhase t y)
    (cglPhaseJetCoeff t n * ((t : ℂ) * Complex.I - n) *
      (x.value⁻¹ : ℂ) ^ (n + 1) * cglMellinPhase t x.value) x.value
  refine hcalc.congr_deriv ?_
  cases n with
  | zero =>
    simp only [cglPhaseJetCoeff]
    ring
  | succ n =>
    simp only [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one, pow_succ]
    ring

/-- Exact all-order derivative formula for `x ↦ x^(it)` at a certified nonzero input. -/
theorem iteratedDeriv_cglMellinPhase_of_nonzero (n : ℕ) (t : ℝ)
    (x : CGLMellinPhaseInput) :
    iteratedDeriv n (cglMellinPhase t) x.value = cglPhaseJet n t x.value := by
  induction n generalizing x with
  | zero => simp [cglPhaseJet, cglPhaseJetCoeff]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    calc
      deriv (iteratedDeriv n (cglMellinPhase t)) x.value =
          deriv (cglPhaseJet n t) x.value := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [eventually_ne_nhds x.nonzero] with y hy
        exact ih ⟨y, hy⟩
      _ = cglPhaseJet (n + 1) t x.value :=
        (hasDerivAt_cglPhaseJet n t x).deriv

/-- The phase-jet coefficient has the uniform source-scale polynomial bound in `|t|`. -/
theorem norm_cglPhaseJetCoeff_le (n : ℕ) (t : ℝ) :
    ‖cglPhaseJetCoeff t n‖ ≤ n.factorial * (1 + |t|) ^ n := by
  induction n with
  | zero => norm_num [cglPhaseJetCoeff]
  | succ n ih =>
    have hterm : ‖(t : ℂ) * Complex.I - n‖ ≤ |t| + n := by
      calc
        ‖(t : ℂ) * Complex.I - n‖ ≤ ‖(t : ℂ) * Complex.I‖ + ‖(n : ℂ)‖ :=
          norm_sub_le _ _
        _ = |t| + n := by
          simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
          norm_cast
    have hfactor : |t| + n ≤ ((n : ℝ) + 1) * (1 + |t|) := by
      have ht : 0 ≤ |t| := abs_nonneg t
      nlinarith
    calc
      ‖cglPhaseJetCoeff t (n + 1)‖ =
          ‖cglPhaseJetCoeff t n‖ * ‖(t : ℂ) * Complex.I - n‖ := by
        rw [cglPhaseJetCoeff, norm_mul]
      _ ≤ (n.factorial * (1 + |t|) ^ n) * (|t| + n) := by
        gcongr
      _ ≤ (n.factorial * (1 + |t|) ^ n) * (((n : ℝ) + 1) * (1 + |t|)) := by
        gcongr
      _ = (n + 1).factorial * (1 + |t|) ^ (n + 1) := by
        rw [Nat.factorial_succ, pow_succ]
        push_cast
        ring

/-- Global pointwise norm bound for the exact Mellin-phase jet. -/
theorem norm_cglPhaseJet_le (n : ℕ) (t x : ℝ) :
    ‖cglPhaseJet n t x‖ ≤
      n.factorial * (1 + |t|) ^ n * |x⁻¹| ^ n := by
  unfold cglPhaseJet
  rw [norm_mul, norm_mul, norm_cglMellinPhase]
  calc
    ‖cglPhaseJetCoeff t n‖ * ‖(x⁻¹ : ℂ) ^ n‖ * 1 =
        ‖cglPhaseJetCoeff t n‖ * |x⁻¹| ^ n * 1 := by
      rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_inv]
    _ ≤
        (n.factorial * (1 + |t|) ^ n) * |x⁻¹| ^ n * 1 := by
      gcongr
      exact norm_cglPhaseJetCoeff_le n t
    _ = n.factorial * (1 + |t|) ^ n * |x⁻¹| ^ n := by ring

end RHTower
