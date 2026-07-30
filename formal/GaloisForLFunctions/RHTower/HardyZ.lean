import GaloisForLFunctions.RHTower.HardyCarrier
import GaloisForLFunctions.HTGeometry.UnitaryReflectionPhaseHalving
import GaloisForLFunctions.RHTower.SymmetrizedEMCarrier
import GaloisForLFunctions.RHTower.XiRealAnchorPositive

/-!
# A continuous Hardy Z-function from the exact zeta reflection law

The zeta functional equation and Schwarz reflection make every critical-line value a unitary
phase times one real amplitude.  The principal-log square root used for the finite carrier need not
be continuous, but the archimedean factor supplies a canonical continuous square root directly:

`gammaHardyPhase(t) = conj(Gammaℝ(1/2+it)) / ‖Gammaℝ(1/2+it)‖`.

Its square is exactly `zetaChi(1/2+it)`.  Unitary phase halving therefore produces a continuous
real function `hardyZ` with the exact polar decomposition

`ζ(1/2+it) = gammaHardyPhase(t) * hardyZ(t)`.

The module proves the corresponding norm, zeta-zero, Xi-zero, square-moment, and interval
integrability interfaces without any nonvanishing hypothesis on zeta and without RH.
-/

noncomputable section

namespace RHTower

open Complex Filter Topology GaloisForLFunctions.HTGeometry

/-! ## Schwarz reflection on the whole open right half-plane -/

/-- **Right-half-plane Schwarz reflection for zeta.**  The Dirichlet-series theorem only supplied
this identity on `Re s > 1`.  Cancelling the nonzero archimedean factor from the global Xi reality
law extends it to every `Re s > 0`, away only from zeta's pole at `s = 1`. -/
theorem riemannZeta_conj_of_re_pos {s : ℂ} (hpos : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannZeta s) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos
  have hcs0 : (starRingEnd ℂ) s ≠ 0 := by
    intro h
    have h' := congrArg (starRingEnd ℂ) h
    rw [Complex.conj_conj, map_zero] at h'
    exact hs0 h'
  have hcs1 : (starRingEnd ℂ) s ≠ 1 := by
    intro h
    have h' := congrArg (starRingEnd ℂ) h
    rw [Complex.conj_conj, map_one] at h'
    exact h1 h'
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hpos
  have hGc : Gammaℝ ((starRingEnd ℂ) s) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by rwa [Complex.conj_re])
  have harch : archFactor ((starRingEnd ℂ) s) = (starRingEnd ℂ) (archFactor s) := by
    unfold archFactor
    rw [Gammaℝ_conj, map_mul, map_div₀, map_mul, map_sub, map_one, map_ofNat]
  have harchc : archFactor ((starRingEnd ℂ) s) ≠ 0 :=
    archFactor_ne_zero hcs0 hcs1 hGc
  have hxi := xi_conj s
  rw [xi_eq_archFactor_mul_zeta hcs0 hcs1 hGc,
    xi_eq_archFactor_mul_zeta hs0 h1 hG, harch, map_mul] at hxi
  have harchc' : (starRingEnd ℂ) (archFactor s) ≠ 0 := by
    rwa [← harch]
  exact mul_left_cancel₀ harchc' hxi

/-- Conjugation preserves zeta zeros throughout the open right half-plane away from the pole. -/
theorem riemannZeta_conj_eq_zero_iff_of_re_pos {s : ℂ}
    (hpos : 0 < s.re) (h1 : s ≠ 1) :
    riemannZeta ((starRingEnd ℂ) s) = 0 ↔ riemannZeta s = 0 := by
  rw [riemannZeta_conj_of_re_pos hpos h1]
  simp

private theorem linePt_ne_zero (τ : ℝ) : linePt τ ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  rw [linePt_re, Complex.zero_re] at h'
  norm_num at h'

private theorem linePt_ne_one (τ : ℝ) : linePt τ ≠ 1 := by
  intro h
  have h' := congrArg Complex.re h
  rw [linePt_re, Complex.one_re] at h'
  norm_num at h'

/-! ## Calculus of height reflections -/

/-- **Derivative reflection law.**  The derivative of every differentiable even real function is
odd.  This converts a value-level height reflection into its exact first-jet reflection. -/
theorem deriv_neg_of_even {f : ℝ → ℝ} (heven : Function.Even f)
    (hf : Differentiable ℝ f) (x : ℝ) : deriv f (-x) = -deriv f x := by
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
  have hcomp : HasDerivAt (fun y : ℝ => f (-y)) (deriv f (-x) * (-1)) x :=
    (hf (-x)).hasDerivAt.comp x hneg
  have heq : (fun y : ℝ => f (-y)) = f := funext heven
  have hderiv := congrArg (fun g : ℝ → ℝ => deriv g x) heq
  change deriv (fun y : ℝ => f (-y)) x = deriv f x at hderiv
  rw [hcomp.deriv] at hderiv
  linarith

/-- A differentiable even real function has a stationary reflection centre. -/
theorem deriv_zero_of_even {f : ℝ → ℝ} (heven : Function.Even f)
    (hf : Differentiable ℝ f) : deriv f 0 = 0 := by
  have h := deriv_neg_of_even heven hf 0
  simp only [neg_zero] at h
  linarith

/-- **Conjugate first-jet reflection law.**  If a differentiable complex path obeys
`f(-t)=conj(f(t))`, then its derivative obeys the reflected chain-rule identity
`f'(-t)=-conj(f'(t))`. -/
theorem deriv_neg_eq_neg_conj_of_conj_neg {f : ℝ → ℂ}
    (href : ∀ x, f (-x) = (starRingEnd ℂ) (f x))
    (hf : Differentiable ℝ f) (x : ℝ) :
    deriv f (-x) = -(starRingEnd ℂ) (deriv f x) := by
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
  have hleft : HasDerivAt (fun y : ℝ => f (-y)) (-(deriv f (-x))) x := by
    simpa [Function.comp_def] using (hf (-x)).hasDerivAt.scomp x hneg
  have hright : HasDerivAt (fun y : ℝ => (starRingEnd ℂ) (f y))
      ((starRingEnd ℂ) (deriv f x)) x := by
    simpa using! Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x (hf x).hasDerivAt
  have heq : (fun y : ℝ => f (-y)) = fun y => (starRingEnd ℂ) (f y) := funext href
  rw [heq] at hleft
  have hu := hleft.unique hright
  have hnegEq := congrArg Neg.neg hu
  simpa using hnegEq

/-- Negating the height conjugates the critical-line point. -/
@[simp] theorem linePt_neg (τ : ℝ) :
    linePt (-τ) = (starRingEnd ℂ) (linePt τ) := by
  rw [conj_linePt]
  unfold linePt
  push_cast
  ring

/-- Negating the height conjugates the finite Riemann--Siegel carrier. -/
@[simp] theorem gN_line_neg (N : ℕ) (τ : ℝ) :
    gN N (linePt (-τ)) = (starRingEnd ℂ) (gN N (linePt τ)) := by
  rw [linePt_neg, gN_conj]

/-! ## The continuous archimedean square-root phase -/

/-- The normalized conjugate archimedean factor on the critical line.  Unlike a principal-log
square root, this phase is globally continuous in the height. -/
noncomputable def gammaHardyPhase (τ : ℝ) : ℂ :=
  (starRingEnd ℂ) (Gammaℝ (linePt τ)) / ‖Gammaℝ (linePt τ)‖

private theorem Gammaℝ_line_ne_zero (τ : ℝ) : Gammaℝ (linePt τ) ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos (linePt_re_pos τ)

/-- The archimedean Hardy phase is unitary. -/
theorem gammaHardyPhase_isUnitary (τ : ℝ) : IsUnitaryPhase (gammaHardyPhase τ) := by
  have hG := Gammaℝ_line_ne_zero τ
  have hn : (‖Gammaℝ (linePt τ)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hG)
  unfold IsUnitaryPhase gammaHardyPhase
  rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
  have hnormsq : Gammaℝ (linePt τ) * (starRingEnd ℂ) (Gammaℝ (linePt τ)) =
      (‖Gammaℝ (linePt τ)‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj']
  field_simp
  exact hnormsq

/-- **Exact continuous square root of the zeta reflection phase.** -/
theorem gammaHardyPhase_sq (τ : ℝ) :
    gammaHardyPhase τ * gammaHardyPhase τ = zetaChi (linePt τ) := by
  have hG := Gammaℝ_line_ne_zero τ
  have hn : (‖Gammaℝ (linePt τ)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hG)
  have hnormsq : Gammaℝ (linePt τ) * (starRingEnd ℂ) (Gammaℝ (linePt τ)) =
      (‖Gammaℝ (linePt τ)‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj']
  unfold gammaHardyPhase zetaChi
  rw [← conj_linePt, Gammaℝ_conj]
  field_simp
  calc
    (starRingEnd ℂ) (Gammaℝ (linePt τ)) ^ 2 * Gammaℝ (linePt τ) =
        (starRingEnd ℂ) (Gammaℝ (linePt τ)) *
          (Gammaℝ (linePt τ) * (starRingEnd ℂ) (Gammaℝ (linePt τ))) := by ring
    _ = (starRingEnd ℂ) (Gammaℝ (linePt τ)) *
          (‖Gammaℝ (linePt τ)‖ : ℂ) ^ 2 := by rw [hnormsq]

/-- The normalized phase removes the Gamma factor exactly, leaving its positive norm. -/
theorem Gammaℝ_mul_gammaHardyPhase (τ : ℝ) :
    Gammaℝ (linePt τ) * gammaHardyPhase τ = (‖Gammaℝ (linePt τ)‖ : ℂ) := by
  have hG := Gammaℝ_line_ne_zero τ
  have hn : (‖Gammaℝ (linePt τ)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hG)
  unfold gammaHardyPhase
  have hnormsq : Gammaℝ (linePt τ) * (starRingEnd ℂ) (Gammaℝ (linePt τ)) =
      (‖Gammaℝ (linePt τ)‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj']
  field_simp
  exact hnormsq

/-- Exact Gamma derivative along the critical line, expressed by its logarithmic digamma
velocity. -/
theorem hasDerivAt_Gammaℝ_line (τ : ℝ) :
    HasDerivAt (fun u : ℝ => Gammaℝ (linePt u))
      (Gammaℝ (linePt τ) *
        (Complex.digamma (linePt τ / 2) / 2 - (Real.log Real.pi : ℂ) / 2) * I) τ := by
  have h := (hasDerivAt_Gammaℝ_of_re_pos (linePt_re_pos τ)).comp τ
    (hasDerivAt_linePt τ)
  simpa [Function.comp_def, mul_assoc] using h

/-- The archimedean Gamma factor is differentiable along the whole critical line. -/
theorem differentiable_Gammaℝ_line :
    Differentiable ℝ fun τ : ℝ => Gammaℝ (linePt τ) :=
  fun τ => (hasDerivAt_Gammaℝ_line τ).differentiableAt

/-- The archimedean factor is continuous along the critical line. -/
theorem continuous_Gammaℝ_line : Continuous fun τ : ℝ => Gammaℝ (linePt τ) :=
  differentiable_Gammaℝ_line.continuous

/-- The real logarithmic phase velocity of the normalized Gamma factor.  This is the exact
Riemann--Siegel theta-prime datum in the present normalization. -/
noncomputable def gammaHardyPhaseRate (τ : ℝ) : ℝ :=
  (Complex.digamma (linePt τ / 2)).re / 2 - Real.log Real.pi / 2

/-- **Exact normalized-Gamma phase equation.**  The phase derivative is its value times the purely
imaginary scalar `-i gammaHardyPhaseRate`; the radial Gamma derivative cancels identically. -/
theorem hasDerivAt_gammaHardyPhase (τ : ℝ) :
    HasDerivAt gammaHardyPhase
      (-I * (gammaHardyPhaseRate τ : ℂ) * gammaHardyPhase τ) τ := by
  let L : ℂ := Complex.digamma (linePt τ / 2) / 2 - (Real.log Real.pi : ℂ) / 2
  have hG : HasDerivAt (fun u : ℝ => Gammaℝ (linePt u))
      (Gammaℝ (linePt τ) * L * I) τ := by
    simpa [L] using hasDerivAt_Gammaℝ_line τ
  have h := hasDerivAt_normalizedConjPhase hG (Gammaℝ_line_ne_zero τ)
  unfold gammaHardyPhase
  convert h using 1
  have hG0 := Gammaℝ_line_ne_zero τ
  have hquot : Gammaℝ (linePt τ) * L * I / Gammaℝ (linePt τ) = L * I := by
    field_simp [hG0]
  rw [hquot]
  have him : (L * I).im = L.re := by simp
  rw [him]
  congr 2
  norm_cast
  simp [gammaHardyPhaseRate, L]

/-- The derivative of the normalized Gamma phase in closed logarithmic form. -/
theorem deriv_gammaHardyPhase (τ : ℝ) :
    deriv gammaHardyPhase τ =
      -I * (gammaHardyPhaseRate τ : ℂ) * gammaHardyPhase τ :=
  (hasDerivAt_gammaHardyPhase τ).deriv

/-- The normalized Gamma phase is globally differentiable; nonvanishing of Gamma discharges the
only norm-denominator premise. -/
theorem differentiable_gammaHardyPhase : Differentiable ℝ gammaHardyPhase :=
  fun τ => (hasDerivAt_gammaHardyPhase τ).differentiableAt

/-- The normalized Gamma phase is globally continuous. -/
theorem continuous_gammaHardyPhase : Continuous gammaHardyPhase :=
  differentiable_gammaHardyPhase.continuous

/-- Negating the height conjugates the canonical Hardy phase. -/
@[simp] theorem gammaHardyPhase_neg (τ : ℝ) :
    gammaHardyPhase (-τ) = (starRingEnd ℂ) (gammaHardyPhase τ) := by
  unfold gammaHardyPhase
  rw [linePt_neg, Gammaℝ_conj, map_div₀,
    Complex.conj_conj, Complex.norm_conj, Complex.conj_ofReal]

/-- The first-jet conjugate reflection for the normalized Gamma phase. -/
@[simp] theorem deriv_gammaHardyPhase_neg (τ : ℝ) :
    deriv gammaHardyPhase (-τ) = -(starRingEnd ℂ) (deriv gammaHardyPhase τ) :=
  deriv_neg_eq_neg_conj_of_conj_neg gammaHardyPhase_neg
    differentiable_gammaHardyPhase τ

/-- The normalized Gamma phase velocity is even.  This is obtained from the phase-value
reflection and its differentiated reflection, without a separate digamma conjugation premise. -/
@[simp] theorem gammaHardyPhaseRate_neg (τ : ℝ) :
    gammaHardyPhaseRate (-τ) = gammaHardyPhaseRate τ := by
  have hd := deriv_gammaHardyPhase_neg τ
  rw [deriv_gammaHardyPhase, deriv_gammaHardyPhase, gammaHardyPhase_neg,
    map_mul, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal] at hd
  have hphase0 : (starRingEnd ℂ) (gammaHardyPhase τ) ≠ 0 := by
    simpa using (gammaHardyPhase_isUnitary τ).ne_zero
  have hcancel : (-I) * (gammaHardyPhaseRate (-τ) : ℂ) =
      (-I) * (gammaHardyPhaseRate τ : ℂ) :=
    mul_right_cancel₀ hphase0 (by simpa [mul_assoc] using hd)
  have hi : (-I : ℂ) ≠ 0 := by norm_num
  have hcast := mul_left_cancel₀ hi hcancel
  exact_mod_cast hcast

/-! ## A continuous orientation of the finite Hardy carrier -/

/-- The principal-log finite phase and the continuous Gamma phase are the two possible square
roots of the same reflection multiplier, so they differ pointwise by exactly one sign. -/
theorem hardyPhase_eq_or_eq_neg_gammaHardyPhase (τ : ℝ) :
    hardyPhase τ = gammaHardyPhase τ ∨ hardyPhase τ = -gammaHardyPhase τ := by
  apply eq_or_eq_neg_of_sq_eq_sq
  simp only [pow_two, hardyPhase_sq, gammaHardyPhase_sq]

/-- The finite Riemann--Siegel carrier also satisfies the reflection Prop interface for the
continuous Gamma phase, independently of the principal-log square-root branch. -/
theorem gN_line_isGammaPhaseReflected (N : ℕ) (τ : ℝ) :
    IsPhaseReflected (gammaHardyPhase τ) (gN N (linePt τ)) := by
  unfold IsPhaseReflected
  rw [gammaHardyPhase_sq]
  exact zetaChi_mul_conj_gN_line N τ

/-- The globally oriented finite Hardy carrier obtained from the continuous Gamma phase.  Unlike
`hardyCarrier`, this real amplitude itself is continuous; their squares remain identical. -/
noncomputable def gammaHardyCarrier (N : ℕ) (τ : ℝ) : ℝ :=
  phaseHalvedAmplitude (gammaHardyPhase τ) (gN N (linePt τ))

/-- Exact polar decomposition of the finite carrier using the continuous Gamma phase. -/
theorem gN_line_eq_gammaHardyPhase_mul_gammaHardyCarrier (N : ℕ) (τ : ℝ) :
    gN N (linePt τ) = gammaHardyPhase τ * (gammaHardyCarrier N τ : ℂ) := by
  exact (gN_line_isGammaPhaseReflected N τ).eq_phase_mul_amplitude
    (gammaHardyPhase_isUnitary τ)

/-- The finite carrier modulus is the absolute continuous Gamma-oriented amplitude. -/
theorem norm_gN_line_eq_abs_gammaHardyCarrier (N : ℕ) (τ : ℝ) :
    ‖gN N (linePt τ)‖ = |gammaHardyCarrier N τ| := by
  exact (gN_line_isGammaPhaseReflected N τ).norm_eq_abs_amplitude
    (gammaHardyPhase_isUnitary τ)

/-- Exact zero interface for the continuously oriented finite Hardy carrier. -/
theorem gN_line_eq_zero_iff_gammaHardyCarrier (N : ℕ) (τ : ℝ) :
    gN N (linePt τ) = 0 ↔ gammaHardyCarrier N τ = 0 := by
  exact (gN_line_isGammaPhaseReflected N τ).eq_zero_iff_amplitude_eq_zero
    (gammaHardyPhase_isUnitary τ)

/-- The Gamma-oriented finite Hardy carrier is globally differentiable at every truncation
length. -/
theorem differentiable_gammaHardyCarrier (N : ℕ) :
    Differentiable ℝ (gammaHardyCarrier N) :=
  differentiable_phaseHalvedAmplitude differentiable_gammaHardyPhase
    (differentiable_gN_line N)

/-- The Gamma-oriented finite Hardy carrier is globally continuous at every truncation length. -/
theorem continuous_gammaHardyCarrier (N : ℕ) : Continuous (gammaHardyCarrier N) :=
  (differentiable_gammaHardyCarrier N).continuous

/-- The continuously oriented finite Hardy carrier is even in the height. -/
@[simp] theorem gammaHardyCarrier_neg (N : ℕ) (τ : ℝ) :
    gammaHardyCarrier N (-τ) = gammaHardyCarrier N τ := by
  unfold gammaHardyCarrier
  rw [gammaHardyPhase_neg, gN_line_neg, phaseHalvedAmplitude_conj]

/-- Prop interface for the finite continuous-Hardy height reflection. -/
theorem even_gammaHardyCarrier (N : ℕ) : Function.Even (gammaHardyCarrier N) :=
  fun τ => gammaHardyCarrier_neg N τ

/-- The principal-log and continuous finite Hardy amplitudes differ pointwise only by the sign of
their square-root phases. -/
theorem hardyCarrier_eq_or_eq_neg_gammaHardyCarrier (N : ℕ) (τ : ℝ) :
    hardyCarrier N τ = gammaHardyCarrier N τ ∨
      hardyCarrier N τ = -gammaHardyCarrier N τ := by
  rcases hardyPhase_eq_or_eq_neg_gammaHardyPhase τ with hphase | hphase
  · left
    unfold hardyCarrier gammaHardyCarrier phaseHalvedAmplitude
    rw [hphase]
  · right
    unfold hardyCarrier gammaHardyCarrier phaseHalvedAmplitude
    rw [hphase, map_neg, neg_mul, Complex.neg_re]

/-- Squaring removes precisely the principal-log sign ambiguity and recovers the continuous
Gamma-oriented finite amplitude. -/
theorem hardyCarrier_sq_eq_gammaHardyCarrier_sq (N : ℕ) (τ : ℝ) :
    (hardyCarrier N τ) ^ 2 = (gammaHardyCarrier N τ) ^ 2 := by
  rcases hardyCarrier_eq_or_eq_neg_gammaHardyCarrier N τ with h | h <;> simp [h]

/-- **Archimedean scale law for every reflected value.**  Multiplying any value carrying the
continuous Gamma reflection phase by the completed archimedean factor removes the phase and
leaves one explicit real scale times its real amplitude.  This single law covers both Xi/Hardy Z
and the completed finite carrier. -/
theorem archFactor_mul_phaseReflected_eq_realScale (τ : ℝ) {z : ℂ}
    (hz : IsPhaseReflected (gammaHardyPhase τ) z) :
    archFactor (linePt τ) * z =
      (((-(1 / 4 + τ ^ 2) / 2) * ‖Gammaℝ (linePt τ)‖ *
        phaseHalvedAmplitude (gammaHardyPhase τ) z : ℝ) : ℂ) := by
  let A := phaseHalvedAmplitude (gammaHardyPhase τ) z
  have hzform : z = gammaHardyPhase τ * (A : ℂ) := by
    simpa [A] using hz.eq_phase_mul_amplitude (gammaHardyPhase_isUnitary τ)
  change archFactor (linePt τ) * z =
    (((-(1 / 4 + τ ^ 2) / 2) * ‖Gammaℝ (linePt τ)‖ * A : ℝ) : ℂ)
  rw [hzform]
  have hpoly : linePt τ * (linePt τ - 1) / 2 =
      ((-(1 / 4 + τ ^ 2) / 2 : ℝ) : ℂ) := by
    unfold linePt
    push_cast
    ring_nf
    rw [I_sq]
    ring
  unfold archFactor
  rw [hpoly]
  calc
    ((-(1 / 4 + τ ^ 2) / 2 : ℝ) : ℂ) * Gammaℝ (linePt τ) *
          (gammaHardyPhase τ * (A : ℂ)) =
        ((-(1 / 4 + τ ^ 2) / 2 : ℝ) : ℂ) *
          (Gammaℝ (linePt τ) * gammaHardyPhase τ) * (A : ℂ) := by ring
    _ = ((-(1 / 4 + τ ^ 2) / 2 : ℝ) : ℂ) *
          (‖Gammaℝ (linePt τ)‖ : ℂ) * (A : ℂ) := by
              rw [Gammaℝ_mul_gammaHardyPhase]
    _ = (((-(1 / 4 + τ ^ 2) / 2) * ‖Gammaℝ (linePt τ)‖ *
          A : ℝ) : ℂ) := by
            push_cast
            ring

/-- Exact real-scale form of the completed finite carrier on the critical line. -/
theorem completedGN_line_eq_scale_mul_gammaHardyCarrier (N : ℕ) (τ : ℝ) :
    completedGN N (linePt τ) =
      (((-(1 / 4 + τ ^ 2) / 2) * ‖Gammaℝ (linePt τ)‖ *
        gammaHardyCarrier N τ : ℝ) : ℂ) := by
  unfold completedGN
  simpa [gammaHardyCarrier] using
    archFactor_mul_phaseReflected_eq_realScale τ (gN_line_isGammaPhaseReflected N τ)

/-- Completed and raw finite-carrier zeros are exactly the zeros of the continuous real
Gamma-oriented amplitude on the critical line. -/
theorem completedGN_line_eq_zero_iff_gammaHardyCarrier (N : ℕ) (τ : ℝ) :
    completedGN N (linePt τ) = 0 ↔ gammaHardyCarrier N τ = 0 := by
  unfold completedGN
  rw [mul_eq_zero, gN_line_eq_zero_iff_gammaHardyCarrier]
  exact or_iff_right
    (archFactor_ne_zero (linePt_ne_zero τ) (linePt_ne_one τ) (Gammaℝ_line_ne_zero τ))

/-! ## Critical-line zeta value reflection and the real Hardy amplitude -/

/-- Negating the height conjugates the critical-line zeta value. -/
@[simp] theorem riemannZeta_line_neg (τ : ℝ) :
    riemannZeta (linePt (-τ)) = (starRingEnd ℂ) (riemannZeta (linePt τ)) := by
  rw [linePt_neg]
  exact riemannZeta_conj_of_re_pos (linePt_re_pos τ) (linePt_ne_one τ)

/-- **Exact critical-line zeta value reflection.**  This is the zeta analogue of the finite
carrier law `zetaChi_mul_conj_gN_line`, now obtained without assuming zeta is nonzero. -/
theorem zetaChi_mul_conj_riemannZeta_line (τ : ℝ) :
    zetaChi (linePt τ) * (starRingEnd ℂ) (riemannZeta (linePt τ)) =
      riemannZeta (linePt τ) := by
  have hconj : riemannZeta ((starRingEnd ℂ) (linePt τ)) =
      (starRingEnd ℂ) (riemannZeta (linePt τ)) :=
    riemannZeta_conj_of_re_pos (linePt_re_pos τ) (linePt_ne_one τ)
  rw [← hconj, conj_linePt]
  exact (zeta_eq_zetaChi_mul (linePt_ne_zero τ) (linePt_ne_one τ)
    (Gammaℝ_ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.one_re, linePt_re]
      norm_num))).symm

/-- The critical-line zeta value satisfies the Prop interface consumed by unitary phase halving. -/
theorem riemannZeta_line_isPhaseReflected (τ : ℝ) :
    IsPhaseReflected (gammaHardyPhase τ) (riemannZeta (linePt τ)) := by
  unfold IsPhaseReflected
  rw [gammaHardyPhase_sq]
  exact zetaChi_mul_conj_riemannZeta_line τ

/-- **Hardy's real Z-function.**  This definition uses the canonical continuous Gamma phase, not a
principal logarithm, so the real amplitude is continuous with no sign-branch hypothesis. -/
noncomputable def hardyZ (τ : ℝ) : ℝ :=
  phaseHalvedAmplitude (gammaHardyPhase τ) (riemannZeta (linePt τ))

/-- **Height reflection for Hardy Z.**  Conjugation of both the canonical phase and zeta value
shows that Hardy Z is globally even, including at zeros, without comparing logarithmic branches. -/
@[simp] theorem hardyZ_neg (τ : ℝ) : hardyZ (-τ) = hardyZ τ := by
  unfold hardyZ
  rw [gammaHardyPhase_neg, riemannZeta_line_neg, phaseHalvedAmplitude_conj]

/-- Prop interface for the global Hardy-Z height reflection. -/
theorem even_hardyZ : Function.Even hardyZ := fun τ => hardyZ_neg τ

/-- Removing the Gamma phase from zeta gives the embedded real Hardy value exactly. -/
theorem conj_gammaHardyPhase_mul_zeta_eq_hardyZ (τ : ℝ) :
    (starRingEnd ℂ) (gammaHardyPhase τ) * riemannZeta (linePt τ) = (hardyZ τ : ℂ) := by
  exact (riemannZeta_line_isPhaseReflected τ).conj_mul_eq_ofReal_amplitude
    (gammaHardyPhase_isUnitary τ)

/-- **Exact polar decomposition of zeta on the critical line.** -/
theorem riemannZeta_line_eq_gammaHardyPhase_mul_hardyZ (τ : ℝ) :
    riemannZeta (linePt τ) = gammaHardyPhase τ * (hardyZ τ : ℂ) := by
  exact (riemannZeta_line_isPhaseReflected τ).eq_phase_mul_amplitude
    (gammaHardyPhase_isUnitary τ)

/-- **Exact zeta/finite-carrier error isometry.**  On the critical line, the complex discrepancy
between zeta and the Riemann--Siegel carrier is exactly the absolute discrepancy of their two
Gamma-oriented real amplitudes.  No accuracy estimate for `gN` is asserted. -/
theorem norm_riemannZeta_line_sub_gN_eq_abs_hardyZ_sub_gammaHardyCarrier
    (N : ℕ) (τ : ℝ) :
    ‖riemannZeta (linePt τ) - gN N (linePt τ)‖ =
      |hardyZ τ - gammaHardyCarrier N τ| := by
  simpa [hardyZ, gammaHardyCarrier] using
    IsPhaseReflected.norm_real_mul_sub_real_mul_eq_abs_amplitude_sub
      (gammaHardyPhase_isUnitary τ) (riemannZeta_line_isPhaseReflected τ)
        (gN_line_isGammaPhaseReflected N τ) 1 1

/-- **Exact Xi/Hardy-Z value bridge.**  Xi is a strictly nonzero real archimedean scale times
`hardyZ`; this connects the corpus's Xi real-structure layer directly to the zeta moment layer. -/
theorem xi_line_eq_scale_mul_hardyZ (τ : ℝ) :
    xi (linePt τ) =
      (((-(1 / 4 + τ ^ 2) / 2) * ‖Gammaℝ (linePt τ)‖ * hardyZ τ : ℝ) : ℂ) := by
  rw [xi_eq_archFactor_mul_zeta (linePt_ne_zero τ) (linePt_ne_one τ)
      (Gammaℝ_line_ne_zero τ)]
  simpa [hardyZ] using
    archFactor_mul_phaseReflected_eq_realScale τ (riemannZeta_line_isPhaseReflected τ)

/-- **Unconditional Hardy-Z sign anchor.**  The coefficient-side positivity of Xi at the real
centre and the negative archimedean scale force `hardyZ(0) < 0`.  This supplies the fixed starting
sign for future critical-line sign-change arguments. -/
theorem hardyZ_zero_height_neg : hardyZ 0 < 0 := by
  have hline0 : linePt 0 = (((1 / 2 : ℝ) : ℝ) : ℂ) := by
    unfold linePt
    push_cast
    ring
  have hxi : 0 < (xi (linePt 0)).re := by
    rw [hline0]
    exact xi_pos_on_real_anchor (by norm_num) (by norm_num)
  have hG : 0 < ‖Gammaℝ (linePt 0)‖ := norm_pos_iff.mpr (Gammaℝ_line_ne_zero 0)
  have hvalue := congrArg Complex.re (xi_line_eq_scale_mul_hardyZ 0)
  rw [Complex.ofReal_re] at hvalue
  norm_num at hvalue
  nlinarith

/-- Zeta's critical-line modulus is exactly the absolute Hardy amplitude. -/
theorem norm_riemannZeta_line_eq_abs_hardyZ (τ : ℝ) :
    ‖riemannZeta (linePt τ)‖ = |hardyZ τ| := by
  exact (riemannZeta_line_isPhaseReflected τ).norm_eq_abs_amplitude
    (gammaHardyPhase_isUnitary τ)

/-- **Exact zeta-zero/Hardy-Z interface.** -/
theorem riemannZeta_line_eq_zero_iff_hardyZ (τ : ℝ) :
    riemannZeta (linePt τ) = 0 ↔ hardyZ τ = 0 := by
  exact (riemannZeta_line_isPhaseReflected τ).eq_zero_iff_amplitude_eq_zero
    (gammaHardyPhase_isUnitary τ)

/-- **Exact Xi-zero/Hardy-Z interface.** -/
theorem xi_line_eq_zero_iff_hardyZ (τ : ℝ) :
    xi (linePt τ) = 0 ↔ hardyZ τ = 0 := by
  exact (xi_eq_zero_iff (linePt_re_pos τ) (linePt_ne_one τ)).trans
    (riemannZeta_line_eq_zero_iff_hardyZ τ)

/-- Squaring removes the real sign and gives the zeta modulus square exactly. -/
theorem hardyZ_sq_eq_norm_riemannZeta_line_sq (τ : ℝ) :
    (hardyZ τ) ^ 2 = ‖riemannZeta (linePt τ)‖ ^ 2 := by
  calc
    (hardyZ τ) ^ 2 = |hardyZ τ| ^ 2 := by rw [sq_abs]
    _ = ‖riemannZeta (linePt τ)‖ ^ 2 := by
      rw [norm_riemannZeta_line_eq_abs_hardyZ]

/-! ## Differentiability, continuity, and moment interfaces -/

/-- Zeta is differentiable along the whole critical line. -/
theorem differentiable_riemannZeta_line :
    Differentiable ℝ fun τ : ℝ => riemannZeta (linePt τ) := by
  intro τ
  have hzeta : DifferentiableAt ℝ riemannZeta (linePt τ) :=
    (differentiableAt_riemannZeta (linePt_ne_one τ)).restrictScalars ℝ
  exact hzeta.comp τ (hasDerivAt_linePt τ).differentiableAt

/-- Zeta is continuous along the critical line. -/
theorem continuous_riemannZeta_line : Continuous fun τ : ℝ => riemannZeta (linePt τ) :=
  differentiable_riemannZeta_line.continuous

/-- **Hardy Z is globally differentiable.**  The canonical Gamma orientation upgrades the usual
continuity interface to real differentiability without any nonvanishing premise on zeta. -/
theorem differentiable_hardyZ : Differentiable ℝ hardyZ :=
  differentiable_phaseHalvedAmplitude differentiable_gammaHardyPhase
    differentiable_riemannZeta_line

/-- The first-jet height reflection for Hardy Z. -/
@[simp] theorem deriv_hardyZ_neg (τ : ℝ) : deriv hardyZ (-τ) = -deriv hardyZ τ :=
  deriv_neg_of_even even_hardyZ differentiable_hardyZ τ

/-- The critical-line reflection centre is a stationary point of Hardy Z. -/
@[simp] theorem deriv_hardyZ_zero : deriv hardyZ 0 = 0 :=
  deriv_zero_of_even even_hardyZ differentiable_hardyZ

/-- The first-jet height reflection for every continuously oriented finite carrier. -/
@[simp] theorem deriv_gammaHardyCarrier_neg (N : ℕ) (τ : ℝ) :
    deriv (gammaHardyCarrier N) (-τ) = -deriv (gammaHardyCarrier N) τ :=
  deriv_neg_of_even (even_gammaHardyCarrier N) (differentiable_gammaHardyCarrier N) τ

/-- Every continuously oriented finite carrier is stationary at the reflection centre. -/
@[simp] theorem deriv_gammaHardyCarrier_zero (N : ℕ) :
    deriv (gammaHardyCarrier N) 0 = 0 :=
  deriv_zero_of_even (even_gammaHardyCarrier N) (differentiable_gammaHardyCarrier N)

/-- **Hardy Z is globally continuous.**  The proof uses the explicit continuous Gamma phase and
therefore discharges the branch-continuity premise required by sign-change arguments. -/
theorem continuous_hardyZ : Continuous hardyZ := differentiable_hardyZ.continuous

/-- The squared Hardy amplitude is interval-integrable on every finite window, the direct interface
for critical-line second-moment arguments. -/
theorem intervalIntegrable_hardyZ_sq (T U : ℝ) :
    IntervalIntegrable (fun τ : ℝ => (hardyZ τ) ^ 2)
      MeasureTheory.volume T (T + U) := by
  exact (continuous_hardyZ.pow 2).intervalIntegrable T (T + U)

/-! ## A real symmetrized Euler--Maclaurin approximation -/

/-- The symmetrized Euler--Maclaurin carrier obeys the same exact critical-line value reflection
as zeta. -/
theorem zetaChi_mul_conj_semCarrier_line (N : ℕ) (τ : ℝ) :
    zetaChi (linePt τ) * (starRingEnd ℂ) (semCarrier N (linePt τ)) =
      semCarrier N (linePt τ) := by
  have hconj : (starRingEnd ℂ) (semCarrier N (linePt τ)) =
      semCarrier N (1 - linePt τ) := by
    rw [← conj_linePt, semCarrier_conj]
  rw [hconj, semCarrier_one_sub (linePt_re_pos τ) (linePt_re_lt_one τ), ← mul_assoc,
    zetaChi_mul_one_sub_of_mem_strip (linePt_re_pos τ) (linePt_re_lt_one τ), one_mul]

/-- The symmetrized Euler--Maclaurin carrier satisfies the shared unitary phase-reflection Prop
interface at every truncation length. -/
theorem semCarrier_line_isPhaseReflected (N : ℕ) (τ : ℝ) :
    IsPhaseReflected (gammaHardyPhase τ) (semCarrier N (linePt τ)) := by
  unfold IsPhaseReflected
  rw [gammaHardyPhase_sq]
  exact zetaChi_mul_conj_semCarrier_line N τ

/-- Negating the height conjugates every symmetrized Euler--Maclaurin carrier value. -/
@[simp] theorem semCarrier_line_neg (N : ℕ) (τ : ℝ) :
    semCarrier N (linePt (-τ)) = (starRingEnd ℂ) (semCarrier N (linePt τ)) := by
  rw [linePt_neg, semCarrier_conj]

/-- The real phase-halved symmetrized Euler--Maclaurin approximation to `hardyZ`.  The factor
`1/2` matches `semCarrier N`'s target `2 * zeta`. -/
noncomputable def hardySEM (N : ℕ) (τ : ℝ) : ℝ :=
  phaseHalvedAmplitude (gammaHardyPhase τ) (semCarrier N (linePt τ)) / 2

/-- Every real symmetrized Euler--Maclaurin Hardy approximant is even. -/
@[simp] theorem hardySEM_neg (N : ℕ) (τ : ℝ) : hardySEM N (-τ) = hardySEM N τ := by
  unfold hardySEM
  rw [gammaHardyPhase_neg, semCarrier_line_neg, phaseHalvedAmplitude_conj]

/-- Prop interface for the symmetrized-EM height reflection. -/
theorem even_hardySEM (N : ℕ) : Function.Even (hardySEM N) := fun τ => hardySEM_neg N τ

/-- Exact polar decomposition of the symmetrized Euler--Maclaurin carrier on the line. -/
theorem semCarrier_line_eq_two_mul_gammaHardyPhase_mul_hardySEM (N : ℕ) (τ : ℝ) :
    semCarrier N (linePt τ) = gammaHardyPhase τ * (2 * hardySEM N τ : ℝ) := by
  rw [(semCarrier_line_isPhaseReflected N τ).eq_phase_mul_amplitude
    (gammaHardyPhase_isUnitary τ)]
  unfold hardySEM
  push_cast
  ring

/-- **Normalized zeta/symmetrized-EM isometry.**  Dividing the carrier by its target factor two
identifies the complex approximation error exactly with the real Hardy-amplitude error. -/
theorem norm_riemannZeta_line_sub_half_semCarrier_eq_abs_hardyZ_sub_hardySEM
    (N : ℕ) (τ : ℝ) :
    ‖riemannZeta (linePt τ) - semCarrier N (linePt τ) / 2‖ =
      |hardyZ τ - hardySEM N τ| := by
  simpa [hardyZ, hardySEM, div_eq_mul_inv, mul_comm] using
    IsPhaseReflected.norm_real_mul_sub_real_mul_eq_abs_amplitude_sub
      (gammaHardyPhase_isUnitary τ) (riemannZeta_line_isPhaseReflected τ)
        (semCarrier_line_isPhaseReflected N τ) 1 (1 / 2)

/-- **Finite-carrier comparison isometry.**  The discrepancy between `gN` and the normalized
symmetrized-EM carrier is likewise exactly one real Gamma-oriented amplitude discrepancy. -/
theorem norm_gN_line_sub_half_semCarrier_eq_abs_gammaHardyCarrier_sub_hardySEM
    (N M : ℕ) (τ : ℝ) :
    ‖gN N (linePt τ) - semCarrier M (linePt τ) / 2‖ =
      |gammaHardyCarrier N τ - hardySEM M τ| := by
  simpa [gammaHardyCarrier, hardySEM, div_eq_mul_inv, mul_comm] using
    IsPhaseReflected.norm_real_mul_sub_real_mul_eq_abs_amplitude_sub
      (gammaHardyPhase_isUnitary τ) (gN_line_isGammaPhaseReflected N τ)
        (semCarrier_line_isPhaseReflected M τ) 1 (1 / 2)

/-- **Exact real/complex approximation isometry.**  The complex symmetrized-carrier error is
exactly twice the absolute error of the real Hardy amplitudes. -/
theorem two_mul_abs_hardyZ_sub_hardySEM_eq_norm (N : ℕ) (τ : ℝ) :
    2 * |hardyZ τ - hardySEM N τ| =
      ‖2 * riemannZeta (linePt τ) - semCarrier N (linePt τ)‖ := by
  have hnorm := IsPhaseReflected.norm_real_mul_sub_real_mul_eq_abs_amplitude_sub
    (gammaHardyPhase_isUnitary τ) (riemannZeta_line_isPhaseReflected τ)
      (semCarrier_line_isPhaseReflected N τ) 2 1
  change 2 * |phaseHalvedAmplitude (gammaHardyPhase τ) (riemannZeta (linePt τ)) -
      phaseHalvedAmplitude (gammaHardyPhase τ) (semCarrier N (linePt τ)) / 2| =
    ‖2 * riemannZeta (linePt τ) - semCarrier N (linePt τ)‖
  calc
    2 * |phaseHalvedAmplitude (gammaHardyPhase τ) (riemannZeta (linePt τ)) -
        phaseHalvedAmplitude (gammaHardyPhase τ) (semCarrier N (linePt τ)) / 2| =
      |2 * phaseHalvedAmplitude (gammaHardyPhase τ) (riemannZeta (linePt τ)) -
        1 * phaseHalvedAmplitude (gammaHardyPhase τ) (semCarrier N (linePt τ))| := by
          rw [show (2 : ℝ) = |2| by norm_num, ← abs_mul]
          congr 1
          ring
    _ = ‖2 * riemannZeta (linePt τ) - semCarrier N (linePt τ)‖ := by
      simpa using hnorm.symm

/-- The explicit pointwise error budget between the actual Hardy Z and its real symmetrized
Euler--Maclaurin approximation. -/
noncomputable def hardySEMError (N : ℕ) (τ : ℝ) : ℝ :=
  2 * ‖linePt τ‖ * (N : ℝ) ^ (-(1 / 2 : ℝ))

/-- The explicit symmetrized-EM error budget is nonnegative at every level and height. -/
theorem hardySEMError_nonneg (N : ℕ) (τ : ℝ) : 0 ≤ hardySEMError N τ := by
  unfold hardySEMError
  positivity

/-- The explicit finite-approximation error budget respects height reflection. -/
@[simp] theorem hardySEMError_neg (N : ℕ) (τ : ℝ) :
    hardySEMError N (-τ) = hardySEMError N τ := by
  unfold hardySEMError
  rw [linePt_neg, Complex.norm_conj]

/-- **Unconditional real Hardy-Z approximation.**  The machine-checked symmetrized
Euler--Maclaurin error transfers through the common unitary phase with no loss except division by
two. -/
theorem abs_hardyZ_sub_hardySEM_le {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    |hardyZ τ - hardySEM N τ| ≤ hardySEMError N τ := by
  have hbound := two_zeta_sub_semCarrier_norm_le hN
    (linePt_re_pos τ) (linePt_re_lt_one τ)
  rw [← two_mul_abs_hardyZ_sub_hardySEM_eq_norm] at hbound
  have hsymmetric : ‖1 - linePt τ‖ = ‖linePt τ‖ := by
    rw [← conj_linePt, Complex.norm_conj]
  rw [linePt_re, Complex.sub_re, Complex.one_re, linePt_re,
    norm_zetaChi_line, hsymmetric] at hbound
  unfold hardySEMError
  norm_num at hbound ⊢
  linarith

/-- The symmetrized Euler--Maclaurin carrier is differentiable along the critical line whenever its
nontrivial truncation premise holds. -/
theorem differentiable_semCarrier_line {N : ℕ} (hN : 1 ≤ N) :
    Differentiable ℝ fun τ : ℝ => semCarrier N (linePt τ) := by
  intro τ
  have hsem : DifferentiableAt ℝ (semCarrier N) (linePt τ) :=
    (semCarrier_analyticAt hN (linePt_re_pos τ)
      (linePt_re_lt_one τ)).differentiableAt.restrictScalars ℝ
  exact hsem.comp τ (hasDerivAt_linePt τ).differentiableAt

/-- The symmetrized Euler--Maclaurin carrier is continuous along the critical line. -/
theorem continuous_semCarrier_line {N : ℕ} (hN : 1 ≤ N) :
    Continuous fun τ : ℝ => semCarrier N (linePt τ) :=
  (differentiable_semCarrier_line hN).continuous

/-- Every nontrivial real symmetrized Euler--Maclaurin approximation is differentiable. -/
theorem differentiable_hardySEM {N : ℕ} (hN : 1 ≤ N) :
    Differentiable ℝ (hardySEM N) := by
  have hAmplitude := differentiable_phaseHalvedAmplitude differentiable_gammaHardyPhase
    (differentiable_semCarrier_line hN)
  exact hAmplitude.div_const 2

/-- The first-jet height reflection for every nontrivial symmetrized-EM Hardy approximant. -/
@[simp] theorem deriv_hardySEM_neg {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    deriv (hardySEM N) (-τ) = -deriv (hardySEM N) τ :=
  deriv_neg_of_even (even_hardySEM N) (differentiable_hardySEM hN) τ

/-- Every nontrivial symmetrized-EM Hardy approximant is stationary at the reflection centre. -/
@[simp] theorem deriv_hardySEM_zero {N : ℕ} (hN : 1 ≤ N) :
    deriv (hardySEM N) 0 = 0 :=
  deriv_zero_of_even (even_hardySEM N) (differentiable_hardySEM hN)

/-- Every nontrivial real symmetrized Euler--Maclaurin approximation is continuous. -/
theorem continuous_hardySEM {N : ℕ} (hN : 1 ≤ N) : Continuous (hardySEM N) :=
  (differentiable_hardySEM hN).continuous

private theorem tendsto_const_mul_nat_rpow_neg_half (C : ℝ) :
    Filter.Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(1 / 2 : ℝ)))
      Filter.atTop (𝓝 0) := by
  have hpow : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 : ℝ)))
      Filter.atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  simpa using hpow.const_mul C

/-- The explicit finite-approximation error budget tends to zero at every fixed height. -/
theorem hardySEMError_tendsto_zero (τ : ℝ) :
    Filter.Tendsto (fun N : ℕ => hardySEMError N τ) Filter.atTop (𝓝 0) := by
  simpa [hardySEMError] using
    tendsto_const_mul_nat_rpow_neg_half (2 * ‖linePt τ‖)

/-- **Pointwise convergence of the real symmetrized-EM approximants.**  At every fixed height,
the explicit `N⁻¹ᐟ²` error forces `hardySEM N` to converge to the actual Hardy Z value. -/
theorem hardySEM_tendsto_hardyZ (τ : ℝ) :
    Filter.Tendsto (fun N : ℕ => hardySEM N τ) Filter.atTop (𝓝 (hardyZ τ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hmajor : Filter.Tendsto
      (fun N : ℕ => 2 * ‖linePt τ‖ * (N : ℝ) ^ (-(1 / 2 : ℝ)))
      Filter.atTop (𝓝 0) := tendsto_const_mul_nat_rpow_neg_half _
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg)
    (Filter.eventually_atTop.mpr ⟨1, fun N hN => ?_⟩) hmajor
  rw [Real.dist_eq, abs_sub_comm]
  simpa [hardySEMError] using abs_hardyZ_sub_hardySEM_le hN τ

/-- **Uniform convergence on every symmetric compact height window.**  The same explicit error
is uniform on `[-R,R]` because `‖1/2+iτ‖ ≤ 1/2+R` there. -/
theorem hardySEM_tendstoUniformlyOn_Icc (R : ℝ) :
    TendstoUniformlyOn (fun N : ℕ => hardySEM N) hardyZ Filter.atTop
      (Set.Icc (-R) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hmajor : Filter.Tendsto
      (fun N : ℕ => 2 * (1 / 2 + R) * (N : ℝ) ^ (-(1 / 2 : ℝ)))
      Filter.atTop (𝓝 0) := tendsto_const_mul_nat_rpow_neg_half _
  filter_upwards [hmajor.eventually (gt_mem_nhds hε), Filter.eventually_ge_atTop 1]
    with N hNε hN τ hτ
  rw [Real.dist_eq]
  calc
    |hardyZ τ - hardySEM N τ| ≤
        2 * ‖linePt τ‖ * (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
      by simpa [hardySEMError] using abs_hardyZ_sub_hardySEM_le hN τ
    _ ≤ 2 * (1 / 2 + R) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have habs : |τ| ≤ R := abs_le.mpr hτ
      have hnorm : ‖linePt τ‖ ≤ 1 / 2 + R := by
        unfold linePt
        calc
          ‖((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I‖ ≤
              ‖((1 / 2 : ℝ) : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
          _ = 1 / 2 + |τ| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
              mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          _ ≤ 1 / 2 + R := by linarith
      gcongr
    _ < ε := hNε

/-! ## Exact finite-tower zero and nonvanishing interfaces -/

/-- **Asymptotic completeness of the finite margin certificate.**  At every nonzero actual Hardy
value, all sufficiently large symmetrized-EM approximants clear their explicit error budget. -/
theorem eventually_hardySEMError_lt_abs_of_hardyZ_ne_zero
    {τ : ℝ} (hZ : hardyZ τ ≠ 0) :
    ∀ᶠ N : ℕ in atTop, hardySEMError N τ < |hardySEM N τ| := by
  have hZabs : 0 < |hardyZ τ| := abs_pos.mpr hZ
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (hardySEM_tendsto_hardyZ τ)
    (|hardyZ τ| / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp (hardySEMError_tendsto_zero τ)
    (|hardyZ τ| / 4) (by positivity)
  filter_upwards [eventually_ge_atTop (max N₁ N₂)] with N hN
  have hdist := hN₁ N (le_trans (le_max_left _ _) hN)
  rw [Real.dist_eq] at hdist
  have herror := hN₂ N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg] at herror
  · have htri : |hardyZ τ| ≤ |hardyZ τ - hardySEM N τ| + |hardySEM N τ| := by
      calc
        |hardyZ τ| = |(hardyZ τ - hardySEM N τ) + hardySEM N τ| := by
          rw [sub_add_cancel]
        _ ≤ |hardyZ τ - hardySEM N τ| + |hardySEM N τ| := abs_add_le _ _
    rw [abs_sub_comm] at hdist
    nlinarith
  · exact hardySEMError_nonneg N τ

/-- A finite value that clears its explicit error budget certifies zeta nonvanishing at that
critical-line height. -/
theorem riemannZeta_line_ne_zero_of_hardySEM_error_lt_abs
    {N : ℕ} (hN : 1 ≤ N) {τ : ℝ}
    (hmargin : hardySEMError N τ < |hardySEM N τ|) :
    riemannZeta (linePt τ) ≠ 0 := by
  intro hzeta
  have hZ : hardyZ τ = 0 := (riemannZeta_line_eq_zero_iff_hardyZ τ).mp hzeta
  have hbound := abs_hardyZ_sub_hardySEM_le hN τ
  rw [hZ, zero_sub, abs_neg] at hbound
  exact (not_lt_of_ge hbound) hmargin

/-- **Exact finitary nonvanishing criterion.**  A critical-line zeta value is nonzero exactly
when one finite symmetrized-EM value clears its explicit error budget.  The forward direction is
nonconstructive convergence, not a numerical witness. -/
theorem riemannZeta_line_ne_zero_iff_exists_hardySEM_certificate (τ : ℝ) :
    riemannZeta (linePt τ) ≠ 0 ↔
      ∃ N : ℕ, 1 ≤ N ∧ hardySEMError N τ < |hardySEM N τ| := by
  constructor
  · intro hzeta
    have hZ : hardyZ τ ≠ 0 :=
      (riemannZeta_line_eq_zero_iff_hardyZ τ).not.mp hzeta
    exact ((eventually_ge_atTop 1).and
      (eventually_hardySEMError_lt_abs_of_hardyZ_ne_zero hZ)).exists
  · rintro ⟨N, hN, hmargin⟩
    exact riemannZeta_line_ne_zero_of_hardySEM_error_lt_abs hN hmargin

/-- **Dual finite-tower zero criterion.**  A critical-line zeta value vanishes exactly when every
nontrivial symmetrized-EM approximant remains trapped inside its shrinking explicit error cone. -/
theorem riemannZeta_line_eq_zero_iff_forall_hardySEM_trapped (τ : ℝ) :
    riemannZeta (linePt τ) = 0 ↔
      ∀ N : ℕ, 1 ≤ N → |hardySEM N τ| ≤ hardySEMError N τ := by
  constructor
  · intro hzeta N hN
    have hZ : hardyZ τ = 0 := (riemannZeta_line_eq_zero_iff_hardyZ τ).mp hzeta
    have hbound := abs_hardyZ_sub_hardySEM_le hN τ
    rwa [hZ, zero_sub, abs_neg] at hbound
  · intro hall
    by_contra hzeta
    obtain ⟨N, hN, hmargin⟩ :=
      (riemannZeta_line_ne_zero_iff_exists_hardySEM_certificate τ).mp hzeta
    exact (not_lt_of_ge (hall N hN)) hmargin

/-- **Tail zero criterion.**  It is enough that the finite approximants remain in their shrinking
error cones eventually: a nonzero Hardy value forces every sufficiently large level to clear the
cone strictly. -/
theorem riemannZeta_line_eq_zero_iff_eventually_hardySEM_trapped (τ : ℝ) :
    riemannZeta (linePt τ) = 0 ↔
      ∀ᶠ N : ℕ in atTop, |hardySEM N τ| ≤ hardySEMError N τ := by
  constructor
  · intro hzeta
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (riemannZeta_line_eq_zero_iff_forall_hardySEM_trapped τ).mp hzeta N hN
  · intro htrap
    by_contra hzeta
    have hZ : hardyZ τ ≠ 0 :=
      (riemannZeta_line_eq_zero_iff_hardyZ τ).not.mp hzeta
    obtain ⟨N, hle, hlt⟩ :=
      (htrap.and (eventually_hardySEMError_lt_abs_of_hardyZ_ne_zero hZ)).exists
    exact (not_lt_of_ge hle) hlt

end RHTower
