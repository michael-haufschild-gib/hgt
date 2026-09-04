import GaloisForLFunctions.HTGeometry.DispersivePDE.NLSSolitons
import Mathlib.Tactic

/-!
# Brizard elastica-NLS solution families

Closed analytic formalizations of arXiv:2607.21750, equations (27)--(31): plane waves,
the stationary optical `sech` soliton, its full Galilean orbit, and Hasimoto's constant-torsion
specialization.  Parameters absorb all side conditions, so theorem statements have no premises.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

open GaloisForLFunctions.HTGeometry.FDNLS

/-- Brizard's NLS after multiplying `-i D⁻¹ ψₜ = ψₛₛ + |ψ|²ψ/2` by `D`. -/
def SolvesNLS (D : ℝ) (J : ComplexEvolutionJet2) : Prop :=
  ∀ t x, Complex.I * J.ut t x + (D : ℂ) * J.uxx t x
    + (((D / 2) * ‖J.u t x‖ ^ 2 : ℝ) : ℂ) * J.u t x = 0

/-- Unit complex phase `exp(i(ωt + kx))`, built from the corpus FDNLS phase. -/
noncomputable def linearPhase (ω k t x : ℝ) : ℂ :=
  staggerPhase (-ω) t * staggerPhase (-k) x

theorem norm_linearPhase (ω k t x : ℝ) : ‖linearPhase ω k t x‖ = 1 := by
  rw [linearPhase, norm_mul, norm_staggerPhase, norm_staggerPhase, one_mul]

theorem hasDerivAt_linearPhase_time (ω k t x : ℝ) :
    HasDerivAt (fun s : ℝ => linearPhase ω k s x)
      (linearPhase ω k t x * (Complex.I * (ω : ℂ))) t := by
  have h := (hasDerivAt_staggerPhase (-ω) t).mul_const (staggerPhase (-k) x)
  apply h.congr_deriv
  rw [linearPhase]
  push_cast
  ring

theorem hasDerivAt_linearPhase_space (ω k t x : ℝ) :
    HasDerivAt (linearPhase ω k t)
      (linearPhase ω k t x * (Complex.I * (k : ℂ))) x := by
  have h := (hasDerivAt_staggerPhase (-k) x).const_mul (staggerPhase (-ω) t)
  apply h.congr_deriv
  rw [linearPhase]
  push_cast
  ring

theorem hasDerivAt_linearPhase_space_one (ω k t x : ℝ) :
    HasDerivAt (fun y : ℝ => linearPhase ω k t y * (Complex.I * (k : ℂ)))
      (linearPhase ω k t x * (Complex.I * (k : ℂ)) ^ 2) x := by
  have h := (hasDerivAt_linearPhase_space ω k t x).mul_const (Complex.I * (k : ℂ))
  apply h.congr_deriv
  ring

private theorem planeResidual_zero (D a k P : ℂ) :
    Complex.I * (a * (P * (Complex.I * (D * (a ^ 2 / 2 - k ^ 2)))))
      + D * (a * (P * (Complex.I * k) ^ 2))
      + (D / 2 * a ^ 2) * (a * P) = 0 := by
  calc
    Complex.I * (a * (P * (Complex.I * (D * (a ^ 2 / 2 - k ^ 2)))))
          + D * (a * (P * (Complex.I * k) ^ 2))
          + (D / 2 * a ^ 2) * (a * P) =
        (D * a ^ 3 * P / 2) * (Complex.I * Complex.I + 1) := by ring
    _ = 0 := by rw [Complex.I_mul_I]; ring

private theorem envelopeResidual_zero (D k v A Ax P : ℂ) :
    Complex.I *
          ((-2 * D * v * Ax) * P + A * (P * (Complex.I * (D * (k ^ 2 - v ^ 2)))))
      + D *
          ((k ^ 2 * A - A ^ 3 / 2) * P
            + 2 * Ax * (P * (Complex.I * v))
            + A * (P * (Complex.I * v) ^ 2))
      + (D / 2 * A ^ 2) * (A * P) = 0 := by
  calc
    Complex.I *
            ((-2 * D * v * Ax) * P + A * (P * (Complex.I * (D * (k ^ 2 - v ^ 2)))))
        + D *
            ((k ^ 2 * A - A ^ 3 / 2) * P
              + 2 * Ax * (P * (Complex.I * v))
              + A * (P * (Complex.I * v) ^ 2))
        + (D / 2 * A ^ 2) * (A * P) =
      (D * k ^ 2 * A * P) * (Complex.I * Complex.I + 1) := by ring
    _ = 0 := by rw [Complex.I_mul_I]; ring

/-- Equation (27), with temporal frequency `D(a²/2-k²)`. -/
noncomputable def planeWave (D a k t x : ℝ) : ℂ :=
  (a : ℂ) * linearPhase (D * (a ^ 2 / 2 - k ^ 2)) k t x

noncomputable def planeWaveJet (D a k : ℝ) : ComplexEvolutionJet2 where
  u := planeWave D a k
  ut := fun t x => (a : ℂ) *
    (linearPhase (D * (a ^ 2 / 2 - k ^ 2)) k t x *
      (Complex.I * ((D * (a ^ 2 / 2 - k ^ 2) : ℝ) : ℂ)))
  ux := fun t x => (a : ℂ) *
    (linearPhase (D * (a ^ 2 / 2 - k ^ 2)) k t x * (Complex.I * (k : ℂ)))
  uxx := fun t x => (a : ℂ) *
    (linearPhase (D * (a ^ 2 / 2 - k ^ 2)) k t x * (Complex.I * (k : ℂ)) ^ 2)
  hasDerivAt_time := by
    intro t x
    exact (hasDerivAt_linearPhase_time _ _ t x).const_mul (a : ℂ)
  hasDerivAt_space := by
    intro t x
    exact (hasDerivAt_linearPhase_space _ _ t x).const_mul (a : ℂ)
  hasDerivAt_space_one := by
    intro t x
    exact (hasDerivAt_linearPhase_space_one _ _ t x).const_mul (a : ℂ)

theorem norm_planeWave_sq (D a k t x : ℝ) : ‖planeWave D a k t x‖ ^ 2 = a ^ 2 := by
  rw [planeWave, norm_mul, norm_linearPhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

/-- Brizard equation (27) is an exact solution for every real amplitude, wave number, and `D`. -/
theorem planeWave_solves (D a k : ℝ) : SolvesNLS D (planeWaveJet D a k) := by
  intro t x
  simp only [planeWaveJet, planeWave]
  have hnorm :
      ‖(a : ℂ) * linearPhase (D * (a ^ 2 / 2 - k ^ 2)) k t x‖ ^ 2 = a ^ 2 := by
    simpa only [planeWave] using norm_planeWave_sq D a k t x
  rw [hnorm]
  push_cast
  exact planeResidual_zero (D : ℂ) (a : ℂ) (k : ℂ)
    (linearPhase (D * (a ^ 2 / 2 - k ^ 2)) k t x)

/-- Galilean coordinate `k(x - 2Dvt)` from equations (30)--(31). -/
def envelopeCoordinate (D k v t x : ℝ) : ℝ := k * (x - 2 * D * v * t)

theorem hasDerivAt_envelopeCoordinate_time (D k v t x : ℝ) :
    HasDerivAt (fun s : ℝ => envelopeCoordinate D k v s x) (-2 * D * v * k) t := by
  have h := ((hasDerivAt_const t x).sub
    ((hasDerivAt_id t).const_mul (2 * D * v))).const_mul k
  apply h.congr_deriv
  ring

theorem hasDerivAt_envelopeCoordinate_space (D k v t x : ℝ) :
    HasDerivAt (envelopeCoordinate D k v t) k x := by
  have h := ((hasDerivAt_id x).sub_const (2 * D * v * t)).const_mul k
  apply h.congr_deriv
  ring

/-- Real curvature envelope `2k sech(k(x-2Dvt))`. -/
noncomputable def envelope (D k v t x : ℝ) : ℝ :=
  2 * k * solitonA (envelopeCoordinate D k v t x)

noncomputable def envelopeT (D k v t x : ℝ) : ℝ :=
  2 * k * solitonA1 (envelopeCoordinate D k v t x) * (-2 * D * v * k)

noncomputable def envelopeX (D k v t x : ℝ) : ℝ :=
  2 * k * solitonA1 (envelopeCoordinate D k v t x) * k

noncomputable def envelopeXX (D k v t x : ℝ) : ℝ :=
  2 * k * solitonA2 (envelopeCoordinate D k v t x) * k ^ 2

theorem hasDerivAt_envelope_time (D k v t x : ℝ) :
    HasDerivAt (fun s : ℝ => envelope D k v s x) (envelopeT D k v t x) t := by
  have h := ((hasDerivAt_solitonA _).comp t
    (hasDerivAt_envelopeCoordinate_time D k v t x)).const_mul (2 * k)
  apply h.congr_deriv
  rw [envelopeT]
  ring

theorem hasDerivAt_envelope_space (D k v t x : ℝ) :
    HasDerivAt (envelope D k v t) (envelopeX D k v t x) x := by
  have h := ((hasDerivAt_solitonA _).comp x
    (hasDerivAt_envelopeCoordinate_space D k v t x)).const_mul (2 * k)
  apply h.congr_deriv
  rw [envelopeX]
  ring

theorem hasDerivAt_envelope_space_one (D k v t x : ℝ) :
    HasDerivAt (envelopeX D k v t) (envelopeXX D k v t x) x := by
  have h := ((hasDerivAt_solitonA1 _).comp x
    (hasDerivAt_envelopeCoordinate_space D k v t x)).const_mul (2 * k * k)
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [envelopeX]
    ring
  · rw [envelopeXX]
    ring

theorem envelopeT_eq (D k v t x : ℝ) :
    envelopeT D k v t x = -2 * D * v * envelopeX D k v t x := by
  rw [envelopeT, envelopeX]
  ring

/-- Scaled `sech` profile equation behind paper equation (28). -/
theorem envelope_schrodinger (D k v t x : ℝ) :
    envelopeXX D k v t x =
      k ^ 2 * envelope D k v t x - envelope D k v t x ^ 3 / 2 := by
  rw [envelopeXX, envelope, solitonA2]
  ring

/-- Equations (30)--(31), parameterized by `v = c/(2D)` without a division premise. -/
noncomputable def envelopeSoliton (D k v t x : ℝ) : ℂ :=
  (envelope D k v t x : ℂ) * linearPhase (D * (k ^ 2 - v ^ 2)) v t x

noncomputable def envelopeSolitonJet (D k v : ℝ) : ComplexEvolutionJet2 where
  u := envelopeSoliton D k v
  ut := fun t x =>
    (envelopeT D k v t x : ℂ) * linearPhase (D * (k ^ 2 - v ^ 2)) v t x
      + (envelope D k v t x : ℂ) *
        (linearPhase (D * (k ^ 2 - v ^ 2)) v t x *
          (Complex.I * ((D * (k ^ 2 - v ^ 2) : ℝ) : ℂ)))
  ux := fun t x =>
    (envelopeX D k v t x : ℂ) * linearPhase (D * (k ^ 2 - v ^ 2)) v t x
      + (envelope D k v t x : ℂ) *
        (linearPhase (D * (k ^ 2 - v ^ 2)) v t x * (Complex.I * (v : ℂ)))
  uxx := fun t x =>
    (envelopeXX D k v t x : ℂ) * linearPhase (D * (k ^ 2 - v ^ 2)) v t x
      + 2 * (envelopeX D k v t x : ℂ) *
        (linearPhase (D * (k ^ 2 - v ^ 2)) v t x * (Complex.I * (v : ℂ)))
      + (envelope D k v t x : ℂ) *
        (linearPhase (D * (k ^ 2 - v ^ 2)) v t x * (Complex.I * (v : ℂ)) ^ 2)
  hasDerivAt_time := by
    intro t x
    exact (hasDerivAt_envelope_time D k v t x).ofReal_comp.mul
      (hasDerivAt_linearPhase_time _ _ t x)
  hasDerivAt_space := by
    intro t x
    exact (hasDerivAt_envelope_space D k v t x).ofReal_comp.mul
      (hasDerivAt_linearPhase_space _ _ t x)
  hasDerivAt_space_one := by
    intro t x
    have h₁ := (hasDerivAt_envelope_space_one D k v t x).ofReal_comp.mul
      (hasDerivAt_linearPhase_space (D * (k ^ 2 - v ^ 2)) v t x)
    have h₂ := (hasDerivAt_envelope_space D k v t x).ofReal_comp.mul
      (hasDerivAt_linearPhase_space_one (D * (k ^ 2 - v ^ 2)) v t x)
    apply (h₁.add h₂).congr_deriv
    ring

theorem norm_envelopeSoliton_sq (D k v t x : ℝ) :
    ‖envelopeSoliton D k v t x‖ ^ 2 = envelope D k v t x ^ 2 := by
  rw [envelopeSoliton, norm_mul, norm_linearPhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Full Zakharov--Shabat/Galilean `sech` family solves Brizard's NLS. -/
theorem envelopeSoliton_solves (D k v : ℝ) : SolvesNLS D (envelopeSolitonJet D k v) := by
  intro t x
  simp only [envelopeSolitonJet, envelopeSoliton]
  have hnorm :
      ‖(envelope D k v t x : ℂ) * linearPhase (D * (k ^ 2 - v ^ 2)) v t x‖ ^ 2 =
        envelope D k v t x ^ 2 := by
    simpa only [envelopeSoliton] using norm_envelopeSoliton_sq D k v t x
  rw [hnorm]
  have ht := envelopeT_eq D k v t x
  have hs := envelope_schrodinger D k v t x
  rw [ht, hs]
  push_cast
  exact envelopeResidual_zero (D : ℂ) (k : ℂ) (v : ℂ)
    (envelope D k v t x : ℂ) (envelopeX D k v t x : ℂ)
    (linearPhase (D * (k ^ 2 - v ^ 2)) v t x)

/-- Equation (28), stationary optical soliton. -/
noncomputable def opticalSoliton (D k : ℝ) : ℝ → ℝ → ℂ := envelopeSoliton D k 0

theorem opticalSoliton_solves (D k : ℝ) :
    SolvesNLS D (envelopeSolitonJet D k 0) := envelopeSoliton_solves D k 0

/-- Equation (30): the envelope peak travels at speed `2Dv`. -/
theorem envelope_peak_norm (D k v t : ℝ) :
    ‖envelopeSoliton D k v t (2 * D * v * t)‖ = |2 * k| := by
  rw [envelopeSoliton, norm_mul, norm_linearPhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  simp [envelope, envelopeCoordinate, solitonA]

/-- Equation (39), Hasimoto's constant-torsion specialization `v = k = τ₀`. -/
noncomputable def hasimotoSoliton (D τ₀ : ℝ) : ℝ → ℝ → ℂ := envelopeSoliton D τ₀ τ₀

theorem hasimotoSoliton_solves (D τ₀ : ℝ) :
    SolvesNLS D (envelopeSolitonJet D τ₀ τ₀) := envelopeSoliton_solves D τ₀ τ₀

/-- Paper normalization at `D=k=1` is twice the corpus focusing bright soliton. -/
theorem opticalSoliton_one_eq_twice_nlsBrightSoliton :
    opticalSoliton 1 1 = fun t x => 2 * nlsBrightSoliton t x := by
  funext t x
  simp [opticalSoliton, envelopeSoliton, envelope, envelopeCoordinate, linearPhase,
    nlsBrightSoliton, brightPhase]
  rw [show staggerPhase 0 x = 1 by simp [staggerPhase]]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
