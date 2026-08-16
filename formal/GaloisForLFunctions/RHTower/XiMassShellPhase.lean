import GaloisForLFunctions.RHTower.XiMassShellLeadingTerm

/-!
# The shell leading amplitude and its constant phase

On the spacelike shell `h = κu + s` the linear radius is

`ζ = q u + (κ s + iσ)/q`,  `q = √(κ²−1)`,

so `e^{-aζ}` splits exactly into a positive real factor and the single constant phase
`e^{-iaσ/q}`.  Consequently the whole leading amplitude

`√(2πa) · (iu) · e^{-aζ} / (q u)^{3/2}`,

damped by `e^{-h/2}`, is a positive real multiple of the fixed unit vector `i e^{-iaσ/q}` — the
phase does not move with `s` at all.  This is the exact coherence that lets a shell sum be bounded
below by the sum of the moduli.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The shell rapidity `q = √(κ²−1)`. -/
def shellQ (kappa : ℝ) : ℝ := Real.sqrt (kappa ^ 2 - 1)

theorem shellQ_pos {kappa : ℝ} (hkappa : 1 < kappa) : 0 < shellQ kappa := by
  rw [shellQ]
  exact Real.sqrt_pos.2 (by nlinarith)

theorem shellQ_sq {kappa : ℝ} (hkappa : 1 < kappa) : shellQ kappa ^ 2 = kappa ^ 2 - 1 := by
  rw [shellQ]
  exact Real.sq_sqrt (by nlinarith)

theorem xiMassShellRadius_eq {sigma kappa u s : ℝ} (hkappa : 1 < kappa) :
    xiMassShellRadius sigma kappa u s
      = ((shellQ kappa * u + kappa * s / shellQ kappa : ℝ) : ℂ)
        + ((sigma / shellQ kappa : ℝ) : ℂ) * I := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hqne : ((shellQ kappa : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hq
  rw [xiMassShellRadius, shellQ] at *
  push_cast
  field_simp
  ring

/-- The constant unit phase of the shell amplitude. -/
def shellPhase (a sigma kappa : ℝ) : ℂ :=
  I * Complex.exp (-(I * ((a * sigma / shellQ kappa : ℝ) : ℂ)))

theorem norm_shellPhase (a sigma kappa : ℝ) : ‖shellPhase a sigma kappa‖ = 1 := by
  rw [shellPhase, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
  have : (-(I * ((a * sigma / shellQ kappa : ℝ) : ℂ))).re = 0 := by
    simp [Complex.mul_re]
  rw [this, Real.exp_zero]

/-- **The exact phase split of the shell exponential.** -/
theorem exp_neg_mul_shellRadius {a sigma kappa u s : ℝ} (hkappa : 1 < kappa) :
    Complex.exp (-((a : ℂ) * xiMassShellRadius sigma kappa u s))
      = ((Real.exp (-(a * (shellQ kappa * u + kappa * s / shellQ kappa))) : ℝ) : ℂ)
        * Complex.exp (-(I * ((a * sigma / shellQ kappa : ℝ) : ℂ))) := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hsplit : -((a : ℂ) * xiMassShellRadius sigma kappa u s)
      = ((-(a * (shellQ kappa * u + kappa * s / shellQ kappa)) : ℝ) : ℂ)
        + -(I * ((a * sigma / shellQ kappa : ℝ) : ℂ)) := by
    rw [xiMassShellRadius_eq hkappa]
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.ofReal_exp]

/-- The positive modulus of the damped shell amplitude. -/
def shellModulus (a kappa u s : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * a) * u
    * Real.exp (-((kappa * u + s) / 2))
    * Real.exp (-(a * (shellQ kappa * u + kappa * s / shellQ kappa)))
    / (shellQ kappa * u * Real.sqrt (shellQ kappa * u))

theorem shellModulus_pos {a kappa u s : ℝ} (ha : 0 < a) (hkappa : 1 < kappa) (hu : 0 < u) :
    0 < shellModulus a kappa u s := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hqu : 0 < shellQ kappa * u := mul_pos hq hu
  have hroot : 0 < Real.sqrt (shellQ kappa * u) := Real.sqrt_pos.2 hqu
  have hamp : 0 < Real.sqrt (2 * Real.pi * a) := Real.sqrt_pos.2 (by positivity)
  rw [shellModulus]
  positivity

/-- The damped leading amplitude of the shell. -/
def shellLeadingDamped (a sigma kappa u s : ℝ) : ℂ :=
  ((Real.exp (-((kappa * u + s) / 2)) : ℝ) : ℂ)
    * (((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ) * ((u : ℂ) * I)
      * Complex.exp (-((a : ℂ) * xiMassShellRadius sigma kappa u s))
      / (((shellQ kappa * u : ℝ) : ℂ) * ((Real.sqrt (shellQ kappa * u) : ℝ) : ℂ)))

/-- **The damped shell amplitude is a positive multiple of one fixed unit phase.** -/
theorem shellLeadingDamped_eq {a sigma kappa u s : ℝ} (hkappa : 1 < kappa) (hu : 0 < u) :
    shellLeadingDamped a sigma kappa u s
      = ((shellModulus a kappa u s : ℝ) : ℂ) * shellPhase a sigma kappa := by
  have hq : 0 < shellQ kappa := shellQ_pos hkappa
  have hqu : 0 < shellQ kappa * u := mul_pos hq hu
  have hroot : 0 < Real.sqrt (shellQ kappa * u) := Real.sqrt_pos.2 hqu
  have hquC : ((shellQ kappa * u : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hqu
  have hrootC : ((Real.sqrt (shellQ kappa * u) : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hroot
  rw [shellLeadingDamped, exp_neg_mul_shellRadius hkappa, shellModulus, shellPhase]
  push_cast
  field_simp

theorem norm_shellLeadingDamped {a sigma kappa u s : ℝ} (ha : 0 < a) (hkappa : 1 < kappa)
    (hu : 0 < u) :
    ‖shellLeadingDamped a sigma kappa u s‖ = shellModulus a kappa u s := by
  rw [shellLeadingDamped_eq hkappa hu, norm_mul, norm_shellPhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (shellModulus_pos ha hkappa hu)]

end

end RHTower
