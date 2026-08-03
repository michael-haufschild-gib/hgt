import GaloisForLFunctions.HTGeometry.ClockProbeCovectorSlicing

/-!
# Clock probes in a static gravitational field

The slicing determination theorem applies to a spatial covector as well as a temporal one. Taking
the first coordinate as the distinguished direction gives the static planar geometry
`g = diag(-e^{2Φ(z)}, 1, …, 1)`: the configuration of the clock-comparison experiment, in which
two clocks sit at different heights of a gravitational potential.

Here the geometry is genuinely **inhomogeneous** — the metric varies from place to place — and
still the clock potential is determined by clock data, with no nondegeneracy hypothesis. The
distinguished direction is spacelike, so the reduced equation is again of divergence form with a
nowhere-vanishing coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

/-- Diagonal of the inverse static metric: `-e^{-2Φ}` in the time direction, `1` in each spatial
direction. -/
noncomputable def staticDiag {d : ℕ} (pot : ℝ → ℝ) (z : ℝ) (i : Fin (d + 1 + 1)) : ℝ :=
  if i = 0 then -Real.exp (-2 * pot z) else 1

/-- Inverse static metric at height `z`. -/
noncomputable def staticCoeff {d : ℕ} (pot : ℝ → ℝ) (z : ℝ) :
    Matrix (Fin (d + 1 + 1)) (Fin (d + 1 + 1)) ℝ :=
  Matrix.diagonal (staticDiag pot z)

theorem staticCoeff_zero_zero {d : ℕ} (pot : ℝ → ℝ) (z : ℝ) :
    staticCoeff (d := d) pot z 0 0 = -Real.exp (-2 * pot z) := by
  simp [staticCoeff, staticDiag]

theorem staticCoeff_one_one {d : ℕ} (pot : ℝ → ℝ) (z : ℝ) :
    staticCoeff (d := d) pot z 1 1 = 1 := by
  simp [staticCoeff, staticDiag]

theorem contDiff_pot_comp {d : ℕ} {pot : ℝ → ℝ} (hpot : ContDiff ℝ ∞ pot) :
    ContDiff ℝ ∞ fun x : Fin (d + 1 + 1) → ℝ => pot (x 1) :=
  hpot.comp (contDiff_apply ℝ ℝ 1)

/-- The static planar chart of an arbitrary smooth gravitational potential. -/
noncomputable def staticChart {d : ℕ} {pot : ℝ → ℝ} (hpot : ContDiff ℝ ∞ pot) :
    SmoothMetricChart (d + 1 + 1) where
  inverseMetric x := staticCoeff pot (x 1)
  density x := Real.exp (pot (x 1))
  contDiff_inverseMetric := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
      by_cases hj0 : j = 0
      · rw [hj0]
        have h : (fun x : Fin (d + 1 + 1) → ℝ => staticCoeff (d := d) pot (x 1) 0 0)
            = fun x => -Real.exp (-2 * pot (x 1)) := by
          funext x
          exact staticCoeff_zero_zero pot (x 1)
        rw [h]
        exact (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_pot_comp hpot))).neg
      · have h : (fun x : Fin (d + 1 + 1) → ℝ => staticCoeff (d := d) pot (x 1) j j)
            = fun _ => (1 : ℝ) := by
          funext x
          simp [staticCoeff, staticDiag, hj0]
        rw [h]
        exact contDiff_const
    · have h : (fun x : Fin (d + 1 + 1) → ℝ => staticCoeff (d := d) pot (x 1) i j)
          = fun _ => (0 : ℝ) := by
        funext x
        simp [staticCoeff, hij]
      rw [h]
      exact contDiff_const
  contDiff_density := Real.contDiff_exp.comp (contDiff_pot_comp hpot)
  density_pos := fun _ => Real.exp_pos _
  inverseMetric_symm := by
    intro x i j
    simp only [staticCoeff, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rfl
    · rw [if_neg hij, if_neg (Ne.symm hij)]

/-- **The static chart is genuinely inhomogeneous.** Where the gravitational potential differs, so
does the metric. -/
theorem staticChart_inhomogeneous {d : ℕ} {pot : ℝ → ℝ} (hpot : ContDiff ℝ ∞ pot)
    {x y : Fin (d + 1 + 1) → ℝ} (hxy : pot (x 1) ≠ pot (y 1)) :
    (staticChart hpot).inverseMetric x ≠ (staticChart hpot).inverseMetric y := by
  intro hEq
  have h : staticCoeff (d := d) pot (x 1) 0 0 = staticCoeff (d := d) pot (y 1) 0 0 := by
    have := congrFun (congrFun hEq 0) 0
    exact this
  rw [staticCoeff_zero_zero, staticCoeff_zero_zero, neg_inj, Real.exp_eq_exp] at h
  exact hxy (by linarith)

theorem staticChart_inverseMetric {d : ℕ} {pot : ℝ → ℝ} (hpot : ContDiff ℝ ∞ pot)
    (x : Fin (d + 1 + 1) → ℝ) :
    (staticChart hpot).inverseMetric x
      = staticCoeff pot (covectorPhase (Pi.single (1 : Fin (d + 1 + 1)) 1) x) := by
  rw [covectorPhase_basis]
  rfl

theorem staticChart_density {d : ℕ} {pot : ℝ → ℝ} (hpot : ContDiff ℝ ∞ pot)
    (x : Fin (d + 1 + 1) → ℝ) :
    (staticChart hpot).density x
      = Real.exp (pot (covectorPhase (Pi.single (1 : Fin (d + 1 + 1)) 1) x)) := by
  rw [covectorPhase_basis]
  rfl

theorem contDiff_staticCoeff {d : ℕ} {pot : ℝ → ℝ} (hpot : ContDiff ℝ ∞ pot)
    (i j : Fin (d + 1 + 1)) : ContDiff ℝ 1 fun t => staticCoeff (d := d) pot t i j := by
  by_cases hij : i = j
  · rw [hij]
    by_cases hj0 : j = 0
    · rw [hj0]
      have h : (fun t => staticCoeff (d := d) pot t 0 0)
          = fun t => -Real.exp (-2 * pot t) := by
        funext t
        exact staticCoeff_zero_zero pot t
      rw [h]
      exact (Real.contDiff_exp.comp (contDiff_const.mul (hpot.of_le (by simp)))).neg
    · have h : (fun t => staticCoeff (d := d) pot t j j) = fun _ => (1 : ℝ) := by
        funext t
        simp [staticCoeff, staticDiag, hj0]
      rw [h]
      exact contDiff_const
  · have h : (fun t => staticCoeff (d := d) pot t i j) = fun _ => (0 : ℝ) := by
      funext t
      simp [staticCoeff, hij]
    rw [h]
    exact contDiff_const

theorem staticLeading_ne_zero {d : ℕ} (pot : ℝ → ℝ) (t : ℝ) :
    Real.exp (pot t) * covectorNorm (staticCoeff (d := d) pot) (Pi.single 1 1) t ≠ 0 := by
  rw [covectorNorm_basis, staticCoeff_one_one, mul_one]
  exact ne_of_gt (Real.exp_pos _)

/-- **Clock probes in a static gravitational field.** For every smooth gravitational potential and
every `C¹` clock potential of height, the equation `□u + Vu = 0` has a solution about every height,
constant on the level sets of the height and normalized to one on the initial leaf. -/
theorem exists_static_localProbe {d : ℕ} {pot : ℝ → ℝ} (hpot : ContDiff ℝ ∞ pot)
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) (a : ℝ) :
    ∃ (u : (Fin (d + 1 + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ x : Fin (d + 1 + 1) → ℝ, x 1 = a → u x = 1) ∧
      (∀ x : Fin (d + 1 + 1) → ℝ, x 1 ∈ Ioo (a - ε) (a + ε) →
        SolvesPotentialWaveAt (staticChart hpot).dalembert
          (covectorLift (Pi.single 1 1) V) u x) := by
  obtain ⟨u, ε, hε, hu1, hsolve⟩ :=
    exists_covector_localProbe (staticChart_inverseMetric hpot) (staticChart_density hpot)
      (Real.contDiff_exp.comp (hpot.of_le (by simp))) (contDiff_staticCoeff hpot)
      (staticLeading_ne_zero pot) hV a
  refine ⟨u, ε, hε, ?_, ?_⟩
  · intro x hx
    exact hu1 x (by rw [covectorPhase_basis]; exact hx)
  · intro x hx
    exact hsolve x (by rw [covectorPhase_basis]; exact hx)

/-- **The clock potential of a static gravitational field is determined by clock data.** The
geometry is inhomogeneous and no nondegeneracy hypothesis is assumed; the probes are constructed. -/
theorem static_potential_eq {d : ℕ} {pot : ℝ → ℝ} (hpot : ContDiff ℝ ∞ pot)
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) {other : (Fin (d + 1 + 1) → ℝ) → ℝ}
    (hother : ∀ (b : ℝ) (u : (Fin (d + 1 + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1 + 1) → ℝ,
        covectorPhase (Pi.single (1 : Fin (d + 1 + 1)) 1) x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (staticChart hpot).dalembert
          (covectorLift (Pi.single 1 1) V) u x) →
      (∀ x : Fin (d + 1 + 1) → ℝ,
        covectorPhase (Pi.single (1 : Fin (d + 1 + 1)) 1) x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt (staticChart hpot).dalembert other u x)) :
    other = covectorLift (Pi.single 1 1) V :=
  chartPotential_eq_of_covector (staticChart_inverseMetric hpot) (staticChart_density hpot)
    (Real.contDiff_exp.comp (hpot.of_le (by simp))) (contDiff_staticCoeff hpot)
    (staticLeading_ne_zero pot) hV hother

end GaloisForLFunctions.HTGeometry
