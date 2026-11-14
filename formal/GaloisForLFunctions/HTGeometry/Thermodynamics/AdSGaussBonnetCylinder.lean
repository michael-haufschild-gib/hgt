import GaloisForLFunctions.HTGeometry.Thermodynamics.AdSGaussBonnetBoundary

/-!
# Cylinder clock and vacuum-energy derivatives

The common boundary clock of arXiv:2611.16364 multiplies the energy by
`beta` and adds the anomaly vacuum energy. Its apparently nested square
roots have simple derivatives: the vacuum response is `-45 beta / 8`.
The coordinate `(1-exp s)/4` covers the entire real subcritical domain.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.AdSGaussBonnet

def subcriticalCoupling (s : ℝ) : ℝ := (1 - Real.exp s) / 4
def eta (l : ℝ) : ℝ := Real.sqrt (1 - 4 * l)
def beta (l : ℝ) : ℝ := Real.sqrt ((1 + eta l) / 2)
def vacuumEnergy (l : ℝ) : ℝ := (3 / 4) * (beta l ^ 3 * (3 * eta l - 2))

def betaSlope (l : ℝ) : ℝ := -1 / (2 * eta l * beta l)
def betaCurvature (l : ℝ) : ℝ :=
  -1 / (eta l ^ 3 * beta l) - 1 / (4 * eta l ^ 2 * beta l ^ 3)

theorem subcriticalCoupling_lt (s : ℝ) : subcriticalCoupling s < 1 / 4 := by
  unfold subcriticalCoupling
  linarith only [Real.exp_pos s]

theorem subcritical_discriminant (s : ℝ) :
    1 - 4 * subcriticalCoupling s = Real.exp s := by
  unfold subcriticalCoupling
  ring

theorem eta_pos (s : ℝ) : 0 < eta (subcriticalCoupling s) := by
  unfold eta
  rw [subcritical_discriminant]
  exact Real.sqrt_pos.mpr (Real.exp_pos s)

theorem beta_pos (s : ℝ) : 0 < beta (subcriticalCoupling s) := by
  unfold beta
  exact Real.sqrt_pos.mpr (div_pos (by linarith only [eta_pos s]) (by norm_num))

theorem beta_sq (s : ℝ) :
    beta (subcriticalCoupling s) ^ 2 = (1 + eta (subcriticalCoupling s)) / 2 := by
  unfold beta
  exact Real.sq_sqrt (by have h := eta_pos s; positivity)

theorem eta_hasDerivAt (s : ℝ) :
    HasDerivAt eta (-2 / eta (subcriticalCoupling s)) (subcriticalCoupling s) := by
  have hinner := (hasDerivAt_const (subcriticalCoupling s) (1 : ℝ)).sub
    ((hasDerivAt_id (subcriticalCoupling s)).const_mul 4)
  have hne : 1 - 4 * subcriticalCoupling s ≠ 0 := by
    rw [subcritical_discriminant]
    exact Real.exp_ne_zero s
  apply ((Real.hasDerivAt_sqrt hne).comp (subcriticalCoupling s) hinner).congr_deriv
  dsimp [eta]
  ring

theorem beta_hasDerivAt (s : ℝ) :
    HasDerivAt beta (betaSlope (subcriticalCoupling s)) (subcriticalCoupling s) := by
  have hinner := ((eta_hasDerivAt s).const_add 1).div_const 2
  have hne : (1 + eta (subcriticalCoupling s)) / 2 ≠ 0 := by
    have h := eta_pos s
    positivity
  apply ((Real.hasDerivAt_sqrt hne).comp (subcriticalCoupling s) hinner).congr_deriv
  dsimp [betaSlope, beta]
  ring

/-- Cancellation of the nested anomaly derivatives leaves one clock factor. -/
theorem vacuumEnergy_hasDerivAt (s : ℝ) :
    HasDerivAt vacuumEnergy (-(45 / 8) * beta (subcriticalCoupling s))
      (subcriticalCoupling s) := by
  apply ((((beta_hasDerivAt s).pow 3).mul
    (((eta_hasDerivAt s).const_mul 3).sub_const 2)).const_mul (3 / 4)).congr_deriv
  dsimp [betaSlope]
  have he := (eta_pos s).ne'
  have hb := (beta_pos s).ne'
  have hs := beta_sq s
  field_simp [he, hb]
  nlinarith only [congrArg (fun x : ℝ =>
    18 * beta (subcriticalCoupling s) ^ 2 * x) hs]

theorem betaSlope_hasDerivAt (s : ℝ) :
    HasDerivAt betaSlope (betaCurvature (subcriticalCoupling s)) (subcriticalCoupling s) := by
  have hd := ((eta_hasDerivAt s).const_mul 2).mul (beta_hasDerivAt s)
  have hn : 2 * eta (subcriticalCoupling s) * beta (subcriticalCoupling s) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (eta_pos s).ne') (beta_pos s).ne'
  apply ((hasDerivAt_const (subcriticalCoupling s) (-1 : ℝ)).div hd hn).congr_deriv
  dsimp [betaSlope, betaCurvature]
  field_simp [(eta_pos s).ne', (beta_pos s).ne']
  ring

theorem betaCurvature_neg (s : ℝ) : betaCurvature (subcriticalCoupling s) < 0 := by
  unfold betaCurvature
  have h₁ : 0 < 1 / (eta (subcriticalCoupling s) ^ 3 * beta (subcriticalCoupling s)) := by
    have he := eta_pos s
    have hb := beta_pos s
    positivity
  have h₂ : 0 < 1 / (4 * eta (subcriticalCoupling s) ^ 2 * beta (subcriticalCoupling s) ^ 3) := by
    have he := eta_pos s
    have hb := beta_pos s
    positivity
  linarith only [h₁, h₂]

def cylinderPotential (t z q x l : ℝ) : ℝ :=
  beta l * energy l q x + vacuumEnergy l - t * entropy l x - z * l

def cylinderPotentialSlope (t z q x l : ℝ) : ℝ :=
  betaSlope l * energy l q x - (21 / 8) * beta l - 24 * Real.pi * x * t - z

/-- The clock varies across couplings and contributes to the source response. -/
theorem cylinderPotential_hasDerivAt (t z q x s : ℝ) :
    HasDerivAt (cylinderPotential t z q x)
      (cylinderPotentialSlope t z q x (subcriticalCoupling s)) (subcriticalCoupling s) := by
  have he := (((hasDerivAt_id (subcriticalCoupling s)).const_add
    (x ^ 4 + x ^ 2)).const_mul 3).add_const (q ^ 2 / x ^ 2)
  have hs := ((((hasDerivAt_id (subcriticalCoupling s)).const_mul 6).mul_const x).const_add
    (x ^ 3)).const_mul (4 * Real.pi)
  apply (((((beta_hasDerivAt s).mul he).add (vacuumEnergy_hasDerivAt s)).sub
    (hs.const_mul t)).sub ((hasDerivAt_id (subcriticalCoupling s)).const_mul z)).congr_deriv
  dsimp [cylinderPotentialSlope, energy]
  ring

/-- The remaining curvature term after combining clock and vacuum responses is negative. -/
theorem cylinderPotentialSlope_hasDerivAt (t z q x s : ℝ) :
    HasDerivAt (cylinderPotentialSlope t z q x)
      (betaCurvature (subcriticalCoupling s) * energy (subcriticalCoupling s) q x -
        3 / (16 * eta (subcriticalCoupling s) * beta (subcriticalCoupling s)))
      (subcriticalCoupling s) := by
  have he := (((hasDerivAt_id (subcriticalCoupling s)).const_add
    (x ^ 4 + x ^ 2)).const_mul 3).add_const (q ^ 2 / x ^ 2)
  apply (((((betaSlope_hasDerivAt s).mul he).sub ((beta_hasDerivAt s).const_mul (21 / 8))).sub_const
    (24 * Real.pi * x * t)).sub_const z).congr_deriv
  dsimp [betaSlope, energy]
  ring

#print axioms vacuumEnergy_hasDerivAt
#print axioms betaCurvature_neg
#print axioms cylinderPotentialSlope_hasDerivAt

end GaloisForLFunctions.HTGeometry.AdSGaussBonnet
