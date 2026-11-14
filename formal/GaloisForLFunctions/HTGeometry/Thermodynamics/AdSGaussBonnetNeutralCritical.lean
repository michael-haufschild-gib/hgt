import GaloisForLFunctions.HTGeometry.Thermodynamics.AdSGaussBonnetBoundary

/-!
# The neutral Hawking--Page critical point

At coupling `1/36` the five-dimensional neutral potential is exactly a
quartic, while the on-shell temperature has a cubic displacement. These
identities strengthen the stationary-inflection observation in
arXiv:2611.16364, section 5: the black-hole saddle is globally unique even
though it coexists with the zero-entropy thermal-AdS state.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.AdSGaussBonnet

def neutralCriticalRadius : ℝ := Real.sqrt 6 / 6
def neutralCriticalTemperature : ℝ := Real.sqrt 6 / (2 * Real.pi)

theorem neutralCriticalRadius_pos : 0 < neutralCriticalRadius := by
  unfold neutralCriticalRadius
  positivity

theorem neutralCriticalRadius_sq : neutralCriticalRadius ^ 2 = 1 / 6 := by
  unfold neutralCriticalRadius
  rw [div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 6)]
  norm_num

private theorem sqrt_six_cube : Real.sqrt 6 ^ 3 = 6 * Real.sqrt 6 := by
  rw [pow_succ, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 6)]

private theorem sqrt_six_fourth : Real.sqrt 6 ^ 4 = 36 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 6)]
  norm_num

/-- The entire critical off-shell landscape is a positive quartic. -/
theorem neutral_critical_potential_quartic (x : ℝ) :
    potential neutralCriticalTemperature 0 (1 / 36) 0 x =
      3 * (x - neutralCriticalRadius) ^ 4 := by
  unfold potential energy entropy neutralCriticalTemperature neutralCriticalRadius
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero, zero_mul, sub_zero]
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 6), sqrt_six_cube, sqrt_six_fourth]
  ring

theorem neutral_critical_potential_nonneg (x : ℝ) :
    0 ≤ potential neutralCriticalTemperature 0 (1 / 36) 0 x := by
  rw [neutral_critical_potential_quartic]
  positivity

/-- The only black-hole radius sharing thermal AdS's zero potential. -/
theorem neutral_critical_potential_zero_iff (x : ℝ) :
    potential neutralCriticalTemperature 0 (1 / 36) 0 x = 0 ↔
      x = neutralCriticalRadius := by
  rw [neutral_critical_potential_quartic]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
    pow_eq_zero_iff (by norm_num : 4 ≠ 0), sub_eq_zero]

/-- The critical thermal state has positive entropy, unlike thermal AdS. -/
theorem neutral_critical_entropy :
    entropy (1 / 36) neutralCriticalRadius = 2 * Real.pi * Real.sqrt 6 / 9 := by
  unfold entropy neutralCriticalRadius
  ring_nf
  rw [sqrt_six_cube]
  ring

theorem neutral_critical_entropy_pos : 0 < entropy (1 / 36) neutralCriticalRadius := by
  rw [neutral_critical_entropy]
  positivity

theorem neutral_critical_latent_heat :
    energy (1 / 36) 0 neutralCriticalRadius = 2 / 3 ∧
      neutralCriticalTemperature * entropy (1 / 36) neutralCriticalRadius = 2 / 3 := by
  constructor
  · unfold energy
    rw [show neutralCriticalRadius ^ 4 = (neutralCriticalRadius ^ 2) ^ 2 by ring,
      neutralCriticalRadius_sq]
    norm_num
  · rw [neutral_critical_entropy]
    unfold neutralCriticalTemperature
    field_simp [Real.pi_ne_zero]
    nlinarith only [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 6)]

/-- The temperature displacement is exactly cubic, not just a truncated expansion. -/
theorem neutral_critical_temperature_cubic (u : ℝ) :
    temperature (1 / 36) 0 (Real.exp u) - neutralCriticalTemperature =
      (Real.exp u - neutralCriticalRadius) ^ 3 /
        (Real.pi * (Real.exp u ^ 2 + 1 / 18)) := by
  unfold temperature neutralCriticalTemperature neutralCriticalRadius
  have hd : Real.exp u ^ 2 + (1 / 18 : ℝ) ≠ 0 := by positivity
  field_simp [Real.pi_ne_zero, hd]
  ring_nf
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 6), sqrt_six_cube]
  ring

/-- The on-shell free-energy crossing has an exact cubic numerator. -/
theorem neutral_critical_on_shell_cubic (u : ℝ) :
    potential (temperature (1 / 36) 0 (Real.exp u)) 0 (1 / 36) 0 (Real.exp u) =
      -(Real.exp u ^ 2 - 1 / 6) ^ 3 / (Real.exp u ^ 2 + 1 / 18) := by
  unfold potential energy entropy temperature
  have hd : Real.exp u ^ 2 + (1 / 18 : ℝ) ≠ 0 := by positivity
  field_simp [Real.pi_ne_zero, hd]
  <;> ring

#print axioms neutral_critical_potential_zero_iff
#print axioms neutral_critical_entropy_pos
#print axioms neutral_critical_latent_heat
#print axioms neutral_critical_temperature_cubic
#print axioms neutral_critical_on_shell_cubic

end GaloisForLFunctions.HTGeometry.AdSGaussBonnet
