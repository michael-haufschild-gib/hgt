import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalAParameters

/-!
# The actual model-A critical Gibbs landscape

Insert the model-A critical data of arXiv:2609.00025 into the logarithmic
entropy free energy. Its derivative factors into a positive coefficient,
a cubic radius difference, and a strictly positive residual factor.
Consequently the critical radius is the unique global minimum, for every
entropy reference length. The proof uses actual derivatives and monotonicity,
not a finite-order Taylor approximation or a numerical phase plot.
-/
noncomputable section
open Real Set
namespace GaloisForLFunctions.HTGeometry

def egbCriticalALogGibbs (x θ l u : ℝ) : ℝ :=
  egbOffShellGibbsA (egbCriticalAPressure x θ) (egbCriticalATemperature x θ)
    (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ) l (exp u)

/-- The exponential part of the n-th logarithmic-radius derivative. -/
def egbCriticalAGibbsJet (x θ : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  exp u / 2 + (-1 : ℝ) ^ n * exp x ^ (2 : ℕ) * (1 - 6 * egbCriticalAShape θ) /
    (12 * (1 + 2 * egbCriticalAShape θ) * exp u) +
    (3 : ℝ) ^ n * (3 - 2 * egbCriticalAShape θ) * exp u ^ (3 : ℕ) /
      (36 * exp x ^ (2 : ℕ) * (1 + 2 * egbCriticalAShape θ)) -
    (2 : ℝ) ^ n * exp u ^ (2 : ℕ) / (3 * exp x * (1 + 2 * egbCriticalAShape θ))

def egbCriticalAEntropySlope (x θ : ℝ) : ℝ :=
  4 * exp x * egbCriticalAShape θ / (3 * (1 + 2 * egbCriticalAShape θ))

def egbCriticalATail (θ : ℝ) : ℝ := (1 - 6 * egbCriticalAShape θ) / (3 - 2 * egbCriticalAShape θ)

theorem egbCriticalATail_pos (θ : ℝ) : 0 < egbCriticalATail θ := by
  have h₁ : 0 < 1 - 6 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  have h₂ : 0 < 3 - 2 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  exact div_pos h₁ h₂

theorem egbCriticalALogGibbs_formula (x θ l u : ℝ) :
    egbCriticalALogGibbs x θ l u = egbCriticalAGibbsJet x θ 0 u - egbCriticalAEntropySlope x θ * (u - l) := by
  unfold egbCriticalALogGibbs egbOffShellGibbsA egbMass egbEntropyA
  rw [egbCriticalA_effective_charge, egbCriticalA_coupling_square,
    log_div (exp_ne_zero u) (exp_ne_zero l), log_exp, log_exp]
  unfold egbCriticalAGibbsJet egbCriticalAEntropySlope egbCriticalAPressure egbCriticalATemperature
  norm_num only [pow_zero, one_mul]
  have hb := (egbCriticalAShape_bounds θ).1
  field_simp
  ring

theorem egbCriticalAGibbsJet_hasDerivAt (x θ u : ℝ) (n : ℕ) :
    HasDerivAt (egbCriticalAGibbsJet x θ n) (egbCriticalAGibbsJet x θ (n + 1) u) u := by
  have he := hasDerivAt_exp u
  have hq := (hasDerivAt_const u ((-1 : ℝ) ^ n * exp x ^ (2 : ℕ) * (1 - 6 * egbCriticalAShape θ))).div
    (he.const_mul (12 * (1 + 2 * egbCriticalAShape θ))) (by
      have hb := (egbCriticalAShape_bounds θ).1
      positivity)
  have h := (((he.div_const 2).add hq).add
    (((he.pow 3).const_mul ((3 : ℝ) ^ n * (3 - 2 * egbCriticalAShape θ))).div_const
      (36 * exp x ^ (2 : ℕ) * (1 + 2 * egbCriticalAShape θ)))).sub
    (((he.pow 2).const_mul ((2 : ℝ) ^ n)).div_const (3 * exp x * (1 + 2 * egbCriticalAShape θ)))
  apply h.congr_deriv
  unfold egbCriticalAGibbsJet
  norm_num only [Nat.cast_ofNat, pow_one]
  simp only [pow_succ]
  have hb := (egbCriticalAShape_bounds θ).1
  field_simp
  ring

theorem egbCriticalALogGibbs_hasDerivAt (x θ l u : ℝ) :
    HasDerivAt (egbCriticalALogGibbs x θ l)
      (egbCriticalAGibbsJet x θ 1 u - egbCriticalAEntropySlope x θ) u := by
  have he : egbCriticalALogGibbs x θ l =
      (fun v => egbCriticalAGibbsJet x θ 0 v - egbCriticalAEntropySlope x θ * (v - l)) :=
    funext (egbCriticalALogGibbs_formula x θ l)
  rw [he]
  have h := (egbCriticalAGibbsJet_hasDerivAt x θ u 0).sub
    (((hasDerivAt_id u).sub_const l).const_mul (egbCriticalAEntropySlope x θ))
  apply h.congr_deriv
  ring

/-- Exact factorization of the actual derivative over the entire positive-radius domain. -/
theorem egbCriticalALogGibbs_derivative_factorization (x θ l u : ℝ) :
    deriv (egbCriticalALogGibbs x θ l) u =
      4 * Real.pi * egbCriticalAPressure x θ / exp u * (exp u - exp x) ^ (3 : ℕ) *
        (exp u + egbCriticalATail θ * exp x) := by
  rw [(egbCriticalALogGibbs_hasDerivAt x θ l u).deriv]
  unfold egbCriticalAGibbsJet egbCriticalAEntropySlope egbCriticalAPressure egbCriticalATail
  have hb := (egbCriticalAShape_bounds θ).1
  have hp : 0 < 3 - 2 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  norm_num only [pow_one]
  field_simp
  ring

theorem egbCriticalALogGibbs_derivative_pos_iff (x θ l u : ℝ) :
    0 < deriv (egbCriticalALogGibbs x θ l) u ↔ x < u := by
  have h₁ : 0 < 4 * Real.pi * egbCriticalAPressure x θ / exp u := by
    have hp := egbCriticalAPressure_pos x θ
    positivity
  have h₂ : 0 < exp u + egbCriticalATail θ * exp x := by
    have ht := egbCriticalATail_pos θ
    positivity
  have ho : Odd (3 : ℕ) := ⟨1, rfl⟩
  rw [egbCriticalALogGibbs_derivative_factorization, mul_pos_iff_of_pos_right h₂,
    mul_pos_iff_of_pos_left h₁, ho.pow_pos_iff, sub_pos, exp_lt_exp]

theorem egbCriticalALogGibbs_derivative_neg_iff (x θ l u : ℝ) :
    deriv (egbCriticalALogGibbs x θ l) u < 0 ↔ u < x := by
  have h₁ : 0 < 4 * Real.pi * egbCriticalAPressure x θ / exp u := by
    have hp := egbCriticalAPressure_pos x θ
    positivity
  have h₂ : 0 < exp u + egbCriticalATail θ * exp x := by
    have ht := egbCriticalATail_pos θ
    positivity
  have ho : Odd (3 : ℕ) := ⟨1, rfl⟩
  rw [egbCriticalALogGibbs_derivative_factorization, ← not_le, mul_nonneg_iff_of_pos_right h₂,
    mul_nonneg_iff_of_pos_left h₁, not_le, ho.pow_neg_iff, sub_neg, exp_lt_exp]

theorem egbCriticalALogGibbs_continuous (x θ l : ℝ) : Continuous (egbCriticalALogGibbs x θ l) :=
  continuous_iff_continuousAt.mpr fun u => (egbCriticalALogGibbs_hasDerivAt x θ l u).continuousAt

theorem egbCriticalALogGibbs_decreases_below (x θ l : ℝ) : StrictAntiOn (egbCriticalALogGibbs x θ l) (Iic x) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic x) (egbCriticalALogGibbs_continuous x θ l).continuousOn
  intro u hu
  rw [interior_Iic] at hu
  exact (egbCriticalALogGibbs_derivative_neg_iff x θ l u).2 hu

theorem egbCriticalALogGibbs_increases_above (x θ l : ℝ) : StrictMonoOn (egbCriticalALogGibbs x θ l) (Ici x) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici x) (egbCriticalALogGibbs_continuous x θ l).continuousOn
  intro u hu
  rw [interior_Ici] at hu
  exact (egbCriticalALogGibbs_derivative_pos_iff x θ l u).2 hu

/-- Every radius except the critical one has strictly larger free energy. -/
theorem egbCriticalALogGibbs_strict_gap (x θ l u : ℝ) :
    egbCriticalALogGibbs x θ l x < egbCriticalALogGibbs x θ l u ↔ u ≠ x := by
  constructor
  · intro h he
    subst u
    exact lt_irrefl _ h
  · intro h
    rcases lt_or_gt_of_ne h with hu | hu
    · exact (egbCriticalALogGibbs_decreases_below x θ l) (le_of_lt hu) (le_refl x) hu
    · exact (egbCriticalALogGibbs_increases_above x θ l) (le_refl x) (le_of_lt hu) hu

theorem egbCriticalALogGibbs_global_minimum (x θ l u : ℝ) :
    egbCriticalALogGibbs x θ l x ≤ egbCriticalALogGibbs x θ l u := by
  by_cases h : u = x
  · subst u
    exact le_refl _
  · exact le_of_lt ((egbCriticalALogGibbs_strict_gap x θ l u).2 h)

theorem egbCriticalALogGibbs_unique_minimum (x θ l u : ℝ) :
    egbCriticalALogGibbs x θ l u = egbCriticalALogGibbs x θ l x ↔ u = x := by
  constructor
  · intro he
    by_contra h
    have hl := (egbCriticalALogGibbs_strict_gap x θ l u).2 h
    rw [he] at hl
    exact lt_irrefl _ hl
  · rintro rfl
    rfl

theorem egbCriticalALogGibbs_value (x θ l : ℝ) :
    egbCriticalALogGibbs x θ l x =
      exp x * (3 + 4 * egbCriticalAShape θ - 12 * egbCriticalAShape θ * (x - l)) /
        (9 * (1 + 2 * egbCriticalAShape θ)) := by
  rw [egbCriticalALogGibbs_formula]
  unfold egbCriticalAGibbsJet egbCriticalAEntropySlope
  have hb := (egbCriticalAShape_bounds θ).1
  norm_num only [pow_zero, one_mul]
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
