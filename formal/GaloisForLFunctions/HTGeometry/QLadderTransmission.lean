import GaloisForLFunctions.HTGeometry.OpenFamilyCDDShell

/-!
# The geometric-ladder transmission germ

A reflectionless Schrödinger operator with geometric discrete spectrum `-κ² q^{2n}` has the
transmission coefficient `∏_{n ≥ 0} (k + i κ q^n)/(k - i κ q^n)`.  In the crossing coordinate
`z = i κ / k` this is the germ `F_q(z) = ∏_{n ≥ 0} (1 + q^n z)/(1 - q^n z)`.

This file constructs that germ unconditionally: normal convergence on the unit disc, the exact
one-shell `q`-difference equation `F_q(z) = ((1 + z)/(1 - z)) · F_q(q z)`, unimodularity on the
imaginary axis, and the identification with the transmission product in the momentum variable.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- One factor of the geometric-ladder transmission product. -/
noncomputable def qLadderFactor (q z : ℂ) (n : ℕ) : ℂ := (1 + q ^ n * z) / (1 - q ^ n * z)

/-- The geometric-ladder transmission germ in the crossing coordinate. -/
noncomputable def qLadderTransmission (q z : ℂ) : ℂ := ∏' n : ℕ, qLadderFactor q z n

@[simp]
theorem qLadderFactor_zero (q z : ℂ) : qLadderFactor q z 0 = (1 + z) / (1 - z) := by
  simp [qLadderFactor]

/-- Scaling the crossing coordinate shifts the ladder index by one. -/
theorem qLadderFactor_succ (q z : ℂ) (n : ℕ) :
    qLadderFactor q z (n + 1) = qLadderFactor q (q * z) n := by
  unfold qLadderFactor
  rw [pow_succ]
  ring_nf

theorem norm_qLadderScale_lt_one {q z : ℂ} (hq : ‖q‖ ≤ 1) (hz : ‖z‖ < 1) (n : ℕ) :
    ‖q ^ n * z‖ < 1 := by
  rw [norm_mul, norm_pow]
  calc ‖q‖ ^ n * ‖z‖ ≤ 1 ^ n * ‖z‖ := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg q) hq n) (norm_nonneg z)
    _ = ‖z‖ := by rw [one_pow, one_mul]
    _ < 1 := hz

theorem one_sub_qLadderScale_ne_zero {q z : ℂ} (hq : ‖q‖ ≤ 1) (hz : ‖z‖ < 1) (n : ℕ) :
    1 - q ^ n * z ≠ 0 := by
  intro h
  have := norm_qLadderScale_lt_one hq hz n
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at this
  exact absurd this (lt_irrefl 1)

theorem one_sub_norm_le_norm_one_sub {q z : ℂ} (hq : ‖q‖ ≤ 1) (_hz : ‖z‖ < 1) (n : ℕ) :
    1 - ‖z‖ ≤ ‖1 - q ^ n * z‖ := by
  have hle : ‖q ^ n * z‖ ≤ ‖z‖ := by
    rw [norm_mul, norm_pow]
    calc ‖q‖ ^ n * ‖z‖ ≤ 1 ^ n * ‖z‖ := by
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg q) hq n) (norm_nonneg z)
      _ = ‖z‖ := by rw [one_pow, one_mul]
  have h1 : ‖(1 : ℂ)‖ - ‖q ^ n * z‖ ≤ ‖1 - q ^ n * z‖ := norm_sub_norm_le _ _
  rw [norm_one] at h1
  linarith

/-- Each ladder factor differs from one by a geometrically small amount. -/
theorem qLadderFactor_eq_one_add {q z : ℂ} (hq : ‖q‖ ≤ 1) (hz : ‖z‖ < 1) (n : ℕ) :
    qLadderFactor q z n = 1 + (2 * (q ^ n * z)) / (1 - q ^ n * z) := by
  have h := one_sub_qLadderScale_ne_zero hq hz n
  unfold qLadderFactor
  field_simp
  ring

/-- **Normal convergence of the geometric-ladder product on the unit disc.** -/
theorem multipliable_qLadderFactor {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Multipliable (qLadderFactor q z) := by
  have hq1 : ‖q‖ ≤ 1 := le_of_lt hq
  have hzpos : 0 < 1 - ‖z‖ := by linarith
  have hsummable : Summable fun n : ℕ =>
      ‖(2 * (q ^ n * z)) / (1 - q ^ n * z)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (((summable_geometric_of_lt_one (norm_nonneg q) hq)).mul_left (2 * ‖z‖ / (1 - ‖z‖)))
    have hden : 0 < ‖1 - q ^ n * z‖ :=
      lt_of_lt_of_le hzpos (one_sub_norm_le_norm_one_sub hq1 hz n)
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, div_le_iff₀ hden]
    have hstep : 2 * ‖z‖ / (1 - ‖z‖) * ‖q‖ ^ n * (1 - ‖z‖)
        ≤ 2 * ‖z‖ / (1 - ‖z‖) * ‖q‖ ^ n * ‖1 - q ^ n * z‖ := by
      apply mul_le_mul_of_nonneg_left (one_sub_norm_le_norm_one_sub hq1 hz n)
      positivity
    refine le_trans (le_of_eq ?_) hstep
    field_simp
  have hone := multipliable_one_add_of_summable hsummable
  have hfun : (fun n : ℕ => 1 + (2 * (q ^ n * z)) / (1 - q ^ n * z))
      = qLadderFactor q z := by
    funext n
    exact (qLadderFactor_eq_one_add hq1 hz n).symm
  rwa [hfun] at hone

/-- **The exact one-shell `q`-difference equation of the transmission germ.** -/
theorem qLadderTransmission_one_shell {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    qLadderTransmission q z = (1 + z) / (1 - z) * qLadderTransmission q (q * z) := by
  have hqz : ‖q * z‖ < 1 := by
    rw [norm_mul]
    calc ‖q‖ * ‖z‖ < 1 * 1 := by
          exact mul_lt_mul'' hq hz (norm_nonneg q) (norm_nonneg z)
      _ = 1 := one_mul 1
  have hshift : (fun n : ℕ => qLadderFactor q z (n + 1)) = qLadderFactor q (q * z) := by
    funext n
    exact qLadderFactor_succ q z n
  have hmul : Multipliable fun n : ℕ => qLadderFactor q z (n + 1) := by
    rw [hshift]
    exact multipliable_qLadderFactor hq hqz
  rw [qLadderTransmission, tprod_eq_zero_mul' hmul, qLadderFactor_zero]
  congr 1
  rw [qLadderTransmission]
  exact tprod_congr fun n => congrFun hshift n

/-- The complex modulus as a monoid homomorphism. -/
noncomputable def normMonoidHomC : ℂ →* ℝ where
  toFun := norm
  map_one' := norm_one
  map_mul' := norm_mul

/-- On the imaginary axis every ladder factor is unimodular. -/
theorem norm_qLadderFactor_eq_one {q : ℝ} {z : ℂ} (hz : z.re = 0) (n : ℕ) :
    ‖qLadderFactor ((q : ℝ) : ℂ) z n‖ = 1 := by
  have hre : ((((q : ℝ) : ℂ) ^ n * z)).re = 0 := by
    simp [Complex.mul_re, ← Complex.ofReal_pow, hz]
  have hsym : ‖(1 : ℂ) - ((q : ℝ) : ℂ) ^ n * z‖ = ‖(1 : ℂ) + ((q : ℝ) : ℂ) ^ n * z‖ := by
    have := norm_sub_eq_norm_add_of_re_eq_zero (1 : ℝ) hre
    simpa using this
  have hne : (1 : ℂ) + ((q : ℝ) : ℂ) ^ n * z ≠ 0 := by
    intro h
    have hzero : ((1 : ℂ) + ((q : ℝ) : ℂ) ^ n * z).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re, hre] at hzero
    norm_num at hzero
  unfold qLadderFactor
  rw [norm_div, hsym, div_self (norm_ne_zero_iff.mpr hne)]

/-- **Unimodularity of the transmission germ on the imaginary axis.**  This is the reflectionless
unitarity `|T(k)| = 1` for real momentum. -/
theorem norm_qLadderTransmission_eq_one {q : ℝ} {z : ℂ}
    (hq : ‖((q : ℝ) : ℂ)‖ < 1) (hzn : ‖z‖ < 1) (hz : z.re = 0) :
    ‖qLadderTransmission ((q : ℝ) : ℂ) z‖ = 1 := by
  have hmul := multipliable_qLadderFactor hq hzn
  have hmap := hmul.hasProd.map normMonoidHomC continuous_norm
  have hone : (fun n : ℕ => ‖qLadderFactor ((q : ℝ) : ℂ) z n‖) = fun _ : ℕ => (1 : ℝ) := by
    funext n
    exact norm_qLadderFactor_eq_one hz n
  have hval : HasProd (fun _ : ℕ => (1 : ℝ))
      (normMonoidHomC (qLadderTransmission ((q : ℝ) : ℂ) z)) := by
    rw [← hone]
    exact hmap
  have := hval.tprod_eq
  rw [tprod_one] at this
  exact this.symm

/-- **The momentum-variable transmission product.**  For nonzero momentum the physical product
`∏ (k + i κ q^n)/(k - i κ q^n)` is the ladder factor at the crossing coordinate `i κ / k`. -/
theorem qLadderFactor_momentum {q kappa k : ℂ} (hk : k ≠ 0) (n : ℕ) :
    (k + Complex.I * kappa * q ^ n) / (k - Complex.I * kappa * q ^ n)
      = qLadderFactor q (Complex.I * kappa / k) n := by
  unfold qLadderFactor
  have h1 : 1 + q ^ n * (Complex.I * kappa / k)
      = (k + Complex.I * kappa * q ^ n) / k := by
    field_simp
  have h2 : 1 - q ^ n * (Complex.I * kappa / k)
      = (k - Complex.I * kappa * q ^ n) / k := by
    field_simp
  rw [h1, h2]
  by_cases hB : k - Complex.I * kappa * q ^ n = 0
  · rw [hB, zero_div, div_zero, div_zero]
  · field_simp

/-- The geometric ladder of wave numbers is absolutely summable. -/
theorem summable_qLadderWaveNumbers (kappa : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ => kappa * q ^ n :=
  (summable_geometric_of_lt_one hq0 hq1).mul_left kappa

end GaloisForLFunctions.HTGeometry
