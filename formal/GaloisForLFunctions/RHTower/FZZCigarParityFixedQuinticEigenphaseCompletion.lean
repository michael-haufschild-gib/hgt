import GaloisForLFunctions.RHTower.FZZCigarParityQuadraticEigenphaseCompletion

/-!
# Fixed-quintic eigenphase completion of the FZZ parity source

HC24 proves that four quadratic channels jointly cover the unit circle, but a target still chooses
one channel. This module removes that freedom. Fifth power of the single positive-imaginary literal
source eigenline covers every unit complex phase as physical scale varies. Degrees one through four
each miss an explicit unit phase, so five is the least positive degree with full phase capacity for
one fixed monomial.

Construction is exact and source-first. For a unit phase `z`, its argument selects a fifth-root
angle strictly inside the upper-left quadrant. HC23 realizes that root by the literal source at
positive scale. No zero data and no target-dependent channel are built into the interaction law.

Matching the fixed quintic phase to the centered dyadic Mellin character is exactly critical-line
placement. Consequently fixed-quintic divisor completeness is equivalent to RH; remaining burden
is dynamical incidence of actual parity-delay Mellin zeros, not phase capacity or channel choice.

`[NEW] [MINIMAL FIXED NONLINEAR SOURCE] [UNIT-CIRCLE SURJECTIVITY] [EXACT RH ENDPOINT]
[LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

def fzzCigarParityUpperLeftFifthRootAngle (z : ℂ) : ℝ :=
  if z.arg = Real.pi then 3 * Real.pi / 5 else (z.arg + 4 * Real.pi) / 5

def fzzCigarParityUpperLeftFifthRoot (z : ℂ) : ℂ :=
  Complex.exp ((fzzCigarParityUpperLeftFifthRootAngle z : ℂ) * Complex.I)

theorem fzzCigarParityUpperLeftFifthRootAngle_mem
    (z : ℂ) :
    Real.pi / 2 < fzzCigarParityUpperLeftFifthRootAngle z ∧
      fzzCigarParityUpperLeftFifthRootAngle z < Real.pi := by
  by_cases harg : z.arg = Real.pi
  · rw [fzzCigarParityUpperLeftFifthRootAngle, if_pos harg]
    constructor <;> nlinarith [Real.pi_pos]
  · rw [fzzCigarParityUpperLeftFifthRootAngle, if_neg harg]
    have hlower := Complex.neg_pi_lt_arg z
    have hupper := (Complex.arg_le_pi z).lt_of_ne harg
    constructor <;> nlinarith [Real.pi_pos]

theorem norm_fzzCigarParityUpperLeftFifthRoot (z : ℂ) :
    ‖fzzCigarParityUpperLeftFifthRoot z‖ = 1 := by
  simp [fzzCigarParityUpperLeftFifthRoot, Complex.norm_exp]

theorem fzzCigarParityUpperLeftFifthRoot_re_neg (z : ℂ) :
    (fzzCigarParityUpperLeftFifthRoot z).re < 0 := by
  simp only [fzzCigarParityUpperLeftFifthRoot, Complex.exp_ofReal_mul_I_re]
  exact Real.cos_neg_of_pi_div_two_lt_of_lt
    (fzzCigarParityUpperLeftFifthRootAngle_mem z).1
    (lt_trans (fzzCigarParityUpperLeftFifthRootAngle_mem z).2 (by linarith [Real.pi_pos]))

theorem fzzCigarParityUpperLeftFifthRoot_im_pos (z : ℂ) :
    0 < (fzzCigarParityUpperLeftFifthRoot z).im := by
  simp only [fzzCigarParityUpperLeftFifthRoot, Complex.exp_ofReal_mul_I_im]
  exact Real.sin_pos_of_pos_of_lt_pi
    (lt_trans (by positivity : 0 < Real.pi / 2)
      (fzzCigarParityUpperLeftFifthRootAngle_mem z).1)
    (fzzCigarParityUpperLeftFifthRootAngle_mem z).2

theorem fzzCigarParityUpperLeftFifthRoot_pow_five
    {z : ℂ} (hnorm : ‖z‖ = 1) :
    fzzCigarParityUpperLeftFifthRoot z ^ 5 = z := by
  have hzexp : Complex.exp ((z.arg : ℂ) * Complex.I) = z := by
    simpa [hnorm] using Complex.norm_mul_exp_arg_mul_I z
  by_cases harg : z.arg = Real.pi
  · rw [fzzCigarParityUpperLeftFifthRoot, fzzCigarParityUpperLeftFifthRootAngle,
      if_pos harg, ← Complex.exp_nat_mul]
    calc
      Complex.exp ((5 : ℕ) * (((3 * Real.pi / 5 : ℝ) : ℂ) * Complex.I)) =
          Complex.exp (((z.arg : ℂ) * Complex.I) + (2 : ℂ) * Real.pi * Complex.I) := by
            congr 1
            rw [harg]
            push_cast
            ring
      _ = z := by rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, hzexp]
  · rw [fzzCigarParityUpperLeftFifthRoot, fzzCigarParityUpperLeftFifthRootAngle,
      if_neg harg, ← Complex.exp_nat_mul]
    have hperiod : Complex.exp ((2 : ℂ) * (2 * Real.pi) * Complex.I) = 1 := by
      convert Complex.exp_nat_mul_two_pi_mul_I 2 using 1
      ring_nf
    calc
      Complex.exp ((5 : ℕ) * ((((z.arg + 4 * Real.pi) / 5 : ℝ) : ℂ) * Complex.I)) =
          Complex.exp (((z.arg : ℂ) * Complex.I) +
            (2 : ℂ) * (2 * Real.pi) * Complex.I) := by
              congr 1
              push_cast
              ring
      _ = z := by rw [Complex.exp_add, hperiod, mul_one, hzexp]

/-- One fixed quintic interaction of the literal positive-imaginary source eigenline. -/
def fzzCigarParityFixedQuinticEigenphase (beta : ℝ) : ℂ :=
  fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta ^ 5

theorem norm_fzzCigarParityFixedQuinticEigenphase
    {beta : ℝ} (hbeta : 0 < beta) :
    ‖fzzCigarParityFixedQuinticEigenphase beta‖ = 1 := by
  simp [fzzCigarParityFixedQuinticEigenphase,
    norm_fzzCigarParityDilatedKreinEigenlineBalancedCoordinate hbeta]

theorem exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_of_norm_one
    {z : ℂ} (hnorm : ‖z‖ = 1) :
    ∃ beta : ℝ, 0 < beta ∧ fzzCigarParityFixedQuinticEigenphase beta = z := by
  obtain ⟨beta, hbeta, hy⟩ :=
    exists_pos_fzzCigarParityKreinEigenline_eq_of_unit_upperLeft
      (norm_fzzCigarParityUpperLeftFifthRoot z)
      (fzzCigarParityUpperLeftFifthRoot_re_neg z)
      (fzzCigarParityUpperLeftFifthRoot_im_pos z)
  refine ⟨beta, hbeta, ?_⟩
  rw [fzzCigarParityFixedQuinticEigenphase, hy]
  exact fzzCigarParityUpperLeftFifthRoot_pow_five hnorm

theorem fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_sq_im_neg
    {beta : ℝ} (hbeta : 0 < beta) :
    (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta ^ 2).im < 0 := by
  rw [pow_two, Complex.mul_im]
  have hre := fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re_neg hbeta
  have him := fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_im_pos hbeta
  have hprod :
      (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).re *
        (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).im < 0 :=
    mul_neg_of_neg_of_pos hre him
  nlinarith

theorem fzzCigarParityFixedMonomialDegreeOne_ne_one
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta ^ 1 ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  have hneg := fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re_neg hbeta
  simp at hre
  linarith

theorem fzzCigarParityFixedMonomialDegreeTwo_ne_one
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta ^ 2 ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  have hneg :=
    fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_sq_im_neg hbeta
  simp at him
  linarith

theorem fzzCigarParityFixedMonomialDegreeThree_ne_neg_one
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta ^ 3 ≠ -1 := by
  let y := fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta
  have hre : y.re < 0 :=
    fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re_neg hbeta
  have him : 0 < y.im :=
    fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_im_pos hbeta
  intro h
  have hfactor : (y + 1) * (y ^ 2 - y + 1) = 0 := by
    calc
      (y + 1) * (y ^ 2 - y + 1) = y ^ 3 + 1 := by ring
      _ = 0 := by rw [h]; ring
  rcases mul_eq_zero.mp hfactor with hlinear | hquadratic
  · have himzero := congrArg Complex.im hlinear
    simp at himzero
    linarith
  · have himzero := congrArg Complex.im hquadratic
    simp only [pow_two, Complex.mul_im, sub_im, add_im, one_im] at himzero
    change y.re * y.im + y.im * y.re - y.im + 0 = 0 at himzero
    have hproduct : (2 * y.re - 1) * y.im = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hproduct with hreal | himzero'
    · nlinarith
    · linarith

theorem fzzCigarParityFixedMonomialDegreeFour_ne_one
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta ^ 4 ≠ 1 := by
  let y := fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta
  have hsqneg : (y ^ 2).im < 0 :=
    fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_sq_im_neg hbeta
  intro h
  have hfactor : (y ^ 2 - 1) * (y ^ 2 + 1) = 0 := by
    calc
      (y ^ 2 - 1) * (y ^ 2 + 1) = y ^ 4 - 1 := by ring
      _ = 0 := by rw [h]; ring
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · have himzero := congrArg Complex.im hminus
    simp at himzero
    linarith
  · have himzero := congrArg Complex.im hplus
    simp at himzero
    linarith

/-- Full unit-circle phase capacity of one fixed source monomial. -/
def FZZCigarParityFixedMonomialPhaseComplete (n : ℕ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    ∃ beta : ℝ, 0 < beta ∧
      fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta ^ n = z

theorem fzzCigarParityFixedMonomialPhaseComplete_five :
    FZZCigarParityFixedMonomialPhaseComplete 5 := by
  intro z hnorm
  simpa [FZZCigarParityFixedMonomialPhaseComplete,
    fzzCigarParityFixedQuinticEigenphase] using
    exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_of_norm_one hnorm

theorem not_fzzCigarParityFixedMonomialPhaseComplete_one :
    ¬FZZCigarParityFixedMonomialPhaseComplete 1 := by
  intro hcomplete
  obtain ⟨beta, hbeta, hmatch⟩ := hcomplete 1 (by simp)
  exact fzzCigarParityFixedMonomialDegreeOne_ne_one hbeta hmatch

theorem not_fzzCigarParityFixedMonomialPhaseComplete_two :
    ¬FZZCigarParityFixedMonomialPhaseComplete 2 := by
  intro hcomplete
  obtain ⟨beta, hbeta, hmatch⟩ := hcomplete 1 (by simp)
  exact fzzCigarParityFixedMonomialDegreeTwo_ne_one hbeta hmatch

theorem not_fzzCigarParityFixedMonomialPhaseComplete_three :
    ¬FZZCigarParityFixedMonomialPhaseComplete 3 := by
  intro hcomplete
  obtain ⟨beta, hbeta, hmatch⟩ := hcomplete (-1) (by simp)
  exact fzzCigarParityFixedMonomialDegreeThree_ne_neg_one hbeta hmatch

theorem not_fzzCigarParityFixedMonomialPhaseComplete_four :
    ¬FZZCigarParityFixedMonomialPhaseComplete 4 := by
  intro hcomplete
  obtain ⟨beta, hbeta, hmatch⟩ := hcomplete 1 (by simp)
  exact fzzCigarParityFixedMonomialDegreeFour_ne_one hbeta hmatch

/-- Degree five is the least positive fixed monomial degree with complete phase capacity. -/
theorem fzzCigarParityFixedMonomialPhaseComplete_five_minimal :
    FZZCigarParityFixedMonomialPhaseComplete 5 ∧
      ∀ n : ℕ, 0 < n → n < 5 → ¬FZZCigarParityFixedMonomialPhaseComplete n := by
  refine ⟨fzzCigarParityFixedMonomialPhaseComplete_five, ?_⟩
  intro n hn hn5
  interval_cases n
  · exact not_fzzCigarParityFixedMonomialPhaseComplete_one
  · exact not_fzzCigarParityFixedMonomialPhaseComplete_two
  · exact not_fzzCigarParityFixedMonomialPhaseComplete_three
  · exact not_fzzCigarParityFixedMonomialPhaseComplete_four

/-- Matching the fixed quintic source phase forces critical-line placement. -/
theorem fzzCigarParityDyadicMellinCharacter_eq_fixedQuintic_forces_critical
    {beta : ℝ} (hbeta : 0 < beta) {rho : ℂ}
    (hmatch : fzzCigarParityDyadicMellinCharacter rho =
      fzzCigarParityFixedQuinticEigenphase beta) :
    rho.re = 1 / 2 := by
  have hnorm := congrArg norm hmatch
  rw [norm_fzzCigarParityDyadicMellinCharacter,
    norm_fzzCigarParityFixedQuinticEigenphase hbeta] at hnorm
  have hnorm' : Real.exp (Real.log 2 * (rho.re - 1 / 2)) = Real.exp 0 := by
    simpa using hnorm
  have harg : Real.log 2 * (rho.re - 1 / 2) = 0 :=
    Real.exp_injective hnorm'
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

theorem exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_dyadicMellinCharacter
    {rho : ℂ} (hrho : rho.re = 1 / 2) :
    ∃ beta : ℝ, 0 < beta ∧
      fzzCigarParityFixedQuinticEigenphase beta =
        fzzCigarParityDyadicMellinCharacter rho := by
  apply exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_of_norm_one
  rw [norm_fzzCigarParityDyadicMellinCharacter, hrho]
  norm_num

theorem exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_dyadicMellinCharacter_iff
    (rho : ℂ) :
    (∃ beta : ℝ, 0 < beta ∧
      fzzCigarParityFixedQuinticEigenphase beta =
        fzzCigarParityDyadicMellinCharacter rho) ↔
      rho.re = 1 / 2 := by
  constructor
  · rintro ⟨beta, hbeta, hmatch⟩
    exact fzzCigarParityDyadicMellinCharacter_eq_fixedQuintic_forces_critical
      hbeta hmatch.symm
  · exact exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_dyadicMellinCharacter

/-- Every open-strip zeta divisor lands in one fixed quintic source phase orbit. -/
def FZZCigarParityFixedQuinticEigenphaseDivisorComplete : Prop :=
  ∀ rho : ℂ, riemannZeta rho = 0 → 0 < rho.re → rho.re < 1 →
    ∃ beta : ℝ, 0 < beta ∧
      fzzCigarParityFixedQuinticEigenphase beta =
        fzzCigarParityDyadicMellinCharacter rho

/-- Fixed-quintic source incidence on the open zeta divisor is exactly RH. -/
theorem fzzCigarParityFixedQuinticEigenphaseDivisorComplete_iff_rh :
    FZZCigarParityFixedQuinticEigenphaseDivisorComplete ↔ RiemannHypothesis := by
  constructor
  · intro hcomplete
    rw [riemannHypothesis_iff_forall_zero_re_le_half]
    intro rho hz
    rcases riemannZeta_zero_trivial_or_mem_strip hz with htrivial | hstrip
    · obtain ⟨n, rfl⟩ := htrivial
      rw [show (-(2 * ((n : ℂ) + 1))) =
          ((-(2 * ((n : ℝ) + 1)) : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · exact le_of_eq
        ((exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_dyadicMellinCharacter_iff
          rho).mp (hcomplete rho hz hstrip.1 hstrip.2))
  · intro hRH rho hz h0 h1
    have htrivial : ¬ ∃ n : ℕ, rho = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, hn⟩
      rw [hn, show (-2 * ((n : ℂ) + 1)) =
          ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re] at h0
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hrho : rho.re = 1 / 2 :=
      hRH rho hz htrivial (riemannZeta_zero_ne_one hz)
    exact exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_dyadicMellinCharacter hrho

end

end RHTower
