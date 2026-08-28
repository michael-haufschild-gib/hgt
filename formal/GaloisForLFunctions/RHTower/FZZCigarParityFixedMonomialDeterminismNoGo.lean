import GaloisForLFunctions.RHTower.FZZCigarParityFixedQuinticEigenphaseCompletion

/-!
# Fixed-monomial determinism no-go for the FZZ parity source

HC25 proves that degree five is the least fixed monomial power of the literal balanced source
eigenline with full unit-circle phase capacity. This module audits whether any fixed monomial can
also determine physical scale uniquely.

The answer is no. Degrees zero through four are phase-incomplete. At every degree `n >= 5`, two
explicit upper-left unit roots at angles `3*pi/4 - pi/n` and `3*pi/4 + pi/n` are distinct but have
the same `n`th power. HC23 realizes both roots at positive source scales; those scales are distinct.
Thus every phase-complete fixed monomial has a constructive two-scale collision.

This retires phase-only fixed-monomial determinism while preserving HC25's complete phase capacity.
Any literal dynamical landing law must carry an additional source observable, orientation, or branch
label capable of resolving the collision.

`[NEW] [SHARP NO-GO] [CONSTRUCTIVE COLLISION] [POSITIVE SURVIVOR] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

def fzzCigarParityFixedMonomialLowerCollisionAngle (n : ℕ) : ℝ :=
  3 * Real.pi / 4 - Real.pi / n

def fzzCigarParityFixedMonomialUpperCollisionAngle (n : ℕ) : ℝ :=
  3 * Real.pi / 4 + Real.pi / n

def fzzCigarParityFixedMonomialLowerCollisionRoot (n : ℕ) : ℂ :=
  Complex.exp ((fzzCigarParityFixedMonomialLowerCollisionAngle n : ℂ) * Complex.I)

def fzzCigarParityFixedMonomialUpperCollisionRoot (n : ℕ) : ℂ :=
  Complex.exp ((fzzCigarParityFixedMonomialUpperCollisionAngle n : ℂ) * Complex.I)

theorem fzzCigarParityFixedMonomialCollisionAngles_mem
    {n : ℕ} (hn : 5 ≤ n) :
    Real.pi / 2 < fzzCigarParityFixedMonomialLowerCollisionAngle n ∧
      fzzCigarParityFixedMonomialLowerCollisionAngle n < Real.pi ∧
      Real.pi / 2 < fzzCigarParityFixedMonomialUpperCollisionAngle n ∧
      fzzCigarParityFixedMonomialUpperCollisionAngle n < Real.pi := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hdiv : Real.pi / (n : ℝ) ≤ Real.pi / 5 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR
  have hquarter : Real.pi / 5 < Real.pi / 4 := by nlinarith [Real.pi_pos]
  have hoff : Real.pi / (n : ℝ) < Real.pi / 4 := lt_of_le_of_lt hdiv hquarter
  have hoffpos : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnpos
  simp only [fzzCigarParityFixedMonomialLowerCollisionAngle,
    fzzCigarParityFixedMonomialUpperCollisionAngle]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem norm_fzzCigarParityFixedMonomialLowerCollisionRoot (n : ℕ) :
    ‖fzzCigarParityFixedMonomialLowerCollisionRoot n‖ = 1 := by
  simp [fzzCigarParityFixedMonomialLowerCollisionRoot, Complex.norm_exp]

theorem norm_fzzCigarParityFixedMonomialUpperCollisionRoot (n : ℕ) :
    ‖fzzCigarParityFixedMonomialUpperCollisionRoot n‖ = 1 := by
  simp [fzzCigarParityFixedMonomialUpperCollisionRoot, Complex.norm_exp]

theorem fzzCigarParityFixedMonomialLowerCollisionRoot_re_neg
    {n : ℕ} (hn : 5 ≤ n) :
    (fzzCigarParityFixedMonomialLowerCollisionRoot n).re < 0 := by
  simp only [fzzCigarParityFixedMonomialLowerCollisionRoot,
    Complex.exp_ofReal_mul_I_re]
  exact Real.cos_neg_of_pi_div_two_lt_of_lt
    (fzzCigarParityFixedMonomialCollisionAngles_mem hn).1
    (lt_trans (fzzCigarParityFixedMonomialCollisionAngles_mem hn).2.1
      (by linarith [Real.pi_pos]))

theorem fzzCigarParityFixedMonomialLowerCollisionRoot_im_pos
    {n : ℕ} (hn : 5 ≤ n) :
    0 < (fzzCigarParityFixedMonomialLowerCollisionRoot n).im := by
  simp only [fzzCigarParityFixedMonomialLowerCollisionRoot,
    Complex.exp_ofReal_mul_I_im]
  exact Real.sin_pos_of_pos_of_lt_pi
    (lt_trans (by positivity : 0 < Real.pi / 2)
      (fzzCigarParityFixedMonomialCollisionAngles_mem hn).1)
    (fzzCigarParityFixedMonomialCollisionAngles_mem hn).2.1

theorem fzzCigarParityFixedMonomialUpperCollisionRoot_re_neg
    {n : ℕ} (hn : 5 ≤ n) :
    (fzzCigarParityFixedMonomialUpperCollisionRoot n).re < 0 := by
  simp only [fzzCigarParityFixedMonomialUpperCollisionRoot,
    Complex.exp_ofReal_mul_I_re]
  exact Real.cos_neg_of_pi_div_two_lt_of_lt
    (fzzCigarParityFixedMonomialCollisionAngles_mem hn).2.2.1
    (lt_trans (fzzCigarParityFixedMonomialCollisionAngles_mem hn).2.2.2
      (by linarith [Real.pi_pos]))

theorem fzzCigarParityFixedMonomialUpperCollisionRoot_im_pos
    {n : ℕ} (hn : 5 ≤ n) :
    0 < (fzzCigarParityFixedMonomialUpperCollisionRoot n).im := by
  simp only [fzzCigarParityFixedMonomialUpperCollisionRoot,
    Complex.exp_ofReal_mul_I_im]
  exact Real.sin_pos_of_pos_of_lt_pi
    (lt_trans (by positivity : 0 < Real.pi / 2)
      (fzzCigarParityFixedMonomialCollisionAngles_mem hn).2.2.1)
    (fzzCigarParityFixedMonomialCollisionAngles_mem hn).2.2.2

theorem fzzCigarParityFixedMonomialCollisionRoots_ne
    {n : ℕ} (hn : 5 ≤ n) :
    fzzCigarParityFixedMonomialLowerCollisionRoot n ≠
      fzzCigarParityFixedMonomialUpperCollisionRoot n := by
  have hbounds := fzzCigarParityFixedMonomialCollisionAngles_mem hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hoffpos : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnpos
  have hangle :
      fzzCigarParityFixedMonomialLowerCollisionAngle n <
        fzzCigarParityFixedMonomialUpperCollisionAngle n := by
    simp only [fzzCigarParityFixedMonomialLowerCollisionAngle,
      fzzCigarParityFixedMonomialUpperCollisionAngle]
    linarith
  have hcos := Real.strictAntiOn_cos
    (show fzzCigarParityFixedMonomialLowerCollisionAngle n ∈
        Set.Icc (0 : ℝ) Real.pi by exact ⟨by linarith [Real.pi_pos], hbounds.2.1.le⟩)
    (show fzzCigarParityFixedMonomialUpperCollisionAngle n ∈
        Set.Icc (0 : ℝ) Real.pi by exact ⟨by linarith [Real.pi_pos], hbounds.2.2.2.le⟩)
    hangle
  intro heq
  have hre := congrArg Complex.re heq
  simp only [fzzCigarParityFixedMonomialLowerCollisionRoot,
    fzzCigarParityFixedMonomialUpperCollisionRoot,
    Complex.exp_ofReal_mul_I_re] at hre
  linarith

theorem fzzCigarParityFixedMonomialCollisionRoots_pow_eq
    {n : ℕ} (hn : 5 ≤ n) :
    fzzCigarParityFixedMonomialLowerCollisionRoot n ^ n =
      fzzCigarParityFixedMonomialUpperCollisionRoot n ^ n := by
  have hnzero : (n : ℂ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  rw [fzzCigarParityFixedMonomialLowerCollisionRoot,
    fzzCigarParityFixedMonomialUpperCollisionRoot,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  calc
    Complex.exp ((n : ℕ) *
        ((fzzCigarParityFixedMonomialLowerCollisionAngle n : ℂ) * Complex.I)) =
      Complex.exp ((n : ℕ) *
        ((fzzCigarParityFixedMonomialUpperCollisionAngle n : ℂ) * Complex.I) -
          (2 : ℂ) * Real.pi * Complex.I) := by
            congr 1
            simp only [fzzCigarParityFixedMonomialLowerCollisionAngle,
              fzzCigarParityFixedMonomialUpperCollisionAngle]
            push_cast
            field_simp
            ring
    _ = Complex.exp ((n : ℕ) *
        ((fzzCigarParityFixedMonomialUpperCollisionAngle n : ℂ) * Complex.I)) := by
          exact Complex.exp_periodic.sub_eq _

/-- Every phase-complete monomial degree has an explicit collision at two positive source scales. -/
theorem exists_distinct_pos_fzzCigarParityFixedMonomialEigenphase_eq
    {n : ℕ} (hn : 5 ≤ n) :
    ∃ beta₁ beta₂ : ℝ,
      0 < beta₁ ∧ 0 < beta₂ ∧ beta₁ ≠ beta₂ ∧
        fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta₁ ^ n =
          fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta₂ ^ n := by
  obtain ⟨beta₁, hbeta₁, hy₁⟩ :=
    exists_pos_fzzCigarParityKreinEigenline_eq_of_unit_upperLeft
      (norm_fzzCigarParityFixedMonomialLowerCollisionRoot n)
      (fzzCigarParityFixedMonomialLowerCollisionRoot_re_neg hn)
      (fzzCigarParityFixedMonomialLowerCollisionRoot_im_pos hn)
  obtain ⟨beta₂, hbeta₂, hy₂⟩ :=
    exists_pos_fzzCigarParityKreinEigenline_eq_of_unit_upperLeft
      (norm_fzzCigarParityFixedMonomialUpperCollisionRoot n)
      (fzzCigarParityFixedMonomialUpperCollisionRoot_re_neg hn)
      (fzzCigarParityFixedMonomialUpperCollisionRoot_im_pos hn)
  have hbetane : beta₁ ≠ beta₂ := by
    intro heq
    apply fzzCigarParityFixedMonomialCollisionRoots_ne hn
    rw [← hy₁, ← hy₂, heq]
  refine ⟨beta₁, beta₂, hbeta₁, hbeta₂, hbetane, ?_⟩
  rw [hy₁, hy₂]
  exact fzzCigarParityFixedMonomialCollisionRoots_pow_eq hn

/-- Scale determinism of the degree-`n` fixed monomial phase on positive physical scales. -/
def FZZCigarParityFixedMonomialPhaseScaleInjective (n : ℕ) : Prop :=
  Set.InjOn
    (fun beta : ℝ =>
      fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta ^ n)
    (Set.Ioi 0)

theorem not_fzzCigarParityFixedMonomialPhaseScaleInjective_of_five_le
    {n : ℕ} (hn : 5 ≤ n) :
    ¬FZZCigarParityFixedMonomialPhaseScaleInjective n := by
  intro hinjective
  obtain ⟨beta₁, beta₂, hbeta₁, hbeta₂, hne, heq⟩ :=
    exists_distinct_pos_fzzCigarParityFixedMonomialEigenphase_eq hn
  exact hne (hinjective hbeta₁ hbeta₂ heq)

theorem not_fzzCigarParityFixedMonomialPhaseComplete_zero :
    ¬FZZCigarParityFixedMonomialPhaseComplete 0 := by
  intro hcomplete
  obtain ⟨beta, hbeta, hmatch⟩ := hcomplete (-1) (by simp)
  norm_num at hmatch

/-- Every phase-complete fixed monomial has an explicit two-scale collision. -/
theorem exists_distinct_pos_fzzCigarParityFixedMonomialEigenphase_eq_of_complete
    {n : ℕ} (hcomplete : FZZCigarParityFixedMonomialPhaseComplete n) :
    ∃ beta₁ beta₂ : ℝ,
      0 < beta₁ ∧ 0 < beta₂ ∧ beta₁ ≠ beta₂ ∧
        fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta₁ ^ n =
          fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta₂ ^ n := by
  have hn : 5 ≤ n := by
    by_contra hn
    have hnlt : n < 5 := by omega
    interval_cases n
    · exact not_fzzCigarParityFixedMonomialPhaseComplete_zero hcomplete
    · exact not_fzzCigarParityFixedMonomialPhaseComplete_one hcomplete
    · exact not_fzzCigarParityFixedMonomialPhaseComplete_two hcomplete
    · exact not_fzzCigarParityFixedMonomialPhaseComplete_three hcomplete
    · exact not_fzzCigarParityFixedMonomialPhaseComplete_four hcomplete
  exact exists_distinct_pos_fzzCigarParityFixedMonomialEigenphase_eq hn

/-- **Sharp phase-only determinism no-go.** No fixed monomial of the literal FZZ source eigenline
is simultaneously unit-circle complete and injective in positive physical scale. -/
theorem not_fzzCigarParityFixedMonomialPhaseComplete_and_scaleInjective
    (n : ℕ) :
    ¬(FZZCigarParityFixedMonomialPhaseComplete n ∧
      FZZCigarParityFixedMonomialPhaseScaleInjective n) := by
  rintro ⟨hcomplete, hinjective⟩
  by_cases hn : n < 5
  · interval_cases n
    · exact not_fzzCigarParityFixedMonomialPhaseComplete_zero hcomplete
    · exact not_fzzCigarParityFixedMonomialPhaseComplete_one hcomplete
    · exact not_fzzCigarParityFixedMonomialPhaseComplete_two hcomplete
    · exact not_fzzCigarParityFixedMonomialPhaseComplete_three hcomplete
    · exact not_fzzCigarParityFixedMonomialPhaseComplete_four hcomplete
  · exact not_fzzCigarParityFixedMonomialPhaseScaleInjective_of_five_le
      (by omega) hinjective

end

end RHTower
