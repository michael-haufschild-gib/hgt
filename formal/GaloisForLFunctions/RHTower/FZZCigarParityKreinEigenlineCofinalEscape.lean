import GaloisForLFunctions.RHTower.FZZCigarParityKreinEigenlinePhaseWindow
import GaloisForLFunctions.RHTower.SuzukiTitchmarshUniqueness
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# Cofinal zeta-divisor escape from the FZZ parity Krein eigenline

The literal positive-imaginary FZZ source eigenline is confined to one quarter of every dyadic
Mellin phase period.  Titchmarsh's shrinking zero-gap theorem, already available unconditionally
in the corpus, forces actual zeta-zero ordinates into arbitrarily small neighbourhoods of every
sufficiently high ordinate.  Applying it at integer phase turns produces cofinally many
nontrivial zeta zeros outside every source-eigenline quarter-window.

This is stronger than a failure at one scale: above every height there is one actual open-strip
zeta zero whose dyadic Mellin character cannot equal the positive-imaginary source eigenline at
any positive physical scale.  Therefore the literal one-eigenline-per-scale construction is
unconditionally divisor-incomplete.  Its sharp survivor is the exact phase-window and critical
fibre classification from the preceding module.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- Radius strictly inside the gap between an integer dyadic phase turn and the nearest source
eigenline quarter-window. -/
def fzzCigarParityKreinEigenlineEscapeRadius : ℝ :=
  Real.pi / (4 * Real.log 2)

theorem fzzCigarParityKreinEigenlineEscapeRadius_pos :
    0 < fzzCigarParityKreinEigenlineEscapeRadius := by
  rw [fzzCigarParityKreinEigenlineEscapeRadius]
  positivity

/-- No logarithmic lift of the positive-imaginary source eigenline enters the fixed neighbourhood
of an integer dyadic phase turn. -/
theorem fzzCigarParityKreinEigenlineCriticalMellinLift_not_near_integer_turn
    {beta : ℝ} (hbeta : 0 < beta) (k m : ℤ) :
    ¬ |(fzzCigarParityDilatedKreinEigenlineCriticalMellinLift beta k).im -
        2 * Real.pi * (m : ℝ) / Real.log 2| <
      fzzCigarParityKreinEigenlineEscapeRadius := by
  intro hnear
  rw [fzzCigarParityDilatedKreinEigenlineCriticalMellinLift_im,
    fzzCigarParityKreinEigenlineEscapeRadius] at hnear
  let theta :=
    Complex.arg (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdiff :
      (theta + 2 * Real.pi * (k : ℝ)) / Real.log 2 -
          2 * Real.pi * (m : ℝ) / Real.log 2 =
        (theta + 2 * Real.pi * ((k - m : ℤ) : ℝ)) / Real.log 2 := by
    push_cast
    ring
  rw [show Complex.arg
      (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta) = theta by rfl,
    hdiff, abs_lt] at hnear
  have hlower :
      -Real.pi / 4 < theta + 2 * Real.pi * ((k - m : ℤ) : ℝ) := by
    have hrewrite : -(Real.pi / (4 * Real.log 2)) =
        (-Real.pi / 4) / Real.log 2 := by
      field_simp
    rw [hrewrite, div_lt_div_iff_of_pos_right hlog] at hnear
    exact hnear.1
  have hupper :
      theta + 2 * Real.pi * ((k - m : ℤ) : ℝ) < Real.pi / 4 := by
    have hrewrite : Real.pi / (4 * Real.log 2) =
        (Real.pi / 4) / Real.log 2 := by
      field_simp
    rw [hrewrite, div_lt_div_iff_of_pos_right hlog] at hnear
    exact hnear.2
  have hthetaLower : Real.pi / 2 < theta := by
    exact fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_pi_div_two_lt_arg hbeta
  have hthetaUpper : theta < Real.pi := by
    exact fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_arg_lt_pi hbeta
  rcases le_or_gt 0 (k - m) with hnonneg | hneg
  · have hcast : (0 : ℝ) ≤ ((k - m : ℤ) : ℝ) := by exact_mod_cast hnonneg
    have hterm : 0 ≤ 2 * Real.pi * ((k - m : ℤ) : ℝ) := by positivity
    linarith
  · have hle : k - m ≤ -1 := by omega
    have hcast : ((k - m : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hle
    have hterm : 2 * Real.pi * ((k - m : ℤ) : ℝ) ≤ -2 * Real.pi := by
      nlinarith
    linarith

/-- Matching a literal positive-imaginary source eigenline already forces critical-line placement,
because the source coordinate is unimodular and the centered dyadic character has radial weight
`exp(log 2 * (Re rho - 1/2))`. -/
theorem fzzCigarParityDyadicMellinCharacter_eq_kreinEigenline_forces_critical
    {beta : ℝ} (hbeta : 0 < beta) {rho : ℂ}
    (hmatch : fzzCigarParityDyadicMellinCharacter rho =
      fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta) :
    rho.re = 1 / 2 := by
  have hnorm := congrArg norm hmatch
  rw [norm_fzzCigarParityDyadicMellinCharacter,
    norm_fzzCigarParityDilatedKreinEigenlineBalancedCoordinate hbeta] at hnorm
  have hnorm' : Real.exp (Real.log 2 * (rho.re - 1 / 2)) = Real.exp 0 := by
    simpa using hnorm
  have harg : Real.log 2 * (rho.re - 1 / 2) = 0 :=
    Real.exp_injective hnorm'
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- **Cofinal divisor escape.** Above every height there is an actual nontrivial zeta zero whose
dyadic Mellin character misses the positive-imaginary literal source eigenline at every positive
physical scale. -/
theorem exists_riemannZeta_zero_not_fzzCigarParityKreinEigenline_above (H : ℝ) :
    ∃ rho : ℂ,
      riemannZeta rho = 0 ∧ 0 < rho.re ∧ rho.re < 1 ∧ H < rho.im ∧
        ∀ beta : ℝ, 0 < beta →
          fzzCigarParityDyadicMellinCharacter rho ≠
            fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta := by
  let delta := fzzCigarParityKreinEigenlineEscapeRadius
  have hdelta : 0 < delta := fzzCigarParityKreinEigenlineEscapeRadius_pos
  obtain ⟨T0, hT0, hwindow⟩ := exists_uniform_riemannZeta_zero_window hdelta
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨m : ℕ, hm⟩ := exists_nat_gt
    (max T0 (H + delta) * Real.log 2 / (2 * Real.pi))
  let T := 2 * Real.pi * (m : ℝ) / Real.log 2
  have hTlarge : max T0 (H + delta) < T := by
    dsimp only [T]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)] at hm
    rw [lt_div_iff₀ hlog]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
  have hT0le : T0 ≤ T := le_trans (le_max_left _ _) hTlarge.le
  obtain ⟨rho, hzeta, hnear⟩ := hwindow T hT0le
  have hrhoH : H < rho.im := by
    rw [abs_lt] at hnear
    have hHT : H + delta < T := lt_of_le_of_lt (le_max_right _ _) hTlarge
    linarith
  have hrhoIm : 0 < rho.im := by
    have hnearLower := (abs_lt.mp hnear).1
    linarith [hT0, hT0le]
  have hstrip := riemannZeta_zero_trivial_or_mem_strip hzeta
  have hrhoStrip : 0 < rho.re ∧ rho.re < 1 := by
    rcases hstrip with htrivial | hnontrivial
    · obtain ⟨n, hn⟩ := htrivial
      have himzero : rho.im = 0 := by rw [hn]; norm_num
      linarith
    · exact hnontrivial
  refine ⟨rho, hzeta, hrhoStrip.1, hrhoStrip.2, hrhoH, ?_⟩
  intro beta hbeta hmatch
  have hrhoRe :=
    fzzCigarParityDyadicMellinCharacter_eq_kreinEigenline_forces_critical
      hbeta hmatch
  obtain ⟨k, hk⟩ :=
    (fzzCigarParityDyadicMellinCharacter_eq_eigenline_iff_lift_ordinate
      hbeta hrhoRe).mp hmatch
  have hliftIm :
      rho.im =
        (fzzCigarParityDilatedKreinEigenlineCriticalMellinLift beta k).im := by
    rw [hk, fzzCigarParityDilatedKreinEigenlineCriticalMellinLift_im]
  apply fzzCigarParityKreinEigenlineCriticalMellinLift_not_near_integer_turn
    hbeta k (m : ℤ)
  rw [← hliftIm]
  simpa only [T, Nat.cast_ofNat, Int.cast_natCast] using hnear

end

end RHTower
