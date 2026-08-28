import GaloisForLFunctions.RHTower.FZZCigarParityKreinEigenlineCofinalEscape

/-!
# Cofinal zeta-divisor escape from the full FZZ parity Krein eigenpair

The second literal source eigenline is the conjugate of the positive-imaginary line.  In the
balanced coordinate its phase therefore lies in the open lower-left quadrant, while the first
line lies in the open upper-left quadrant.  Together the full source Krein eigenpair occupies only
the left half of each dyadic Mellin phase period.

The corpus Titchmarsh zero-window theorem supplies an actual zeta zero arbitrarily high near every
sufficiently high integer phase turn.  Such a turn is separated from both source quarters.  Hence,
above every height, an open-strip zeta zero misses both members of the literal source eigenpair at
every positive scale.  This is an unconditional terminal obstruction to divisor completeness for
the two-dimensional Krein block itself, not merely for one chosen orientation.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- Balanced projective coordinate of the negative-imaginary member of the source Krein pair. -/
def fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate
    (beta : ℝ) : ℂ :=
  fzzCigarParitySourceBalancedProjectiveCoordinate beta
    (fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector beta)

/-- The second balanced Krein coordinate is exactly the conjugate of the first. -/
theorem fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate_eq_star
    (beta : ℝ) :
    fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate beta =
      star (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta) := by
  simp [fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate,
    fzzCigarParityDilatedKreinEigenlineBalancedCoordinate,
    fzzCigarParitySourceBalancedProjectiveCoordinate,
    fzzCigarParitySourceProjectiveRatio,
    fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector,
    fzzCigarParityDilatedTwoScaleKreinEigenvector,
    Complex.conj_ofReal]

/-- Principal argument of the conjugate eigenline is the negative of the first argument. -/
theorem fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate_arg
    {beta : ℝ} (hbeta : 0 < beta) :
    Complex.arg
        (fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate beta) =
      -Complex.arg (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta) := by
  rw [fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate_eq_star,
    Complex.star_def, Complex.arg_conj,
    if_neg (ne_of_lt
      (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_arg_lt_pi hbeta))]

/-- The conjugate balanced eigenline lies in the strict lower-left phase quadrant. -/
theorem fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate_arg_window
    {beta : ℝ} (hbeta : 0 < beta) :
    -Real.pi <
        Complex.arg
          (fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate beta) ∧
      Complex.arg
          (fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate beta) <
        -Real.pi / 2 := by
  rw [fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate_arg hbeta]
  constructor <;> linarith [
    fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_pi_div_two_lt_arg hbeta,
    fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_arg_lt_pi hbeta]

/-- The centered dyadic Mellin character commutes with complex conjugation. -/
theorem fzzCigarParityDyadicMellinCharacter_star (rho : ℂ) :
    fzzCigarParityDyadicMellinCharacter (star rho) =
      star (fzzCigarParityDyadicMellinCharacter rho) := by
  rw [fzzCigarParityDyadicMellinCharacter,
    fzzCigarParityDyadicMellinCharacter,
    centeredComplexModularCharacter, centeredComplexModularCharacter]
  rw [show (Real.log 2 : ℂ) * (star rho - 1 / 2) =
      star ((Real.log 2 : ℂ) * (rho - 1 / 2)) by
    change (Real.log 2 : ℂ) * ((starRingEnd ℂ) rho - 1 / 2) =
      (starRingEnd ℂ) ((Real.log 2 : ℂ) * (rho - 1 / 2))
    have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
        simpa using Complex.conj_ofReal (2 : ℝ)
      rw [map_div₀, map_one, htwo]
    rw [map_mul, map_sub, Complex.conj_ofReal, hhalf]]
  exact Complex.exp_conj _

/-- A Mellin character near an integer phase turn cannot equal the conjugate source eigenline at
any fixed positive scale. -/
theorem fzzCigarParityDyadicMellinCharacter_ne_conjugateKreinEigenline_of_near_integer_turn
    {beta : ℝ} (hbeta : 0 < beta) {rho : ℂ} (m : ℤ)
    (hnear : |rho.im - 2 * Real.pi * (m : ℝ) / Real.log 2| <
      fzzCigarParityKreinEigenlineEscapeRadius) :
    fzzCigarParityDyadicMellinCharacter rho ≠
      fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate beta := by
  intro hmatch
  have hstarMatch :
      fzzCigarParityDyadicMellinCharacter (star rho) =
        fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta := by
    rw [fzzCigarParityDyadicMellinCharacter_star, hmatch,
      fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate_eq_star,
      star_star]
  have hstarRe : (star rho).re = 1 / 2 :=
    fzzCigarParityDyadicMellinCharacter_eq_kreinEigenline_forces_critical
      hbeta hstarMatch
  obtain ⟨k, hk⟩ :=
    (fzzCigarParityDyadicMellinCharacter_eq_eigenline_iff_lift_ordinate
      hbeta hstarRe).mp hstarMatch
  have hliftIm :
      (star rho).im =
        (fzzCigarParityDilatedKreinEigenlineCriticalMellinLift beta k).im := by
    rw [hk, fzzCigarParityDilatedKreinEigenlineCriticalMellinLift_im]
  apply fzzCigarParityKreinEigenlineCriticalMellinLift_not_near_integer_turn
    hbeta k (-m)
  rw [← hliftIm]
  have hstarIm : (star rho).im = -rho.im := by
    exact Complex.conj_im rho
  rw [hstarIm]
  have heq :
      -rho.im - 2 * Real.pi * ((-m : ℤ) : ℝ) / Real.log 2 =
        -(rho.im - 2 * Real.pi * (m : ℝ) / Real.log 2) := by
    push_cast
    ring
  rw [heq, abs_neg]
  exact hnear

/-- **Full-pair cofinal divisor escape.** Above every height there is an actual nontrivial zeta
zero whose dyadic Mellin character misses both literal source Krein eigenlines at every positive
physical scale. -/
theorem exists_riemannZeta_zero_not_fzzCigarParityKreinEigenpair_above (H : ℝ) :
    ∃ rho : ℂ,
      riemannZeta rho = 0 ∧ 0 < rho.re ∧ rho.re < 1 ∧ H < rho.im ∧
        ∀ beta : ℝ, 0 < beta →
          fzzCigarParityDyadicMellinCharacter rho ≠
              fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta ∧
            fzzCigarParityDyadicMellinCharacter rho ≠
              fzzCigarParityDilatedConjugateKreinEigenlineBalancedCoordinate beta := by
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
  intro beta hbeta
  constructor
  · intro hmatch
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
  · apply
      fzzCigarParityDyadicMellinCharacter_ne_conjugateKreinEigenline_of_near_integer_turn
        hbeta (m : ℤ)
    simpa only [T, Nat.cast_ofNat, Int.cast_natCast] using hnear

end

end RHTower
