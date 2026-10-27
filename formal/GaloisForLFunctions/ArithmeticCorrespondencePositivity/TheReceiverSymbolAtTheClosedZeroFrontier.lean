import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheReceiverEnergyGrowthAtTheZeroAbscissa
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The receiver at the endpoint zero abscissa

The symbol identity only excludes the actual pole of the shifted zeta factor.
When the zero abscissa equals one, approaching lines lie strictly right of
that pole. The zero-free closed half-plane for the residue unit then gives
uniform bounds on compact height windows, including their boundary.
-/

open Complex Set Filter Topology MeasureTheory Metric
open RHTower RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The actual symbol agrees with its meromorphic formula whenever the
numerator lies below one and the shifted line avoids the pole at one. -/
theorem lineSymbol_receiver_eq_centered_ne_pole {ε e : ℝ}
    (hε : 0 < ε) (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2) (he : 0 < e)
    (hupper : zetaZeroAbscissa - ε + e < 1) (hne : zetaZeroAbscissa + e ≠ 1)
    (y : ℝ) :
    lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y =
      centeredReceiverSymbol ε (((zetaZeroAbscissa - ε + e : ℝ) : ℂ) + (y : ℂ) * I) := by
  obtain ⟨C, hC, hE⟩ := exists_receiver_energy_le_of_zeroAbscissa hε
    (κ := 2 * (zetaZeroAbscissa - ε - 1 / 2) + e)
    (max_lt (by linarith) (by linarith))
  let s : ℂ := ((zetaZeroAbscissa - ε + e : ℝ) : ℂ) + (y : ℂ) * I
  have hsre : s.re = zetaZeroAbscissa - ε + e := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre, one_re] at this
    linarith
  have hse1 : s + (ε : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, one_re, hsre] at this
    exact hne (by linarith)
  have hζ : riemannZeta (s + (ε : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_zetaZeroAbscissa_lt
      (by simp only [add_re, ofReal_re, hsre]; linarith)
  have hε1 : ε < 1 := by linarith [zetaZeroAbscissa_le_one]
  have hΦ := complexMellinPairing_receiver_eq hε hε1 hC (by linarith) hE
    (s := s) (by rw [hsre]; linarith) (by rw [hsre]; exact hupper) hζ hse1
  rw [lineSymbol_receiver_eq hC (by linarith) hE (by linarith)]
  rw [show zetaZeroAbscissa - ε - 1 / 2 + e + 1 / 2 =
    zetaZeroAbscissa - ε + e by ring]
  change complexMellinPairing (receiver ε) s / s = centeredReceiverSymbol ε s
  rw [hΦ, centeredReceiverSymbol_eq hs1, invZeta_eq_inv hse1,
    invZeta_one_add_eq_dampedDensity hε]
  ring

/-- If the zero abscissa is one, no compact height window contains a boundary
pole, and the actual spectral symbol remains uniformly bounded there. -/
theorem exists_receiver_lineSymbol_compact_bound_of_abscissa_one {ε : ℝ}
    (hε : 0 < ε) (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2)
    (hΘ : zetaZeroAbscissa = 1) (a b : ℝ) :
    ∃ η > 0, ∃ B : ℝ, 0 ≤ B ∧ ∀ e ∈ Ioo 0 η, ∀ y ∈ Icc a b,
      ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ≤ B := by
  let σ : ℝ := zetaZeroAbscissa - ε
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσ1 : σ + η < 1 := by dsimp [σ, η]; rw [hΘ]; linarith
  let R : ℝ := |σ| + |a| + |b| + 3
  let K : Set ℂ := closedBall 0 R ∩ {s : ℂ | σ ≤ s.re ∧ s.re ≤ σ + η}
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) R).inter_right
    ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const))
  have hs0 : ∀ s ∈ K, s ≠ 0 := by
    intro s hs h
    have := hs.2.1
    rw [h, zero_re] at this
    linarith
  have hs1 : ∀ s ∈ K, s ≠ 1 := by
    intro s hs h
    have := hs.2.2
    rw [h, one_re] at this
    linarith
  have hunit : ∀ s ∈ K, zetaResidueUnit (s + (ε : ℂ)) ≠ 0 := by
    intro s hs
    by_cases hp : s + (ε : ℂ) = 1
    · simp [hp]
    · apply (zetaResidueUnit_ne_zero_iff hp).mpr
      apply riemannZeta_ne_zero_of_one_le_re
      have hlo := hs.2.1
      dsimp only [σ] at hlo
      simp only [add_re, ofReal_re]
      rw [hΘ] at hlo
      linarith
  have hc : ContinuousOn (centeredReceiverSymbol ε) K := by
    have hq : ContinuousOn (fun s : ℂ => riemannZeta s *
        (invZeta (s + (ε : ℂ)) - invZeta (1 + (ε : ℂ))) / s) K := by
      intro s hs
      have hi : ContinuousAt (fun z : ℂ => invZeta (z + (ε : ℂ))) s :=
        (differentiableAt_invZeta (hunit s hs)).continuousAt.comp
          (f := fun z : ℂ => z + (ε : ℂ))
          (by fun_prop : ContinuousAt (fun z : ℂ => z + (ε : ℂ)) s)
      exact (((analyticOn_riemannZeta s (hs1 s hs)).continuousAt.mul
        (hi.sub continuousAt_const)).div continuousAt_id (hs0 s hs)).continuousWithinAt
    exact hq.congr (fun s hs => centeredReceiverSymbol_eq (hs1 s hs))
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨η, hη, max B 0, le_max_right _ _, fun e he y hy => ?_⟩
  have he1 : zetaZeroAbscissa - ε + e < 1 := by
    have := he.2
    dsimp only [η] at this
    rw [hΘ]
    linarith
  have hne : zetaZeroAbscissa + e ≠ 1 := by rw [hΘ]; linarith [he.1]
  rw [lineSymbol_receiver_eq_centered_ne_pole hε hθ he.1 he1 hne]
  let s : ℂ := ((σ + e : ℝ) : ℂ) + (y : ℂ) * I
  have hre : s.re = σ + e := by simp [s]
  have him : s.im = y := by simp [s]
  have hmem : s ∈ K := by
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      have hyabs : |y| ≤ |a| + |b| := abs_le.mpr
        ⟨by linarith [hy.1, neg_abs_le a, abs_nonneg b],
          by linarith [hy.2, le_abs_self b, abs_nonneg a]⟩
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ R := by
          rw [hre, him, abs_of_pos (by linarith [he.1] : 0 < σ + e)]
          dsimp [R]
          linarith [he.2, le_abs_self σ]
    · rw [hre]; linarith [he.1]
    · rw [hre]; linarith [he.2]
  exact (hB s hmem).trans (le_max_left _ _)

#print axioms exists_receiver_lineSymbol_compact_bound_of_abscissa_one

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
