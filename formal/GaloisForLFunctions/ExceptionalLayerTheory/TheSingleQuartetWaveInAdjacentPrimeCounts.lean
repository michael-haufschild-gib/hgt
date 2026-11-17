import GaloisForLFunctions.ExceptionalLayerTheory.AdjacentVaughanOctavesRecoverTheOrdinaryPrimeCount
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity
import GaloisForLFunctions.RHTower.ZetaFractLaplace

/-!
# The single-quartet waveform in consecutive arithmetic cofactor counts

At cofinally many adjacent first-octave cutoffs their difference, sampled
at multiples of an ordinary prime, recovers the complete Chebyshev error.
The quartet criterion on these counts retains the same multiplicity,
frequency and error bound as the criterion on the original prime count.
-/

noncomputable section

namespace GaloisForLFunctions.ExceptionalLayerTheory

open ExclusionOfTheCriticalState

/-- Difference of the two ordinary cofactor counts, including the fractional
part of the real cutoff in the integer-density subtraction. -/
def adjacentCountAt (t : ℕ) (x : ℝ) : ℝ :=
  cofactorCountError (t + 1) (2 * (t + 1)) ((2 * t + 1) * ⌊x⌋₊) -
    cofactorCountError t (2 * t) ((2 * t + 1) * ⌊x⌋₊) + (x - ⌊x⌋₊)

/-- A cofinal family of adjacent ordinary cofactor counts characterizes the
single off-line quartet, with a common pair of cutoffs for all strip zeros. -/
theorem cofinal_adjacentCounts_characterize_singleQuartet (B : ℕ) :
    ∃ t > B, (2 * t + 1).Prime ∧ ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 →
      riemannZeta ρ = 0 → (HasSingleOffLineQuartet ρ ↔
        ∃ K : ℝ, ∀ x : ℝ, 16 ≤ x →
          |adjacentCountAt t x - 2 * (quartetCopyMult ρ : ℝ) * ((x : ℂ) ^ ρ / ρ).re| ≤
            K * Real.sqrt x * Real.log x ^ 2) := by
  obtain ⟨t, ht, hp, hcount⟩ := cofinal_adjacent_octaves_recover_prime_error B
  have hreal (x : ℝ) : adjacentCountAt t x = x - Chebyshev.psi x := by
    rw [adjacentCountAt, hcount, ← Chebyshev.psi_eq_psi_coe_floor x]
    ring
  have hsign (a b c : ℝ) : |a - b - c| = |b - a + c| := by
    rw [show a - b - c = -(b - a + c) by ring, abs_neg]
  refine ⟨t, ht, hp, fun ρ hhalf hhi hz => ?_⟩
  simp_rw [hreal, hsign]
  exact hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave hhalf
    ⟨hz, by linarith only [hhalf], hhi⟩

private theorem positive_dilate_of_nonreal_frequency {ρ z : ℂ} (hρ : ρ.im ≠ 0) (hz : z ≠ 0) :
    ∃ τ a : ℝ, 0 < a ∧ |τ| ≤ Real.pi / |ρ.im| ∧ (a : ℂ) * Complex.exp (ρ * (τ : ℂ)) = z := by
  let τ := (Complex.log z).im / ρ.im
  refine ⟨τ, Real.exp ((Complex.log z).re - ρ.re * τ), Real.exp_pos _, ?_, ?_⟩
  · change |(Complex.log z).im / ρ.im| ≤ _
    rw [abs_div, Complex.log_im]
    exact div_le_div_of_nonneg_right (Complex.abs_arg_le_pi z) (abs_nonneg _)
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  refine (congrArg Complex.exp ?_).trans (Complex.exp_log hz)
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, mul_zero,
      Complex.ofReal_re]
    dsimp [τ]
    field_simp

private theorem scaled_mode_eq_dilated_power {ρ A : ℂ} (hρ : ρ ≠ 0) {τ a : ℝ}
    (ha : (a : ℂ) * Complex.exp (ρ * (τ : ℂ)) = ρ * A) (t : ℝ) :
    (Real.exp (17 / 2 * t) : ℂ) * (A * Complex.exp ((ρ - 1 / 2 - 8) * (t : ℂ))) =
      (a : ℂ) * (((Real.exp (t + τ) : ℝ) : ℂ) ^ ρ / ρ) := by
  rw [RHTower.cpow_ofReal_exp, Complex.ofReal_add, mul_add, Complex.exp_add]
  calc
    _ = A * Complex.exp (ρ * (t : ℂ)) := by
      rw [mul_left_comm, Complex.ofReal_exp, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    _ = ((a : ℂ) * Complex.exp (ρ * (τ : ℂ))) * Complex.exp (ρ * (t : ℂ)) / ρ := by
      rw [ha]
      field_simp
    _ = _ := by ring

/-- Under a single quartet the averaged state of every confined rung is
recovered, through square-root accuracy on the prime scale, from one
positive multiple of the same pair of ordinary counts. The log delay is at
most half the oscillation period. -/
theorem cofinal_adjacentCounts_recover_confined_states (B : ℕ) :
    ∃ u > B, (2 * u + 1).Prime ∧ ∀ {ρ : ℂ}, HasSingleOffLineQuartet ρ →
      ∀ {R : ℝ}, 0 < R → ∀ {F : ℝ → ℝ}, IsConfinedNullVector R F →
      ∃ τ a : ℝ, 0 < a ∧ |τ| ≤ Real.pi / |ρ.im| ∧ ∃ K L : ℝ, ∀ t : ℝ, 0 < t → 16 ≤ Real.exp (t + τ) →
        |Real.exp (17 / 2 * t) * averagedState F t - a * adjacentCountAt u (Real.exp (t + τ))| ≤
          Real.exp (t / 2) * (K + L * (t + τ) ^ 2) := by
  obtain ⟨u, hu, hp, hchar⟩ := cofinal_adjacentCounts_characterize_singleQuartet B
  refine ⟨u, hu, hp, fun {ρ} hq {R} hR {F} hF => ?_⟩
  let A := -(ArithmeticHodgeTheoryOfDegenerations.criticalAliasCoefficient R : ℂ)⁻¹ *
    HTGeometry.negativeHalfLineLaplace (ArithmeticCastelnuovoSeveri.cx F) (ρ - 1 / 2) *
    averageSymbol (ρ - 1 / 2 - 8)
  obtain ⟨hA, K, hK⟩ := singleQuartet_nullVector_averagedState_singleConjugatePair hq hR hF
  change A ≠ 0 at hA
  have hρ : ρ ≠ 0 := fun h => hq.im_ne_zero (by simp [h])
  obtain ⟨τ, a, ha, hτ, hphase⟩ := positive_dilate_of_nonreal_frequency hq.im_ne_zero
    (mul_ne_zero hρ hA)
  obtain ⟨L, hL⟩ := (hchar ρ hq.1 hq.re_lt_one hq.2.1.1).mp hq
  refine ⟨τ, a, ha, hτ, K, a * L * Real.exp (τ / 2), fun t ht htτ => ?_⟩
  let m : ℝ := 2 * (quartetCopyMult ρ : ℝ)
  let Z := (A * Complex.exp ((ρ - 1/2 - 8) * (t : ℂ))).re
  let P := ((((Real.exp (t + τ) : ℝ) : ℂ) ^ ρ) / ρ).re
  let T := Real.exp (17 / 2 * t)
  have hmode : T * (m * Z) = a * (m * P) := by
    have h := congrArg Complex.re (scaled_mode_eq_dilated_power hρ hphase t)
    simp only [Complex.re_ofReal_mul] at h
    change T * Z = a * P at h
    linear_combination m * h
  have hs : |averagedState F t - m * Z| ≤ K * Real.exp (-(8*t)) := hK t ht
  have hc : |adjacentCountAt u (Real.exp (t + τ)) - m * P| ≤
      L * Real.sqrt (Real.exp (t + τ)) * Real.log (Real.exp (t + τ)) ^ 2 :=
    hL _ htτ
  have hscale : T * Real.exp (-(8*t)) = Real.exp (t/2) := by
    rw [show T = Real.exp (17 / 2 * t) from rfl, ← Real.exp_add]
    congr 1
    ring
  have hsqrt : Real.sqrt (Real.exp (t + τ)) = Real.exp (t/2) * Real.exp (τ/2) := by
    rw [← Real.exp_half, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = |T * (averagedState F t - m * Z) -
        a * (adjacentCountAt u (Real.exp (t + τ)) - m * P)| := by
      congr 1
      change T * averagedState F t - _ = _
      linear_combination hmode
    _ ≤ |T * (averagedState F t - m * Z)| +
        |a * (adjacentCountAt u (Real.exp (t + τ)) - m * P)| := abs_sub _ _
    _ ≤ T * (K * Real.exp (-(8 * t))) +
        a * (L * Real.sqrt (Real.exp (t + τ)) * Real.log (Real.exp (t + τ)) ^ 2) := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _ : 0 < T), abs_of_pos ha]
      exact add_le_add (mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _))
        (mul_le_mul_of_nonneg_left hc ha.le)
    _ = _ := by
      rw [Real.log_exp, hsqrt, mul_left_comm T K, hscale]
      ring

#print axioms cofinal_adjacentCounts_characterize_singleQuartet
#print axioms cofinal_adjacentCounts_recover_confined_states

end GaloisForLFunctions.ExceptionalLayerTheory
