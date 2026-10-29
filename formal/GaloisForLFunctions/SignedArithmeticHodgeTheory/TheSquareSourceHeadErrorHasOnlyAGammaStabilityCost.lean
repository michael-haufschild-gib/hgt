import GaloisForLFunctions.SignedArithmeticHodgeTheory.ActualGeneratorHeadsPreserveTheSourceMean

/-!
# The even-power source head error has an explicit Gamma stability cost

The centered mixed estimate also controls its diagonal by exact quadratic
homogeneity. The actual generator tail has zero ordinary mean, so its literal
square-prime source differs from the centered source only by a constant times
its square mass. Original Gamma pays that mass uniformly across every level.
The resulting full head error retains the Gamma energies of the constructed
head and tail explicitly; it assumes no bound for those energies.
-/

noncomputable section
open MeasureTheory Set RHTower

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells ArithmeticIndexDescent
open GaloisForLFunctions.RHTower ArithmeticFunction

private theorem squarePrimeSource_two_mul (f : ℝ → ℝ) :
    squarePrimeSource (fun x => 2 * f x) = 4 * squarePrimeSource f := by
  have hc (u : ℝ) : screwCrossCorr (fun x => 2 * f x) (fun x => 2 * f x) u =
      4 * screwCrossCorr f f u := by
    unfold screwCrossCorr
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  unfold squarePrimeSource
  have he : (fun n : ℕ => (vonMangoldt n / (n : ℝ)) *
      screwCrossCorr (fun x => 2 * f x) (fun x => 2 * f x) (2 * Real.log n)) =
      fun n : ℕ => 4 * ((vonMangoldt n / (n : ℝ)) * screwCrossCorr f f (2 * Real.log n)) := by
    funext n
    rw [hc]
    ring
  rw [he, tsum_mul_left]
  ring

private theorem centeredSquarePrimeSource_two_mul (f : ℝ → ℝ) :
    centeredSquarePrimeSource (fun x => 2 * f x) = 4 * centeredSquarePrimeSource f := by
  have hs : (∫ x, (2 * f x) ^ 2) = 4 * ∫ x, f x ^ 2 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [centeredSquarePrimeSource, squarePrimeSource_two_mul, integral_const_mul, hs,
    centeredSquarePrimeSource]
  ring

/-- Centered even-power source values cost arbitrarily little Gamma plus ordinary square mass. -/
theorem exists_centeredSquare_diagonal_gamma_mass {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℝ),
      BoundedVariationOn f univ → HasCompactSupport f →
      |centeredSquarePrimeSource f| ≤ ε * levyEnergy f + C * ∫ x, f x ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_centeredSquareSource_gamma_mass_bv hε
  refine ⟨C / 2, div_nonneg hC (by norm_num), ?_⟩
  intro f hv hc
  have h := hb f f hv hc hv hc
  have he : (fun x => f x + f x) = fun x => 2 * f x := by funext x; ring
  rw [he, centeredSquarePrimeSource_two_mul,
    show 4 * centeredSquarePrimeSource f - centeredSquarePrimeSource f -
      centeredSquarePrimeSource f = 2 * centeredSquarePrimeSource f by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
  linarith only [h]

/-- One constant controls the complete even-power source error for every finite source and horizon.
Only the actual head and tail Gamma energies remain unpaid. -/
theorem exists_actualGenerator_square_head_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℕ+) (κ : Type) [Fintype κ] (n : κ → ℕ+) (c : κ → ℝ),
      |squarePrimeSource (finiteLogCellProfile n c) -
          squarePrimeSource (actualGeneratorHeadProfile A n c)| ≤
        ε * (levyEnergy (actualGeneratorHeadProfile A n c) +
          levyEnergy (actualGeneratorTailProfile A n c)) +
            C * (32 * levyEnergy (finiteLogCellProfile n c) / (1 + Real.log (A : ℝ))) := by
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨Cm, hCm, hm⟩ := exists_actualGenerator_square_mixed_bound hε2
  obtain ⟨Cd, hCd, hd⟩ := exists_centeredSquare_diagonal_gamma_mass hε2
  refine ⟨Cm + Cd + |squarePrimeRegularSymbol 0|,
    add_nonneg (add_nonneg hCm hCd) (abs_nonneg _), ?_⟩
  intro A κ _ n c
  let f := finiteLogCellProfile n c
  let h := actualGeneratorHeadProfile A n c
  let t := actualGeneratorTailProfile A n c
  let Q := 32 * levyEnergy f / (1 + Real.log (A : ℝ))
  have hmix := hm A κ n c
  have hdiag := hd t (actualGeneratorTailProfile_bv A n c) (actualGeneratorTailProfile_compact A n c)
  have hmass : 0 ≤ ∫ x, t x ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have he : squarePrimeSource t = centeredSquarePrimeSource t +
      squarePrimeRegularSymbol 0 * ∫ x, t x ^ 2 := by
    rw [centeredSquarePrimeSource]
    change _ = squarePrimeSource t - (1 / 2 : ℝ) *
      (∫ x, actualGeneratorTailProfile A n c x) ^ 2 - _ + _
    rw [integral_actualGeneratorTail, zero_pow (by norm_num : 2 ≠ 0)]
    ring
  have htail : |squarePrimeSource t| ≤ (ε / 2) * levyEnergy t +
      (Cd + |squarePrimeRegularSymbol 0|) * Q := by
    calc
      _ ≤ |centeredSquarePrimeSource t| +
          |squarePrimeRegularSymbol 0| * ∫ x, t x ^ 2 := by
        rw [he]
        simpa only [abs_mul, abs_of_nonneg hmass] using
          abs_add_le (centeredSquarePrimeSource t) (squarePrimeRegularSymbol 0 * ∫ x, t x ^ 2)
      _ ≤ (ε / 2) * levyEnergy t + (Cd + |squarePrimeRegularSymbol 0|) * ∫ x, t x ^ 2 := by
        linarith only [hdiag]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (integral_actualGeneratorTail_sq_le A n c) (add_nonneg hCd (abs_nonneg _)))
  have htri : |squarePrimeSource f - squarePrimeSource h| ≤
      |squarePrimeSource f - squarePrimeSource h - squarePrimeSource t| + |squarePrimeSource t| := by
    calc
      _ = |(squarePrimeSource f - squarePrimeSource h - squarePrimeSource t) + squarePrimeSource t| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hhead : 0 ≤ levyEnergy h :=
    levyEnergy_nonneg_bv (actualGeneratorHeadProfile_bv A n c) (actualGeneratorHeadProfile_compact A n c)
  have hreserve := mul_nonneg hε2.le hhead
  change |squarePrimeSource f - squarePrimeSource h| ≤
    ε * (levyEnergy h + levyEnergy t) + (Cm + Cd + |squarePrimeRegularSymbol 0|) * Q
  change |squarePrimeSource f - squarePrimeSource h - squarePrimeSource t| ≤
    (ε / 2) * (levyEnergy h + levyEnergy t) + Cm * Q at hmix
  linarith only [htri, hmix, htail, hreserve]

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_centeredSquare_diagonal_gamma_mass
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_actualGenerator_square_head_bound
