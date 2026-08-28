import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProposition22Identity
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanRectangularMinorantPaperScale
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanAggregateDilationErrorPaperScale
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanBoundaryPaperScale
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanBoundarySupport

/-!
# Proposition 2.2 total error at paper scale

The interval-restricted rectangularization and iteration errors cannot increase pointwise norms.
Combining them with the product boundary costs one fixed three-term Hilbert factor.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction

noncomputable section

theorem sum_normSq_mtRealIntervalAF_le
    (S : Finset ℕ) (f : ℕ → ℂ) (L U : ℝ) :
    ∑ n ∈ S, ‖mtRealIntervalAF f L U n‖ ^ 2 ≤
      ∑ n ∈ S, ‖f n‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  change ‖(if n = 0 then 0 else if L < (n : ℝ) ∧ (n : ℝ) ≤ U then f n else 0)‖ ^ 2 ≤
    ‖f n‖ ^ 2
  split_ifs <;> simp

theorem sum_normSq_add_add_le_four
    (S : Finset ℕ) (f g h : ArithmeticFunction ℂ) :
    ∑ n ∈ S, ‖(f + g + h) n‖ ^ 2 ≤
      4 * ∑ n ∈ S, ‖f n‖ ^ 2 +
      4 * ∑ n ∈ S, ‖g n‖ ^ 2 +
      4 * ∑ n ∈ S, ‖h n‖ ^ 2 := by
  calc
    ∑ n ∈ S, ‖(f + g + h) n‖ ^ 2 ≤
        ∑ n ∈ S, (4 * ‖f n‖ ^ 2 + 4 * ‖g n‖ ^ 2 + 4 * ‖h n‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      change ‖f n + g n + h n‖ ^ 2 ≤ _
      have hfg := norm_add_sq_le_two (f n) (g n)
      have htotal := norm_add_sq_le_two (f n + g n) (h n)
      nlinarith
    _ = 4 * ∑ n ∈ S, ‖f n‖ ^ 2 +
        4 * ∑ n ∈ S, ‖g n‖ ^ 2 +
        4 * ∑ n ∈ S, ‖h n‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

set_option maxHeartbeats 600000 in
/-- Complete error mean square on the full coarse support interval. -/
theorem eventually_sum_normSq_mtHarmanProposition22ErrorAF_le_paper
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ {outerQ : ℕ} (endpointQ endpointD : ℕ → ℕ) (z Q D E Y : ℕ),
      mtLowerCutoffNat X ≤ z → z ≤ D → (D : ℝ) ≤ X →
      endpointD = mtPaperAlignedEndpoint (mtLowerCutoffNat X) D (mtPaperWidth A X) →
      1 ≤ Y → (Y : ℝ) ≤ X / 2 → X ^ (1 / 2 : ℝ) ≤ (Y : ℝ) →
      (∀ i, 2 ≤ endpointQ i) → Monotone endpointQ →
      (∀ i, mtAdjacentBlockUpperScale endpointQ i ≤
        (1 + mtPaperWidth A X) * mtAdjacentBlockLowerScale endpointQ i) →
      primesIco z Q ⊆ primesIco (endpointQ 0) (endpointQ outerQ) →
      (∀ i, 2 ≤ endpointD i) → Monotone endpointD →
      (∀ i, mtAdjacentBlockUpperScale endpointD i ≤
        (1 + mtPaperWidth A X) * mtAdjacentBlockLowerScale endpointD i) →
      ∀ (z0 Dtrunc recStart : ℕ) (recRoot : ℝ)
        (hdelta : 0 < mtPaperWidth A X)
        (hz0 : (z0 : ℝ) ≤ mtGeometricLevel (mtPaperWidth A X) recStart 0)
        (hroot : mtGeometricLevel (mtPaperWidth A X) recStart 0 < recRoot),
      ∀ (data : MTFiniteIterationSourceData
          (mtMinimalGeometricDepth (mtPaperWidth A X) recStart recRoot hdelta))
        (_cert : MTGridFreeDilationCertificate data A X),
      data.block =
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 Dtrunc recStart (mtPaperWidth A X) recRoot hdelta hz0 hroot).block →
      data.z₀ = z0 → data.D = Dtrunc →
      ∀ (J : ℕ)
        (j : Fin (mtMinimalGeometricDepth (mtPaperWidth A X) recStart recRoot hdelta + 1)),
      (J : ℝ) ≤ Real.log X →
      (1 + mtPaperWidth A X) ^ (J + 5) ≤ 1 + mtPaperWidth (A - 1) X →
      let boundary := mtHarmanProductBoundaryErrorAF
        (outerQ := outerQ) (outerD := D - mtLowerCutoffNat X)
        endpointQ endpointD z Q D (E : ℝ) data J j (mtPaperWidth A X)
        (4 * Y) recStart (Y : ℝ)
      ∑ n ∈ Finset.Icc 1 (8 * Y),
          ‖mtHarmanProposition22ErrorAF (outerD := D - mtLowerCutoffNat X)
            endpointD z Q D E data J j Y boundary n‖ ^ 2 ≤
        ((92224 : ℝ) * (5 : ℝ) ^ 35 + 7232) * (Y : ℝ) *
          (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
  filter_upwards [
    eventually_sum_normSq_mtHarmanRectangularMinorantError_actualSource_le_log_rpow A hA,
    eventually_sum_normSq_mtHarmanAggregateIterationErrorAF_dilation_le_paper A hA,
    eventually_sum_normSq_mtHarmanProductBoundaryErrorAF_le_paper A hA,
    Filter.eventually_ge_atTop (Real.exp 2)] with X hrectX haggX hboundaryX hX
  intro outerQ endpointQ endpointD z Q D E Y hz hD hDX hendpointDEq hY hYX hYlower
    hendpointQ hmonoQ hbandQ hsourceQ hendpointD hmonoD hbandD
    z0 Dtrunc recStart recRoot hdelta hz0 hroot data _cert hblocks hz0Data hDData
    J j hJ hdilation
  subst endpointD
  let endpointD := mtPaperAlignedEndpoint (mtLowerCutoffNat X) D (mtPaperWidth A X)
  dsimp only
  let boundary := mtHarmanProductBoundaryErrorAF
    (outerQ := outerQ) (outerD := D - mtLowerCutoffNat X)
    endpointQ endpointD z Q D (E : ℝ) data J j (mtPaperWidth A X)
    (4 * Y) recStart (Y : ℝ)
  let rect := mtRealIntervalAF
    (mtHarmanRectangularMinorantError (t := D - mtLowerCutoffNat X) endpointD z D E)
    ((Y : ℝ) / 2) (4 * (Y : ℝ))
  let iteration := mtRealIntervalAF
    (mtHarmanAggregateIterationErrorAF (outerDepth := D - mtLowerCutoffNat X)
      endpointD z Q D (E : ℝ) data J j)
    ((Y : ℝ) / 2) (4 * (Y : ℝ))
  have h8Y : (1 : ℕ) ≤ 8 * Y := by omega
  have h8YX : ((8 * Y : ℕ) : ℝ) ≤ 4 * X := by
    push_cast
    linarith
  have hrectRaw := hrectX z D (8 * Y) E hz hD hDX h8Y h8YX
  have hrectRestrict := sum_normSq_mtRealIntervalAF_le
    (Finset.Icc 1 (8 * Y))
    (mtHarmanRectangularMinorantError (t := D - mtLowerCutoffNat X)
      endpointD z D E) ((Y : ℝ) / 2) (4 * (Y : ℝ))
  have hrect : ∑ n ∈ Finset.Icc 1 (8 * Y), ‖rect n‖ ^ 2 ≤
      (8 * Y : ℕ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
    exact hrectRestrict.trans hrectRaw
  have haggRaw := haggX (outerDepth := D - mtLowerCutoffNat X)
    endpointD z Q D (E : ℝ) data _cert J j (8 * Y)
    (fun i => one_le_two.trans (hendpointD i)) hmonoD h8Y h8YX hJ
  have haggRestrict := sum_normSq_mtRealIntervalAF_le
    (Finset.Icc 1 (8 * Y))
    (mtHarmanAggregateIterationErrorAF (outerDepth := D - mtLowerCutoffNat X)
      endpointD z Q D (E : ℝ) data J j) ((Y : ℝ) / 2) (4 * (Y : ℝ))
  have hagg : ∑ n ∈ Finset.Icc 1 (8 * Y), ‖iteration n‖ ^ 2 ≤
      225 * (8 * Y : ℕ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) :=
    haggRestrict.trans haggRaw
  have hYupper : (Y : ℝ) ≤ X := by
    have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
    linarith
  have hboundary := hboundaryX (S := Finset.Icc 1 (8 * Y))
    (outerQ := outerQ) (outerD := D - mtLowerCutoffNat X)
    endpointQ endpointD z Q D (E : ℝ)
    hendpointQ hmonoQ hbandQ hsourceQ hendpointD hmonoD hbandD
    z0 Dtrunc recStart recRoot hdelta hz0 hroot data hblocks hz0Data hDData
    J j (4 * Y) (Y : ℝ) hYlower hYupper hdilation
  have hsum := sum_normSq_add_add_le_four
    (Finset.Icc 1 (8 * Y)) rect iteration boundary
  have hlogOne : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 2) hX
    have : (2 : ℝ) ≤ Real.log X := by simpa only [Real.log_exp] using hmono
    linarith
  have hpow : (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) ≤
      (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hlogOne
    have hAc : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    push_cast
    linarith
  have hnonneg : 0 ≤ (Y : ℝ) * (Real.log X) ^ (-((A : ℕ) : ℝ)) := by positivity
  change ∑ n ∈ Finset.Icc 1 (8 * Y), ‖(rect + iteration + boundary) n‖ ^ 2 ≤ _
  calc
    ∑ n ∈ Finset.Icc 1 (8 * Y), ‖(rect + iteration + boundary) n‖ ^ 2 ≤
      4 * ∑ n ∈ Finset.Icc 1 (8 * Y), ‖rect n‖ ^ 2 +
      4 * ∑ n ∈ Finset.Icc 1 (8 * Y), ‖iteration n‖ ^ 2 +
      4 * ∑ n ∈ Finset.Icc 1 (8 * Y), ‖boundary n‖ ^ 2 := hsum
    _ ≤ 4 * ((8 * Y : ℕ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ))) +
        4 * (225 * (8 * Y : ℕ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ))) +
        4 * ((23056 * (5 : ℝ) ^ 35) * (Y : ℝ) *
          (Real.log X) ^ (-((A : ℕ) : ℝ))) := by gcongr
    _ ≤ ((92224 : ℝ) * (5 : ℝ) ^ 35 + 7232) * (Y : ℝ) *
        (Real.log X) ^ (-((A : ℕ) : ℝ)) := by
      rw [Nat.cast_mul]
      have hsmall := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 7232 * (Y : ℝ))
      calc
        4 * (8 * (Y : ℝ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ))) +
            4 * (225 * (8 * (Y : ℝ)) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ))) +
            4 * (23056 * 5 ^ 35 * (Y : ℝ) *
              (Real.log X) ^ (-((A : ℕ) : ℝ))) =
          7232 * (Y : ℝ) * (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) +
            92224 * 5 ^ 35 * (Y : ℝ) *
              (Real.log X) ^ (-((A : ℕ) : ℝ)) := by ring
        _ ≤ 7232 * (Y : ℝ) * (Real.log X) ^ (-((A : ℕ) : ℝ)) +
            92224 * 5 ^ 35 * (Y : ℝ) *
              (Real.log X) ^ (-((A : ℕ) : ℝ)) := add_le_add hsmall (le_refl _)
        _ = ((92224 : ℝ) * 5 ^ 35 + 7232) * (Y : ℝ) *
            (Real.log X) ^ (-((A : ℕ) : ℝ)) := by ring

end

end RHTower.Sieve
