import GaloisForLFunctions.RHTower.Sieve.MaynardOrderedPrimeGapProportionalPrimeFree
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedAmbientPacketInterval

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- Proportional polynomial-width prime-freeness forces one literal fixed-source finite packet to
be large.  The only cutoff obligation is the displayed uniform Mellin-tail inequality. -/
theorem exists_eventually_routeT_proportional_primeFree_large_range_packet
    {theta : ℝ} (htheta : 0 < theta) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ᶠ lambda : ℝ in Filter.atTop,
        ∀ (L X k K : ℕ) {T0 t x H0 : ℝ},
          1 ≤ X → 0 < x → lambda ∈ Set.Icc x (2 * x) →
          0 < H0 → H0 ≤ 1 / 4 → 0 < K →
          X < (L + 1) ^ k →
          1 < T0 →
          ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ lambda →
          lambda ^ theta ≤ lambda * H0 →
          lambda + 2 * (lambda / 4) ≤ X →
          (∀ J : ℕ, 0 < J →
            (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ (1 / 4) / H0 →
            ∀ j ∈ Finset.range J,
            heathBrownWindowRelevantFixedPolylogBound L X k x 1 *
                (130 * C *
                  ((lambda * 1) /
                    (lambda * routeTComparableWidthLadder H0 (1 / 4) j)) ^ (2 : ℕ) /
                  (K : ℝ)) ≤
              (((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) /
                (J : ℝ)) / 2) →
          Chebyshev.theta (lambda + 2 * (lambda * H0)) -
              Chebyshev.theta lambda = 0 →
          ∃ J : ℕ, 0 < J ∧
            (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ (1 / 4) / H0 ∧
            ∃ j ∈ Finset.range J,
            (((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) /
                (J : ℝ)) / 8 ≤
              ‖maynardFixedAmbientPhysicalDefectPacket (Finset.range K)
                (fun y : ℝ =>
                  heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t x
                    ((1 : ℂ) + (y : ℝ) * Complex.I))
                lambda 1
                  (routeTComparableWidthLadder H0 (1 / 4) j)
                  (routeTComparableWidthLadder H0 (1 / 4) (j + 1)) 1‖ := by
  obtain ⟨C, hC, hpacket⟩ :=
    exists_large_range_fixedAmbientPhysicalDefectPacket_of_full_defect
  refine ⟨C, hC, ?_⟩
  filter_upwards
      [exists_eventually_routeT_proportional_primeFree_leftWindowRelevant_defect htheta]
      with lambda hdefect
  intro L X k K T0 t x H0 hX hx hlambda hH0 hH0quarter hK hXL hT0 hscale
    hpower hsupport htail hprimeFree
  obtain ⟨J, hJ, hbelow, j, hj, hlarge⟩ :=
    hdefect L X k hx hlambda hH0 hH0quarter hXL hT0 hscale hpower hsupport hprimeFree
  have hadj := routeTComparableWidthLadder_adjacent
    hH0 (by norm_num : (0 : ℝ) < 1 / 4) j
  have houter : routeTComparableWidthLadder H0 (1 / 4) j ≤ 1 := by
    rw [routeTComparableWidthLadder, max_le_iff]
    constructor
    · linarith
    · have hpow : (1 : ℝ) ≤ (((2 ^ j : ℕ) : ℝ)) := by
        exact_mod_cast Nat.one_le_pow j 2 (by norm_num)
      have hpowpos : (0 : ℝ) < (((2 ^ j : ℕ) : ℝ)) := by positivity
      apply (div_le_iff₀ hpowpos).2
      nlinarith
  have hB : 0 <
      ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / (J : ℝ) := by
    have hJreal : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
    positivity [routeTSmoothWindowCentralMargin_pos]
  have hlarge' :
      ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / (J : ℝ) ≤
        ‖∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t x
              ((1 : ℂ) + (y : ℝ) * Complex.I) *
            (routeTNormalizedSmoothWindowMellin (lambda * 1)
                (lambda * routeTComparableWidthLadder H0 (1 / 4) j)
                ((1 : ℂ) + (y : ℝ) * Complex.I) -
              routeTNormalizedSmoothWindowMellin (lambda * 1)
                (lambda * routeTComparableWidthLadder H0 (1 / 4) (j + 1))
                ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
    simpa using hlarge
  have hresult := hpacket L X k K T0 t hX hx
    (show 0 < lambda from hx.trans_le hlambda.1)
    (by norm_num : (0 : ℝ) < 1)
    (routeTComparableWidthLadder_pos hH0 (j + 1))
    (routeTComparableWidthLadder_pos hH0 j)
    hadj.1 hadj.2 houter hB hK (htail J hJ hbelow j hj) hlarge'
  exact ⟨J, hJ, hbelow, j, hj, hresult⟩

end

end RHTower.Sieve
