import GaloisForLFunctions.RHTower.Sieve.MaynardOrderedPrimeGapProportionalPrimeFree
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedAmbientPacketNatOrder
import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSlicePrimeFreeComposition
import GaloisForLFunctions.RHTower.Sieve.MaynardOrdinateShellReparameterization

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- One logarithmic envelope controls every stopped rung at arbitrary Mellin order. -/
theorem routeTComparableWidthLadder_uniform_natOrder_tail_of_log_envelope
    (r : ℕ) {P C lambda H0 A : ℝ} {K : ℕ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hlambda : 0 < lambda)
    (hH0 : 0 < H0) (hH0quarter : H0 ≤ 1 / 4)
    (hA : 0 < A)
    (hcut :
      P * (C * (1 / H0) ^ (r + 1) * (K : ℝ) ^ (-(r : ℝ))) ≤
        A / (2 * (1 + Real.log ((1 / 4) / H0) / Real.log 2))) :
    ∀ J : ℕ, 0 < J →
      (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ (1 / 4) / H0 →
      ∀ j ∈ Finset.range J,
        P * (C *
          ((lambda * 1) /
            (lambda * routeTComparableWidthLadder H0 (1 / 4) j)) ^ (r + 1) *
          (K : ℝ) ^ (-(r : ℝ))) ≤
        (A / (J : ℝ)) / 2 := by
  intro J hJ hbelow j _hj
  have hratioOne : 1 ≤ (1 / 4) / H0 := by
    exact (le_div_iff₀ hH0).2 (by simpa using hH0quarter)
  have hlogRatio : 0 ≤ Real.log ((1 / 4) / H0) :=
    Real.log_nonneg hratioOne
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let Q : ℝ := 1 + Real.log ((1 / 4) / H0) / Real.log 2
  have hQ : 0 < Q := by
    dsimp only [Q]
    positivity
  have hJQ : (J : ℝ) ≤ Q := by
    dsimp only [Q]
    exact routeTComparableWidthLadder_index_le_log hH0 hH0quarter hJ hbelow
  have hrung := (routeTComparableWidthLadder_mem hH0 hH0quarter j).1
  have hrungPos : 0 < routeTComparableWidthLadder H0 (1 / 4) j :=
    hH0.trans_le hrung
  have hratio :
      (lambda * 1) /
          (lambda * routeTComparableWidthLadder H0 (1 / 4) j) ≤
        1 / H0 := by
    rw [mul_one]
    field_simp
    nlinarith
  have hratio0 : 0 ≤
      (lambda * 1) /
        (lambda * routeTComparableWidthLadder H0 (1 / 4) j) := by
    positivity
  have hpow :
      ((lambda * 1) /
          (lambda * routeTComparableWidthLadder H0 (1 / 4) j)) ^ (r + 1) ≤
        (1 / H0) ^ (r + 1) :=
    pow_le_pow_left₀ hratio0 hratio (r + 1)
  have hfactor0 : 0 ≤ C := hC
  have hKpow0 : 0 ≤ (K : ℝ) ^ (-(r : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg K) _
  have htailEnvelope :
      P * (C *
          ((lambda * 1) /
            (lambda * routeTComparableWidthLadder H0 (1 / 4) j)) ^ (r + 1) *
          (K : ℝ) ^ (-(r : ℝ))) ≤
        P * (C * (1 / H0) ^ (r + 1) * (K : ℝ) ^ (-(r : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ hP
    apply mul_le_mul_of_nonneg_right _ hKpow0
    exact mul_le_mul_of_nonneg_left hpow hfactor0
  have hJreal : 0 < (J : ℝ) := by exact_mod_cast hJ
  have htarget : A / (2 * Q) ≤ A / (2 * (J : ℝ)) := by
    exact (div_le_div_iff₀ (mul_pos (by norm_num) hQ)
      (mul_pos (by norm_num) hJreal)).2 (by nlinarith)
  calc
    P * (C *
          ((lambda * 1) /
            (lambda * routeTComparableWidthLadder H0 (1 / 4) j)) ^ (r + 1) *
          (K : ℝ) ^ (-(r : ℝ))) ≤
        P * (C * (1 / H0) ^ (r + 1) * (K : ℝ) ^ (-(r : ℝ))) := htailEnvelope
    _ ≤ A / (2 * Q) := by simpa only [Q] using hcut
    _ ≤ A / (2 * (J : ℝ)) := htarget
    _ = (A / (J : ℝ)) / 2 := by ring

/-- A proportional polynomial-width prime-free interval forces a literal finite packet at any
fixed Mellin order; all adaptive tail obligations collapse to one logarithmic scalar inequality. -/
theorem exists_eventually_routeT_proportional_primeFree_large_range_packet_natOrder
    (r : ℕ) (hr : 1 ≤ r) {theta : ℝ} (htheta : 0 < theta) :
    ∃ Cr : ℝ, 1 ≤ Cr ∧
      ∀ᶠ lambda : ℝ in Filter.atTop,
        ∀ (L X k K : ℕ) {T0 t x H0 : ℝ},
          1 ≤ X → 0 < x → lambda ∈ Set.Icc x (2 * x) →
          0 < H0 → H0 ≤ 1 / 4 → 0 < K →
          X < (L + 1) ^ k →
          1 < T0 →
          ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ lambda →
          lambda ^ theta ≤ lambda * H0 →
          lambda + 2 * (lambda / 4) ≤ X →
          heathBrownWindowRelevantFixedPolylogBound L X k x 1 *
              (Cr * (1 / H0) ^ (r + 1) * (K : ℝ) ^ (-(r : ℝ))) ≤
            ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) /
              (2 * (1 + Real.log ((1 / 4) / H0) / Real.log 2)) →
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
  obtain ⟨Cr, hCr, hpacket⟩ :=
    exists_large_range_fixedAmbientPhysicalDefectPacket_of_full_defect_natOrder r hr
  refine ⟨Cr, hCr, ?_⟩
  filter_upwards
      [exists_eventually_routeT_proportional_primeFree_leftWindowRelevant_defect htheta,
        Filter.eventually_ge_atTop (2 : ℝ)]
      with lambda hdefect hlambdaTwo
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
  have hA : 0 <
      (2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4) := by
    positivity [routeTSmoothWindowCentralMargin_pos]
  have hB : 0 <
      ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / (J : ℝ) := by
    have hJreal : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
    positivity
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
  have hP : 0 ≤ heathBrownWindowRelevantFixedPolylogBound L X k x 1 := by
    exact (norm_nonneg
      (heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t x
        ((1 : ℂ) + (0 : ℝ) * Complex.I))).trans
      (norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
        L X k hX T0 t x 1 0 hx (by norm_num))
  have htailSelected :=
    routeTComparableWidthLadder_uniform_natOrder_tail_of_log_envelope r
      hP (zero_le_one.trans hCr) (hx.trans_le hlambda.1) hH0 hH0quarter hA htail
      J hJ hbelow j hj
  have hresult := hpacket L X k K T0 t hX hx
    (show 0 < lambda from hx.trans_le hlambda.1)
    (by norm_num : (0 : ℝ) < 1)
    (routeTComparableWidthLadder_pos hH0 (j + 1))
    (routeTComparableWidthLadder_pos hH0 j)
    hadj.1 hadj.2 houter (by simpa using (show (1 : ℝ) ≤ lambda by linarith))
      hB hK htailSelected hlarge'
  exact ⟨J, hJ, hbelow, j, hj, hresult⟩

end

end RHTower.Sieve
