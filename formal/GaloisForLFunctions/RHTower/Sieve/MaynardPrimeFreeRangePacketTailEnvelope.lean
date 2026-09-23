import GaloisForLFunctions.RHTower.Sieve.MaynardPrimeFreeRangePacketComposition
import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSlicePrimeFreeComposition
import GaloisForLFunctions.RHTower.Sieve.MaynardOrdinateShellReparameterization

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- One logarithmic envelope controls the Mellin tail on every admissible stopped rung. -/
theorem routeTComparableWidthLadder_uniform_tail_of_log_envelope
    {P C lambda H0 A : ℝ} {K : ℕ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hlambda : 0 < lambda)
    (hH0 : 0 < H0) (hH0quarter : H0 ≤ 1 / 4)
    (hA : 0 < A) (hK : 0 < K)
    (hcut :
      P * (130 * C * (1 / H0) ^ (2 : ℕ) / (K : ℝ)) ≤
        A / (2 * (1 + Real.log ((1 / 4) / H0) / Real.log 2))) :
    ∀ J : ℕ, 0 < J →
      (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ (1 / 4) / H0 →
      ∀ j ∈ Finset.range J,
        P * (130 * C *
          ((lambda * 1) /
            (lambda * routeTComparableWidthLadder H0 (1 / 4) j)) ^ (2 : ℕ) /
          (K : ℝ)) ≤
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
  have hsquare :
      ((lambda * 1) /
          (lambda * routeTComparableWidthLadder H0 (1 / 4) j)) ^ (2 : ℕ) ≤
        (1 / H0) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hratio0 hratio 2
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hfactor0 : 0 ≤ 130 * C := mul_nonneg (by norm_num) hC
  have htailEnvelope :
      P * (130 * C *
          ((lambda * 1) /
            (lambda * routeTComparableWidthLadder H0 (1 / 4) j)) ^ (2 : ℕ) /
          (K : ℝ)) ≤
        P * (130 * C * (1 / H0) ^ (2 : ℕ) / (K : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hP
    apply div_le_div_of_nonneg_right _ hKreal.le
    exact mul_le_mul_of_nonneg_left hsquare hfactor0
  have hJreal : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hden : 2 * (J : ℝ) ≤ 2 * Q := by nlinarith
  have htarget : A / (2 * Q) ≤ A / (2 * (J : ℝ)) := by
    exact (div_le_div_iff₀ (mul_pos (by norm_num) hQ)
      (mul_pos (by norm_num) hJreal)).2 (by nlinarith)
  calc
    P * (130 * C *
          ((lambda * 1) /
            (lambda * routeTComparableWidthLadder H0 (1 / 4) j)) ^ (2 : ℕ) /
          (K : ℝ)) ≤
        P * (130 * C * (1 / H0) ^ (2 : ℕ) / (K : ℝ)) := htailEnvelope
    _ ≤ A / (2 * Q) := by simpa only [Q] using hcut
    _ ≤ A / (2 * (J : ℝ)) := htarget
    _ = (A / (J : ℝ)) / 2 := by ring

/-- The proportional prime-free producer needs only one scalar logarithmic tail cutoff. -/
theorem exists_eventually_routeT_proportional_primeFree_large_range_packet_of_log_tail_envelope
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
          heathBrownWindowRelevantFixedPolylogBound L X k x 1 *
              (130 * C * (1 / H0) ^ (2 : ℕ) / (K : ℝ)) ≤
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
  obtain ⟨C, hC, hpacket⟩ :=
    exists_eventually_routeT_proportional_primeFree_large_range_packet htheta
  refine ⟨C, hC, ?_⟩
  filter_upwards [hpacket] with lambda hpacketLambda
  intro L X k K T0 t x H0 hX hx hlambda hH0 hH0quarter hK hXL hT0 hscale
    hpower hsupport hcut hprimeFree
  have hlambda0 : 0 < lambda := hx.trans_le hlambda.1
  have hP : 0 ≤ heathBrownWindowRelevantFixedPolylogBound L X k x 1 := by
    exact (norm_nonneg
      (heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t x
        ((1 : ℂ) + (0 : ℝ) * Complex.I))).trans
      (norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
        L X k hX T0 t x 1 0 hx (by norm_num))
  have hA : 0 <
      (2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4) := by
    positivity [routeTSmoothWindowCentralMargin_pos]
  apply hpacketLambda L X k K hX hx hlambda hH0 hH0quarter hK hXL hT0 hscale
    hpower hsupport
  · exact routeTComparableWidthLadder_uniform_tail_of_log_envelope
      hP (zero_le_one.trans hC) hlambda0 hH0 hH0quarter hA hK hcut
  · exact hprimeFree

end

end RHTower.Sieve
