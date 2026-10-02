import GaloisForLFunctions.RHTower.RoutePCoprimeSquareNative

/-!
# Native coprime energy cannot be everywhere nonnegative

The admitted combined budget has a positive first-order zero. An everywhere
nonnegative source supported below one would instead have a decreasing real
Mellin budget. The contradiction applies to the literal complete native head.
No endpoint-square integrability is assumed.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower

private theorem source_zero {y : ℝ} (hy : 1 ≤ y) : routePCoprimeSquareSource y = 0 := by
  unfold routePCoprimeSquareSource pmWeightedDilationSource
  have hz (n : ℕ) : ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      (routePCoprimeSquareWeight ((n : ℝ) * y) : ℂ) = 0 := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hny : 1 ≤ (n : ℝ) * y :=
        hy.trans (by simpa using mul_le_mul_of_nonneg_right hn1 (by linarith : 0 ≤ y))
      simp [routePCoprimeSquareWeight_eq_zero_of_one_le hny]
  simp only [hz, tsum_zero]

private theorem integrand_re (ε y : ℝ) (hy : 0 < y) :
    ((y : ℂ) ^ ((1 + (ε : ℂ)) - 1) • routePCoprimeSquareSource y).re =
      y ^ ε * (routePCoprimeSquareSource y).re := by
  rw [show (1 + (ε : ℂ)) - 1 = (ε : ℂ) by ring, smul_eq_mul,
    ← Complex.ofReal_cpow hy.le]
  simp

private theorem real_integrable {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun y : ℝ => y ^ ε * (routePCoprimeSquareSource y).re) (Ioi 0) := by
  have hs : 1 < ((1 : ℂ) + (ε : ℂ)).re := by simpa using hε
  have h := (routePCoprimeSquareSource_hasMellin hs).1.re
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simpa only [RCLike.re_eq_complex_re] using integrand_re ε y hy

private theorem real_integral_eq {ε : ℝ} (hε : 0 < ε) :
    (∫ y in Ioi (0 : ℝ), y ^ ε * (routePCoprimeSquareSource y).re) =
      (mellin routePCoprimeSquareSource (1 + (ε : ℂ))).re := by
  have hs : 1 < ((1 : ℂ) + (ε : ℂ)).re := by simpa using hε
  have h := integral_re (routePCoprimeSquareSource_hasMellin hs).1
  simp only [RCLike.re_eq_complex_re] at h
  unfold mellin
  rw [← h]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (integrand_re ε y hy).symm

private theorem budget_antitone
    (hA : ∀ y : ℝ, 0 < y → 0 ≤ (routePCoprimeSquareSource y).re)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hle : δ ≤ ε) :
    (mellin routePCoprimeSquareSource (1 + (ε : ℂ))).re ≤
      (mellin routePCoprimeSquareSource (1 + (δ : ℂ))).re := by
  rw [← real_integral_eq hε, ← real_integral_eq hδ]
  apply integral_mono_ae (real_integrable hε) (real_integrable hδ)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  by_cases hy1 : y ≤ 1
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hy hy1 hle) (hA y hy)
  · simp [source_zero (le_of_not_ge hy1)]

/-- The actual combined Möbius square source takes a negative value below one. -/
theorem routePCoprimeSquareSource_exists_negative :
    ∃ y : ℝ, 0 < y ∧ y < 1 ∧ (routePCoprimeSquareSource y).re < 0 := by
  have hex : ∃ y : ℝ, 0 < y ∧ (routePCoprimeSquareSource y).re < 0 := by
    by_contra hn
    push Not at hn
    have hj := (Complex.continuous_re.tendsto (routePCoprimeSquareMass : ℂ)).comp
      mellin_routePCoprimeSquareSource_simpleJet
    simp only [Function.comp_def, Complex.ofReal_re, Complex.div_ofReal_re] at hj
    have hev := hj.eventually (eventually_gt_nhds routePCoprimeSquareMass_pos)
    have hep : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    obtain ⟨ε, hε, hp⟩ := (hep.and hev).exists
    change 0 < ε at hε
    have hpos : 0 < (mellin routePCoprimeSquareSource (1 + (ε : ℂ))).re :=
      (div_pos_iff_of_pos_right hε).mp hp
    have hz := (Complex.continuous_re.tendsto (0 : ℂ)).comp
      mellin_routePCoprimeSquareSource_tendsto_zero
    simp only [Function.comp_def, Complex.zero_re] at hz
    have hle : (mellin routePCoprimeSquareSource (1 + (ε : ℂ))).re ≤ 0 := by
      apply ge_of_tendsto hz
      have he : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < ε :=
        (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, he] with δ hδ hd
      exact budget_antitone hn hε hδ hd.le
    exact (not_lt_of_ge hle) hpos
  obtain ⟨y, hy, hn⟩ := hex
  refine ⟨y, hy, ?_, hn⟩
  by_contra h
  simp [source_zero (le_of_not_gt h)] at hn

/-- This is a native sign obstruction, not a counterexample to RH. -/
theorem nativeCoprimeEnergy_exists_negative :
    ∃ t : ℝ, 0 < t ∧ logarithmicCoprimeEnergy routePCoprimeNativeProfile t < 0 := by
  obtain ⟨y, hy, hy1, hn⟩ := routePCoprimeSquareSource_exists_negative
  refine ⟨-Real.log y, neg_pos.mpr (Real.log_neg hy hy1), ?_⟩
  rw [routePCoprimeSquareSource_eq_nativeCoprimeEnergy_log hy, Complex.ofReal_re] at hn
  exact hn

theorem nativeCoprimeCross_lt_neg_square :
    ∃ t : ℝ, 0 < t ∧ logarithmicCoprimeCross routePCoprimeNativeProfile t <
      -(routePCoprimeNativeProfile t ^ 2) := by
  obtain ⟨t, ht, hn⟩ := nativeCoprimeEnergy_exists_negative
  refine ⟨t, ht, ?_⟩
  rw [logarithmicCoprimeEnergy_eq_endpoint_add_cross routePCoprimeNativeProfile ht.le] at hn
  linarith

theorem nativeCoprimeCross_exists_negative :
    ∃ t : ℝ, 0 < t ∧ logarithmicCoprimeCross routePCoprimeNativeProfile t < 0 := by
  obtain ⟨t, ht, hn⟩ := nativeCoprimeCross_lt_neg_square
  refine ⟨t, ht, ?_⟩
  nlinarith [sq_nonneg (routePCoprimeNativeProfile t)]

end RHTower
