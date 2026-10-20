import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateSpanPlateauLaw
import GaloisForLFunctions.ArithmeticCriticalityTheory.SingleShiftCompleteness

/-!
# The odd arithmetic form is never subcritical

In Pinchover's trichotomy a form `Q` is subcritical if it admits a Hardy weight: `W ≥ 0`, not
identically zero, with `Q(F) ≥ ∫ W F²` for every test. The odd Markov form admits none:

**Theorem** (`exists_odd_markovEnergy_lt_integral_weight_mul_sq`). For every locally integrable
`W ≥ 0` that is positive on a set of positive measure there is an odd `v ∈ C²_c(ℝ)` with

    markovEnergy(Φ v) < ∫ W(x) (Φ v)(x)² dx.

Hence the odd form is either supercritical (RH fails) or **critical** (RH holds), never
subcritical: `riemannHypothesis_iff_nonneg_and_no_hardyWeight`.

Proof. The pole-free pair `M_n = sinh(n/2) m_1 − sinh(1/2) m_n` has pole coefficient `σ = 0`, so by
the span plateau law its plateau truncations `M_n u_L` have Markov energy `O(e^{−8L})`. For each
`x ≠ 0` some `M_n(x) ≠ 0`, because `|m_n| ≤ Φ(0)` while `sinh(n/2) |m_1(x)| → ∞`. So `W M_n²` has
positive integral over some `[−R, R]` for some `n`, and `∫ W (M_n u_L)²` stays above it for
`L ≥ R`. Choosing `L` large beats the `O(e^{−8L})` energy.

The null directions are the pole-free superpositions of shifted ground states, an
infinite-dimensional family (the odd critical band of the theta span): the odd form, if nonnegative,
is critical with infinitely many independent approximate ground states, unlike a Schrödinger form,
whose critical ground state is unique and positive.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- Shifts `1, n` of the pole-free pair. -/
def nullPairShift (n : ℝ) : Fin 2 → ℝ := ![1, n]

/-- Coefficients `sinh(n/2), −sinh(1/2)` of the pole-free pair. -/
def nullPairCoeff (n : ℝ) : Fin 2 → ℝ := ![Real.sinh (n / 2), -Real.sinh (1 / 2)]

theorem spanShiftDifference_nullPair (n x : ℝ) :
    spanShiftDifference Finset.univ (nullPairCoeff n) (nullPairShift n) x =
      Real.sinh (n / 2) * shiftDifference 1 x - Real.sinh (1 / 2) * shiftDifference n x := by
  simp [spanShiftDifference, Fin.sum_univ_two, nullPairCoeff, nullPairShift]
  ring

theorem spanSourceCoefficient_nullPair (n : ℝ) :
    spanSourceCoefficient Finset.univ (nullPairCoeff n) (nullPairShift n) = 0 := by
  simp [spanSourceCoefficient, Fin.sum_univ_two, nullPairCoeff, nullPairShift]
  ring

/-- Away from the origin the pole-free pairs separate points: some `M_n(x) ≠ 0`. -/
theorem exists_nat_nullPair_ne_zero {x : ℝ} (hx : x ≠ 0) :
    ∃ n : ℕ, spanShiftDifference Finset.univ (nullPairCoeff n) (nullPairShift n) x ≠ 0 := by
  have hm1 : shiftDifference 1 x ≠ 0 := shiftDifference_ne_zero_of_ne one_pos hx
  have hm1' : 0 < |shiftDifference 1 x| := abs_pos.mpr hm1
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (Real.sinh (1 / 2) * riemannKernelReal 0 + 1) /
    |shiftDifference 1 x|)
  refine ⟨n, fun h0 => ?_⟩
  rw [spanShiftDifference_nullPair] at h0
  have hs : (n : ℝ) / 2 ≤ Real.sinh ((n : ℝ) / 2) :=
    Real.self_le_sinh_iff.mpr (by positivity)
  have hmn := abs_shiftDifference_le (n : ℝ) x
  have hs1 : 0 < Real.sinh (1 / 2) := Real.sinh_pos_iff.mpr (by norm_num)
  have hbig : 2 * (Real.sinh (1 / 2) * riemannKernelReal 0 + 1) < n * |shiftDifference 1 x| := by
    rwa [div_lt_iff₀ hm1'] at hn
  have hsn : 0 ≤ Real.sinh ((n : ℝ) / 2) := Real.sinh_nonneg_iff.mpr (by positivity)
  have heq : Real.sinh ((n : ℝ) / 2) * |shiftDifference 1 x| =
      Real.sinh (1 / 2) * |shiftDifference (n : ℝ) x| := by
    have h := congrArg abs (sub_eq_zero.mp h0)
    rwa [abs_mul, abs_mul, abs_of_nonneg hsn, abs_of_pos hs1] at h
  have h1 := mul_le_mul_of_nonneg_right hs hm1'.le
  have h2 := mul_le_mul_of_nonneg_left hmn hs1.le
  nlinarith

/-- The plateau truncation of the pole-free pair is an odd `C²_c` Doob test. -/
theorem spanPlateauProfile_neg (s : Finset (Fin 2)) (c a : Fin 2 → ℝ) (L x : ℝ) :
    spanPlateauProfile s c a L (-x) = -spanPlateauProfile s c a L x := by
  unfold spanPlateauProfile spanGroundState
  rw [smoothPlateau_neg, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [shiftedGroundState_neg]
  ring

/-- **No Hardy weight.** For every locally integrable `W ≥ 0`, positive on a set of positive
measure, some odd `v ∈ C²_c(ℝ)` has `markovEnergy(Φ v) < ∫ W (Φ v)²`. -/
theorem exists_odd_markovEnergy_lt_integral_weight_mul_sq {W : ℝ → ℝ} (hW0 : ∀ x, 0 ≤ W x)
    (hWi : LocallyIntegrable W) (hWpos : 0 < volume {x | 0 < W x}) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧ (∀ x, v (-x) = -v x) ∧
      markovEnergy (fun x => (phiDoobTest v x : ℂ)) < ∫ x, W x * phiDoobTest v x ^ 2 := by
  -- a pole-free pair seeing `W`
  set S : ℕ → Set ℝ := fun n =>
    {x | 0 < W x ∧ spanShiftDifference Finset.univ (nullPairCoeff n) (nullPairShift n) x ≠ 0}
    with hS_def
  have hcover : {x | 0 < W x} ⊆ {0} ∪ ⋃ n, S n := by
    intro x hx
    by_cases h0 : x = 0
    · exact Or.inl h0
    · obtain ⟨n, hn⟩ := exists_nat_nullPair_ne_zero h0
      exact Or.inr (mem_iUnion.mpr ⟨n, hx, hn⟩)
  obtain ⟨n, R, hpos⟩ : ∃ n : ℕ, ∃ R : ℕ, 0 < volume (S n ∩ Icc (-(R : ℝ)) R) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have hnull : volume (⋃ n, S n) = 0 := by
      refine measure_iUnion_null fun n => ?_
      have hU : S n = ⋃ R : ℕ, S n ∩ Icc (-(R : ℝ)) R := by
        ext x
        simp only [mem_iUnion, mem_inter_iff, mem_Icc]
        constructor
        · intro hx
          obtain ⟨R, hR⟩ := exists_nat_ge |x|
          exact ⟨R, hx, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
        · rintro ⟨_, hx, _⟩
          exact hx
      rw [hU]
      exact measure_iUnion_null fun R => nonpos_iff_eq_zero.mp (hcon n R)
    have h0 : volume ({x | 0 < W x}) = 0 :=
      measure_mono_null hcover (measure_union_null (by simp) hnull)
    exact absurd h0 hWpos.ne'
  set c := nullPairCoeff (n : ℝ)
  set a := nullPairShift (n : ℝ)
  set M := spanShiftDifference Finset.univ c a with hM_def
  have hMc : Continuous M := continuous_spanShiftDifference _ _ _
  -- the weighted mass on `[−R, R]` is positive
  have hIcc : IntegrableOn (fun x => W x * M x ^ 2) (Icc (-(R : ℝ)) R) :=
    (hWi.integrableOn_isCompact isCompact_Icc).mul_continuousOn (hMc.pow 2).continuousOn
      isCompact_Icc
  have hc₀ : 0 < ∫ x in Icc (-(R : ℝ)) R, W x * M x ^ 2 := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun x => mul_nonneg (hW0 x) (sq_nonneg _)) hIcc]
    refine lt_of_lt_of_le hpos (measure_mono fun x hx => ⟨?_, hx.2⟩)
    exact mul_ne_zero hx.1.1.ne' (pow_ne_zero 2 hx.1.2)
  -- the null sequence
  obtain ⟨K, hK0, hK⟩ := exists_abs_markovEnergy_spanPlateauProfile_le_of_poleFree
    (s := Finset.univ) (c := c) (a := a) (spanSourceCoefficient_nullPair n)
  obtain ⟨L, hLR, hLK⟩ : ∃ L : ℝ, (R : ℝ) ≤ L ∧
      K * Real.exp (-(8 * L)) < ∫ x in Icc (-(R : ℝ)) R, W x * M x ^ 2 := by
    have h0 : Tendsto (fun L : ℝ => K * Real.exp (-(8 * L))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 8))).const_mul K
      simpa [Function.comp_def, neg_mul] using this
    obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp (h0.eventually (gt_mem_nhds hc₀))
    exact ⟨max L₁ R, le_max_right _ _, hL₁ _ (le_max_left _ _)⟩
  refine ⟨spanPlateauProfile Finset.univ c a L, contDiff_spanPlateauProfile _ _ _ L,
    hasCompactSupport_spanPlateauProfile _ _ _ L, spanPlateauProfile_neg _ _ _ L, ?_⟩
  -- the weighted mass of the truncation dominates the mass on `[−R, R]`
  have htest : ∀ x, phiDoobTest (spanPlateauProfile Finset.univ c a L) x = M x * smoothPlateau L x :=
    phiDoobTest_spanPlateauProfile _ _ _ L
  have hsupp : Function.support (fun x => W x * (M x * smoothPlateau L x) ^ 2) ⊆
      Icc (-(L + 1)) (L + 1) := by
    intro x hx
    by_contra hout
    apply hx
    have h1 : L + 1 ≤ |x| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hout
      rcases hout with h | h
      · linarith [neg_abs_le x]
      · linarith [le_abs_self x]
    simp [smoothPlateau_eq_zero h1]
  have hint : Integrable fun x => W x * (M x * smoothPlateau L x) ^ 2 := by
    refine (integrableOn_iff_integrable_of_support_subset hsupp).mp ?_
    exact (hWi.integrableOn_isCompact isCompact_Icc).mul_continuousOn
      ((hMc.mul (contDiff_smoothPlateau L).continuous).pow 2).continuousOn isCompact_Icc
  have hmass : (∫ x in Icc (-(R : ℝ)) R, W x * M x ^ 2) ≤
      ∫ x, W x * phiDoobTest (spanPlateauProfile Finset.univ c a L) x ^ 2 := by
    simp_rw [htest]
    calc (∫ x in Icc (-(R : ℝ)) R, W x * M x ^ 2)
        = ∫ x in Icc (-(R : ℝ)) R, W x * (M x * smoothPlateau L x) ^ 2 := by
          refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
          have hxL : |x| ≤ L := (abs_le.mpr ⟨hx.1, hx.2⟩).trans hLR
          simp only [smoothPlateau_eq_one hxL, mul_one]
      _ ≤ ∫ x, W x * (M x * smoothPlateau L x) ^ 2 :=
          setIntegral_le_integral hint (ae_of_all _ fun x => mul_nonneg (hW0 x) (sq_nonneg _))
  have hQ := hK L
  calc markovEnergy (fun x => (phiDoobTest (spanPlateauProfile Finset.univ c a L) x : ℂ))
      ≤ K * Real.exp (-(8 * L)) := (le_abs_self _).trans hQ
    _ < ∫ x in Icc (-(R : ℝ)) R, W x * M x ^ 2 := hLK
    _ ≤ _ := hmass

/-- **RH is criticality of the odd form.** RH holds if and only if the odd Markov form is
nonnegative and admits no Hardy weight; the second condition holds unconditionally. -/
theorem riemannHypothesis_iff_nonneg_and_no_hardyWeight :
    RiemannHypothesis ↔
      (∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, v (-x) = -v x) →
          0 ≤ markovEnergy (fun x => (phiDoobTest v x : ℂ))) ∧
        ∀ W : ℝ → ℝ, (∀ x, 0 ≤ W x) → LocallyIntegrable W → 0 < volume {x | 0 < W x} →
          ¬ ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, v (-x) = -v x) →
            (∫ x, W x * phiDoobTest v x ^ 2) ≤ markovEnergy (fun x => (phiDoobTest v x : ℂ)) := by
  rw [← riemannHypothesis_iff_forall_odd_phiDoob_markovEnergy_nonneg]
  refine ⟨fun hRH => ⟨hRH, fun W hW0 hWi hWpos hHardy => ?_⟩, fun h => h.1⟩
  obtain ⟨v, hv, hvc, hodd, hlt⟩ := exists_odd_markovEnergy_lt_integral_weight_mul_sq hW0 hWi hWpos
  exact absurd (hHardy v hv hvc hodd) (not_le.mpr hlt)

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
