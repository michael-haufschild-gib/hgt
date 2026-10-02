import GaloisForLFunctions.RHTower.RoutePPairedSourceCurrentEscape
import GaloisForLFunctions.RHTower.RoutePCompensatedTerminalEscape
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePLinearHistoryEscape
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePActiveQuantileCellPort

/-!
# Complete paired-current escape for positive native prime heads

Every active prime-power atom retains its literal primitive Xi coefficient.
One common positive scaling of cofinally late native heads makes the complete
matched-minus-quantile parabolic form exactly minus one while its full Xi jet
norm is arbitrarily small. The proof combines unconditional negative linear
history excursions with the actual mass bound and uniform normalized-jet
control. Consequently even the unscaled native heads admit no fixed lower
budget by Xi norm squared.

This excludes that source-energy payment mechanism; it neither proves nor
falsifies the RH-equivalent native-history linear floor.
-/

open Complex Set Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section

def routePNativePrimitive (n : ℕ) (hn : IsPrimePow n) : Nat.Primes × ℕ :=
  Classical.choose (isPrimePow_exists_routePPrimitiveBurnolZeroClockRay n hn)

theorem routePNativePrimitive_node (n : ℕ) (hn : IsPrimePow n) :
    xiGammaEulerValuationNat (routePNativePrimitive n hn) = n :=
  (Classical.choose_spec (isPrimePow_exists_routePPrimitiveBurnolZeroClockRay n hn)).1

/-- The literal primitive jet on active nodes, zero on inactive nodes. -/
def routePNativeAtomXiJet (n : ℕ) : DeningerArithmeticJetHilbert :=
  if hn : IsPrimePow n then
    (criticalMellinAtomWeight n : ℂ) •
      routePDepthMassNormalizedXiJet (routePNativePrimitive n hn).1 (routePNativePrimitive n hn).2
  else 0

theorem routePNativeAtomXiJet_eq_literal (n : ℕ) (hn : IsPrimePow n) :
    routePNativeAtomXiJet n =
      routePDeningerUpperSquaredCauchyJet (-finiteVonMangoldtDepthOneAmplitude n)
        (routePPrimitiveDeningerUpperPoint (routePNativePrimitive n hn) 0) := by
  rw [routePNativeAtomXiJet, dif_pos hn, routePDepthMassNormalizedXiJet_eq]
  have hw : (criticalMellinAtomWeight n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalMellinAtomWeight_pos hn).ne'
  simp only [Prod.mk.eta, routePNativePrimitive_node, smul_smul, mul_inv_cancel₀ hw, one_smul]

theorem routePNativeAtomXiJet_norm_le (n : ℕ) :
    ‖routePNativeAtomXiJet n‖ ≤ criticalMellinAtomWeight n *
      ‖routePDepthMassNormalizedXiJet ⟨2, Nat.prime_two⟩ 0‖ := by
  have hw : 0 ≤ criticalMellinAtomWeight n :=
    criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
  by_cases hn : IsPrimePow n
  · rw [routePNativeAtomXiJet, dif_pos hn, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (routeP_massNormalizedXiJet_norm_le_base _ _) hw
  · rw [routePNativeAtomXiJet, dif_neg hn, norm_zero]
    positivity

/-- All native atoms through the physical cutoff, each with its original coefficient. -/
def routePNativeXiHead (K : ℕ) : DeningerArithmeticJetHilbert :=
  ∑ n ∈ Finset.range (K + 1), routePNativeAtomXiJet (n + 2)

theorem routePNativeXiHead_norm_le_mass (K : ℕ) :
    ‖routePNativeXiHead K‖ ≤ ccmActualHeadParabolicMass K *
      ‖routePDepthMassNormalizedXiJet ⟨2, Nat.prime_two⟩ 0‖ := by
  calc
    _ ≤ ∑ n ∈ Finset.range (K + 1), ‖routePNativeAtomXiJet (n + 2)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (K + 1), criticalMellinAtomWeight (n + 2) *
        ‖routePDepthMassNormalizedXiJet ⟨2, Nat.prime_two⟩ 0‖ :=
      Finset.sum_le_sum fun n _ => routePNativeAtomXiJet_norm_le (n + 2)
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem routeP_native_mass_div_index_tendsto_zero :
    Tendsto (fun K : ℕ => ccmActualHeadParabolicMass K / ((K + 2 : ℕ) : ℝ)) atTop (nhds 0) := by
  have hx : Tendsto (fun K : ℕ => ((K + 2 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hx)
  have hupper (K : ℕ) : ccmActualHeadParabolicMass K / ((K + 2 : ℕ) : ℝ) ≤
      21 * (Real.sqrt ((K + 2 : ℕ) : ℝ))⁻¹ := by
    let x : ℝ := ((K + 2 : ℕ) : ℝ)
    have hx0 : 0 < x := by dsimp [x]; positivity
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    have hm : ccmActualHeadParabolicMass K ≤ 21 * Real.sqrt x := by
      rw [routeP_parabolicMass_eq_primeMassHalf]
      exact primeMassHalf_le_sqrt (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) K])
    change ccmActualHeadParabolicMass K / x ≤ 21 * (Real.sqrt x)⁻¹
    calc
      _ ≤ (21 * Real.sqrt x) / x := div_le_div_of_nonneg_right hm hx0.le
      _ = _ := by field_simp; nlinarith only [hs2]
  exact squeeze_zero (fun K => div_nonneg (ccmActualHeadParabolicMass_pos K).le (by positivity))
    hupper (by simpa only [mul_zero, Function.comp_def] using hi.const_mul 21)

/-- Both complete physical moment sums, with the same common source scaling. -/
def routePNativePairedHeadForm (K : ℕ) (s : ℝ) : ℝ :=
  ccmParabolicForm (s • ccmActualHeadMatchedParabolicAggregate K) -
    ccmParabolicForm (s • ccmActualHeadQuantileParabolicAggregate K)

theorem routePNativePairedHeadForm_eq (K : ℕ) (s : ℝ) :
    routePNativePairedHeadForm K s = s ^ 2 * ccmActualHeadParabolicMass K *
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K := by
  have hh := ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect_eq_sourceCurrent K
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary] at hh
  have hid := (eq_div_iff (ccmActualHeadParabolicMass_pos K).ne').mp hh
  have hform (v : Fin 3 → ℝ) : ccmParabolicForm (s • v) = s ^ 2 * ccmParabolicForm v := by
    simp only [ccmParabolicForm, Pi.smul_apply, smul_eq_mul]
    ring
  rw [routePNativePairedHeadForm, hform, hform]
  calc
    _ = s ^ 2 * (ccmParabolicForm (ccmActualHeadMatchedParabolicAggregate K) -
      ccmParabolicForm (ccmActualHeadQuantileParabolicAggregate K)) := by ring
    _ = _ := by rw [← hid]; ring

/-- A cofinal positive native-head witness with retained negative unit current. -/
theorem routeP_native_positive_head_negative_unit_at_small_Xi {ε : ℝ} (hε : 0 < ε) (L : ℕ) :
    ∃ (K : ℕ) (s : ℝ), L ≤ K ∧ 0 < s ∧
      ‖(s : ℂ) • routePNativeXiHead K‖ < ε ∧ routePNativePairedHeadForm K s = -1 := by
  obtain ⟨δ, hδ, hescape⟩ := routeP_normalized_history_cofinally_below_negative_linear
  let D : ℝ := ‖routePDepthMassNormalizedXiJet ⟨2, Nat.prime_two⟩ 0‖
  have hD : 0 ≤ D := norm_nonneg _
  have htend : Tendsto (fun K : ℕ => D ^ 2 *
      (ccmActualHeadParabolicMass K / ((K + 2 : ℕ) : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using routeP_native_mass_div_index_tendsto_zero.const_mul (D ^ 2)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htend.eventually
    (gt_mem_nhds (by positivity : 0 < δ * ε ^ 2)))
  obtain ⟨K, hK, hneg⟩ := hescape (max L N)
  let m := ccmActualHeadParabolicMass K
  let x : ℝ := ((K + 2 : ℕ) : ℝ)
  let H := ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K
  have hm : 0 < m := ccmActualHeadParabolicMass_pos K
  have hx : 0 < x := by dsimp [x]; positivity
  have hH : H < -δ * x := hneg
  have hden : δ * m * x < -m * H := by
    have h := mul_lt_mul_of_pos_left hH hm
    nlinarith only [h]
  have hpos : 0 < -m * H := (by positivity : 0 < δ * m * x).trans hden
  let s : ℝ := 1 / Real.sqrt (-m * H)
  have hs : 0 < s := div_pos zero_lt_one (Real.sqrt_pos.mpr hpos)
  have hsden : s ^ 2 * (-m * H) = 1 := by
    dsimp [s]
    rw [div_pow, one_pow, Real.sq_sqrt hpos.le]
    exact div_mul_cancel₀ _ hpos.ne'
  have hsmall := hN K ((le_max_right _ _).trans hK)
  change D ^ 2 * (m / x) < δ * ε ^ 2 at hsmall
  have hsmall' : D ^ 2 * m < δ * ε ^ 2 * x := by
    rw [← mul_div_assoc] at hsmall
    exact (div_lt_iff₀ hx).mp hsmall
  have hJ := routePNativeXiHead_norm_le_mass K
  change ‖routePNativeXiHead K‖ ≤ m * D at hJ
  have hJ2 := pow_le_pow_left₀ (norm_nonneg _) hJ 2
  have hmSmall := mul_lt_mul_of_pos_right hsmall' hm
  have hdenSmall := mul_lt_mul_of_pos_left hden (sq_pos_of_pos hε)
  have hJsmall : ‖routePNativeXiHead K‖ ^ 2 < ε ^ 2 * (-m * H) := by
    nlinarith only [hJ2, hmSmall, hdenSmall]
  refine ⟨K, s, (le_max_left _ _).trans hK, hs, ?_, ?_⟩
  · apply (sq_lt_sq₀ (norm_nonneg _) hε.le).mp
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, mul_pow]
    calc
      _ < s ^ 2 * (ε ^ 2 * (-m * H)) := mul_lt_mul_of_pos_left hJsmall (sq_pos_of_pos hs)
      _ = ε ^ 2 := by rw [mul_left_comm, hsden, mul_one]
  · rw [routePNativePairedHeadForm_eq]
    change s ^ 2 * m * H = -1
    nlinarith only [hsden]

theorem not_routeP_native_current_eventually_lower_bounded_by_Xi :
    ¬ ∃ (C : ℝ) (L : ℕ), ∀ K : ℕ, L ≤ K →
      -C * ‖routePNativeXiHead K‖ ^ 2 ≤ routePNativePairedHeadForm K 1 := by
  rintro ⟨C, L, hC⟩
  let ε : ℝ := 1 / (|C| + 2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεone : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0 < |C| + 2)).mpr
    linarith [abs_nonneg C]
  have hεeq : (|C| + 2) * ε = 1 := by dsimp [ε]; field_simp
  obtain ⟨K, s, hK, hs, hn, hf⟩ := routeP_native_positive_head_negative_unit_at_small_Xi hε L
  have hlow := mul_le_mul_of_nonneg_left (hC K hK) (sq_nonneg s)
  have hhom : routePNativePairedHeadForm K s = s ^ 2 * routePNativePairedHeadForm K 1 := by
    rw [routePNativePairedHeadForm_eq, routePNativePairedHeadForm_eq]
    ring
  have hnorm : ‖(s : ℂ) • routePNativeXiHead K‖ ^ 2 =
      s ^ 2 * ‖routePNativeXiHead K‖ ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, mul_pow]
  have hlow' : -C * ‖(s : ℂ) • routePNativeXiHead K‖ ^ 2 ≤ -1 := by
    rw [hnorm, ← hf, hhom]
    nlinarith only [hlow]
  have hnorm0 := norm_nonneg ((s : ℂ) • routePNativeXiHead K)
  have hnorm1 := hn.trans_le hεone
  have hsq : ‖(s : ℂ) • routePNativeXiHead K‖ ^ 2 ≤
      ‖(s : ℂ) • routePNativeXiHead K‖ := by nlinarith
  have hm := mul_lt_mul_of_pos_left hn (by positivity : 0 < |C| + 2)
  rw [hεeq] at hm
  have hm2 := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ |C| + 2)
  have hCabs := mul_le_mul_of_nonneg_right (le_abs_self C)
    (sq_nonneg ‖(s : ℂ) • routePNativeXiHead K‖)
  nlinarith [sq_nonneg ‖(s : ℂ) • routePNativeXiHead K‖]

end
end RHTower
