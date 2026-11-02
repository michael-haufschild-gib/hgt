import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LinearOverlapBoundsControlBothPacketArguments
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryProfileHasALogarithmicHighConductorGap

/-!
# Linear overlap comparison retains its cutoff ratio

Orthogonality makes the low coefficient packet proportional to `log R / log N`.
The linear bilinear overlap estimate preserves that small factor. The remaining
coefficient-high packet is controlled by the cubic lag estimate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  SpacingScaleHarmonicAnalysis CriticalScaleArithmeticRigidity ArithmeticElectrostatics

private def lowBandPacket (Q₁ N : ℕ) (a : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N

private def highBandCoeffs (Q₁ : ℕ) (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m ≤ Q₁ then 0 else a m

private def highBandPacket (Q₁ R' N : ℕ) (a : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ m ∈ Icc 1 R', highBandCoeffs Q₁ a m • normalizedRamanujanHorizonVector m N

private theorem lowBand_highBand_packet_split {Q₁ R' N : ℕ} {a : ℕ → ℝ}
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hQ₁ : 2 ≤ Q₁) (hQR' : Q₁ ≤ R') (hRR_N : R' * R' ≤ N)
    (hlog18_R' : 18 * (1 + Real.log R') ≤ Real.log N)
    (hu_eq : u = ∑ m ∈ Icc 1 R', a m • normalizedRamanujanHorizonVector m N)
    (huQ : u ∈ (conductorSubspace Q₁ N)ᗮ)
    (hu_sq_ge : 3 / 4 ≤ ‖u‖ ^ 2) (hu_le1 : ‖u‖ ≤ 1)
    (h1080 : 1080 * ((1 + Real.log R') / Real.log N) ≤ 1) :
    u = lowBandPacket Q₁ N a + highBandPacket Q₁ R' N a ∧
    lowBandPacket Q₁ N a ∈ conductorSubspace R' N ∧
    highBandPacket Q₁ R' N a ∈ conductorSubspace R' N ∧
    ‖lowBandPacket Q₁ N a‖ ≤ 54 * (1 + Real.log R') / Real.log N ∧
    ‖lowBandPacket Q₁ N a‖ ≤ 1 / 20 ∧
    1 / 2 ≤ ‖highBandPacket Q₁ R' N a‖ ^ 2 ∧
    ‖highBandPacket Q₁ R' N a‖ ≤ 2 := by
  have hR'2 : 2 ≤ R' := hQ₁.trans hQR'
  have huLow_R' : lowBandPacket Q₁ N a = ∑ m ∈ Icc 1 R',
      (if m ≤ Q₁ then a m else 0) • normalizedRamanujanHorizonVector m N := by
    unfold lowBandPacket
    have hsub : Icc 1 Q₁ ⊆ Icc 1 R' := Icc_subset_Icc le_rfl hQR'
    calc
      (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) =
          ∑ m ∈ Icc 1 Q₁,
            (if m ≤ Q₁ then a m else 0) • normalizedRamanujanHorizonVector m N :=
        sum_congr rfl fun m hm => by rw [if_pos (mem_Icc.mp hm).2]
      _ = _ := sum_subset hsub fun m hmR hmQ => by
        have hnot : ¬m ≤ Q₁ := fun h => hmQ (mem_Icc.mpr ⟨(mem_Icc.mp hmR).1, h⟩)
        rw [if_neg hnot, zero_smul]
  have hu_split : u = lowBandPacket Q₁ N a + highBandPacket Q₁ R' N a := by
    rw [hu_eq, huLow_R', highBandPacket]
    unfold highBandCoeffs
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  have huLow_mem : lowBandPacket Q₁ N a ∈ conductorSubspace R' N := by
    unfold lowBandPacket
    exact conductorSubspace_mono hQR' N
      (sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q₁ N a)
  have hy_mem : highBandPacket Q₁ R' N a ∈ conductorSubspace R' N := by
    unfold highBandPacket
    exact sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R' N (highBandCoeffs Q₁ a)
  have huLow_bound : ‖lowBandPacket Q₁ N a‖ ≤ 54 * (1 + Real.log R') / Real.log N := by
    have hlow := (low_band_norm_le_of_mem_orthogonal (by omega : 1 ≤ Q₁) hQR' hR'2 hRR_N
      hlog18_R' (hu_eq ▸ huQ)).2
    rw [← hu_eq, show (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) =
      lowBandPacket Q₁ N a from rfl] at hlow
    have h0 : 0 ≤ 54 * (1 + Real.log R') / Real.log N := by
      have := Real.log_natCast_nonneg R'; positivity
    exact hlow.trans ((mul_le_mul_of_nonneg_left hu_le1 h0).trans_eq (mul_one _))
  have huLow_le20 : ‖lowBandPacket Q₁ N a‖ ≤ 1 / 20 := by
    have h54 : 54 * (1 + Real.log R') / Real.log N =
        54 * ((1 + Real.log R') / Real.log N) := by ring
    linarith only [huLow_bound, h1080, h54]
  have hy_bounds : 1 / 2 ≤ ‖highBandPacket Q₁ R' N a‖ ^ 2 ∧ ‖highBandPacket Q₁ R' N a‖ ≤ 2 := by
    have hu_ge : 17 / 20 ≤ ‖u‖ := by nlinarith only [hu_sq_ge, norm_nonneg u]
    have htri1 : ‖u‖ ≤ ‖lowBandPacket Q₁ N a‖ + ‖highBandPacket Q₁ R' N a‖ := by
      rw [hu_split]; exact norm_add_le _ _
    have hy_ge : 4 / 5 ≤ ‖highBandPacket Q₁ R' N a‖ := by
      linarith only [hu_ge, htri1, huLow_le20]
    have hy_eq : highBandPacket Q₁ R' N a = u - lowBandPacket Q₁ N a := by
      rw [hu_split]; abel
    have htri2 : ‖highBandPacket Q₁ R' N a‖ ≤ ‖u‖ + ‖lowBandPacket Q₁ N a‖ := by
      rw [hy_eq]; exact norm_sub_le _ _
    exact ⟨by nlinarith only [hy_ge], by linarith only [htri2, hu_le1, huLow_le20]⟩
  exact ⟨hu_split, huLow_mem, hy_mem, huLow_bound, huLow_le20, hy_bounds.1, hy_bounds.2⟩

/-- Above the low conductor space, overlap costs `c log R / log N` plus the cubic
lag error. No error term is required to be bounded by an absolute constant. -/
theorem exists_overlapMatrix_high_inner_le_linear_cutoff_rate {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Q R N : ℕ} {c : ℝ},
      2 ≤ Q → Q ≤ R → R ^ 6 ≤ N → 1080 * (1 + Real.log R) ≤ Real.log N →
      1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ a : ℕ → ℝ,
      (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace Q N)ᗮ →
      ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ = 1 →
      |⟪Matrix.toEuclideanLin (overlapMatrix φ c N)
          (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N),
          ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N⟫| ≤
        C * (c * (1 + Real.log R) / Real.log N +
          c ^ 2 * (1 + Real.log c) / Real.log N + c ^ 5 * Real.log N / N +
          c ^ 3 / Real.sqrt Q + c ^ 3 * (R : ℝ) ^ 4 / N) := by
  obtain ⟨Cov, hCov, hov⟩ := exists_overlapMatrix_inner_le_linear hφ hsupp hM
  obtain ⟨Cmid, hCmid, hmid⟩ := exists_overlapMatrix_midBand_inner_le_cubic hφ hsupp hM
  refine ⟨270 * Cov + 4 * Cmid + 1, by positivity, ?_⟩
  intro Q R N c hQ hQR hR6 hlog hc hcL hw hrad hsize a huQ huNorm
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  have hR : 2 ≤ R := hQ.trans hQR
  have hR4 : R ^ 4 ≤ N :=
    (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 4 ≤ 6)).trans hR6
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have hL : 0 < Real.log N := by linarith only [hlog, Real.log_natCast_nonneg R]
  have h18 : 18 * (1 + Real.log R) ≤ Real.log N := by
    linarith only [hlog, Real.log_natCast_nonneg R]
  have h1080 : 1080 * ((1 + Real.log R) / Real.log N) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hL]
    exact hlog
  obtain ⟨hsplit, hv, hy, hvBound, hv20, -, hy2⟩ :=
    lowBand_highBand_packet_split hQ hQR hRR h18 (show u = _ from rfl) huQ
      (by rw [huNorm]; norm_num) huNorm.le h1080
  let v := lowBandPacket Q N a
  let y := highBandPacket Q R N a
  let A := Matrix.toEuclideanLin (overlapMatrix φ c N)
  change u = v + y at hsplit
  change v ∈ conductorSubspace R N at hv
  change y ∈ conductorSubspace R N at hy
  change ‖v‖ ≤ 54 * (1 + Real.log R) / Real.log N at hvBound
  change ‖v‖ ≤ 1 / 20 at hv20
  change ‖y‖ ≤ 2 at hy2
  have hdiffEq : ⟪A u, u⟫ - ⟪A y, y⟫ =
      ⟪A v, v⟫ + ⟪A v, y⟫ + ⟪A y, v⟫ := by
    rw [hsplit, map_add, inner_add_left, inner_add_right, inner_add_right]
    ring
  have h1 := hov hR hR4 h18 hc hcL hw hv hv
  have h2 := hov hR hR4 h18 hc hcL hw hv hy
  have h3 := hov hR hR4 h18 hc hcL hw hy hv
  have hnormSum : ‖v‖ * ‖v‖ + ‖v‖ * ‖y‖ + ‖y‖ * ‖v‖ ≤ 5 * ‖v‖ := by
    have hv1 : ‖v‖ ≤ 1 := by linarith only [hv20]
    have hvv := mul_le_mul_of_nonneg_left hv1 (norm_nonneg v)
    have hvy := mul_le_mul_of_nonneg_left hy2 (norm_nonneg v)
    have hyv := mul_le_mul_of_nonneg_right hy2 (norm_nonneg v)
    linarith only [hvv, hvy, hyv]
  have hdiff : |⟪A u, u⟫ - ⟪A y, y⟫| ≤
      270 * Cov * (c * (1 + Real.log R) / Real.log N) := by
    rw [hdiffEq]
    calc
      _ ≤ |⟪A v, v⟫| + |⟪A v, y⟫| + |⟪A y, v⟫| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ Cov * c * (‖v‖ * ‖v‖ + ‖v‖ * ‖y‖ + ‖y‖ * ‖v‖) := by
        linarith only [h1, h2, h3]
      _ ≤ Cov * c * (5 * (54 * (1 + Real.log R) / Real.log N)) :=
        mul_le_mul_of_nonneg_left
          (hnormSum.trans (by linarith only [hvBound])) (mul_nonneg hCov.le (zero_le_one.trans hc))
      _ = _ := by ring
  have ha0 : ∀ m ∈ Icc 1 Q, highBandCoeffs Q a m = 0 := fun m hm => if_pos (mem_Icc.mp hm).2
  have hmy := hmid hQ hQR hRR h18 hc hcL hw hrad hsize ha0
  let rate := c ^ 2 * (1 + Real.log c) / Real.log N + c ^ 5 * Real.log N / N +
    c ^ 3 / Real.sqrt Q + c ^ 3 * (R : ℝ) ^ 4 / N
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hlogc : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc]
  have hrate : 0 ≤ rate := by dsimp only [rate]; positivity
  change |⟪A y, y⟫| ≤ Cmid * rate * ‖y‖ ^ 2 at hmy
  have hy4 : ‖y‖ ^ 2 ≤ 4 := by nlinarith only [hy2, norm_nonneg y]
  have hyBound : |⟪A y, y⟫| ≤ 4 * Cmid * rate := by
    exact hmy.trans ((mul_le_mul_of_nonneg_left hy4 (mul_nonneg hCmid.le hrate)).trans_eq (by ring))
  have habs : |⟪A u, u⟫| ≤ |⟪A u, u⟫ - ⟪A y, y⟫| + |⟪A y, y⟫| := by
    simpa only [sub_add_cancel] using abs_add_le (⟪A u, u⟫ - ⟪A y, y⟫) ⟪A y, y⟫
  have hfirst : 0 ≤ c * (1 + Real.log R) / Real.log N := by positivity
  have hpay1 := mul_nonneg (show 0 ≤ 4 * Cmid + 1 by positivity) hfirst
  have hpay2 := mul_nonneg (show 0 ≤ 270 * Cov + 1 by positivity) hrate
  change |⟪A u, u⟫| ≤ _
  dsimp only [rate] at hyBound hpay2
  nlinarith only [habs, hdiff, hyBound, hpay1, hpay2]

#print axioms exists_overlapMatrix_high_inner_le_linear_cutoff_rate

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
