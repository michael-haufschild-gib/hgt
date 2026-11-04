import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeNearMean

/-!
# The near Gram retains the polar coefficient and each divisor mean

Linearization and periodic cancellation leave a coefficient-weighted mean.
Conductor one is kept explicitly; no pole coefficient is discarded when
passing from exact harmonic centering to the near-Gram form.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  BezoutValuationIncidence

/-- The near-weight mass costs its number of shifts, with the exact overlap dependence. -/
theorem abs_sum_nearWeightMass_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc : 1 ≤ c) :
    |∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, nearWeightMass φ c N h| ≤
      (20 * Real.exp 2 * (∫ u, φ u ^ 2)) * c * (1 + Real.log c) := by
  have hM0 : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hlog : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc]
  calc
    _ ≤ ∑ _h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
        10 * (∫ u, φ u ^ 2) * (1 + Real.log c) :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun h _ => abs_nearWeightMass_le hφ hsupp hN hc h)
    _ = (⌊linearNearRowRadius c⌋₊ : ℝ) *
        (10 * (∫ u, φ u ^ 2) * (1 + Real.log c)) := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ linearNearRowRadius c * (10 * (∫ u, φ u ^ 2) * (1 + Real.log c)) :=
      mul_le_mul_of_nonneg_right (Nat.floor_le (by unfold linearNearRowRadius; positivity))
        (by positivity)
    _ = _ := by unfold linearNearRowRadius; ring

/-- The near-Gram quadratic form separates the polar coefficient from the individual divisor means. -/
theorem exists_nearGram_packet_form_polar_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Q N : ℕ} {c : ℝ},
      2 ≤ Q → Q * Q ≤ N → 18 * (1 + Real.log Q) ≤ Real.log N →
      1 ≤ c → c / N ≤ 1 → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ∀ a : ℕ → ℝ,
      let u := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
      |∑ n ∈ Icc 1 N, primeHorizonExtension u n * nearGram φ c N (primeHorizonExtension u) n| ≤
        C * ((c ^ 5 / N + c ^ 3 * (Q : ℝ) ^ 4 / (N * Real.log N)) * ‖u‖ ^ 2 +
          (1 + Real.log c) / Real.log N *
            ((∑ m ∈ (Icc 1 Q).filter (fun m => m ≠ 1),
              a m ^ 2 * ((ArithmeticFunction.sigma 1 m : ℝ) / m.totient)) + c * a 1 ^ 2)) := by
  obtain ⟨A, hA, herr⟩ := exists_midBand_lag_sub_linearized_le hφ hsupp hM
  obtain ⟨B, hB, hosc⟩ := exists_midBand_osc_sum_le hφ hsupp hM
  obtain ⟨D, hD, hmean⟩ := exists_midBandMeanSum_sub_pole_bound hφ hsupp
  let P := 20 * Real.exp 2 * (∫ u, φ u ^ 2)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  let K := A + B + D + P
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨2 / (∫ u, φ u ^ 2) * K, by positivity, ?_⟩
  intro Q N c hQ hQN hlog hc hw hrad a
  dsimp only
  let u := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
  let V := ∑ m ∈ (Icc 1 Q).filter (fun m => m ≠ 1),
    a m ^ 2 * ((ArithmeticFunction.sigma 1 m : ℝ) / m.totient)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hL : 0 < Real.log N := by linarith only [hlog, Real.log_natCast_nonneg Q]
  have hN : 1 ≤ N := (Nat.mul_pos (by omega : 0 < Q) (by omega : 0 < Q)).trans_le hQN
  have hc0 := zero_lt_one.trans_le hc
  have hlogc : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc]
  have hHN : 2 * ⌊linearNearRowRadius c⌋₊ ≤ N := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    have hf := Nat.floor_le h0
    have h : ((2 * ⌊linearNearRowRadius c⌋₊ : ℕ) : ℝ) ≤ N := by
      push_cast
      nlinarith only [h0, hf, hrad]
    exact_mod_cast h
  have hmean' : |midBandMeanSum φ Q N c a| ≤
      D * (1 + Real.log c) * V + P * c * (1 + Real.log c) * a 1 ^ 2 := by
    have hp := mul_le_mul_of_nonneg_left (abs_sum_nearWeightMass_le hφ hsupp hN hc) (sq_nonneg (a 1))
    have h := abs_add_le
      (midBandMeanSum φ Q N c a -
        a 1 ^ 2 * ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, nearWeightMass φ c N h)
      (a 1 ^ 2 * ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, nearWeightMass φ c N h)
    rw [sub_add_cancel, abs_mul, abs_of_nonneg (sq_nonneg _)] at h
    exact h.trans ((add_le_add (hmean (by omega) hN hc hHN a) hp).trans_eq (by dsimp only [P, V]; ring))
  have hlag : |midBandLagSum φ Q N c a| ≤
      K * ((c ^ 5 * Real.log N / N + c ^ 3 * (Q : ℝ) ^ 4 / N) * ‖u‖ ^ 2 +
        (1 + Real.log c) * (V + c * a 1 ^ 2)) := by
    have he := herr (R₂ := Q) hL hc hrad a
    have ho := hosc hQ hQN hlog hc hrad a
    have hid : midBandLagSum φ Q N c a =
        (midBandLagSum φ Q N c a - midBandLinearizedSum φ Q N c a) +
          midBandMeanSum φ Q N c a + midBandOscSum φ Q N c a := by
      linarith only [midBandLinearizedSum_eq_mean_add_osc φ Q N c a]
    have htri : |midBandLagSum φ Q N c a| ≤
        |midBandLagSum φ Q N c a - midBandLinearizedSum φ Q N c a| +
          |midBandMeanSum φ Q N c a| + |midBandOscSum φ Q N c a| := by
      calc
        _ = |(midBandLagSum φ Q N c a - midBandLinearizedSum φ Q N c a) +
          midBandMeanSum φ Q N c a + midBandOscSum φ Q N c a| := congrArg abs hid
        _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have hAK : A ≤ K := by dsimp only [K]; linarith only [hB, hD, hP]
    have hBK : B ≤ K := by dsimp only [K]; linarith only [hA, hD, hP]
    have hDK : D ≤ K := by dsimp only [K]; linarith only [hA, hB, hP]
    have hPK : P ≤ K := by dsimp only [K]; linarith only [hA, hB, hD]
    have he' := he.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAK (by positivity : 0 ≤ c ^ 5 * Real.log N / (N : ℝ)))
      (sq_nonneg _))
    have ho' := ho.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBK (by positivity : 0 ≤ c ^ 3 * (Q : ℝ) ^ 4 / (N : ℝ)))
      (sq_nonneg _))
    have hd' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDK hlogc) hV
    have hp' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPK hc0.le) hlogc) (sq_nonneg (a 1))
    exact htri.trans ((add_le_add (add_le_add he' (hmean'.trans (add_le_add hd' hp'))) ho').trans_eq (by ring))
  have hform : (∑ n ∈ Icc 1 N, primeHorizonExtension u n * nearGram φ c N (primeHorizonExtension u) n) =
      (1 / ∫ v, φ v ^ 2) * (Real.log N)⁻¹ * (2 * midBandLagSum φ Q N c a) := by
    have hlead := midBand_leadKernel_sum_eq (R₂ := Q) hφ hsupp hL hc0 hw hrad a
    change _ = (Real.log N)⁻¹ * (2 * midBandLagSum φ Q N c a) at hlead
    rw [mul_assoc, ← hlead, mul_sum]
    apply sum_congr rfl
    intro n _
    unfold nearGram midBandLeadKernel
    rw [mul_sum, mul_sum, mul_sum]
    exact sum_congr rfl fun j _ => by rw [abs_sub_comm]; ring
  rw [hform, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (1 / ∫ v, φ v ^ 2) * (Real.log N)⁻¹), abs_mul, abs_two]
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlag zero_le_two)
    (by positivity : 0 ≤ (1 / ∫ v, φ v ^ 2) * (Real.log N)⁻¹)
  exact h.trans_eq (by dsimp only [V]; field_simp [hL.ne']; ring)

#print axioms abs_sum_nearWeightMass_le
#print axioms exists_nearGram_packet_form_polar_bound

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
