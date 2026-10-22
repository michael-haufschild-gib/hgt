import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileLorentzSupport

/-!
# Debt--geometry factorization of literal matched--quantile Lorentz current

This module tests the exact denominator-free Cauchy split whose first factor is the literal
quadratic displacement debt. The conjugate geometry is forced by the source current itself.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

open Filter

/-- Geometric conjugate of literal squared displacement debt on one strict-cross edge. -/
def ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry (m n : ℕ) : ℝ :=
  let c := ccmActualHeadMatchedPolarCentroid (n + 2) -
    ccmActualHeadMatchedPolarCentroid (m + 2)
  let d := ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
    ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)
  let w := criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2)
  w / 2 * (2 * c + d) ^ (2 : ℕ)

/-- **Exact debt--geometry factorization.** The strict-cross current squared is the product of
the literal ordered displacement debt and its denominator-free conjugate geometry. -/
theorem ccmActualHeadMatchedQuantileLorentzEdgeCurrent_sq_eq_debt_mul_conjugateGeometry
    (m n : ℕ) :
    ccmActualHeadMatchedQuantileLorentzEdgeCurrent m n ^ (2 : ℕ) =
      ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (n + 2) *
        ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry m n := by
  let c := ccmActualHeadMatchedPolarCentroid (n + 2) -
    ccmActualHeadMatchedPolarCentroid (m + 2)
  let d := ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
    ccmActualHeadMatchedQuantilePolarDisplacement (m + 2)
  let w := criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2)
  have hcurrent : ccmActualHeadMatchedQuantileLorentzEdgeCurrent m n =
      -(w / 2) * d * (2 * c + d) := by
    unfold ccmActualHeadMatchedQuantileLorentzEdgeCurrent
    rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge]
    unfold ccmActualHeadMatchedQuantileLorentzSquare ccmActualHeadMatchedQuantileLorentzEdge
    simp
    rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (m + 2),
      ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (n + 2)]
    dsimp only [c, d, w]
    ring
  rw [hcurrent]
  unfold ccmActualHeadMatchedQuantileParabolicDisplacementDebt
    ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry
  dsimp only [c, d, w]
  ring

lemma ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry_nonneg (m n : ℕ) :
    0 ≤ ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry m n := by
  unfold ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry
  apply mul_nonneg
  · exact div_nonneg
      (mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _) (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _))
      (by norm_num)
  · exact sq_nonneg _

/-- Total finite conjugate geometry of the strict-cross actual head. -/
def ccmActualHeadMatchedQuantileParabolicLorentzDebtConjugateGeometry (K : ℕ) : ℝ :=
  ∑ e ∈ ccmActualHeadMatchedQuantileLorentzEdgeSet K,
    ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry e.1 e.2

/-- **Exact debt-energy graph wall.** Cauchy uses the literal full displacement debt itself,
without an auxiliary resistance or a division by a displacement difference. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzDebtGeometryWall (K : ℕ) :
    (ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
      (ccmActualHeadMatchedQuantileParabolicSourceBoundary K)) ^ (2 : ℕ) ≤
      ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum K *
        ccmActualHeadMatchedQuantileParabolicLorentzDebtConjugateGeometry K := by
  have hCauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (ccmActualHeadMatchedQuantileLorentzEdgeSet K)
    (r := fun e => ccmActualHeadMatchedQuantileLorentzEdgeCurrent e.1 e.2)
    (f := fun e => ccmActualHeadMatchedQuantileParabolicDisplacementDebt (e.1 + 2) (e.2 + 2))
    (g := fun e => ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry e.1 e.2)
    (by
      rintro ⟨m, n⟩ h
      exact ccmActualHeadMatchedQuantileParabolicDisplacementDebt_nonneg (m + 2) (n + 2))
    (by
      rintro ⟨m, n⟩ h
      exact ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry_nonneg m n)
    (by
      rintro ⟨m, n⟩ h
      exact le_of_eq
        (ccmActualHeadMatchedQuantileLorentzEdgeCurrent_sq_eq_debt_mul_conjugateGeometry m n))
  rw [ccmActualHeadMatchedQuantileLorentzEdgeCurrent_sum_eq_parabolic_pairing] at hCauchy
  simpa [ccmActualHeadMatchedQuantileParabolicDisplacementDebtSum,
    ccmActualHeadMatchedQuantileParabolicLorentzDebtConjugateGeometry,
    ccmActualHeadMatchedQuantileLorentzEdgeSet, Finset.sum_sigma] using hCauchy

/-- Strict fixed geometry separating the base matched centroid from its next literal cell. -/
def ccmActualHeadMatchedQuantileLorentzBaseCentroidGap : ℝ :=
  ccmActualHeadMatchedPolarCentroid 3 - ccmActualHeadMatchedPolarCentroid 2

lemma ccmActualHeadMatchedQuantileLorentzBaseCentroidGap_pos :
    0 < ccmActualHeadMatchedQuantileLorentzBaseCentroidGap := by
  unfold ccmActualHeadMatchedQuantileLorentzBaseCentroidGap
  exact sub_pos.mpr (strictMono_ccmActualHeadMatchedPolarCentroid_shift_two (by omega))

/-- Every base-prime conjugate edge retains a fixed positive centroid-gap charge, independently
of its displacement. -/
theorem ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry_ge_base_weight_gap_sq
    {n : ℕ} (hn0 : n ≠ 0) :
    criticalMellinAtomWeight 2 * criticalMellinAtomWeight (n + 2) / 2 *
        ccmActualHeadMatchedQuantileLorentzBaseCentroidGap ^ (2 : ℕ) ≤
      ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry 0 n := by
  let c : ℝ := ccmActualHeadMatchedPolarCentroid (n + 2) -
    ccmActualHeadMatchedPolarCentroid 2
  let d : ℝ := ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
    ccmActualHeadMatchedQuantilePolarDisplacement 2
  let q : ℝ := ccmActualHeadQuantilePolarCentroid (n + 2) -
    ccmActualHeadQuantilePolarCentroid 2
  let w : ℝ := criticalMellinAtomWeight 2 * criticalMellinAtomWeight (n + 2)
  have hq : 0 ≤ q := by
    dsimp [q]
    exact sub_nonneg.mpr (ccmActualHeadQuantilePolarCentroid_le_of_le (by omega))
  have hc : ccmActualHeadMatchedQuantileLorentzBaseCentroidGap ≤ c := by
    dsimp [c, ccmActualHeadMatchedQuantileLorentzBaseCentroidGap]
    have hcent : ccmActualHeadMatchedPolarCentroid 3 ≤
        ccmActualHeadMatchedPolarCentroid (n + 2) := by
      exact (strictMono_ccmActualHeadMatchedPolarCentroid_shift_two.monotone (by omega))
    linarith
  have hgap : 0 ≤ ccmActualHeadMatchedQuantileLorentzBaseCentroidGap :=
    ccmActualHeadMatchedQuantileLorentzBaseCentroidGap_pos.le
  have hsum : c ≤ c + q := by linarith
  have hsquare : ccmActualHeadMatchedQuantileLorentzBaseCentroidGap ^ (2 : ℕ) ≤ (c + q) ^ (2 : ℕ) := by
    nlinarith
  have hw : 0 ≤ w / 2 := by
    dsimp [w]
    exact div_nonneg
      (mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _) (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _))
      (by norm_num)
  have hfactor : 2 * c + d = c + q := by
    dsimp [c, d, q]
    rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement 2,
      ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement (n + 2)]
    ring
  unfold ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry
  dsimp only [c, d, w]
  rw [hfactor]
  exact mul_le_mul_of_nonneg_left hsquare hw

/-- Fixed-base lower envelope for finite conjugate geometry. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzDebtConjugateGeometry_ge_baseOffDiagonalMass
    (K : ℕ) :
    (criticalMellinAtomWeight 2 / 2 *
      ccmActualHeadMatchedQuantileLorentzBaseCentroidGap ^ (2 : ℕ)) *
        (∑ n ∈ (Finset.range (K + 1)).erase 0,
          criticalMellinAtomWeight (n + 2)) ≤
      ccmActualHeadMatchedQuantileParabolicLorentzDebtConjugateGeometry K := by
  calc
    (criticalMellinAtomWeight 2 / 2 *
      ccmActualHeadMatchedQuantileLorentzBaseCentroidGap ^ (2 : ℕ)) *
        (∑ n ∈ (Finset.range (K + 1)).erase 0,
          criticalMellinAtomWeight (n + 2)) =
        ∑ n ∈ (Finset.range (K + 1)).erase 0,
          criticalMellinAtomWeight 2 * criticalMellinAtomWeight (n + 2) / 2 *
            ccmActualHeadMatchedQuantileLorentzBaseCentroidGap ^ (2 : ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ ∑ n ∈ (Finset.range (K + 1)).erase 0,
        ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry 0 n := by
      apply Finset.sum_le_sum
      intro n hn
      exact ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry_ge_base_weight_gap_sq
        (Finset.mem_erase.mp hn).1
    _ ≤ ccmActualHeadMatchedQuantileParabolicLorentzDebtConjugateGeometry K := by
      have houter :
          (∑ n ∈ (Finset.range (K + 1)).erase 0,
            ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry 0 n) ≤
          ∑ m ∈ Finset.range (K + 1),
            ∑ n ∈ (Finset.range (K + 1)).erase m,
              ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry m n := by
        exact Finset.single_le_sum
          (s := Finset.range (K + 1))
          (f := fun m => ∑ n ∈ (Finset.range (K + 1)).erase m,
            ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry m n)
          (fun m hm => Finset.sum_nonneg fun n hn =>
            ccmActualHeadMatchedQuantileLorentzDebtConjugateGeometry_nonneg m n)
          (Finset.mem_range.mpr (Nat.succ_pos K))
      simpa [ccmActualHeadMatchedQuantileParabolicLorentzDebtConjugateGeometry,
        ccmActualHeadMatchedQuantileLorentzEdgeSet, Finset.sum_sigma] using houter

/-- **Debt-Cauchy no-go.** The conjugate geometry forced by the exact literal displacement debt
diverges cofinally. Therefore a uniform Cauchy wall that treats that debt alone as its energy
cannot bound the actual signed source. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzDebtConjugateGeometry_tendsto_atTop :
    Tendsto ccmActualHeadMatchedQuantileParabolicLorentzDebtConjugateGeometry atTop atTop := by
  have hweightTwo : 0 < criticalMellinAtomWeight 2 :=
    criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow
  have hgap : 0 < ccmActualHeadMatchedQuantileLorentzBaseCentroidGap :=
    ccmActualHeadMatchedQuantileLorentzBaseCentroidGap_pos
  have hcoefficient : 0 < criticalMellinAtomWeight 2 / 2 *
      ccmActualHeadMatchedQuantileLorentzBaseCentroidGap ^ (2 : ℕ) := by positivity
  apply tendsto_atTop.2
  intro B
  filter_upwards [ccmActualHeadParabolicMass_tendsto_atTop.eventually_ge_atTop
      (B / (criticalMellinAtomWeight 2 / 2 *
        ccmActualHeadMatchedQuantileLorentzBaseCentroidGap ^ (2 : ℕ)) +
          criticalMellinAtomWeight 2)] with K hK
  have hlower := ccmActualHeadMatchedQuantileParabolicLorentzDebtConjugateGeometry_ge_baseOffDiagonalMass K
  rw [ccmActualHeadParabolicBaseOffDiagonalMass_eq_mass_sub_weightTwo] at hlower
  have hsub : B / (criticalMellinAtomWeight 2 / 2 *
      ccmActualHeadMatchedQuantileLorentzBaseCentroidGap ^ (2 : ℕ)) ≤
      ccmActualHeadParabolicMass K - criticalMellinAtomWeight 2 := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hsub hcoefficient.le
  have htarget : B ≤ (criticalMellinAtomWeight 2 / 2 *
      ccmActualHeadMatchedQuantileLorentzBaseCentroidGap ^ (2 : ℕ)) *
      (ccmActualHeadParabolicMass K - criticalMellinAtomWeight 2) := by
    calc
      B = (B / (criticalMellinAtomWeight 2 / 2 *
          ccmActualHeadMatchedQuantileLorentzBaseCentroidGap ^ (2 : ℕ))) *
          (criticalMellinAtomWeight 2 / 2 *
            ccmActualHeadMatchedQuantileLorentzBaseCentroidGap ^ (2 : ℕ)) := by
              field_simp [hcoefficient.ne']
      _ ≤ _ := by simpa [mul_comm] using hscaled
  exact htarget.trans hlower

end RHTower
