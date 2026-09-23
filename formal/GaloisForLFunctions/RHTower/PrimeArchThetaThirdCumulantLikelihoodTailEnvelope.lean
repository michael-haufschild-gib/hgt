import GaloisForLFunctions.RHTower.XiCenteredOrderNineteenSourceBudgetClosure
import GaloisForLFunctions.RHTower.PrimeArchThetaReflectedBudgetTailTransfer

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-!
# Likelihood-tail envelope for the theta third cumulant

The first theta atom dominates every normalized even moment.  Conversely, the
exact first-atom tail factor `3005 / 2997` supplies the lower bounds needed to
retain the favorable sign of the mixed term in the third cumulant.  Combining
these two likelihood-order estimates gives an unconditional reduction of the
full normalized prime-archimedean sixth reciprocal trace to one first-atom
scalar inequality.
-/

/-- Even moment of the first theta atom, normalized by its mass. -/
def thetaCuspFirstAtomNormalizedEvenMoment (j : ℕ) : ℝ :=
  thetaCuspAtomRawEvenMoment j 1 / thetaCuspAtomRawEvenMoment 0 1

/-- Likelihood ordering: the normalized full theta moment is no larger than
the normalized first-atom moment. -/
theorem thetaCuspNormalizedEvenMoment_le_firstAtomNormalizedEvenMoment (j : ℕ) :
    thetaCuspNormalizedEvenMoment j ≤ thetaCuspFirstAtomNormalizedEvenMoment j := by
  have ha0 : 0 < thetaCuspAtomRawEvenMoment 0 1 :=
    thetaCuspAtomRawEvenMoment_pos_of_nat_pos 0 (by norm_num)
  have hm0 : 0 < thetaCuspRawEvenMoment 0 := thetaCuspRawEvenMoment_zero_pos
  have hcross := thetaCuspRawFirst_rawEvenMoment_cross_le 0 j
  simp only [Nat.zero_add] at hcross
  rw [thetaCuspNormalizedEvenMoment, thetaCuspFirstAtomNormalizedEvenMoment]
  exact (div_le_div_iff₀ hm0 ha0).2 hcross

/-- The exact tail factor also gives the reverse normalized comparison, at
loss `3005 / 2997`. -/
theorem thetaCuspFirstAtomNormalizedEvenMoment_div_factor_le_normalized (j : ℕ) :
    thetaCuspFirstAtomNormalizedEvenMoment j / (3005 / 2997 : ℝ) ≤
      thetaCuspNormalizedEvenMoment j := by
  let c : ℝ := 3005 / 2997
  let a0 : ℝ := thetaCuspAtomRawEvenMoment 0 1
  let aj : ℝ := thetaCuspAtomRawEvenMoment j 1
  let m0 : ℝ := thetaCuspRawEvenMoment 0
  let mj : ℝ := thetaCuspRawEvenMoment j
  have hc : 0 < c := by dsimp only [c]; norm_num
  have ha0 : 0 < a0 := by
    simpa only [a0] using thetaCuspAtomRawEvenMoment_pos_of_nat_pos 0 (by norm_num)
  have hm0 : 0 < m0 := by simpa only [m0] using thetaCuspRawEvenMoment_zero_pos
  have haj : 0 ≤ aj := by
    simpa only [aj] using thetaCuspAtomRawEvenMoment_nonneg j 1
  have hajm : aj ≤ mj := by
    simpa only [aj, mj] using thetaCuspAtomRawEvenMoment_one_le_raw j
  have hm0c : m0 ≤ c * a0 := by
    simpa only [m0, c, a0] using thetaCuspRawEvenMoment_le_first_atom_factor 0
  rw [thetaCuspFirstAtomNormalizedEvenMoment, thetaCuspNormalizedEvenMoment]
  dsimp only [c, a0, aj, m0, mj] at *
  rw [div_div]
  apply (div_le_div_iff₀ (mul_pos ha0 hc) hm0).2
  calc
    aj * m0 ≤ aj * (c * a0) := mul_le_mul_of_nonneg_left hm0c haj
    _ = (a0 * c) * aj := by ring
    _ ≤ (a0 * c) * mj :=
      mul_le_mul_of_nonneg_left hajm (mul_nonneg ha0.le hc.le)
    _ = mj * (a0 * c) := by ring

/-- Unconditional first-atom envelope for the full theta third cumulant, hence
for the normalized prime-archimedean sixth reciprocal trace. -/
theorem normalizedPrimeArchMoment_two_le_firstAtomTailEnvelope :
    normalizedPrimeArchMoment 2 ≤
      thetaCuspFirstAtomNormalizedEvenMoment 3 / 120 -
        thetaCuspFirstAtomNormalizedEvenMoment 1 *
            thetaCuspFirstAtomNormalizedEvenMoment 2 /
          (8 * (3005 / 2997 : ℝ) ^ (2 : ℕ)) +
        thetaCuspFirstAtomNormalizedEvenMoment 1 ^ (3 : ℕ) / 4 := by
  let c : ℝ := 3005 / 2997
  let u1 : ℝ := thetaCuspNormalizedEvenMoment 1
  let u2 : ℝ := thetaCuspNormalizedEvenMoment 2
  let u3 : ℝ := thetaCuspNormalizedEvenMoment 3
  let a1 : ℝ := thetaCuspFirstAtomNormalizedEvenMoment 1
  let a2 : ℝ := thetaCuspFirstAtomNormalizedEvenMoment 2
  let a3 : ℝ := thetaCuspFirstAtomNormalizedEvenMoment 3
  have hc : 0 < c := by dsimp only [c]; norm_num
  have hu1 : 0 ≤ u1 := by
    dsimp only [u1, thetaCuspNormalizedEvenMoment]
    exact div_nonneg (thetaCuspRawEvenMoment_nonneg 1)
      thetaCuspRawEvenMoment_zero_pos.le
  have hu2 : 0 ≤ u2 := by
    dsimp only [u2, thetaCuspNormalizedEvenMoment]
    exact div_nonneg (thetaCuspRawEvenMoment_nonneg 2)
      thetaCuspRawEvenMoment_zero_pos.le
  have ha1 : 0 ≤ a1 := by
    dsimp only [a1, thetaCuspFirstAtomNormalizedEvenMoment]
    exact div_nonneg (thetaCuspAtomRawEvenMoment_nonneg 1 1)
      (thetaCuspAtomRawEvenMoment_pos_of_nat_pos 0 (by norm_num)).le
  have ha2 : 0 ≤ a2 := by
    dsimp only [a2, thetaCuspFirstAtomNormalizedEvenMoment]
    exact div_nonneg (thetaCuspAtomRawEvenMoment_nonneg 2 1)
      (thetaCuspAtomRawEvenMoment_pos_of_nat_pos 0 (by norm_num)).le
  have h1lo : a1 / c ≤ u1 := by
    simpa only [a1, c, u1] using
      thetaCuspFirstAtomNormalizedEvenMoment_div_factor_le_normalized 1
  have h2lo : a2 / c ≤ u2 := by
    simpa only [a2, c, u2] using
      thetaCuspFirstAtomNormalizedEvenMoment_div_factor_le_normalized 2
  have h1hi : u1 ≤ a1 := by
    simpa only [u1, a1] using
      thetaCuspNormalizedEvenMoment_le_firstAtomNormalizedEvenMoment 1
  have h3hi : u3 ≤ a3 := by
    simpa only [u3, a3] using
      thetaCuspNormalizedEvenMoment_le_firstAtomNormalizedEvenMoment 3
  have hprod : a1 * a2 / c ^ (2 : ℕ) ≤ u1 * u2 := by
    have hmul := mul_le_mul h1lo h2lo
      (div_nonneg ha2 hc.le) hu1
    calc
      a1 * a2 / c ^ (2 : ℕ) = (a1 / c) * (a2 / c) := by
        field_simp [hc.ne']
      _ ≤ u1 * u2 := hmul
  have hcub : u1 ^ (3 : ℕ) ≤ a1 ^ (3 : ℕ) := by gcongr
  rw [normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment]
  have hthird : u3 / 120 ≤ a3 / 120 := by
    exact div_le_div_of_nonneg_right h3hi (by norm_num)
  have hnegative : -(u1 * u2 / 8) ≤ -(a1 * a2 / (8 * c ^ (2 : ℕ))) := by
    rw [neg_le_neg_iff]
    calc
      a1 * a2 / (8 * c ^ (2 : ℕ)) = (a1 * a2 / c ^ (2 : ℕ)) / 8 := by ring
      _ ≤ (u1 * u2) / 8 := div_le_div_of_nonneg_right hprod (by norm_num)
  have hcubic : u1 ^ (3 : ℕ) / 4 ≤ a1 ^ (3 : ℕ) / 4 := by
    exact div_le_div_of_nonneg_right hcub (by norm_num)
  dsimp only [u1, u2, u3, a1, a2, a3, c] at *
  linarith

end

end RHTower
