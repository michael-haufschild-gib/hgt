import GaloisForLFunctions.RHTower.BernsteinAffineRowDiagonalAsymptotic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Finite affine Bernstein-coordinate packet asymptotics

A finite packet of equal-amplitude affine Bernstein coordinates has a sharp half-order energy
limit.  Polarized Parseval separates its positive diagonal contributions from the mixed modes;
any strict mixed circle gap makes the latter exponentially smaller.
-/

open Complex Filter Topology
open scoped BigOperators Real ComplexConjugate

namespace RHTower

noncomputable section

/-- A finite packet assembled from distinct affine Bernstein coordinates. -/
def finiteBernsteinCoordinatePacket
    (U : Finset ℂ) (C : ℂ → ℂ) (n k : ℕ) : ℂ :=
  ∑ u ∈ U, C u * bernsteinAffineRowCoefficient u n k

/-- Squared Euclidean energy of a finite coordinate packet. -/
def finiteBernsteinCoordinatePacketEnergy
    (U : Finset ℂ) (C : ℂ → ℂ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ‖finiteBernsteinCoordinatePacket U C n k‖ ^ 2

/-- Exact polarized expansion of the finite packet energy. -/
theorem ofReal_finiteBernsteinCoordinatePacketEnergy_eq_sum_crossMoment
    (U : Finset ℂ) (C : ℂ → ℂ) (n : ℕ) :
    (finiteBernsteinCoordinatePacketEnergy U C n : ℂ) =
      ∑ u ∈ U, ∑ v ∈ U,
        C u * conj (C v) * reflectedBernsteinCrossMoment u v n := by
  rw [finiteBernsteinCoordinatePacketEnergy]
  push_cast
  rw [show (∑ k ∈ Finset.range (n + 1),
      ((‖finiteBernsteinCoordinatePacket U C n k‖ : ℂ) ^ 2)) =
    ∑ k ∈ Finset.range (n + 1),
      finiteBernsteinCoordinatePacket U C n k *
        conj (finiteBernsteinCoordinatePacket U C n k) by
      apply Finset.sum_congr rfl
      intro k _
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl]
  simp_rw [finiteBernsteinCoordinatePacket, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [reflectedBernsteinCrossMoment_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring_nf

/-- Real-part form of the exact polarized packet expansion. -/
theorem finiteBernsteinCoordinatePacketEnergy_eq_sum_re_crossMoment
    (U : Finset ℂ) (C : ℂ → ℂ) (n : ℕ) :
    finiteBernsteinCoordinatePacketEnergy U C n =
      ∑ u ∈ U, ∑ v ∈ U,
        (C u * conj (C v) * reflectedBernsteinCrossMoment u v n).re := by
  have h := congrArg Complex.re
    (ofReal_finiteBernsteinCoordinatePacketEnergy_eq_sum_crossMoment U C n)
  calc
    finiteBernsteinCoordinatePacketEnergy U C n =
        (∑ u ∈ U, ∑ v ∈ U,
          C u * conj (C v) * reflectedBernsteinCrossMoment u v n).re := by
      simpa only [Complex.ofReal_re] using h
    _ = ∑ u ∈ U, ∑ v ∈ U,
        (C u * conj (C v) * reflectedBernsteinCrossMoment u v n).re := by
      rw [← Complex.reCLM_apply, map_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro v _
      rfl

/-- Self cross moments are the real affine-row energy. -/
theorem reflectedBernsteinCrossMoment_self (u : ℂ) (n : ℕ) :
    reflectedBernsteinCrossMoment u u n = (bernsteinAffineRowEnergy u n : ℂ) := by
  rw [reflectedBernsteinCrossMoment_eq_sum, bernsteinAffineRowEnergy]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- A square-root factor cannot defeat a strict geometric gap. -/
theorem tendsto_sqrtNat_mul_const_pow_of_lt_one
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => Real.sqrt n * q ^ n) atTop (nhds 0) := by
  have hself := tendsto_self_mul_const_pow_of_lt_one hq0 hq1
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hupper : Tendsto (fun n : ℕ => (n + 1 : ℝ) * q ^ n) atTop (nhds 0) := by
    convert hself.add hpow using 1
    · funext n
      ring_nf
    · ring_nf
  apply squeeze_zero
  · exact fun n => mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hq0 n)
  · intro n
    have hsqrt : Real.sqrt (n : ℝ) ≤ n + 1 := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hsq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg (n : ℝ)
        nlinarith
    exact mul_le_mul_of_nonneg_right hsqrt (pow_nonneg hq0 n)
  · exact hupper

/-- Cross moments below the squared main amplitude vanish after half-order normalization. -/
theorem tendsto_sqrtNat_mul_re_crossMoment_div_pow_zero
    {u v : ℂ} {B gamma : ℝ} (hB : 0 < B)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma < B ^ 2)
    (C D : ℂ)
    (hcross : ∀ n : ℕ, ‖reflectedBernsteinCrossMoment u v n‖ ≤ gamma ^ n) :
    Tendsto
      (fun n : ℕ => Real.sqrt n *
        (C * conj D * reflectedBernsteinCrossMoment u v n).re /
          (B ^ 2) ^ n)
      atTop (nhds 0) := by
  let q : ℝ := gamma / B ^ 2
  have hB2 : 0 < B ^ 2 := sq_pos_of_pos hB
  have hq0 : 0 ≤ q := div_nonneg hgamma0 hB2.le
  have hq1 : q < 1 := (div_lt_one hB2).2 hgamma
  have hbase := (tendsto_sqrtNat_mul_const_pow_of_lt_one hq0 hq1).const_mul
    (‖C‖ * ‖D‖)
  apply squeeze_zero_norm'
    (a := fun n : ℕ => (‖C‖ * ‖D‖) * (Real.sqrt n * q ^ n))
  · filter_upwards with n
    rw [Real.norm_eq_abs]
    have hden : 0 < (B ^ 2) ^ n := pow_pos hB2 n
    rw [abs_div, abs_of_pos hden]
    calc
      |Real.sqrt n * (C * conj D * reflectedBernsteinCrossMoment u v n).re| /
            (B ^ 2) ^ n ≤
          (Real.sqrt n *
            ‖C * conj D * reflectedBernsteinCrossMoment u v n‖) /
              (B ^ 2) ^ n := by
        gcongr
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_mul_of_nonneg_left (abs_re_le_norm _) (Real.sqrt_nonneg _)
      _ ≤ (Real.sqrt n * (‖C‖ * ‖D‖ * gamma ^ n)) / (B ^ 2) ^ n := by
        gcongr
        rw [norm_mul, norm_mul, norm_conj]
        exact mul_le_mul_of_nonneg_left (hcross n)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖C‖ * ‖D‖) * (Real.sqrt n * q ^ n) := by
        dsimp only [q]
        rw [div_pow]
        ring_nf
  · simpa only [mul_zero] using hbase

/-- The half-order constant of one nondegenerate affine Bernstein coordinate. -/
def bernsteinAffineRowHalfOrderConstant (u : ℂ) : ℝ :=
  (1 / Real.sqrt Real.pi) *
    ((1 - (‖u‖ - ‖1 - u‖) ^ 2 / (‖u‖ + ‖1 - u‖) ^ 2) ^
      (-1 / 2 : ℝ))

/-- Every nondegenerate affine coordinate has a strictly positive half-order constant. -/
theorem bernsteinAffineRowHalfOrderConstant_pos
    {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    0 < bernsteinAffineRowHalfOrderConstant u := by
  let a : ℝ := ‖u‖
  let b : ℝ := ‖1 - u‖
  have ha : 0 < a := norm_pos_iff.mpr hu0
  have hb : 0 < b := norm_pos_iff.mpr (sub_ne_zero.mpr hu1.symm)
  have hsum : 0 < (a + b) ^ 2 := sq_pos_of_pos (add_pos ha hb)
  have hdiff : (a - b) ^ 2 < (a + b) ^ 2 := by nlinarith
  have hinterior : 0 < 1 - (a - b) ^ 2 / (a + b) ^ 2 := by
    exact sub_pos.mpr ((div_lt_one hsum).2 hdiff)
  dsimp only [bernsteinAffineRowHalfOrderConstant, a, b]
  exact mul_pos (one_div_pos.mpr (Real.sqrt_pos.2 Real.pi_pos))
    (Real.rpow_pos_of_pos hinterior _)

/-- **Finite-packet half-order theorem.**  Equal-amplitude coordinates contribute only their
positive diagonal half-order constants; every strictly gapped mixed moment is exponentially
smaller. -/
theorem tendsto_sqrtNat_mul_finiteBernsteinCoordinatePacketEnergy_div_pow
    (U : Finset ℂ) (C : ℂ → ℂ) {B : ℝ} (hB : 0 < B)
    (hamp : ∀ u ∈ U, ‖u‖ + ‖1 - u‖ = B)
    (hu0 : ∀ u ∈ U, u ≠ 0) (hu1 : ∀ u ∈ U, u ≠ 1)
    (hmixed : ∀ u ∈ U, ∀ v ∈ U, u ≠ v →
      ∃ gamma : ℝ, 0 ≤ gamma ∧ gamma < B ^ 2 ∧
        ∀ n : ℕ, ‖reflectedBernsteinCrossMoment u v n‖ ≤ gamma ^ n) :
    Tendsto
      (fun n : ℕ => Real.sqrt n * finiteBernsteinCoordinatePacketEnergy U C n /
        (B ^ 2) ^ n)
      atTop
      (nhds (∑ u ∈ U, ‖C u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u)) := by
  have hterm (u : ℂ) (hu : u ∈ U) (v : ℂ) (hv : v ∈ U) :
      Tendsto
        (fun n : ℕ => Real.sqrt n *
          (C u * conj (C v) * reflectedBernsteinCrossMoment u v n).re /
            (B ^ 2) ^ n)
        atTop
        (nhds (if u = v then
          ‖C u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u else 0)) := by
    by_cases huv : u = v
    · subst v
      have hdiag := tendsto_sqrtNat_mul_bernsteinAffineRowEnergy_div_pow
        (hu0 u hu) (hu1 u hu)
      have hdiagB : Tendsto
          (fun n : ℕ => Real.sqrt n * bernsteinAffineRowEnergy u n / (B ^ 2) ^ n)
          atTop (nhds (bernsteinAffineRowHalfOrderConstant u)) := by
        simpa only [hamp u hu, bernsteinAffineRowHalfOrderConstant] using hdiag
      have hscaled := hdiagB.const_mul (‖C u‖ ^ 2)
      convert hscaled using 1
      · funext n
        rw [reflectedBernsteinCrossMoment_self, Complex.mul_conj,
          Complex.normSq_eq_norm_sq, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
        change Real.sqrt n * (‖C u‖ ^ 2 * bernsteinAffineRowEnergy u n) /
            (B ^ 2) ^ n =
          ‖C u‖ ^ 2 *
            (Real.sqrt n * bernsteinAffineRowEnergy u n / (B ^ 2) ^ n)
        ring_nf
      · simp
    · obtain ⟨gamma, hgamma0, hgamma, hcross⟩ := hmixed u hu v hv huv
      simpa only [if_neg huv] using
        tendsto_sqrtNat_mul_re_crossMoment_div_pow_zero
          hB hgamma0 hgamma (C u) (C v) hcross
  have hdouble : Tendsto
      (fun n : ℕ => ∑ u ∈ U, ∑ v ∈ U,
        Real.sqrt n *
          (C u * conj (C v) * reflectedBernsteinCrossMoment u v n).re /
            (B ^ 2) ^ n)
      atTop
      (nhds (∑ u ∈ U, ∑ v ∈ U,
        if u = v then ‖C u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u else 0)) := by
    exact tendsto_finsetSum U fun u hu =>
      tendsto_finsetSum U fun v hv => hterm u hu v hv
  have hlimit :
      (∑ u ∈ U, ∑ v ∈ U,
        if u = v then ‖C u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u else 0) =
        ∑ u ∈ U, ‖C u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.sum_eq_single u]
    · rw [if_pos rfl]
    · intro v hv hvu
      rw [if_neg (fun h => hvu h.symm)]
    · exact fun h => (h hu).elim
  rw [hlimit] at hdouble
  apply hdouble.congr'
  filter_upwards with n
  rw [finiteBernsteinCoordinatePacketEnergy_eq_sum_re_crossMoment,
    Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum, Finset.sum_div]

end

end RHTower
