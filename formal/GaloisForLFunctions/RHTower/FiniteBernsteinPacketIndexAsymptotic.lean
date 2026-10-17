import GaloisForLFunctions.RHTower.BernsteinAffineRowIndexConcentration
import GaloisForLFunctions.HTGeometry.FinitePacketWeightedPairing

/-!
# Index-resolved limits of finite Bernstein packets

Binomial localization transports the strict mixed-mode gap through bounded test weights.
The surviving diagonal masses locate the packet on the coefficient-index interval.
-/

open Complex Filter Topology
open scoped BigOperators Real unitInterval ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem sum_fin_bernsteinAffineRow_pairing (u v C D : ℂ) (n : ℕ) :
    (∑ k : Fin (n + 1),
      (C * bernsteinAffineRowCoefficient u n k) *
        conj (D * bernsteinAffineRowCoefficient v n k)) =
      C * conj D * reflectedBernsteinCrossMoment u v n := by
  rw [reflectedBernsteinCrossMoment_eq_sum, Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    (C * bernsteinAffineRowCoefficient u n k) *
      conj (D * bernsteinAffineRowCoefficient v n k)) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_mul]
  ring

theorem tendsto_bernsteinAffineRow_weighted_mixed
    {u v : ℂ} {B gamma : ℝ} (C D : ℂ)
    (hB : 0 < B) (huamp : ‖u‖ + ‖1 - u‖ = B) (hvamp : ‖v‖ + ‖1 - v‖ = B)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma < B ^ 2)
    (hcross : ∀ n : ℕ, ‖reflectedBernsteinCrossMoment u v n‖ ≤ gamma ^ n)
    {g : I → ℝ} {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, |g x| ≤ M)
    (hg : ContinuousAt g (bernsteinAffineOccupation u)) :
    Tendsto (fun n : ℕ => Real.sqrt n / (B ^ 2) ^ n * ∑ k : Fin (n + 1),
      g (bernstein.z k) * ((C * bernsteinAffineRowCoefficient u n k) *
        conj (D * bernsteinAffineRowCoefficient v n k)).re) atTop (nhds 0) := by
  have hue := tendsto_bernsteinAffineRow_weighted_error hu0 hu1 hM hbound hg
  rw [huamp] at hue
  have hvm := tendsto_bernsteinAffineRow_weighted_energy hv0 hv1
    (g := fun _ => 1) (M := 1) (by norm_num) (by intro x; norm_num)
    continuous_const.continuousAt
  simp only [mul_one] at hvm
  rw [hvamp] at hvm
  have herr : Tendsto (fun n : ℕ => Real.sqrt n / (B ^ 2) ^ n *
      ∑ k : Fin (n + 1), ‖C * bernsteinAffineRowCoefficient u n k‖ ^ 2 *
        (g (bernstein.z k) - g (bernsteinAffineOccupation u)) ^ 2)
      atTop (nhds 0) := by
    convert hue.const_mul (‖C‖ ^ 2) using 1
    · ext n
      simp_rw [norm_mul, mul_pow, mul_assoc, ← Finset.mul_sum]
      ring
    · simp
  have hmass : Tendsto (fun n : ℕ => Real.sqrt n / (B ^ 2) ^ n *
      ∑ k : Fin (n + 1), ‖D * bernsteinAffineRowCoefficient v n k‖ ^ 2)
      atTop (nhds (‖D‖ ^ 2 * bernsteinAffineRowHalfOrderConstant v)) := by
    convert hvm.const_mul (‖D‖ ^ 2) using 1
    ext n
    simp_rw [norm_mul, mul_pow, ← Finset.mul_sum]
    ring
  have hp : Tendsto (fun n : ℕ => Real.sqrt n / (B ^ 2) ^ n *
      ∑ k : Fin (n + 1), ((C * bernsteinAffineRowCoefficient u n k) *
        conj (D * bernsteinAffineRowCoefficient v n k)).re) atTop (nhds 0) := by
    convert tendsto_sqrtNat_mul_re_crossMoment_div_pow_zero
      hB hgamma0 hgamma C D hcross using 1
    ext n
    have heq := congrArg Complex.re (sum_fin_bernsteinAffineRow_pairing u v C D n)
    rw [Complex.re_sum] at heq
    rw [heq]
    ring
  simpa only [mul_zero] using tendsto_finiteWeighted_real_pairing
    (fun n => (Finset.univ : Finset (Fin (n + 1))))
    (fun n => Real.sqrt n / (B ^ 2) ^ n)
    (fun n k => C * bernsteinAffineRowCoefficient u n k)
    (fun n k => D * bernsteinAffineRowCoefficient v n k)
    (fun _ k => g (bernstein.z k)) (fun n => by positivity) herr hmass hp

/-- Index-resolved square energy tested against a function on the unit interval. -/
def finiteBernsteinCoordinatePacketIndexEnergy
    (U : Finset ℂ) (C : ℂ → ℂ) (g : I → ℝ) (n : ℕ) : ℝ :=
  ∑ k : Fin (n + 1), g (bernstein.z k) * ‖finiteBernsteinCoordinatePacket U C n k‖ ^ 2

theorem finiteBernsteinCoordinatePacket_norm_sq (U : Finset ℂ) (C : ℂ → ℂ) (n k : ℕ) :
    ‖finiteBernsteinCoordinatePacket U C n k‖ ^ 2 =
      ∑ u ∈ U, ∑ v ∈ U, ((C u * bernsteinAffineRowCoefficient u n k) *
        conj (C v * bernsteinAffineRowCoefficient v n k)).re := by
  calc
    _ = (finiteBernsteinCoordinatePacket U C n k *
        conj (finiteBernsteinCoordinatePacket U C n k)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    _ = _ := by
      simp only [finiteBernsteinCoordinatePacket, map_sum, Finset.sum_mul,
        Finset.mul_sum, Complex.re_sum]
      rw [Finset.sum_comm]

theorem finiteBernsteinCoordinatePacketIndexEnergy_eq_sum_pairings
    (U : Finset ℂ) (C : ℂ → ℂ) (g : I → ℝ) (n : ℕ) :
    finiteBernsteinCoordinatePacketIndexEnergy U C g n =
      ∑ u ∈ U, ∑ v ∈ U, ∑ k : Fin (n + 1),
        g (bernstein.z k) * ((C u * bernsteinAffineRowCoefficient u n k) *
          conj (C v * bernsteinAffineRowCoefficient v n k)).re := by
  simp_rw [finiteBernsteinCoordinatePacketIndexEnergy,
    finiteBernsteinCoordinatePacket_norm_sq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]

/-- Weighted maximal-packet asymptotics. Conjugate rows may have the same occupation point;
the mixed gap still makes their interference vanish. -/
theorem tendsto_finiteBernsteinCoordinatePacketIndexEnergy
    (U : Finset ℂ) (C : ℂ → ℂ) {B : ℝ} (hB : 0 < B)
    (hamp : ∀ u ∈ U, ‖u‖ + ‖1 - u‖ = B)
    (hzero : ∀ u ∈ U, u ≠ 0) (hone : ∀ u ∈ U, u ≠ 1)
    (hcross : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ∃ gamma : ℝ,
      0 ≤ gamma ∧ gamma < B ^ 2 ∧
        ∀ n : ℕ, ‖reflectedBernsteinCrossMoment u v n‖ ≤ gamma ^ n)
    {g : I → ℝ} {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, |g x| ≤ M)
    (hg : ∀ u ∈ U, ContinuousAt g (bernsteinAffineOccupation u)) :
    Tendsto (fun n : ℕ => Real.sqrt n / (B ^ 2) ^ n *
      finiteBernsteinCoordinatePacketIndexEnergy U C g n) atTop
      (nhds (∑ u ∈ U, ‖C u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u *
        g (bernsteinAffineOccupation u))) := by
  classical
  have hpair : ∀ u ∈ U, ∀ v ∈ U, Tendsto (fun n : ℕ => Real.sqrt n / (B ^ 2) ^ n *
      ∑ k : Fin (n + 1), g (bernstein.z k) *
        ((C u * bernsteinAffineRowCoefficient u n k) *
          conj (C v * bernsteinAffineRowCoefficient v n k)).re) atTop
      (nhds (if u = v then ‖C u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u *
        g (bernsteinAffineOccupation u) else 0)) := by
    intro u hu v hv
    by_cases huv : u = v
    · subst v
      rw [if_pos rfl]
      have h := tendsto_bernsteinAffineRow_weighted_energy
        (hzero u hu) (hone u hu) hM hbound (hg u hu)
      rw [hamp u hu] at h
      convert h.const_mul (‖C u‖ ^ 2) using 1
      · ext n
        simp_rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
          norm_mul, mul_pow]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      · ring
    · rw [if_neg huv]
      obtain ⟨gamma, hgamma0, hgamma, hgap⟩ := hcross u hu v hv huv
      exact tendsto_bernsteinAffineRow_weighted_mixed (C u) (C v) hB
        (hamp u hu) (hamp v hv) (hzero u hu) (hone u hu) (hzero v hv) (hone v hv)
        hgamma0 hgamma hgap hM hbound (hg u hu)
  have hsum := tendsto_finsetSum U fun u hu => tendsto_finsetSum U fun v hv => hpair u hu v hv
  convert hsum using 1
  · ext n
    rw [finiteBernsteinCoordinatePacketIndexEnergy_eq_sum_pairings]
    simp_rw [Finset.mul_sum]
  · apply congrArg nhds
    apply Finset.sum_congr rfl
    intro u hu
    simp [hu]

end
end RHTower
