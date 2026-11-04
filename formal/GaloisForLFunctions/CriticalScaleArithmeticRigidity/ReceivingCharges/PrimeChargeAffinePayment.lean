import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeCompleteEnergy

/-!
# The affine and shell terms vanish separately on coherent charge

The ordinary and harmonic incidence moments make both nonnegative terms
vanish before physical normalization. The surviving dilation energy is
therefore not a cancellation of two large affine and shell energies.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity

/-- The literal shell diagonal of the neutral coherent prime packet. -/
def harmonicPrimeChargeShell (φ : ℝ → ℝ) (c : ℝ) (Q N : ℕ) (t : ℝ) : ℝ :=
  ∑ n : PrimeHorizonIndex N, shellDegree φ c N n *
    normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t) n ^ 2

private theorem coherent_shell_moment_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {Q N : ℕ} (hQ : 1 ≤ Q) (hN : 1 ≤ N)
    {c : ℝ} (hc : 0 < c) (hcN : c ≤ N) (t : ℝ) :
    harmonicPrimeChargeShell φ c Q N t ≤
      (2 * (Real.log 4 + 4) * Real.exp (5 / 2) + 2 * Real.exp (3 / 2)) *
        c * (Real.log N + 1) * (t / primePoleScale Q) ^ 2 *
          (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
            2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) := by
  let V := (t / primePoleScale Q) ^ 2 *
    (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
      2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ))
  let F := normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hH : harmonicMass N ≤ Real.log N + 1 := by
    have h := harmonic_le_one_add_log N
    have he : (harmonic N : ℝ) = harmonicMass N := by
      simpa only [harmonicMass, one_div] using
        _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum N
    rw [he] at h
    linarith only [h]
  have hHF : (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) ≤ (Real.log N + 1) * V := by
    refine (harmonicPrimeCharge_harmonic_square_le hQ hN t).trans ?_
    convert mul_le_mul_of_nonneg_right hH hV using 1
    dsimp only [V]
    ring
  have hOF : (∑ n ∈ Icc 1 N, F n ^ 2) ≤ (N : ℝ) * V := by
    convert harmonicPrimeCharge_ordinary_square_le hQ hN t using 1
    dsimp only [V]
    ring
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine (shell_packet_moments_le hφ hsupp hM hc hcN F).trans ?_
  have h := add_le_add
    (mul_le_mul_of_nonneg_left hHF (by positivity :
      0 ≤ 2 * (Real.log 4 + 4) * Real.exp (5 / 2) * c))
    (mul_le_mul_of_nonneg_left hOF (by positivity :
      0 ≤ 2 * Real.exp (3 / 2) * c * (Real.log N + 1) / N))
  refine h.trans_eq ?_
  dsimp only [V]
  field_simp [hN0]

/-- The shell diagonal vanishes on every fixed polynomial charge family. -/
theorem tendsto_harmonicPrimeCharge_shell {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ => harmonicPrimeChargeShell φ
      (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ a) (X ^ d) t) atTop (𝓝 0) := by
  have hN : Tendsto (fun X : ℕ => X ^ d) atTop atTop :=
    tendsto_pow_atTop (ha.trans_le had).ne'
  have hlim := (tendsto_primeChargePolynomialMoment_cost ha had t
    (r := 1 / 8) (by norm_num)).const_mul
      ((2 * (Real.log 4 + 4) * Real.exp (5 / 2) + 2 * Real.exp (3 / 2)) * (2 * K))
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2,
    hN.eventually (eventually_primeCharge_criticalOverlap_facts hK)] with X hX hc
  have hQa : 1 ≤ X ^ a := Nat.one_le_pow a X (by omega)
  have hNd : 1 ≤ X ^ d := Nat.one_le_pow d X (by omega)
  have hc0 := zero_lt_one.trans_le hc.1
  have hcN : 2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ) ≤ (X ^ d : ℕ) := by
    apply (div_le_one (by exact_mod_cast (show 0 < X ^ d by omega))).mp
    linarith only [hc.2]
  have hnonneg : 0 ≤ harmonicPrimeChargeShell φ
      (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ a) (X ^ d) t := by
    exact sum_nonneg fun n _ => mul_nonneg (shellDegree_nonneg hφ0 hsupp hM hc0 n) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact (coherent_shell_moment_bound hφ hsupp hM hQa hNd hc0 hcN t).trans_eq (by ring)

/-- The affine successor energy itself vanishes, so it cannot pay a nonzero limiting charge. -/
theorem tendsto_harmonicPrimeCharge_affine {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ => affineDirichlet φ
      (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
      (normalizedConductorPacket (X ^ a)
        (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t))) atTop (𝓝 0) := by
  have hlim := (tendsto_harmonicPrimeCharge_shell hφ hφ0 hsupp hM hK ha had t).const_mul 4
  simp only [mul_zero] at hlim
  have hN : Tendsto (fun X : ℕ => X ^ d) atTop atTop :=
    tendsto_pow_atTop (ha.trans_le had).ne'
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hN.eventually (eventually_primeCharge_criticalOverlap_facts hK)] with X hc
  have hc0 := zero_lt_one.trans_le hc.1
  rw [Real.norm_eq_abs, abs_of_nonneg (affineDirichlet_nonneg hφ0 hsupp hM hc0 _ _)]
  exact affineDirichlet_le_four_shell hφ0 hsupp hM hc0 _ _

#print axioms tendsto_harmonicPrimeCharge_shell
#print axioms tendsto_harmonicPrimeCharge_affine

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
