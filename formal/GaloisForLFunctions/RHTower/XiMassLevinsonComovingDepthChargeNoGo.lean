import GaloisForLFunctions.RHTower.XiMassTruePrimeCoboundaryBridge
import GaloisForLFunctions.RHTower.XiMassLevinsonRoughTailHorizon

open Complex Finset

namespace RHTower

noncomputable section

/-- Finite co-moving packet of true-prime cones, with one legal depth per channel. -/
def xiMassCriticalTruePrimeDepthPacket
    {ι : Type*} [Fintype ι] (alpha : ι → ℂ) (depth : ι → ℝ)
    (a sigma u : ℝ) : ℂ :=
  ∑ i, alpha i * xiMassCriticalTruePrimeCone a sigma (depth i) u

/-- Uniform line boundedness on the forward ray. -/
def XiMassCriticalTruePrimeDepthPacketLineBound
    {ι : Type*} [Fintype ι] (alpha : ι → ℂ) (depth : ι → ℝ)
    (a sigma : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassCriticalTruePrimeDepthPacket alpha depth a sigma u‖ ≤ C

/-- Exact charge decomposition relative to any reference cone. -/
theorem xiMassCriticalTruePrimeDepthPacket_eq_charge_mul_add_difference
    {ι : Type*} [Fintype ι] (alpha : ι → ℂ) (depth : ι → ℝ)
    (a sigma d₀ u : ℝ) :
    xiMassCriticalTruePrimeDepthPacket alpha depth a sigma u =
      (∑ i, alpha i) * xiMassCriticalTruePrimeCone a sigma d₀ u +
        ∑ i, alpha i *
          (xiMassCriticalTruePrimeCone a sigma (depth i) u -
            xiMassCriticalTruePrimeCone a sigma d₀ u) := by
  rw [xiMassCriticalTruePrimeDepthPacket]
  calc
    ∑ i, alpha i * xiMassCriticalTruePrimeCone a sigma (depth i) u =
        ∑ i, (alpha i * xiMassCriticalTruePrimeCone a sigma d₀ u +
          alpha i * (xiMassCriticalTruePrimeCone a sigma (depth i) u -
            xiMassCriticalTruePrimeCone a sigma d₀ u)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      exact (Finset.sum_mul Finset.univ alpha
        (xiMassCriticalTruePrimeCone a sigma d₀ u)).symm

/-- A finite zero-charge packet is unconditionally line bounded. -/
theorem xiMassCriticalTruePrimeDepthPacketLineBound_of_charge_zero
    {ι : Type*} [Fintype ι] {alpha : ι → ℂ} {depth : ι → ℝ}
    {a sigma : ℝ}
    (hhalf : ∀ i, 1 / 2 < depth i) (ha : ∀ i, depth i < a)
    (hsigma : 0 < sigma) (hcharge : ∑ i, alpha i = 0) :
    XiMassCriticalTruePrimeDepthPacketLineBound alpha depth a sigma := by
  classical
  have hbounds : ∀ i : ι, ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalTruePrimeCone a sigma (depth i) u -
        xiMassCriticalOutgoingFlux a sigma u‖ ≤ B := fun i =>
    exists_norm_truePrimeCone_sub_outgoingFlux_bound (hhalf i) (ha i) hsigma
  choose B hB using hbounds
  refine ⟨∑ i, ‖alpha i‖ * B i, fun u hu => ?_⟩
  have hrewrite : xiMassCriticalTruePrimeDepthPacket alpha depth a sigma u =
      ∑ i, alpha i *
        (xiMassCriticalTruePrimeCone a sigma (depth i) u -
          xiMassCriticalOutgoingFlux a sigma u) := by
    rw [xiMassCriticalTruePrimeDepthPacket]
    calc
      ∑ i, alpha i * xiMassCriticalTruePrimeCone a sigma (depth i) u =
          ∑ i, (alpha i *
            (xiMassCriticalTruePrimeCone a sigma (depth i) u -
              xiMassCriticalOutgoingFlux a sigma u) +
            alpha i * xiMassCriticalOutgoingFlux a sigma u) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, alpha i *
            (xiMassCriticalTruePrimeCone a sigma (depth i) u -
              xiMassCriticalOutgoingFlux a sigma u)) +
            (∑ i, alpha i) * xiMassCriticalOutgoingFlux a sigma u := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = _ := by rw [hcharge, zero_mul, add_zero]
  rw [hrewrite]
  calc
    ‖∑ i, alpha i *
        (xiMassCriticalTruePrimeCone a sigma (depth i) u -
          xiMassCriticalOutgoingFlux a sigma u)‖
        ≤ ∑ i, ‖alpha i *
          (xiMassCriticalTruePrimeCone a sigma (depth i) u -
            xiMassCriticalOutgoingFlux a sigma u)‖ := norm_sum_le _ _
    _ = ∑ i, ‖alpha i‖ *
          ‖xiMassCriticalTruePrimeCone a sigma (depth i) u -
            xiMassCriticalOutgoingFlux a sigma u‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul]
    _ ≤ ∑ i, ‖alpha i‖ * B i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hB i u hu) (norm_nonneg _)

/-- Relative to any legal reference depth, a finite packet differs from its total charge times
the reference cone by one uniformly bounded family. -/
theorem exists_norm_xiMassCriticalTruePrimeDepthPacket_sub_charge_mul_bound
    {ι : Type*} [Fintype ι] {alpha : ι → ℂ} {depth : ι → ℝ}
    {a sigma d₀ : ℝ}
    (hhalf : ∀ i, 1 / 2 < depth i) (ha : ∀ i, depth i < a)
    (hd₀half : 1 / 2 < d₀) (hd₀a : d₀ < a) (hsigma : 0 < sigma) :
    ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalTruePrimeDepthPacket alpha depth a sigma u -
        (∑ i, alpha i) * xiMassCriticalTruePrimeCone a sigma d₀ u‖ ≤ B := by
  classical
  have hbounds : ∀ i : ι, ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalTruePrimeCone a sigma (depth i) u -
        xiMassCriticalTruePrimeCone a sigma d₀ u‖ ≤ B := fun i =>
    exists_norm_truePrimeCone_depth_difference_bound
      (hhalf i) (ha i) hd₀half hd₀a hsigma
  choose B hB using hbounds
  refine ⟨∑ i, ‖alpha i‖ * B i, fun u hu => ?_⟩
  have hrewrite :
      xiMassCriticalTruePrimeDepthPacket alpha depth a sigma u -
          (∑ i, alpha i) * xiMassCriticalTruePrimeCone a sigma d₀ u =
        ∑ i, alpha i *
          (xiMassCriticalTruePrimeCone a sigma (depth i) u -
            xiMassCriticalTruePrimeCone a sigma d₀ u) := by
    rw [xiMassCriticalTruePrimeDepthPacket_eq_charge_mul_add_difference]
    ring
  rw [hrewrite]
  calc
    ‖∑ i, alpha i *
        (xiMassCriticalTruePrimeCone a sigma (depth i) u -
          xiMassCriticalTruePrimeCone a sigma d₀ u)‖
        ≤ ∑ i, ‖alpha i *
          (xiMassCriticalTruePrimeCone a sigma (depth i) u -
            xiMassCriticalTruePrimeCone a sigma d₀ u)‖ := norm_sum_le _ _
    _ = ∑ i, ‖alpha i‖ *
          ‖xiMassCriticalTruePrimeCone a sigma (depth i) u -
            xiMassCriticalTruePrimeCone a sigma d₀ u‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul]
    _ ≤ ∑ i, ‖alpha i‖ * B i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hB i u hu) (norm_nonneg _)

/-- Nonzero total charge is the complete invariant: the packet is line bounded exactly when any
one legal reference cone is line bounded. -/
theorem xiMassCriticalTruePrimeDepthPacketLineBound_iff_truePrimeCone
    {ι : Type*} [Fintype ι] {alpha : ι → ℂ} {depth : ι → ℝ}
    {a sigma d₀ : ℝ}
    (hhalf : ∀ i, 1 / 2 < depth i) (ha : ∀ i, depth i < a)
    (hd₀half : 1 / 2 < d₀) (hd₀a : d₀ < a) (hsigma : 0 < sigma)
    (hcharge : (∑ i, alpha i) ≠ 0) :
    XiMassCriticalTruePrimeDepthPacketLineBound alpha depth a sigma ↔
      XiMassCriticalTruePrimeConeLineBound a sigma d₀ := by
  let z : ℂ := ∑ i, alpha i
  obtain ⟨B, hB⟩ :=
    exists_norm_xiMassCriticalTruePrimeDepthPacket_sub_charge_mul_bound
      hhalf ha hd₀half hd₀a hsigma
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨‖z⁻¹‖ * (C + B), fun u hu => ?_⟩
    let P : ℂ := xiMassCriticalTruePrimeCone a sigma d₀ u
    let Q : ℂ := xiMassCriticalTruePrimeDepthPacket alpha depth a sigma u
    let R : ℂ := Q - z * P
    have hR : ‖R‖ ≤ B := by
      simpa only [R, Q, P, z] using hB u hu
    have hz : z ≠ 0 := by simpa only [z] using hcharge
    have hsolve : P = z⁻¹ * (Q - R) := by
      dsimp only [R]
      have hzi : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
      calc
        P = (z⁻¹ * z) * P := by rw [hzi, one_mul]
        _ = z⁻¹ * (Q - (Q - z * P)) := by ring
    change ‖P‖ ≤ _
    rw [hsolve, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (norm_sub_le Q R).trans (add_le_add (hC u hu) hR)
  · rintro ⟨C, hC⟩
    refine ⟨‖z‖ * C + B, fun u hu => ?_⟩
    let P : ℂ := xiMassCriticalTruePrimeCone a sigma d₀ u
    let Q : ℂ := xiMassCriticalTruePrimeDepthPacket alpha depth a sigma u
    let R : ℂ := Q - z * P
    have hR : ‖R‖ ≤ B := by
      simpa only [R, Q, P, z] using hB u hu
    have hsolve : Q = z * P + R := by dsimp only [R]; ring
    change ‖Q‖ ≤ _
    rw [hsolve]
    exact (norm_add_le _ _).trans
      (add_le_add (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC u hu) (norm_nonneg _)) hR)

/-- Every finite legal depth packet with nonzero charge is itself an exact RH criterion. -/
theorem riemannHypothesis_iff_xiMassCriticalTruePrimeDepthPacketLineBound
    {ι : Type*} [Fintype ι] {alpha : ι → ℂ} {depth : ι → ℝ}
    {a c sigma d₀ : ℝ}
    (hhalfC : 1 / 2 < c) (hca : c < a)
    (hhalf : ∀ i, 1 / 2 < depth i) (ha : ∀ i, depth i < a)
    (hd₀half : 1 / 2 < d₀) (hd₀a : d₀ < a) (hsigma : 0 < sigma)
    (hcharge : (∑ i, alpha i) ≠ 0) :
    RiemannHypothesis ↔
      XiMassCriticalTruePrimeDepthPacketLineBound alpha depth a sigma := by
  exact (riemannHypothesis_iff_xiMassCriticalTruePrimeConeLineBound
    hhalfC hca hsigma hd₀half hd₀a).trans
      (xiMassCriticalTruePrimeDepthPacketLineBound_iff_truePrimeCone
        hhalf ha hd₀half hd₀a hsigma hcharge).symm

/-- Prime correctness forces zero depth charge, hence any finite co-moving realization with the
same channel coefficients is unconditionally line bounded. -/
theorem levinsonPrimeCorrectOnRoughTail_depthPacketLineBound
    {S : Finset ℕ} {alpha : ℕ → ℂ} {M : ℕ} {depth : {L // L ∈ S} → ℝ}
    {a sigma : ℝ}
    (hlegalAperture : ∀ L ∈ S, 1 < L) (hbound : ∀ L ∈ S, L ≤ M)
    (hcorrect : Sieve.PrimeCorrectOnRoughTail S alpha M)
    (hhalf : ∀ L, 1 / 2 < depth L) (ha : ∀ L, depth L < a)
    (hsigma : 0 < sigma) :
    XiMassCriticalTruePrimeDepthPacketLineBound
      (fun L : {L // L ∈ S} => alpha L) depth a sigma := by
  have hintercept :=
    (Sieve.intercept_eq_zero_and_logSlope_eq_neg_one_of_primeCorrectOnRoughTail
      hlegalAperture hbound hcorrect).1
  have hcharge : ∑ L : {L // L ∈ S}, alpha L = 0 := by
    rw [← Finset.sum_subtype S (by intro L; rfl)]
    simpa only [Sieve.levinsonReciprocalDetectorCombinationIntercept] using hintercept
  exact xiMassCriticalTruePrimeDepthPacketLineBound_of_charge_zero
    hhalf ha hsigma hcharge

end

end RHTower
