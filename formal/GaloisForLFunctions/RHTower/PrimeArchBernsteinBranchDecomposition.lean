import GaloisForLFunctions.RHTower.XiBernsteinPuritySquareRootDecomposition
import GaloisForLFunctions.RHTower.XiBernsteinMaximalPacketGap
import GaloisForLFunctions.RHTower.FiniteBernsteinCoordinatePacketAsymptotic
import GaloisForLFunctions.RHTower.FiniteComplexPacketEnergyPerturbation
import Mathlib

/-!
# The exact finite-packet branch decomposition of the Bernstein susceptibility

The corpus already splits the endpoint susceptibility into the finite maximal diagonal square-root
kernel plus a remainder, and shows that the remainder carries no square-root boundary.  This module
supplies the missing analytic half: the remainder coefficients decay at a geometric rate strictly
below `B²`, so the remainder Abel series converges on a disc strictly larger than the critical
radius `R_A = B^{-2}` and is therefore holomorphic across it.

Two inputs do the work: the polarized packet expansion, which turns the finite packet energy minus
its diagonal into the mixed cross moments, and the corpus mixed-mode gap, which bounds every mixed
cross moment of one maximal packet by a rate below `B²`.  The non-maximal atoms are controlled by
the corpus `l1` packet bounds at rates `Bβ` and `β²`.

Consequently the only non-single-valued part of the susceptibility germ at `R_A` is the explicit
square-root kernel: the card's exact local branch decomposition.
-/

set_option maxHeartbeats 1600000

open Complex Filter Topology Finset ComplexConjugate
open scoped BigOperators Real
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The mixed-maximal energy gap of a finite coordinate packet -/

theorem abs_finiteBernsteinCoordinatePacketEnergy_sub_diagonal_le
    (U : Finset ℂ) (C : ℂ → ℂ) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hgap : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ∀ n : ℕ,
      ‖reflectedBernsteinCrossMoment u v n‖ ≤ gamma ^ n) (n : ℕ) :
    |finiteBernsteinCoordinatePacketEnergy U C n
        - finiteBernsteinCoordinateDiagonalEnergy U C n|
      ≤ (∑ u ∈ U, ‖C u‖) ^ (2 : ℕ) * gamma ^ n := by
  classical
  have hdiag : finiteBernsteinCoordinateDiagonalEnergy U C n
      = ∑ u ∈ U, (C u * conj (C u) * reflectedBernsteinCrossMoment u u n).re := by
    rw [finiteBernsteinCoordinateDiagonalEnergy]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [reflectedBernsteinCrossMoment_self, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hsplit : finiteBernsteinCoordinatePacketEnergy U C n
      - finiteBernsteinCoordinateDiagonalEnergy U C n
      = ∑ u ∈ U, ∑ v ∈ U.erase u,
          (C u * conj (C v) * reflectedBernsteinCrossMoment u v n).re := by
    rw [finiteBernsteinCoordinatePacketEnergy_eq_sum_re_crossMoment, hdiag,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← Finset.sum_erase_add U _ hu]
    ring
  rw [hsplit]
  have hbound : ∀ u ∈ U, ∀ v ∈ U.erase u,
      |(C u * conj (C v) * reflectedBernsteinCrossMoment u v n).re|
        ≤ ‖C u‖ * ‖C v‖ * gamma ^ n := by
    intro u hu v hv
    have hvU : v ∈ U := Finset.mem_of_mem_erase hv
    have hne : u ≠ v := (Ne.symm (Finset.ne_of_mem_erase hv))
    have hcross := hgap u hu v hvU hne n
    calc |(C u * conj (C v) * reflectedBernsteinCrossMoment u v n).re|
        ≤ ‖C u * conj (C v) * reflectedBernsteinCrossMoment u v n‖ :=
          Complex.abs_re_le_norm _
      _ = ‖C u‖ * ‖C v‖ * ‖reflectedBernsteinCrossMoment u v n‖ := by
          rw [norm_mul, norm_mul, RCLike.norm_conj]
      _ ≤ ‖C u‖ * ‖C v‖ * gamma ^ n := by
          refine mul_le_mul_of_nonneg_left hcross (by positivity)
  calc |∑ u ∈ U, ∑ v ∈ U.erase u,
        (C u * conj (C v) * reflectedBernsteinCrossMoment u v n).re|
      ≤ ∑ u ∈ U, |∑ v ∈ U.erase u,
          (C u * conj (C v) * reflectedBernsteinCrossMoment u v n).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ U, ∑ v ∈ U.erase u, ‖C u‖ * ‖C v‖ * gamma ^ n := by
        refine Finset.sum_le_sum fun u hu => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact Finset.sum_le_sum fun v hv => hbound u hu v hv
    _ ≤ ∑ u ∈ U, ∑ v ∈ U, ‖C u‖ * ‖C v‖ * gamma ^ n := by
        refine Finset.sum_le_sum fun u _ => ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
        intro v _ _
        positivity
    _ = (∑ u ∈ U, ‖C u‖) ^ (2 : ℕ) * gamma ^ n := by
        rw [sq, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum]

end

end RHTower

namespace RHTower

noncomputable section

open Complex Filter Topology Finset ComplexConjugate
open scoped BigOperators Real
open GaloisForLFunctions.HTGeometry

/-- The mixed pairs of a finite coordinate set. -/
def mixedCoordinatePairs (U : Finset ℂ) : Finset (ℂ × ℂ) :=
  (U ×ˢ U).filter fun p => p.1 ≠ p.2

/-- **Uniform mixed-maximal cross-moment gap.**  Over one maximal Xi packet all mixed cross
moments are dominated by a single geometric rate strictly below `B²`. -/
theorem exists_uniform_mixedCrossMoment_gap
    {D : Finset XiZeroCopy} {B : ℝ} (hB : 1 < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) :
    ∃ gamma : ℝ, 0 ≤ gamma ∧ gamma < B ^ (2 : ℕ) ∧
      ∀ u ∈ xiEndpointCoordinateSet D, ∀ v ∈ xiEndpointCoordinateSet D, u ≠ v →
        ∀ n : ℕ, ‖reflectedBernsteinCrossMoment u v n‖ ≤ gamma ^ n := by
  classical
  set U : Finset ℂ := xiEndpointCoordinateSet D with hU
  set P : Finset (ℂ × ℂ) := mixedCoordinatePairs U with hP
  have hBsq : (0 : ℝ) < B ^ (2 : ℕ) := by positivity
  have hpair : ∀ p : ℂ × ℂ, ∃ g : ℝ, 0 ≤ g ∧ g < B ^ (2 : ℕ) ∧
      (p ∈ P → ∀ n : ℕ, ‖reflectedBernsteinCrossMoment p.1 p.2 n‖ ≤ g ^ n) := by
    intro p
    by_cases hp : p ∈ P
    · rw [hP, mixedCoordinatePairs, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, hne⟩ := hp
      rw [hU, xiEndpointCoordinateSet] at hp1 hp2
      obtain ⟨q, hqD, hq⟩ := Finset.mem_image.mp hp1
      obtain ⟨r, hrD, hr⟩ := Finset.mem_image.mp hp2
      have hcoord : xiEndpointNormalizedReciprocalSquare q ≠
          xiEndpointNormalizedReciprocalSquare r := by
        rw [hq, hr]
        exact hne
      obtain ⟨gamma, hg0, hgB, hgn⟩ :=
        exists_uniform_mixedXiBernsteinCrossMoment_gap_of_distinct_maximal_coordinates
          hB (hD q hqD) (hD r hrD) hcoord
      refine ⟨gamma, hg0, hgB, fun _ n => ?_⟩
      rw [← hq, ← hr]
      exact hgn n
    · exact ⟨0, le_rfl, hBsq, fun h => absurd h hp⟩
  choose g hg0 hgB hgn using hpair
  by_cases hPne : P.Nonempty
  · refine ⟨P.sup' hPne g, ?_, ?_, ?_⟩
    · obtain ⟨p, hp⟩ := hPne
      exact le_trans (hg0 p) (Finset.le_sup' g hp)
    · rw [Finset.sup'_lt_iff]
      exact fun p _ => hgB p
    · intro u hu v hv hne n
      have hmem : (u, v) ∈ P := by
        rw [hP, mixedCoordinatePairs, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hu, hv⟩, hne⟩
      have hle : g (u, v) ≤ P.sup' hPne g := Finset.le_sup' g hmem
      calc ‖reflectedBernsteinCrossMoment u v n‖ ≤ g (u, v) ^ n := hgn (u, v) hmem n
        _ ≤ (P.sup' hPne g) ^ n := pow_le_pow_left₀ (hg0 (u, v)) hle n
  · refine ⟨0, le_rfl, hBsq, ?_⟩
    intro u hu v hv hne n
    exfalso
    exact hPne ⟨(u, v), by
      rw [hP, mixedCoordinatePairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hu, hv⟩, hne⟩⟩

end

end RHTower

namespace RHTower

noncomputable section

open Complex Filter Topology Finset ComplexConjugate
open scoped BigOperators Real
open GaloisForLFunctions.HTGeometry

/-- **Uniform exponential bound for the diagonal remainder.**  After the finite maximal diagonal
packet is removed, the remaining Xi purity decays at a geometric rate strictly below `B²`:
the non-maximal atoms contribute at most `(Bβ)^n` and `β^{2n}`, and distinct maximal coordinates
contribute at most the mixed cross-moment gap. -/
theorem exists_remainder_exponential_bound {D : Finset XiZeroCopy} {B beta : ℝ}
    (hB : 1 < B) (hbeta1 : 1 < beta) (hbeta : beta < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    (hDsub : ∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) :
    ∃ gamma K : ℝ, 0 ≤ gamma ∧ gamma < B ^ (2 : ℕ) ∧ 0 ≤ K ∧
      ∀ n : ℕ, |primeArchEndpointBernsteinDiagonalRemainder D n| ≤ K * gamma ^ n := by
  classical
  obtain ⟨gamma1, hg10, hg1B, hg1⟩ := exists_uniform_mixedCrossMoment_gap hB hD
  set c : XiZeroCopy → ℂ := xiZeroCopyReciprocalSquare with hc
  set u : XiZeroCopy → ℂ := xiEndpointNormalizedReciprocalSquare with hu
  set U : Finset ℂ := xiEndpointCoordinateSet D with hU
  set C : ℂ → ℂ := xiEndpointCoordinateWeight D with hC
  have hcsum : Summable c := summable_xiZeroCopyReciprocalSquare
  have hBpos : (0 : ℝ) < B := lt_trans zero_lt_one hB
  have hbeta0 : (0 : ℝ) < beta := lt_trans zero_lt_one hbeta1
  have hampD : ∀ q ∈ D, ‖u q‖ + ‖1 - u q‖ ≤ B := by
    intro q hq
    have := hD q hq
    rw [xiEndpointBernsteinAtomAmplitudeBase] at this
    exact le_of_eq this
  have hampAll : ∀ q : XiZeroCopy, ‖u q‖ + ‖1 - u q‖ ≤ B := by
    intro q
    by_cases hq : q ∈ D
    · exact hampD q hq
    · have := hDsub q hq
      rw [xiEndpointBernsteinAtomAmplitudeBase] at this
      linarith
  have hampC : ∀ q ∉ D, ‖u q‖ + ‖1 - u q‖ ≤ beta := by
    intro q hq
    have := hDsub q hq
    rw [xiEndpointBernsteinAtomAmplitudeBase] at this
    exact this
  set A : ℝ := atomicWeightL1 (fun j : {j : XiZeroCopy // j ∈ D} => c j) with hA
  set R : ℝ := atomicWeightL1 (fun j : {j : XiZeroCopy // j ∉ D} => c j) with hR
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have hR0 : 0 ≤ R := tsum_nonneg fun _ => norm_nonneg _
  -- the two rates
  set gamma : ℝ := max gamma1 (max (B * beta) (beta ^ (2 : ℕ))) with hgamma
  have hgamma0 : 0 ≤ gamma := le_trans hg10 (le_max_left _ _)
  have hgammaB : gamma < B ^ (2 : ℕ) := by
    refine max_lt hg1B (max_lt ?_ ?_)
    · nlinarith
    · nlinarith
  set K : ℝ := 2 * A * R + R ^ (2 : ℕ) + (∑ x ∈ U, ‖C x‖) ^ (2 : ℕ) with hK
  have hK0 : 0 ≤ K := by
    have h1 : (0 : ℝ) ≤ 2 * A * R := by positivity
    have h2 : (0 : ℝ) ≤ R ^ (2 : ℕ) := by positivity
    have h3 : (0 : ℝ) ≤ (∑ x ∈ U, ‖C x‖) ^ (2 : ℕ) := by positivity
    linarith
  refine ⟨gamma, K, hgamma0, hgammaB, hK0, ?_⟩
  intro n
  set a : ℕ → ℕ → ℂ := finiteBernsteinCoordinatePacket U C with ha
  set r : ℕ → ℕ → ℂ := atomicBernsteinComplementPacket D c u with hr
  have hsplit : ∀ k ∈ Finset.range (n + 1),
      atomicBernsteinPacket c u n k = a n k + r n k := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h := atomicBernsteinPacket_eq_finiteCoordinate_add_complement D c u hcsum hampAll hkn
    exact h
  have hpurity : primeArchEndpointBernsteinPurity n
      = finiteComplexPacketSquareEnergy (fun k => a n k + r n k) (n + 1) := by
    rw [primeArchEndpointBernsteinPurity_eq_atomicBernsteinPacketSquareEnergy,
      atomicBernsteinPacketSquareEnergy, finiteComplexPacketSquareEnergy,
      finiteComplexPacketSquareEnergy]
    exact Finset.sum_congr rfl fun k hk => by rw [hsplit k hk]
  have hpacket : finiteComplexPacketSquareEnergy (a n) (n + 1)
      = finiteBernsteinCoordinatePacketEnergy U C n := rfl
  have hL1a : finitePacketL1 a n ≤ A * B ^ n :=
    finitePacketL1_finiteBernsteinCoordinatePacket_le D c u hcsum hampD n
  have hL1r : finitePacketL1 r n ≤ R * beta ^ n :=
    finitePacketL1_atomicBernsteinComplementPacket_le D c u hcsum hampC n
  have hL1a0 : 0 ≤ finitePacketL1 a n := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hL1r0 : 0 ≤ finitePacketL1 r n := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hpert := abs_finiteComplexPacketSquareEnergy_add_sub_le (a n) (r n) (n + 1)
  have hterm1 : |primeArchEndpointBernsteinPurity n
      - finiteBernsteinCoordinatePacketEnergy U C n|
      ≤ 2 * A * R * (B * beta) ^ n + R ^ (2 : ℕ) * (beta ^ (2 : ℕ)) ^ n := by
    rw [hpurity, ← hpacket]
    refine hpert.trans ?_
    have hbound1 : (2 * (∑ k ∈ Finset.range (n + 1), ‖a n k‖)) *
        (∑ k ∈ Finset.range (n + 1), ‖r n k‖) ≤ (2 * (A * B ^ n)) * (R * beta ^ n) := by
      refine mul_le_mul ?_ hL1r hL1r0 (by positivity)
      have h1 : (∑ k ∈ Finset.range (n + 1), ‖a n k‖) ≤ A * B ^ n := hL1a
      linarith
    have hbound2 : (∑ k ∈ Finset.range (n + 1), ‖r n k‖) ^ (2 : ℕ) ≤ (R * beta ^ n) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ hL1r0 hL1r 2
    have hrw1 : 2 * (A * B ^ n) * (R * beta ^ n) = 2 * A * R * (B * beta) ^ n := by
      rw [mul_pow]
      ring
    have hrw2 : (R * beta ^ n) ^ (2 : ℕ) = R ^ (2 : ℕ) * (beta ^ (2 : ℕ)) ^ n := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
    linarith [hbound1, hbound2, hrw1, hrw2]
  have hterm2 : |finiteBernsteinCoordinatePacketEnergy U C n
      - xiEndpointCoordinateDiagonalPurity D n|
      ≤ (∑ x ∈ U, ‖C x‖) ^ (2 : ℕ) * gamma1 ^ n := by
    rw [xiEndpointCoordinateDiagonalPurity]
    exact abs_finiteBernsteinCoordinatePacketEnergy_sub_diagonal_le U C hg10
      (fun x hx y hy hxy m => hg1 x hx y hy hxy m) n
  have htri : |primeArchEndpointBernsteinDiagonalRemainder D n|
      ≤ |primeArchEndpointBernsteinPurity n - finiteBernsteinCoordinatePacketEnergy U C n|
        + |finiteBernsteinCoordinatePacketEnergy U C n
          - xiEndpointCoordinateDiagonalPurity D n| := by
    rw [primeArchEndpointBernsteinDiagonalRemainder]
    have hsub : primeArchEndpointBernsteinPurity n - xiEndpointCoordinateDiagonalPurity D n
        = (primeArchEndpointBernsteinPurity n - finiteBernsteinCoordinatePacketEnergy U C n)
          + (finiteBernsteinCoordinatePacketEnergy U C n
            - xiEndpointCoordinateDiagonalPurity D n) := by ring
    rw [hsub]
    exact abs_add_le _ _
  refine htri.trans ?_
  have hpow1 : (B * beta) ^ n ≤ gamma ^ n := by
    refine pow_le_pow_left₀ (by positivity) ?_ n
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hpow2 : (beta ^ (2 : ℕ)) ^ n ≤ gamma ^ n := by
    refine pow_le_pow_left₀ (by positivity) ?_ n
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hpow3 : gamma1 ^ n ≤ gamma ^ n := pow_le_pow_left₀ hg10 (le_max_left _ _) n
  have hcoef1 : (0 : ℝ) ≤ 2 * A * R := by positivity
  have hcoef2 : (0 : ℝ) ≤ R ^ (2 : ℕ) := by positivity
  have hcoef3 : (0 : ℝ) ≤ (∑ x ∈ U, ‖C x‖) ^ (2 : ℕ) := by positivity
  have hfin : 2 * A * R * (B * beta) ^ n + R ^ (2 : ℕ) * (beta ^ (2 : ℕ)) ^ n
      + (∑ x ∈ U, ‖C x‖) ^ (2 : ℕ) * gamma1 ^ n ≤ K * gamma ^ n := by
    rw [hK]
    nlinarith [hpow1, hpow2, hpow3]
  linarith [hterm1, hterm2, hfin]

end

end RHTower

namespace RHTower

noncomputable section

open Complex Filter Topology Finset ComplexConjugate
open scoped BigOperators Real
open GaloisForLFunctions.HTGeometry

/-- A geometric coefficient bound makes the remainder Abel series converge on the whole disc of
radius `1/gamma`. -/
theorem summable_remainder_of_lt_inv_gamma {D : Finset XiZeroCopy} {gamma K : ℝ}
    (hgamma : 0 ≤ gamma) (_hK : 0 ≤ K)
    (hbound : ∀ n : ℕ, |primeArchEndpointBernsteinDiagonalRemainder D n| ≤ K * gamma ^ n)
    {t : ℝ} (ht : |t| * gamma < 1) :
    Summable fun n : ℕ => primeArchEndpointBernsteinDiagonalRemainder D n * t ^ n := by
  refine Summable.of_norm ?_
  have hgeo : Summable fun n : ℕ => K * (|t| * gamma) ^ n := by
    refine Summable.mul_left K ?_
    exact summable_geometric_of_lt_one (by positivity) ht
  refine hgeo.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc |primeArchEndpointBernsteinDiagonalRemainder D n| * |t| ^ n
      ≤ (K * gamma ^ n) * |t| ^ n := by
        exact mul_le_mul_of_nonneg_right (hbound n) (by positivity)
    _ = K * (|t| * gamma) ^ n := by
        rw [mul_pow]
        ring

/-- **`(4)`--`(6)`: the exact finite-packet branch decomposition.**  If RH fails, below the
critical radius the endpoint susceptibility splits as an explicit finite square-root kernel plus a
remainder whose Abel series converges on a strictly larger disc; the kernel carries the whole
half-order boundary and the remainder is therefore holomorphic across `R_A = B^{-2}`. -/
theorem exists_branchDecomposition_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ∃ (D : Finset XiZeroCopy) (B beta gamma K L : ℝ),
      1 < B ∧ 1 < beta ∧ beta < B ∧ D.Nonempty ∧
      0 ≤ gamma ∧ gamma < B ^ (2 : ℕ) ∧ 0 ≤ K ∧ 0 < L ∧
      (∀ t : ℝ, 0 < t → t < 1 / B ^ (2 : ℕ) →
        primeArchEndpointBernsteinAbelSusceptibility t =
          finiteBernsteinCoordinateDiagonalSquareRootKernel
            (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D) B t +
          primeArchEndpointBernsteinDiagonalRemainderAbelSusceptibility D t) ∧
      (∀ n : ℕ, |primeArchEndpointBernsteinDiagonalRemainder D n| ≤ K * gamma ^ n) ∧
      (∀ t : ℝ, |t| * gamma < 1 →
        Summable fun n : ℕ =>
          primeArchEndpointBernsteinDiagonalRemainder D n * t ^ n) ∧
      Tendsto
        (fun t : ℝ => Real.sqrt (1 - B ^ (2 : ℕ) * t) *
          primeArchEndpointBernsteinAbelSusceptibility t)
        (nhdsWithin (1 / B ^ (2 : ℕ)) (Set.Ico 0 (1 / B ^ (2 : ℕ))))
        (nhds (Real.sqrt Real.pi * L)) := by
  obtain ⟨D, B, beta, L, hB, hbeta1, hbeta, hDne, hD, hDsub, hL, hLpos, hcrit,
      hdiagSum, hsplit, hremTend, hdiagTend, hfullTend⟩ :=
    exists_exact_maximalDiagonalSquareRootDecomposition_of_not_rh hRH
  obtain ⟨gamma, K, hgamma0, hgammaB, hK0, hbound⟩ :=
    exists_remainder_exponential_bound hB hbeta1 hbeta hD hDsub
  exact ⟨D, B, beta, gamma, K, L, hB, hbeta1, hbeta, hDne, hgamma0, hgammaB, hK0, hLpos,
    hsplit, hbound,
    fun t ht => summable_remainder_of_lt_inv_gamma hgamma0 hK0 hbound ht,
    hfullTend⟩

end

end RHTower
