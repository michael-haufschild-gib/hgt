import GaloisForLFunctions.ArithmeticCountingPositivity.RelativePrimePatternCoordinates
import GaloisForLFunctions.ArithmeticCountingPositivity.PositiveDensityTransfersTheExactCutoffGap

/-!
# Finite-cutoff upper bounds without an Euler-density assumption

A positive hyperplane gap forces unbounded harmonic sums on a cofinal sequence.
Relative conductor coordinates on that sequence recover the finite arithmetic
constraint. Correcting only the ground coefficient makes each trial packet
exactly orthogonal, with vanishing correction. Thus actual gaps obey every
finite-cutoff secular inequality even at zero Euler density.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.BezoutValuationIncidence

open private primeSet_form_bound_iff from
  GaloisForLFunctions.ArithmeticCountingPositivity.PositiveDensityTransfersTheExactCutoffGap
open private conductor_energy_gap from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheFullResolvent
open private finite_weight_le_primeSet_weight from
  GaloisForLFunctions.ArithmeticCountingPositivity.InfinitePrimeCountsHaveAZeroOrUnitConductorMass
open private primeSetCutoff_prime primeSetFlip_mul_self from
  GaloisForLFunctions.ArithmeticCountingPositivity.DivisibilityCountsControlInfinitePrimeFlips

local notation "γ" => Real.eulerMascheroniConstant

private theorem primeSetRamanujanSum_one (P : Set ℕ) (N : ℕ) :
    primeSetRamanujanSum P 1 N = gaugeHarmonicSum (primeSetFlip P) N := by
  simp [primeSetRamanujanSum_eq, moebiusReal, primeSetFlip, primeSignGauge]

private theorem primeSet_inner_ground (P : Set ℕ) (N : ℕ) :
    ⟪primeSetHorizonVector P N, harmonicRamanujanHorizonVector 1 N⟫ =
      gaugeHarmonicSum (primeSetFlip P) N / gaugeHarmonicSum (fun _ => 1) N := by
  rw [primeSetHorizonVector_inner P zero_lt_one, primeSetRamanujanSum_one]
  simp only [Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one]

private theorem primeSet_inner_packet (P : Set ℕ) (S : Finset ℕ)
    (hS : ∀ m ∈ S, 0 < m) (a : ℕ → ℝ) (N : ℕ) :
    ⟪primeSetHorizonVector P N, harmonicConductorPacket S a N⟫ =
      (∑ m ∈ S, a m * (primeSetRamanujanSum P m N / Real.sqrt (m.totient : ℝ))) /
        gaugeHarmonicSum (fun _ => 1) N := by
  rw [harmonicConductorPacket, inner_sum, sum_div]
  apply sum_congr rfl fun m hm => ?_
  rw [real_inner_smul_right, primeSetHorizonVector_inner P (hS m hm)]
  ring

/-- Every positive actual gap bounds the limiting diagonal form on the
relative arithmetic hyperplane, without a density assumption. -/
theorem primeSet_gap_le_finite_diagonal_form (P : Set ℕ) {g s : ℝ}
    (hg : 0 < g) (hgap : HasHyperplaneGap (primeSetFlip P) g) (hsg : s < g)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (h1 : 1 ∈ S) (b : ℕ → ℝ)
    (hb : ∑ m ∈ S, b m * (primeSetMobius P m / Real.sqrt (m.totient : ℝ)) = 0) :
    0 ≤ ∑ m ∈ S, b m ^ 2 * (ramanujanAdjunctionEnergy m - γ - s) := by
  classical
  obtain ⟨ν, hν, hlarge⟩ := exists_large_harmonic_sequence_of_primeSet_gap P hg hgap
  let R := fun j => (∑ m ∈ S, b m *
      (primeSetRamanujanSum P m (ν j) / Real.sqrt (m.totient : ℝ))) /
        gaugeHarmonicSum (primeSetFlip P) (ν j)
  have hR : Tendsto R atTop (𝓝 0) := by
    have h := tendsto_finsetSum S fun m _ =>
      ((tendsto_primeSetRamanujanSum_div_harmonic P m hlarge).div_const
        (Real.sqrt (m.totient : ℝ))).const_mul (b m)
    rw [hb] at h
    convert h using 1
    ext j
    dsimp only [R]
    rw [sum_div]
    exact sum_congr rfl fun m _ => by ring
  let a := fun j m => if m = 1 then b m - R j else b m
  have ha (m : ℕ) (_hm : m ∈ S) : Tendsto (fun j => a j m) atTop (𝓝 (b m)) := by
    by_cases hm : m = 1
    · simpa only [a, if_pos hm, sub_zero] using tendsto_const_nhds.sub hR
    · simpa only [a, if_neg hm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => b m) atTop (𝓝 (b m)))
  have hpacket (j : ℕ) : harmonicConductorPacket S (a j) (ν j) =
      harmonicConductorPacket S b (ν j) - R j • harmonicRamanujanHorizonVector 1 (ν j) := by
    have he (m : ℕ) : a j m • harmonicRamanujanHorizonVector m (ν j) =
        b m • harmonicRamanujanHorizonVector m (ν j) -
          (if m = 1 then R j • harmonicRamanujanHorizonVector 1 (ν j) else 0) := by
      by_cases hm : m = 1
      · subst m
        simp only [a, if_pos rfl, sub_smul]
      · simp only [a, if_neg hm, sub_zero]
    simp only [harmonicConductorPacket, he, sum_sub_distrib]
    congr 1
    rw [sum_eq_single 1]
    · simp only [ite_true]
    · exact fun m _ hm => if_neg hm
    · exact fun h => False.elim (h h1)
  have horth : ∀ᶠ j in atTop,
      ⟪primeSetHorizonVector P (ν j), harmonicConductorPacket S (a j) (ν j)⟫ = 0 := by
    filter_upwards [hlarge.eventually_gt_atTop 0] with j hj
    have hn := abs_pos.mp hj
    rw [hpacket, inner_sub_right, real_inner_smul_right, primeSet_inner_packet P S hS,
      primeSet_inner_ground]
    dsimp only [R]
    field_simp
  obtain ⟨N₀, hN₀⟩ := hgap (g - s) (sub_pos.mpr hsg)
  have hnonneg : ∀ᶠ j in atTop,
      0 ≤ (Real.log (ν j) - (γ + s)) * ‖harmonicConductorPacket S (a j) (ν j)‖ ^ 2 -
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix (ν j)) (harmonicConductorPacket S (a j) (ν j)),
          harmonicConductorPacket S (a j) (ν j)⟫ := by
    filter_upwards [horth, hν.eventually_ge_atTop N₀, hν.eventually_ge_atTop 1] with j hj hN hN1
    have hbound := (primeSet_form_bound_iff P hN1 s).mpr (by
      intro x hx
      have h := hN₀ (ν j) hN x hx
      convert h using 1 <;> ring)
    have h := hbound (harmonicConductorPacket S (a j) (ν j)) hj
    nlinarith only [h]
  have h := ge_of_tendsto (tendsto_harmonicConductorPacket_energy S hS hν ha (γ + s)) hnonneg
  convert h using 1
  apply sum_congr rfl fun m _ => ?_
  ring

private theorem primeSet_relative_one (P : Set ℕ) :
    primeSetMobius P 1 / Real.sqrt (Nat.totient 1 : ℝ) = 1 := by
  have h := (primeSetMobius_eq_finiteCutoff P (m := 1) (Q := 1) le_rfl).trans
    (finiteFlipMobius_isMultiplicative (primeSetCutoff P 1)).map_one
  simp only [h, Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one]

private theorem primeSet_relative_sq (P : Set ℕ) (m : ℕ) :
    (primeSetMobius P m / Real.sqrt (m.totient : ℝ)) ^ 2 = primeSetSpectralWeight P m := by
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rfl

/-- A positive actual gap bounds every finite arithmetic reciprocal tail. -/
theorem primeSet_partial_secular_le_of_gap (P : Set ℕ) {g s : ℝ}
    (hgap : HasHyperplaneGap (primeSetFlip P) g) (hs : 0 < s) (hsg : s < g)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 2 ≤ m) :
    (∑ m ∈ S, primeSetSpectralWeight P m /
      (ramanujanAdjunctionEnergy m - γ - s)) ≤ 1 / s := by
  classical
  have hcap := le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one
    (primeSetFlip_mul_self P) hgap
  have hs2 := hsg.trans_le hcap
  let β := fun m => primeSetMobius P m / Real.sqrt (m.totient : ℝ)
  let d := fun m => ramanujanAdjunctionEnergy m - γ - s
  let T := ∑ m ∈ S, primeSetSpectralWeight P m / d m
  have h1 : 1 ∉ S := fun h => by have := hS 1 h; omega
  have hd (m : ℕ) (hm : m ∈ S) : 0 < d m := by
    have hm2 := hS m hm
    have he := conductor_energy_gap (m - 2)
    rw [Nat.sub_add_cancel hm2] at he
    exact sub_pos.mpr (hs2.trans_le he)
  have hβ (m : ℕ) : β m ^ 2 = primeSetSpectralWeight P m := primeSet_relative_sq P m
  have hβ1 : β 1 = 1 := primeSet_relative_one P
  let b := fun m => if m = 1 then -T else β m / d m
  have hb1 : b 1 = -T := if_pos rfl
  have hbm (m : ℕ) (hm : m ∈ S) : b m = β m / d m :=
    if_neg (by have := hS m hm; omega)
  have horth : ∑ m ∈ insert 1 S, b m * β m = 0 := by
    rw [sum_insert h1, hb1, hβ1, mul_one]
    have he : (∑ m ∈ S, b m * β m) = T := by
      apply sum_congr rfl fun m hm => ?_
      rw [hbm m hm, ← hβ]
      ring
    rw [he]
    ring
  have henergy := primeSet_gap_le_finite_diagonal_form P (hs.trans hsg) hgap hsg
    (insert 1 S) (fun m hm => by
      rcases mem_insert.mp hm with rfl | hm
      · exact zero_lt_one
      · exact lt_of_lt_of_le (by norm_num) (hS m hm)) (mem_insert_self _ _) b horth
  have he : (∑ m ∈ insert 1 S, b m ^ 2 * (ramanujanAdjunctionEnergy m - γ - s)) =
      -s * T ^ 2 + T := by
    rw [sum_insert h1, hb1, ramanujanAdjunctionEnergy_one, sub_self, zero_sub, neg_sq]
    have htail : (∑ m ∈ S, b m ^ 2 * (ramanujanAdjunctionEnergy m - γ - s)) = T := by
      apply sum_congr rfl fun m hm => ?_
      rw [hbm m hm]
      change (β m / d m) ^ 2 * d m = primeSetSpectralWeight P m / d m
      rw [← hβ]
      field_simp [(hd m hm).ne']
    rw [htail]
    ring
  rw [he] at henergy
  change T ≤ 1 / s
  by_contra hnot
  have hT : 1 < s * T := by
    have h := (div_lt_iff₀ hs).mp (lt_of_not_ge hnot)
    simpa only [mul_comm] using h
  have hT0 : 0 < T := (div_pos zero_lt_one hs).trans (lt_of_not_ge hnot)
  nlinarith only [henergy, mul_pos hT0 (sub_pos.mpr hT)]

/-- Every actual prime-pattern gap is also a gap for every finite prime cutoff.
The assertion includes vanishing Euler density. -/
theorem primeSetFlip_gap_implies_cutoff_gap (P : Set ℕ) {g : ℝ}
    (hgap : HasHyperplaneGap (primeSetFlip P) g) (Q : ℕ) :
    HasHyperplaneGap (finiteFlip (primeSetCutoff P Q)) g := by
  classical
  apply (finiteFlip_hasHyperplaneGap_iff_secular _ (primeSetCutoff_prime P Q) g).mpr
  have hcap := le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one
    (primeSetFlip_mul_self P) hgap
  refine ⟨hcap, fun s hs hsg => ?_⟩
  have hs2 := hsg.trans_le hcap
  have hpartial (K : ℕ) :
      (∑ k ∈ range K, finiteFlipSpectralWeight (primeSetCutoff P Q) (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - s)) ≤ 1 / s := by
    have h := primeSet_partial_secular_le_of_gap P hgap hs hsg
      ((range K).image (fun k => k + 2)) (fun m hm => by
        obtain ⟨k, _, rfl⟩ := mem_image.mp hm
        omega)
    rw [sum_image (fun a _ b _ h => by omega)] at h
    refine (sum_le_sum fun k _ => ?_).trans h
    exact div_le_div_of_nonneg_right (finite_weight_le_primeSet_weight P Q _)
      (sub_pos.mpr (hs2.trans_le (conductor_energy_gap k))).le
  have hsum := summable_finiteFlipSecularTail _ (primeSetCutoff_prime P Q) hs hs2
  have htail := le_of_tendsto hsum.hasSum.tendsto_sum_nat (Eventually.of_forall hpartial)
  dsimp only [finiteFlipSecular]
  linarith only [htail]

/-- Finite prime cutoffs bound every actual greatest gap from above. -/
theorem primeSetGreatestGap_le_every_cutoff (P : Set ℕ) (Q : ℕ) :
    primeSetGreatestGap P ≤ finiteFlipGreatestGap (primeSetCutoff P Q) :=
  (finiteFlip_hasHyperplaneGap_iff_le_greatestGap _ (primeSetCutoff_prime P Q) _).mp
    (primeSetFlip_gap_implies_cutoff_gap P (isGreatest_primeSetFlip_hyperplaneGap P).1 Q)

end GaloisForLFunctions.ArithmeticCountingPositivity
