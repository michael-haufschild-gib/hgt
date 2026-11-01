import GaloisForLFunctions.ArithmeticCountingPositivity.EveryPrimePatternHasActualConductorCoordinates
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeEnergyHasFiniteRamanujanCoordinates

/-!
# Relative conductor coordinates without an Euler-density assumption

Fixed dilations change a signed harmonic sum by a bounded amount. Consequently,
on every sequence where its absolute value diverges, division by that sum
recovers the unnormalized Möbius conductor coefficients. This retains the
arithmetic information even when all density-normalized coordinates vanish.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.BezoutValuationIncidence

open private signed_harmonic_shell_le from
  GaloisForLFunctions.ArithmeticCountingPositivity.PrimeStrippingHasAnAdditiveHarmonicError
open private harmonicMass_shell from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeFlipsHavePositiveHarmonicDensity
open private primeSetFlip_sign primeSetFlip_mul_self from
  GaloisForLFunctions.ArithmeticCountingPositivity.DivisibilityCountsControlInfinitePrimeFlips
open private tendsto_div_harmonicMass_of_div_log from
  GaloisForLFunctions.ArithmeticCountingPositivity.HarmonicParitySpectralCoordinates

/-- The dilation error is bounded independently of the prime pattern and horizon. -/
theorem abs_primeSet_harmonic_decimation_sub_le (P : Set ℕ) {d : ℕ} (hd : 0 < d) (N : ℕ) :
    |gaugeHarmonicSum (primeSetFlip P) (N / d) -
      gaugeHarmonicSum (primeSetFlip P) N| ≤ 1 + Real.log d := by
  rw [abs_sub_comm]
  exact (signed_harmonic_shell_le (primeSetFlip P) (primeSetFlip_sign P)
    (Nat.div_le_self N d)).trans (harmonicMass_shell hd N).2

/-- Every fixed mixed conductor count differs from its Möbius multiple of the
ground harmonic sum by a bounded amount. -/
theorem abs_primeSetRamanujanSum_sub_mobius_mul_le (P : Set ℕ) (m N : ℕ) :
    |primeSetRamanujanSum P m N -
      primeSetMobius P m * gaugeHarmonicSum (primeSetFlip P) N| ≤
      ∑ d ∈ m.divisors, |moebiusReal (m / d) * primeSetFlip P d| * (1 + Real.log d) := by
  rw [primeSetRamanujanSum_eq, primeSetMobius, sum_mul, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (abs_primeSet_harmonic_decimation_sub_le P (Nat.pos_of_mem_divisors hd) N) (abs_nonneg _)

/-- Relative coordinates survive along any sequence of unbounded harmonic sums. -/
theorem tendsto_primeSetRamanujanSum_div_harmonic (P : Set ℕ) (m : ℕ) {ν : ℕ → ℕ}
    (hν : Tendsto (fun j => |gaugeHarmonicSum (primeSetFlip P) (ν j)|) atTop atTop) :
    Tendsto (fun j => primeSetRamanujanSum P m (ν j) /
      gaugeHarmonicSum (primeSetFlip P) (ν j)) atTop (𝓝 (primeSetMobius P m)) := by
  let C := ∑ d ∈ m.divisors,
    |moebiusReal (m / d) * primeSetFlip P d| * (1 + Real.log d)
  have herr : Tendsto (fun j =>
      (primeSetRamanujanSum P m (ν j) -
        primeSetMobius P m * gaugeHarmonicSum (primeSetFlip P) (ν j)) /
          gaugeHarmonicSum (primeSetFlip P) (ν j)) atTop (𝓝 0) := by
    have hsmall : Tendsto (fun j => C / |gaugeHarmonicSum (primeSetFlip P) (ν j)|)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop hν
    apply squeeze_zero_norm (fun j => ?_) hsmall
    rw [Real.norm_eq_abs, abs_div]
    exact div_le_div_of_nonneg_right
      (abs_primeSetRamanujanSum_sub_mobius_mul_le P m (ν j)) (abs_nonneg _)
  have he : ∀ᶠ j in atTop,
      (primeSetRamanujanSum P m (ν j) -
        primeSetMobius P m * gaugeHarmonicSum (primeSetFlip P) (ν j)) /
          gaugeHarmonicSum (primeSetFlip P) (ν j) + primeSetMobius P m =
        primeSetRamanujanSum P m (ν j) / gaugeHarmonicSum (primeSetFlip P) (ν j) := by
    filter_upwards [hν.eventually_gt_atTop 0] with j hj
    have hn := abs_pos.mp hj
    field_simp
    ring
  simpa only [zero_add] using (herr.add_const (primeSetMobius P m)).congr' he

/-- A positive actual gap supplies a cofinal sequence on which relative
conductor normalization is valid, regardless of Euler density. -/
theorem exists_large_harmonic_sequence_of_primeSet_gap (P : Set ℕ) {g : ℝ}
    (hg : 0 < g) (hgap : HasHyperplaneGap (primeSetFlip P) g) :
    ∃ ν : ℕ → ℕ, Tendsto ν atTop atTop ∧
      Tendsto (fun j => |gaugeHarmonicSum (primeSetFlip P) (ν j)|) atTop atTop := by
  obtain ⟨c, hc, hf⟩ := frequently_harmonicSum_sq_ge_of_hasHyperplaneGap
    (primeSetFlip_mul_self P) hg hgap
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hex (j : ℕ) : ∃ N : ℕ, j ≤ N ∧
      (j : ℝ) ≤ |gaugeHarmonicSum (primeSetFlip P) N| := by
    obtain ⟨N, hN, hj, hL⟩ := (hf.and_eventually ((eventually_ge_atTop j).and
      (hlog.eventually_ge_atTop (((j : ℝ) + 1) ^ 2 / c)))).exists
    refine ⟨N, hj, ?_⟩
    have hsq : ((j : ℝ) + 1) ^ 2 ≤ c * Real.log N := by
      exact (div_le_iff₀ hc).mp hL |>.trans_eq (mul_comm _ _)
    have ha := abs_nonneg (gaugeHarmonicSum (primeSetFlip P) N)
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    nlinarith only [hN, hsq, ha, hj0, sq_abs (gaugeHarmonicSum (primeSetFlip P) N)]
  choose ν hν hS using hex
  refine ⟨ν, tendsto_atTop.2 (fun b => ?_), tendsto_atTop.2 (fun b => ?_)⟩
  · exact (eventually_ge_atTop b).mono fun j hj => hj.trans (hν j)
  · exact (tendsto_natCast_atTop_atTop.eventually_ge_atTop b).mono fun j hj => hj.trans (hS j)

/-- Harmonic normalization preserves the identity Gram limit. -/
theorem tendsto_harmonicRamanujanHorizonVector_gram {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N => ⟪harmonicRamanujanHorizonVector m N,
      harmonicRamanujanHorizonVector l N⟫) atTop (𝓝 (if m = l then 1 else 0)) := by
  have he (N : ℕ) : ⟪harmonicRamanujanHorizonVector m N,
      harmonicRamanujanHorizonVector l N⟫ =
      (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) /
        gaugeHarmonicSum (fun _ => 1) N := by
    rw [harmonicRamanujanHorizonVector, harmonicRamanujanHorizonVector,
      real_inner_smul_left, real_inner_smul_right, ramanujanHorizonVector_inner]
    have hH : 0 ≤ gaugeHarmonicSum (fun _ => 1) N := sum_nonneg fun _ _ => by positivity
    rw [← mul_assoc, ← mul_inv, ← sq, Real.sq_sqrt hH]
    ring
  simpa only [he] using tendsto_div_harmonicMass_of_div_log
    (tendsto_ramanujanPoleProfile_gram hm hl)

/-- The complete renormalized prime bilinear form on two fixed conductor modes. -/
def harmonicPrimeEnergyPair (N m l : ℕ) : ℝ :=
  Real.log N * ⟪harmonicRamanujanHorizonVector m N, harmonicRamanujanHorizonVector l N⟫ -
    ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (harmonicRamanujanHorizonVector m N),
      harmonicRamanujanHorizonVector l N⟫

/-- Fixed conductor pairs converge to the diagonal adjunction form. -/
theorem tendsto_harmonicPrimeEnergyPair {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N => harmonicPrimeEnergyPair N m l) atTop
      (𝓝 (if m = l then ramanujanAdjunctionEnergy m else 0)) := by
  let r := fun N => Matrix.toEuclideanLin (fullPrimeMatrix N)
    (harmonicRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • harmonicRamanujanHorizonVector m N
  have hr : Tendsto (fun N => ‖r N‖) atTop (𝓝 0) := by
    simpa only [r, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using
      (tendsto_harmonicRamanujanHorizonVector_residual_sq hm).sqrt
  have hv : Tendsto (fun N => ‖harmonicRamanujanHorizonVector l N‖) atTop (𝓝 1) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_one] using
      (tendsto_harmonicRamanujanHorizonVector_norm_sq hl).sqrt
  have herr : Tendsto (fun N => ⟪r N, harmonicRamanujanHorizonVector l N⟫) atTop (𝓝 0) := by
    have hbound : Tendsto (fun N => ‖r N‖ * ‖harmonicRamanujanHorizonVector l N‖)
        atTop (𝓝 0) := by simpa only [zero_mul] using hr.mul hv
    apply squeeze_zero_norm (fun N => ?_) hbound
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  have he (N : ℕ) : harmonicPrimeEnergyPair N m l =
      ramanujanAdjunctionEnergy m *
        ⟪harmonicRamanujanHorizonVector m N, harmonicRamanujanHorizonVector l N⟫ -
          ⟪r N, harmonicRamanujanHorizonVector l N⟫ := by
    dsimp only [harmonicPrimeEnergyPair, r]
    rw [inner_sub_left, real_inner_smul_left]
    ring
  have h := ((tendsto_harmonicRamanujanHorizonVector_gram hm hl).const_mul
    (ramanujanAdjunctionEnergy m)).sub herr
  simpa only [he, sub_zero, mul_ite, mul_one, mul_zero] using h

/-- A finite conductor packet in common harmonic normalization. -/
def harmonicConductorPacket (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ m ∈ S, a m • harmonicRamanujanHorizonVector m N

/-- Convergent coefficients retain the diagonal finite-packet energy limit. -/
theorem tendsto_harmonicConductorPacket_energy (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m)
    {ν : ℕ → ℕ} (hν : Tendsto ν atTop atTop) {a : ℕ → ℕ → ℝ} {b : ℕ → ℝ}
    (ha : ∀ m ∈ S, Tendsto (fun j => a j m) atTop (𝓝 (b m))) (s : ℝ) :
    Tendsto (fun j => (Real.log (ν j) - s) * ‖harmonicConductorPacket S (a j) (ν j)‖ ^ 2 -
      ⟪Matrix.toEuclideanLin (fullPrimeMatrix (ν j)) (harmonicConductorPacket S (a j) (ν j)),
        harmonicConductorPacket S (a j) (ν j)⟫) atTop
      (𝓝 (∑ m ∈ S, b m ^ 2 * (ramanujanAdjunctionEnergy m - s))) := by
  have he (j : ℕ) : (Real.log (ν j) - s) * ‖harmonicConductorPacket S (a j) (ν j)‖ ^ 2 -
      ⟪Matrix.toEuclideanLin (fullPrimeMatrix (ν j)) (harmonicConductorPacket S (a j) (ν j)),
        harmonicConductorPacket S (a j) (ν j)⟫ =
      ∑ m ∈ S, ∑ l ∈ S, a j m * a j l * (harmonicPrimeEnergyPair (ν j) m l -
        s * ⟪harmonicRamanujanHorizonVector m (ν j), harmonicRamanujanHorizonVector l (ν j)⟫) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [harmonicConductorPacket, map_sum, map_smul, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right, mul_sum, ← sum_sub_distrib]
    rw [sum_comm]
    apply sum_congr rfl fun m _ => sum_congr rfl fun l _ => ?_
    dsimp only [harmonicPrimeEnergyPair]
    ring
  have h := tendsto_finsetSum S fun m hm => tendsto_finsetSum S fun l hl =>
    ((ha m hm).mul (ha l hl)).mul
      (((tendsto_harmonicPrimeEnergyPair (hS m hm) (hS l hl)).comp hν).sub
        (((tendsto_harmonicRamanujanHorizonVector_gram (hS m hm) (hS l hl)).comp hν).const_mul s))
  have hlim : (∑ m ∈ S, ∑ l ∈ S, b m * b l *
      ((if m = l then ramanujanAdjunctionEnergy m else 0) - s * (if m = l then 1 else 0))) =
      ∑ m ∈ S, b m ^ 2 * (ramanujanAdjunctionEnergy m - s) := by
    apply sum_congr rfl fun m hm => ?_
    rw [sum_eq_single m]
    · simp only [ite_true, mul_one, sq]
    · intro l _ hl
      simp only [if_neg (Ne.symm hl), mul_zero, sub_zero]
    · exact fun h => False.elim (h hm)
  rw [hlim] at h
  exact h.congr' (Eventually.of_forall fun j => (he j).symm)

end GaloisForLFunctions.ArithmeticCountingPositivity
