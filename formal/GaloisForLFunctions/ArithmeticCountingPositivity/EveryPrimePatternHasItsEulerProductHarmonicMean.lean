import GaloisForLFunctions.ArithmeticCountingPositivity.PrimeStrippingHasAnAdditiveHarmonicError
import GaloisForLFunctions.ArithmeticCountingPositivity.DivisibilityCountsControlInfinitePrimeFlips
import GaloisForLFunctions.ArithmeticCountingPositivity.FiniteReciprocalMassControlsTheHyperplane
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Every prime pattern has its Euler-product harmonic mean

Finite prime stripping controls patterns with vanishing Euler product.
When the product stays positive, its tail ratio bounds the omitted
reciprocal divisibility mass. These two counts prove the harmonic mean
for every prime-sign pattern and pay its squared-density selective gap.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticElectrostatics

open private primeSetFlip_sign primeSetFlip_mul_self primeSetCutoff_prime
  primeSetFlip_partition primeSetFlip_cutoff_eq from
  GaloisForLFunctions.ArithmeticCountingPositivity.DivisibilityCountsControlInfinitePrimeFlips

/-- The decreasing Euler-product density of a prime-sign pattern. -/
def primeSetHarmonicDensity (P : Set ℕ) : ℝ :=
  ⨅ Q : ℕ, finiteFlipHarmonicDensity (primeSetCutoff P Q)

private theorem primeSetCutoff_mono (P : Set ℕ) : Monotone (primeSetCutoff P) := by
  classical
  intro Q N hQN p hp
  simp only [primeSetCutoff, mem_filter, Nat.mem_primesLE] at hp ⊢
  exact ⟨⟨hp.1.1.trans hQN, hp.1.2⟩, hp.2⟩

private theorem cutoffDensity_antitone (P : Set ℕ) :
    Antitone (fun Q => finiteFlipHarmonicDensity (primeSetCutoff P Q)) := by
  intro Q N hQN
  have hsub := primeSetCutoff_mono P hQN
  have hprime : ∀ p ∈ primeSetCutoff P N \ primeSetCutoff P Q, p.Prime :=
    fun p hp => primeSetCutoff_prime P N p (mem_sdiff.mp hp).1
  have he : finiteFlipHarmonicDensity (primeSetCutoff P N \ primeSetCutoff P Q) *
      finiteFlipHarmonicDensity (primeSetCutoff P Q) =
        finiteFlipHarmonicDensity (primeSetCutoff P N) := prod_sdiff hsub
  change finiteFlipHarmonicDensity (primeSetCutoff P N) ≤
    finiteFlipHarmonicDensity (primeSetCutoff P Q)
  rw [← he]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (finiteFlipHarmonicDensity_le_one hprime)
    (finiteFlipHarmonicDensity_pos (primeSetCutoff_prime P Q)).le

/-- Finite prime-cutoff densities decrease to the full Euler product. -/
theorem tendsto_primeSetCutoff_density (P : Set ℕ) :
    Tendsto (fun Q => finiteFlipHarmonicDensity (primeSetCutoff P Q))
      atTop (𝓝 (primeSetHarmonicDensity P)) := by
  apply tendsto_atTop_ciInf (cutoffDensity_antitone P)
  refine ⟨0, ?_⟩
  rintro _ ⟨Q, rfl⟩
  exact (finiteFlipHarmonicDensity_pos (primeSetCutoff_prime P Q)).le

/-- Every prime-pattern Euler-product density lies between zero and one. -/
theorem primeSetHarmonicDensity_bounds (P : Set ℕ) :
    0 ≤ primeSetHarmonicDensity P ∧ primeSetHarmonicDensity P ≤ 1 := by
  constructor
  · exact ge_of_tendsto (tendsto_primeSetCutoff_density P) (Eventually.of_forall
      fun Q => (finiteFlipHarmonicDensity_pos (primeSetCutoff_prime P Q)).le)
  · exact le_of_tendsto (tendsto_primeSetCutoff_density P) (Eventually.of_forall
      fun Q => finiteFlipHarmonicDensity_le_one (primeSetCutoff_prime P Q))

private theorem primeSetHarmonicDensity_le_cutoff (P : Set ℕ) (Q : ℕ) :
    primeSetHarmonicDensity P ≤ finiteFlipHarmonicDensity (primeSetCutoff P Q) := by
  apply le_of_tendsto (tendsto_primeSetCutoff_density P)
  filter_upwards [eventually_ge_atTop Q] with N hN
  exact cutoffDensity_antitone P hN

/-- Each local density pays its reciprocal prime mass; multiplication
retains the positive mixed terms. -/
private theorem density_mul_reciprocal_mass_le (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) :
    finiteFlipHarmonicDensity F * (1 + ∑ p ∈ F, 1 / (p : ℝ)) ≤ 1 := by
  classical
  revert hF
  induction F using Finset.induction_on with
  | empty =>
      intro _
      simp only [finiteFlipHarmonicDensity, prod_empty, sum_empty, add_zero, mul_one, le_refl]
  | @insert p F hpF ih =>
      intro hF
      have hp := hF p (mem_insert_self p F)
      have hF' : ∀ q ∈ F, q.Prime := fun q hq => hF q (mem_insert_of_mem hq)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hpp : 0 < (p : ℝ) + 1 := by positivity
      have hcp : 0 ≤ ((p : ℝ) - 1) / ((p : ℝ) + 1) :=
        div_nonneg (sub_nonneg.mpr hp1.le) hpp.le
      have hlocal : (((p : ℝ) - 1) / ((p : ℝ) + 1)) * (1 + 1 / (p : ℝ)) ≤ 1 := by
        calc
          _ = ((p : ℝ) - 1) / p := by field_simp [hp0.ne', hpp.ne']
          _ ≤ 1 := (div_le_one hp0).mpr (by linarith)
      have hrecip : finiteFlipHarmonicDensity F * (1 / (p : ℝ)) ≤ 1 / (p : ℝ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (finiteFlipHarmonicDensity_le_one hF') (by positivity : 0 ≤ 1 / (p : ℝ))
      have hhead := ih hF'
      change (∏ q ∈ insert p F, ((q : ℝ) - 1) / ((q : ℝ) + 1)) * _ ≤ 1
      rw [prod_insert hpF, sum_insert hpF]
      change (((p : ℝ) - 1) / ((p : ℝ) + 1) * finiteFlipHarmonicDensity F) * _ ≤ 1
      calc
        _ = (((p : ℝ) - 1) / ((p : ℝ) + 1)) *
            (finiteFlipHarmonicDensity F * (1 + ∑ q ∈ F, 1 / (q : ℝ)) +
              finiteFlipHarmonicDensity F * (1 / (p : ℝ))) := by ring
        _ ≤ (((p : ℝ) - 1) / ((p : ℝ) + 1)) * (1 + 1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add hhead hrecip) hcp
        _ ≤ 1 := hlocal

private theorem primeSetCutoff_tail (P : Set ℕ) (Q N : ℕ) :
    primeSetCutoff (P \ Set.Iic Q) N = primeSetCutoff P N \ primeSetCutoff P Q := by
  classical
  apply Finset.ext
  intro p
  simp only [primeSetCutoff, Finset.mem_sdiff, Finset.mem_filter, Nat.mem_primesLE,
    Set.mem_sdiff, Set.mem_Iic]
  tauto

/-- A positive limiting product makes every residual reciprocal tail
small uniformly beyond its cutoff. -/
private theorem reciprocal_tail_le_density_ratio (P : Set ℕ)
    (hc : 0 < primeSetHarmonicDensity P) {Q N : ℕ} (hQN : Q ≤ N) :
    primeSetReciprocalSum (P \ Set.Iic Q) N ≤
      finiteFlipHarmonicDensity (primeSetCutoff P Q) / primeSetHarmonicDensity P - 1 := by
  have htail := density_mul_reciprocal_mass_le (primeSetCutoff (P \ Set.Iic Q) N)
    (primeSetCutoff_prime _ N)
  change finiteFlipHarmonicDensity (primeSetCutoff (P \ Set.Iic Q) N) *
    (1 + primeSetReciprocalSum (P \ Set.Iic Q) N) ≤ 1 at htail
  have he : finiteFlipHarmonicDensity (primeSetCutoff (P \ Set.Iic Q) N) *
      finiteFlipHarmonicDensity (primeSetCutoff P Q) =
        finiteFlipHarmonicDensity (primeSetCutoff P N) := by
    rw [primeSetCutoff_tail]
    exact prod_sdiff (primeSetCutoff_mono P hQN)
  have hm : 0 ≤ primeSetReciprocalSum (P \ Set.Iic Q) N :=
    sum_nonneg fun _ _ => by positivity
  have hproduct : primeSetHarmonicDensity P *
      (1 + primeSetReciprocalSum (P \ Set.Iic Q) N) ≤
        finiteFlipHarmonicDensity (primeSetCutoff P Q) := by
    calc
      _ ≤ finiteFlipHarmonicDensity (primeSetCutoff P N) *
          (1 + primeSetReciprocalSum (P \ Set.Iic Q) N) :=
        mul_le_mul_of_nonneg_right (primeSetHarmonicDensity_le_cutoff P N) (by positivity)
      _ = (finiteFlipHarmonicDensity (primeSetCutoff (P \ Set.Iic Q) N) *
          (1 + primeSetReciprocalSum (P \ Set.Iic Q) N)) *
            finiteFlipHarmonicDensity (primeSetCutoff P Q) := by rw [← he]; ring
      _ ≤ 1 * finiteFlipHarmonicDensity (primeSetCutoff P Q) :=
        mul_le_mul_of_nonneg_right htail
          (finiteFlipHarmonicDensity_pos (primeSetCutoff_prime P Q)).le
      _ = _ := one_mul _
  have hratio : 1 + primeSetReciprocalSum (P \ Set.Iic Q) N ≤
      finiteFlipHarmonicDensity (primeSetCutoff P Q) / primeSetHarmonicDensity P :=
    (le_div_iff₀ hc).mpr (by nlinarith only [hproduct])
  linarith only [hratio]

private theorem primeSet_stripping_error (P : Set ℕ) (Q : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    |harmonicCorrelation (primeSetFlip P) N -
        finiteFlipHarmonicDensity (primeSetCutoff P Q) *
          harmonicCorrelation (primeSetFlip (P \ Set.Iic Q)) N| ≤
      finitePrimeStrippingCost (primeSetCutoff P Q) / gaugeHarmonicSum (fun _ => 1) N := by
  classical
  have hfree : ∀ p ∈ primeSetCutoff P Q, primeSetFlip (P \ Set.Iic Q) p = 1 := by
    intro p hp
    have hprime := primeSetCutoff_prime P Q p hp
    have hpQ : p ≤ Q := by
      simp only [primeSetCutoff, mem_filter, Nat.mem_primesLE] at hp
      exact hp.1.1
    rw [primeSetFlip, primeSignGauge_prime hprime]
    exact if_neg (fun h => h.2 hpQ)
  have hfun : (fun n => finiteFlip (primeSetCutoff P Q) n *
      primeSetFlip (P \ Set.Iic Q) n) = primeSetFlip P := by
    funext n
    rw [← primeSetFlip_cutoff_eq P Q n, ← primeSetFlip_partition P Q n]
  have h := finiteFlip_harmonic_stripping_error (primeSetCutoff P Q)
    (primeSetCutoff_prime P Q) (primeSetFlip (P \ Set.Iic Q)) (primeSetFlip_sign _) hfree N
  rw [hfun] at h
  have hH := gaugeHarmonicSum_one_pos hN
  have he : harmonicCorrelation (primeSetFlip P) N -
      finiteFlipHarmonicDensity (primeSetCutoff P Q) *
        harmonicCorrelation (primeSetFlip (P \ Set.Iic Q)) N =
      (gaugeHarmonicSum (primeSetFlip P) N -
        finiteFlipHarmonicDensity (primeSetCutoff P Q) *
          gaugeHarmonicSum (primeSetFlip (P \ Set.Iic Q)) N) /
            gaugeHarmonicSum (fun _ => 1) N := by
    simp only [harmonicCorrelation]
    ring
  rw [he, abs_div, abs_of_pos hH]
  exact div_le_div_of_nonneg_right h hH.le

private theorem primeSet_correlation_interval (P : Set ℕ) (Q : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    -finiteFlipHarmonicDensity (primeSetCutoff P Q) -
        finitePrimeStrippingCost (primeSetCutoff P Q) / gaugeHarmonicSum (fun _ => 1) N ≤
      harmonicCorrelation (primeSetFlip P) N ∧
    harmonicCorrelation (primeSetFlip P) N ≤ finiteFlipHarmonicDensity (primeSetCutoff P Q) +
        finitePrimeStrippingCost (primeSetCutoff P Q) / gaugeHarmonicSum (fun _ => 1) N := by
  have he := abs_le.mp (primeSet_stripping_error P Q hN)
  have hs := harmonicCorrelation_sq_le_one (primeSetFlip_mul_self (P \ Set.Iic Q)) hN
  have hlo : -1 ≤ harmonicCorrelation (primeSetFlip (P \ Set.Iic Q)) N := by nlinarith only [hs]
  have hhi : harmonicCorrelation (primeSetFlip (P \ Set.Iic Q)) N ≤ 1 := by nlinarith only [hs]
  have hc := (finiteFlipHarmonicDensity_pos (primeSetCutoff_prime P Q)).le
  have hl := mul_le_mul_of_nonneg_left hlo hc
  have hu := mul_le_mul_of_nonneg_left hhi hc
  constructor <;> nlinarith only [he.1, he.2, hl, hu]

private theorem const_div_harmonic_tendsto_zero (K : ℝ) :
    Tendsto (fun N => K / gaugeHarmonicSum (fun _ => 1) N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hH : Tendsto (gaugeHarmonicSum (fun _ => 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hlog.eventually_ge_atTop b, eventually_ge_atTop 1] with N hb hN
    exact hb.trans (log_le_gaugeHarmonicSum_one hN)
  exact tendsto_const_nhds.div_atTop hH

/-- Every prime-sign pattern has the harmonic mean given by its decreasing
Euler product, including products that vanish. -/
theorem primeSetFlip_harmonicCorrelation_tendsto (P : Set ℕ) :
    Tendsto (harmonicCorrelation (primeSetFlip P)) atTop (𝓝 (primeSetHarmonicDensity P)) := by
  have hd := tendsto_primeSetCutoff_density P
  by_cases hc : primeSetHarmonicDensity P = 0
  · -- Vanishing finite products squeeze every residual sign uniformly.
    rw [hc] at hd ⊢
    apply tendsto_of_eventual_packet_bounds
      (lower := fun Q N => -finiteFlipHarmonicDensity (primeSetCutoff P Q) -
        finitePrimeStrippingCost (primeSetCutoff P Q) / gaugeHarmonicSum (fun _ => 1) N)
      (upper := fun Q N => finiteFlipHarmonicDensity (primeSetCutoff P Q) +
        finitePrimeStrippingCost (primeSetCutoff P Q) / gaugeHarmonicSum (fun _ => 1) N)
      (lowerLimit := fun Q => -finiteFlipHarmonicDensity (primeSetCutoff P Q))
      (upperLimit := fun Q => finiteFlipHarmonicDensity (primeSetCutoff P Q))
    · intro Q
      simpa only [sub_zero] using tendsto_const_nhds.sub
        (const_div_harmonic_tendsto_zero (finitePrimeStrippingCost (primeSetCutoff P Q)))
    · intro Q
      simpa only [add_zero] using tendsto_const_nhds.add
        (const_div_harmonic_tendsto_zero (finitePrimeStrippingCost (primeSetCutoff P Q)))
    · simpa only [neg_zero] using hd.neg
    · exact hd
    · intro Q
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact primeSet_correlation_interval P Q hN
  · -- A positive product pays the residual divisibility defect.
    have hcpos : 0 < primeSetHarmonicDensity P :=
      lt_of_le_of_ne (primeSetHarmonicDensity_bounds P).1 (Ne.symm hc)
    apply tendsto_of_eventual_packet_bounds
      (lower := fun Q N => finiteFlipHarmonicDensity (primeSetCutoff P Q) *
        (1 - 2 * (finiteFlipHarmonicDensity (primeSetCutoff P Q) / primeSetHarmonicDensity P - 1)) -
        finitePrimeStrippingCost (primeSetCutoff P Q) / gaugeHarmonicSum (fun _ => 1) N)
      (upper := fun Q N => finiteFlipHarmonicDensity (primeSetCutoff P Q) +
        finitePrimeStrippingCost (primeSetCutoff P Q) / gaugeHarmonicSum (fun _ => 1) N)
      (lowerLimit := fun Q => finiteFlipHarmonicDensity (primeSetCutoff P Q) *
        (1 - 2 * (finiteFlipHarmonicDensity (primeSetCutoff P Q) / primeSetHarmonicDensity P - 1)))
      (upperLimit := fun Q => finiteFlipHarmonicDensity (primeSetCutoff P Q))
    · intro Q
      simpa only [sub_zero] using tendsto_const_nhds.sub
        (const_div_harmonic_tendsto_zero (finitePrimeStrippingCost (primeSetCutoff P Q)))
    · intro Q
      simpa only [add_zero] using tendsto_const_nhds.add
        (const_div_harmonic_tendsto_zero (finitePrimeStrippingCost (primeSetCutoff P Q)))
    · have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      have ht := hd.mul (hOne.sub
        (((hd.div_const (primeSetHarmonicDensity P)).sub_const 1).const_mul 2))
      simpa only [div_self hc, sub_self, mul_zero, sub_zero, mul_one] using ht
    · exact hd
    · intro Q
      filter_upwards [eventually_ge_atTop (max 1 Q)] with N hN
      have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
      have hQN : Q ≤ N := (le_max_right _ _).trans hN
      refine ⟨?_, (primeSet_correlation_interval P Q hN1).2⟩
      have he := (abs_le.mp (primeSet_stripping_error P Q hN1)).1
      have hm := reciprocal_tail_le_density_ratio P hcpos hQN
      have hcount := primeSetFlip_harmonicCorrelation_ge (P \ Set.Iic Q) hN1
      have htail : 1 - 2 * (finiteFlipHarmonicDensity (primeSetCutoff P Q) /
          primeSetHarmonicDensity P - 1) ≤
            harmonicCorrelation (primeSetFlip (P \ Set.Iic Q)) N := by
        linarith only [hm, hcount]
      have hpaid := mul_le_mul_of_nonneg_left htail
        (finiteFlipHarmonicDensity_pos (primeSetCutoff_prime P Q)).le
      linarith only [he, hpaid]

/-- The full prime-pattern Euler product pays its squared-density gap on
the fixed pole hyperplane. -/
theorem primeSetFlip_hasHyperplaneGap (P : Set ℕ) :
    HasHyperplaneGap (primeSetFlip P) (2 * Real.log 2 * primeSetHarmonicDensity P ^ 2) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨N₀, hN₀⟩ := eventually_prime_gap_ge_squared_correlation hε2
  have hlim := ((primeSetFlip_harmonicCorrelation_tendsto P).pow 2).const_mul (2 * Real.log 2)
  have hevent : ∀ᶠ N : ℕ in atTop,
      2 * Real.log 2 * primeSetHarmonicDensity P ^ 2 - ε / 2 <
        2 * Real.log 2 * harmonicCorrelation (primeSetFlip P) N ^ 2 :=
    hlim.eventually (lt_mem_nhds (sub_lt_self _ hε2))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hevent
  refine ⟨max N₀ N₁, fun N hN x hx => ?_⟩
  have h := hN₀ N ((le_max_left _ _).trans hN) (primeSetFlip P)
    (primeSetFlip_mul_self P) x hx
  have hcoeff := hN₁ N ((le_max_right _ _).trans hN)
  have hmass : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hpay := mul_le_mul_of_nonneg_right hcoeff.le hmass
  linarith only [h, hpay]

end GaloisForLFunctions.ArithmeticCountingPositivity
