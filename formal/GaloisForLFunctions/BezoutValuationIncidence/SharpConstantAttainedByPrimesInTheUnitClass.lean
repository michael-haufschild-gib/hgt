import GaloisForLFunctions.BezoutValuationIncidence.CrossScaleParityBlindnessOfThePronicGram

/-!
# The sharp constant is attained by primes in the unit class

The Bernoulli kernel at the residue one is within `O(d log d)` of its maximum. Write
`𝔅(d, 1) = Φ_d(0) ζ(2) - Σ_j (Φ_d(0) - Φ_d(j))/j²` and use `Φ_d(0) - Φ_d(j) = ρ(d-ρ)/2 ≤ min(jd/2, d²/8)`,
`ρ = j mod d`. The deficit is at most `(d/2) h_d + d/8`, so

`π²(d² - 1)/72 - (d/2)(h_d + 1/4) ≤ 𝔅(d, 1) ≤ π²(d² - 1)/72`.

For a prime `p` and a prime `q ≡ 1 (mod p)` the kernel is `𝔅(p, q) = 𝔅(p, 1)`. By Dirichlet's theorem
there are such primes `q` beyond every bound. Hence for every prime `p` there are arbitrarily large primes
`q` with

`𝒢^{ec}(p, q) - [D_p log q - p β_p] ≥ (π²(p² - 1)/72 - (p/2)(h_p + 1/4))/q - ¾ p³/q²`,

against the universal upper bound `π²(p² - 1)/(72q) + ¾ p³/q²`. The extremal second-order coupling
`π²p²/(72q)` of the pronic Gram is realised within the primes, by the Bézout seeds `q ≡ 1 (mod p)`.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The deficit of the potential from its maximum: `Φ_d(0) - Φ_d(j) ≤ jd/2` and `≤ d²/8`. -/
theorem residuePotential_deficit_le {d : ℕ} (hd : 0 < d) (j : ℕ) :
    residuePotential d 0 - residuePotential d j ≤ (j : ℝ) * d / 2 ∧
      residuePotential d 0 - residuePotential d j ≤ (d : ℝ) ^ 2 / 8 := by
  have hlt := Nat.mod_lt j hd
  have hρ0 : (0 : ℝ) ≤ ((j % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hρd : ((j % d : ℕ) : ℝ) ≤ d := by exact_mod_cast hlt.le
  have hρj : ((j % d : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.mod_le j d
  have e : residuePotential d 0 - residuePotential d j =
      ((j % d : ℕ) : ℝ) * ((d : ℝ) - ((j % d : ℕ) : ℝ)) / 2 := by
    simp only [residuePotential, Nat.zero_mod, Nat.cast_zero, zero_mul, zero_div, sub_zero]; ring
  rw [e]
  constructor
  · have : ((j % d : ℕ) : ℝ) * ((d : ℝ) - ((j % d : ℕ) : ℝ)) ≤ (j : ℝ) * d := by nlinarith
    linarith
  · nlinarith [sq_nonneg ((d : ℝ) - 2 * ((j % d : ℕ) : ℝ))]

/-- **The kernel at the residue one.** `𝔅(d, 1) ≥ π²(d² - 1)/72 - (d/2)(h_d + 1/4)`. -/
theorem bernoulliKernel_one_ge {d : ℕ} (hd : 1 ≤ d) :
    Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 - (d : ℝ) / 2 * (∑ k ∈ Icc 1 d, 1 / (k : ℝ) + 1 / 4) ≤
      bernoulliKernel d 1 := by
  have hd0 : 0 < d := hd
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hB := hasSum_bernoulliKernel hd0 1
  -- deficit series
  set δ : ℕ → ℝ := fun j => (residuePotential d 0 - residuePotential d ((j + 1) * 1)) / ((j : ℝ) + 1) ^ 2
  have hδsum : HasSum δ (residuePotential d 0 * (Real.pi ^ 2 / 6) - bernoulliKernel d 1) := by
    have := (hz.mul_left (residuePotential d 0)).sub hB
    refine this.congr_fun fun j => ?_
    simp only [δ]; ring
  have hδ0 : ∀ j, 0 ≤ δ j := fun j => div_nonneg (by
    have := residuePotential_le_zero_value hd0 ((j + 1) * 1); linarith) (by positivity)
  have hδbound : ∀ K, ∑ j ∈ range K, δ j ≤ (d : ℝ) / 2 * (∑ k ∈ Icc 1 d, 1 / (k : ℝ) + 1 / 4) := by
    intro K
    have hpt : ∀ j ∈ range K, δ j ≤ (d : ℝ) / 2 * (if j < d then 1 / ((j : ℝ) + 1) else 0) +
        (d : ℝ) ^ 2 / 8 * (if d ≤ j then 1 / ((j : ℝ) + 1) ^ 2 else 0) := by
      intro j _
      obtain ⟨h1, h2⟩ := residuePotential_deficit_le hd0 ((j + 1) * 1)
      have hpos : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 := by positivity
      simp only [δ]
      split_ifs with hjd hdj hdj
      · omega
      · rw [mul_zero, add_zero, div_le_iff₀ hpos]
        push_cast at h1
        have : (d : ℝ) / 2 * (1 / ((j : ℝ) + 1)) * ((j : ℝ) + 1) ^ 2 = ((j : ℝ) + 1) * d / 2 := by
          field_simp
        rw [this]; linarith
      · rw [mul_zero, zero_add, div_le_iff₀ hpos]
        have : (d : ℝ) ^ 2 / 8 * (1 / ((j : ℝ) + 1) ^ 2) * ((j : ℝ) + 1) ^ 2 = (d : ℝ) ^ 2 / 8 := by
          field_simp
        rw [this]; linarith
      · omega
    have hhead : ∑ j ∈ range K, (if j < d then 1 / ((j : ℝ) + 1) else 0) ≤ ∑ k ∈ Icc 1 d, 1 / (k : ℝ) := by
      rw [← sum_range_inv_eq d, ← sum_filter]
      exact sum_le_sum_of_subset_of_nonneg (fun j hj => mem_range.mpr (mem_filter.mp hj).2)
        fun _ _ _ => by positivity
    have htail := sum_range_ite_ge_div_sq_le hd K
    calc ∑ j ∈ range K, δ j
        ≤ ∑ j ∈ range K, ((d : ℝ) / 2 * (if j < d then 1 / ((j : ℝ) + 1) else 0) +
            (d : ℝ) ^ 2 / 8 * (if d ≤ j then 1 / ((j : ℝ) + 1) ^ 2 else 0)) := sum_le_sum hpt
      _ = (d : ℝ) / 2 * ∑ j ∈ range K, (if j < d then 1 / ((j : ℝ) + 1) else 0) +
            (d : ℝ) ^ 2 / 8 * ∑ j ∈ range K, (if d ≤ j then 1 / ((j : ℝ) + 1) ^ 2 else 0) := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ (d : ℝ) / 2 * ∑ k ∈ Icc 1 d, 1 / (k : ℝ) + (d : ℝ) ^ 2 / 8 * (1 / (d : ℝ)) := by
          gcongr
      _ = (d : ℝ) / 2 * (∑ k ∈ Icc 1 d, 1 / (k : ℝ) + 1 / 4) := by field_simp; ring
  have hle := Real.tsum_le_of_sum_range_le hδ0 hδbound
  rw [hδsum.tsum_eq] at hle
  have h0 : residuePotential d 0 = ((d : ℝ) ^ 2 - 1) / 12 := by simp [residuePotential]
  rw [h0] at hle
  linarith

/-- **Attained by primes.** For every prime `p` and every bound `n` there is a prime `q > n`,
`q ≡ 1 (mod p)`, whose second-order coupling with `p` is at least
`(π²(p² - 1)/72 - (p/2)(h_p + 1/4))/q - ¾ p³/q²`. -/
theorem exists_prime_second_order_ge (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ∃ q > n, q.Prime ∧ q % p = 1 ∧ ∀ N, q ≤ N →
      (Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 72 - (p : ℝ) / 2 * (∑ k ∈ Icc 1 p, 1 / (k : ℝ) + 1 / 4)) / q -
          3 / 4 * (p : ℝ) ^ 3 / (q : ℝ) ^ 2 ≤
        pmRamanujanEnergyCenteredGram p q - ((((p : ℝ) - 1) / 2 - Real.log p) * Real.log q -
          p * rowBeta N (unitRow p)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨q, hqn, hq, hq1⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := p) (a := 1) isUnit_one
    (max n p)
  have hqmod : q % p = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' q 1 p).mp (by rw [hq1, Nat.cast_one])
    rw [this, Nat.mod_eq_of_lt hp.one_lt]
  refine ⟨q, lt_of_le_of_lt (le_max_left _ _) hqn, hq, hqmod, fun N hqN => ?_⟩
  have hpq : p < q := lt_of_le_of_lt (le_max_right _ _) hqn
  have h := abs_pmRamanujanEnergyCenteredGram_sub_second_order_le hp hq (hpq.le.trans hqN) hqN
  have hk : bernoulliKernel p q = bernoulliKernel p 1 := by rw [bernoulliKernel_mod, hqmod]
  have hlow := bernoulliKernel_one_ge hp.one_lt.le
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hdiv := div_le_div_of_nonneg_right hlow hqR.le
  rw [← hk] at hdiv
  have := (abs_le.mp h).1
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
