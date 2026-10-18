import GaloisForLFunctions.RHTower.PMAdjacentDivisorCorrelation

/-!
# Euler product of the adjacent divisor correlation

Coprimality at consecutive integers excludes the common-prime state. The resulting local
factor is `1 - p⁻¹⁻ε - p⁻¹⁻η`, including for arbitrarily small positive damping.
-/

open Filter Topology Finset ArithmeticFunction

noncomputable section
namespace RHTower

private theorem pm_dampedMobius_prime (f : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    DampedMobius.dampedMobius f p = -f p := by
  simpa using DampedMobius.dampedMobius_apply_prime_pow f hp (k := 1)

private theorem pm_dampedMobius_coprime_convolution (f g : ℕ → ℝ) (n : ℕ) :
    (∑ z ∈ n.divisorsAntidiagonal,
      if z.1.Coprime z.2 then
        DampedMobius.dampedMobius f z.1 * DampedMobius.dampedMobius g z.2 else 0) =
      DampedMobius.dampedMobius (fun p => f p + g p) n := by
  by_cases hn : Squarefree n
  · have hs :
        (∑ z ∈ n.divisorsAntidiagonal,
          if z.1.Coprime z.2 then
            DampedMobius.dampedMobius f z.1 * DampedMobius.dampedMobius g z.2 else 0) =
          (DampedMobius.dampedMobius f * DampedMobius.dampedMobius g) n := by
      rw [ArithmeticFunction.mul_apply]
      apply sum_congr rfl
      intro z hz
      have hzprod := (Nat.mem_divisorsAntidiagonal.mp hz).1
      exact if_pos (Nat.coprime_of_squarefree_mul (hzprod.symm ▸ hn))
    rw [hs, ← (DampedMobius.isMultiplicative_dampedMobius f).prodPrimeFactors_add_of_squarefree
      (DampedMobius.isMultiplicative_dampedMobius g) hn, prodPrimeFactors_apply hn.ne_zero,
      ← (DampedMobius.isMultiplicative_dampedMobius (fun p => f p + g p)).prod_primeFactors hn]
    apply prod_congr rfl
    intro p hp
    simp only [ArithmeticFunction.add_apply, pm_dampedMobius_prime _ (Nat.prime_of_mem_primeFactors hp)]
    ring
  · have hzero : DampedMobius.dampedMobius (fun p => f p + g p) n = 0 := by
      simp [DampedMobius.dampedMobius, pmul_apply, intCoe_apply, moebius_eq_zero_of_not_squarefree hn]
    rw [hzero]
    apply sum_eq_zero
    intro z hz
    split_ifs with hc
    · by_cases h1 : Squarefree z.1
      · have h2 : ¬Squarefree z.2 := by
          intro h2
          apply hn
          rw [← (Nat.mem_divisorsAntidiagonal.mp hz).1]
          exact (Nat.squarefree_mul hc).mpr ⟨h1, h2⟩
        simp [DampedMobius.dampedMobius, pmul_apply, intCoe_apply,
          moebius_eq_zero_of_not_squarefree h2]
      · simp [DampedMobius.dampedMobius, pmul_apply, intCoe_apply,
          moebius_eq_zero_of_not_squarefree h1]
    · rfl

private def pmAdjacentPairTerm (ε η : ℝ) (z : ℕ × ℕ) : ℝ :=
  if z.1.Coprime z.2 then
    ((moebius z.1 : ℝ) * (z.1 : ℝ) ^ (-η) / z.1) *
      ((moebius z.2 : ℝ) * (z.2 : ℝ) ^ (-ε) / z.2) else 0

private theorem pmAdjacentPairTerm_summable {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    Summable (pmAdjacentPairTerm ε η) := by
  apply Summable.of_norm_bounded
    (summable_mul_of_summable_norm (pm_summable_real_mobius_reciprocal hη).norm
      (pm_summable_real_mobius_reciprocal hε).norm).norm
  intro z
  dsimp only [pmAdjacentPairTerm]
  split_ifs
  · simp
  · rw [norm_zero]
    exact norm_nonneg _

private theorem pmAdjacentDivisorDensity_eq_pair_tsum {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    pmAdjacentDivisorDensity ε η = ∑' z : ℕ × ℕ, pmAdjacentPairTerm ε η z := by
  rw [pmAdjacentDivisorDensity, (pmAdjacentPairTerm_summable hε hη).tsum_prod]
  apply tsum_congr
  intro d
  rw [← tsum_mul_left]
  apply tsum_congr
  intro a
  dsimp only [pmAdjacentPairTerm]
  by_cases hc : a.Coprime d
  · rw [if_pos hc, if_pos hc.symm]
    ring
  · rw [if_neg hc, if_neg (fun h => hc h.symm)]
    ring

/-- The squarefree coefficient whose local weight records either of two adjacent divisibilities. -/
def pmAdjacentEulerCoeff (ε η : ℝ) : ArithmeticFunction ℝ :=
  DampedMobius.dampedMobius (fun p => (p : ℝ) ^ (-η) + (p : ℝ) ^ (-ε))

private theorem pmAdjacentPairTerm_fiber (ε η : ℝ) (n : ℕ) :
    (∑' z : (fun z : ℕ × ℕ => z.1 * z.2) ⁻¹' {n}, pmAdjacentPairTerm ε η z) =
      pmAdjacentEulerCoeff ε η n / (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    have hz (z : (fun z : ℕ × ℕ => z.1 * z.2) ⁻¹' {0}) :
        pmAdjacentPairTerm ε η z = 0 := by
      have h : z.val.1 = 0 ∨ z.val.2 = 0 := mul_eq_zero.mp z.property
      rcases h with h | h <;> simp [pmAdjacentPairTerm, h]
    simp [hz]
  · rw [show (fun z : ℕ × ℕ => z.1 * z.2) ⁻¹' {n} = n.divisorsAntidiagonal by
      ext z; simp [Nat.mem_divisorsAntidiagonal, hn],
      Finset.tsum_subtype']
    have hterm (z : ℕ × ℕ) (hz : z ∈ n.divisorsAntidiagonal) :
        pmAdjacentPairTerm ε η z =
          (if z.1.Coprime z.2 then
            DampedMobius.dampedMobius (fun p => (p : ℝ) ^ (-η)) z.1 *
              DampedMobius.dampedMobius (fun p => (p : ℝ) ^ (-ε)) z.2 else 0) / n := by
      have hnprod := (Nat.mem_divisorsAntidiagonal.mp hz).1
      rw [pmAdjacentPairTerm, pm_dampedMobius_rpow, pm_dampedMobius_rpow]
      split_ifs
      · rw [← hnprod, Nat.cast_mul]
        ring
      · simp
    rw [sum_congr rfl hterm, ← sum_div, pm_dampedMobius_coprime_convolution]
    rfl

/-- Absolute convergence and value of the Euler coefficient series, obtained from coprime fibres. -/
theorem pmAdjacentEulerCoeff_hasSum {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    HasSum (fun n : ℕ => pmAdjacentEulerCoeff ε η n / (n : ℝ))
      (pmAdjacentDivisorDensity ε η) := by
  rw [pmAdjacentDivisorDensity_eq_pair_tsum hε hη]
  have h := (pmAdjacentPairTerm_summable hε hη).hasSum.tsum_fiberwise
    (fun z : ℕ × ℕ => z.1 * z.2)
  simpa only [pmAdjacentPairTerm_fiber] using h

/-- The complete adjacent correlation has the local factor with no common-prime state. -/
theorem pmAdjacentDivisorDensity_hasProd {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    HasProd (fun p : Nat.Primes =>
      1 - ((p : ℝ) ^ (-ε) + (p : ℝ) ^ (-η)) / p)
      (pmAdjacentDivisorDensity ε η) := by
  let a := pmAdjacentEulerCoeff ε η
  have hm : a.IsMultiplicative := DampedMobius.isMultiplicative_dampedMobius _
  have h1 : a 1 / ((1 : ℕ) : ℝ) = 1 := by simpa using hm.map_one
  have hmul {m n : ℕ} (hc : m.Coprime n) :
      a (m * n) / ((m * n : ℕ) : ℝ) = (a m / (m : ℝ)) * (a n / (n : ℝ)) := by
    rw [hm.map_mul_of_coprime hc, Nat.cast_mul]
    ring
  have hs := pmAdjacentEulerCoeff_hasSum hε hη
  have hp := EulerProduct.eulerProduct_hasProd h1 (fun {_ _} h => hmul h)
    hs.summable.norm (by simp)
  rw [hs.tsum_eq] at hp
  apply hp.congr_fun
  intro p
  rw [tsum_eq_sum (s := {0, 1}) (fun k hk => ?_)]
  · simp [pmAdjacentEulerCoeff, DampedMobius.dampedMobius_apply_prime_pow, p.property]
    ring
  · have hk0 : k ≠ 0 := fun h => hk (by simp [h])
    have hk1 : k ≠ 1 := fun h => hk (by simp [h])
    simp [pmAdjacentEulerCoeff, DampedMobius.dampedMobius_apply_prime_pow,
      p.property, hk0, hk1]

end RHTower
