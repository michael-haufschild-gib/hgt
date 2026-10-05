import GaloisForLFunctions.RHTower.ChiRamanujanFiniteRationalAtoms
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicPrimeOnlyVaughan
import GaloisForLFunctions.HTGeometry.SquarefreeClockLaw

/-!
# Exact finite prime-square projection of the compensated source

The square-divisor Möbius sum is a zero-one Fourier multiplier at every
integer, including zero. Multiplying the existing compensated source by
this finite sieve gives the exact prime logarithm in the joint limit.
The smooth test is unchanged; no cancellation estimate is asserted.
-/

noncomputable section
open Filter Set ArithmeticFunction
open scoped BigOperators Topology
namespace RHTower.BAGTrace

/-- The finite square-divisor sieve sees exactly the retained prime squares. -/
def ramanujanSquareSieveGcd (P : Finset ℕ) (n : ℕ) : ℕ :=
  (ramanujanPrimeRadical P ^ 2).gcd n

def ramanujanSquareSieveWeight (P : Finset ℕ) (n : ℕ) : ℝ :=
  (moebius (ramanujanSquareSieveGcd P n) : ℝ)^2

/-- The squarefree projector belongs to the source, leaving its test smooth. -/
def ramanujanPrimeOnlyMultiplier (P : Finset ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  ramanujanSquareSieveWeight P n * ramanujanCompensatedMultiplier P ε n

private theorem primeRadical_ne_zero (P : Finset ℕ) : ramanujanPrimeRadical P ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (Finset.mem_filter.mp hp).2.ne_zero

private theorem prime_dvd_radical {P : Finset ℕ} {p : ℕ} (hP : p ∈ P) (hp : p.Prime) :
    p ∣ ramanujanPrimeRadical P := by
  exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hP,hp⟩)

private theorem squareSieveGcd_ne_zero (P : Finset ℕ) (n : ℕ) :
    ramanujanSquareSieveGcd P n ≠ 0 :=
  (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero (pow_ne_zero 2 (primeRadical_ne_zero P)))).ne'

/-- Exact finite Möbius square-divisor identity, valid also at frequency zero. -/
theorem ramanujanSquareSieveWeight_eq_sum (P : Finset ℕ) (n : ℕ) :
    ramanujanSquareSieveWeight P n =
      ∑ d ∈ (ramanujanPrimeRadical P).divisors.filter (fun d => d^2 ∣ n), (moebius d : ℝ) := by
  have hQ := primeRadical_ne_zero P
  have hg := squareSieveGcd_ne_zero P n
  have hf : ((ramanujanPrimeRadical P).divisors.filter (fun d => d^2 ∣ n)) =
      (ramanujanSquareSieveGcd P n).divisors.filter (fun d => d^2 ∣ ramanujanSquareSieveGcd P n) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdQ, _⟩, hdn⟩
      have hdg : d^2 ∣ ramanujanSquareSieveGcd P n :=
        Nat.dvd_gcd (pow_dvd_pow_of_dvd hdQ 2) hdn
      have hdd : d ∣ d^2 := by simpa only [pow_two] using dvd_mul_right d d
      exact ⟨⟨hdd.trans hdg, hg⟩, hdg⟩
    · rintro ⟨_, hdg⟩
      exact ⟨⟨(Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp
        (hdg.trans (Nat.gcd_dvd_left _ _)), hQ⟩, hdg.trans (Nat.gcd_dvd_right _ _)⟩
  rw [hf]
  have h := GaloisForLFunctions.HTGeometry.sum_moebius_sq_dvd hg
  unfold ramanujanSquareSieveWeight
  exact_mod_cast h.symm

theorem ramanujanSquareSieveWeight_eq_indicator (P : Finset ℕ) (n : ℕ) :
    ramanujanSquareSieveWeight P n = if Squarefree (ramanujanSquareSieveGcd P n) then 1 else 0 := by
  by_cases h : Squarefree (ramanujanSquareSieveGcd P n)
  · rw [if_pos h, ramanujanSquareSieveWeight]
    exact_mod_cast moebius_sq_eq_one_of_squarefree h
  · simp [ramanujanSquareSieveWeight,h,moebius_eq_zero_of_not_squarefree h]

theorem ramanujanSquareSieveWeight_bounds (P : Finset ℕ) (n : ℕ) :
    0 ≤ ramanujanSquareSieveWeight P n ∧ ramanujanSquareSieveWeight P n ≤ 1 := by
  rw [ramanujanSquareSieveWeight_eq_indicator]
  split_ifs <;> norm_num

private theorem squarefree_squareSieveGcd_iff {P : Finset ℕ} {n : ℕ}
    (h2 : 2 ∈ P) (hP : n.primeFactors ⊆ P) :
    Squarefree (ramanujanSquareSieveGcd P n) ↔ Squarefree n := by
  by_cases hn : n = 0
  · subst n
    have h0 : ¬ Squarefree (0 : ℕ) := fun h =>
      Nat.squarefree_iff_prime_squarefree.mp h 2 Nat.prime_two (dvd_zero _)
    have hg0 : ¬ Squarefree (ramanujanSquareSieveGcd P 0) := by
      intro h
      apply Nat.squarefree_iff_prime_squarefree.mp h 2 Nat.prime_two
      simpa only [ramanujanSquareSieveGcd, Nat.gcd_zero_right, pow_two] using
        pow_dvd_pow_of_dvd (prime_dvd_radical h2 Nat.prime_two) 2
    simp [h0,hg0]
  · constructor
    · intro h
      apply Nat.squarefree_iff_prime_squarefree.mpr
      intro p hp hpn
      have hpP : p ∈ P := hP (Nat.mem_primeFactors.mpr
        ⟨hp,(dvd_mul_right p p).trans hpn,hn⟩)
      apply Nat.squarefree_iff_prime_squarefree.mp h p hp
      have hpQ := pow_dvd_pow_of_dvd (prime_dvd_radical hpP hp) 2
      apply Nat.dvd_gcd
      · simpa only [pow_two] using hpQ
      · exact hpn
    · intro h
      exact Squarefree.squarefree_of_dvd (Nat.gcd_dvd_right _ _) h

/-- Eventual exactness of the finite prime-square sieve, including zero. -/
theorem eventually_ramanujanSquareSieveWeight (n : ℕ) :
    ∀ᶠ P : Finset ℕ in atTop,
      ramanujanSquareSieveWeight P n = if Squarefree n then 1 else 0 := by
  filter_upwards [eventually_ge_atTop (insert 2 n.primeFactors)] with P hP
  have h2 : 2 ∈ P := hP (Finset.mem_insert_self _ _)
  have hp : n.primeFactors ⊆ P := fun p hp => hP (Finset.mem_insert_of_mem hp)
  simp only [ramanujanSquareSieveWeight_eq_indicator, squarefree_squareSieveGcd_iff h2 hp]

/-- The critical limit is the EXACT prime logarithm; all proper prime powers disappear. -/
theorem tendsto_ramanujanPrimeOnlyMultiplier (n : ℕ) :
    Tendsto (fun z : Finset ℕ × ℝ => ramanujanPrimeOnlyMultiplier z.1 z.2 n)
      (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (if n.Prime then Real.log n else 0)) := by
  have hw : Tendsto (fun z : Finset ℕ × ℝ => ramanujanSquareSieveWeight z.1 n)
      (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (if Squarefree n then (1 : ℝ) else 0)) := by
    have he : ∀ᶠ z : Finset ℕ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ),
        ramanujanSquareSieveWeight z.1 n = if Squarefree n then 1 else 0 :=
      tendsto_fst.eventually (eventually_ramanujanSquareSieveWeight n)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with z hz
    exact hz.symm
  have ht := hw.mul (tendsto_ramanujanCompensatedMultiplier n)
  have he : (if Squarefree n then (1 : ℝ) else 0) * vonMangoldt n =
      if n.Prime then Real.log n else 0 := by
    rw [← RHTower.Sieve.vaughanSquarefreePart_vonMangoldt n]
    by_cases h : Squarefree n <;> simp [RHTower.Sieve.vaughanSquarefreePart,h]
  simpa only [ramanujanPrimeOnlyMultiplier,he] using ht

/-- The same polynomial envelope survives the exact arithmetic projector. -/
theorem ramanujanPrimeOnlyMultiplier_bounds {P : Finset ℕ}
    (h2 : 2 ∈ P) (h3 : 3 ∈ P) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ) :
    0 ≤ ramanujanPrimeOnlyMultiplier P ε n ∧
      ramanujanPrimeOnlyMultiplier P ε n ≤ 6*(1+(n : ℝ)) := by
  obtain ⟨hw0,hw1⟩ := ramanujanSquareSieveWeight_bounds P n
  obtain ⟨hk0,hk1⟩ := ramanujanCompensatedMultiplier_nat_bound h2 h3 hε hε1 n
  refine ⟨mul_nonneg hw0 hk0, ?_⟩
  exact (mul_le_mul_of_nonneg_right hw1 hk0).trans (by simpa only [one_mul] using hk1)

/-- Every integer in the covered finite band has its exact squarefree divisor-source value. -/
theorem ramanujanPrimeOnlyMultiplier_range (ε : ℝ) (M : ℕ)
    {n : ℕ} (hn : 1 < n) (hM : n ≤ M) :
    ramanujanPrimeOnlyMultiplier (Finset.range (M+1)) ε n =
      if Squarefree n then pmPowerDampedDivisorCoeff ε n / ε else 0 := by
  have h2 : 2 ∈ Finset.range (M+1) := Finset.mem_range.mpr (by omega)
  have hP : n.primeFactors ⊆ Finset.range (M+1) := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      ((Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans hM))
  simp only [ramanujanPrimeOnlyMultiplier, ramanujanSquareSieveWeight_eq_indicator,
    squarefree_squareSieveGcd_iff h2 hP, ramanujanCompensatedMultiplier_range ε M hn hM]
  split_ifs <;> simp

end RHTower.BAGTrace
