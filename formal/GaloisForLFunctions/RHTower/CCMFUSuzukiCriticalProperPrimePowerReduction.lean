import GaloisForLFunctions.RHTower.PrimeLagLandauPrimesOnly
import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalRemainderVariation
import GaloisForLFunctions.HTGeometry.ReciprocalLogPowerTailGeneral

/-!
# Proper-prime-power reduction for the critical Suzuki FU reporter

The moving critical triangular reporter retains the literal von Mangoldt--polar
source.  This file isolates its proper-prime-power sector without touching the
valuation-one prime--polar cancellation: after critical rescaling, each
`p^(j+2)` atom is dominated by a reciprocal-log-square prime tail times a
geometric exponent tail.  Thus proper powers have one height-independent
budget, and the remaining unboundedness problem is exactly the true-prime
versus polar current.
-/

open Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Static critical majorant on proper prime powers. -/
def suzukiCheckpointCriticalProperPrimePowerWeight (n : ℕ) : ℝ :=
  if IsProperPrimePow n then
    1 / (Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ (2 : ℕ))
  else 0

private theorem exp_one_le_three : Real.exp 1 ≤ (3 : ℝ) := by
  have h : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  norm_num at h ⊢
  linarith

/-- The reciprocal-log-square tail restricted to primes is summable.  The proof
uses the all-integer integral-test tail after the injective shift `p ↦ p - 2`. -/
private theorem summable_prime_reciprocal_log_sq :
    Summable (fun p : Nat.Primes =>
      1 / ((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ))) := by
  let g : ℕ → ℝ := fun i =>
    1 / ((3 + ((i : ℝ) + 1)) * Real.log (3 + ((i : ℝ) + 1)) ^ (2 : ℕ))
  have hg : Summable g :=
    GaloisForLFunctions.HTGeometry.summable_one_div_mul_log_pow_succ
      (p := 1) (by omega) exp_one_le_three
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ) - 2) := by
    intro p q hpq
    apply Subtype.ext
    change (p : ℕ) - 2 = (q : ℕ) - 2 at hpq
    have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
    have hq2 : 2 ≤ (q : ℕ) := q.2.two_le
    omega
  have hcomp : Summable (fun p : Nat.Primes => g ((p : ℕ) - 2)) :=
    hg.comp_injective hinj
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hcomp.mul_left 8)
  · have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.2.one_lt)
    positivity
  · have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
    have hp0 : (0 : ℝ) < (p : ℕ) := by linarith
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.2.one_lt)
    have hshift : (p : ℝ) + 2 ≤ (p : ℝ) * (p : ℝ) := by nlinarith
    have hlogshift : Real.log ((p : ℝ) + 2) ≤ 2 * Real.log (p : ℝ) := by
      calc
        Real.log ((p : ℝ) + 2) ≤ Real.log ((p : ℝ) * (p : ℝ)) :=
          Real.strictMonoOn_log.monotoneOn
            (show 0 < (p : ℝ) + 2 by linarith)
            (show 0 < (p : ℝ) * (p : ℝ) by positivity) hshift
        _ = 2 * Real.log (p : ℝ) := by rw [Real.log_mul hp0.ne' hp0.ne']; ring
    have hlogshift0 : 0 ≤ Real.log ((p : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    have hlogsq : Real.log ((p : ℝ) + 2) ^ (2 : ℕ) ≤ 4 * Real.log (p : ℝ) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (Real.log ((p : ℝ) + 2) - 2 * Real.log (p : ℝ))]
    have hlinear : (p : ℝ) + 2 ≤ 2 * (p : ℝ) := by linarith
    have hden : ((p : ℝ) + 2) * Real.log ((p : ℝ) + 2) ^ (2 : ℕ) ≤
        8 * ((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ)) := by
      calc
        ((p : ℝ) + 2) * Real.log ((p : ℝ) + 2) ^ (2 : ℕ) ≤
            (2 * (p : ℝ)) * (4 * Real.log (p : ℝ) ^ (2 : ℕ)) := by gcongr
        _ = 8 * ((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ)) := by ring
    have hden0 : 0 < ((p : ℝ) + 2) * Real.log ((p : ℝ) + 2) ^ (2 : ℕ) := by
      have : 0 < Real.log ((p : ℝ) + 2) := Real.log_pos (by linarith)
      positivity
    change 1 / ((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ)) ≤
      8 * g ((p : ℕ) - 2)
    dsimp only [g]
    rw [Nat.cast_sub p.2.two_le]
    norm_num
    rw [show (3 + (((p : ℝ) - 2) + 1)) = (p : ℝ) + 2 by ring]
    have hratio : 1 / ((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ)) ≤
        8 / (((p : ℝ) + 2) * Real.log ((p : ℝ) + 2) ^ (2 : ℕ)) :=
      (div_le_div_iff₀ (by positivity) hden0).mpr (by nlinarith)
    convert hratio using 1 <;> field_simp

private def suzukiCheckpointCriticalProperPrimePowerMajor
    (pk : Nat.Primes × ℕ) : ℝ :=
  (1 / ((pk.1 : ℝ) * Real.log (pk.1 : ℝ) ^ (2 : ℕ))) * (3 / 4 : ℝ) ^ pk.2

private theorem summable_suzukiCheckpointCriticalProperPrimePowerMajor :
    Summable suzukiCheckpointCriticalProperPrimePowerMajor := by
  let f : Nat.Primes → ℝ := fun p =>
    1 / ((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ))
  let g : ℕ → ℝ := fun j => (3 / 4 : ℝ) ^ j
  have hf : Summable f := summable_prime_reciprocal_log_sq
  have hg : Summable g := summable_geometric_of_norm_lt_one (by
    rw [Real.norm_eq_abs]
    norm_num)
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    dsimp only [f]
    have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.2.one_lt)
    positivity
  have hg0 : ∀ j, 0 ≤ g j := by
    intro j
    dsimp only [g]
    positivity
  change Summable (fun pk : Nat.Primes × ℕ => f pk.1 * g pk.2)
  exact hf.mul_of_nonneg hg hf0 hg0

private theorem sqrt_pow_lower_geometric (p j : ℕ) (hp : 2 ≤ p) :
    (p : ℝ) * (4 / 3 : ℝ) ^ j ≤
      Real.sqrt (((p ^ (j + 2) : ℕ) : ℝ)) := by
  apply Real.le_sqrt_of_sq_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hbase : (16 / 9 : ℝ) ≤ (p : ℝ) := by linarith
  have hpow : (16 / 9 : ℝ) ^ j ≤ (p : ℝ) ^ j :=
    pow_le_pow_left₀ (by norm_num) hbase j
  calc
    ((p : ℝ) * (4 / 3 : ℝ) ^ j) ^ (2 : ℕ) =
        (p : ℝ) ^ (2 : ℕ) * (16 / 9 : ℝ) ^ j := by
      rw [mul_pow]
      congr 1
      calc
        ((4 / 3 : ℝ) ^ j) ^ (2 : ℕ) = ((4 / 3 : ℝ) ^ (2 : ℕ)) ^ j := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
        _ = (16 / 9 : ℝ) ^ j := by norm_num
    _ ≤ (p : ℝ) ^ (2 : ℕ) * (p : ℝ) ^ j :=
      mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    _ = (p : ℝ) ^ (j + 2) := by
      rw [← pow_add]
      congr 1
      omega
    _ = (((p ^ (j + 2) : ℕ) : ℝ)) := by norm_cast

private theorem suzukiCheckpointCriticalProperPrimePowerWeight_comp_le_major
    (pk : Nat.Primes × ℕ) :
    suzukiCheckpointCriticalProperPrimePowerWeight (properPowMap pk) ≤
      suzukiCheckpointCriticalProperPrimePowerMajor pk := by
  rcases pk with ⟨p, j⟩
  have hproper : IsProperPrimePow ((p : ℕ) ^ (j + 2)) :=
    isProperPrimePow_iff.mpr ⟨p, p.2, j, rfl⟩
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hpow0 : (0 : ℝ) < (((p : ℕ) ^ (j + 2) : ℕ) : ℝ) := by positivity
  have hlogpow : Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) =
      ((j : ℝ) + 2) * Real.log (p : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  have hloglower : Real.log (p : ℝ) ≤
      Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) := by
    rw [hlogpow]
    nlinarith
  have hlogsq : Real.log (p : ℝ) ^ (2 : ℕ) ≤
      Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg
      (Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) - Real.log (p : ℝ))]
  have hsqrt := sqrt_pow_lower_geometric (p : ℕ) j hp2
  have hsqrt0 : 0 < Real.sqrt ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) :=
    Real.sqrt_pos.mpr hpow0
  have hden : (p : ℝ) * (4 / 3 : ℝ) ^ j * Real.log (p : ℝ) ^ (2 : ℕ) ≤
      Real.sqrt ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) *
        Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) ^ (2 : ℕ) := by
    have hleft0 : 0 ≤ (p : ℝ) * (4 / 3 : ℝ) ^ j := by positivity
    have hright0 : 0 ≤ Real.sqrt ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) :=
      Real.sqrt_nonneg _
    calc
      (p : ℝ) * (4 / 3 : ℝ) ^ j * Real.log (p : ℝ) ^ (2 : ℕ) ≤
          Real.sqrt ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) * Real.log (p : ℝ) ^ (2 : ℕ) := by
        gcongr
      _ ≤ Real.sqrt ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) *
          Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) ^ (2 : ℕ) := by
        gcongr
  have hden0 : 0 < (p : ℝ) * (4 / 3 : ℝ) ^ j * Real.log (p : ℝ) ^ (2 : ℕ) := by
    positivity
  unfold suzukiCheckpointCriticalProperPrimePowerWeight
    suzukiCheckpointCriticalProperPrimePowerMajor properPowMap
  rw [if_pos hproper]
  have hrecip :
      1 / (Real.sqrt ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) *
        Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) ^ (2 : ℕ)) ≤
        1 / ((p : ℝ) * (4 / 3 : ℝ) ^ j * Real.log (p : ℝ) ^ (2 : ℕ)) :=
    one_div_le_one_div_of_le hden0 hden
  calc
    1 / (Real.sqrt ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) *
        Real.log ((((p : ℕ) ^ (j + 2) : ℕ) : ℝ)) ^ (2 : ℕ)) ≤
        1 / ((p : ℝ) * (4 / 3 : ℝ) ^ j * Real.log (p : ℝ) ^ (2 : ℕ)) := hrecip
    _ = (1 / ((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ))) * (3 / 4 : ℝ) ^ j := by
      have hpow : (4 / 3 : ℝ) ^ j * (3 / 4 : ℝ) ^ j = 1 := by
        rw [← mul_pow]
        norm_num
      field_simp
      rw [hpow]

private theorem suzukiCheckpointCriticalProperPrimePowerWeight_nonneg (n : ℕ) :
    0 ≤ suzukiCheckpointCriticalProperPrimePowerWeight n := by
  unfold suzukiCheckpointCriticalProperPrimePowerWeight
  split_ifs <;> positivity

private theorem suzukiCheckpointCriticalProperPrimePowerWeight_eq_zero_of_notMem_range
    {n : ℕ} (hn : n ∉ Set.range properPowMap) :
    suzukiCheckpointCriticalProperPrimePowerWeight n = 0 := by
  unfold suzukiCheckpointCriticalProperPrimePowerWeight
  rw [if_neg]
  intro hproper
  obtain ⟨p, hp, j, rfl⟩ := isProperPrimePow_iff.mp hproper
  exact hn ⟨(⟨p, hp⟩, j), rfl⟩

/-- Proper prime powers have a single unconditional critical FU mass budget. -/
theorem summable_suzukiCheckpointCriticalProperPrimePowerWeight :
    Summable suzukiCheckpointCriticalProperPrimePowerWeight := by
  rw [← properPow_injective.summable_iff
    (fun n hn => suzukiCheckpointCriticalProperPrimePowerWeight_eq_zero_of_notMem_range hn)]
  exact Summable.of_nonneg_of_le
    (fun pk => suzukiCheckpointCriticalProperPrimePowerWeight_nonneg _)
    suzukiCheckpointCriticalProperPrimePowerWeight_comp_le_major
    summable_suzukiCheckpointCriticalProperPrimePowerMajor

/-- Literal proper-prime-power atomic sector of the critical moving FU source. -/
def suzukiCheckpointCriticalProperPrimePowerAtomicAction (H : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
    (if IsProperPrimePow (j + 3) then
        ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)
      else 0) * suzukiCheckpointCriticalTriangularMultiplier H j

/-- Literal valuation-one-prime minus polar sector of the critical moving FU source. -/
def suzukiCheckpointCriticalPrimeOnlyPolarAction (H : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
    ((if Nat.Prime (j + 3) then
        ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)
      else 0) -
      (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ))) *
        suzukiCheckpointCriticalTriangularMultiplier H j

/-- Literal completed prime-minus-polar finite source sum. -/
def suzukiCheckpointCriticalPrimePolarAction (H : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
    (ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ) -
      (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ))) *
        suzukiCheckpointCriticalTriangularMultiplier H j

private theorem vonMangoldt_div_eq_prime_add_properPrimePower
    (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / (n : ℝ) =
      (if Nat.Prime n then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0) +
        (if IsProperPrimePow n then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0) := by
  by_cases hp : Nat.Prime n
  · have hproper : ¬ IsProperPrimePow n := fun h => h.2 hp
    simp [hp, hproper]
  · by_cases hproper : IsProperPrimePow n
    · simp [hp, hproper]
    · have hnotpow : ¬ IsPrimePow n := by
        intro hpow
        exact hproper ⟨hpow, hp⟩
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnotpow, zero_div]
      simp [hp, hproper]

/-- One literal prime--polar increment splits into its valuation-one codiagonal and the proper
prime-power atom.  This is an identity of cells, before either term is estimated. -/
theorem suzukiCheckpointCriticalPrimePolarIncrement_eq_primeOnly_add_properPrimePower
    (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / (n : ℝ) -
        (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) =
      ((if Nat.Prime n then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0) -
        (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ))) +
        (if IsProperPrimePow n then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0) := by
  nth_rewrite 1 [vonMangoldt_div_eq_prime_add_properPrimePower n]
  ring

/-- Exact source-faithful split: no polar term is moved or estimated. -/
theorem suzukiCheckpointCriticalPrimePolarAction_eq_primeOnlyPolar_add_properPrimePower
    (H : ℝ) :
    suzukiCheckpointCriticalPrimePolarAction H =
      suzukiCheckpointCriticalPrimeOnlyPolarAction H +
        suzukiCheckpointCriticalProperPrimePowerAtomicAction H := by
  unfold suzukiCheckpointCriticalPrimePolarAction
    suzukiCheckpointCriticalPrimeOnlyPolarAction
    suzukiCheckpointCriticalProperPrimePowerAtomicAction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  nth_rewrite 1 [vonMangoldt_div_eq_prime_add_properPrimePower (j + 3)]
  ring

private theorem abs_properPrimePowerAtomicCell_le
    {H : ℝ} (hH : 2 ≤ H) {j : ℕ}
    (hj : j ∈ Finset.range (suzukiCheckpointEventIndex H - 2)) :
    |(if IsProperPrimePow (j + 3) then
        ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)
      else 0) * suzukiCheckpointCriticalTriangularMultiplier H j| ≤
      32 * suzukiCheckpointCriticalProperPrimePowerWeight (j + 3) := by
  by_cases hproper : IsProperPrimePow (j + 3)
  · rw [if_pos hproper]
    have hn0 : (0 : ℝ) < ((j + 3 : ℕ) : ℝ) := by positivity
    have hlog : 0 < Real.log ((j + 3 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < j + 3))
    have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt (j + 3) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hΛ : ArithmeticFunction.vonMangoldt (j + 3) ≤
        Real.log ((j + 3 : ℕ) : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    have hmult := abs_suzukiCheckpointCriticalTriangularMultiplier_le hH hj
    have hscalar0 : 0 ≤ ArithmeticFunction.vonMangoldt (j + 3) /
        ((j + 3 : ℕ) : ℝ) := div_nonneg hΛ0 hn0.le
    have hpotential0 : 0 ≤ HTGeometry.shiftedReciprocalLogPotential 3 j :=
      HTGeometry.shiftedReciprocalLogPotential_nonneg 3 j
    have hmultBound0 : 0 ≤ 32 * Real.sqrt ((j + 3 : ℕ) : ℝ) *
        HTGeometry.shiftedReciprocalLogPotential 3 j := by positivity
    rw [abs_mul, abs_of_nonneg hscalar0]
    calc
      (ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)) *
          |suzukiCheckpointCriticalTriangularMultiplier H j| ≤
          (ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)) *
            (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) *
              HTGeometry.shiftedReciprocalLogPotential 3 j) := by
            exact mul_le_mul_of_nonneg_left hmult hscalar0
      _ ≤ (Real.log ((j + 3 : ℕ) : ℝ) / ((j + 3 : ℕ) : ℝ)) *
            (32 * Real.sqrt ((j + 3 : ℕ) : ℝ) *
              HTGeometry.shiftedReciprocalLogPotential 3 j) := by
            exact mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right hΛ hn0.le) hmultBound0
      _ = 32 * suzukiCheckpointCriticalProperPrimePowerWeight (j + 3) := by
            unfold HTGeometry.shiftedReciprocalLogPotential
              suzukiCheckpointCriticalProperPrimePowerWeight
            rw [if_pos hproper]
            have hsqrt : Real.sqrt ((j + 3 : ℕ) : ℝ) ≠ 0 :=
              (Real.sqrt_pos.mpr hn0).ne'
            have hsquare : Real.sqrt ((j + 3 : ℕ) : ℝ) ^ (2 : ℕ) =
                ((j + 3 : ℕ) : ℝ) := Real.sq_sqrt hn0.le
            have hcast : ((j + 3 : ℕ) : ℝ) = (j : ℝ) + 3 := by
              push_cast
              ring
            have hsquare' : Real.sqrt ((j : ℝ) + 3) ^ (2 : ℕ) = (j : ℝ) + 3 := by
              rw [← hcast]
              exact hsquare
            rw [hcast]
            field_simp [hsqrt, hlog.ne']
            rw [hsquare']
  · rw [if_neg hproper, zero_mul, abs_zero]
    unfold suzukiCheckpointCriticalProperPrimePowerWeight
    rw [if_neg hproper]
    norm_num

/-- One height-independent bound absorbs the entire proper-prime-power sector. -/
theorem exists_suzukiCheckpointCriticalProperPrimePowerAtomicAction_uniform_bound :
    ∃ C : ℝ, ∀ H : ℝ, 2 ≤ H →
      |suzukiCheckpointCriticalProperPrimePowerAtomicAction H| ≤ C := by
  let w : ℕ → ℝ := fun j =>
    suzukiCheckpointCriticalProperPrimePowerWeight (j + 3)
  have hw : Summable w := by
    exact (summable_nat_add_iff 3).mpr
      summable_suzukiCheckpointCriticalProperPrimePowerWeight
  have hw0 : ∀ j, 0 ≤ w j := by
    intro j
    exact suzukiCheckpointCriticalProperPrimePowerWeight_nonneg _
  refine ⟨32 * ∑' j : ℕ, w j, ?_⟩
  intro H hH
  unfold suzukiCheckpointCriticalProperPrimePowerAtomicAction
  calc
    |∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        (if IsProperPrimePow (j + 3) then
          ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)
        else 0) * suzukiCheckpointCriticalTriangularMultiplier H j| ≤
        ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2), 32 * w j := by
      calc
        |∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
            (if IsProperPrimePow (j + 3) then
              ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)
            else 0) * suzukiCheckpointCriticalTriangularMultiplier H j| ≤
            ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
              |(if IsProperPrimePow (j + 3) then
                ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)
              else 0) * suzukiCheckpointCriticalTriangularMultiplier H j| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2), 32 * w j := by
              apply Finset.sum_le_sum
              intro j hj
              exact abs_properPrimePowerAtomicCell_le hH hj
    _ = 32 * ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2), w j := by
      rw [Finset.mul_sum]
    _ ≤ 32 * ∑' j : ℕ, w j := by
      exact mul_le_mul_of_nonneg_left
        (hw.sum_le_tsum _ (fun i _ => hw0 i)) (by norm_num)

/-- The proper-prime-power sector is uniformly absolutely summable inside every literal moving
FU aperture.  This is stronger than boundedness of its signed action and is used only to isolate
the valuation-one absolute-variation obstruction. -/
theorem exists_suzukiCheckpointCriticalProperPrimePowerAbsoluteVariation_uniform_bound :
    ∃ C : ℝ, ∀ H : ℝ, 2 ≤ H →
      ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        |(if IsProperPrimePow (j + 3) then
            ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)
          else 0) * suzukiCheckpointCriticalTriangularMultiplier H j| ≤ C := by
  let w : ℕ → ℝ := fun j =>
    suzukiCheckpointCriticalProperPrimePowerWeight (j + 3)
  have hw : Summable w := by
    exact (summable_nat_add_iff 3).mpr
      summable_suzukiCheckpointCriticalProperPrimePowerWeight
  have hw0 : ∀ j, 0 ≤ w j := by
    intro j
    exact suzukiCheckpointCriticalProperPrimePowerWeight_nonneg _
  refine ⟨32 * ∑' j : ℕ, w j, ?_⟩
  intro H hH
  calc
    ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        |(if IsProperPrimePow (j + 3) then
            ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)
          else 0) * suzukiCheckpointCriticalTriangularMultiplier H j| ≤
        ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2), 32 * w j := by
      apply Finset.sum_le_sum
      intro j hj
      exact abs_properPrimePowerAtomicCell_le hH hj
    _ = 32 * ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2), w j := by
      rw [Finset.mul_sum]
    _ ≤ 32 * ∑' j : ℕ, w j := by
      exact mul_le_mul_of_nonneg_left
        (hw.sum_le_tsum _ (fun i _ => hw0 i)) (by norm_num)

/-- The RH-bearing critical FU action differs from the valuation-one prime--polar
action only by its bounded proper-prime-power sector. -/
theorem suzukiCheckpointCriticalMertensDeviationVariationAction_eq_primeOnlyPolar_add_proper
    (H : ℝ) :
    suzukiCheckpointCriticalVariationAction suzukiCheckpointCriticalMertensDeviation H =
      suzukiCheckpointCriticalMertensDeviation 0 *
          suzukiCheckpointCriticalTriangularMultiplier H 0 +
        suzukiCheckpointCriticalPrimeOnlyPolarAction H +
          suzukiCheckpointCriticalProperPrimePowerAtomicAction H := by
  rw [suzukiCheckpointCriticalMertensDeviationVariationAction_eq_weightedPrimePolar]
  rw [show (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
      (ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ) -
        (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ))) *
          suzukiCheckpointCriticalTriangularMultiplier H j) =
      suzukiCheckpointCriticalPrimePolarAction H by rfl,
    suzukiCheckpointCriticalPrimePolarAction_eq_primeOnlyPolar_add_properPrimePower]
  ring

/-- Uniform boundedness of the literal valuation-one prime--polar codiagonal.

This is not a replacement reporter: its coefficients and its moving triangular cutoff are those
of the original critical FU source after the absolutely summable proper-prime-power sector has
been removed. -/
def CCMFUSuzukiCriticalPrimeOnlyPolarActionBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 2 ≤ H →
    |suzukiCheckpointCriticalPrimeOnlyPolarAction H| ≤ C

/-- **Exact valuation-one frontier.**  Proper prime powers carry a uniform unconditional budget,
so the RH-bearing critical FU bound is equivalent to boundedness of the literal valuation-one
prime--polar codiagonal.  The polar increments have not been moved, smoothed, or replaced. -/
theorem ccmFUSuzukiCriticalPrimeOnlyPolarActionBound_iff_riemannHypothesis :
    CCMFUSuzukiCriticalPrimeOnlyPolarActionBound ↔ RiemannHypothesis := by
  obtain ⟨B, hB⟩ :=
    exists_suzukiCheckpointCriticalProperPrimePowerAtomicAction_uniform_bound
  let D : ℝ := |suzukiCheckpointCriticalMertensDeviation 0| *
    (32 * Real.sqrt 3)
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hbase : ∀ H : ℝ, 2 ≤ H →
      |suzukiCheckpointCriticalMertensDeviation 0 *
        suzukiCheckpointCriticalTriangularMultiplier H 0| ≤ D := by
    intro H hH
    rw [abs_mul]
    calc
      |suzukiCheckpointCriticalMertensDeviation 0| *
          |suzukiCheckpointCriticalTriangularMultiplier H 0| ≤
          |suzukiCheckpointCriticalMertensDeviation 0| * (32 * Real.sqrt 3) :=
        mul_le_mul_of_nonneg_left
          (abs_suzukiCheckpointCriticalTriangularMultiplier_zero_le hH)
          (abs_nonneg _)
      _ = D := rfl
  constructor
  · rintro ⟨C, hC0, hC⟩
    apply ccmFUSuzukiCriticalMertensDeviationVariationActionBound_iff_riemannHypothesis.mp
    refine ⟨D + C + |B|, by positivity, ?_⟩
    intro H hH
    rw [suzukiCheckpointCriticalMertensDeviationVariationAction_eq_primeOnlyPolar_add_proper]
    calc
      |suzukiCheckpointCriticalMertensDeviation 0 *
            suzukiCheckpointCriticalTriangularMultiplier H 0 +
          suzukiCheckpointCriticalPrimeOnlyPolarAction H +
            suzukiCheckpointCriticalProperPrimePowerAtomicAction H| ≤
          |suzukiCheckpointCriticalMertensDeviation 0 *
              suzukiCheckpointCriticalTriangularMultiplier H 0| +
            |suzukiCheckpointCriticalPrimeOnlyPolarAction H| +
              |suzukiCheckpointCriticalProperPrimePowerAtomicAction H| := by
            calc
              _ ≤ |suzukiCheckpointCriticalMertensDeviation 0 *
                    suzukiCheckpointCriticalTriangularMultiplier H 0 +
                  suzukiCheckpointCriticalPrimeOnlyPolarAction H| +
                    |suzukiCheckpointCriticalProperPrimePowerAtomicAction H| :=
                abs_add_le _ _
              _ ≤ _ := by gcongr; exact abs_add_le _ _
      _ ≤ D + C + |B| := by
        have hproper :
            |suzukiCheckpointCriticalProperPrimePowerAtomicAction H| ≤ |B| :=
          (hB H hH).trans (le_abs_self B)
        nlinarith [hbase H hH, hC H hH]
  · intro hRH
    obtain ⟨C, hC0, hC⟩ :=
      ccmFUSuzukiCriticalMertensDeviationVariationActionBound_iff_riemannHypothesis.mpr hRH
    refine ⟨C + D + |B|, by positivity, ?_⟩
    intro H hH
    have hsplit :=
      suzukiCheckpointCriticalMertensDeviationVariationAction_eq_primeOnlyPolar_add_proper H
    have hsolve : suzukiCheckpointCriticalPrimeOnlyPolarAction H =
        suzukiCheckpointCriticalVariationAction
          suzukiCheckpointCriticalMertensDeviation H -
          suzukiCheckpointCriticalMertensDeviation 0 *
            suzukiCheckpointCriticalTriangularMultiplier H 0 -
          suzukiCheckpointCriticalProperPrimePowerAtomicAction H := by
      linarith
    rw [hsolve]
    calc
      |suzukiCheckpointCriticalVariationAction
            suzukiCheckpointCriticalMertensDeviation H -
          suzukiCheckpointCriticalMertensDeviation 0 *
            suzukiCheckpointCriticalTriangularMultiplier H 0 -
          suzukiCheckpointCriticalProperPrimePowerAtomicAction H| ≤
          |suzukiCheckpointCriticalVariationAction
              suzukiCheckpointCriticalMertensDeviation H| +
            |suzukiCheckpointCriticalMertensDeviation 0 *
              suzukiCheckpointCriticalTriangularMultiplier H 0| +
              |suzukiCheckpointCriticalProperPrimePowerAtomicAction H| := by
            calc
              _ ≤ |suzukiCheckpointCriticalVariationAction
                    suzukiCheckpointCriticalMertensDeviation H -
                  suzukiCheckpointCriticalMertensDeviation 0 *
                    suzukiCheckpointCriticalTriangularMultiplier H 0| +
                    |suzukiCheckpointCriticalProperPrimePowerAtomicAction H| :=
                abs_sub _ _
              _ ≤ _ := by gcongr; exact abs_sub _ _
      _ ≤ C + D + |B| := by
        have hproper :
            |suzukiCheckpointCriticalProperPrimePowerAtomicAction H| ≤ |B| :=
          (hB H hH).trans (le_abs_self B)
        nlinarith [hC H hH, hbase H hH]

end

end RHTower
