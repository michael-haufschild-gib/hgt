import GaloisForLFunctions.RHTower.EulerActivationSquarefreeDisintegration
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.InfinitePi

/-!
# Squarefree Gibbs pushforward and critical Euler probability

This module completes the probability-theoretic layer of diagonal Euler
activation. It proves the exact finite squarefree Gibbs pushforward, constructs
the Bernoulli--geometric local probability measure and its critical Kolmogorov
product, proves the orthogonal occupancy/valuation Fisher decomposition, and
applies the second Borel--Cantelli lemma to show almost-sure infinite prime
occupancy at `σ = 1`.
-/

open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

/-- Product occupancy weight of a subset of a finite source palette. -/
def finiteActivationOccupancyWeight
    {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (P S : Finset ι) : ℝ :=
  (∏ i ∈ S, diagonalActivationOccupancyProbability (q i)) *
    ∏ i ∈ P \ S, (1 - diagonalActivationOccupancyProbability (q i))

/-- The finite occupancy weights are normalized on the powerset. -/
theorem sum_finiteActivationOccupancyWeight_powerset
    {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (P : Finset ι) :
    ∑ S ∈ P.powerset, finiteActivationOccupancyWeight q P S = 1 := by
  classical
  have h := Finset.prod_add
    (fun i ↦ diagonalActivationOccupancyProbability (q i))
    (fun i ↦ 1 - diagonalActivationOccupancyProbability (q i)) P
  simpa [finiteActivationOccupancyWeight] using h.symm

/-- Closed Gibbs form of a finite occupancy weight. -/
theorem finiteActivationOccupancyWeight_eq_prod_div
    {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (P S : Finset ι) (hSP : S ⊆ P)
    (hq : ∀ i ∈ P, 0 ≤ q i) :
    finiteActivationOccupancyWeight q P S =
      (∏ i ∈ S, q i) / ∏ i ∈ P, (1 + q i) := by
  classical
  have hden (i : ι) (hi : i ∈ P) : 1 + q i ≠ 0 := by
    have := hq i hi
    linarith
  have hocc (i : ι) :
      diagonalActivationOccupancyProbability (q i) = q i / (1 + q i) := rfl
  have hnot (i : ι) (hi : i ∈ P) :
      1 - q i / (1 + q i) = 1 / (1 + q i) := by
    field_simp [hden i hi]
    ring
  rw [finiteActivationOccupancyWeight]
  simp_rw [hocc]
  have hSden : ∏ i ∈ S, (1 + q i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi ↦ hden i (hSP hi)
  have hDden : ∏ i ∈ P \ S, (1 + q i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi ↦ hden i (Finset.mem_sdiff.mp hi).1
  have hPden : ∏ i ∈ P, (1 + q i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hden
  rw [Finset.prod_congr rfl fun i hi ↦ hnot i (Finset.mem_sdiff.mp hi).1]
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
  simp only [Finset.prod_const_one]
  have hsplit := Finset.prod_sdiff (f := fun i ↦ 1 + q i) hSP
  rw [← hsplit]
  field_simp [hSden, hDden, hPden]

/-- Radical integer encoded by an occupied subset of a finite prime palette. -/
def finitePrimeActivationRadical (S : Finset Nat.Primes) : ℕ :=
  ∏ p ∈ S, (p : ℕ)

/-- Exact finite squarefree Gibbs weight of a prime radical. -/
theorem finitePrimeActivationOccupancyWeight_eq_gibbs
    (sigma : ℝ) (P S : Finset Nat.Primes) (hSP : S ⊆ P) :
    finiteActivationOccupancyWeight
        (fun p : Nat.Primes ↦ (p : ℝ) ^ (-sigma)) P S =
      (finitePrimeActivationRadical S : ℝ) ^ (-sigma) /
        ∏ p ∈ P, (1 + (p : ℝ) ^ (-sigma)) := by
  rw [finiteActivationOccupancyWeight_eq_prod_div _ P S hSP
    (fun _ _ ↦ Real.rpow_nonneg (by positivity) _)]
  congr 1
  rw [finitePrimeActivationRadical, Nat.cast_prod]
  exact Real.finsetProd_rpow S (fun p : Nat.Primes ↦ (p : ℝ))
    (fun _ _ ↦ by positivity) (-sigma)

/-- Nonnegative-real representative of a unit-interval parameter. -/
def unitIntervalToNNReal (q : unitInterval) : ℝ≥0 :=
  ⟨q, q.2.1⟩

/-- Complementary geometric success parameter. -/
def unitIntervalComplement (q : unitInterval) : unitInterval :=
  ⟨1 - q, by constructor <;> linarith [q.2.1, q.2.2]⟩

/-- Canonical local activation probability measure: an empty atom together
with an occupied, shifted geometric fibre. -/
noncomputable def diagonalActivationMeasure (q : unitInterval) : MeasureTheory.Measure ℕ :=
  (1 / (1 + (unitIntervalToNNReal q : ℝ≥0∞))) • MeasureTheory.Measure.dirac 0 +
    ((unitIntervalToNNReal q : ℝ≥0∞) /
        (1 + (unitIntervalToNNReal q : ℝ≥0∞))) •
      (ProbabilityTheory.geometricMeasure (unitIntervalComplement q)).map Nat.succ

instance diagonalActivationMeasure_isProbabilityMeasure (q : unitInterval) :
    MeasureTheory.IsProbabilityMeasure (diagonalActivationMeasure q) := by
  constructor
  have hmap :
      (ProbabilityTheory.geometricMeasure (unitIntervalComplement q)).map Nat.succ
          Set.univ = 1 := by
    rw [MeasureTheory.Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  rw [diagonalActivationMeasure, MeasureTheory.Measure.add_apply]
  simp only [MeasureTheory.Measure.smul_apply,
    MeasureTheory.IsProbabilityMeasure.measure_univ, hmap]
  simp only [smul_eq_mul, mul_one]
  calc
    1 / (1 + (unitIntervalToNNReal q : ℝ≥0∞)) +
          (unitIntervalToNNReal q : ℝ≥0∞) /
            (1 + (unitIntervalToNNReal q : ℝ≥0∞)) =
        (1 + (unitIntervalToNNReal q : ℝ≥0∞)) /
          (1 + (unitIntervalToNNReal q : ℝ≥0∞)) := ENNReal.add_div.symm
    _ = 1 := ENNReal.div_self (by simp) (by simp)

/-- Positive-valuation mass of the canonical local activation measure. -/
theorem diagonalActivationMeasure_positive
    (q : unitInterval) :
    diagonalActivationMeasure q {k : ℕ | 0 < k} =
      (unitIntervalToNNReal q : ℝ≥0∞) /
        (1 + (unitIntervalToNNReal q : ℝ≥0∞)) := by
  have hmap :
      (ProbabilityTheory.geometricMeasure (unitIntervalComplement q)).map Nat.succ
          {k : ℕ | 0 < k} = 1 := by
    rw [MeasureTheory.Measure.map_apply (by fun_prop) (by measurability)]
    simp
  simp [diagonalActivationMeasure, hmap]

/-- Critical Euler parameter `q_p = 1 / p`. -/
def criticalEulerParameter (p : Nat.Primes) : unitInterval :=
  ⟨1 / (p : ℝ), by
    have hp : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast p.2.pos
    constructor
    · positivity
    · apply (div_le_one₀ hp).2
      exact_mod_cast p.2.two_le.trans' (by norm_num : 1 ≤ 2)⟩

/-- Critical occupancy probability `1 / (p + 1)`. -/
def criticalPrimeOccupancyProbability (p : Nat.Primes) : ℝ≥0 :=
  ⟨1 / ((p : ℝ) + 1), by positivity⟩

/-- The critical local activation measure occupies prime `p` with probability
exactly `1 / (p + 1)`. -/
theorem diagonalActivationMeasure_critical_positive
    (p : Nat.Primes) :
    diagonalActivationMeasure (criticalEulerParameter p) {k : ℕ | 0 < k} =
      (criticalPrimeOccupancyProbability p : ℝ≥0∞) := by
  rw [diagonalActivationMeasure_positive]
  let qn := unitIntervalToNNReal (criticalEulerParameter p)
  have hden : (1 : ℝ≥0) + qn ≠ 0 := by positivity
  change (qn : ℝ≥0∞) / (1 + (qn : ℝ≥0∞)) =
    (criticalPrimeOccupancyProbability p : ℝ≥0∞)
  rw [← ENNReal.coe_one, ← ENNReal.coe_add, ← ENNReal.coe_div hden]
  norm_cast
  apply NNReal.eq
  push_cast
  have hq :
      ((unitIntervalToNNReal (criticalEulerParameter p) : ℝ≥0) : ℝ) =
        1 / (p : ℝ) := rfl
  have hprob :
      ((criticalPrimeOccupancyProbability p : ℝ≥0) : ℝ) =
        1 / ((p : ℝ) + 1) := rfl
  dsimp only [qn]
  rw [hq, hprob]
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hp : (p : ℝ) ≠ 0 := hppos.ne'
  have hpplus : (p : ℝ) + 1 ≠ 0 := by linarith
  field_simp [hp, hpplus]

/-- Canonical enumeration of all prime numbers. -/
noncomputable def natEquivPrimes : ℕ ≃ Nat.Primes where
  toFun n := ⟨Nat.nth Nat.Prime n,
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n⟩
  invFun p := Nat.count Nat.Prime p
  left_inv n := Nat.count_nth_of_infinite Nat.infinite_setOf_prime n
  right_inv p := Subtype.ext (Nat.nth_count p.2)

/-- The critical prime occupancy probabilities are not summable. -/
theorem criticalPrimeOccupancyProbability_not_summable :
    ¬ Summable (fun p : Nat.Primes ↦
      (criticalPrimeOccupancyProbability p : ℝ)) := by
  intro h
  apply Nat.Primes.not_summable_one_div
  refine (h.mul_left 2).of_nonneg_of_le (fun _ ↦ by positivity) ?_
  intro p
  change 1 / (p : ℝ) ≤ 2 * (1 / ((p : ℝ) + 1))
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast p.2.two_le.trans' (by norm_num : 1 ≤ 2)
  calc
    1 / (p : ℝ) ≤ 2 / ((p : ℝ) + 1) := by
      apply (div_le_div_iff₀ hp (by linarith)).2
      linarith
    _ = 2 * (1 / ((p : ℝ) + 1)) := by ring

/-- Prime-indexed critical valuation configurations. -/
abbrev CriticalEulerConfiguration := Nat.Primes → ℕ

/-- Kolmogorov product of the critical local activation laws. -/
noncomputable def criticalEulerProductMeasure :
    MeasureTheory.Measure CriticalEulerConfiguration :=
  MeasureTheory.Measure.infinitePi fun p : Nat.Primes ↦
    diagonalActivationMeasure (criticalEulerParameter p)

/-- Event that a specified prime has positive valuation. -/
def criticalPrimeOccupied (p : Nat.Primes) :
    Set CriticalEulerConfiguration :=
  {K | 0 < K p}

/-- Occupancy events enumerated by the canonical prime enumeration. -/
noncomputable def criticalPrimeOccupiedSequence (n : ℕ) :
    Set CriticalEulerConfiguration :=
  criticalPrimeOccupied (natEquivPrimes n)

theorem measurableSet_criticalPrimeOccupiedSequence (n : ℕ) :
    MeasurableSet (criticalPrimeOccupiedSequence n) := by
  exact MeasurableSet.preimage (by measurability) (by fun_prop)

/-- Critical occupancy cylinder probabilities are `1 / (p + 1)`. -/
theorem criticalEulerProductMeasure_criticalPrimeOccupied
    (p : Nat.Primes) :
    criticalEulerProductMeasure (criticalPrimeOccupied p) =
      (criticalPrimeOccupancyProbability p : ℝ≥0∞) := by
  let μp : Nat.Primes → MeasureTheory.Measure ℕ :=
    fun r ↦ diagonalActivationMeasure (criticalEulerParameter r)
  have hmap := MeasureTheory.Measure.infinitePi_map_eval μp p
  calc
    criticalEulerProductMeasure (criticalPrimeOccupied p) =
        (criticalEulerProductMeasure.map (fun K ↦ K p)) {k : ℕ | 0 < k} := by
      rw [MeasureTheory.Measure.map_apply (by fun_prop) (by measurability)]
      rfl
    _ = diagonalActivationMeasure (criticalEulerParameter p) {k : ℕ | 0 < k} := by
      rw [show criticalEulerProductMeasure =
          MeasureTheory.Measure.infinitePi μp by rfl, hmap]
    _ = (criticalPrimeOccupancyProbability p : ℝ≥0∞) :=
      diagonalActivationMeasure_critical_positive p

/-- The enumerated critical occupancy cylinders are independent. -/
theorem iIndepSet_criticalPrimeOccupiedSequence :
    ProbabilityTheory.iIndepSet criticalPrimeOccupiedSequence
      criticalEulerProductMeasure := by
  let μp : Nat.Primes → MeasureTheory.Measure ℕ :=
    fun p ↦ diagonalActivationMeasure (criticalEulerParameter p)
  have hindPrime :
      ProbabilityTheory.iIndepFun
        (fun p (K : CriticalEulerConfiguration) ↦ K p)
        (MeasureTheory.Measure.infinitePi μp) :=
    ProbabilityTheory.iIndepFun_infinitePi (X := fun _ k ↦ k) (by fun_prop)
  have hindNat :=
    ProbabilityTheory.iIndepFun.precomp natEquivPrimes.injective hindPrime
  apply (ProbabilityTheory.iIndepSet_iff_meas_biInter
    measurableSet_criticalPrimeOccupiedSequence).2
  intro S
  exact hindNat.meas_biInter fun n _ ↦ by
    change @MeasurableSet CriticalEulerConfiguration
      ((inferInstance : MeasurableSpace ℕ).comap
        (fun K : CriticalEulerConfiguration ↦ K (natEquivPrimes n)))
      ((fun K : CriticalEulerConfiguration ↦ K (natEquivPrimes n)) ⁻¹'
        {k : ℕ | 0 < k})
    exact (by measurability : MeasurableSet {k : ℕ | 0 < k}).preimage
      (comap_measurable _)

/-- The critical occupancy cylinder masses have divergent ENNReal sum. -/
theorem tsum_criticalPrimeOccupiedSequence_eq_top :
    (∑' n : ℕ, criticalEulerProductMeasure
      (criticalPrimeOccupiedSequence n)) = ∞ := by
  rw [show (fun n : ℕ ↦ criticalEulerProductMeasure
      (criticalPrimeOccupiedSequence n)) =
      fun n ↦ (criticalPrimeOccupancyProbability (natEquivPrimes n) : ℝ≥0∞) by
    funext n
    exact criticalEulerProductMeasure_criticalPrimeOccupied _]
  apply ENNReal.tsum_coe_eq_top_iff_not_summable_coe.mpr
  intro h
  apply criticalPrimeOccupancyProbability_not_summable
  exact natEquivPrimes.summable_iff.mp h

/-- Limsup occupancy is exactly occupancy of infinitely many primes. -/
theorem limsup_criticalPrimeOccupiedSequence :
    Filter.limsup criticalPrimeOccupiedSequence Filter.atTop =
      {K : CriticalEulerConfiguration |
        Set.Infinite {p : Nat.Primes | 0 < K p}} := by
  ext K
  rw [Filter.mem_limsup_iff_frequently_mem,
    Nat.frequently_atTop_iff_infinite]
  change Set.Infinite {n : ℕ | 0 < K (natEquivPrimes n)} ↔
    Set.Infinite {p : Nat.Primes | 0 < K p}
  have himage :
      natEquivPrimes '' {n : ℕ | 0 < K (natEquivPrimes n)} =
        {p : Nat.Primes | 0 < K p} := by
    ext p
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hn
    · intro hp
      exact ⟨natEquivPrimes.symm p, by simpa, by simp⟩
  rw [← himage]
  exact (Set.infinite_image_iff natEquivPrimes.injective.injOn).symm

/-- At the Euler edge, the honest Kolmogorov product is supported on
configurations with infinitely many occupied primes. -/
theorem criticalEulerProductMeasure_infinite_occupancy :
    criticalEulerProductMeasure
        {K : CriticalEulerConfiguration |
          Set.Infinite {p : Nat.Primes | 0 < K p}} = 1 := by
  rw [← limsup_criticalPrimeOccupiedSequence]
  exact ProbabilityTheory.measure_limsup_eq_one
    measurableSet_criticalPrimeOccupiedSequence
    iIndepSet_criticalPrimeOccupiedSequence
    tsum_criticalPrimeOccupiedSequence_eq_top

/-- Score of the squarefree occupancy bit in the natural coordinate
`x = -log q`. -/
def diagonalActivationOccupancyScore (q : ℝ) (occupied : Bool) : ℝ :=
  diagonalActivationOccupancyProbability q - if occupied then 1 else 0

/-- Score of the conditional geometric valuation fibre in the natural
coordinate `x = -log q`. -/
def diagonalActivationValuationScore (q : ℝ) (e : ℕ) : ℝ :=
  q / (1 - q) - e

/-- Full local activation score, expressed on the Bernoulli--geometric
disintegration. -/
def diagonalActivationFullScore (q : ℝ) (occupied : Bool) (e : ℕ) : ℝ :=
  diagonalActivationOccupancyScore q occupied +
    if occupied then diagonalActivationValuationScore q e else 0

/-- The full activation score splits pointwise into occupancy and conditional
valuation scores. -/
theorem diagonalActivationFullScore_eq_orthogonal_split
    (q : ℝ) (occupied : Bool) (e : ℕ) :
    diagonalActivationFullScore q occupied e =
      diagonalActivationOccupancyScore q occupied +
        if occupied then diagonalActivationValuationScore q e else 0 := by
  rfl

/-- Exact second raw moment of the geometric power series. -/
theorem hasSum_sq_mul_geometric_of_abs_lt_one
    {q : ℝ} (hq : |q| < 1) :
    HasSum (fun e : ℕ ↦ (e : ℝ) ^ 2 * q ^ e)
      (q * (1 + q) / (1 - q) ^ 3) := by
  have hchoose0 := hasSum_choose_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) 2 (by simpa [Real.norm_eq_abs] using hq)
  have hchooseTail :
      HasSum (fun e : ℕ ↦ ((e + 2).choose 2 : ℝ) * q ^ (e + 2))
        (q ^ 2 * (1 / (1 - q) ^ 3)) := by
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using
      hchoose0.mul_left (q ^ 2)
  have hchoose :
      HasSum (fun e : ℕ ↦ (e.choose 2 : ℝ) * q ^ e)
        (q ^ 2 / (1 - q) ^ 3) := by
    apply (hasSum_nat_add_iff' 2).mp
    simpa [Finset.sum_range_succ, div_eq_mul_inv] using hchooseTail
  have hfirst := hasSum_coe_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) (by simpa [Real.norm_eq_abs] using hq)
  have hraw := hchoose.mul_left 2 |>.add hfirst
  have hterm (e : ℕ) :
      2 * ((e.choose 2 : ℝ) * q ^ e) + (e : ℝ) * q ^ e =
        (e : ℝ) ^ 2 * q ^ e := by
    cases e with
    | zero => simp
    | succ e =>
        rw [Nat.cast_choose_two]
        push_cast
        simp
        ring
  have hvalue :
      2 * (q ^ 2 / (1 - q) ^ 3) + q / (1 - q) ^ 2 =
        q * (1 + q) / (1 - q) ^ 3 := by
    have hminus : 1 - q ≠ 0 := by linarith [abs_lt.mp hq]
    field_simp [hminus]
    ring
  rw [← hvalue]
  exact hraw.congr_fun fun e ↦ (hterm e).symm

/-- The conditional geometric valuation masses sum to one. -/
theorem hasSum_diagonalActivationConditionalValuationMass
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (diagonalActivationConditionalValuationMass q) 1 := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have hminus : 1 - q ≠ 0 := by linarith
  have hgeom : HasSum (fun e : ℕ ↦ q ^ e) (1 - q)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hnorm
  have hmass := hgeom.mul_left (1 - q)
  have hvalue : (1 - q) * (1 - q)⁻¹ = (1 : ℝ) := by
    exact mul_inv_cancel₀ hminus
  rw [← hvalue]
  exact hmass.congr_fun fun e ↦ by
    simp [diagonalActivationConditionalValuationMass]

/-- The conditional geometric valuation score has mean zero. -/
theorem hasSum_diagonalActivationConditionalValuationMass_mul_score
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun e : ℕ ↦ diagonalActivationConditionalValuationMass q e *
        diagonalActivationValuationScore q e) 0 := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have hminus : 1 - q ≠ 0 := by linarith
  have hgeom : HasSum (fun e : ℕ ↦ q ^ e) (1 - q)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hnorm
  have hfirst := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hnorm
  have hscore := hgeom.mul_left ((1 - q) * (q / (1 - q)))
    |>.sub (hfirst.mul_left (1 - q))
  have hvalue :
      (1 - q) * (q / (1 - q)) * (1 - q)⁻¹ -
          (1 - q) * (q / (1 - q) ^ 2) = 0 := by
    field_simp [hminus]
    ring
  rw [← hvalue]
  exact hscore.congr_fun fun e ↦ by
    simp only [diagonalActivationConditionalValuationMass,
      diagonalActivationValuationScore]
    ring

/-- Tsum form of conditional score centering. -/
theorem tsum_diagonalActivationConditionalValuationMass_mul_score
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (∑' e : ℕ, diagonalActivationConditionalValuationMass q e *
        diagonalActivationValuationScore q e) = 0 :=
  (hasSum_diagonalActivationConditionalValuationMass_mul_score hq hq1).tsum_eq

/-- The conditional geometric valuation score has variance
`q / (1 - q)^(2 : ℕ)`. -/
theorem hasSum_diagonalActivationConditionalValuationMass_mul_score_sq
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun e : ℕ ↦ diagonalActivationConditionalValuationMass q e *
        diagonalActivationValuationScore q e ^ 2)
      (q / (1 - q) ^ 2) := by
  have habs : |q| < 1 := by simpa [abs_of_nonneg hq] using hq1
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs] using habs
  have hminus : 1 - q ≠ 0 := by linarith
  have hgeom : HasSum (fun e : ℕ ↦ q ^ e) (1 - q)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hnorm
  have hfirst := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hnorm
  have hsecond := hasSum_sq_mul_geometric_of_abs_lt_one habs
  have hscore :=
    (hgeom.mul_left ((1 - q) * (q / (1 - q)) ^ 2)).sub
      (hfirst.mul_left ((1 - q) * (2 * (q / (1 - q)))))
    |>.add (hsecond.mul_left (1 - q))
  have hvalue :
      (1 - q) * (q / (1 - q)) ^ 2 * (1 - q)⁻¹ -
          (1 - q) * (2 * (q / (1 - q))) * (q / (1 - q) ^ 2) +
          (1 - q) * (q * (1 + q) / (1 - q) ^ 3) =
        q / (1 - q) ^ 2 := by
    field_simp [hminus]
    ring
  rw [← hvalue]
  exact hscore.congr_fun fun e ↦ by
    simp only [diagonalActivationConditionalValuationMass,
      diagonalActivationValuationScore]
    ring

/-- Tsum form of the conditional geometric valuation-score variance. -/
theorem tsum_diagonalActivationConditionalValuationMass_mul_score_sq
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (∑' e : ℕ, diagonalActivationConditionalValuationMass q e *
        diagonalActivationValuationScore q e ^ 2) =
      q / (1 - q) ^ 2 :=
  (hasSum_diagonalActivationConditionalValuationMass_mul_score_sq hq hq1).tsum_eq

/-- The occupancy score is centered under its Bernoulli marginal. -/
theorem diagonalActivationOccupancyScore_mean
    {q : ℝ} (hq : 0 ≤ q) (_hq1 : q < 1) :
    (1 - diagonalActivationOccupancyProbability q) *
          diagonalActivationOccupancyScore q false +
        diagonalActivationOccupancyProbability q *
          diagonalActivationOccupancyScore q true = 0 := by
  have hplus : 1 + q ≠ 0 := by linarith
  simp only [diagonalActivationOccupancyScore, Bool.false_eq_true, if_false,
    if_true, sub_zero,
    diagonalActivationOccupancyProbability]
  field_simp [hplus]
  ring

/-- The occupancy-score second moment is exactly occupancy Fisher information. -/
theorem diagonalActivationOccupancyScore_secondMoment
    {q : ℝ} (hq : 0 ≤ q) (_hq1 : q < 1) :
    (1 - diagonalActivationOccupancyProbability q) *
          diagonalActivationOccupancyScore q false ^ 2 +
        diagonalActivationOccupancyProbability q *
          diagonalActivationOccupancyScore q true ^ 2 =
      diagonalActivationOccupancyFisher q := by
  have hplus : 1 + q ≠ 0 := by linarith
  simp only [diagonalActivationOccupancyScore, Bool.false_eq_true, if_false,
    if_true, sub_zero,
    diagonalActivationOccupancyProbability, diagonalActivationOccupancyFisher]
  field_simp [hplus]
  ring

/-- Occupancy and conditional valuation scores are orthogonal under the
Bernoulli--geometric disintegration. -/
theorem tsum_diagonalActivationOccupancyScore_mul_valuationScore
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (∑' e : ℕ, diagonalActivationOccupancyProbability q *
        diagonalActivationConditionalValuationMass q e *
        (diagonalActivationOccupancyScore q true *
          diagonalActivationValuationScore q e)) = 0 := by
  have hmean :=
    hasSum_diagonalActivationConditionalValuationMass_mul_score hq hq1
  have hscaled := hmean.mul_left
    (diagonalActivationOccupancyProbability q *
      diagonalActivationOccupancyScore q true)
  convert hscaled.tsum_eq using 1
  · apply tsum_congr
    intro e
    ring
  · ring

/-- Exact orthogonal Fisher decomposition of the full local activation score. -/
theorem diagonalActivationFullFisher_eq_occupancy_add_valuation
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (1 - diagonalActivationOccupancyProbability q) *
          diagonalActivationFullScore q false 0 ^ 2 +
        (∑' e : ℕ, diagonalActivationOccupancyProbability q *
          diagonalActivationConditionalValuationMass q e *
          diagonalActivationFullScore q true e ^ 2) =
      diagonalActivationOccupancyFisher q +
        diagonalActivationOccupancyProbability q * (q / (1 - q) ^ 2) := by
  let pi := diagonalActivationOccupancyProbability q
  let a := diagonalActivationOccupancyScore q true
  have hmass := hasSum_diagonalActivationConditionalValuationMass hq hq1
  have hmean :=
    hasSum_diagonalActivationConditionalValuationMass_mul_score hq hq1
  have hvar :=
    hasSum_diagonalActivationConditionalValuationMass_mul_score_sq hq hq1
  have hpositive :=
    (hmass.mul_left (pi * a ^ 2)).add
        (hmean.mul_left (pi * (2 * a)))
      |>.add (hvar.mul_left pi)
  have hpositive' :
      HasSum (fun e : ℕ ↦ pi *
          diagonalActivationConditionalValuationMass q e *
          diagonalActivationFullScore q true e ^ 2)
        (pi * a ^ 2 + pi * (2 * a) * 0 +
          pi * (q / (1 - q) ^ 2)) := by
    simpa only [mul_one] using hpositive.congr_fun fun e ↦ by
      change pi * diagonalActivationConditionalValuationMass q e *
          (a + diagonalActivationValuationScore q e) ^ 2 =
        pi * a ^ 2 * diagonalActivationConditionalValuationMass q e +
            pi * (2 * a) *
              (diagonalActivationConditionalValuationMass q e *
                diagonalActivationValuationScore q e) +
          pi * (diagonalActivationConditionalValuationMass q e *
            diagonalActivationValuationScore q e ^ 2)
      ring
  rw [hpositive'.tsum_eq]
  simp only [mul_zero, add_zero]
  rw [show diagonalActivationFullScore q false 0 =
      diagonalActivationOccupancyScore q false by
    simp [diagonalActivationFullScore]]
  have hocc :
      (1 - diagonalActivationOccupancyProbability q) *
            diagonalActivationOccupancyScore q false ^ 2 +
          pi * a ^ 2 =
        diagonalActivationOccupancyFisher q := by
    simpa [pi, a] using diagonalActivationOccupancyScore_secondMoment hq hq1
  rw [← add_assoc, hocc]

end

end RHTower
