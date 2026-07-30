import GaloisForLFunctions.RHTower.SoninEulerFiniteGramLower
import GaloisForLFunctions.RHTower.XiPrimeSeamCoherenceCollapse
import Mathlib.NumberTheory.PrimeCounting

/-!
# One norm-summable all-prime Sonin Gram detects Xi orientation

The finite Sonin Gram lower bound already recovers every coefficient of a finite prime matrix
modulo compact operators.  This file passes that statement to an absolutely norm-summable
infinite matrix: rectangular finite sections converge in operator norm, so compactness of the
full aggregate forces every coefficient to vanish.

We then give one canonical application.  On each Xi divisor fibre, every difference of two
FE--Schwarz prime-seam charges weights the corresponding even Sonin Gram entry.  A positive
geometric factor divided by one plus the norm of the weighted entry makes the double series
unconditionally norm-summable without changing the zero set of any coefficient.  Compactness of
this one operator forces prime-seam coherence.  Cofinal decay, already formalized in
`XiPrimeSeamCoherenceCollapse`, kills the common charge and gives the critical line.

Compactness of the aggregate is the remaining source-side assertion.  No compactness, RH, zero
location, or limiting-measure hypothesis is used to construct the operator or prove convergence.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Norm-summable infinite Gram injectivity -/

/-- One coefficient-weighted entry of an infinite even Sonin dilation Gram matrix. -/
def summableEvenDilationGramTerm
    (a : ℝ) (p : ℕ → ℕ) (hp : ∀ i, 1 < (p i : ℝ))
    (A : ℕ × ℕ → ℂ) (ij : ℕ × ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  A ij • evenCentralSoninQuadraticCorner a (p ij.1) (p ij.2)
    (hp ij.1) (hp ij.2)

/-- The rectangular finite section of an infinite even Sonin dilation Gram matrix. -/
def rectangularEvenDilationGramCombination
    (a : ℝ) (p : ℕ → ℕ) (hp : ∀ i, 1 < (p i : ℝ))
    (A : ℕ × ℕ → ℂ) (N : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  ∑ ij ∈ (Finset.range N).product (Finset.range N),
    summableEvenDilationGramTerm a p hp A ij

/-- Rectangles `range N × range N` are cofinal among finite subsets of `ℕ × ℕ`. -/
theorem rectangleFinsets_tendsto_atTop :
    Tendsto (fun N : ℕ => (Finset.range N).product (Finset.range N))
      atTop atTop := by
  rw [tendsto_atTop]
  intro s
  let N : ℕ := s.sup fun ij => max ij.1 ij.2
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  show s ⊆ (Finset.range n).product (Finset.range n)
  intro ij hij
  apply Finset.mem_product.mpr
  simp only [Finset.mem_range]
  have hle : max ij.1 ij.2 ≤ N := by
    simpa [N] using
      (Finset.le_sup (f := fun ij : ℕ × ℕ => max ij.1 ij.2) hij)
  omega

/-- The `Fin N` Gram combination is definitionally the `N × N` rectangular section. -/
theorem finiteEvenDilationGramCombination_eq_rectangle
    (a : ℝ) (p : ℕ → ℕ) (hp : ∀ i, 1 < (p i : ℝ))
    (A : ℕ × ℕ → ℂ) (N : ℕ) :
    finiteEvenDilationGramCombination a
      (fun i : Fin N => (p i : ℝ)) (fun i => hp i)
      (fun i j : Fin N => A (i, j)) =
        rectangularEvenDilationGramCombination a p hp A N := by
  classical
  unfold finiteEvenDilationGramCombination rectangularEvenDilationGramCombination
    summableEvenDilationGramTerm
  rw [show (∑ ij ∈ (Finset.range N).product (Finset.range N),
      A ij • evenCentralSoninQuadraticCorner a (p ij.1) (p ij.2)
        (hp ij.1) (hp ij.2)) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        A (i, j) • evenCentralSoninQuadraticCorner a (p i) (p j)
          (hp i) (hp j) from
    Finset.sum_product (Finset.range N) (Finset.range N)
      (fun ij => A ij • evenCentralSoninQuadraticCorner a (p ij.1) (p ij.2)
        (hp ij.1) (hp ij.2))]
  simp only [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos (Finset.mem_range.mp hi)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dif_pos (Finset.mem_range.mp hj)]
  rfl

/-- The full norm-summable infinite Gram operator. -/
def summableEvenDilationGramAggregate
    (a : ℝ) (p : ℕ → ℕ) (hp : ∀ i, 1 < (p i : ℝ))
    (A : ℕ × ℕ → ℂ) : evenSubspace →L[ℂ] evenSubspace :=
  ∑' ij, summableEvenDilationGramTerm a p hp A ij

/-- A finite partial sum differs from an absolutely convergent sum by at most the scalar norm
tail over its complement. -/
theorem norm_finsetSum_sub_tsum_le_compl
    {E ι : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ι → E) (hf : Summable fun i => ‖f i‖) (s : Finset ι) :
    ‖(∑ i ∈ s, f i) - ∑' i, f i‖ ≤
      ∑' i : {i // i ∉ s}, ‖f i‖ := by
  have hsplit := hf.of_norm.sum_add_tsum_subtype_compl s
  have heq : (∑ i ∈ s, f i) - ∑' i, f i =
      -(∑' i : {i // i ∉ s}, f i) := by
    rw [← hsplit]
    abel
  rw [heq, norm_neg]
  exact norm_tsum_le_tsum_norm (hf.subtype _)

/-- Rectangular partial sums of an absolutely norm-summable double series converge in norm. -/
theorem norm_rectangleSum_sub_tsum_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ × ℕ → E) (hf : Summable fun ij => ‖f ij‖) :
    Tendsto (fun N =>
        ‖(∑ ij ∈ (Finset.range N).product (Finset.range N), f ij) -
          ∑' ij, f ij‖) atTop (nhds 0) := by
  have htail : Tendsto (fun N =>
      ∑' ij : {ij // ij ∉ (Finset.range N).product (Finset.range N)}, ‖f ij‖)
      atTop (nhds 0) := by
    exact (tendsto_tsum_compl_atTop_zero (fun ij => ‖f ij‖)).comp
      rectangleFinsets_tendsto_atTop
  exact squeeze_zero
    (fun N => norm_nonneg _)
    (fun N => norm_finsetSum_sub_tsum_le_compl f hf
      ((Finset.range N).product (Finset.range N))) htail

set_option maxHeartbeats 500000 in
/-- **Infinite Calkin Gram injectivity.**  If the operator-norm sum of an absolutely summable
prime Gram matrix is compact and its diagonal coefficients vanish, then every coefficient
vanishes.  The finite quantitative lower bound is applied to larger and larger rectangles. -/
theorem coefficients_eq_zero_of_summableEvenDilationGramAggregate_isCompact
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hpReal : ∀ i, 1 < (p i : ℝ))
    (hinj : Function.Injective p)
    (A : ℕ × ℕ → ℂ) (hdiag : ∀ i, A (i, i) = 0)
    (hsnorm : Summable fun ij =>
      ‖summableEvenDilationGramTerm a p hpReal A ij‖)
    (hcompact : IsCompactOperator
      (summableEvenDilationGramAggregate a p hpReal A)) :
    A = 0 := by
  let T : evenSubspace →L[ℂ] evenSubspace :=
    summableEvenDilationGramAggregate a p hpReal A
  apply funext
  rintro ⟨i, j⟩
  by_cases hij : i = j
  · subst j
    exact hdiag i
  · have hdiff : Tendsto (fun N =>
        ‖rectangularEvenDilationGramCombination a p hpReal A N - T‖)
        atTop (nhds 0) := by
      change Tendsto (fun N =>
        ‖(∑ ij ∈ (Finset.range N).product (Finset.range N),
          summableEvenDilationGramTerm a p hpReal A ij) -
          ∑' ij, summableEvenDilationGramTerm a p hpReal A ij‖)
        atTop (nhds 0)
      exact norm_rectangleSum_sub_tsum_tendsto_zero
        (summableEvenDilationGramTerm a p hpReal A) hsnorm
    have hbound : ∀ᶠ N in atTop,
        ‖A (i, j)‖ ≤
          ‖rectangularEvenDilationGramCombination a p hpReal A N - T‖ := by
      filter_upwards [eventually_ge_atTop (max i j + 1)] with N hN
      let ii : Fin N := ⟨i, by omega⟩
      let jj : Fin N := ⟨j, by omega⟩
      have hijFin : jj ≠ ii := by
        intro h
        apply hij
        exact congrArg Fin.val h |>.symm
      have hle := norm_matrixEntry_le_norm_finitePrimeEvenDilationGram_sub_compact
        a ha (fun k : Fin N => p k) (fun k => hp k)
        (fun _ _ h => Fin.ext (hinj h))
        (fun k l : Fin N => A (k, l)) jj ii hijFin T hcompact
      rw [finiteEvenDilationGramCombination_eq_rectangle a p hpReal A N] at hle
      simpa [ii, jj] using hle
    have hle : ‖A (i, j)‖ ≤ 0 := ge_of_tendsto hdiff hbound
    exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))

/-! ## The canonical all-prime Xi seam aggregate -/

/-- The increasing enumeration of the rational primes. -/
def canonicalNthPrime (i : ℕ) : ℕ := Nat.nth Nat.Prime i

theorem canonicalNthPrime_prime (i : ℕ) : Nat.Prime (canonicalNthPrime i) :=
  Nat.prime_nth_prime i

theorem canonicalNthPrime_real_one_lt (i : ℕ) :
    1 < (canonicalNthPrime i : ℝ) := by
  exact_mod_cast (canonicalNthPrime_prime i).one_lt

theorem canonicalNthPrime_injective : Function.Injective canonicalNthPrime :=
  (Nat.nth_strictMono Nat.infinite_setOf_prime).injective

theorem range_canonicalNthPrime :
    Set.range canonicalNthPrime = {p : ℕ | Nat.Prime p} := by
  simpa [canonicalNthPrime] using!
    (Nat.range_nth_of_infinite Nat.infinite_setOf_prime)

/-- The difference of the two canonical FE--Schwarz prime seam values on one fibre. -/
def primeSeamAggregateDifference (rho : ℂ) (ij : ℕ × ℕ) : ℂ :=
  orbitwiseNatPrimeSeamCharge (canonicalNthPrime ij.1) rho -
    orbitwiseNatPrimeSeamCharge (canonicalNthPrime ij.2) rho

/-- The literal even Sonin Gram entry indexed by the `i`th and `j`th primes. -/
def canonicalPrimeEvenGramEntry (a : ℝ) (ij : ℕ × ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  evenCentralSoninQuadraticCorner a
    (canonicalNthPrime ij.1) (canonicalNthPrime ij.2)
    (canonicalNthPrime_real_one_lt ij.1) (canonicalNthPrime_real_one_lt ij.2)

/-- A positive summable weight on prime-index pairs. -/
def primeSeamAggregateWeight (ij : ℕ × ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (ij.1 + ij.2)

/-- The canonical nonzero damping of a prime-seam difference.  Dividing by one plus the norm of
the already weighted Gram entry ensures operator-norm summability without imposing a uniform
bound on the Gram family. -/
def primeSeamAggregateCoefficient
    (a : ℝ) (rho : ℂ) (ij : ℕ × ℕ) : ℂ :=
  let d := primeSeamAggregateDifference rho ij
  let G := canonicalPrimeEvenGramEntry a ij
  ((primeSeamAggregateWeight ij / (1 + ‖d‖ * ‖G‖) : ℝ) : ℂ) * d

theorem primeSeamAggregateWeight_pos (ij : ℕ × ℕ) :
    0 < primeSeamAggregateWeight ij := by
  unfold primeSeamAggregateWeight
  positivity

/-- Damping preserves exactly the zero set of every prime-seam difference. -/
theorem primeSeamAggregateCoefficient_eq_zero_iff
    (a : ℝ) (rho : ℂ) (ij : ℕ × ℕ) :
    primeSeamAggregateCoefficient a rho ij = 0 ↔
      primeSeamAggregateDifference rho ij = 0 := by
  let d := primeSeamAggregateDifference rho ij
  let G := canonicalPrimeEvenGramEntry a ij
  let c : ℝ := primeSeamAggregateWeight ij / (1 + ‖d‖ * ‖G‖)
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos (primeSeamAggregateWeight_pos ij) (by positivity)
  have hc : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hcpos.ne'
  change (c : ℂ) * d = 0 ↔ d = 0
  simp [hc]

theorem primeSeamAggregateCoefficient_diagonal
    (a : ℝ) (rho : ℂ) (i : ℕ) :
    primeSeamAggregateCoefficient a rho (i, i) = 0 := by
  apply (primeSeamAggregateCoefficient_eq_zero_iff a rho (i, i)).mpr
  simp [primeSeamAggregateDifference]

/-- Every damped operator entry is bounded by its geometric scalar weight. -/
theorem norm_primeSeamAggregateCoefficient_smul_gram_le
    (a : ℝ) (rho : ℂ) (ij : ℕ × ℕ) :
    ‖primeSeamAggregateCoefficient a rho ij •
        canonicalPrimeEvenGramEntry a ij‖ ≤
      primeSeamAggregateWeight ij := by
  let d := primeSeamAggregateDifference rho ij
  let G := canonicalPrimeEvenGramEntry a ij
  let w := primeSeamAggregateWeight ij
  have hw : 0 ≤ w := (primeSeamAggregateWeight_pos ij).le
  have hx : 0 ≤ ‖d‖ * ‖G‖ :=
    mul_nonneg (norm_nonneg d) (norm_nonneg G)
  have hden : 0 < 1 + ‖d‖ * ‖G‖ := by positivity
  change ‖(((w / (1 + ‖d‖ * ‖G‖) : ℝ) : ℂ) * d) • G‖ ≤ w
  calc
    _ ≤ ‖(((w / (1 + ‖d‖ * ‖G‖) : ℝ) : ℂ) * d)‖ * ‖G‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = w / (1 + ‖d‖ * ‖G‖) * (‖d‖ * ‖G‖) := by
      rw [norm_mul, norm_real, Real.norm_of_nonneg (div_nonneg hw hden.le)]
      ring
    _ ≤ w := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hden).mpr
      exact mul_le_mul_of_nonneg_left (by linarith) hw

theorem summable_primeSeamAggregateWeight :
    Summable primeSeamAggregateWeight := by
  have hgeom : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hprod := hgeom.mul_of_nonneg hgeom
    (fun _ => by positivity) (fun _ => by positivity)
  change Summable fun ij : ℕ × ℕ => (1 / 2 : ℝ) ^ (ij.1 + ij.2)
  simpa only [pow_add] using hprod

set_option maxHeartbeats 500000 in
/-- The canonical all-prime seam Gram series is unconditionally absolutely summable in operator
norm on every fibre. -/
theorem summable_norm_primeSeamAggregateTerm (a : ℝ) (rho : ℂ) :
    Summable fun ij =>
      ‖summableEvenDilationGramTerm a canonicalNthPrime
        canonicalNthPrime_real_one_lt (primeSeamAggregateCoefficient a rho) ij‖ := by
  have hle : ∀ ij,
      ‖summableEvenDilationGramTerm a canonicalNthPrime
        canonicalNthPrime_real_one_lt (primeSeamAggregateCoefficient a rho) ij‖ ≤
        primeSeamAggregateWeight ij := by
    intro ij
    change ‖primeSeamAggregateCoefficient a rho ij •
        canonicalPrimeEvenGramEntry a ij‖ ≤ primeSeamAggregateWeight ij
    exact norm_primeSeamAggregateCoefficient_smul_gram_le a rho ij
  exact Summable.of_nonneg_of_le
    (fun ij => norm_nonneg (summableEvenDilationGramTerm a canonicalNthPrime
      canonicalNthPrime_real_one_lt (primeSeamAggregateCoefficient a rho) ij)) hle
    summable_primeSeamAggregateWeight

/-- One concrete norm-summable all-prime Sonin Gram operator on a strip fibre. -/
def orbitwisePrimeSeamSummableCalkinAggregate (a : ℝ) (rho : ℂ) :
    evenSubspace →L[ℂ] evenSubspace :=
  summableEvenDilationGramAggregate a canonicalNthPrime
    canonicalNthPrime_real_one_lt (primeSeamAggregateCoefficient a rho)

/-- Compactness of the single all-prime aggregate on one fibre. -/
def OrbitwisePrimeSeamSummableCalkinAggregateCompact
    (a : ℝ) (rho : ℂ) : Prop :=
  IsCompactOperator (orbitwisePrimeSeamSummableCalkinAggregate a rho)

/-- Compactness of the aggregate forces coherence of every rational-prime seam charge. -/
theorem orbitwisePrimeSeamChargesCoherent_of_summableCalkinAggregateCompact
    (a : ℝ) (rho : ℂ) (ha : 0 < a)
    (hcompact : OrbitwisePrimeSeamSummableCalkinAggregateCompact a rho) :
    OrbitwisePrimeSeamChargesCoherent rho := by
  have hcoeff :=
    coefficients_eq_zero_of_summableEvenDilationGramAggregate_isCompact
      a ha canonicalNthPrime canonicalNthPrime_prime
      canonicalNthPrime_real_one_lt canonicalNthPrime_injective
      (primeSeamAggregateCoefficient a rho)
      (primeSeamAggregateCoefficient_diagonal a rho)
      (summable_norm_primeSeamAggregateTerm a rho) hcompact
  intro p q hp hq
  have hpRange : p ∈ Set.range canonicalNthPrime := by
    rw [range_canonicalNthPrime]
    exact hp
  have hqRange : q ∈ Set.range canonicalNthPrime := by
    rw [range_canonicalNthPrime]
    exact hq
  obtain ⟨i, rfl⟩ := hpRange
  obtain ⟨j, rfl⟩ := hqRange
  have hc0 : primeSeamAggregateCoefficient a rho (i, j) = 0 := by
    simpa using congrFun hcoeff (i, j)
  exact sub_eq_zero.mp
    ((primeSeamAggregateCoefficient_eq_zero_iff a rho (i, j)).mp hc0)

/-- On the open strip, compactness of one norm-summable aggregate is exactly the critical-line
orientation equation. -/
theorem orbitwisePrimeSeamSummableCalkinAggregateCompact_iff_re_eq_half
    (a : ℝ) (rho : ℂ) (ha : 0 < a)
    (hstrip : 0 < rho.re ∧ rho.re < 1) :
    OrbitwisePrimeSeamSummableCalkinAggregateCompact a rho ↔
      rho.re = 1 / 2 := by
  constructor
  · intro hcompact
    exact (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half hstrip).mp
      (orbitwisePrimeSeamChargesCoherent_of_summableCalkinAggregateCompact
        a rho ha hcompact)
  · intro hre
    have hcoh :=
      (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half hstrip).mpr hre
    have hcoeff : ∀ ij,
        primeSeamAggregateCoefficient a rho ij = 0 := by
      rintro ⟨i, j⟩
      apply (primeSeamAggregateCoefficient_eq_zero_iff a rho (i, j)).mpr
      exact sub_eq_zero.mpr
        (hcoh (canonicalNthPrime i) (canonicalNthPrime j)
          (canonicalNthPrime_prime i) (canonicalNthPrime_prime j))
    have hzero : orbitwisePrimeSeamSummableCalkinAggregate a rho = 0 := by
      unfold orbitwisePrimeSeamSummableCalkinAggregate
        summableEvenDilationGramAggregate
      change (∑' ij, primeSeamAggregateCoefficient a rho ij •
        canonicalPrimeEvenGramEntry a ij) = 0
      have hterm : (fun ij => primeSeamAggregateCoefficient a rho ij •
          canonicalPrimeEvenGramEntry a ij) =
          (fun _ : ℕ × ℕ => (0 : evenSubspace →L[ℂ] evenSubspace)) := by
        funext ij
        rw [hcoeff ij]
        apply ContinuousLinearMap.ext
        intro x
        simp
      rw [hterm]
      simp
    change IsCompactOperator (orbitwisePrimeSeamSummableCalkinAggregate a rho)
    rw [hzero]
    exact isCompactOperator_zero

/-- Compactness of the canonical aggregate on every actual Xi divisor fibre. -/
def XiPrimeSeamSummableCalkinAggregateCompact (a : ℝ) : Prop :=
  ∀ rho : XiDivisorSupport,
    OrbitwisePrimeSeamSummableCalkinAggregateCompact a (rho : ℂ)

/-- **Top-down capstone.**  For every positive Sonin cutoff, compactness of one explicit,
unconditionally norm-summable all-prime Gram operator per Xi divisor fibre is equivalent to RH. -/
theorem xiPrimeSeamSummableCalkinAggregateCompact_iff_riemannHypothesis
    (a : ℝ) (ha : 0 < a) :
    XiPrimeSeamSummableCalkinAggregateCompact a ↔ RiemannHypothesis := by
  rw [← xiPrimeSeamChargesCoherent_iff_riemannHypothesis]
  constructor
  · intro hcompact rho
    exact orbitwisePrimeSeamChargesCoherent_of_summableCalkinAggregateCompact
      a (rho : ℂ) ha (hcompact rho)
  · intro hcoherent rho
    apply (orbitwisePrimeSeamSummableCalkinAggregateCompact_iff_re_eq_half
      a (rho : ℂ) ha (xi_divisor_support_re_mem_open_unit rho)).mpr
    exact (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)).mp (hcoherent rho)

/-- The forward proof-chain interface without an equivalence wrapper. -/
theorem riemannHypothesis_of_xiPrimeSeamSummableCalkinAggregateCompact
    (a : ℝ) (ha : 0 < a)
    (hcompact : XiPrimeSeamSummableCalkinAggregateCompact a) :
    RiemannHypothesis :=
  (xiPrimeSeamSummableCalkinAggregateCompact_iff_riemannHypothesis a ha).mp hcompact

/-- Positive contradiction form: failure of RH produces an actual Xi fibre on which the single
norm-summable aggregate is noncompact. -/
theorem exists_noncompact_primeSeamSummableCalkinAggregate_of_not_riemannHypothesis
    (a : ℝ) (ha : 0 < a) (hRH : ¬ RiemannHypothesis) :
    ∃ rho : XiDivisorSupport,
      ¬ OrbitwisePrimeSeamSummableCalkinAggregateCompact a (rho : ℂ) := by
  by_contra hnone
  apply hRH
  apply riemannHypothesis_of_xiPrimeSeamSummableCalkinAggregateCompact a ha
  intro rho
  by_contra hnoncompact
  exact hnone ⟨rho, hnoncompact⟩

end

end RHTower
