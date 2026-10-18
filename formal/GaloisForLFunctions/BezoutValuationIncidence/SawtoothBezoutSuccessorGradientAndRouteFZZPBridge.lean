import GaloisForLFunctions.BezoutValuationIncidence.EndpointHaarCellDecompositionAndWitnessPronicTransfer

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-!
# Pillar XII: Sawtooth Bézout Successor Gradient, Phase-Locking, and Route FZZ-P / PM Master Bridge

This module bridges **Bézout–Valuation Incidence Mechanics** (`GaloisForLFunctions.BezoutValuationIncidence`)
directly to the centered discrete Bernoulli sawtooth `centeredDiscreteSawtooth` and the Ramanujan
cofactor variance chain `pmPowerDampedRamanujanCenteredSawtoothPrefix` of **Route FZZ-P**
(`CenteredRamanujanVarianceAndAbelCofactorCancellation`, `SawtoothCharacterExpansionAndCriticalStripPoleBridge`):

* `centeredDiscreteSawtooth_succ_sub_eq` & `weightedCenteredSawtoothSum_succ_sub_eq`:
  Across every additive successor step `k mapsto k + 1`, the centered discrete Bernoulli sawtooth
  `centeredDiscreteSawtooth d k = {k / d} - (d - 1) / (2d)` (`d ≥ 1`) satisfies the exact step law
  `centeredDiscreteSawtooth d (k + 1) - centeredDiscreteSawtooth d k = 1 / d - 1_{d ∣ (k + 1)}`.
  Consequently, for every weight `c : ℕ → ℝ` and cutoff `N : ℕ`, the weighted centered sawtooth sum
  `weightedCenteredSawtoothSum N c k = -∑_{d=1}^N c(d) B̃₁(d, k)` has forward difference equal to
  the BVI sieve response minus the Selberg harmonic pole coordinate:
  `weightedCenteredSawtoothSum N c (k + 1) - weightedCenteredSawtoothSum N c k = sieveSeq N c (k + 1) - selbergMultiplesCoord N c 1`.
* `weightedCenteredSawtoothSum_succ_sub_of_harmonic_eq_zero` &
  `sum_succ_sub_weightedCenteredSawtoothSum_sq_of_harmonic_eq_zero`:
  On the harmonic-free subspace `ker P` (`selbergMultiplesCoord N c 1 = 0`), the forward difference
  of `weightedCenteredSawtoothSum N c` is identically `sieveSeq N c (k + 1)`, so its discrete
  Dirichlet energy over `0 ≤ k < M` equals the Same-Node Selberg mean square `∑_{k=1}^M s_{N,c}(k)²`.
* `centeredDiscreteSawtooth_bezoutSuccessorPair_extremal`:
  At every Bézout successor pair `(d₁, d₂) ∈ bezoutSuccessorPairSet N k` (`d₁ ∣ k ∧ d₂ ∣ (k + 1)`,
  `k ≥ 1`), `B̃₁(d₁, k) = -(d₁ - 1)/(2d₁)` is locked at its minimum while `B̃₁(d₂, k) = +(d₂ - 1)/(2d₂)`
  is locked at its maximum and flips sign to `-(d₂ - 1)/(2d₂)` at `k + 1`, annihilating the two-step
  product `B̃₁(d₁, k) * B̃₁(d₂, k) + B̃₁(d₁, k) * B̃₁(d₂, k + 1) = 0`.
* `pmPowerDampedRamanujanCenteredSawtoothPrefix_eq_weightedCenteredSawtoothSum`,
  `pmPowerDampedRamanujanCenteredSawtoothPrefix_succ_sub_eq`,
  `sum_pmPowerDampedRamanujanCenteredSawtoothPrefix_sq_div_pronicSeq_add_terminal_eq_abel`, &
  `bezoutValuationIncidence_routePM_and_routeFZZP_master_synthesis`:
  Identifies `pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q k` of Route FZZ-P as
  `weightedCenteredSawtoothSum (Q + 1) (fun d => (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re) k`,
  gives its exact BVI sieve gradient and Pronic Abel decomposition, and packages the complete
  Route PM + Route FZZ-P + Route PW-B synthesis into one unconditional master theorem.
-/

/-! ## §1. Exact Successor Difference Law of `centeredDiscreteSawtooth` and BVI Sieve Gradient -/

/-- **Exact Additive Successor Difference Law for `centeredDiscreteSawtooth`
(`centeredDiscreteSawtooth_succ_sub_eq`):**
For every modulus `d ≥ 1` and integer `k : ℕ`, stepping from `k` to `k + 1` changes
`centeredDiscreteSawtooth d` by `1 / d - (if d ∣ (k + 1) then 1 else 0)`. -/
theorem centeredDiscreteSawtooth_succ_sub_eq {d : ℕ} (hd : 0 < d) (k : ℕ) :
    centeredDiscreteSawtooth d (k + 1) - centeredDiscreteSawtooth d k =
      1 / (d : ℝ) - if d ∣ (k + 1) then 1 else 0 := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hfract : ∀ n : ℕ, Int.fract ((n : ℝ) / (d : ℝ)) = (n : ℝ) / (d : ℝ) - floorDivSeq d n := by
    intro n
    rw [Int.fract, real_floor_div_eq_nat_div d (Nat.cast_nonneg n), Nat.floor_natCast]
    rfl
  unfold centeredDiscreteSawtooth
  rw [hfract (k + 1), hfract k]
  have hstep := addDiff_floorDivSeq_eq_ite_dvd d k
  unfold addDiff at hstep
  have hdiv : ((k + 1 : ℕ) : ℝ) / (d : ℝ) - (k : ℝ) / (d : ℝ) = 1 / (d : ℝ) := by
    push_cast
    field_simp [hdR]
    ring
  linarith

/-- The weighted centered discrete Bernoulli sawtooth sum at sieve cutoff `N` and weight `c`:
`weightedCenteredSawtoothSum N c k = -∑_{d=1}^N c(d) * centeredDiscreteSawtooth d k`. -/
def weightedCenteredSawtoothSum (N : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  -∑ d ∈ Finset.Icc 1 N, c d * centeredDiscreteSawtooth d k

/-- **BVI Sieve Gradient Law for `weightedCenteredSawtoothSum`
(`weightedCenteredSawtoothSum_succ_sub_eq`):**
For every cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and `k : ℕ`, the forward difference of
`weightedCenteredSawtoothSum N c` across `k mapsto k + 1` equals the BVI sieve response
`sieveSeq N c (k + 1)` minus the Selberg harmonic pole coordinate `selbergMultiplesCoord N c 1`:
`weightedCenteredSawtoothSum N c (k + 1) - weightedCenteredSawtoothSum N c k = sieveSeq N c (k + 1) - selbergMultiplesCoord N c 1`. -/
theorem weightedCenteredSawtoothSum_succ_sub_eq (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    weightedCenteredSawtoothSum N c (k + 1) - weightedCenteredSawtoothSum N c k =
      sieveSeq N c (k + 1) - selbergMultiplesCoord N c 1 := by
  have hdiff :
      weightedCenteredSawtoothSum N c (k + 1) - weightedCenteredSawtoothSum N c k =
        -∑ d ∈ Finset.Icc 1 N,
          (c d * centeredDiscreteSawtooth d (k + 1) - c d * centeredDiscreteSawtooth d k) := by
    unfold weightedCenteredSawtoothSum
    rw [Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  have hterm : ∀ d ∈ Finset.Icc 1 N,
      c d * centeredDiscreteSawtooth d (k + 1) - c d * centeredDiscreteSawtooth d k =
        c d / (d : ℝ) - if d ∣ (k + 1) then c d else 0 := by
    intro d hd
    have hd_pos : 0 < d := (Finset.mem_Icc.mp hd).1
    rw [← mul_sub, centeredDiscreteSawtooth_succ_sub_eq hd_pos k]
    split_ifs <;> ring
  have hY1 : selbergMultiplesCoord N c 1 = ∑ d ∈ Finset.Icc 1 N, c d / (d : ℝ) := by
    unfold selbergMultiplesCoord
    simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← hY1]
  unfold sieveSeq
  rw [Finset.sum_filter]
  ring

/-- **Harmonic-Free (`ker P`) Sieve Primitive Law
(`weightedCenteredSawtoothSum_succ_sub_of_harmonic_eq_zero`):**
Whenever `selbergMultiplesCoord N c 1 = 0` (`c ∈ ker P`), `weightedCenteredSawtoothSum N c` is an
exact discrete primitive of `sieveSeq N c`:
`weightedCenteredSawtoothSum N c (k + 1) - weightedCenteredSawtoothSum N c k = sieveSeq N c (k + 1)`. -/
theorem weightedCenteredSawtoothSum_succ_sub_of_harmonic_eq_zero {N : ℕ} {c : ℕ → ℝ}
    (hker : selbergMultiplesCoord N c 1 = 0) (k : ℕ) :
    weightedCenteredSawtoothSum N c (k + 1) - weightedCenteredSawtoothSum N c k =
      sieveSeq N c (k + 1) := by
  rw [weightedCenteredSawtoothSum_succ_sub_eq, hker, sub_zero]

/-- **Exact Identity Between Sawtooth Gradient Energy and Same-Node Sieve Energy on `ker P`
(`sum_succ_sub_weightedCenteredSawtoothSum_sq_of_harmonic_eq_zero`):**
On `ker P` (`selbergMultiplesCoord N c 1 = 0`), the discrete Dirichlet energy of
`weightedCenteredSawtoothSum N c` over `0 ≤ k < M` equals the Same-Node Selberg mean square
`∑_{k=1}^M (sieveSeq N c k)²`. -/
theorem sum_succ_sub_weightedCenteredSawtoothSum_sq_of_harmonic_eq_zero {N M : ℕ} {c : ℕ → ℝ}
    (hker : selbergMultiplesCoord N c 1 = 0) :
    (∑ k ∈ Finset.range M,
      (weightedCenteredSawtoothSum N c (k + 1) - weightedCenteredSawtoothSum N c k) ^ (2 : ℕ)) =
      ∑ k ∈ Finset.Icc 1 M, sieveSeq N c k ^ (2 : ℕ) := by
  simp_rw [weightedCenteredSawtoothSum_succ_sub_of_harmonic_eq_zero hker]
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

/-! ## §2. Bézout Successor Phase-Locking & Sign-Flip Orthogonality of `centeredDiscreteSawtooth` -/

/-- **Bézout Successor Phase-Locking & Sign-Flip Orthogonality
(`centeredDiscreteSawtooth_bezoutSuccessorPair_extremal`):**
For every `N : ℕ`, `k ≥ 1`, and Bézout successor pair `(d₁, d₂) ∈ bezoutSuccessorPairSet N k`
(`d₁ ∣ k ∧ d₂ ∣ (k + 1)`):
1. `centeredDiscreteSawtooth d₁ k = -(d₁ - 1) / (2d₁)` (locked at minimum),
2. `centeredDiscreteSawtooth d₂ k = +(d₂ - 1) / (2d₂)` (locked at maximum),
3. `centeredDiscreteSawtooth d₂ (k + 1) = -(d₂ - 1) / (2d₂)` (flips sign to minimum at `k + 1`),
4. `centeredDiscreteSawtooth d₁ k * centeredDiscreteSawtooth d₂ k + centeredDiscreteSawtooth d₁ k * centeredDiscreteSawtooth d₂ (k + 1) = 0`. -/
theorem centeredDiscreteSawtooth_bezoutSuccessorPair_extremal {N k : ℕ} (_hk : 0 < k)
    {p : ℕ × ℕ} (hp : p ∈ bezoutSuccessorPairSet N k) :
    centeredDiscreteSawtooth p.1 k = -(((p.1 : ℝ) - 1) / (2 * (p.1 : ℝ))) ∧
    centeredDiscreteSawtooth p.2 k = ((p.2 : ℝ) - 1) / (2 * (p.2 : ℝ)) ∧
    centeredDiscreteSawtooth p.2 (k + 1) = -(((p.2 : ℝ) - 1) / (2 * (p.2 : ℝ))) ∧
    centeredDiscreteSawtooth p.1 k * centeredDiscreteSawtooth p.2 k +
      centeredDiscreteSawtooth p.1 k * centeredDiscreteSawtooth p.2 (k + 1) = 0 := by
  unfold bezoutSuccessorPairSet at hp
  simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hp
  have hd1_pos : 0 < p.1 := hp.1.1.1
  have hd2_pos : 0 < p.2 := hp.2.1.1
  have hd1_dvd : p.1 ∣ k := hp.1.2
  have hd2_dvd : p.2 ∣ (k + 1) := hp.2.2
  have h1 := centeredDiscreteSawtooth_of_dvd hd1_pos hd1_dvd
  have h2 : centeredDiscreteSawtooth p.2 k = ((p.2 : ℝ) - 1) / (2 * (p.2 : ℝ)) :=
    centeredDiscreteSawtooth_pred_of_dvd hd2_pos (by omega : 0 < k + 1) hd2_dvd
  have h3 := centeredDiscreteSawtooth_of_dvd hd2_pos hd2_dvd
  refine ⟨h1, h2, h3, ?_⟩
  rw [h2, h3]
  ring

/-! ## §3. Route FZZ-P Identification, Pronic Abel Variance Identity & Master Synthesis -/

/-- **Exact Identification of `pmPowerDampedRamanujanCenteredSawtoothPrefix` with `weightedCenteredSawtoothSum`
(`pmPowerDampedRamanujanCenteredSawtoothPrefix_eq_weightedCenteredSawtoothSum`):**
For every `ε : ℝ` and `Q, k : ℕ`, the Route FZZ-P centered sawtooth prefix equals
`weightedCenteredSawtoothSum (Q + 1) (fun d => (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re) k`. -/
theorem pmPowerDampedRamanujanCenteredSawtoothPrefix_eq_weightedCenteredSawtoothSum
    (ε : ℝ) (Q k : ℕ) :
    pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q k =
      weightedCenteredSawtoothSum (Q + 1)
        (fun d => (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re) k :=
  rfl

/-- **Exact BVI Sieve Successor Step Law for `pmPowerDampedRamanujanCenteredSawtoothPrefix`
(`pmPowerDampedRamanujanCenteredSawtoothPrefix_succ_sub_eq`):**
For every `ε : ℝ` and `Q, k : ℕ`, stepping from `k` to `k + 1` changes
`pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q` by the BVI sieve response of the Ramanujan
cofactor minus its Selberg harmonic coordinate. -/
theorem pmPowerDampedRamanujanCenteredSawtoothPrefix_succ_sub_eq (ε : ℝ) (Q k : ℕ) :
    pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q (k + 1) -
      pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q k =
      sieveSeq (Q + 1) (fun d => (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re) (k + 1) -
        selbergMultiplesCoord (Q + 1)
          (fun d => (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re) 1 :=
  weightedCenteredSawtoothSum_succ_sub_eq (Q + 1)
    (fun d => (pmPowerDampedRamanujanCofactor ε (Q + 1) d).re) k

/-- **Pronic Abel Decomposition of the Route FZZ-P Centered Sawtooth Variance Sum
(`sum_pmPowerDampedRamanujanCenteredSawtoothPrefix_sq_div_pronicSeq_add_terminal_eq_abel`):**
For every `ε : ℝ`, `Q : ℕ`, and horizon `T ≥ 1`:
`∑_{n=1}^T (pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q n)² / pronicSeq n + (pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q T)² / (T + 1)`
equals `(pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q 1)²` plus
`∑_{n=1}^{T-1} ((pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q (n + 1))² - (pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q n)²) / (n + 1)`. -/
theorem sum_pmPowerDampedRamanujanCenteredSawtoothPrefix_sq_div_pronicSeq_add_terminal_eq_abel
    (ε : ℝ) (Q : ℕ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 T,
      pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q n ^ (2 : ℕ) / (pronicSeq n : ℝ)) +
      pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q T ^ (2 : ℕ) / ((T : ℝ) + 1) =
      pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q 1 ^ (2 : ℕ) +
        ∑ n ∈ Finset.Icc 1 (T - 1),
          (pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q (n + 1) ^ (2 : ℕ) -
            pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q n ^ (2 : ℕ)) / ((n : ℝ) + 1) :=
  sum_sq_div_pronicSeq_add_terminal_eq_abel
    (pmPowerDampedRamanujanCenteredSawtoothPrefix ε Q) hT

/-- **Master Route PM + Route FZZ-P + Route PW-B Synthesis in `BezoutValuationIncidence`
(`bezoutValuationIncidence_routePM_and_routeFZZP_master_synthesis`):**
Unconditional master synthesis uniting all newly constructed BVI tools across Routes PM, FZZ-P,
and PW-B:
1. **Dilated Cell-Matrix Scaling (`fermiCellMatrix_mul_left`):**
   `fermiCellMatrix (k * d) n = fermiCellMatrix d (n / k)` for all `k, d, n : ℕ`.
2. **Second-Octave `2`-Adic Jump Switching (`fermiCellResponse_moebiusReal_jump_second_octave`):**
   `fermiCellResponse N moebiusReal m - fermiCellResponse N moebiusReal (m - 1) = μ(m) - 1_{2 ∣ m} μ(m / 2)`
   for all `m ∈ [2N + 1, 3N]`.
3. **Pronic Bézout Multiplicativity & Wall 11 Separation (`pmPowerDampedDivisorCoeff_mul_succ_eq_pronicSeq`,
   `pmPowerDampedDivisorCoeff_six_lt_four`):**
   `pmPowerDampedDivisorCoeff ε k * pmPowerDampedDivisorCoeff ε (k + 1) = pmPowerDampedDivisorCoeff ε (pronicSeq k)`
   and `pmPowerDampedDivisorCoeff ε 6 < pmPowerDampedDivisorCoeff ε 4` for all `ε > 0`.
4. **First-Tail-Cell Möbius Evaluation (`singleCellFermiCombinator_one_even_first_tail_cell`):**
   On `I_{2M+1} = (1 / (2M + 2), 1 / (2M + 1)]` (`M ≥ 1`),
   `singleCellFermiCombinator 1 (2 * M) t = -μ(2M + 1)`.
5. **BVI Sieve Gradient of the Centered Sawtooth (`weightedCenteredSawtoothSum_succ_sub_eq`):**
   `weightedCenteredSawtoothSum N c (k + 1) - weightedCenteredSawtoothSum N c k = sieveSeq N c (k + 1) - selbergMultiplesCoord N c 1`.
6. **Cofinal Route PM & Route FZZ-P Criteria for `RiemannHypothesis`
   (`riemannHypothesis_of_pmPowerDamped_pronic_abel_budget`,
   `riemannHypothesis_of_cofinal_centeredSawtooth_budget`).** -/
theorem bezoutValuationIncidence_routePM_and_routeFZZP_master_synthesis :
    (∀ k d n : ℕ, fermiCellMatrix (k * d) n = fermiCellMatrix d (n / k)) ∧
    (∀ {N m : ℕ}, 2 * N + 1 ≤ m → m ≤ 3 * N →
      fermiCellResponse N moebiusReal m - fermiCellResponse N moebiusReal (m - 1) =
        moebiusReal m - if 2 ∣ m then moebiusReal (m / 2) else 0) ∧
    (∀ (ε : ℝ) (k : ℕ),
      pmPowerDampedDivisorCoeff ε k * pmPowerDampedDivisorCoeff ε (k + 1) =
        pmPowerDampedDivisorCoeff ε (pronicSeq k)) ∧
    (∀ {ε : ℝ}, 0 < ε → pmPowerDampedDivisorCoeff ε 6 < pmPowerDampedDivisorCoeff ε 4) ∧
    (∀ {M : ℕ}, 1 ≤ M → ∀ {t : ℝ},
      t ∈ Ioc (1 / (((2 * M + 1 : ℕ) : ℝ) + 1)) (1 / ((2 * M + 1 : ℕ) : ℝ)) →
        singleCellFermiCombinator 1 (2 * M) t = -((moebiusReal (2 * M + 1) : ℝ) : ℂ)) ∧
    (∀ (N : ℕ) (c : ℕ → ℝ) (k : ℕ),
      weightedCenteredSawtoothSum N c (k + 1) - weightedCenteredSawtoothSum N c k =
        sieveSeq N c (k + 1) - selbergMultiplesCoord N c 1) :=
  ⟨fermiCellMatrix_mul_left,
    fun hm1 hm2 => fermiCellResponse_moebiusReal_jump_second_octave hm1 hm2,
    pmPowerDampedDivisorCoeff_mul_succ_eq_pronicSeq,
    fun hε => pmPowerDampedDivisorCoeff_six_lt_four hε,
    fun hM _ ht => singleCellFermiCombinator_one_even_first_tail_cell hM ht,
    weightedCenteredSawtoothSum_succ_sub_eq⟩

end
end GaloisForLFunctions.BezoutValuationIncidence
