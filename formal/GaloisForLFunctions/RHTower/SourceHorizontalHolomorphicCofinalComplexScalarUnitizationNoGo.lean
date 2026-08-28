import GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicCofinalScalarUnitizationNoGo
import GaloisForLFunctions.HTGeometry.PowerSumTorelli
import GaloisForLFunctions.RHTower.PrimeLogTripleCluster

/-!
# Cofinal complex-scalar unitization third-jet no-go for the holomorphic SC reservoir

This module closes the complex-phase survivor left by the real-scalar SC obstruction. For every
complex scalar sequence `c`, it computes the exact central jets of the complete
coefficient-faithful holomorphic prime Gamma-Bockstein reservoir determinant:

* the second jet is `-2 c_m^2 e₂(q)`;
* the third jet is `12 c_m^3 e₃(q)`.

The positive neutral-jet packet mass diverges, each neutral jet is at most two, and a cubic
Newton--Girard law gives `S^3 ≤ 12 e₃` once `S ≥ 12`. Compact-open convergence to normalized
centered Xi would therefore force `‖c_m‖ S_m → 0` through Xi's zero third central jet. The exact
second jet would then vanish, contradicting Xi's strictly negative normalized curvature.

Arbitrary complex phases, oscillations, and decay rates are covered. No RH assumption,
zero-location input, numerical computation, or nonstandard axiom is used.
-/

open Complex Filter Topology Set
open scoped BigOperators Matrix

namespace RHTower

noncomputable section

theorem six_mul_sum_powersetCard_three_eq_powerSums
    {n : ℕ} (q : Fin n → ℝ) :
    6 * (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard 3,
      ∏ i ∈ s, q i) =
      2 * ∑ i, q i ^ 3 -
        3 * (∑ i, q i) * (∑ i, q i ^ 2) + (∑ i, q i) ^ 3 := by
  have h := GaloisForLFunctions.secularMoment_girard_three
    (fun i : Fin n => (q i : ℂ))
  rw [Finset.esymm_map_val] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

theorem preDivisorHolomorphicPrimeNeutralJet_le_two (p : Nat.Primes) :
    preDivisorHolomorphicPrimeNeutralJet p ≤ 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hlog : Real.log (p : ℝ) ≤ (p : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hp
    linarith
  calc
    preDivisorHolomorphicPrimeNeutralJet p ≤
        2 * (1 / (p : ℝ)) * Real.log (p : ℝ) := by
      unfold preDivisorHolomorphicPrimeNeutralJet
      gcongr
      exact primeActivationOccupancyFisherDensity_le_one_div p
    _ ≤ 2 * (1 / (p : ℝ)) * (p : ℝ) := by
      gcongr
    _ = 2 := by field_simp

theorem log_two_div_two_mul_primeReciprocal_le_neutralJet (p : Nat.Primes) :
    Real.log 2 / 2 * (1 / (p : ℝ)) ≤
      preDivisorHolomorphicPrimeNeutralJet p := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hp
      (by exact_mod_cast p.prop.two_le)
  calc
    Real.log 2 / 2 * (1 / (p : ℝ)) =
        2 * (1 / (4 * (p : ℝ))) * Real.log 2 := by ring
    _ ≤ 2 * primeActivationOccupancyFisherDensity p * Real.log 2 := by
      gcongr
      exact one_div_four_mul_le_primeActivationOccupancyFisherDensity p
    _ ≤ 2 * primeActivationOccupancyFisherDensity p * Real.log (p : ℝ) := by
      gcongr
      exact mul_nonneg (by norm_num) (primeActivationOccupancyFisherDensity_pos p).le
    _ = preDivisorHolomorphicPrimeNeutralJet p := rfl

theorem nthPrimePoint_eq_nthPrimeSubtype (n : ℕ) :
    nthPrimePoint n = nthPrimeSubtype n := by
  apply Subtype.ext
  rfl

theorem not_summable_preDivisorHolomorphicPrimeNeutralJet_nthPrimePoint :
    ¬ Summable (fun n =>
      preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint n)) := by
  intro hsum
  have hminor : Summable (fun n =>
      Real.log 2 / 2 * (1 / ((nthPrimePoint n : Nat.Primes) : ℝ))) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (by positivity) (by positivity))
      (fun n => log_two_div_two_mul_primeReciprocal_le_neutralJet (nthPrimePoint n))
      hsum
  have hscaled := hminor.mul_left (2 / Real.log 2)
  have hrecip : Summable (fun n => 1 / ((nthPrimePoint n : Nat.Primes) : ℝ)) := by
    refine hscaled.congr fun n => ?_
    have hlogne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp
  apply not_summable_nthPrime_reciprocal
  refine hrecip.congr fun n => ?_
  rw [nthPrimePoint_eq_nthPrimeSubtype]

theorem tendsto_neutralJet_partialSum_atTop :
    Tendsto (fun n => ∑ i ∈ Finset.range n,
      preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) atTop atTop := by
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => preDivisorHolomorphicPrimeNeutralJet_nonneg (nthPrimePoint n))).mp
      not_summable_preDivisorHolomorphicPrimeNeutralJet_nthPrimePoint

theorem sum_pow_three_le_twelve_mul_sum_powersetCard_three
    {n : ℕ} (q : Fin n → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq2 : ∀ i, q i ≤ 2)
    (hS : 12 ≤ ∑ i, q i) :
    (∑ i, q i) ^ 3 ≤
      12 * ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard 3,
        ∏ i ∈ s, q i := by
  let S : ℝ := ∑ i, q i
  let P2 : ℝ := ∑ i, q i ^ 2
  let P3 : ℝ := ∑ i, q i ^ 3
  let E3 : ℝ := ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard 3,
    ∏ i ∈ s, q i
  have hnewton : 6 * E3 = 2 * P3 - 3 * S * P2 + S ^ 3 := by
    exact six_mul_sum_powersetCard_three_eq_powerSums q
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hq0 i
  have hP20 : 0 ≤ P2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hP30 : 0 ≤ P3 := Finset.sum_nonneg fun i _ => pow_nonneg (hq0 i) 3
  have hP2 : P2 ≤ 2 * S := by
    dsimp only [P2, S]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    nlinarith [hq0 i, hq2 i]
  have hSP2 : S * P2 ≤ 2 * S ^ 2 := by
    nlinarith [mul_nonneg hS0 (sub_nonneg.mpr hP2)]
  have hlarge : 6 * S ^ 2 ≤ S ^ 3 / 2 := by
    nlinarith [sq_nonneg S, mul_nonneg (sq_nonneg S) (sub_nonneg.mpr hS)]
  change 12 ≤ S at hS
  change S ^ 3 ≤ 12 * E3
  nlinarith

theorem iteratedDeriv_two_scaledComplex_preDivisorHolomorphicPrimeBockstein_zero
    (c : ℂ) (p : Nat.Primes) :
    iteratedDeriv 2
        (fun z => c * preDivisorHolomorphicPrimeBockstein z p) 0 = 0 := by
  unfold preDivisorHolomorphicPrimeBockstein
  rw [show (fun z : ℂ => c *
      ((primeActivationOccupancyFisherDensity p : ℂ) *
        (Complex.exp (-((Real.log (p : ℝ) : ℂ) * z)) -
          Complex.exp ((Real.log (p : ℝ) : ℂ) * z)))) =
      fun z : ℂ =>
        (c * (primeActivationOccupancyFisherDensity p : ℂ)) *
          (Complex.exp ((-(Real.log (p : ℝ) : ℂ)) * z) -
            Complex.exp ((Real.log (p : ℝ) : ℂ) * z)) by
      funext z
      ring]
  rw [iteratedDeriv_const_mul_field]
  change (c * (primeActivationOccupancyFisherDensity p : ℂ)) *
    iteratedDeriv 2
      ((fun z => Complex.exp ((-(Real.log (p : ℝ) : ℂ)) * z)) -
        (fun z => Complex.exp ((Real.log (p : ℝ) : ℂ) * z))) 0 = 0
  have hneg : iteratedDeriv 2
      (fun z => Complex.exp ((-(Real.log (p : ℝ) : ℂ)) * z)) 0 =
        (Real.log (p : ℝ) : ℂ) ^ 2 := by
    simpa using congrFun
      (HurwitzExp.iteratedDeriv_expLin (-(Real.log (p : ℝ) : ℂ)) 2) 0
  have hpos : iteratedDeriv 2
      (fun z => Complex.exp ((Real.log (p : ℝ) : ℂ) * z)) 0 =
        (Real.log (p : ℝ) : ℂ) ^ 2 := by
    simpa only [mul_zero, Complex.exp_zero, mul_one] using congrFun
      (HurwitzExp.iteratedDeriv_expLin (Real.log (p : ℝ) : ℂ) 2) 0
  rw [iteratedDeriv_sub
    (HurwitzExp.contDiff_expLin (-(Real.log (p : ℝ) : ℂ))).contDiffAt
    (HurwitzExp.contDiff_expLin (Real.log (p : ℝ) : ℂ)).contDiffAt,
    hneg, hpos, sub_self, mul_zero]

theorem iteratedDeriv_three_finset_prod_zero_of_four_le_card
    {ι : Type*} [DecidableEq ι] (f : ι → ℂ → ℂ) (s : Finset ι)
    (hf : ∀ i, Differentiable ℂ (f i)) (hz : ∀ i, f i 0 = 0)
    (hs : 4 ≤ s.card) :
    iteratedDeriv 3 (fun z => ∏ i ∈ s, f i z) 0 = 0 := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have heraseThree : 3 ≤ (s.erase i).card := by
    rw [Finset.card_erase_of_mem hi]
    omega
  have heraseTwo : 2 ≤ (s.erase i).card := by omega
  have heraseNonempty : (s.erase i).Nonempty := Finset.card_pos.mp (by omega)
  have hfun : (fun z => ∏ j ∈ s, f j z) =
      fun z => f i z * ∏ j ∈ s.erase i, f j z := by
    funext z
    exact (Finset.mul_prod_erase s (fun j => f j z) hi).symm
  rw [hfun]
  change iteratedDeriv 3 ((f i) * (fun z => ∏ j ∈ s.erase i, f j z)) 0 = 0
  rw [iteratedDeriv_mul
    (hf i).contDiff.contDiffAt
    ((Differentiable.fun_finsetProd fun j _ => hf j).contDiff.contDiffAt)]
  have hzero := finset_prod_zero_of_nonempty f hz heraseNonempty
  have hone := iteratedDeriv_one_finset_prod_zero_of_two_le_card f (s.erase i) hf hz heraseTwo
  have htwo := iteratedDeriv_two_finset_prod_zero_of_three_le_card
    f (s.erase i) hf hz heraseThree
  norm_num [Finset.sum_range_succ, hz i, hzero, hone, htwo]

theorem iteratedDeriv_three_finset_prod_eq_of_card_eq_three
    {ι : Type*} [DecidableEq ι] (f : ι → ℂ → ℂ) (s : Finset ι)
    (hf : ∀ i, Differentiable ℂ (f i)) (hz : ∀ i, f i 0 = 0)
    (hs : s.card = 3) :
    iteratedDeriv 3 (fun z => ∏ i ∈ s, f i z) 0 =
      6 * ∏ i ∈ s, iteratedDeriv 1 (f i) 0 := by
  obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp hs
  have hfun : (fun z => ∏ l ∈ ({i, j, k} : Finset ι), f l z) =
      fun z => f i z * (f j z * f k z) := by
    funext z
    simp [hij, hik, hjk]
  rw [hfun]
  change iteratedDeriv 3 ((f i) * ((f j) * (f k))) 0 = _
  rw [iteratedDeriv_mul
    (hf i).contDiff.contDiffAt
    ((hf j).mul (hf k)).contDiff.contDiffAt]
  have hjkzero : f j 0 * f k 0 = 0 := by simp [hz]
  have hjkone : iteratedDeriv 1 ((f j) * (f k)) 0 = 0 := by
    rw [iteratedDeriv_mul
      (hf j).contDiff.contDiffAt (hf k).contDiff.contDiffAt]
    norm_num [Finset.sum_range_succ, hz]
  have hjktwo : iteratedDeriv 2 ((f j) * (f k)) 0 =
      2 * iteratedDeriv 1 (f j) 0 * iteratedDeriv 1 (f k) 0 := by
    rw [iteratedDeriv_mul
      (hf j).contDiff.contDiffAt (hf k).contDiff.contDiffAt]
    norm_num [Finset.sum_range_succ, hz]
  norm_num [Finset.sum_range_succ, hz, hjkzero, hjkone, hjktwo, hij, hik, hjk]
  ring

theorem iteratedDeriv_three_finset_prod_eq_zero_of_card_eq_two
    {ι : Type*} [DecidableEq ι] (f : ι → ℂ → ℂ) (s : Finset ι)
    (hf : ∀ i, Differentiable ℂ (f i)) (hz : ∀ i, f i 0 = 0)
    (htwo : ∀ i, iteratedDeriv 2 (f i) 0 = 0)
    (hs : s.card = 2) :
    iteratedDeriv 3 (fun z => ∏ i ∈ s, f i z) 0 = 0 := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hs
  have hfun : (fun z => ∏ k ∈ ({i, j} : Finset ι), f k z) =
      fun z => f i z * f j z := by
    funext z
    simp [hij]
  rw [hfun]
  change iteratedDeriv 3 ((f i) * (f j)) 0 = 0
  rw [iteratedDeriv_mul
    (hf i).contDiff.contDiffAt (hf j).contDiff.contDiffAt]
  norm_num [Finset.sum_range_succ, hz, htwo]

/-- Complex scalar unitization of the complete coefficient-faithful holomorphic SC reservoir. -/
def preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant
    (c : ℕ → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  (1 + c m •
    preDivisorRiggedPrimeHolomorphicReservoirMatrix (m + 1) z).det

theorem differentiable_preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant
    (c : ℕ → ℂ) (m : ℕ) :
    Differentiable ℂ
      (preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant c m) := by
  unfold preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant
  unfold preDivisorRiggedPrimeHolomorphicReservoirMatrix
  unfold preDivisorHolomorphicPrimeBockstein
  simp only [Matrix.det_apply', Matrix.add_apply, Matrix.smul_apply,
    Matrix.mul_diagonal]
  fun_prop

theorem preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant_eq_complexReservoir
    (c : ℕ → ℂ) (m : ℕ) (z : ℂ) :
    preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant c m z =
      unitizedComplexReservoirDeterminant
        (fun i : Fin (m + 3) =>
          c m * preDivisorHolomorphicPrimeBockstein z (nthPrimePoint i)) := by
  rw [preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant,
    unitizedComplexReservoirDeterminant]
  have hmat : c m •
      preDivisorRiggedPrimeHolomorphicReservoirMatrix (m + 1) z =
    complexReservoirDiagonalMatrix
      (fun i : Fin (m + 3) =>
        c m * preDivisorHolomorphicPrimeBockstein z (nthPrimePoint i)) := by
    ext i j
    rw [Matrix.smul_apply, preDivisorRiggedPrimeHolomorphicReservoirMatrix,
      Matrix.mul_diagonal, complexReservoirDiagonalMatrix_apply]
    by_cases hij : i = j
    · subst j
      simp [holomorphicReservoirBaseMatrix, holomorphicReservoirColumn,
        holomorphicReservoirRow, complexReservoirBaseMatrix,
        complexReservoirOnesMatrix, Matrix.mul_apply]
    · simp [holomorphicReservoirBaseMatrix, holomorphicReservoirColumn,
        holomorphicReservoirRow, complexReservoirBaseMatrix,
        complexReservoirOnesMatrix, Matrix.mul_apply, hij]
  rw [hmat]

theorem iteratedDeriv_one_scaledComplex_preDivisorHolomorphicPrimeBockstein_zero
    (c : ℂ) (p : Nat.Primes) :
    iteratedDeriv 1
        (fun z => c * preDivisorHolomorphicPrimeBockstein z p) 0 =
      -c * (preDivisorHolomorphicPrimeNeutralJet p : ℂ) := by
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_one_preDivisorHolomorphicPrimeBockstein_zero]
  simp only [preDivisorHolomorphicPrimeNeutralJet, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

theorem iteratedDeriv_two_preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant
    (c : ℕ → ℂ) (m : ℕ) :
    iteratedDeriv 2
        (preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant c m) 0 =
      -(2 : ℂ) * (c m) ^ 2 *
        ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
          ∏ i ∈ s, (preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) : ℂ) := by
  let f : Fin (m + 3) → ℂ → ℂ := fun i z =>
    c m * preDivisorHolomorphicPrimeBockstein z (nthPrimePoint i)
  have hf : ∀ i, Differentiable ℂ (f i) := by
    intro i
    exact (differentiable_const (c m)).mul
      (differentiable_preDivisorHolomorphicPrimeBockstein (nthPrimePoint i))
  have hz : ∀ i, f i 0 = 0 := by
    intro i
    simp [f, preDivisorHolomorphicPrimeBockstein_zero]
  have hone : ∀ i, iteratedDeriv 1 (f i) 0 =
      -(c m) *
        (preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) : ℂ) := by
    intro i
    exact iteratedDeriv_one_scaledComplex_preDivisorHolomorphicPrimeBockstein_zero
      (c m) (nthPrimePoint i)
  have hfun : preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant c m =
      fun z => ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powerset,
        (1 - (s.card : ℂ)) * ∏ i ∈ s, f i z := by
    funext z
    rw [preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant_eq_complexReservoir,
      unitizedComplexReservoirDeterminant_eq_sum_powerset]
  rw [hfun]
  rw [HurwitzExp.iteratedDeriv_finset_sum]
  · have hterm : ∀ s : Finset (Fin (m + 3)),
        iteratedDeriv 2
            (fun z => (1 - (s.card : ℂ)) * ∏ i ∈ s, f i z) 0 =
          if s.card = 2 then
            -(2 : ℂ) * (c m) ^ 2 *
              ∏ i ∈ s,
                (preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) : ℂ)
          else 0 := by
      intro s
      by_cases htwo : s.card = 2
      · rw [if_pos htwo, iteratedDeriv_const_mul_field,
          iteratedDeriv_two_finset_prod_eq_of_card_eq_two f s hf hz htwo]
        have hprod :
            ∏ i ∈ s, iteratedDeriv 1 (f i) 0 =
              (c m) ^ 2 *
                ∏ i ∈ s,
                  (preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) : ℂ) := by
          obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp htwo
          simp [hone, hij]
          ring
        rw [hprod, htwo]
        norm_num
        ring
      · rw [if_neg htwo]
        by_cases hzero : s.card = 0
        · have hs : s = ∅ := Finset.card_eq_zero.mp hzero
          subst s
          simp [iteratedDeriv_const]
        by_cases honecard : s.card = 1
        · rw [iteratedDeriv_const_mul_field, honecard]
          norm_num
        · have hthree : 3 ≤ s.card := by omega
          rw [iteratedDeriv_const_mul_field,
            iteratedDeriv_two_finset_prod_zero_of_three_le_card f s hf hz hthree]
          simp
    simp_rw [hterm]
    rw [Finset.mul_sum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  · intro s hs
    have hprod : ContDiff ℂ 2 (fun z => ∏ i ∈ s, f i z) :=
      (Differentiable.fun_finsetProd fun i _ => hf i).contDiff
    exact (contDiff_const : ContDiff ℂ 2
      (fun _ : ℂ => (1 - (s.card : ℂ)))).mul hprod

theorem iteratedDeriv_three_preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant
    (c : ℕ → ℂ) (m : ℕ) :
    iteratedDeriv 3
        (preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant c m) 0 =
      (12 : ℂ) * (c m) ^ 3 *
        ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 3,
          ∏ i ∈ s, (preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) : ℂ) := by
  let f : Fin (m + 3) → ℂ → ℂ := fun i z =>
    c m * preDivisorHolomorphicPrimeBockstein z (nthPrimePoint i)
  have hf : ∀ i, Differentiable ℂ (f i) := by
    intro i
    exact (differentiable_const (c m)).mul
      (differentiable_preDivisorHolomorphicPrimeBockstein (nthPrimePoint i))
  have hz : ∀ i, f i 0 = 0 := by
    intro i
    simp [f, preDivisorHolomorphicPrimeBockstein_zero]
  have hone : ∀ i, iteratedDeriv 1 (f i) 0 =
      -(c m) *
        (preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) : ℂ) := by
    intro i
    exact iteratedDeriv_one_scaledComplex_preDivisorHolomorphicPrimeBockstein_zero
      (c m) (nthPrimePoint i)
  have htwo : ∀ i, iteratedDeriv 2 (f i) 0 = 0 := by
    intro i
    exact iteratedDeriv_two_scaledComplex_preDivisorHolomorphicPrimeBockstein_zero
      (c m) (nthPrimePoint i)
  have hfun : preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant c m =
      fun z => ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powerset,
        (1 - (s.card : ℂ)) * ∏ i ∈ s, f i z := by
    funext z
    rw [preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant_eq_complexReservoir,
      unitizedComplexReservoirDeterminant_eq_sum_powerset]
  rw [hfun]
  rw [HurwitzExp.iteratedDeriv_finset_sum]
  · have hterm : ∀ s : Finset (Fin (m + 3)),
        iteratedDeriv 3
            (fun z => (1 - (s.card : ℂ)) * ∏ i ∈ s, f i z) 0 =
          if s.card = 3 then
            (12 : ℂ) * (c m) ^ 3 *
              ∏ i ∈ s,
                (preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) : ℂ)
          else 0 := by
      intro s
      by_cases hthree : s.card = 3
      · rw [if_pos hthree, iteratedDeriv_const_mul_field,
          iteratedDeriv_three_finset_prod_eq_of_card_eq_three f s hf hz hthree]
        have hprod :
            ∏ i ∈ s, iteratedDeriv 1 (f i) 0 =
              -(c m) ^ 3 *
                ∏ i ∈ s,
                  (preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) : ℂ) := by
          obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp hthree
          simp [hone, hij, hik, hjk]
          ring
        rw [hprod, hthree]
        norm_num
        ring
      · rw [if_neg hthree]
        by_cases hzero : s.card = 0
        · have hs : s = ∅ := Finset.card_eq_zero.mp hzero
          subst s
          simp [iteratedDeriv_const]
        by_cases honecard : s.card = 1
        · rw [iteratedDeriv_const_mul_field, honecard]
          norm_num
        by_cases htwocard : s.card = 2
        · rw [iteratedDeriv_const_mul_field,
            iteratedDeriv_three_finset_prod_eq_zero_of_card_eq_two
              f s hf hz htwo htwocard]
          simp
        · have hfour : 4 ≤ s.card := by omega
          rw [iteratedDeriv_const_mul_field,
            iteratedDeriv_three_finset_prod_zero_of_four_le_card f s hf hz hfour]
          simp
    simp_rw [hterm]
    rw [Finset.mul_sum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  · intro s hs
    have hprod : ContDiff ℂ 3 (fun z => ∏ i ∈ s, f i z) :=
      (Differentiable.fun_finsetProd fun i _ => hf i).contDiff
    exact (contDiff_const : ContDiff ℂ 3
      (fun _ : ℂ => (1 - (s.card : ℂ)))).mul hprod

theorem tendsto_neutralJet_packetSum_atTop :
    Tendsto (fun m => ∑ i : Fin (m + 3),
      preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) atTop atTop := by
  have hshift : Tendsto (fun m : ℕ => m + 3) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have h := tendsto_neutralJet_partialSum_atTop.comp hshift
  refine h.congr' (Eventually.of_forall fun m => ?_)
  change (∑ i ∈ Finset.range (m + 3),
      preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) =
    ∑ i : Fin (m + 3),
      preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)
  symm
  exact Fin.sum_univ_eq_sum_range
    (fun i => preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) (m + 3)

theorem tendsto_zero_of_nonnegative_cube_tendsto_zero
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hcube : Tendsto (fun n => (u n) ^ 3) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hcube ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hcube (ε ^ 3) (pow_pos hε 3)
  refine ⟨N, fun n hn => ?_⟩
  have hpow := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg (hu n) 3)] at hpow
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hu n)]
  by_contra hnot
  have heu : ε ≤ u n := le_of_not_gt hnot
  have hfactorNonneg :
      0 ≤ (u n - ε) * ((u n) ^ 2 + u n * ε + ε ^ 2) := by
    exact mul_nonneg (sub_nonneg.mpr heu)
      (add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (hu n) hε.le)) (sq_nonneg _))
  have hfactor :
      (u n) ^ 3 - ε ^ 3 =
        (u n - ε) * ((u n) ^ 2 + u n * ε + ε ^ 2) := by ring
  nlinarith

theorem absScale_packetSum_cube_le_norm_iteratedDeriv_three
    (c : ℕ → ℂ) (m : ℕ)
    (hS : 12 ≤ ∑ i : Fin (m + 3),
      preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) :
    (‖c m‖ * ∑ i : Fin (m + 3),
      preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) ^ 3 ≤
      ‖iteratedDeriv 3
        (preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant c m) 0‖ := by
  let q : Fin (m + 3) → ℝ := fun i =>
    preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)
  let E3 : ℝ :=
    ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 3,
      ∏ i ∈ s, q i
  have hq0 : ∀ i, 0 ≤ q i := fun i =>
    preDivisorHolomorphicPrimeNeutralJet_nonneg (nthPrimePoint i)
  have hq2 : ∀ i, q i ≤ 2 := fun i =>
    preDivisorHolomorphicPrimeNeutralJet_le_two (nthPrimePoint i)
  have hcubic : (∑ i, q i) ^ 3 ≤ 12 * E3 :=
    sum_pow_three_le_twelve_mul_sum_powersetCard_three q hq0 hq2 hS
  have hE30 : 0 ≤ E3 := by
    exact Finset.sum_nonneg fun s hs =>
      Finset.prod_nonneg fun i hi => hq0 i
  have hcast :
      (∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 3,
          ∏ i ∈ s, (q i : ℂ)) = (E3 : ℂ) := by
    dsimp only [E3]
    push_cast
    rfl
  rw [iteratedDeriv_three_preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant]
  change (‖c m‖ * ∑ i, q i) ^ 3 ≤
    ‖(12 : ℂ) * (c m) ^ 3 *
      ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 3,
        ∏ i ∈ s, (q i : ℂ)‖
  rw [hcast]
  calc
    (‖c m‖ * ∑ i, q i) ^ 3 =
        ‖c m‖ ^ 3 * (∑ i, q i) ^ 3 := by ring
    _ ≤ ‖c m‖ ^ 3 * (12 * E3) :=
      mul_le_mul_of_nonneg_left hcubic (pow_nonneg (norm_nonneg _) 3)
    _ = ‖(12 : ℂ) * (c m) ^ 3 * (E3 : ℂ)‖ := by
      rw [norm_mul, norm_mul, norm_ofNat, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hE30]
      ring

theorem tendsto_norm_scale_mul_neutralJet_packetSum_zero_of_thirdJet_zero
    (c : ℕ → ℂ)
    (hjet : Tendsto (fun m => iteratedDeriv 3
      (preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant c m) 0)
      atTop (𝓝 0)) :
    Tendsto (fun m => ‖c m‖ * ∑ i : Fin (m + 3),
      preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) atTop (𝓝 0) := by
  have hlarge : ∀ᶠ m in atTop, 12 ≤ ∑ i : Fin (m + 3),
      preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) :=
    (tendsto_atTop.1 tendsto_neutralJet_packetSum_atTop) 12
  have hsum0 : ∀ m, 0 ≤ ∑ i : Fin (m + 3),
      preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) := by
    intro m
    exact Finset.sum_nonneg fun i _ =>
      preDivisorHolomorphicPrimeNeutralJet_nonneg (nthPrimePoint i)
  have hnorm : Tendsto (fun m => ‖iteratedDeriv 3
      (preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant c m) 0‖)
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using (continuous_norm.tendsto 0).comp hjet
  have hcube : Tendsto (fun m =>
      (‖c m‖ * ∑ i : Fin (m + 3),
        preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) ^ 3)
      atTop (𝓝 0) := by
    refine squeeze_zero'
      (Eventually.of_forall fun m => pow_nonneg
        (mul_nonneg (norm_nonneg _) (hsum0 m)) 3)
      ?_ hnorm
    filter_upwards [hlarge] with m hm
    exact absScale_packetSum_cube_le_norm_iteratedDeriv_three c m hm
  exact tendsto_zero_of_nonnegative_cube_tendsto_zero _
    (fun m => mul_nonneg (norm_nonneg _) (hsum0 m))
    hcube

theorem norm_iteratedDeriv_two_complexScalarUnitizedDeterminant_le
    (c : ℕ → ℂ) (m : ℕ) :
    ‖iteratedDeriv 2
        (preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant c m) 0‖ ≤
      (‖c m‖ * ∑ i : Fin (m + 3),
        preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) ^ 2 := by
  let q : Fin (m + 3) → ℝ := fun i =>
    preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)
  have hq : ∀ i, 0 ≤ q i := fun i =>
    preDivisorHolomorphicPrimeNeutralJet_nonneg (nthPrimePoint i)
  have hpair :=
    GaloisForLFunctions.HTGeometry.factorial_mul_sum_powersetCard_le_sum_pow
      hq (Finset.univ : Finset (Fin (m + 3))) 2
  norm_num at hpair
  have hpairsNonneg : 0 ≤
      ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
        ∏ i ∈ s, q i := by
    exact Finset.sum_nonneg fun s hs =>
      Finset.prod_nonneg fun i hi => hq i
  have hcast :
      (∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
          ∏ i ∈ s, (q i : ℂ)) =
        ((∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
          ∏ i ∈ s, q i : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [iteratedDeriv_two_preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant]
  change ‖-(2 : ℂ) * (c m) ^ 2 *
      ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
        ∏ i ∈ s, (q i : ℂ)‖ ≤ _
  rw [hcast]
  calc
    ‖-(2 : ℂ) * (c m) ^ 2 *
        ((∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
          ∏ i ∈ s, q i : ℝ) : ℂ)‖ =
        ‖c m‖ ^ 2 *
          (2 * ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
            ∏ i ∈ s, q i) := by
      have hnormPairs :
          ‖((∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
            ∏ i ∈ s, q i : ℝ) : ℂ)‖ =
            ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
              ∏ i ∈ s, q i := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpairsNonneg]
      rw [norm_mul, norm_mul, norm_neg, norm_ofNat, norm_pow, hnormPairs]
      ring
    _ ≤ ‖c m‖ ^ 2 * (∑ i : Fin (m + 3), q i) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hpair (sq_nonneg _)
    _ = (‖c m‖ * ∑ i : Fin (m + 3),
        preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) ^ 2 := by
      ring

theorem tendsto_iteratedDeriv_two_complexScalarUnitizedDeterminant_zero
    (c : ℕ → ℂ)
    (hscale : Tendsto (fun m => ‖c m‖ * ∑ i : Fin (m + 3),
      preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) atTop (𝓝 0)) :
    Tendsto (fun m => iteratedDeriv 2
      (preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant c m) 0)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero
    (fun m => norm_nonneg _)
    (norm_iteratedDeriv_two_complexScalarUnitizedDeterminant_le c)
    (by simpa using hscale.pow 2)

theorem iteratedDeriv_three_normalizedXiC_zero :
    iteratedDeriv 3 (fun z => XiC z / XiC 0) 0 = 0 := by
  rw [show (fun z => XiC z / XiC 0) =
      fun z => (XiC 0)⁻¹ * XiC z by
        funext z
        rw [div_eq_inv_mul],
    iteratedDeriv_const_mul_field,
    iteratedDeriv_XiC_odd_zero (by decide), mul_zero]

/-- **Cofinal complex-scalar unitization third-jet no-go.** No complex scale sequence can make
the complete coefficient-faithful holomorphic SC reservoir converge compact-open to normalized
centered Xi. The exact third central jet is `12 c_m^3 e₃(q)`; divergence and boundedness of the
positive prime neutral jets force `‖c_m‖ ∑q_i → 0`, which collapses the exact quadratic jet and
contradicts normalized Xi curvature. -/
theorem not_tendstoLocallyUniformly_normalizedXiC_of_cofinalComplexScalarUnitization
    (c : ℕ → ℂ) :
    ¬ TendstoLocallyUniformly
      (preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant c)
      (fun z => XiC z / XiC 0) atTop := by
  intro hconv
  have hconvOn : TendstoLocallyUniformlyOn
      (preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant c)
      (fun z => XiC z / XiC 0) atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr hconv
  have hjetThree := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform
    isOpen_univ hconvOn
    (Filter.Eventually.of_forall fun m =>
      (differentiable_preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant
        c m).differentiableOn)
    3 (Set.mem_univ 0)
  rw [iteratedDeriv_three_normalizedXiC_zero] at hjetThree
  have hscale :=
    tendsto_norm_scale_mul_neutralJet_packetSum_zero_of_thirdJet_zero c hjetThree
  have hjetZero :=
    tendsto_iteratedDeriv_two_complexScalarUnitizedDeterminant_zero c hscale
  have hjetTarget := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform
    isOpen_univ hconvOn
    (Filter.Eventually.of_forall fun m =>
      (differentiable_preDivisorRiggedPrimeHolomorphicComplexScalarUnitizedDeterminant
        c m).differentiableOn)
    2 (Set.mem_univ 0)
  have hcurvatureZero :
      iteratedDeriv 2 (fun z => XiC z / XiC 0) 0 = 0 :=
    tendsto_nhds_unique hjetTarget hjetZero
  rw [iteratedDeriv_XiC_normalized_two] at hcurvatureZero
  have hre := congrArg Complex.re hcurvatureZero
  have hpos : 0 < thetaCuspNormalizedEvenMoment 1 := by
    rw [thetaCuspNormalizedEvenMoment]
    exact div_pos (thetaCuspRawEvenMoment_pos 1) thetaCuspRawEvenMoment_zero_pos
  norm_num at hre
  linarith

end
end RHTower
