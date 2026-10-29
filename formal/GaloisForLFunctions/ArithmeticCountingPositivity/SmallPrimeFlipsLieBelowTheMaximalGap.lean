import GaloisForLFunctions.ArithmeticCountingPositivity.HarmonicParitySpectralCoordinates
import GaloisForLFunctions.ArithmeticCountingPositivity.LargePrimeFlipsAttainTheMaximalGap
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheConductorTwoIsTheFirstExcitation

/-!
# Small-prime flips lie below the maximal gap

The ground and conductor-p eigenlines have explicit squared coordinates
against prime parity. Their exactly constrained plane supplies the upper
gap bound p log(p)/(p+3). For primes below eleven this is strictly below
the maximal margin, while the parity count still pays a positive gap.
Together with the large-prime inequality, this makes eleven the exact cutoff.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticIntersectionTheory
  GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.BezoutValuationIncidence

local notation "γ" => Real.eulerMascheroniConstant

private def parityMean (p : ℕ) : ℝ := ((p : ℝ) - 1) / ((p : ℝ) + 1)

private theorem parityMean_pos {p : ℕ} (hp : p.Prime) : 0 < parityMean p := by
  have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact div_pos (sub_pos.mpr h) (by positivity)

private theorem parityWindow_ground_limit {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => primeParityWindowCoordinateSq p 1 N δ)
      atTop (𝓝 (parityMean p ^ 2)) := by
  simpa [parityMean, moebiusReal, finiteFlip] using
    tendsto_primeParityWindowCoordinateSq hp (by norm_num : 0 < 1) hδ

private theorem parityWindow_prime_limit {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => primeParityWindowCoordinateSq p p N δ)
      atTop (𝓝 (4 * parityMean p ^ 2 / ((p : ℝ) - 1))) := by
  have hsum : (∑ d ∈ p.divisors, moebiusReal (p / d) * finiteFlip {p} d) = -2 := by
    rw [hp.divisors, sum_pair hp.ne_one.symm]
    norm_num [moebiusReal, finiteFlip, hp.factorization_self,
      ArithmeticFunction.moebius_apply_prime hp, Nat.div_self hp.pos]
  have hφ : (p.totient : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hp1 : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  have he : ((((p : ℝ) - 1) / ((p : ℝ) + 1) *
      ∑ d ∈ p.divisors, moebiusReal (p / d) * finiteFlip {p} d) /
        Real.sqrt (p.totient : ℝ)) ^ 2 =
      4 * parityMean p ^ 2 / ((p : ℝ) - 1) := by
    rw [hsum, hφ, div_pow, mul_pow, Real.sq_sqrt hp1.le,
      show (-2 : ℝ) ^ 2 = 4 by norm_num]
    change (parityMean p ^ 2 * 4) / ((p : ℝ) - 1) = _
    ring
  simpa only [he] using tendsto_primeParityWindowCoordinateSq hp hp.pos hδ

private theorem prime_adjunction_energy {p : ℕ} (hp : p.Prime) :
    ramanujanAdjunctionEnergy p = γ + (p : ℝ) * Real.log p / ((p : ℝ) - 1) := by
  have hp1 : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  have ht := tameDifferent_prime_pow hp (by norm_num : (1 : ℕ) ≠ 0)
  simp only [pow_one] at ht
  rw [ramanujanAdjunctionEnergy, ht]
  field_simp [hp1.ne']
  ring

private theorem parity_harmonic_sum {N : ℕ} (hN : 1 ≤ N) (p : ℕ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    (∑ k : PrimeHorizonIndex N, finiteFlip {p} k * u k / Real.sqrt k) =
      Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) * ⟪primeParityHorizonVector p N, u⟫ := by
  have hS : 0 < Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) :=
    Real.sqrt_pos.mpr (gaugeHarmonicSum_one_pos hN)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ k : PrimeHorizonIndex N, finiteFlip {p} k * u k / Real.sqrt k) =
    Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) *
      ∑ k : PrimeHorizonIndex N,
        u k * (finiteFlip {p} k / Real.sqrt k /
          Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have hk : (0 : ℝ) < (k : ℕ) := by exact_mod_cast (mem_Icc.mp k.property).1
  have hsk := (Real.sqrt_pos.mpr hk).ne'
  field_simp [hS.ne', hsk]

/-- The eigenvector plane meets the parity constraint with its exact two weights. -/
private theorem parity_eigenpair_necessary_bound {p N : ℕ} {g ε : ℝ}
    (hN : 1 ≤ N)
    (hbound : ∀ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 →
      atomicWeilForm N (fun n => finiteFlip {p} n * x n) ≤
        (Real.log N - γ - g + ε) * ∑ n ∈ Icc 1 N, x n ^ 2)
    {i j : PrimeHorizonIndex N} (hij : i ≠ j) :
    (γ + g - ε) *
        (⟪primeParityHorizonVector p N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2 +
          ⟪primeParityHorizonVector p N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis j⟫ ^ 2) ≤
      fullPrimeEnergyEigenvalue N i *
          ⟪primeParityHorizonVector p N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis j⟫ ^ 2 +
        fullPrimeEnergyEigenvalue N j *
          ⟪primeParityHorizonVector p N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2 := by
  let e := (fullPrimeMatrix_isHermitian N).eigenvectorBasis
  let a := ⟪primeParityHorizonVector p N, e i⟫
  let b := ⟪primeParityHorizonVector p N, e j⟫
  let f : PrimeHorizonIndex N → ℝ := b • ⇑(e i) + (-a) • ⇑(e j)
  let x : ℕ → ℝ := fun n => finiteFlip {p} n * horizonExtend f n
  have hx : ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 := by
    change (∑ n ∈ Icc 1 N, finiteFlip {p} n * horizonExtend f n / Real.sqrt n) = 0
    rw [sum_horizonExtend f (fun n t => finiteFlip {p} n * t / Real.sqrt n)]
    calc
      (∑ k : PrimeHorizonIndex N, finiteFlip {p} k * f k / Real.sqrt k) =
          b * (∑ k : PrimeHorizonIndex N, finiteFlip {p} k * e i k / Real.sqrt k) -
            a * (∑ k : PrimeHorizonIndex N, finiteFlip {p} k * e j k / Real.sqrt k) := by
        rw [mul_sum, mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun k _ => ?_
        simp only [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      _ = 0 := by
        rw [parity_harmonic_sum hN p (e i), parity_harmonic_sum hN p (e j)]
        change b * (Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) * a) -
          a * (Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) * b) = 0
        ring
  have hplane := quadratic_eigenvector_plane hij b (-a)
  have hmass : (∑ n ∈ Icc 1 N, x n ^ 2) = b ^ 2 + a ^ 2 := by
    calc
      _ = ∑ n ∈ Icc 1 N, horizonExtend f n ^ 2 := by
        refine sum_congr rfl fun n _ => ?_
        have hs : finiteFlip {p} n ^ 2 = 1 := by rw [sq, singleFlip_mul_self]
        dsimp only [x]
        rw [mul_pow, hs, one_mul]
      _ = ∑ k : PrimeHorizonIndex N, f k ^ 2 := sum_horizonExtend f (fun _ t => t ^ 2)
      _ = _ := by simpa only [f, e, neg_sq] using hplane.2
  have htwist : (fun n => finiteFlip {p} n * x n) = horizonExtend f := by
    funext n
    dsimp only [x]
    rw [← mul_assoc, singleFlip_mul_self, one_mul]
  have hform : atomicWeilForm N (fun n => finiteFlip {p} n * x n) =
      b ^ 2 * (fullPrimeMatrix_isHermitian N).eigenvalues i +
        a ^ 2 * (fullPrimeMatrix_isHermitian N).eigenvalues j := by
    rw [htwist, atomicWeilForm_horizonExtend]
    simpa only [f, e, neg_sq] using hplane.1
  have h := hbound x hx
  rw [hform, hmass] at h
  change (γ + g - ε) * (a ^ 2 + b ^ 2) ≤
    (Real.log N - (fullPrimeMatrix_isHermitian N).eigenvalues i) * b ^ 2 +
      (Real.log N - (fullPrimeMatrix_isHermitian N).eigenvalues j) * a ^ 2
  nlinarith only [h]

/-- The ground and conductor-p coordinates bound every gap of a prime flip. -/
theorem primeFlip_hyperplaneGap_le_prime_log_div {p : ℕ} (hp : p.Prime) {g : ℝ}
    (hgap : HasHyperplaneGap (finiteFlip {p}) g) :
    g ≤ (p : ℝ) * Real.log p / ((p : ℝ) + 3) := by
  let c := parityMean p
  let w := 4 * c ^ 2 / ((p : ℝ) - 1)
  let D := (p : ℝ) * Real.log p / ((p : ℝ) - 1)
  let B := (p : ℝ) * Real.log p / ((p : ℝ) + 3)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  have hp3 : 0 < (p : ℝ) + 3 := by positivity
  have hc : 0 < c := parityMean_pos hp
  have hD : 0 < D := div_pos
    (mul_pos hp0 (Real.log_pos (by exact_mod_cast hp.one_lt))) hp1
  have henergy : ramanujanAdjunctionEnergy p = γ + D := prime_adjunction_energy hp
  have hmass : 0 < c ^ 2 + w :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (by dsimp only [w]; positivity)
  have hbalance : D * c ^ 2 = B * (c ^ 2 + w) := by
    dsimp only [D, B, w]
    field_simp [hp1.ne', hp3.ne']
    ring
  change g ≤ B
  by_contra hnot
  have hBg : B < g := lt_of_not_ge hnot
  let ε := (g - B) / 4
  have hε : 0 < ε := by dsimp only [ε]; linarith only [hBg]
  obtain ⟨N₀, hN₀⟩ := hgap ε hε
  obtain ⟨δ₁, hδ₁, hcard₁, hnear₁, _⟩ :=
    exists_primeParity_eigenline_coordinates hp (by norm_num : 0 < 1)
  obtain ⟨δp, hδp, hcardp, hnearp, _⟩ :=
    exists_primeParity_eigenline_coordinates hp hp.pos
  have hlim₁ : Tendsto (fun N : ℕ => primeParityWindowCoordinateSq p 1 N δ₁)
      atTop (𝓝 (c ^ 2)) := parityWindow_ground_limit hp hδ₁
  have hlimp : Tendsto (fun N : ℕ => primeParityWindowCoordinateSq p p N δp)
      atTop (𝓝 w) := parityWindow_prime_limit hp hδp
  have hpos₁ : ∀ᶠ N : ℕ in atTop,
      0 < ‖harmonicRamanujanWindowProjection 1 N δ₁‖ ^ 2 :=
    (tendsto_harmonicRamanujanWindowProjection_norm_sq (by norm_num : 0 < 1) hδ₁).eventually
      (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hposp : ∀ᶠ N : ℕ in atTop,
      0 < ‖harmonicRamanujanWindowProjection p N δp‖ ^ 2 :=
    (tendsto_harmonicRamanujanWindowProjection_norm_sq hp.pos hδp).eventually
      (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  -- Distinct limiting energies force distinct actual indices before any plane is used.
  have hsep : ∀ᶠ N : ℕ in atTop,
      ∀ i ∈ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy 1) δ₁,
        ∀ j ∈ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy p) δp, i ≠ j := by
    have hD3 : 0 < D / 3 := by positivity
    filter_upwards [hnear₁ (D / 3) hD3, hnearp (D / 3) hD3] with N h₁ hp' i hi j hj hij
    subst j
    have h₁' := abs_lt.mp (h₁ i hi)
    have hp'' := abs_lt.mp (hp' i hj)
    rw [ramanujanAdjunctionEnergy_one] at h₁'
    rw [henergy] at hp''
    linarith only [h₁'.2, hp''.1, hD]
  have hineq : ∀ᶠ N : ℕ in atTop,
      (g - 2 * ε) * (primeParityWindowCoordinateSq p 1 N δ₁ +
        primeParityWindowCoordinateSq p p N δp) ≤ D * primeParityWindowCoordinateSq p 1 N δ₁ := by
    filter_upwards [hcard₁, hcardp, hnear₁ ε hε, hnearp ε hε,
      hpos₁, hposp, hsep, eventually_ge_atTop (max 1 N₀)]
      with N hc₁ hcp he₁ hep hn₁ hnp hsepN hN
    obtain ⟨i, hi⟩ := card_eq_one.mp hc₁
    obtain ⟨j, hj⟩ := card_eq_one.mp hcp
    have him : i ∈ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy 1) δ₁ := by
      rw [hi]
      exact mem_singleton_self i
    have hjm : j ∈ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy p) δp := by
      rw [hj]
      exact mem_singleton_self j
    have hpair := parity_eigenpair_necessary_bound
      ((le_max_left _ _).trans hN) (hN₀ N ((le_max_right _ _).trans hN)) (hsepN i him j hjm)
    have hei : fullPrimeEnergyEigenvalue N i ≤ γ + ε := by
      have h := (abs_lt.mp (he₁ i him)).2
      rw [ramanujanAdjunctionEnergy_one] at h
      linarith only [h]
    have hej : fullPrimeEnergyEigenvalue N j ≤ γ + D + ε := by
      have h := (abs_lt.mp (hep j hjm)).2
      rw [henergy] at h
      linarith only [h]
    have hpay₁ := mul_le_mul_of_nonneg_right hei
      (sq_nonneg ⟪primeParityHorizonVector p N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis j⟫)
    have hpayp := mul_le_mul_of_nonneg_right hej
      (sq_nonneg ⟪primeParityHorizonVector p N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫)
    have h : (g - 2 * ε) *
        (⟪primeParityHorizonVector p N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2 +
          ⟪primeParityHorizonVector p N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis j⟫ ^ 2) ≤
        D * ⟪primeParityHorizonVector p N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫ ^ 2 := by
      nlinarith only [hpair, hpay₁, hpayp]
    have hcoord₁ := primeParityWindowCoordinateSq_eq (p := p) (m := 1) i hi hn₁
    have hcoordp := primeParityWindowCoordinateSq_eq (p := p) (m := p) j hj hnp
    simpa only [← hcoord₁, ← hcoordp] using h
  have hlim := le_of_tendsto_of_tendsto ((hlim₁.add hlimp).const_mul (g - 2 * ε))
    (hlim₁.const_mul D) hineq
  rw [hbalance] at hlim
  have hle := le_of_mul_le_mul_right hlim hmass
  dsimp only [ε] at hle
  linarith only [hBg, hle]

private theorem small_prime_ceiling_lt_maximum {p : ℕ} (hp : p.Prime) (hpSmall : p < 11) :
    (p : ℝ) * Real.log p / ((p : ℝ) + 3) < 2 * Real.log 2 := by
  have hp7 : p ≤ 7 := by
    by_contra hn
    have hp8 : 8 ≤ p := by omega
    interval_cases p <;> norm_num at hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp7R : (p : ℝ) ≤ 7 := by exact_mod_cast hp7
  have hp3 : 0 < (p : ℝ) + 3 := by positivity
  have hratio : (p : ℝ) / ((p : ℝ) + 3) ≤ 7 / 10 := by
    rw [div_le_iff₀ hp3]
    linarith only [hp7R]
  have hlog : Real.log p ≤ Real.log 7 := Real.log_le_log hp0 hp7R
  have hlog7 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  calc
    (p : ℝ) * Real.log p / ((p : ℝ) + 3) =
        ((p : ℝ) / ((p : ℝ) + 3)) * Real.log p := by ring
    _ ≤ ((p : ℝ) / ((p : ℝ) + 3)) * Real.log 7 :=
      mul_le_mul_of_nonneg_left hlog (div_nonneg hp0.le hp3.le)
    _ ≤ (7 / 10) * Real.log 7 := mul_le_mul_of_nonneg_right hratio hlog7
    _ < 2 * Real.log 2 := by
      have h : Real.log ((7 : ℝ) ^ 7) < Real.log ((2 : ℝ) ^ 20) :=
        Real.log_lt_log (by positivity) (by norm_num)
      rw [Real.log_pow, Real.log_pow] at h
      norm_num at h
      linarith only [h]

/-- Small-prime parity retains a positive counted gap but cannot attain the maximum. -/
theorem smallPrimeFlip_has_positive_but_not_maximal_gap {p : ℕ} (hp : p.Prime)
    (hpSmall : p < 11) :
    HasHyperplaneGap (finiteFlip {p})
        (2 * Real.log 2 * (((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2) ∧
      ¬ HasHyperplaneGap (finiteFlip {p}) (2 * Real.log 2) := by
  refine ⟨primeFlip_hasHyperplaneGap hp, fun h => ?_⟩
  exact not_le_of_gt (small_prime_ceiling_lt_maximum hp hpSmall)
    (primeFlip_hyperplaneGap_le_prime_log_div hp h)

/-- A single-prime flip attains the maximal hyperplane gap exactly from eleven on. -/
theorem primeFlip_hasHyperplaneGap_two_mul_log_two_iff {p : ℕ} (hp : p.Prime) :
    HasHyperplaneGap (finiteFlip {p}) (2 * Real.log 2) ↔ 11 ≤ p := by
  constructor
  · intro hgap
    by_contra hpSmall
    exact (smallPrimeFlip_has_positive_but_not_maximal_gap hp (lt_of_not_ge hpSmall)).2 hgap
  · exact primeFlip_hasHyperplaneGap_two_mul_log_two hp

end GaloisForLFunctions.ArithmeticCountingPositivity
