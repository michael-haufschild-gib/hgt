import GaloisForLFunctions.BiScaleUncertainty.SignedLcmFractionalDefectAndCompleteFibreCollapse
import GaloisForLFunctions.BiScaleUncertainty.FoldFreeKernelGramAndFranelGcdCancellation
import GaloisForLFunctions.RHTower.Sieve.SelbergMoebiusLogDiagonal
import GaloisForLFunctions.RHTower.Sieve.SelbergDiagonalLowerAsymptotic

/-!
# Barban–Vehov Logarithmic Selberg Diagonal, Jordan `J₂` Franel Diagonalization, and the `ker P` Cauchy–Schwarz Pinch (`BarbanVehovLogarithmicDiagonalAndKerPCauchyPinch`)

This module builds the second foundational bridge in `BiScaleUncertainty` for overcoming the
naive harmonic-square divergence (`H_N² ~ log² N`) on the origin tail `m > N`:

1. **Unification of Selberg Multiples Coordinates & `ker P` Centering
   (`selbergMultiplesCoord_one_eq_finiteHarmonicSum`, `sum_moebius_mul_selbergMultiplesCoord`,
   `sq_div_sum_sqfreeTotientInv_Icc_two_le_selbergTotientDiagonalForm_of_harmonic_eq_zero`):**
   The `e = 1` Selberg multiples-coordinate `Y_{N,c}(1) = ∑_{d=1}^N c(d)/d` is literally the
   Nyman–Beurling harmonic shadow `finiteHarmonicSum N c`. Thus the `ker P` centering condition
   `∑_{d=1}^N c(d)/d = 0` is equivalent to `Y_{N,c}(1) = 0`. Möbius inversion
   `∑_{e=1}^N μ(e) Y_{N,c}(e) = c(1)` then restricts on `ker P` to the higher-frequency squarefree
   moduli `2 ≤ e ≤ N`, yielding the sharpened `ker P` Selberg Cauchy–Schwarz lower bound
   `c(1)² / (∑_{e=2}^N sqfreeTotientInv e) ≤ selbergTotientDiagonalForm N c`.

2. **Exact Jordan `J₂` Diagonalization of the Periodic Franel GCD-Square Form & Rank-One Harmonic
   Shadow Cancellation (`franelGcdQuadraticForm_eq_jordanTotient2_diagonal`,
   `franelGcdQuadraticForm_sub_selbergTotientDiagonalForm_eq_Icc_two`):**
   Defining Jordan's second totient function `jordanTotient2 e = ∑_{d ∣ e} μ(e/d) d²`, the periodic
   Franel sawtooth Gram quadratic form `Q_Franel(N, c) = ∑_{d₁, d₂ ≤ N} c(d₁) c(d₂) gcd(d₁, d₂)² / (d₁ d₂)`
   diagonalizes in the **exact same** Selberg coordinates `Y_{N,c}(e)`:
   `Q_Franel(N, c) = ∑_{e=1}^N J₂(e) Y_{N,c}(e)²`.
   Because `J₂(1) = φ(1) = 1`, the rank-one harmonic mode `Y_{N,c}(1)²` cancels identically in the
   discrepancy `Q_Franel(N, c) - Q_Sel(N, c) = ∑_{e=2}^N (J₂(e) - φ(e)) Y_{N,c}(e)²` for **all** `c`.

3. **Barban–Vehov Logarithmic Diagonal Pinch & Prime-Power Head + Tail Mean-Square Law
   (`selbergTotientDiagonalForm_barbanVehovWeight_pinch`,
   `selbergTotientDiagonalForm_normalizedBarbanVehovWeight_pinch`,
   `barbanVehov_prefixMeanSquare_eq_primePowers_add_tail_selberg`):**
   Connecting `RHTower.Sieve.barbanVehovWeight X` to `BiScaleUncertainty`, we prove that for
   `1 ≤ X ≤ N`, `sievedDivisorSum N (barbanVehovWeight X) k` equals `log X` at `k = 1` and the
   exact von Mangoldt weight `Λ(k)` on `2 ≤ k ≤ X`, while its Selberg totient diagonal satisfies
   the two-sided logarithmic pinch
   `(log X)² / ∑_{e=1}^X sqfreeTotientInv e ≤ Q_Sel(N, b_X) ≤ 4 A² (1 + log X)`,
   so the normalized weight `w_X(d) = b_X(d) / log X` (`w_X(1) = 1`) achieves `O(1 / log X)` tail
   density.
-/

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

open Finset ArithmeticFunction RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

/-! ## §1. Selberg Multiples Coordinates, Möbius Inversion, and `ker P` Centering -/

/-- `selbergMultiplesCoord` coincides definitionally with `RHTower.Sieve.selbergMultiplesInner`. -/
theorem selbergMultiplesCoord_eq_selbergMultiplesInner (N : ℕ) (c : ℕ → ℝ) (e : ℕ) :
    selbergMultiplesCoord N c e = selbergMultiplesInner N c e :=
  rfl

/-- **The `e = 1` Selberg Coordinate is the Harmonic Pole Sum (`finiteHarmonicSum`):**
For every `N : ℕ` and `c : ℕ → ℝ`, `selbergMultiplesCoord N c 1 = ∑_{d=1}^N c(d) / d`. -/
theorem selbergMultiplesCoord_one_eq_finiteHarmonicSum (N : ℕ) (c : ℕ → ℝ) :
    selbergMultiplesCoord N c 1 = finiteHarmonicSum N c := by
  unfold selbergMultiplesCoord finiteHarmonicSum
  have hfilter : (Finset.Icc 1 N).filter (fun d => (1 : ℕ) ∣ d) = Finset.Icc 1 N :=
    Finset.filter_true_of_mem fun d _ => one_dvd d
  rw [hfilter]

/-- **Möbius Inversion of the Selberg Multiples Coordinates:**
For `N ≥ 1`, `∑_{e=1}^N μ(e) Y_{N,c}(e) = c(1)`. -/
theorem sum_moebius_mul_selbergMultiplesCoord {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    (∑ e ∈ Finset.Icc 1 N, (μ e : ℝ) * selbergMultiplesCoord N c e) = c 1 :=
  sum_moebius_mul_selbergMultiplesInner hN c

/-- **Reduced Möbius Inversion on `ker P` (`finiteHarmonicSum N c = 0`):**
When `∑_{d=1}^N c(d)/d = 0`, the `e = 1` Selberg coordinate vanishes and the normalization
constraint `c(1)` is carried purely by the higher-frequency moduli `2 ≤ e ≤ N`. -/
theorem sum_moebius_Icc_two_mul_selbergMultiplesCoord_of_harmonic_eq_zero
    {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (hker : finiteHarmonicSum N c = 0) :
    (∑ e ∈ Finset.Icc 2 N, (μ e : ℝ) * selbergMultiplesCoord N c e) = c 1 := by
  have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext e
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have htot := sum_moebius_mul_selbergMultiplesCoord hN c
  rw [hIcc, Finset.sum_insert (by simp), selbergMultiplesCoord_one_eq_finiteHarmonicSum,
    hker, mul_zero, zero_add] at htot
  exact htot

/-- **Unconditional Selberg Cauchy–Schwarz Lower Bound on `selbergTotientDiagonalForm`:**
For any `N ≥ 1` and `c : ℕ → ℝ`,
`c(1)² / (∑_{e=1}^N sqfreeTotientInv e) ≤ selbergTotientDiagonalForm N c`. -/
theorem sq_div_sum_sqfreeTotientInv_le_selbergTotientDiagonalForm
    {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    (c 1) ^ (2 : ℕ) / (∑ e ∈ Finset.Icc 1 N, sqfreeTotientInv e) ≤
      selbergTotientDiagonalForm N c :=
  sq_div_sum_sqfreeTotientInv_le_totientDiagonal hN c

/-- **Sharpened `ker P` Selberg Cauchy–Schwarz Lower Bound:**
When `finiteHarmonicSum N c = 0` (`c ∈ ker P`), the `e = 1` term vanishes from the Selberg diagonal
and Cauchy–Schwarz over `e ∈ [2, N]` gives the strictly tighter lower bound with denominator
`∑_{e=2}^N sqfreeTotientInv e`. -/
theorem sq_div_sum_sqfreeTotientInv_Icc_two_le_selbergTotientDiagonalForm_of_harmonic_eq_zero
    {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (hker : finiteHarmonicSum N c = 0) :
    (c 1) ^ (2 : ℕ) / (∑ e ∈ Finset.Icc 2 N, sqfreeTotientInv e) ≤
      selbergTotientDiagonalForm N c := by
  let S := (Finset.Icc 2 N).filter Squarefree
  have hphi : ∀ e ∈ S, 0 < (1 / (Nat.totient e : ℝ)) := by
    intro e he
    have he2 : 2 ≤ e := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
    have htot : 0 < Nat.totient e := Nat.totient_pos.mpr (by omega)
    positivity
  have hconstraint : (∑ e ∈ S, (μ e : ℝ) * selbergMultiplesCoord N c e) = c 1 := by
    calc (∑ e ∈ S, (μ e : ℝ) * selbergMultiplesCoord N c e)
        = ∑ e ∈ Finset.Icc 2 N, (μ e : ℝ) * selbergMultiplesCoord N c e := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro e he heS
          have hnsq : ¬ Squarefree e := fun hsq => heS (Finset.mem_filter.mpr ⟨he, hsq⟩)
          rw [show (μ e : ℝ) = 0 by exact_mod_cast moebius_eq_zero_of_not_squarefree hnsq]
          simp
      _ = c 1 := sum_moebius_Icc_two_mul_selbergMultiplesCoord_of_harmonic_eq_zero hN c hker
  have hcs := Finset.sq_sum_div_le_sum_sq_div S
    (fun e => (μ e : ℝ) * selbergMultiplesCoord N c e) hphi
  rw [hconstraint] at hcs
  have hdenom : (∑ e ∈ S, 1 / (Nat.totient e : ℝ)) =
      ∑ e ∈ Finset.Icc 2 N, sqfreeTotientInv e := by
    dsimp [S]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [sqfreeTotientInv_apply]
  rw [hdenom] at hcs
  have hrhs : (∑ e ∈ S, ((μ e : ℝ) * selbergMultiplesCoord N c e) ^ (2 : ℕ) /
      (1 / (Nat.totient e : ℝ))) =
      ∑ e ∈ S, (Nat.totient e : ℝ) * (selbergMultiplesCoord N c e) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun e he => ?_
    have hsq : Squarefree e := (Finset.mem_filter.mp he).2
    have he2 : 2 ≤ e := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
    have htot : (Nat.totient e : ℝ) ≠ 0 :=
      by exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
    have hmu : (μ e : ℝ) ^ (2 : ℕ) = 1 := by
      have h := ArithmeticFunction.moebius_sq (n := e)
      rw [if_pos hsq] at h
      exact_mod_cast h
    rw [mul_pow, hmu, one_mul]
    field_simp
  rw [hrhs] at hcs
  have hsub : S ⊆ Finset.Icc 1 N := by
    intro e he
    obtain ⟨he2, heN⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp he).1
    exact Finset.mem_Icc.mpr ⟨by omega, heN⟩
  exact hcs.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity)

/-! ## §2. Jordan's Second Totient `J₂` and Shared-Coordinate Diagonalization of the Franel GCD Form -/

/-- **Jordan's Second Totient Function `J₂(e) = ∑_{d ∣ e} μ(d) (e/d)²`:**
The Dirichlet convolution `μ * id²` that diagonalizes the Franel GCD-square kernel `gcd(d₁, d₂)²`. -/
def jordanTotient2 (e : ℕ) : ℝ :=
  ∑ x ∈ e.divisorsAntidiagonal, ((μ x.1 : ℤ) : ℝ) * (x.2 : ℝ) ^ (2 : ℕ)

/-- At `e = 1`, `jordanTotient2 1 = 1 = φ(1)`. -/
@[simp]
theorem jordanTotient2_one : jordanTotient2 1 = 1 := by
  unfold jordanTotient2
  simp

/-- **Fundamental Divisor-Sum Identity for `jordanTotient2` (`∑_{e ∣ n} J₂(e) = n²`):**
For every `n ≥ 1`, summing `jordanTotient2 e` over the divisors of `n` recovers `n²`. -/
theorem sum_divisors_jordanTotient2 {n : ℕ} (hn : 0 < n) :
    ∑ e ∈ n.divisors, jordanTotient2 e = (n : ℝ) ^ (2 : ℕ) :=
  (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := jordanTotient2) (g := fun m : ℕ => (m : ℝ) ^ (2 : ℕ))).mpr
      (fun _ _ => rfl) n hn

/-- The normalized Franel GCD-square quadratic form on `[1, N]`:
`Q_Franel(N, c) = ∑_{d₁, d₂ ∈ [1, N]} c(d₁) c(d₂) gcd(d₁, d₂)² / (d₁ d₂)`. -/
def franelGcdQuadraticForm (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
    c p.1 * c p.2 * (((Nat.gcd p.1 p.2 : ℕ) : ℝ) ^ (2 : ℕ) / ((p.1 : ℝ) * (p.2 : ℝ)))

/-- Pairwise expansion of the Franel GCD-square term via `jordanTotient2`. -/
theorem gcd_sq_div_eq_sum_jordanTotient2 (c : ℕ → ℝ) {m n : ℕ} (hm : 0 < m) (_hn : 0 < n) :
    c m * c n * (((Nat.gcd m n : ℕ) : ℝ) ^ (2 : ℕ) / ((m : ℝ) * (n : ℝ))) =
      ∑ e ∈ (Nat.gcd m n).divisors, jordanTotient2 e * ((c m / (m : ℝ)) * (c n / (n : ℝ))) := by
  have hgcd : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left _ hm
  rw [← Finset.sum_mul, sum_divisors_jordanTotient2 hgcd]
  ring

/-- **Exact Jordan `J₂` Diagonalization of the Franel GCD-Square Form
(`franelGcdQuadraticForm_eq_jordanTotient2_diagonal`):**
For every `N : ℕ` and `c : ℕ → ℝ`, `franelGcdQuadraticForm N c` is diagonal in the **exact same**
Selberg multiples-coordinates `selbergMultiplesCoord N c e` as `selbergTotientDiagonalForm N c`:
`franelGcdQuadraticForm N c = ∑_{e=1}^N J₂(e) Y_{N,c}(e)²`. -/
theorem franelGcdQuadraticForm_eq_jordanTotient2_diagonal (N : ℕ) (c : ℕ → ℝ) :
    franelGcdQuadraticForm N c =
      ∑ e ∈ Finset.Icc 1 N, jordanTotient2 e * (selbergMultiplesCoord N c e) ^ (2 : ℕ) := by
  classical
  unfold franelGcdQuadraticForm selbergMultiplesCoord
  have hS : ∀ m ∈ Finset.Icc 1 N, 0 < m := fun m hm => (Finset.mem_Icc.mp hm).1
  have hexp : ∀ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      c p.1 * c p.2 * (((Nat.gcd p.1 p.2 : ℕ) : ℝ) ^ (2 : ℕ) / ((p.1 : ℝ) * (p.2 : ℝ))) =
        ∑ e ∈ (Nat.gcd p.1 p.2).divisors,
          jordanTotient2 e * ((c p.1 / (p.1 : ℝ)) * (c p.2 / (p.2 : ℝ))) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact gcd_sq_div_eq_sum_jordanTotient2 c (hS _ hp1) (hS _ hp2)
  rw [Finset.sum_congr rfl hexp]
  have hmem : ∀ (p : ℕ × ℕ) (e : ℕ),
      p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ∧ e ∈ (Nat.gcd p.1 p.2).divisors ↔
        p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun q => e ∣ q.1 ∧ e ∣ q.2) ∧
          e ∈ (Finset.Icc 1 N).biUnion Nat.divisors := by
    intro p e
    constructor
    · rintro ⟨hp, he⟩
      obtain ⟨hp1, _⟩ := Finset.mem_product.mp hp
      have hgcd : e ∣ Nat.gcd p.1 p.2 := Nat.dvd_of_mem_divisors he
      have hd1 : e ∣ p.1 := dvd_trans hgcd (Nat.gcd_dvd_left _ _)
      have hd2 : e ∣ p.2 := dvd_trans hgcd (Nat.gcd_dvd_right _ _)
      refine ⟨Finset.mem_filter.mpr ⟨hp, hd1, hd2⟩, Finset.mem_biUnion.mpr ⟨p.1, hp1, ?_⟩⟩
      exact Nat.mem_divisors.mpr ⟨hd1, (hS _ hp1).ne'⟩
    · rintro ⟨hpf, -⟩
      obtain ⟨hp, hd1, hd2⟩ := Finset.mem_filter.mp hpf
      obtain ⟨hp1, _⟩ := Finset.mem_product.mp hp
      refine ⟨hp, Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hd1 hd2, ?_⟩⟩
      exact (Nat.gcd_pos_of_pos_left _ (hS _ hp1)).ne'
  rw [Finset.sum_comm' hmem, biUnion_divisors_Icc_eq_Icc]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hfilter : ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun q => e ∣ q.1 ∧ e ∣ q.2) =
      ((Finset.Icc 1 N).filter (fun m => e ∣ m)) ×ˢ ((Finset.Icc 1 N).filter (fun m => e ∣ m)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hfilter, ← Finset.mul_sum, sq, Finset.sum_mul_sum, Finset.sum_product]

/-- **Universal Cancellation of the `e = 1` Harmonic Shadow Between `Q_Franel` and `Q_Sel`:**
Because `J₂(1) = φ(1) = 1`, for **every** `N ≥ 1` and **every** `c : ℕ → ℝ` (even off `ker P`!),
the `e = 1` harmonic-pole mode `Y_{N,c}(1)² = (∑_{d=1}^N c(d)/d)²` cancels out of the difference
`franelGcdQuadraticForm N c - selbergTotientDiagonalForm N c`:
`Q_Franel(N, c) - Q_Sel(N, c) = ∑_{e=2}^N (J₂(e) - φ(e)) Y_{N,c}(e)²`. -/
theorem franelGcdQuadraticForm_sub_selbergTotientDiagonalForm_eq_Icc_two
    {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    franelGcdQuadraticForm N c - selbergTotientDiagonalForm N c =
      ∑ e ∈ Finset.Icc 2 N,
        (jordanTotient2 e - (Nat.totient e : ℝ)) * (selbergMultiplesCoord N c e) ^ (2 : ℕ) := by
  rw [franelGcdQuadraticForm_eq_jordanTotient2_diagonal, selbergTotientDiagonalForm,
    ← Finset.sum_sub_distrib]
  have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext e
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.sum_insert (by simp)]
  simp only [jordanTotient2_one, Nat.totient_one, Nat.cast_one, one_mul, sub_self, zero_add]
  refine Finset.sum_congr rfl fun e _ => by ring

/-! ## §3. Barban–Vehov Sieve Weight Bridge & Logarithmic Selberg Diagonal Pinch -/

/-- **Exact Agreement of `sievedDivisorSum` for `barbanVehovWeight X` with `barbanVehovCoeff`:**
Whenever `X ≤ N`, `barbanVehovWeight X` is supported on `[1, X] ⊆ [1, N]`, so for **every** `k ≥ 1`
(including all origin-tail integers `k > N`), `sievedDivisorSum N (barbanVehovWeight X) k` equals
`barbanVehovCoeff X k`. -/
theorem sievedDivisorSum_barbanVehovWeight_eq_barbanVehovCoeff
    {X N k : ℕ} (hXN : X ≤ N) :
    sievedDivisorSum N (barbanVehovWeight X) k = barbanVehovCoeff X k := by
  unfold sievedDivisorSum barbanVehovCoeff truncatedSieveWeight
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  by_cases hdN : d ≤ N
  · rw [if_pos (Finset.mem_Icc.mpr ⟨hd1, hdN⟩)]
  · rw [if_neg (fun hmem => hdN (Finset.mem_Icc.mp hmem).2)]
    unfold barbanVehovWeight
    rw [if_neg (by omega)]

/-- At `k = 1`, `sievedDivisorSum N (barbanVehovWeight X) 1 = log X` for `1 ≤ X ≤ N`. -/
theorem sievedDivisorSum_barbanVehovWeight_one {X N : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) :
    sievedDivisorSum N (barbanVehovWeight X) 1 = Real.log (X : ℝ) := by
  rw [sievedDivisorSum_barbanVehovWeight_eq_barbanVehovCoeff hXN, barbanVehovCoeff_one hX]

/-- **Exact Recovery of `vonMangoldt` on `[2, X]` by `sievedDivisorSum N (barbanVehovWeight X)`:**
For `1 < k ≤ X ≤ N`, `sievedDivisorSum N (barbanVehovWeight X) k = Λ(k)`. -/
theorem sievedDivisorSum_barbanVehovWeight_eq_vonMangoldt
    {X N k : ℕ} (hk : 1 < k) (hkX : k ≤ X) (hXN : X ≤ N) :
    sievedDivisorSum N (barbanVehovWeight X) k = vonMangoldt k := by
  rw [sievedDivisorSum_barbanVehovWeight_eq_barbanVehovCoeff hXN,
    barbanVehovCoeff_eq_vonMangoldt hk hkX]

/-- For `X ≤ N`, `selbergTotientDiagonalForm N (barbanVehovWeight X)` equals the `[1, X]` diagonal
`barbanVehovSelbergDiagonal X`. -/
theorem selbergTotientDiagonalForm_barbanVehovWeight_eq_barbanVehovSelbergDiagonal
    {X N : ℕ} (hXN : X ≤ N) :
    selbergTotientDiagonalForm N (barbanVehovWeight X) = barbanVehovSelbergDiagonal X := by
  unfold selbergTotientDiagonalForm barbanVehovSelbergDiagonal
    selbergMultiplesCoord selbergMultiplesInner
  have hsub : Finset.Icc 1 X ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_right hXN
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
    congr 1
    have hfsub : (Finset.Icc 1 X).filter (fun d => e ∣ d) ⊆
        (Finset.Icc 1 N).filter (fun d => e ∣ d) :=
      Finset.filter_subset_filter _ hsub
    rw [← Finset.sum_subset hfsub]
    intro d hd hnot
    obtain ⟨hdIcc, hde⟩ := Finset.mem_filter.mp hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
    have hdX : ¬ d ≤ X := fun hle => hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, hle⟩, hde⟩)
    unfold barbanVehovWeight
    rw [if_neg hdX, zero_div]
  · intro e he hnot
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hXe : X < e := by
      by_contra hle
      exact hnot (Finset.mem_Icc.mpr ⟨he1, by omega⟩)
    rw [barbanVehov_inner_eq_zero he1 hXN hXe]
    ring

/-- **Two-Sided Logarithmic Selberg Diagonal Pinch for `barbanVehovWeight X`:**
For every `1 ≤ X ≤ N`, the Selberg totient diagonal of `barbanVehovWeight X` is pinched between
`(log X)² / ∑_{e=1}^X sqfreeTotientInv e` and `4 A² (1 + log X)`:
`(log X)² / ∑_{e=1}^X sqfreeTotientInv e ≤ Q_Sel(N, b_X) ≤ 4 A² (1 + log X)`. -/
theorem selbergTotientDiagonalForm_barbanVehovWeight_pinch
    {X N : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) :
    (Real.log (X : ℝ)) ^ (2 : ℕ) / (∑ e ∈ Finset.Icc 1 X, sqfreeTotientInv e) ≤
        selbergTotientDiagonalForm N (barbanVehovWeight X) ∧
      selbergTotientDiagonalForm N (barbanVehovWeight X) ≤
        4 * coprimeLogMoebiusConst ^ (2 : ℕ) * (1 + Real.log (X : ℝ)) := by
  refine ⟨?_, barbanVehov_totient_diagonal_le hXN⟩
  rw [selbergTotientDiagonalForm_barbanVehovWeight_eq_barbanVehovSelbergDiagonal hXN]
  exact sq_log_div_sum_sqfreeTotientInv_le_barbanVehovSelbergDiagonal hX

/-- The normalized Barban–Vehov sieve weight `w_X(d) = (μ(d) log(X/d) / log X) 1_{d ≤ X}`, which
satisfies `w_X(1) = 1` for `X ≥ 2`. -/
def normalizedBarbanVehovWeight (X d : ℕ) : ℝ :=
  barbanVehovWeight X d / Real.log (X : ℝ)

/-- For `X ≥ 2`, `normalizedBarbanVehovWeight X` satisfies the Selberg normalization `w_X(1) = 1`. -/
theorem normalizedBarbanVehovWeight_one {X : ℕ} (hX : 2 ≤ X) :
    normalizedBarbanVehovWeight X 1 = 1 := by
  unfold normalizedBarbanVehovWeight
  rw [barbanVehovWeight_one (by omega)]
  have hlog : Real.log (X : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < X by omega))).ne'
  exact div_self hlog

/-- Scaling law for `selbergTotientDiagonalForm` under multiplication of weights by a constant. -/
theorem selbergTotientDiagonalForm_const_mul (N : ℕ) (α : ℝ) (c : ℕ → ℝ) :
    selbergTotientDiagonalForm N (fun d => α * c d) =
      α ^ (2 : ℕ) * selbergTotientDiagonalForm N c := by
  unfold selbergTotientDiagonalForm selbergMultiplesCoord
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hinner : (∑ d ∈ (Finset.Icc 1 N).filter (fun d => e ∣ d), α * c d / (d : ℝ)) =
      α * ∑ d ∈ (Finset.Icc 1 N).filter (fun d => e ∣ d), c d / (d : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hinner]
  ring

/-- **Two-Sided `O(1 / log X)` Pinch for `normalizedBarbanVehovWeight X`:**
For every `2 ≤ X ≤ N`, the normalized Barban–Vehov sieve weight (`w_X(1) = 1`) achieves the
Selberg `1 / log X` tail-density scale from both below and above:
`1 / ∑_{e=1}^X sqfreeTotientInv e ≤ Q_Sel(N, w_X) ≤ 4 A² (1 + log X) / (log X)²`. -/
theorem selbergTotientDiagonalForm_normalizedBarbanVehovWeight_pinch
    {X N : ℕ} (hX : 2 ≤ X) (hXN : X ≤ N) :
    1 / (∑ e ∈ Finset.Icc 1 X, sqfreeTotientInv e) ≤
        selbergTotientDiagonalForm N (normalizedBarbanVehovWeight X) ∧
      selbergTotientDiagonalForm N (normalizedBarbanVehovWeight X) ≤
        4 * coprimeLogMoebiusConst ^ (2 : ℕ) * (1 + Real.log (X : ℝ)) /
          (Real.log (X : ℝ)) ^ (2 : ℕ) := by
  have hlogpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogsq : 0 < (Real.log (X : ℝ)) ^ (2 : ℕ) := sq_pos_of_pos hlogpos
  have hrew : normalizedBarbanVehovWeight X =
      fun d => (Real.log (X : ℝ))⁻¹ * barbanVehovWeight X d := by
    funext d
    unfold normalizedBarbanVehovWeight
    ring
  rw [hrew, selbergTotientDiagonalForm_const_mul]
  obtain ⟨hlow, hhigh⟩ := selbergTotientDiagonalForm_barbanVehovWeight_pinch (by omega) hXN
  constructor
  · have h1 : (Real.log (X : ℝ))⁻¹ ^ (2 : ℕ) *
        ((Real.log (X : ℝ)) ^ (2 : ℕ) / ∑ e ∈ Finset.Icc 1 X, sqfreeTotientInv e) =
        1 / ∑ e ∈ Finset.Icc 1 X, sqfreeTotientInv e := by
      field_simp
    rw [← h1]
    exact mul_le_mul_of_nonneg_left hlow (by positivity)
  · calc (Real.log (X : ℝ))⁻¹ ^ (2 : ℕ) * selbergTotientDiagonalForm N (barbanVehovWeight X)
        ≤ (Real.log (X : ℝ))⁻¹ ^ (2 : ℕ) *
            (4 * coprimeLogMoebiusConst ^ (2 : ℕ) * (1 + Real.log (X : ℝ))) :=
          mul_le_mul_of_nonneg_left hhigh (by positivity)
      _ = 4 * coprimeLogMoebiusConst ^ (2 : ℕ) * (1 + Real.log (X : ℝ)) /
            (Real.log (X : ℝ)) ^ (2 : ℕ) := by
          field_simp

/-- **Exact Prime-Power Head + Tail Selberg Decomposition of the Barban–Vehov Mean Square:**
For `1 ≤ X ≤ N` and `X ≤ M`, the prefix mean square of `barbanVehovCoeff X` over `1 ≤ k ≤ M` splits
into `(log X)² + ∑_{k=2}^X Λ(k)² + ∑_{k=X+1}^M b_X(k)²` and equals
`M · selbergTotientDiagonalForm N (barbanVehovWeight X) - signedLcmFractDefect N M (barbanVehovWeight X)`. -/
theorem barbanVehov_prefixMeanSquare_eq_primePowers_add_tail_selberg
    {X N M : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) (hXM : X ≤ M) :
    (Real.log (X : ℝ)) ^ (2 : ℕ) +
      (∑ k ∈ Finset.Icc 2 X, (vonMangoldt k) ^ (2 : ℕ)) +
      (∑ k ∈ Finset.Icc (X + 1) M, (barbanVehovCoeff X k) ^ (2 : ℕ)) =
      (M : ℝ) * selbergTotientDiagonalForm N (barbanVehovWeight X) -
        signedLcmFractDefect N M (barbanVehovWeight X) := by
  rw [← sievedDivisorPrefixMeanSquare_eq_selberg_sub_signedLcmFractDefect N M (barbanVehovWeight X)]
  have hunion : Finset.Icc 1 M = Finset.Icc 1 X ∪ Finset.Icc (X + 1) M := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 X) (Finset.Icc (X + 1) M) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  rw [hunion, Finset.sum_union hdisj]
  have hhead : Finset.Icc 1 X = insert 1 (Finset.Icc 2 X) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hhead, Finset.sum_insert (by simp), sievedDivisorSum_barbanVehovWeight_one hX hXN]
  have h2 : (∑ k ∈ Finset.Icc 2 X, sievedDivisorSum N (barbanVehovWeight X) k ^ (2 : ℕ)) =
      ∑ k ∈ Finset.Icc 2 X, (vonMangoldt k) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk2, hkX⟩ := Finset.mem_Icc.mp hk
    rw [sievedDivisorSum_barbanVehovWeight_eq_vonMangoldt (by omega) hkX hXN]
  have h3 : (∑ k ∈ Finset.Icc (X + 1) M, sievedDivisorSum N (barbanVehovWeight X) k ^ (2 : ℕ)) =
      ∑ k ∈ Finset.Icc (X + 1) M, (barbanVehovCoeff X k) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sievedDivisorSum_barbanVehovWeight_eq_barbanVehovCoeff hXN]
  rw [h2, h3]

end GaloisForLFunctions.BiScaleUncertainty
