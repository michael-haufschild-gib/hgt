import GaloisForLFunctions.RHTower.Sieve.RamarePhaseBilinear
import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare
import GaloisForLFunctions.RHTower.Sieve.LogPolyProductScale

/-!
# Multiplying a Gallagher polynomial by a prime phase

`μ(p)p^{2πiw}·∑_{m ∈ S} c_m m^{2πiw} = ∑_{n ∈ pS} μ(p)c_{n/p} n^{2πiw}` — multiplying by the phase
of a prime shifts the index set by that prime.  So every summand of the Ramaré bilinear form is
itself a Gallagher polynomial, over the shifted index set, and the mean value theorem applies to
the whole sum at once rather than one prime at a time.

That distinction is what the parameter accounting of the ladder needs: the error of the ladder is a
single Dirichlet polynomial whose `ℓ²` mass carries one power of the number of designated primes,
not two.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The coefficients of a Gallagher polynomial after multiplication by a prime phase. -/
noncomputable def primeShiftCoeff (p : ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  if p ∣ n then ((ArithmeticFunction.moebius p : ℤ) : ℂ) * c (n / p) else 0

/-- **Multiplying by a prime phase shifts the index set.** -/
theorem moebiusPhase_mul_logPoly {p : ℕ} (hp : 0 < p) (c : ℕ → ℂ) {S : Finset ℕ}
    (hS : ∀ m ∈ S, 0 < m) (w : ℝ) :
    moebiusPhase w p * logPoly c S w
      = logPoly (primeShiftCoeff p c) (S.image (fun m => p * m)) w := by
  classical
  have hinj : Set.InjOn (fun m => p * m) (S : Set ℕ) := by
    intro m₁ _ m₂ _ hEq
    have hEq' : p * m₁ = p * m₂ := hEq
    exact Nat.eq_of_mul_eq_mul_left hp hEq'
  rw [moebiusPhase, logPoly, logPoly, Finset.sum_image hinj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : 0 < m := hS m hm
  have hcoeff : primeShiftCoeff p c (p * m) = ((ArithmeticFunction.moebius p : ℤ) : ℂ) * c m := by
    rw [primeShiftCoeff, if_pos ⟨m, rfl⟩, Nat.mul_div_cancel_left m hp]
  rw [hcoeff]
  show ((ArithmeticFunction.moebius p : ℤ) : ℂ) * unitLogPhase w p
      * (c m * unitLogPhase w m)
    = ((ArithmeticFunction.moebius p : ℤ) : ℂ) * c m * unitLogPhase w (p * m)
  rw [unitLogPhase_mul w hp.ne' hm0.ne']
  ring

theorem primeShiftCoeff_eq_zero {p : ℕ} (c : ℕ → ℂ) {n : ℕ} (h : ¬ p ∣ n) :
    primeShiftCoeff p c n = 0 := by
  rw [primeShiftCoeff, if_neg h]

theorem norm_primeShiftCoeff_le {p : ℕ} {c : ℕ → ℂ} (hc : ∀ m, ‖c m‖ ≤ 1) (n : ℕ) :
    ‖primeShiftCoeff p c n‖ ≤ 1 := by
  rw [primeShiftCoeff]
  by_cases hd : p ∣ n
  · rw [if_pos hd, norm_mul]
    have hnum : ‖((ArithmeticFunction.moebius p : ℤ) : ℂ)‖ ≤ 1 := by
      have hnorm : ‖((ArithmeticFunction.moebius p : ℤ) : ℂ)‖
          = |((ArithmeticFunction.moebius p : ℤ) : ℝ)| := by
        rw [show (((ArithmeticFunction.moebius p : ℤ)) : ℂ)
            = ((((ArithmeticFunction.moebius p : ℤ) : ℝ)) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
      rw [hnorm]
      exact abs_moebius_real_le_one p
    have h1 := hc (n / p)
    nlinarith [hnum, h1, norm_nonneg (((ArithmeticFunction.moebius p : ℤ) : ℂ)),
      norm_nonneg (c (n / p))]
  · rw [if_neg hd, norm_zero]
    norm_num

/-! ## A sum of Gallagher polynomials is one Gallagher polynomial -/

open MeasureTheory

theorem sum_logPoly_eq {ι : Type*} (I : Finset ι) (b : ι → ℕ → ℂ) (T : Finset ℕ) (w : ℝ) :
    ∑ i ∈ I, logPoly (b i) T w = logPoly (fun n => ∑ i ∈ I, b i n) T w := by
  simp only [logPoly]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_mul]

/-- **The coefficient mass of a sum of unit-coefficient polynomials.**  Each index is hit at most
`K` times, so the `ℓ²` mass is at most `K` times the total number of index-set elements — one power
of the number of summands, not two. -/
theorem sum_normSq_overlap_coeff_le {ι : Type*} [DecidableEq ι] (I : Finset ι) (a : ι → ℕ → ℂ)
    (S : ι → Finset ℕ) (N : ℕ) {K : ℝ}
    (ha : ∀ i n, ‖a i n‖ ≤ 1) (hK0 : 0 ≤ K)
    (hK : ∀ n ∈ Finset.Icc 1 N, ((I.filter (fun i => n ∈ S i)).card : ℝ) ≤ K) :
    ∑ n ∈ Finset.Icc 1 N, ‖∑ i ∈ I, (if n ∈ S i then a i n else 0)‖ ^ 2
      ≤ K * ∑ i ∈ I, ((S i ∩ Finset.Icc 1 N).card : ℝ) := by
  classical
  have hcount : ∀ n : ℕ, ‖∑ i ∈ I, (if n ∈ S i then a i n else 0)‖
      ≤ ((I.filter (fun i => n ∈ S i)).card : ℝ) := by
    intro n
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ I, ‖(if n ∈ S i then a i n else 0)‖
        ≤ (if n ∈ S i then (1 : ℝ) else 0) := by
      intro i _
      by_cases hi : n ∈ S i
      · rw [if_pos hi, if_pos hi]
        exact ha i n
      · rw [if_neg hi, if_neg hi, norm_zero]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsq : ∀ n ∈ Finset.Icc 1 N, ‖∑ i ∈ I, (if n ∈ S i then a i n else 0)‖ ^ 2
      ≤ K * ((I.filter (fun i => n ∈ S i)).card : ℝ) := by
    intro n hn
    have h0 : (0 : ℝ) ≤ ‖∑ i ∈ I, (if n ∈ S i then a i n else 0)‖ := norm_nonneg _
    have hc := hcount n
    have hKn := hK n hn
    nlinarith [h0, hc, hKn]
  refine le_trans (Finset.sum_le_sum hsq) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) ?_
  · -- double counting
    have hdc : ∑ n ∈ Finset.Icc 1 N, ((I.filter (fun i => n ∈ S i)).card : ℝ)
        = ∑ i ∈ I, ((S i ∩ Finset.Icc 1 N).card : ℝ) := by
      have hnat : ∑ n ∈ Finset.Icc 1 N, (I.filter (fun i => n ∈ S i)).card
          = ∑ i ∈ I, (S i ∩ Finset.Icc 1 N).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hnat
    exact hdc
  · exact hK0

/-- **The mean square of a sum of Gallagher polynomials.**  With every index set inside `[1, N]` and
unit coefficients, the mean square is at most the mean-value factor times `K` times the total
index-set size. -/
theorem integral_Icc_normSq_sum_logPoly_le {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (a : ι → ℕ → ℂ) (S : ι → Finset ℕ) {N : ℕ} (hSN : ∀ i ∈ I, S i ⊆ Finset.Icc 1 N)
    (ha : ∀ i n, ‖a i n‖ ≤ 1) {K W : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ n ∈ Finset.Icc 1 N, ((I.filter (fun i => n ∈ S i)).card : ℝ) ≤ K) (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖∑ i ∈ I, logPoly (a i) (S i) w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ))
          * (K * ∑ i ∈ I, ((S i ∩ Finset.Icc 1 N).card : ℝ)) := by
  classical
  set A : ℕ → ℂ := fun n => ∑ i ∈ I, (if n ∈ S i then a i n else 0) with hA
  have hrep : ∀ w : ℝ, ∑ i ∈ I, logPoly (a i) (S i) w = logPoly A (Finset.Icc 1 N) w := by
    intro w
    have hstep : ∀ i ∈ I, logPoly (a i) (S i) w
        = logPoly (fun n => if n ∈ S i then a i n else 0) (Finset.Icc 1 N) w := by
      intro i hi
      exact logPoly_restrict (a i) (hSN i hi) w
    rw [Finset.sum_congr rfl hstep, sum_logPoly_eq]
  have hcongr : (∫ w in Set.Icc (-W) W, ‖∑ i ∈ I, logPoly (a i) (S i) w‖ ^ 2)
      = ∫ w in Set.Icc (-W) W, ‖logPoly A (Finset.Icc 1 N) w‖ ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [hrep w]
  rw [hcongr]
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 N := by
    intro hc
    rw [Finset.mem_Icc] at hc
    omega
  have hM : ∀ n ∈ Finset.Icc 1 N, n ≤ N := fun n hn => (Finset.mem_Icc.1 hn).2
  have henergy := integral_Icc_normSq_logPoly_le_energy A h0 hM hW
  have hmass := sum_normSq_overlap_coeff_le I a S N ha hK0 hK
  have hcoef : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ) := by
    have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W := mul_nonneg (by positivity) hW0.le
    have h2 : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * (N : ℝ) := mul_nonneg (by positivity) hN0
    linarith
  exact henergy.trans (mul_le_mul_of_nonneg_left hmass hcoef)

/-- **The mean square of a prime-shifted family.**  A sum `∑_i μ(p_i)p_i^{2πiw}·∑_{m ∈ D_i}c_m
m^{2πiw}` is a single Gallagher polynomial over the shifted sets, so its mean square carries one
power of the overlap count `K` and the total index-set size — never a Cauchy--Schwarz over `i`. -/
theorem integral_Icc_normSq_primeShift_family_le {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (p : ι → ℕ) (D : ι → Finset ℕ) (c : ℕ → ℂ) {N : ℕ} {K W : ℝ}
    (hp : ∀ i ∈ I, 0 < p i) (hD : ∀ i ∈ I, ∀ m ∈ D i, 0 < m)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hK0 : 0 ≤ K)
    (hDN : ∀ i ∈ I, (D i).image (fun m => p i * m) ⊆ Finset.Icc 1 N)
    (hK : ∀ n ∈ Finset.Icc 1 N,
      ((I.filter (fun i => n ∈ (D i).image (fun m => p i * m))).card : ℝ) ≤ K)
    (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖∑ i ∈ I, moebiusPhase w (p i) * logPoly c (D i) w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ))
          * (K * ∑ i ∈ I, ((D i).card : ℝ)) := by
  classical
  have hrep : ∀ w : ℝ, (∑ i ∈ I, moebiusPhase w (p i) * logPoly c (D i) w)
      = ∑ i ∈ I, logPoly (primeShiftCoeff (p i) c) ((D i).image (fun m => p i * m)) w := by
    intro w
    refine Finset.sum_congr rfl fun i hi => ?_
    exact moebiusPhase_mul_logPoly (hp i hi) c (hD i hi) w
  have hcongr : (∫ w in Set.Icc (-W) W,
        ‖∑ i ∈ I, moebiusPhase w (p i) * logPoly c (D i) w‖ ^ 2)
      = ∫ w in Set.Icc (-W) W,
        ‖∑ i ∈ I, logPoly (primeShiftCoeff (p i) c)
          ((D i).image (fun m => p i * m)) w‖ ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [hrep w]
  rw [hcongr]
  have hbase := integral_Icc_normSq_sum_logPoly_le I (fun i => primeShiftCoeff (p i) c)
    (fun i => (D i).image (fun m => p i * m)) hDN
    (fun i n => norm_primeShiftCoeff_le hc n) hK0 hK hW
  refine hbase.trans ?_
  have hcoef : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ) := by
    have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W := mul_nonneg (by positivity) hW0.le
    have h2 : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * (N : ℝ) := mul_nonneg (by positivity) hN0
    linarith
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) hK0) hcoef
  intro i hi
  have hcard : (((D i).image (fun m => p i * m) ∩ Finset.Icc 1 N).card : ℝ)
      ≤ (((D i).image (fun m => p i * m)).card : ℝ) := by
    have := Finset.card_le_card (Finset.inter_subset_left
      (s₁ := (D i).image (fun m => p i * m)) (s₂ := Finset.Icc 1 N))
    exact_mod_cast this
  have himg : (((D i).image (fun m => p i * m)).card : ℝ) = ((D i).card : ℝ) := by
    have hinj : Set.InjOn (fun m => p i * m) ((D i) : Set ℕ) := by
      intro m₁ _ m₂ _ hEq
      have hEq' : p i * m₁ = p i * m₂ := hEq
      exact Nat.eq_of_mul_eq_mul_left (hp i hi) hEq'
    rw [Finset.card_image_of_injOn hinj]
  rw [himg] at hcard
  exact hcard

end

end RHTower.Sieve
