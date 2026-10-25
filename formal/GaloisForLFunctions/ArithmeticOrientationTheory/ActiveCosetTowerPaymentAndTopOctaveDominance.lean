import GaloisForLFunctions.ArithmeticOrientationTheory.CosetToeplitzDominanceAndShiftedPairSelectivity
import GaloisForLFunctions.ArithmeticOrientationTheory.ContinuumTowerReflectionCholesky
import Mathlib.NumberTheory.Chebyshev

/-!
# Active-coset shared tower payment, top-octave Archimedean dominance, and single-cell continuum Cholesky compensation

In `TheTowerOddSideIsACholeskyEnergyMinusTheMass`, dropping every non-unit zeroth Cholesky mode
`cosetTail q p X a' 0²` (`a' ≠ 1`) and every higher innovation `(1 − 1/p) cosetTail q p X a' (j+1)²`
gave the single-prime bound `towerOddPrimeSide q X p K ≥ −log p · ∑_{2 ≤ n ≤ X} q(n)²`. Summing that
coarse bound over a prime set `S ⊆ [2, M]` produces `−ϑ(M) · ∑ q(n)²`, which diverges linearly in
`M` (`ϑ(M) ≫ M`) once `M` exceeds `X`.

This module eliminates the `M`-divergence completely and establishes the sharp `M`-independent
shared-payment architecture across arbitrary finite sets of primes:

1. **Exact `p > X` tower vanishing (`towerOddPrimeSide_eq_zero_of_lt`).**
   By axis-pair cancellation (`two_mul_ratioCorr_sub_productCorr_eq_interior`), for any profile `q`
   supported on `[1, X]` (`X ≥ 1`), every prime `p > X` and every truncation `K : ℕ` satisfy
   `towerOddPrimeSide q X p K = 0` identically.

2. **Singleton-coset cancellation and top-site Cholesky reduction
   (`cosetTail_eq_single_of_lt_mul`, `towerOddPrimeSide_ge_neg_primeTowerCharge`,
   `sum_towerOddPrimeSide_ge_neg_activeTowerWeight`).**
   For `p ≤ X` and any `n ∈ [2, X]` with `X / p < n`:
   * If `p ∤ n`, `n` is the sole site of its non-unit `p`-free coset, so
     `cosetTail q p X n 0² − q(n)² = 0` (`0` net charge at `n` instead of `log p`).
   * If `p ∣ n`, `n` is the top occupied site of its coset, so
     `(1 − 1/p) cosetTail q p X a' M² − q(n)² = −(1/p) q(n)²` (reducing the charge at `n` from
     `log p` to `log p / p`).
   Summing over **any** finite set of primes `S : Finset ℕ` (with **zero upper bound on `max S`**)
   yields the `M`-independent shared-payment bound
   `∑_{p ∈ S} towerOddPrimeSide q X p (K p) ≥ −∑_{n=2}^X activeTowerWeight S X n · q(n)²`,
   where `activeTowerWeight S X n ≤ Chebyshev.theta (X / n) + (1/2) log n`.

3. **Unconditional Archimedean dominance on the top octave and down to the square-root horizon
   (`activeTowerWeight_lt_archReflectedDiagWeight_of_top_octave`,
   `activeTowerWeight_lt_archReflectedDiagWeight_of_sq_horizon`,
   `sum_towerOddPrimeSide_add_archDiag_nonneg_of_top_octave`,
   `sum_towerOddPrimeSide_add_archDiag_ge_sub_sqrtHorizon`).**
   * On the entire **top octave** `X / 2 < n ≤ X` (`n ≥ 4`), `X / n < 2` forces `θ(X / n) = 0`, and
     `(1/2) log n < archReflectedDiagWeight n`, so `archReflectedDiagWeight` pays **all primes
     simultaneously** with strictly positive reserve on arbitrary-sign top-octave profiles.
   * By Chebyshev's elementary bound `θ(Y) ≤ (log 4) Y < (7/5) Y`, `archReflectedDiagWeight n`
     strictly dominates `activeTowerWeight S X n` for every `n ≥ 5` satisfying
     `9 X + 3 n log n ≤ n²` (down to `n ≳ 3 √X`), localizing the entire lattice shared-payment
     problem to the sub-square-root support `2 ≤ n ≲ 3 √X`.

4. **Single-cell continuum Cholesky compensation (`log p ≥ A`), `S`-uniform all-prime continuum
   shared payment, and shifted-pair selectivity
   (`continuumPrimeTower_eq_zero_of_two_mul_le_log`,
   `continuumPrimeTower_zero_ge_neg_div_sqrt`,
   `sum_continuumPrimeTower_ge_neg_twelve_exp`,
   `shiftedTowerOddPrimeSide_point_top_octave_lt_neg_arch`).**
   * For a continuum profile `F` vanishing on `[A, ∞)` (`A ≥ 0`), `continuumPrimeTower F p N = 0`
     whenever `2 A ≤ log p`, and when `A ≤ log p` the reflected Cholesky identity retains
     `(1 − p^{−1/2}) ‖F‖₂²`, reducing the required diagonal compensation from `log p · ‖F‖₂²` to
     `(log p / √p) ∫_0^A F(x)² dx`. Combining all three prime regimes (`2 A ≤ log p`, `A ≤ log p < 2 A`,
     and `log p < A`) with a dyadic Chebyshev bound eliminates the `#S`-divergence of
     `ContinuumTowerReflectionCholesky` completely across **arbitrary** finite prime sets `S`:
     `∑_{p ∈ S} continuumPrimeTower F p (N p) ≥ −12 e^A ∫_0^A F(x)² dx`.
   * Conversely, for the non-tempered shifted pair `ζ(s − a)ζ(s + a)` with `|a| ≥ 1`, even a single
     point mass `q = δ_p` in the top octave `(X/2, X]` (`X = p`) violates Archimedean payment:
     `shiftedTowerOddPrimeSide a δ_p p p 1 + archReflectedDiagWeight p < 0`.
-/

open Finset ArithmeticFunction MeasureTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact `p > X` vanishing of `towerOddPrimeSide` -/

/-- **Exact vanishing above the profile cutoff (`p > X`).**
For any profile `q : ℕ → ℝ` supported on `[1, X]` (`X ≥ 1`), every prime `p > X` and every
truncation `K : ℕ` satisfy `towerOddPrimeSide q X p K = 0` identically (regardless of `q(1)`). -/
theorem towerOddPrimeSide_eq_zero_of_lt {q : ℕ → ℝ} {X : ℕ} (hX : 1 ≤ X)
    (hq : ∀ n, X < n → q n = 0) {p : ℕ} (hp : p.Prime) (hpX : X < p) (K : ℕ) :
    towerOddPrimeSide q X p K = 0 := by
  unfold towerOddPrimeSide
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hpk_ge_p : p ≤ p ^ k := Nat.le_self_pow (by omega) p
  have hpk2 : 2 ≤ p ^ k := hp.two_le.trans hpk_ge_p
  rw [two_mul_ratioCorr_sub_productCorr_eq_interior q hX hpk2]
  have hrat0 : ∑ a ∈ Icc 2 X, q a * q (a * p ^ k) = 0 :=
    Finset.sum_eq_zero fun a ha => by
      have ha2 : 2 ≤ a := (Finset.mem_Icc.mp ha).1
      have hgt : X < a * p ^ k :=
        lt_of_lt_of_le (lt_of_lt_of_le hpX hpk_ge_p) (Nat.le_mul_of_pos_left _ (by omega))
      rw [hq _ hgt, mul_zero]
  have hprod0 : ∑ d ∈ ((p ^ k).divisors.erase 1).erase (p ^ k), q d * q (p ^ k / d) = 0 :=
    Finset.sum_eq_zero fun d hd => by
      have hd1 : d ≠ 1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hd)).1
      have hdvd : d ∣ p ^ k :=
        Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd))
      obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · exact absurd rfl hd1
        · exact hj
      have hgt : X < p ^ j := lt_of_lt_of_le hpX (Nat.le_self_pow (by omega) p)
      rw [hq _ hgt, zero_mul]
  rw [hrat0, hprod0]
  ring

/-! ## §2. Singleton-coset cancellation, top-site reduction, and `M`-independent tower payment -/

/-- At the top occupied site `j` of a coset (`X < p^{j+1} a'`), all strictly higher coset sites
vanish, so `cosetTail q p X a' j = q(p^j a')`. -/
theorem cosetTail_eq_single_of_lt_mul {q : ℕ → ℝ} {X : ℕ} (hq : ∀ n, X < n → q n = 0)
    {p a' j : ℕ} (hp : p.Prime) (hj : j ≤ Nat.log p X) (htop : X < p ^ (j + 1) * a') :
    cosetTail q p X a' j = q (p ^ j * a') := by
  unfold cosetTail
  rw [kmsTail_eq_of_le _ _ hj]
  have hnext0 : kmsTail ((p : ℝ) ^ (-(1 / 2 : ℝ))) (fun i => q (p ^ i * a'))
      (Nat.log p X) (j + 1) = 0 := by
    unfold kmsTail
    refine Finset.sum_eq_zero fun i hi => ?_
    have hij : j + 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hgt : X < p ^ i * a' :=
      lt_of_lt_of_le htop (Nat.mul_le_mul_right a' (Nat.pow_le_pow_right hp.pos hij))
    dsimp only
    rw [hq _ hgt, mul_zero]
  rw [hnext0, mul_zero, add_zero]

/-- Sharp single-prime Cholesky diagonal charge at integer `n ∈ [2, X]`:
`log p` if `p n ≤ X` (`n ≤ X / p`), `log p / p` if `p n > X` and `p ∣ n`, and `0` otherwise. -/
def primeTowerCharge (X p n : ℕ) : ℝ :=
  if n ≤ X / p then Real.log p
  else if p ∣ n then Real.log p / (p : ℝ)
  else 0

theorem primeTowerCharge_nonneg {p : ℕ} (hp : p.Prime) (X n : ℕ) :
    0 ≤ primeTowerCharge X p n := by
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold primeTowerCharge
  split_ifs <;> positivity

theorem primeTowerCharge_eq_zero_of_lt {X p n : ℕ} (hn2 : 2 ≤ n) (hnX : n ≤ X) (hpX : X < p) :
    primeTowerCharge X p n = 0 := by
  unfold primeTowerCharge
  rw [if_neg (by rw [Nat.div_eq_of_lt hpX]; omega),
    if_neg (fun hdvd => absurd (Nat.le_of_dvd (by omega) hdvd) (by omega))]

/-- **Sharpened single-prime Cholesky lower bound.**
Retaining singleton non-unit coset modes `cosetTail q p X n 0²` (`X < p n`, `p ∤ n`) and top-site
innovations `(1 − 1/p) cosetTail q p X a' M²` (`X < p n`, `p ∣ n`) improves `towerOddPrimeSide_ge`
to `−∑_{n=2}^X primeTowerCharge X p n · q(n)²` for every prime `p` (including `p > X`). -/
theorem towerOddPrimeSide_ge_neg_primeTowerCharge {q : ℕ → ℝ} {X : ℕ} (hX : 1 ≤ X)
    (hq : ∀ n, X < n → q n = 0) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hK : p ≤ X → Nat.log p X ≤ K) :
    -(∑ n ∈ Icc 2 X, primeTowerCharge X p n * q n ^ 2) ≤ towerOddPrimeSide q X p K := by
  rcases lt_or_ge X p with hpX | hpX
  · rw [towerOddPrimeSide_eq_zero_of_lt hX hq hp hpX K,
      Finset.sum_eq_zero fun n hn => by
        rw [primeTowerCharge_eq_zero_of_lt (Finset.mem_Icc.mp hn).1
          (Finset.mem_Icc.mp hn).2 hpX, zero_mul],
      neg_zero]
  · have hKL : Nat.log p X ≤ K := hK hpX
    have hK_vanish : ∀ i, K < i → q (p ^ i) = 0 := fun i hi => by
      simpa using coset_vanishes hq hp le_rfl i (lt_of_le_of_lt hKL hi)
    rw [towerOddPrimeSide_eq_cholesky hX hq hp hK_vanish (by omega)]
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : 0 ≤ 1 - 1 / (p : ℝ) := by
      rw [sub_nonneg, div_le_one hp0]; exact_mod_cast hp.one_le
    -- Rewrite the bound as a positive saving sum over `{n ∈ Icc 2 X | X / p < n}`
    suffices hsave : ∑ n ∈ Icc 2 X, (Real.log p - primeTowerCharge X p n) * q n ^ 2 ≤
        Real.log p * (∑ a' ∈ (pfreeLabels p X).erase 1, cosetTail q p X a' 0 ^ 2 +
          (1 - 1 / (p : ℝ)) * ∑ a' ∈ pfreeLabels p X,
            ∑ j ∈ range (Nat.log p X), cosetTail q p X a' (j + 1) ^ 2) by
      have hexp : ∑ n ∈ Icc 2 X, (Real.log p - primeTowerCharge X p n) * q n ^ 2 =
          Real.log p * (∑ n ∈ Icc 2 X, q n ^ 2) -
            ∑ n ∈ Icc 2 X, primeTowerCharge X p n * q n ^ 2 := by
        simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
      linarith
    rw [← Finset.sum_filter_add_sum_filter_not (Icc 2 X) (fun n => n ≤ X / p)]
    have hlow0 : ∑ n ∈ (Icc 2 X).filter (fun n => n ≤ X / p),
        (Real.log p - primeTowerCharge X p n) * q n ^ 2 = 0 :=
      Finset.sum_eq_zero fun n hn => by
        rw [primeTowerCharge, if_pos (Finset.mem_filter.mp hn).2, sub_self, zero_mul]
    rw [hlow0, zero_add]
    set Top := (Icc 2 X).filter (fun n => ¬ n ≤ X / p)
    rw [← Finset.sum_filter_add_sum_filter_not Top (fun n => p ∣ n), mul_add,
      add_comm (Real.log p * ∑ a' ∈ (pfreeLabels p X).erase 1, cosetTail q p X a' 0 ^ 2)]
    refine add_le_add ?_ ?_
    · -- Top-site prime multiples (`X / p < n`, `p ∣ n`) map injectively to `(a', v_p(n) - 1)`
      set TopDvd := Top.filter (fun n => p ∣ n)
      have hterm_dvd : ∀ n ∈ TopDvd,
          (Real.log p - primeTowerCharge X p n) * q n ^ 2 =
            Real.log p * ((1 - 1 / (p : ℝ)) * q n ^ 2) := fun n hn => by
        obtain ⟨hnTop, hdvd⟩ := Finset.mem_filter.mp hn
        have hnotle : ¬ n ≤ X / p := (Finset.mem_filter.mp hnTop).2
        rw [primeTowerCharge, if_neg hnotle, if_pos hdvd]
        ring
      rw [Finset.sum_congr rfl hterm_dvd, ← Finset.mul_sum, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hp1) hlog
      set φ : ℕ → ℕ × ℕ := fun n => (pfreePart p n, n.factorization p - 1)
      have hφ_props : ∀ n ∈ TopDvd,
          φ n ∈ pfreeLabels p X ×ˢ range (Nat.log p X) ∧
            p ^ ((φ n).2 + 1) * (φ n).1 = n ∧
            cosetTail q p X (φ n).1 ((φ n).2 + 1) = q n := by
        intro n hn
        obtain ⟨hnTop, hdvd⟩ := Finset.mem_filter.mp hn
        obtain ⟨hnIcc, hnotle⟩ := Finset.mem_filter.mp hnTop
        obtain ⟨hn2, hnX⟩ := Finset.mem_Icc.mp hnIcc
        have hn0 : n ≠ 0 := by omega
        have hv1 : 1 ≤ n.factorization p :=
          (hp.dvd_iff_one_le_factorization hn0).mp hdvd
        have hmul_n : p ^ ((n.factorization p - 1) + 1) * pfreePart p n = n := by
          rw [Nat.sub_add_cancel hv1]
          exact pfreePart_mul_pow p n
        have hv_le_log : n.factorization p ≤ Nat.log p X := by
          apply Nat.le_log_of_pow_le hp.one_lt
          calc p ^ n.factorization p
              ≤ p ^ n.factorization p * pfreePart p n :=
                Nat.le_mul_of_pos_right _ (pfreePart_pos hn0)
            _ = n := pfreePart_mul_pow p n
            _ ≤ X := hnX
        have hgt_mul : X < p * n := by
          by_contra hle
          push Not at hle
          exact hnotle ((Nat.le_div_iff_mul_le hp.pos).mpr (by rw [mul_comm]; exact hle))
        have htop_pow : X < p ^ ((n.factorization p - 1) + 1 + 1) * pfreePart p n := by
          calc X < p * n := hgt_mul
            _ = p * (p ^ ((n.factorization p - 1) + 1) * pfreePart p n) := by rw [hmul_n]
            _ = p ^ ((n.factorization p - 1) + 1 + 1) * pfreePart p n := by rw [pow_succ']; ring
        refine ⟨Finset.mem_product.mpr ⟨pfreePart_mem_pfreeLabels hp (Finset.mem_Icc.mpr ⟨by omega, hnX⟩),
          Finset.mem_range.mpr (by dsimp only [φ]; omega)⟩, hmul_n, ?_⟩
        dsimp only [φ]
        rw [cosetTail_eq_single_of_lt_mul hq hp (by omega) htop_pow, hmul_n]
      have hinj : Set.InjOn φ TopDvd := fun n₁ hn₁ n₂ hn₂ heq => by
        have h1 := (hφ_props n₁ hn₁).2.1
        have h2 := (hφ_props n₂ hn₂).2.1
        rw [heq] at h1
        exact h1.symm.trans h2
      have hrew_sq : ∑ n ∈ TopDvd, q n ^ 2 =
          ∑ n ∈ TopDvd, (fun x : ℕ × ℕ => cosetTail q p X x.1 (x.2 + 1) ^ 2) (φ n) :=
        Finset.sum_congr rfl fun n hn => by dsimp only; rw [(hφ_props n hn).2.2]
      rw [hrew_sq,
        ← Finset.sum_image (f := fun x : ℕ × ℕ => cosetTail q p X x.1 (x.2 + 1) ^ 2) hinj,
        ← Finset.sum_product']
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => by obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx; exact (hφ_props n hn).1)
        (fun _ _ _ => sq_nonneg _)
    · -- Singleton non-unit cosets (`X / p < n`, `¬ p ∣ n`) lie in `(pfreeLabels p X).erase 1`
      set TopCop := Top.filter (fun n => ¬ p ∣ n)
      have hterm_cop : ∀ n ∈ TopCop,
          (Real.log p - primeTowerCharge X p n) * q n ^ 2 =
            Real.log p * cosetTail q p X n 0 ^ 2 := fun n hn => by
        obtain ⟨hnTop, hndvd⟩ := Finset.mem_filter.mp hn
        obtain ⟨hnIcc, hnotle⟩ := Finset.mem_filter.mp hnTop
        rw [primeTowerCharge, if_neg hnotle, if_neg hndvd, sub_zero]
        have hgt_mul : X < p ^ (0 + 1) * n := by
          rw [zero_add, pow_one]
          by_contra hle
          push Not at hle
          exact hnotle ((Nat.le_div_iff_mul_le hp.pos).mpr (by rw [mul_comm]; exact hle))
        rw [cosetTail_eq_single_of_lt_mul hq hp (Nat.zero_le _) hgt_mul, pow_zero, one_mul]
      rw [Finset.sum_congr rfl hterm_cop, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hlog
      have hsub : TopCop ⊆ (pfreeLabels p X).erase 1 := fun n hn => by
        obtain ⟨hnTop, hndvd⟩ := Finset.mem_filter.mp hn
        obtain ⟨hn2, hnX⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hnTop).1
        exact Finset.mem_erase.mpr ⟨by omega,
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hnX⟩, hndvd⟩⟩
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _

/-- Total `S`-shared diagonal charge at integer `n`:
`activeTowerWeight S X n = ∑_{p ∈ S} primeTowerCharge X p n`. -/
def activeTowerWeight (S : Finset ℕ) (X n : ℕ) : ℝ :=
  ∑ p ∈ S, primeTowerCharge X p n

theorem activeTowerWeight_nonneg {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (X n : ℕ) :
    0 ≤ activeTowerWeight S X n :=
  Finset.sum_nonneg fun p hp => primeTowerCharge_nonneg (hS p hp) X n

/-- **All-prime `M`-independent shared tower payment lower bound.**
For every profile `q` supported on `[1, X]`, every finite set of primes `S : Finset ℕ` (with no
upper bound on `S`), and every truncation family `K : ℕ → ℕ` with `K p ≥ log_p X` for `p ≤ X`,
`∑_{p ∈ S} towerOddPrimeSide q X p (K p) ≥ −∑_{n=2}^X activeTowerWeight S X n · q(n)²`. -/
theorem sum_towerOddPrimeSide_ge_neg_activeTowerWeight {q : ℕ → ℝ} {X : ℕ} (hX : 1 ≤ X)
    (hq : ∀ n, X < n → q n = 0) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {K : ℕ → ℕ} (hK : ∀ p ∈ S, p ≤ X → Nat.log p X ≤ K p) :
    -(∑ n ∈ Icc 2 X, activeTowerWeight S X n * q n ^ 2) ≤
      ∑ p ∈ S, towerOddPrimeSide q X p (K p) := by
  have hsum : ∑ n ∈ Icc 2 X, activeTowerWeight S X n * q n ^ 2 =
      ∑ p ∈ S, ∑ n ∈ Icc 2 X, primeTowerCharge X p n * q n ^ 2 := by
    unfold activeTowerWeight
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hsum, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun p hp =>
    towerOddPrimeSide_ge_neg_primeTowerCharge hX hq (hS p hp) (hK p hp)

/-! ## §3. Chebyshev + prime-divisor bound and Archimedean closure down to `n ≳ √X` -/

private theorem sum_primeFactors_log_le_log {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ n.primeFactors, Real.log p ≤ Real.log n := by
  have hprimes : ∀ p ∈ n.primeFactors, p.Prime := fun _ hp => Nat.prime_of_mem_primeFactors hp
  have hdvd : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
  have hpos : 0 < ∏ p ∈ n.primeFactors, p :=
    Finset.prod_pos fun p hp => (hprimes p hp).pos
  have hle : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) ≤ (n : ℝ) :=
    by exact_mod_cast Nat.le_of_dvd (by omega) hdvd
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (hprimes p hp).ne_zero), ← Nat.cast_prod]
  exact Real.log_le_log (by exact_mod_cast hpos) hle

/-- **Uniform `S`-independent bound on `activeTowerWeight`.**
For every finite set of primes `S`, cutoff `X`, and `n ≥ 1`,
`activeTowerWeight S X n ≤ Chebyshev.theta (X / n) + (1 / 2) log n`. -/
theorem activeTowerWeight_le_theta_add_half_log {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (X : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    activeTowerWeight S X n ≤ Chebyshev.theta ((X / n : ℕ) : ℝ) + (1 / 2) * Real.log n := by
  unfold activeTowerWeight
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => n ≤ X / p)]
  refine add_le_add ?_ ?_
  · -- Active non-top primes satisfy `p ≤ X / n`, bounded by `Chebyshev.theta (X / n)`
    have hterm1 : ∀ p ∈ S.filter (fun p => n ≤ X / p), primeTowerCharge X p n = Real.log p :=
      fun p hp => by rw [primeTowerCharge, if_pos (Finset.mem_filter.mp hp).2]
    rw [Finset.sum_congr rfl hterm1, Chebyshev.theta, Nat.floor_natCast]
    have hsub1 : S.filter (fun p => n ≤ X / p) ⊆ (Ioc 0 (X / n)).filter Nat.Prime := by
      intro p hp
      obtain ⟨hpS, hnle⟩ := Finset.mem_filter.mp hp
      have hpp := hS p hpS
      have hple : p ≤ X / n := (Nat.le_div_iff_mul_le hn).mpr
        (by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hpp.pos).mp hnle)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpp.pos, hple⟩, hpp⟩
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun p hp _ =>
      Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
  · -- Top-site primes divide `n` and carry `log p / p ≤ (1/2) log p`
    rw [← Finset.sum_filter_add_sum_filter_not (S.filter (fun p => ¬ n ≤ X / p)) (fun p => p ∣ n)]
    have hzero : ∑ p ∈ (S.filter (fun p => ¬ n ≤ X / p)).filter (fun p => ¬ p ∣ n),
        primeTowerCharge X p n = 0 :=
      Finset.sum_eq_zero fun p hp => by
        obtain ⟨hp1, hndvd⟩ := Finset.mem_filter.mp hp
        rw [primeTowerCharge, if_neg (Finset.mem_filter.mp hp1).2, if_neg hndvd]
    rw [hzero, add_zero]
    set S_dvd := (S.filter (fun p => ¬ n ≤ X / p)).filter (fun p => p ∣ n)
    calc ∑ p ∈ S_dvd, primeTowerCharge X p n
        ≤ ∑ p ∈ S_dvd, (1 / 2 : ℝ) * Real.log p := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨hp1, hdvd⟩ := Finset.mem_filter.mp hp
          obtain ⟨hpS, hnotle⟩ := Finset.mem_filter.mp hp1
          have hpp := hS p hpS
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
          have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
          rw [primeTowerCharge, if_neg hnotle, if_pos hdvd]
          rw [div_le_iff₀ (by positivity)]
          nlinarith
      _ = (1 / 2 : ℝ) * ∑ p ∈ S_dvd, Real.log p := (Finset.mul_sum _ _ _).symm
      _ ≤ (1 / 2 : ℝ) * ∑ p ∈ n.primeFactors, Real.log p := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ =>
              Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
            (by norm_num)
          obtain ⟨hp1, hdvd⟩ := Finset.mem_filter.mp hp
          exact Nat.mem_primeFactors.mpr ⟨hS p (Finset.mem_filter.mp hp1).1, hdvd, by omega⟩
      _ ≤ (1 / 2 : ℝ) * Real.log n :=
          mul_le_mul_of_nonneg_left (sum_primeFactors_log_le_log hn) (by norm_num)

private theorem half_log_lt_archReflectedDiagWeight {n : ℕ} (hn : 4 ≤ n) :
    (1 / 2 : ℝ) * Real.log n < archReflectedDiagWeight n := by
  rcases eq_or_lt_of_le hn with rfl | hn5
  · -- Direct check at `n = 4`: `(1/2) log 4 = log 2 < 0.694 < 1783 / 2040 = W_arch(4)`
    rw [archReflectedDiagWeight_eq (by omega : 2 ≤ 4)]
    have hlog4 : (1 / 2 : ℝ) * Real.log (4 : ℕ) = Real.log 2 := by
      rw [show ((4 : ℕ) : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [hlog4]
    norm_num
    linarith [Real.log_two_lt_d9]
  · -- For `n ≥ 5`, `(1/2) log n < n / 6 < W_arch(n)`
    refine lt_trans ?_ (div_six_lt_archReflectedDiagWeight hn)
    have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn5
    have hsplit : Real.log (n : ℝ) = 2 * Real.log 2 + Real.log ((n : ℝ) / 4) := by
      have h4 : (n : ℝ) = (2 : ℝ) ^ 2 * ((n : ℝ) / 4) := by ring
      conv_lhs => rw [h4]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    have hlog_div : Real.log ((n : ℝ) / 4) ≤ (n : ℝ) / 4 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    linarith [Real.log_two_lt_d9]

/-- **Unconditional top-octave Archimedean dominance (`X < 2 n`, `n ≥ 4`).**
At every integer `n ≥ 4` in the top octave `X / 2 < n ≤ X`, `activeTowerWeight S X n` is strictly
dominated by `archReflectedDiagWeight n` simultaneously for **every** finite set of primes `S`. -/
theorem activeTowerWeight_lt_archReflectedDiagWeight_of_top_octave {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {X n : ℕ} (hn4 : 4 ≤ n) (htop : X < 2 * n) :
    activeTowerWeight S X n < archReflectedDiagWeight n := by
  have hdiv_lt : ((X / n : ℕ) : ℝ) < 2 := by
    exact_mod_cast Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact htop)
  have hθ0 : Chebyshev.theta ((X / n : ℕ) : ℝ) = 0 :=
    Chebyshev.theta_eq_zero_of_lt_two hdiv_lt
  calc activeTowerWeight S X n
      ≤ Chebyshev.theta ((X / n : ℕ) : ℝ) + (1 / 2) * Real.log n :=
        activeTowerWeight_le_theta_add_half_log hS X (by omega)
    _ = (1 / 2) * Real.log n := by rw [hθ0, zero_add]
    _ < archReflectedDiagWeight n := half_log_lt_archReflectedDiagWeight hn4

/-- **Archimedean dominance down to the square-root horizon (`9 X + 3 n log n ≤ n²`).**
By Chebyshev's elementary bound `θ(Y) ≤ (log 4) Y`, for every `n ≥ 5` satisfying
`9 X + 3 n log n ≤ n²`, `archReflectedDiagWeight n` strictly dominates `activeTowerWeight S X n`
across **every** finite set of primes `S` (independently of `max S`). -/
theorem activeTowerWeight_lt_archReflectedDiagWeight_of_sq_horizon {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {X n : ℕ} (hn5 : 5 ≤ n)
    (hsq : 9 * (X : ℝ) + 3 * (n : ℝ) * Real.log n ≤ (n : ℝ) ^ 2) :
    activeTowerWeight S X n < archReflectedDiagWeight n := by
  refine lt_of_le_of_lt ?_ (div_six_lt_archReflectedDiagWeight (by omega : 4 ≤ n))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdiv_le : ((X / n : ℕ) : ℝ) ≤ (X : ℝ) / n := by
    rw [le_div_iff₀ hn0]
    exact_mod_cast Nat.div_mul_le_self X n
  have hlog4 : Real.log 4 < 3 / 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have hθ : Chebyshev.theta ((X / n : ℕ) : ℝ) ≤ (3 / 2 : ℝ) * ((X : ℝ) / n) := by
    calc Chebyshev.theta ((X / n : ℕ) : ℝ)
        ≤ Real.log 4 * ((X / n : ℕ) : ℝ) := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
      _ ≤ (3 / 2 : ℝ) * ((X / n : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hlog4.le (Nat.cast_nonneg _)
      _ ≤ (3 / 2 : ℝ) * ((X : ℝ) / n) := mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
  calc activeTowerWeight S X n
      ≤ Chebyshev.theta ((X / n : ℕ) : ℝ) + (1 / 2) * Real.log n :=
        activeTowerWeight_le_theta_add_half_log hS X (by omega)
    _ ≤ (3 / 2 : ℝ) * ((X : ℝ) / n) + (1 / 2) * Real.log n := add_le_add hθ le_rfl
    _ ≤ (n : ℝ) / 6 := by
        rw [div_eq_mul_inv (X : ℝ), ← le_sub_iff_add_le']
        have h1 : 9 * (X : ℝ) ≤ (n : ℝ) ^ 2 - 3 * (n : ℝ) * Real.log n := by linarith
        have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (6 * (n : ℝ))⁻¹)
        field_simp at h2 ⊢
        linarith

/-- **Unconditional all-prime shared-payment positivity on the top octave.**
For any profile `q : ℕ → ℝ` supported on the top octave `[max 4 (⌊X/2⌋ + 1), X]`, the sum of
`towerOddPrimeSide` over **any** finite set of primes `S` plus the Archimedean reflected diagonal
`∑_{n=4}^X archReflectedDiagWeight n · q(n)²` is nonnegative. -/
theorem sum_towerOddPrimeSide_add_archDiag_nonneg_of_top_octave {q : ℕ → ℝ} {X : ℕ}
    (hX : 1 ≤ X) (hq_hi : ∀ n, X < n → q n = 0)
    (hq_lo : ∀ n, n < 4 ∨ 2 * n ≤ X → q n = 0)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {K : ℕ → ℕ} (hK : ∀ p ∈ S, p ≤ X → Nat.log p X ≤ K p) :
    0 ≤ (∑ p ∈ S, towerOddPrimeSide q X p (K p)) +
      ∑ n ∈ Icc 4 X, archReflectedDiagWeight n * q n ^ 2 := by
  have htower := sum_towerOddPrimeSide_ge_neg_activeTowerWeight hX hq_hi hS hK
  suffices hdom : ∑ n ∈ Icc 2 X, activeTowerWeight S X n * q n ^ 2 ≤
      ∑ n ∈ Icc 4 X, archReflectedDiagWeight n * q n ^ 2 by linarith
  have hsplit : ∑ n ∈ Icc 2 X, activeTowerWeight S X n * q n ^ 2 =
      ∑ n ∈ Icc 4 X, activeTowerWeight S X n * q n ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.Icc_subset_Icc_left (by omega)) fun n hn hnot => ?_
    have hn4 : n < 4 := by
      simp only [Finset.mem_Icc] at hn hnot
      omega
    rw [hq_lo n (Or.inl hn4), sq, mul_zero, mul_zero]
  rw [hsplit]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn4 : 4 ≤ n := (Finset.mem_Icc.mp hn).1
  rcases le_or_gt (2 * n) X with hle | hgt
  · rw [hq_lo n (Or.inr hle), sq, mul_zero, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right
      (activeTowerWeight_lt_archReflectedDiagWeight_of_top_octave hS hn4 hgt).le (sq_nonneg _)

/-- **Localization of lattice shared payment to the sub-square-root support.**
For every profile `q` supported on `[1, X]` and every finite set of primes `S`, adding
`∑_{n=4}^X archReflectedDiagWeight n · q(n)²` pays all `n ≥ 5` with `9 X + 3 n log n ≤ n²`
simultaneously, leaving only the sub-square-root support `n < 5` or `n² < 9 X + 3 n log n`. -/
theorem sum_towerOddPrimeSide_add_archDiag_ge_sub_sqrtHorizon {q : ℕ → ℝ} {X : ℕ}
    (hX : 1 ≤ X) (hq : ∀ n, X < n → q n = 0) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {K : ℕ → ℕ} (hK : ∀ p ∈ S, p ≤ X → Nat.log p X ≤ K p) :
    -(∑ n ∈ (Icc 2 X).filter
        (fun n : ℕ => n < 5 ∨ (n : ℝ) ^ 2 < 9 * (X : ℝ) + 3 * (n : ℝ) * Real.log (n : ℝ)),
      activeTowerWeight S X n * q n ^ 2) ≤
      (∑ p ∈ S, towerOddPrimeSide q X p (K p)) +
        ∑ n ∈ Icc 4 X, archReflectedDiagWeight n * q n ^ 2 := by
  have htower := sum_towerOddPrimeSide_ge_neg_activeTowerWeight hX hq hS hK
  set Sub := (Icc 2 X).filter
    (fun n : ℕ => n < 5 ∨ (n : ℝ) ^ 2 < 9 * (X : ℝ) + 3 * (n : ℝ) * Real.log (n : ℝ))
  set Sup := (Icc 2 X).filter
    (fun n : ℕ => ¬ (n < 5 ∨ (n : ℝ) ^ 2 < 9 * (X : ℝ) + 3 * (n : ℝ) * Real.log (n : ℝ)))
  have hpart : ∑ n ∈ Icc 2 X, activeTowerWeight S X n * q n ^ 2 =
      (∑ n ∈ Sub, activeTowerWeight S X n * q n ^ 2) +
        ∑ n ∈ Sup, activeTowerWeight S X n * q n ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not (Icc 2 X)
      (fun n : ℕ => n < 5 ∨ (n : ℝ) ^ 2 < 9 * (X : ℝ) + 3 * (n : ℝ) * Real.log (n : ℝ))
      (fun n => activeTowerWeight S X n * q n ^ 2)).symm
  have hsup_le : ∑ n ∈ Sup, activeTowerWeight S X n * q n ^ 2 ≤
      ∑ n ∈ Icc 4 X, archReflectedDiagWeight n * q n ^ 2 := by
    have hsub : Sup ⊆ Icc 4 X := fun n hn => by
      obtain ⟨hnIcc, hnot⟩ := Finset.mem_filter.mp hn
      push Not at hnot
      exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hnIcc).2⟩
    calc ∑ n ∈ Sup, activeTowerWeight S X n * q n ^ 2
        ≤ ∑ n ∈ Sup, archReflectedDiagWeight n * q n ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          obtain ⟨-, hnot⟩ := Finset.mem_filter.mp hn
          push Not at hnot
          exact mul_le_mul_of_nonneg_right
            (activeTowerWeight_lt_archReflectedDiagWeight_of_sq_horizon hS hnot.1 hnot.2).le
            (sq_nonneg _)
      _ ≤ ∑ n ∈ Icc 4 X, archReflectedDiagWeight n * q n ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => by
            have hn4 : 4 ≤ n := (Finset.mem_Icc.mp hn).1
            have hn_pos : (0 : ℝ) < (n : ℝ) / 6 := by
              have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
              positivity
            exact mul_nonneg (lt_trans hn_pos (div_six_lt_archReflectedDiagWeight hn4)).le
              (sq_nonneg _)
  linarith

/-! ## §4. Continuum single-cell Cholesky compensation (`log p ≥ A`) and shifted-pair selectivity -/

/-- **Continuum `2 A ≤ log p` tower vanishing.**
If `F : ℝ → ℝ` vanishes on `[A, ∞)` (`A ≥ 0`), then every prime `p` with `2 A ≤ log p` has
`continuumPrimeTower F p 0 = 0` identically. -/
theorem continuumPrimeTower_eq_zero_of_two_mul_le_log {F : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ x, A ≤ x → F x = 0) {p : ℕ} (_hp : p.Prime) (hlog : 2 * A ≤ Real.log p) :
    continuumPrimeTower F p 0 = 0 := by
  unfold continuumPrimeTower
  simp only [Nat.mul_zero, zero_add, Finset.Icc_self, Finset.sum_singleton, pow_one,
    Nat.cast_one, one_mul]
  have hL : 0 ≤ Real.log p := by linarith
  have h1 : (∫ x in (0 : ℝ)..Real.log p, F x * F (x + Real.log p)) = 0 := by
    calc (∫ x in (0 : ℝ)..Real.log p, F x * F (x + Real.log p))
        = ∫ _x in (0 : ℝ)..Real.log p, (0 : ℝ) := by
          refine intervalIntegral.integral_congr fun x hx => ?_
          rw [Set.uIcc_of_le hL] at hx
          rw [hF (x + Real.log p) (by linarith [hx.1]), mul_zero]
      _ = 0 := by simp
  have h2 : (∫ x in (0 : ℝ)..Real.log p, F x * F (Real.log p - x)) = 0 := by
    calc (∫ x in (0 : ℝ)..Real.log p, F x * F (Real.log p - x))
        = ∫ _x in (0 : ℝ)..Real.log p, (0 : ℝ) := by
          refine intervalIntegral.integral_congr fun x _ => ?_
          rcases le_or_gt A x with hxA | hxA
          · rw [hF x hxA, zero_mul]
          · rw [hF (Real.log p - x) (by linarith), mul_zero]
      _ = 0 := by simp
  rw [h1, h2]
  ring

/-- **Sharpened `O(log p / √p)` single-cell continuum Cholesky bound (`A ≤ log p`).**
When `F` is continuous and vanishes on `[A, ∞)` with `A ≤ log p`, `continuumTower_reflection_cholesky`
retains `(1 − p^{−1/2}) ‖F‖₂²`, improving the required diagonal compensation from `log p · ‖F‖₂²`
(`continuumPrimeTower_compensated_nonneg`) to `(log p / √p) ∫_0^{log p} F(x)² dx`. -/
theorem continuumPrimeTower_zero_ge_neg_div_sqrt {F : ℝ → ℝ} (hF_cont : Continuous F)
    {A : ℝ} (hF_supp : ∀ x, A ≤ x → F x = 0) {p : ℕ} (hp : p.Prime)
    (hlog : A ≤ Real.log p) :
    -(Real.log p / Real.sqrt p) * (∫ x in (0 : ℝ)..Real.log p, F x ^ 2) ≤
      continuumPrimeTower F p 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hL : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hsupp0 : ∀ x, ((0 + 1 : ℕ) : ℝ) * Real.log p ≤ x → F x = 0 := fun x hx => by
    simp only [zero_add, Nat.cast_one, one_mul] at hx
    exact hF_supp x (hlog.trans hx)
  set r : ℝ := (p : ℝ) ^ (-(1 / 2 : ℝ))
  have hr_eq : r = 1 / Real.sqrt p := by
    dsimp [r]
    rw [Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow, one_div]
  have hr0 : 0 ≤ r := by rw [hr_eq]; positivity
  have hchol := continuumTower_reflection_cholesky hF_cont (r := r) hL hsupp0
  have htail0 : ∀ θ : ℝ, continuumTowerTail F r (Real.log p) 0 0 θ = F θ := fun θ => by
    simp [continuumTowerTail, kmsTail]
  simp only [htail0, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero] at hchol
  have hmass_eq : continuumTowerMass F (Real.log p) 0 = ∫ x in (0 : ℝ)..Real.log p, F x ^ 2 := by
    simp [continuumTowerMass]
  have href_nonneg : 0 ≤ (r / 2) * ∫ θ in (0 : ℝ)..Real.log p, (F θ - F (Real.log p - θ)) ^ 2 :=
    mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hL fun _ _ => sq_nonneg _)
  have h2R_sub : -r * (∫ x in (0 : ℝ)..Real.log p, F x ^ 2) ≤
      2 * continuumTowerRatio F r (Real.log p) 0 -
        continuumTowerCrossing F r (Real.log p) 0 := by
    rw [hmass_eq] at hchol
    linarith
  rw [continuumPrimeTower_eq hp hsupp0]
  have hcoeff : Real.log p * (-r * ∫ x in (0 : ℝ)..Real.log p, F x ^ 2) =
      -(Real.log p / Real.sqrt p) * ∫ x in (0 : ℝ)..Real.log p, F x ^ 2 := by
    rw [hr_eq]; ring
  exact hcoeff ▸ mul_le_mul_of_nonneg_left h2R_sub hL

/-- For a continuous profile `F` vanishing on `[A, ∞)`, the `L²` integral over `[0, B]` equals
`∫_0^A F(x)² dx` for every `B ≥ A`. -/
theorem integral_sq_eq_of_le {F : ℝ → ℝ} (hF_cont : Continuous F) {A B : ℝ}
    (hF_supp : ∀ x, A ≤ x → F x = 0) (hAB : A ≤ B) :
    (∫ x in (0 : ℝ)..B, F x ^ 2) = ∫ x in (0 : ℝ)..A, F x ^ 2 := by
  have hcont2 : Continuous (fun x => F x ^ 2) := hF_cont.pow 2
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont2.intervalIntegrable 0 A) (hcont2.intervalIntegrable A B)]
  have hzero : (∫ x in A..B, F x ^ 2) = 0 := by
    calc (∫ x in A..B, F x ^ 2)
        = ∫ _x in A..B, (0 : ℝ) := by
          refine intervalIntegral.integral_congr fun x hx => ?_
          rw [Set.uIcc_of_le hAB] at hx
          rw [hF_supp x hx.1, zero_pow two_ne_zero]
      _ = 0 := by simp
  rw [hzero, add_zero]

/-- When `A ≤ log p` and `F` vanishes on `[A, ∞)` (`A ≥ 0`), all `k ≥ 2` prime-power terms and all
same-side correlations of `continuumPrimeTower F p N` vanish identically, so
`continuumPrimeTower F p N = continuumPrimeTower F p 0` for every truncation `N : ℕ`. -/
theorem continuumPrimeTower_eq_zero_trunc_of_le_log {F : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hF_supp : ∀ x, A ≤ x → F x = 0) {p : ℕ} (hlog : A ≤ Real.log p) (N : ℕ) :
    continuumPrimeTower F p N = continuumPrimeTower F p 0 := by
  have hL : 0 ≤ Real.log p := hA.trans hlog
  unfold continuumPrimeTower
  have hsub : (Icc 1 (2 * 0 + 1) : Finset ℕ) ⊆ Icc 1 (2 * N + 1) :=
    Finset.Icc_subset_Icc_right (by omega)
  have hvanish : ∀ k ∈ Icc 1 (2 * N + 1), k ∉ (Icc 1 (2 * 0 + 1) : Finset ℕ) →
      ArithmeticFunction.vonMangoldt (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        (2 * (∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p,
          F x * F (x + (k : ℝ) * Real.log p)) -
          ∫ x in (0 : ℝ)..(k : ℝ) * Real.log p,
            F x * F ((k : ℝ) * Real.log p - x)) = 0 := by
    intro k hk hnot
    have hk2 : 2 ≤ k := by
      simp only [Finset.mem_Icc, Nat.mul_zero, zero_add] at hk hnot
      omega
    have hkR2 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hNL : 0 ≤ ((N + 1 : ℕ) : ℝ) * Real.log p := mul_nonneg (Nat.cast_nonneg _) hL
    have hi1 : (∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p,
        F x * F (x + (k : ℝ) * Real.log p)) = 0 := by
      calc (∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p,
            F x * F (x + (k : ℝ) * Real.log p))
          = ∫ _x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p, (0 : ℝ) := by
            refine intervalIntegral.integral_congr fun x hx => ?_
            rw [Set.uIcc_of_le hNL] at hx
            rw [hF_supp (x + (k : ℝ) * Real.log p) (by nlinarith [hx.1]), mul_zero]
        _ = 0 := by simp
    have hi2 : (∫ x in (0 : ℝ)..(k : ℝ) * Real.log p,
        F x * F ((k : ℝ) * Real.log p - x)) = 0 := by
      calc (∫ x in (0 : ℝ)..(k : ℝ) * Real.log p,
            F x * F ((k : ℝ) * Real.log p - x))
          = ∫ _x in (0 : ℝ)..(k : ℝ) * Real.log p, (0 : ℝ) := by
            refine intervalIntegral.integral_congr fun x _ => ?_
            rcases le_or_gt A x with hxA | hxA
            · rw [hF_supp x hxA, zero_mul]
            · rw [hF_supp ((k : ℝ) * Real.log p - x) (by nlinarith), mul_zero]
        _ = 0 := by simp
    rw [hi1, hi2]
    ring
  rw [← Finset.sum_subset hsub hvanish]
  simp only [Nat.mul_zero, zero_add, Finset.Icc_self, Finset.sum_singleton, pow_one,
    Nat.cast_one, one_mul]
  have h1N : (∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p, F x * F (x + Real.log p)) = 0 := by
    have hNL : 0 ≤ ((N + 1 : ℕ) : ℝ) * Real.log p := mul_nonneg (Nat.cast_nonneg _) hL
    calc (∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p, F x * F (x + Real.log p))
        = ∫ _x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p, (0 : ℝ) := by
          refine intervalIntegral.integral_congr fun x hx => ?_
          rw [Set.uIcc_of_le hNL] at hx
          rw [hF_supp (x + Real.log p) (by linarith [hx.1]), mul_zero]
      _ = 0 := by simp
  have h10 : (∫ x in (0 : ℝ)..Real.log p, F x * F (x + Real.log p)) = 0 := by
    calc (∫ x in (0 : ℝ)..Real.log p, F x * F (x + Real.log p))
        = ∫ _x in (0 : ℝ)..Real.log p, (0 : ℝ) := by
          refine intervalIntegral.integral_congr fun x hx => ?_
          rw [Set.uIcc_of_le hL] at hx
          rw [hF_supp (x + Real.log p) (by linarith [hx.1]), mul_zero]
      _ = 0 := by simp
  rw [h1N, h10]

/-- **Dyadic Chebyshev square-root prime sum bound.**
For every `M : ℕ`, `∑_{p ≤ M, p prime} log p / √p ≤ 10 √M`. -/
theorem sum_primes_log_div_sqrt_le_ten_sqrt (M : ℕ) :
    ∑ p ∈ (Icc 1 M).filter Nat.Prime, Real.log p / Real.sqrt p ≤ 10 * Real.sqrt M := by
  rcases lt_or_ge M 2 with hM2 | hM2
  · have hemp : (Icc 1 M).filter Nat.Prime = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and]
      intro hp
      have hp1 : p = 1 := by omega
      rw [hp1]
      exact Nat.not_prime_one
    rw [hemp, Finset.sum_empty]
    positivity
  set P := (Icc 1 M).filter Nat.Prime
  set L := Nat.log 2 M
  have hgeom : ∀ k : ℕ,
      ∑ j ∈ range (k + 1), (Real.sqrt 2) ^ j ≤ (2 + Real.sqrt 2) * (Real.sqrt 2) ^ k := by
    intro k
    induction k with
    | zero =>
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one]
      linarith [Real.sqrt_nonneg 2]
    | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ']
      have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      have hstep : (2 + Real.sqrt 2) * (Real.sqrt 2) ^ k +
          Real.sqrt 2 * (Real.sqrt 2) ^ k =
            (2 + Real.sqrt 2) * (Real.sqrt 2 * (Real.sqrt 2) ^ k) := by
        linear_combination -(Real.sqrt 2) ^ k * hsq2
      linarith
  have hpart : P = (range (L + 1)).biUnion (fun j => P.filter (fun p => Nat.log 2 p = j)) := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    constructor
    · intro hpP
      refine ⟨Nat.log 2 p, ?_, hpP, rfl⟩
      have hpM : p ≤ M := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpP).1).2
      exact Nat.lt_succ_of_le (Nat.log_mono_right hpM)
    · rintro ⟨_, _, hpP, _⟩
      exact hpP
  have hdisj : Set.PairwiseDisjoint ((Finset.range (L + 1) : Finset ℕ) : Set ℕ)
      (fun j => P.filter (fun p => Nat.log 2 p = j)) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun p hpi hpj => hij ?_
    rw [← (Finset.mem_filter.mp hpi).2, (Finset.mem_filter.mp hpj).2]
  have hlog4 : Real.log 4 ≤ 7 / 5 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have hfiber : ∀ j ∈ range (L + 1),
      ∑ p ∈ P.filter (fun p => Nat.log 2 p = j), Real.log p / Real.sqrt p ≤
        (14 / 5 : ℝ) * (Real.sqrt 2) ^ j := by
    intro j _
    have hsqrt_pow : (Real.sqrt 2) ^ j = Real.sqrt ((2 ^ j : ℕ) : ℝ) := by
      symm
      calc Real.sqrt ((2 ^ j : ℕ) : ℝ)
          = Real.sqrt (((Real.sqrt 2) ^ 2) ^ j) := by
            rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Nat.cast_pow, Nat.cast_ofNat]
        _ = Real.sqrt (((Real.sqrt 2) ^ j) ^ 2) := by rw [← pow_mul, mul_comm 2 j, pow_mul]
        _ = (Real.sqrt 2) ^ j := Real.sqrt_sq (by positivity)
    have hsqrt_pos : 0 < (Real.sqrt 2) ^ j := by positivity
    have hterm : ∀ p ∈ P.filter (fun p => Nat.log 2 p = j),
        Real.log p / Real.sqrt p ≤ Real.log p / (Real.sqrt 2) ^ j := by
      intro p hpj
      obtain ⟨hpP, hlogp⟩ := Finset.mem_filter.mp hpj
      have hpp : p.Prime := (Finset.mem_filter.mp hpP).2
      have h2j_le : 2 ^ j ≤ p := by
        rw [← hlogp]
        exact Nat.pow_log_le_self 2 hpp.ne_zero
      have hsqrt_le : (Real.sqrt 2) ^ j ≤ Real.sqrt p := by
        rw [hsqrt_pow]
        exact Real.sqrt_le_sqrt (by exact_mod_cast h2j_le)
      exact div_le_div_of_nonneg_left
        (Real.log_nonneg (by exact_mod_cast hpp.one_le)) hsqrt_pos hsqrt_le
    have hsub_dyad : P.filter (fun p => Nat.log 2 p = j) ⊆
        (Ioc 0 (2 ^ (j + 1))).filter Nat.Prime := by
      intro p hpj
      obtain ⟨hpP, hlogp⟩ := Finset.mem_filter.mp hpj
      have hpp : p.Prime := (Finset.mem_filter.mp hpP).2
      have hp_lt : p < 2 ^ (j + 1) := by
        rw [← hlogp]
        exact Nat.lt_pow_succ_log_self (by omega : 1 < 2) p
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpp.pos, hp_lt.le⟩, hpp⟩
    have htheta : ∑ p ∈ P.filter (fun p => Nat.log 2 p = j), Real.log p ≤
        (14 / 5 : ℝ) * (2 : ℝ) ^ j := by
      calc ∑ p ∈ P.filter (fun p => Nat.log 2 p = j), Real.log p
          ≤ ∑ p ∈ (Ioc 0 (2 ^ (j + 1))).filter Nat.Prime, Real.log p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_dyad fun p hp _ =>
              Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
        _ = Chebyshev.theta ((2 ^ (j + 1) : ℕ) : ℝ) := by
            rw [Chebyshev.theta, Nat.floor_natCast]
        _ ≤ Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ) :=
            Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
        _ ≤ (7 / 5 : ℝ) * ((2 ^ (j + 1) : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hlog4 (Nat.cast_nonneg _)
        _ = (14 / 5 : ℝ) * (2 : ℝ) ^ j := by
            push_cast; rw [pow_succ]; ring
    have h2_eq : (2 : ℝ) ^ j = (Real.sqrt 2) ^ j * (Real.sqrt 2) ^ j := by
      rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
    calc ∑ p ∈ P.filter (fun p => Nat.log 2 p = j), Real.log p / Real.sqrt p
        ≤ ∑ p ∈ P.filter (fun p => Nat.log 2 p = j), Real.log p / (Real.sqrt 2) ^ j :=
          Finset.sum_le_sum hterm
      _ = (∑ p ∈ P.filter (fun p => Nat.log 2 p = j), Real.log p) / (Real.sqrt 2) ^ j :=
          (Finset.sum_div _ _ _).symm
      _ ≤ ((14 / 5 : ℝ) * (2 : ℝ) ^ j) / (Real.sqrt 2) ^ j :=
          div_le_div_of_nonneg_right htheta hsqrt_pos.le
      _ = (14 / 5 : ℝ) * (Real.sqrt 2) ^ j := by
          rw [h2_eq]
          field_simp
  have hsqrt2_lt : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2 : ℝ) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2L_le : (Real.sqrt 2) ^ L ≤ Real.sqrt M := by
    have hsqrt_L : (Real.sqrt 2) ^ L = Real.sqrt ((2 ^ L : ℕ) : ℝ) := by
      symm
      calc Real.sqrt ((2 ^ L : ℕ) : ℝ)
          = Real.sqrt (((Real.sqrt 2) ^ 2) ^ L) := by
            rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Nat.cast_pow, Nat.cast_ofNat]
        _ = Real.sqrt (((Real.sqrt 2) ^ L) ^ 2) := by rw [← pow_mul, mul_comm 2 L, pow_mul]
        _ = (Real.sqrt 2) ^ L := Real.sqrt_sq (by positivity)
    rw [hsqrt_L]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.pow_log_le_self 2 (by omega : M ≠ 0))
  calc ∑ p ∈ P, Real.log p / Real.sqrt p
      = ∑ j ∈ range (L + 1),
          ∑ p ∈ P.filter (fun p => Nat.log 2 p = j), Real.log p / Real.sqrt p := by
        conv_lhs => rw [hpart]
        exact Finset.sum_biUnion hdisj
    _ ≤ ∑ j ∈ range (L + 1), (14 / 5 : ℝ) * (Real.sqrt 2) ^ j := Finset.sum_le_sum hfiber
    _ = (14 / 5 : ℝ) * ∑ j ∈ range (L + 1), (Real.sqrt 2) ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ (14 / 5 : ℝ) * ((2 + Real.sqrt 2) * (Real.sqrt 2) ^ L) :=
        mul_le_mul_of_nonneg_left (hgeom L) (by norm_num)
    _ ≤ (14 / 5 : ℝ) * ((2 + 3 / 2) * Real.sqrt M) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul (by linarith) h2L_le (by positivity) (by norm_num)
    _ ≤ 10 * Real.sqrt M := by
        nlinarith [Real.sqrt_nonneg M]

/-- **`S`-uniform all-prime continuum shared-payment theorem (`O(e^A)` across arbitrary finite prime sets).**
For any continuous profile `F : ℝ → ℝ` vanishing on `[A, ∞)` (`A ≥ 0`), **every** finite set of
primes `S : Finset ℕ` (with zero bound on `#S` or `max S`) and **every** truncation schedule
`N : ℕ → ℕ` satisfying `A ≤ (N p + 1) log p` on `S` obey
`∑_{p ∈ S} continuumPrimeTower F p (N p) ≥ -12 e^A ∫_0^A F(x)² dx`. -/
theorem sum_continuumPrimeTower_ge_neg_twelve_exp {F : ℝ → ℝ} (hF_cont : Continuous F)
    {A : ℝ} (hA : 0 ≤ A) (hF_supp : ∀ x, A ≤ x → F x = 0)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {N : ℕ → ℕ} (hN : ∀ p ∈ S, A ≤ ((N p + 1 : ℕ) : ℝ) * Real.log p) :
    -12 * Real.exp A * (∫ x in (0 : ℝ)..A, F x ^ 2) ≤
      ∑ p ∈ S, continuumPrimeTower F p (N p) := by
  set M_int : ℝ := ∫ x in (0 : ℝ)..A, F x ^ 2
  have hM_nonneg : 0 ≤ M_int :=
    intervalIntegral.integral_nonneg hA fun _ _ => sq_nonneg _
  set w : ℕ → ℝ := fun p =>
    if 2 * A ≤ Real.log p then 0
    else if A ≤ Real.log p then Real.log p / Real.sqrt p
    else Real.log p
  have hpt : ∀ p ∈ S, -w p * M_int ≤ continuumPrimeTower F p (N p) := by
    intro p hpS
    have hpp : p.Prime := hS p hpS
    dsimp only [w]
    split_ifs with h2A h1A
    · rw [continuumPrimeTower_eq_zero_trunc_of_le_log hA hF_supp (by linarith) (N p),
        continuumPrimeTower_eq_zero_of_two_mul_le_log hA hF_supp hpp h2A]
      ring_nf
      exact le_rfl
    · rw [continuumPrimeTower_eq_zero_trunc_of_le_log hA hF_supp h1A (N p)]
      have h0 := continuumPrimeTower_zero_ge_neg_div_sqrt hF_cont hF_supp hpp h1A
      rwa [integral_sq_eq_of_le hF_cont hF_supp h1A] at h0
    · have hNL_ge : A ≤ ((N p + 1 : ℕ) : ℝ) * Real.log p := hN p hpS
      have hsuppN : ∀ x, ((N p + 1 : ℕ) : ℝ) * Real.log p ≤ x → F x = 0 :=
        fun x hx => hF_supp x (hNL_ge.trans hx)
      have hcomp := continuumPrimeTower_compensated_nonneg hF_cont hpp hsuppN
      have hmass : continuumTowerMass F (Real.log p) (N p) = M_int := by
        unfold continuumTowerMass
        exact integral_sq_eq_of_le hF_cont hF_supp hNL_ge
      rw [hmass] at hcomp
      linarith
  have hsum_ge : -(∑ p ∈ S, w p) * M_int ≤ ∑ p ∈ S, continuumPrimeTower F p (N p) := by
    calc -(∑ p ∈ S, w p) * M_int
        = ∑ p ∈ S, (-w p * M_int) := by
          rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ ∑ p ∈ S, continuumPrimeTower F p (N p) := Finset.sum_le_sum hpt
  suffices hw_le : ∑ p ∈ S, w p ≤ 12 * Real.exp A by
    nlinarith
  -- Split `S` at `A ≤ log p`
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => A ≤ Real.log (p : ℝ))]
  -- Low primes (`log p < A`) have `p ≤ ⌊e^A⌋` and carry `w p = log p`
  have hlow : ∑ p ∈ S.filter (fun p : ℕ => ¬ A ≤ Real.log (p : ℝ)), w p ≤ 2 * Real.exp A := by
    have hrew : ∀ p ∈ S.filter (fun p : ℕ => ¬ A ≤ Real.log (p : ℝ)), w p = Real.log p := by
      intro p hp
      have hnot : ¬ A ≤ Real.log (p : ℝ) := (Finset.mem_filter.mp hp).2
      have hnot2 : ¬ 2 * A ≤ Real.log (p : ℝ) := fun h2 => hnot (by linarith)
      dsimp only [w]
      rw [if_neg hnot2, if_neg hnot]
    have hsub : S.filter (fun p : ℕ => ¬ A ≤ Real.log (p : ℝ)) ⊆
        (Ioc 0 ⌊Real.exp A⌋₊).filter Nat.Prime := by
      intro p hp
      obtain ⟨hpS, hnot⟩ := Finset.mem_filter.mp hp
      push Not at hnot
      have hpp := hS p hpS
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hpe : (p : ℝ) < Real.exp A := (Real.log_lt_iff_lt_exp hp0).mp hnot
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hpp.pos, Nat.le_floor hpe.le⟩, hpp⟩
    have hlog4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_lt_d9]
    calc ∑ p ∈ S.filter (fun p : ℕ => ¬ A ≤ Real.log (p : ℝ)), w p
        = ∑ p ∈ S.filter (fun p : ℕ => ¬ A ≤ Real.log (p : ℝ)), Real.log p :=
          Finset.sum_congr rfl hrew
      _ ≤ ∑ p ∈ (Ioc 0 ⌊Real.exp A⌋₊).filter Nat.Prime, Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
            Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
      _ = Chebyshev.theta (Real.exp A) := by rw [Chebyshev.theta]
      _ ≤ Real.log 4 * Real.exp A := Chebyshev.theta_le_log4_mul_x (Real.exp_pos A).le
      _ ≤ 2 * Real.exp A := mul_le_mul_of_nonneg_right hlog4 (Real.exp_pos A).le
  -- Middle/high primes (`A ≤ log p`) vanish above `2 A` and carry `log p / √p` on `[e^A, e^{2A})`
  have hmid : ∑ p ∈ S.filter (fun p : ℕ => A ≤ Real.log (p : ℝ)), w p ≤ 10 * Real.exp A := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (S.filter (fun p : ℕ => A ≤ Real.log (p : ℝ))) (fun p : ℕ => 2 * A ≤ Real.log (p : ℝ))]
    have hz : ∑ p ∈ (S.filter (fun p : ℕ => A ≤ Real.log (p : ℝ))).filter
        (fun p : ℕ => 2 * A ≤ Real.log (p : ℝ)), w p = 0 :=
      Finset.sum_eq_zero fun p hp => by
        dsimp only [w]
        rw [if_pos (Finset.mem_filter.mp hp).2]
    rw [hz, zero_add]
    set S_mid := (S.filter (fun p : ℕ => A ≤ Real.log (p : ℝ))).filter
      (fun p : ℕ => ¬ 2 * A ≤ Real.log (p : ℝ))
    have hrew : ∀ p ∈ S_mid, w p = Real.log p / Real.sqrt p := by
      intro p hp
      obtain ⟨hp1, hnot2⟩ := Finset.mem_filter.mp hp
      dsimp only [w]
      rw [if_neg hnot2, if_pos (Finset.mem_filter.mp hp1).2]
    have hsub : S_mid ⊆ (Icc 1 ⌊Real.exp (2 * A)⌋₊).filter Nat.Prime := by
      intro p hp
      obtain ⟨hp1, hnot2⟩ := Finset.mem_filter.mp hp
      push Not at hnot2
      have hpp := hS p (Finset.mem_filter.mp hp1).1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hpe : (p : ℝ) < Real.exp (2 * A) := (Real.log_lt_iff_lt_exp hp0).mp hnot2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpp.one_le, Nat.le_floor hpe.le⟩, hpp⟩
    have hsqrt_exp : Real.sqrt (⌊Real.exp (2 * A)⌋₊ : ℝ) ≤ Real.exp A := by
      calc Real.sqrt (⌊Real.exp (2 * A)⌋₊ : ℝ)
          ≤ Real.sqrt (Real.exp (2 * A)) :=
            Real.sqrt_le_sqrt (Nat.floor_le (Real.exp_pos _).le)
        _ = Real.sqrt (Real.exp A ^ 2) := by
            rw [← Real.exp_nat_mul]; push_cast; rfl
        _ = Real.exp A := Real.sqrt_sq (Real.exp_pos A).le
    calc ∑ p ∈ S_mid, w p
        = ∑ p ∈ S_mid, Real.log p / Real.sqrt p := Finset.sum_congr rfl hrew
      _ ≤ ∑ p ∈ (Icc 1 ⌊Real.exp (2 * A)⌋₊).filter Nat.Prime, Real.log p / Real.sqrt p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
            div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
              (Real.sqrt_nonneg _)
      _ ≤ 10 * Real.sqrt (⌊Real.exp (2 * A)⌋₊ : ℝ) :=
          sum_primes_log_div_sqrt_le_ten_sqrt _
      _ ≤ 10 * Real.exp A := mul_le_mul_of_nonneg_left hsqrt_exp (by norm_num)
  linarith

/-- **Shifted-pair selectivity: failure of top-octave Archimedean payment at `|a| ≥ 1`.**
Whereas `ζ(s)` satisfies `sum_towerOddPrimeSide_add_archDiag_nonneg_of_top_octave` across arbitrary
finite prime sets on the top octave, for `ζ(s − a)ζ(s + a)` with `1 ≤ |a|` even a single prime point
mass `q = δ_p` at `X = p` (`p > X / 2`) satisfies
`shiftedTowerOddPrimeSide a δ_p p p 1 + archReflectedDiagWeight p < 0`. -/
theorem shiftedTowerOddPrimeSide_point_top_octave_lt_neg_arch {a : ℝ} (ha : 1 ≤ |a|)
    {p : ℕ} (hp : p.Prime) :
    shiftedTowerOddPrimeSide a (fun n => if n = p then 1 else 0) p p 1 +
      archReflectedDiagWeight p < 0 := by
  set q : ℕ → ℝ := fun n => if n = p then 1 else 0
  have hq : ∀ n, p < n → q n = 0 := fun n hn => if_neg (by omega)
  have hK : ∀ i, 1 < i → q (p ^ i) = 0 := fun i hi => by
    have hgt : p < p ^ i := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ i := Nat.pow_lt_pow_right hp.one_lt hi
    exact if_neg hgt.ne'
  rw [shiftedTowerOddPrimeSide_eq a q hq hp hK]
  have hp1_ne : (1 : ℕ) ≠ p := hp.one_lt.ne
  have hq1 : q 1 = 0 := if_neg hp1_ne
  have htoe0 : ∀ (b : ℝ) (a' : ℕ), shiftedCosetToeplitz b q p p 2 a' = 0 := fun b a' => by
    unfold shiftedCosetToeplitz
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hinner0 : ∑ i ∈ range (Nat.log p p + 1), q (p ^ i * a') * q (p ^ (i + k) * a') = 0 :=
      Finset.sum_eq_zero fun i _ => by
        dsimp only [q]
        by_cases h1 : p ^ i * a' = p
        · have h2 : p < p ^ (i + k) * a' := by
            calc p = p ^ i * a' := h1.symm
              _ < p ^ (i + k) * a' := by
                have ha'0 : 0 < a' := by
                  by_contra h0; push Not at h0
                  have ha'z : a' = 0 := by omega
                  rw [ha'z, mul_zero] at h1
                  exact hp.ne_zero h1.symm
                exact Nat.mul_lt_mul_of_pos_right
                  (Nat.pow_lt_pow_right hp.one_lt (by omega)) ha'0
          rw [if_neg (by omega : p ^ (i + k) * a' ≠ p), mul_zero]
        · rw [if_neg h1, zero_mul]
    rw [hinner0, mul_zero]
  have hmellin : ∀ b : ℝ, shiftedTowerMellin b q p 1 = (p : ℝ) ^ (b - 1 / 2) := fun b => by
    unfold shiftedTowerMellin
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [q, hp1_ne]
  simp only [htoe0, add_zero, Finset.sum_const_zero, mul_zero, hq1, hmellin, zero_pow two_ne_zero,
    sub_zero, zero_sub]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsq_eq : ((p : ℝ) ^ (a - 1 / 2)) ^ 2 + ((p : ℝ) ^ (-a - 1 / 2)) ^ 2 =
      (p : ℝ) ^ (-(1 : ℝ)) * ((p : ℝ) ^ (2 * (1 : ℝ) * a) + (p : ℝ) ^ (-(2 * (1 : ℝ) * a))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
      ← Real.rpow_mul hp0.le, mul_add, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
    push_cast
    congr 1 <;> congr 1 <;> ring
  have hsel := archReflectedDiagWeight_lt_shiftedPrimeDiag_of_one_le ha hp le_rfl
  rw [pow_one] at hsel
  push_cast at hsel
  have hrew : Real.log p * (-((p : ℝ) ^ (a - 1 / 2)) ^ 2 - ((p : ℝ) ^ (-a - 1 / 2)) ^ 2) =
      -(Real.log p * (p : ℝ) ^ (-(1 : ℝ)) *
        ((p : ℝ) ^ (2 * (1 : ℝ) * a) + (p : ℝ) ^ (-(2 * (1 : ℝ) * a)))) := by
    linear_combination -Real.log p * hsq_eq
  rw [hrew, add_comm, ← sub_eq_add_neg, sub_neg]
  exact hsel

end

end GaloisForLFunctions.ArithmeticOrientationTheory
