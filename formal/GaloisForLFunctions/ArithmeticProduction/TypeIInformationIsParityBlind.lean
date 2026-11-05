import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheLiouvilleTwinIsARatioOfHorizonTorsions
import GaloisForLFunctions.RHTower.LiouvilleSummatoryRH
import GaloisForLFunctions.RHTower.MontgomerySpacedDetectionCore
import GaloisForLFunctions.RHTower.BaezDuarteLogDualEnergy
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovMoebius

/-!
# The Type I parity barrier

A level-`D` divisor sum is `W(n) = Σ_{d ∈ D, d ∣ n} c_d`.  Its correlation with the Liouville function is computed
exactly, because `λ` is completely multiplicative:

  `Σ_{n ≤ N} λ(n) W(n) = Σ_{d ∈ D} c_d λ(d) L(⌊N/d⌋)`, `L(M) = Σ_{m ≤ M} λ(m)`
  (`sum_lam_mul_divisorSum`).

So Type I information sees `λ` only through `L` at the scales `N/d`.  On the other hand `Σ_{n ≤ N} λ(n)Λ(n) = 2ψ(√N) − ψ(N)`.
Testing `Λ − W` against the sign `λ` gives the barrier

  `ψ(N) − 2ψ(√N) − Σ_{d ∈ D} |c_d| |L(⌊N/d⌋)| ≤ Σ_{n ≤ N} |Λ(n) − W(n)|`
  (`psi_sub_le_sum_abs_sub_divisorSum`).

With `L(M) ≪ M/log^k M`, proved here from the Vinogradov–Korobov bound for `M` through
`L(N) = Σ_{j ≤ √N} M(⌊N/j²⌋)`, every divisor sum of level `N^{1-δ}` with coefficients `≪ log N` stays at `L¹`-distance
`≥ (1 − ε)N` from `Λ` (`typeI_parity_barrier`).  This is Selberg's parity barrier as an inequality, and it reaches
every level below `N^{1−o(1)}`: the identity `Λ = −Σ_{d ∣ n} μ(d) log d` has level `N`, coefficients `≤ log N`, and distance `0`,
so the range of levels is sharp.
-/

noncomputable section

open Finset Filter Topology Asymptotics
open ArithmeticFunction (vonMangoldt cardFactors)

namespace GaloisForLFunctions.ArithmeticProduction

open ArithmeticOfSquareRootPrecision

/-- The real Liouville function. -/
abbrev lam (n : ℕ) : ℝ := _root_.RHTower.liouvilleR n

theorem lam_mul (m n : ℕ) : lam (m * n) = lam m * lam n := by
  simp [lam, _root_.RHTower.liouvilleR, ArithmeticFunction.liouville_apply_mul]

theorem abs_lam_le_one (n : ℕ) : |lam n| ≤ 1 := _root_.RHTower.abs_liouville_le_one n

theorem lam_eq {n : ℕ} (hn : n ≠ 0) : lam n = (-1) ^ cardFactors n := by
  simp [lam, _root_.RHTower.liouvilleR, ArithmeticFunction.liouville_apply hn]

/-- The Liouville summatory function on the integers. -/
def liouvilleCount (N : ℕ) : ℝ := ∑ k ∈ Icc 1 N, lam k

/-- A level-`D` divisor sum. -/
def divisorSum (D : Finset ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ := ∑ d ∈ D.filter (· ∣ n), c d

/-- Multiples of `d` in `[1, N]` are `d k`, `k ≤ N/d`. -/
theorem sum_Icc_ite_dvd {d : ℕ} (hd : 0 < d) (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, (if d ∣ n then f n else 0) = ∑ k ∈ Icc 1 (N / d), f (d * k) := by
  rw [← sum_filter]
  symm
  refine sum_nbij' (fun k => d * k) (fun n => n / d) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨h1, h2⟩ := mem_Icc.mp hk
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd h1, ?_⟩, Dvd.intro k rfl⟩
    calc d * k ≤ d * (N / d) := Nat.mul_le_mul_left d h2
      _ ≤ N := Nat.mul_div_le N d
  · intro n hn
    obtain ⟨hn1, hdn⟩ := mem_filter.mp hn
    obtain ⟨h1, h2⟩ := mem_Icc.mp hn1
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd h1 hdn) hd, Nat.div_le_div_right h2⟩
  · intro k _
    exact Nat.mul_div_cancel_left k hd
  · intro n hn
    exact Nat.mul_div_cancel' (mem_filter.mp hn).2
  · intro k _
    rfl

/-- **Type I sees `λ` only through `L`.** -/
theorem sum_lam_mul_divisorSum {D : Finset ℕ} (hD : ∀ d ∈ D, 0 < d) (c : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, lam n * divisorSum D c n = ∑ d ∈ D, c d * lam d * liouvilleCount (N / d) := by
  unfold divisorSum
  simp_rw [sum_filter, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have hite : ∀ n, lam n * (if d ∣ n then c d else 0) = if d ∣ n then c d * lam n else 0 := by
    intro n
    split_ifs <;> ring
  simp_rw [hite]
  rw [sum_Icc_ite_dvd (hD d hd), liouvilleCount, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [lam_mul]
  ring

/-- `Σ_{n ≤ N} λ(n)Λ(n) = 2ψ(√N) − ψ(N)`. -/
theorem sum_lam_mul_vonMangoldt (N : ℕ) :
    ∑ n ∈ Icc 1 N, lam n * vonMangoldt n =
      2 * Chebyshev.psi (Nat.sqrt N) - Chebyshev.psi N := by
  rw [← partialSum_liouvilleWeight_eq, partialSum, Nat.floor_natCast]
  have hIoc : Ioc 0 N = Icc 1 N := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  rw [hIoc]
  refine sum_congr rfl fun n hn => ?_
  rw [lam_eq (by have := (mem_Icc.mp hn).1; omega)]
  rfl

/-- **The Type I barrier.** -/
theorem psi_sub_le_sum_abs_sub_divisorSum {D : Finset ℕ} (hD : ∀ d ∈ D, 0 < d) (c : ℕ → ℝ) (N : ℕ) :
    Chebyshev.psi N - 2 * Chebyshev.psi (Nat.sqrt N) - ∑ d ∈ D, |c d| * |liouvilleCount (N / d)| ≤
      ∑ n ∈ Icc 1 N, |(vonMangoldt n : ℝ) - divisorSum D c n| := by
  have hsplit : ∑ n ∈ Icc 1 N, lam n * ((vonMangoldt n : ℝ) - divisorSum D c n) =
      (2 * Chebyshev.psi (Nat.sqrt N) - Chebyshev.psi N) -
        ∑ d ∈ D, c d * lam d * liouvilleCount (N / d) := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib, sum_lam_mul_vonMangoldt, sum_lam_mul_divisorSum hD]
  have hup : |∑ n ∈ Icc 1 N, lam n * ((vonMangoldt n : ℝ) - divisorSum D c n)| ≤
      ∑ n ∈ Icc 1 N, |(vonMangoldt n : ℝ) - divisorSum D c n| := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_lam_le_one n)
  have hW : |∑ d ∈ D, c d * lam d * liouvilleCount (N / d)| ≤
      ∑ d ∈ D, |c d| * |liouvilleCount (N / d)| := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg _) (abs_lam_le_one d)) (abs_nonneg _)
  rw [hsplit] at hup
  have h1 := neg_abs_le ((2 * Chebyshev.psi (Nat.sqrt N) - Chebyshev.psi N) -
    ∑ d ∈ D, c d * lam d * liouvilleCount (N / d))
  have h2 := neg_abs_le (∑ d ∈ D, c d * lam d * liouvilleCount (N / d))
  linarith

/-! ### A rate for the Liouville summatory function -/

/-- The Mertens function on the integers. -/
abbrev mertensCount (m : ℕ) : ℝ := _root_.RHTower.sourcePartialSum _root_.RHTower.moebiusR m

theorem abs_mertensCount_le (m : ℕ) : |mertensCount m| ≤ m := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hle : ∀ n ∈ Icc 1 m, |_root_.RHTower.moebiusR n| ≤ 1 := fun n _ => by
    unfold _root_.RHTower.moebiusR
    have := ArithmeticFunction.abs_moebius_le_one (n := n)
    exact_mod_cast this
  refine (sum_le_card_nsmul _ _ 1 hle).trans ?_
  simp

/-- `M(m) ≪ m/log^k m` from the Vinogradov–Korobov rate. -/
theorem exists_abs_mertensCount_le (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ m : ℕ in atTop, |mertensCount m| ≤ K * m / Real.log m ^ k := by
  obtain ⟨B, hB, hrate⟩ := _root_.RHTower.Sieve.exists_abs_sum_moebius_le_vk_rate
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = ((2 * k).factorial * 12 ^ (2 * k) : ℝ) := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  refine ⟨B * F, by positivity, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (hrate.and (_root_.RHTower.Sieve.eventually_vk_conditions one_pos 0))] with m hm
  obtain ⟨hm1, -, hL3, -, -, hLg2, -⟩ := hm
  rw [Nat.floor_natCast] at hm1
  have hL0 : 0 < Real.log (m : ℝ) := by linarith
  set s := _root_.RHTower.Sieve.vkSaving (m : ℝ) with hs
  have hsq : Real.sqrt (Real.log m) ≤ s := by
    rw [hs, _root_.RHTower.Sieve.vkSaving_eq]
    linarith
  have hs0 : 0 ≤ s := (Real.sqrt_nonneg _).trans hsq
  have hexp : _root_.RHTower.Sieve.vkKappa * _root_.RHTower.Sieve.vkScale (m : ℝ) / 24 = s / 12 := by
    rw [hs, _root_.RHTower.Sieve.vkSaving]
    ring
  rw [hexp] at hm1
  have hsum : ∑ n ∈ Finset.range (m + 1), (ArithmeticFunction.moebius n : ℝ) = mertensCount m := by
    have hrange : Finset.range (m + 1) = insert 0 (Icc 1 m) := by
      ext n
      simp only [Finset.mem_range, mem_insert, mem_Icc]
      omega
    rw [hrange, sum_insert (by simp)]
    simp [mertensCount, _root_.RHTower.sourcePartialSum, _root_.RHTower.moebiusR]
  rw [hsum] at hm1
  have hLk : Real.log m ^ k ≤ s ^ (2 * k) := by
    have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq (2 * k)
    rwa [pow_mul, Real.sq_sqrt hL0.le] at h1
  have hfact := Real.pow_div_factorial_le_exp (s / 12) (by positivity) (2 * k)
  have hfpos : (0 : ℝ) < (2 * k).factorial := by exact_mod_cast Nat.factorial_pos _
  have hsk : s ^ (2 * k) ≤ F * Real.exp (s / 12) := by
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at hfact
    rw [hF]
    calc s ^ (2 * k) ≤ Real.exp (s / 12) * (12 ^ (2 * k) * (2 * k).factorial) := hfact
      _ = _ := by ring
  have habs : Real.log m ^ k * Real.exp (-(s / 12)) ≤ F := by
    have hE := Real.exp_pos (-(s / 12))
    calc Real.log m ^ k * Real.exp (-(s / 12))
        ≤ (F * Real.exp (s / 12)) * Real.exp (-(s / 12)) :=
          mul_le_mul_of_nonneg_right (hLk.trans hsk) hE.le
      _ = F := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rw [le_div_iff₀ (pow_pos hL0 k)]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc |mertensCount m| * Real.log m ^ k
      ≤ (B * m * Real.exp (-(s / 12))) * Real.log m ^ k :=
        mul_le_mul_of_nonneg_right hm1 (pow_nonneg hL0.le k)
    _ = B * m * (Real.log m ^ k * Real.exp (-(s / 12))) := by ring
    _ ≤ B * m * F := mul_le_mul_of_nonneg_left habs (by positivity)
    _ = B * F * m := by ring

/-- `Σ_{d ≤ N, d = □} f(d) = Σ_{j ≤ √N} f(j²)`. -/
theorem sum_Icc_squareIndicatorR (N : ℕ) (f : ℕ → ℝ) :
    ∑ d ∈ Icc 1 N, _root_.RHTower.squareIndicatorR d * f d =
      ∑ j ∈ Icc 1 (Nat.sqrt N), f (j * j) := by
  classical
  have hfil : ∑ d ∈ Icc 1 N, _root_.RHTower.squareIndicatorR d * f d =
      ∑ d ∈ (Icc 1 N).filter IsSquare, f d := by
    rw [sum_filter]
    refine sum_congr rfl fun d _ => ?_
    by_cases h : IsSquare d <;> simp [_root_.RHTower.squareIndicatorR, h]
  rw [hfil]
  symm
  refine sum_nbij' (fun j => j * j) Nat.sqrt ?_ ?_ ?_ ?_ ?_
  · intro j hj
    obtain ⟨h1, h2⟩ := mem_Icc.mp hj
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos h1 h1, Nat.le_sqrt.mp h2⟩, ⟨j, rfl⟩⟩
  · intro d hd
    obtain ⟨hd1, r, rfl⟩ := mem_filter.mp hd
    obtain ⟨h1, h2⟩ := mem_Icc.mp hd1
    rw [Nat.sqrt_eq]
    refine mem_Icc.mpr ⟨Nat.pos_of_ne_zero ?_, Nat.le_sqrt.mpr h2⟩
    rintro rfl
    simp at h1
  · intro j _
    exact Nat.sqrt_eq j
  · intro d hd
    obtain ⟨-, r, rfl⟩ := mem_filter.mp hd
    show Nat.sqrt (r * r) * Nat.sqrt (r * r) = r * r
    rw [Nat.sqrt_eq]
  · intro j _
    rfl

/-- `L(N) = Σ_{j ≤ √N} M(⌊N/j²⌋)`. -/
theorem liouvilleCount_eq (N : ℕ) :
    liouvilleCount N = ∑ j ∈ Icc 1 (Nat.sqrt N), mertensCount (N / (j * j)) := by
  have h := _root_.RHTower.sourcePartialSum_liouvilleR_eq N
  have hL : liouvilleCount N = _root_.RHTower.sourcePartialSum _root_.RHTower.liouvilleR N := rfl
  rw [hL, h, _root_.RHTower.floorTransform]
  exact sum_Icc_squareIndicatorR N fun d => mertensCount (N / d)

/-- **`L(N) ≪ N/log^k N`.** -/
theorem exists_abs_liouvilleCount_le (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, |liouvilleCount N| ≤ K * N / Real.log N ^ k := by
  obtain ⟨K₀, hK₀, hM⟩ := exists_abs_mertensCount_le k
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hM
  refine ⟨2 * K₀ * 3 ^ k + 1, by positivity, ?_⟩
  have hsmall : ∀ᶠ x : ℝ in atTop, Real.log x ^ k ≤ x ^ ((1 : ℝ) / 8) := by
    have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (by norm_num : (0 : ℝ) < 1 / 8)).bound one_pos
    filter_upwards [h, eventually_gt_atTop (0 : ℝ), Real.tendsto_log_atTop.eventually_gt_atTop 0]
      with x hx hx0 hlog
    rw [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg hlog.le k), one_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
    exact hx
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hsmall,
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_gt_atTop 0),
    eventually_ge_atTop ((max m₀ 9 * max m₀ 9) * (max m₀ 9 * max m₀ 9))] with N hsm hlog hN
  set M := max m₀ 9 with hMdef
  have hM9 : 9 ≤ M := le_max_right _ _
  have hMm : m₀ ≤ M := le_max_left _ _
  set r := Nat.sqrt N with hr
  set J := Nat.sqrt r with hJ
  have hrM : M * M ≤ r := Nat.le_sqrt.mpr hN
  have hJM : M ≤ J := Nat.le_sqrt.mpr hrM
  have hJ2 : 2 ≤ J := by omega
  have hrm : M ≤ r := by nlinarith
  have hr3 : 3 ≤ r := by omega
  have hNr : N < (r + 1) * (r + 1) := Nat.lt_succ_sqrt N
  have hrJ : r < (J + 1) * (J + 1) := Nat.lt_succ_sqrt r
  have hJr : J ≤ r := Nat.sqrt_le_self r
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hN0 : (0 : ℝ) < N := by
    have h9 : 9 * 9 * (9 * 9) ≤ M * M * (M * M) :=
      Nat.mul_le_mul (Nat.mul_le_mul hM9 hM9) (Nat.mul_le_mul hM9 hM9)
    have : 0 < N := lt_of_lt_of_le (by norm_num) (h9.trans hN)
    exact_mod_cast this
  have hlogN : 0 < Real.log N := hlog
  -- `log N ≤ 3 log r`
  have hNr3 : (N : ℝ) ≤ (r : ℝ) ^ 3 := by
    have : N ≤ r ^ 3 := by
      have h1 : (r + 1) * (r + 1) ≤ r ^ 3 := by nlinarith [Nat.mul_le_mul hr3 hr3]
      omega
    exact_mod_cast this
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlogr : Real.log N / 3 ≤ Real.log r := by
    have h1 := Real.log_le_log hN0 hNr3
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  -- `(log N)^k ≤ J`
  have hJ8 : (N : ℝ) ≤ (J : ℝ) ^ 8 := by
    have h1 : J + 1 ≤ J * J := by nlinarith
    have h2 : r + 1 ≤ (J * J) * (J * J) := by nlinarith [Nat.mul_le_mul h1 h1]
    have h3 : (r + 1) * (r + 1) ≤ ((J * J) * (J * J)) * ((J * J) * (J * J)) :=
      Nat.mul_le_mul h2 h2
    have h4 : N ≤ J ^ 8 := by
      have h5 : ((J * J) * (J * J)) * ((J * J) * (J * J)) = J ^ 8 := by ring
      omega
    exact_mod_cast h4
  have hlogJ : Real.log N ^ k ≤ J := by
    refine hsm.trans ?_
    calc (N : ℝ) ^ ((1 : ℝ) / 8) ≤ ((J : ℝ) ^ 8) ^ ((1 : ℝ) / 8) :=
          Real.rpow_le_rpow hN0.le hJ8 (by norm_num)
      _ = J := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hJ0.le]
        norm_num
  have hpow0 : 0 < Real.log N ^ k := pow_pos hlogN k
  -- split at `J`
  rw [le_div_iff₀ hpow0]
  have hIcc : Icc 1 r = Icc 1 J ∪ Ioc J r := by
    ext j
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hdisj : Disjoint (Icc 1 J) (Ioc J r) := by
    rw [disjoint_left]
    intro j hj hj'
    have := (mem_Icc.mp hj).2
    have := (mem_Ioc.mp hj').1
    omega
  have hlarge : ∀ j ∈ Icc 1 J, |mertensCount (N / (j * j))| ≤
      K₀ * 3 ^ k * (N * ((j : ℝ) ^ 2)⁻¹) / Real.log N ^ k := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_Icc.mp hj
    have hjj : j * j ≤ r := Nat.le_sqrt.mp hj2
    have hjpos : 0 < j * j := Nat.mul_pos hj1 hj1
    have hrN : r * r ≤ N := Nat.sqrt_le N
    have hmr : r ≤ N / (j * j) := by
      rw [Nat.le_div_iff_mul_le hjpos]
      calc r * (j * j) ≤ r * r := Nat.mul_le_mul_left r hjj
        _ ≤ N := hrN
    have hbound := hm₀ (N / (j * j)) (by omega)
    have hm0 : (0 : ℝ) < (N / (j * j) : ℕ) := by
      have : 0 < N / (j * j) := by omega
      exact_mod_cast this
    have hlogm : Real.log N / 3 ≤ Real.log ((N / (j * j) : ℕ) : ℝ) := by
      refine hlogr.trans (Real.log_le_log hr0 ?_)
      exact_mod_cast hmr
    have hmle : ((N / (j * j) : ℕ) : ℝ) ≤ N * ((j : ℝ) ^ 2)⁻¹ := by
      have h1 := Nat.cast_div_le (α := ℝ) (m := N) (n := j * j)
      rw [div_eq_mul_inv] at h1
      refine h1.trans (le_of_eq ?_)
      push_cast
      rw [sq]
    have hlogpos : 0 < Real.log N / 3 := by positivity
    have hden : (Real.log N / 3) ^ k ≤ Real.log ((N / (j * j) : ℕ) : ℝ) ^ k :=
      pow_le_pow_left₀ hlogpos.le hlogm k
    have hden0 : 0 < (Real.log N / 3) ^ k := pow_pos hlogpos k
    calc |mertensCount (N / (j * j))|
        ≤ K₀ * ((N / (j * j) : ℕ) : ℝ) / Real.log ((N / (j * j) : ℕ) : ℝ) ^ k := hbound
      _ ≤ K₀ * ((N / (j * j) : ℕ) : ℝ) / (Real.log N / 3) ^ k :=
        div_le_div_of_nonneg_left (by positivity) hden0 hden
      _ ≤ K₀ * (N * ((j : ℝ) ^ 2)⁻¹) / (Real.log N / 3) ^ k := by
        gcongr
      _ = K₀ * 3 ^ k * (N * ((j : ℝ) ^ 2)⁻¹) / Real.log N ^ k := by
        rw [div_pow]
        field_simp
  have htail : ∀ j ∈ Ioc J r, |mertensCount (N / (j * j))| ≤ N * ((j : ℝ) ^ 2)⁻¹ := by
    intro j _
    refine (abs_mertensCount_le _).trans ?_
    have h1 := Nat.cast_div_le (α := ℝ) (m := N) (n := j * j)
    rw [div_eq_mul_inv] at h1
    refine h1.trans (le_of_eq ?_)
    push_cast
    rw [sq]
  have hsum1 : ∑ j ∈ Icc 1 J, |mertensCount (N / (j * j))| ≤
      2 * K₀ * 3 ^ k * N / Real.log N ^ k := by
    refine (sum_le_sum hlarge).trans ?_
    have hs : ∑ j ∈ Icc 1 J, K₀ * 3 ^ k * (N * ((j : ℝ) ^ 2)⁻¹) / Real.log N ^ k =
        K₀ * 3 ^ k * N / Real.log N ^ k * ∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹ := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      ring
    rw [hs]
    have htwo := _root_.RHTower.sum_Icc_inv_sq_le_two J
    have hc : 0 ≤ K₀ * 3 ^ k * N / Real.log N ^ k := by positivity
    calc K₀ * 3 ^ k * N / Real.log N ^ k * ∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹
        ≤ K₀ * 3 ^ k * N / Real.log N ^ k * 2 := mul_le_mul_of_nonneg_left htwo hc
      _ = _ := by ring
  have hsum2 : ∑ j ∈ Ioc J r, |mertensCount (N / (j * j))| ≤ N * (J : ℝ)⁻¹ := by
    refine (sum_le_sum htail).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hN0.le
    have h1 := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := J) (n := r) (by omega) hJr
    have h2 : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
    linarith
  have hLle : |liouvilleCount N| ≤ 2 * K₀ * 3 ^ k * N / Real.log N ^ k + N * (J : ℝ)⁻¹ := by
    rw [liouvilleCount_eq, ← hr, hIcc]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [sum_union hdisj]
    exact add_le_add hsum1 hsum2
  have hJinv : N * (J : ℝ)⁻¹ * Real.log N ^ k ≤ N := by
    calc N * (J : ℝ)⁻¹ * Real.log N ^ k ≤ N * (J : ℝ)⁻¹ * J :=
          mul_le_mul_of_nonneg_left hlogJ (by positivity)
      _ = N := by field_simp
  calc |liouvilleCount N| * Real.log N ^ k
      ≤ (2 * K₀ * 3 ^ k * N / Real.log N ^ k + N * (J : ℝ)⁻¹) * Real.log N ^ k :=
        mul_le_mul_of_nonneg_right hLle hpow0.le
    _ = 2 * K₀ * 3 ^ k * N + N * (J : ℝ)⁻¹ * Real.log N ^ k := by
        field_simp
    _ ≤ 2 * K₀ * 3 ^ k * N + N := by linarith
    _ = (2 * K₀ * 3 ^ k + 1) * N := by ring

/-- **The parity barrier at level `N^{1−δ}`.**  Every divisor sum of level `N^{1−δ}` with coefficients `≤ C log N` has
`L¹`-distance at least `(1 − ε)N` from `Λ` on `[1, N]`, for all large `N`, uniformly in the divisor sum. -/
theorem typeI_parity_barrier {δ ε C : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ (D : Finset ℕ) (c : ℕ → ℝ),
      (∀ d ∈ D, 0 < d ∧ (d : ℝ) ≤ (N : ℝ) ^ (1 - δ)) →
      (∀ d ∈ D, |c d| ≤ C * Real.log N) →
      (1 - ε) * N ≤ ∑ n ∈ Icc 1 N, |(vonMangoldt n : ℝ) - divisorSum D c n| := by
  obtain ⟨K, hK, hL⟩ := exists_abs_liouvilleCount_le 3
  obtain ⟨m₁, hm₁⟩ := eventually_atTop.mp hL
  -- the analytic eventualities on the real line
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hA : ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ ε / 3 * x :=
    eventually_abs_psi_sub_le (by positivity)
  have hB : ∀ᶠ x : ℝ in atTop, x ^ (δ / 2) + 1 ≤ x ^ δ := by
    have h1 : Tendsto (fun x : ℝ => x ^ (δ / 2)) atTop atTop := tendsto_rpow_atTop hδ2
    filter_upwards [h1.eventually_ge_atTop 2, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have hsq : x ^ δ = x ^ (δ / 2) * x ^ (δ / 2) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [hsq]
    nlinarith
  have hC1 : ∀ᶠ x : ℝ in atTop, (m₁ : ℝ) ≤ x ^ (δ / 2) :=
    (tendsto_rpow_atTop hδ2).eventually_ge_atTop _
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = 16 * C * K / δ ^ 3 := ⟨_, rfl⟩
  have hA₀0 : 0 ≤ A₀ := by rw [hA₀]; positivity
  have hlogbig : ∀ᶠ x : ℝ in atTop, A₀ / (ε / 3) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have hlog1 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℕ, 6 * (Real.log 4 + 4) / ε ≤ r₀ := exists_nat_ge _
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hA,
    tendsto_natCast_atTop_atTop.eventually hB, tendsto_natCast_atTop_atTop.eventually hC1,
    tendsto_natCast_atTop_atTop.eventually hlogbig, tendsto_natCast_atTop_atTop.eventually hlog1,
    eventually_ge_atTop (r₀ * r₀), eventually_ge_atTop 1] with N hpsi hrp hm hlb hl1 hNr hN1 D c hD hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hbarrier := psi_sub_le_sum_abs_sub_divisorSum (fun d hd => (hD d hd).1) c N
  -- the main term
  have hpsiN : (1 - ε / 3) * N ≤ Chebyshev.psi N := by
    have := (abs_le.mp hpsi).1
    linarith
  have hsqrt : 2 * Chebyshev.psi (Nat.sqrt N) ≤ ε / 3 * N := by
    set r := Nat.sqrt N with hr
    have hrr : r * r ≤ N := Nat.sqrt_le N
    have hrr' : (r : ℝ) * r ≤ N := by exact_mod_cast hrr
    have hr0 : r₀ ≤ r := Nat.le_sqrt.mpr hNr
    have hrreal : 6 * (Real.log 4 + 4) / ε ≤ (r : ℝ) :=
      hr₀.trans (by exact_mod_cast hr0)
    have hpsi2 := Chebyshev.psi_le_const_mul_self (x := (r : ℝ)) (Nat.cast_nonneg r)
    have h1 : 6 * (Real.log 4 + 4) ≤ ε * r := by
      rw [div_le_iff₀ hε] at hrreal
      linarith [mul_comm (r : ℝ) ε]
    have hrnn : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have h2 : 2 * ((Real.log 4 + 4) * r) ≤ ε / 3 * (r * r) := by nlinarith
    have h3 : ε / 3 * ((r : ℝ) * r) ≤ ε / 3 * N :=
      mul_le_mul_of_nonneg_left hrr' (by positivity)
    linarith
  -- the Liouville sum
  have hlogN : 0 < Real.log (N : ℝ) := by linarith
  have hterm : ∀ d ∈ D, |c d| * |liouvilleCount (N / d)| ≤
      8 * C * K / δ ^ 3 * (N / Real.log N ^ 2) * (d : ℝ)⁻¹ := by
    intro d hd
    obtain ⟨hd0, hdle⟩ := hD d hd
    have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
    -- `N/d ≥ N^δ`
    have hdiv : (N : ℝ) ^ δ ≤ N / d := by
      rw [le_div_iff₀ hd0']
      calc (N : ℝ) ^ δ * d ≤ (N : ℝ) ^ δ * (N : ℝ) ^ (1 - δ) :=
            mul_le_mul_of_nonneg_left hdle (by positivity)
        _ = N := by
          rw [← Real.rpow_add hN0]
          norm_num
    have hfloor : (N : ℝ) / d - 1 < ((N / d : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one ((N : ℝ) / d)
      rw [Nat.floor_div_eq_div] at this
      linarith
    have hm2 : (N : ℝ) ^ (δ / 2) ≤ ((N / d : ℕ) : ℝ) := by linarith
    have hmbig : m₁ ≤ N / d := by
      have : (m₁ : ℝ) ≤ ((N / d : ℕ) : ℝ) := hm.trans hm2
      exact_mod_cast this
    have hLd := hm₁ (N / d) hmbig
    have hpow0 : 0 < (N : ℝ) ^ (δ / 2) := by positivity
    have hlogm : δ / 2 * Real.log N ≤ Real.log ((N / d : ℕ) : ℝ) := by
      have h1 := Real.log_le_log hpow0 hm2
      rwa [Real.log_rpow hN0] at h1
    have hlpos : 0 < δ / 2 * Real.log (N : ℝ) := by positivity
    have hcube : (δ / 2 * Real.log N) ^ 3 ≤ Real.log ((N / d : ℕ) : ℝ) ^ 3 :=
      pow_le_pow_left₀ hlpos.le hlogm 3
    have hdivle : ((N / d : ℕ) : ℝ) ≤ N / d := Nat.cast_div_le
    have hL2 : |liouvilleCount (N / d)| ≤ K * (N / d) / (δ / 2 * Real.log N) ^ 3 := by
      calc |liouvilleCount (N / d)|
          ≤ K * ((N / d : ℕ) : ℝ) / Real.log ((N / d : ℕ) : ℝ) ^ 3 := hLd
        _ ≤ K * ((N / d : ℕ) : ℝ) / (δ / 2 * Real.log N) ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hcube
        _ ≤ K * (N / d) / (δ / 2 * Real.log N) ^ 3 := by gcongr
    calc |c d| * |liouvilleCount (N / d)|
        ≤ (C * Real.log N) * (K * (N / d) / (δ / 2 * Real.log N) ^ 3) :=
          mul_le_mul (hc d hd) hL2 (abs_nonneg _) (by positivity)
      _ = 8 * C * K / δ ^ 3 * (N / Real.log N ^ 2) * (d : ℝ)⁻¹ := by
        field_simp
        ring
  have hsumD : ∑ d ∈ D, (d : ℝ)⁻¹ ≤ 2 * Real.log N := by
    have hsub : D ⊆ Icc 1 N := by
      intro d hd
      obtain ⟨hd0, hdle⟩ := hD d hd
      refine mem_Icc.mpr ⟨hd0, ?_⟩
      have h1 : (N : ℝ) ^ (1 - δ) ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      rw [Real.rpow_one] at h1
      exact_mod_cast hdle.trans h1
    have h1 := sum_le_sum_of_subset_of_nonneg (f := fun d : ℕ => (d : ℝ)⁻¹) hsub
      (fun d _ _ => by positivity)
    have h2 := _root_.RHTower.sum_Icc_inv_le_one_add_log N
    simp only [one_div] at h2
    linarith
  have hsumterm : ∑ d ∈ D, |c d| * |liouvilleCount (N / d)| ≤ ε / 3 * N := by
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum]
    have hc0 : 0 ≤ 8 * C * K / δ ^ 3 * ((N : ℝ) / Real.log N ^ 2) := by positivity
    have hstep := mul_le_mul_of_nonneg_left hsumD hc0
    refine hstep.trans ?_
    have hval : 8 * C * K / δ ^ 3 * ((N : ℝ) / Real.log N ^ 2) * (2 * Real.log N) =
        A₀ * N / Real.log N := by
      rw [hA₀]
      field_simp
      ring
    rw [hval, div_le_iff₀ hlogN]
    have h3 := (div_le_iff₀ (by positivity : 0 < ε / 3)).mp hlb
    nlinarith
  have hfinal : (1 - ε) * (N : ℝ) = (1 - ε / 3) * N - ε / 3 * N - ε / 3 * N := by ring
  rw [hfinal]
  linarith

end GaloisForLFunctions.ArithmeticProduction
