import GaloisForLFunctions.ArithmeticElectrostatics.TheWeilPrimeFormOnAtomsIsLogarithmic
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheHeckeCocycleOfRenormalization

/-!
# The covariant counterterm is the anomaly

The renormalized torsion form is `−P − diag(c)`: Weil's prime kernel `P`, which is Hecke invariant,
and the self-intersection density `c(n)`, which is not — its Hecke variation is the cocycle
`β(n, t) = log t − (tame different)` (AIT). A renormalization is **covariant** when its finite part
is invariant under every Hecke transport `n ↦ tn`.

* **Covariance forces a scalar** (`renormalizedPrimeForm_transport`,
  `renormalizedPrimeForm_covariant_iff`, `heckeCovariant_iff_const`). A diagonal `h` gives a covariant
  renormalized form `−P + diag(h)` iff `h(tn) = h(n)` for all `t, n ≥ 1`, i.e. iff `h` is constant on
  the orders. By the survival law a scalar counterterm has survival cone `{0}` (RBG
  `survivalCone_one`): covariance and survival exclude each other for diagonal counterterms.
* **The rows of the pole vector** (`sum_up_eq`, `sum_down_eq`, `row_eq`): on the orders `≤ N`, the
  Schur-weighted row of `P` at `m` is exactly `A(⌊N/m⌋) + log m`, with `A(y) = Σ_{t ≤ y} Λ(t)/t`: up
  the tower Mertens' sum, down the tower `Σ_{t ∣ m} Λ(t) = log m`.
* **The pole vector is an approximate eigenvector with eigenvalue `log N`**
  (`row_le`, `row_ge`, `poleVector_eigen`): for `u_n = n^{−1/2}` and every `m ≤ N`,
  `(log N − log 8 − 4) u_m ≤ (P u)_m ≤ (log N + log 4 + 4) u_m`.
* **The covariant counterterm is `log N + O(1)`** (`atomicWeilForm_le_log`,
  `atomicWeilForm_poleVector_ge`, `log_sub_le_of_atomicWeilForm_le`, `covariantCounterterm_sandwich`):
  every scalar `κ` with `κ |x|² ≥ P_N(x)` for all `x` satisfies `κ ≥ log N − log 8 − 4`, and
  `κ = log N + log 4 + 4` works.

So the cheapest positive covariant renormalization of the prime place at atomic resolution `N` is the
scalar `log N + O(1)`: the regulator anomaly `log N = log #ker[N]` of the Hecke correspondence `[N]`,
with constant one — the same constant as the archimedean self-energy `log(1/ε)` of an atom at the
atomic spacing `ε ≍ 1/N`. The upper bound sharpens `2 log N + O(1)` (AES `atomicWeilForm_le`); the
lower bound sharpens `√(log 2 (log N − C))` (AES `sqrt_le_of_atomicWeilForm_le`).
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticIntersectionTheory

/-! ### Covariance forces a scalar -/

/-- The renormalized prime form with diagonal `h`: `−Σ x_m x_n P(m, n) + Σ h(n) x_n²` on `S`. -/
def renormalizedPrimeForm (S : Finset ℕ) (h : ℕ → ℝ) (x : ℕ → ℝ) : ℝ :=
  -(∑ m ∈ S, ∑ n ∈ S, x m * x n * weilPrimeKernel m n) + ∑ n ∈ S, h n * x n ^ 2

/-- **The Hecke variation of a diagonal renormalization**: transporting a cycle by `[t]` leaves the
prime part unchanged and moves the diagonal from `h(n)` to `h(tn)`. -/
theorem renormalizedPrimeForm_transport {S : Finset ℕ} {t : ℕ} (ht : 0 < t) (h x : ℕ → ℝ) :
    renormalizedPrimeForm (S.image (t * ·)) h (heckeTransport t x) - renormalizedPrimeForm S h x =
      ∑ n ∈ S, (h (t * n) - h n) * x n ^ 2 := by
  simp only [renormalizedPrimeForm, sum_image_mul_left ht, heckeTransport_mul ht,
    weilPrimeKernel_mul_left ht, sub_mul, sum_sub_distrib]
  ring

/-- **Covariance of a diagonal renormalization**: the renormalized form is invariant under every
Hecke transport iff `h(tn) = h(n)` for all `t ≥ 1` and all `n`. -/
theorem renormalizedPrimeForm_covariant_iff (h : ℕ → ℝ) :
    (∀ (S : Finset ℕ) (t : ℕ) (x : ℕ → ℝ), 0 < t →
        renormalizedPrimeForm (S.image (t * ·)) h (heckeTransport t x) =
          renormalizedPrimeForm S h x) ↔
      ∀ t n : ℕ, 0 < t → h (t * n) = h n := by
  constructor
  · intro hcov t n ht
    have h1 := renormalizedPrimeForm_transport (S := {n}) ht h (fun _ => 1)
    rw [hcov {n} t _ ht, sub_self] at h1
    simp only [sum_singleton, one_pow, mul_one] at h1
    linarith
  · intro hh S t x ht
    have h1 := renormalizedPrimeForm_transport (S := S) ht h x
    simp only [hh t _ ht, sub_self, zero_mul, sum_const_zero] at h1
    linarith

/-- **Covariance forces a scalar**: `h(tn) = h(n)` for all `t ≥ 1` iff `h` is constant on the
positive orders. -/
theorem heckeCovariant_iff_const (h : ℕ → ℝ) :
    (∀ t n : ℕ, 0 < t → h (t * n) = h n) ↔ ∀ n : ℕ, 0 < n → h n = h 1 := by
  constructor
  · intro hh n hn
    simpa using hh n 1 hn
  · intro hh t n ht
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [hh _ (Nat.mul_pos ht hn), hh n hn]

/-! ### The rows of Weil's prime kernel -/

/-- Up the tower the Schur-weighted row is Mertens' sum: the term `n = m` carries `Λ(1) = 0`. -/
theorem sum_up_eq {m N : ℕ} (hm : 0 < m) :
    ∑ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) =
      ∑ t ∈ Icc 1 (N / m), Λ t / t := by
  have hterm : ∀ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) =
      if m ∣ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0 := by
    intro n _
    by_cases h : m ∣ n
    · by_cases h' : m = n
      · subst h'
        simp [Nat.div_self hm]
      · rw [if_pos ⟨h, h'⟩, if_pos h]
    · rw [if_neg (fun h'' => h h''.1), if_neg h]
  rw [sum_congr rfl hterm, ← sum_filter, filter_dvd_Icc_eq_image hm,
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h]
  exact sum_congr rfl fun t _ => by rw [Nat.mul_div_cancel_left t hm]

/-- Down the tower the row is `Σ_{t ∣ m} Λ(t) = log m`. -/
theorem sum_down_eq {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ n ∈ Icc 1 N, (if n ∣ m ∧ n ≠ m then Λ (m / n) else 0) = Real.log m := by
  have hterm : ∀ n ∈ Icc 1 N, (if n ∣ m ∧ n ≠ m then Λ (m / n) else 0) =
      if n ∣ m then Λ (m / n) else 0 := by
    intro n _
    by_cases h : n ∣ m
    · by_cases h' : n = m
      · subst h'
        simp [Nat.div_self hm]
      · rw [if_pos ⟨h, h'⟩, if_pos h]
    · rw [if_neg (fun h'' => h h''.1), if_neg h]
  rw [sum_congr rfl hterm, ← sum_filter, filter_Icc_dvd_eq_divisors hm hmN,
    Nat.sum_div_divisors m (fun d => Λ d), vonMangoldt_sum]

/-- Mertens' sum `A(y) = Σ_{t ≤ y} Λ(t)/t`. -/
def mertensSum (y : ℕ) : ℝ := ∑ t ∈ Icc 1 y, Λ t / t

/-- **The Schur-weighted row is exact**: `Σ_{n ≤ N} P(m, n) √(m/n) = A(⌊N/m⌋) + log m`. -/
theorem row_eq {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ n ∈ Icc 1 N, weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) =
      mertensSum (N / m) + Real.log m := by
  rw [sum_congr rfl fun n hn => weilPrimeKernel_mul_sqrt_ratio hm (mem_Icc.mp hn).1,
    sum_add_distrib, sum_up_eq hm, sum_down_eq hm hmN, mertensSum]

/-- `log ⌊N/m⌋ + log m ≤ log N`. -/
theorem log_div_add_log_le {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    Real.log ((N / m : ℕ) : ℝ) + Real.log m ≤ Real.log N := by
  have hq : 1 ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr (by linarith)
  rw [← Real.log_mul (by positivity) (by positivity)]
  refine Real.log_le_log (by positivity) ?_
  exact_mod_cast Nat.div_mul_le_self N m

/-- `log N ≤ log ⌊N/m⌋ + log m + log 2`, since `N/m < 2 ⌊N/m⌋`. -/
theorem log_le_log_div_add_log {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    Real.log N ≤ Real.log ((N / m : ℕ) : ℝ) + Real.log m + Real.log 2 := by
  have hq : 1 ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr (by linarith)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hlt := RHTower.Mertens.cast_div_lt N m hm
  have hq' : (1 : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast hq
  rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_mul (by positivity)
    (by norm_num)]
  have hN : (0 : ℝ) < N := by exact_mod_cast hm.trans_le hmN
  refine Real.log_le_log hN ?_
  have : (N : ℝ) < (((N / m : ℕ) : ℝ) + 1) * m := by
    rw [div_lt_iff₀ hm'] at hlt; linarith
  nlinarith

/-- **Upper row bound**: `A(⌊N/m⌋) + log m ≤ log N + log 4 + 4`. -/
theorem row_le {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    mertensSum (N / m) + Real.log m ≤ Real.log N + (Real.log 4 + 4) := by
  have hq : 1 ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr (by linarith)
  have hmert := (abs_le.mp (RHTower.Mertens.mertens_first (N / m) hq)).2
  have := log_div_add_log_le hm hmN
  unfold mertensSum
  linarith

/-- **Lower row bound**: `A(⌊N/m⌋) + log m ≥ log N − log 8 − 4`. -/
theorem row_ge {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    Real.log N - (Real.log 8 + 4) ≤ mertensSum (N / m) + Real.log m := by
  have hq : 1 ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr (by linarith)
  have hmert := (abs_le.mp (RHTower.Mertens.mertens_first (N / m) hq)).1
  have := log_le_log_div_add_log hm hmN
  have h8 : Real.log 8 = Real.log 4 + Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  unfold mertensSum
  linarith

/-! ### The covariant counterterm -/

/-- **Schur's test for the atomic prime form**: a bound `R` on every Schur-weighted row bounds the
form by `R |x|²`. -/
theorem atomicWeilForm_le_of_row {N : ℕ} {R : ℝ}
    (hrow : ∀ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) ≤ R)
    (x : ℕ → ℝ) : atomicWeilForm N x ≤ R * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  set S := Icc 1 N
  have hpos : ∀ n ∈ S, 0 < n := fun n hn => (mem_Icc.mp hn).1
  -- `2 x_m x_n ≤ x_m² √(m/n) + x_n² √(n/m)`
  have hpair : ∀ m ∈ S, ∀ n ∈ S, x m * x n * weilPrimeKernel m n ≤
      (x m ^ 2 * (weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n)) +
        x n ^ 2 * (weilPrimeKernel n m * Real.sqrt ((n : ℝ) / m))) / 2 := by
    intro m hm n hn
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos m hm
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos n hn
    have ha : 0 < Real.sqrt ((m : ℝ) / n) := Real.sqrt_pos.mpr (by positivity)
    have hinv : Real.sqrt ((n : ℝ) / m) = (Real.sqrt ((m : ℝ) / n))⁻¹ := by
      rw [← Real.sqrt_inv, inv_div]
    rw [weilPrimeKernel_comm n m, hinv]
    have hP := weilPrimeKernel_nonneg m n
    set a := Real.sqrt ((m : ℝ) / n)
    have key : x m ^ 2 * a + x n ^ 2 * a⁻¹ - 2 * (x m * x n) = (x m * a - x n) ^ 2 / a := by
      field_simp
      ring
    have h2 : 2 * (x m * x n) ≤ x m ^ 2 * a + x n ^ 2 * a⁻¹ := by
      have : 0 ≤ (x m * a - x n) ^ 2 / a := by positivity
      linarith
    nlinarith
  have hsym : ∑ m ∈ S, ∑ n ∈ S, x n ^ 2 * (weilPrimeKernel n m * Real.sqrt ((n : ℝ) / m)) =
      ∑ m ∈ S, ∑ n ∈ S, x m ^ 2 * (weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n)) := sum_comm
  calc atomicWeilForm N x
      ≤ ∑ m ∈ S, ∑ n ∈ S, (x m ^ 2 * (weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n)) +
          x n ^ 2 * (weilPrimeKernel n m * Real.sqrt ((n : ℝ) / m))) / 2 :=
        sum_le_sum fun m hm => sum_le_sum fun n hn => hpair m hm n hn
    _ = ∑ m ∈ S, x m ^ 2 * ∑ n ∈ S, weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) := by
        simp only [← sum_div, sum_add_distrib, hsym, mul_sum]
        ring
    _ ≤ ∑ m ∈ S, x m ^ 2 * R := sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hrow m hm)
        (sq_nonneg _)
    _ = R * ∑ n ∈ S, x n ^ 2 := by rw [← sum_mul, mul_comm]

/-- **The covariant counterterm, upper bound**: `P_N(x) ≤ (log N + log 4 + 4) |x|²`. -/
theorem atomicWeilForm_le_log (N : ℕ) (x : ℕ → ℝ) :
    atomicWeilForm N x ≤ (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2 :=
  atomicWeilForm_le_of_row (fun m hm => by
    rw [row_eq (mem_Icc.mp hm).1 (mem_Icc.mp hm).2]
    exact row_le (mem_Icc.mp hm).1 (mem_Icc.mp hm).2) x

/-- The **pole vector** `u_n = n^{−1/2}`: the coefficients of the partial sums of `ζ` at the centre. -/
def poleVector (n : ℕ) : ℝ := 1 / Real.sqrt n

theorem poleVector_sq (n : ℕ) : poleVector n ^ 2 = 1 / n := by
  rw [poleVector, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- `(P u)_m = (A(⌊N/m⌋) + log m) u_m`: the pole vector against Weil's kernel. -/
theorem sum_weilPrimeKernel_poleVector {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ n ∈ Icc 1 N, weilPrimeKernel m n * poleVector n =
      (mertensSum (N / m) + Real.log m) * poleVector m := by
  rw [← row_eq hm hmN, sum_mul]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [poleVector, poleVector, Real.sqrt_div' _ hn0.le, mul_assoc]
  congr 1
  have hsm : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm0).ne'
  have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  field_simp

/-- **The pole vector is an approximate eigenvector of `P` with eigenvalue `log N`**:
`(log N − log 8 − 4) u_m ≤ (P u)_m ≤ (log N + log 4 + 4) u_m` for every `m ≤ N`. -/
theorem poleVector_eigen {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (Real.log N - (Real.log 8 + 4)) * poleVector m ≤
        ∑ n ∈ Icc 1 N, weilPrimeKernel m n * poleVector n ∧
      ∑ n ∈ Icc 1 N, weilPrimeKernel m n * poleVector n ≤
        (Real.log N + (Real.log 4 + 4)) * poleVector m := by
  have hu : 0 ≤ poleVector m := by unfold poleVector; positivity
  rw [sum_weilPrimeKernel_poleVector hm hmN]
  exact ⟨mul_le_mul_of_nonneg_right (row_ge hm hmN) hu,
    mul_le_mul_of_nonneg_right (row_le hm hmN) hu⟩

/-- **The pole vector attains the covariant counterterm up to `O(1)`**:
`P_N(u) ≥ (log N − log 8 − 4) |u|²`. -/
theorem atomicWeilForm_poleVector_ge (N : ℕ) :
    (Real.log N - (Real.log 8 + 4)) * ∑ n ∈ Icc 1 N, poleVector n ^ 2 ≤
      atomicWeilForm N poleVector := by
  rw [atomicWeilForm, mul_sum]
  refine sum_le_sum fun m hm => ?_
  have hm' := mem_Icc.mp hm
  have h := (poleVector_eigen hm'.1 hm'.2).1
  have hu : 0 ≤ poleVector m := by unfold poleVector; positivity
  calc (Real.log N - (Real.log 8 + 4)) * poleVector m ^ 2
      = ((Real.log N - (Real.log 8 + 4)) * poleVector m) * poleVector m := by ring
    _ ≤ (∑ n ∈ Icc 1 N, weilPrimeKernel m n * poleVector n) * poleVector m :=
        mul_le_mul_of_nonneg_right h hu
    _ = ∑ n ∈ Icc 1 N, poleVector m * poleVector n * weilPrimeKernel m n := by
        rw [sum_mul]
        exact sum_congr rfl fun n _ => by ring

/-- **The covariant counterterm, lower bound**: if a scalar `κ` dominates the atomic prime form on
the orders `≤ N`, then `κ ≥ log N − log 8 − 4`. -/
theorem log_sub_le_of_atomicWeilForm_le {N : ℕ} (hN : 1 ≤ N) {κ : ℝ}
    (hκ : ∀ x : ℕ → ℝ, atomicWeilForm N x ≤ κ * ∑ n ∈ Icc 1 N, x n ^ 2) :
    Real.log N - (Real.log 8 + 4) ≤ κ := by
  have hmass : 0 < ∑ n ∈ Icc 1 N, poleVector n ^ 2 := by
    refine sum_pos (fun n hn => ?_) ⟨1, mem_Icc.mpr ⟨le_rfl, hN⟩⟩
    rw [poleVector_sq]
    have : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    positivity
  have h := (atomicWeilForm_poleVector_ge N).trans (hκ poleVector)
  exact le_of_mul_le_mul_right h hmass

/-- **The covariant counterterm is `log N + O(1)`.** The scalar `log N + log 4 + 4` renormalizes
the atomic prime form on the orders `≤ N`, and every renormalizing scalar is at least
`log N − log 8 − 4`. -/
theorem covariantCounterterm_sandwich {N : ℕ} (hN : 1 ≤ N) :
    (∀ x : ℕ → ℝ, atomicWeilForm N x ≤
        (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2) ∧
      ∀ κ : ℝ, (∀ x : ℕ → ℝ, atomicWeilForm N x ≤ κ * ∑ n ∈ Icc 1 N, x n ^ 2) →
        Real.log N - (Real.log 8 + 4) ≤ κ :=
  ⟨atomicWeilForm_le_log N, fun _ hκ => log_sub_le_of_atomicWeilForm_le hN hκ⟩

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
