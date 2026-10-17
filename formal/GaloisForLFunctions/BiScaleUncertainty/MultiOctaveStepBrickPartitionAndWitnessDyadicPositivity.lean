import GaloisForLFunctions.RHTower.FermiNymanMultiplicityIndex
import GaloisForLFunctions.RHTower.FermiNymanBoundedSpuriousClassification
import GaloisForLFunctions.BiScaleUncertainty.LocalToGlobalTailStabilityAndWitnessIndicatorPairing

/-!
# Multi-Octave Step-Brick Partition, Cellular Möbius Inversion & Witness Dyadic Positivity

This module resolves **Item 3** on Route `PW-B` / `Route PM` by establishing the exact cellular
piecewise-constant structure of the Fermi-Nyman generators $\varphi_d$, constructing the explicit
finite combinations of $\{\varphi_a\}_{1 \le a \le N}$ that isolate **individual reciprocal cells**
$I_k = (1/(k+1), 1/k]$ across the entire bulk $(1/(N+1), 1]$, and connecting them to the dyadic
quadratic form `dyadicForm w w` and the witness negative index `witnessNegIndex`.

## Main Results

1. **Exact Cellular Piecewise-Constancy of $\varphi_d$ (`fermiNymanGen_eq_fermiCellMatrix_on_cell`, §1):**
   - For every real $a \ge 2$, $\varphi_a(t) = 0$ identically on the top octave $(1/2, 1]$.
   - For every integer $d \ge 1$ and every reciprocal cell $I_n = (1/(n+1), 1/n]$ ($n \ge 1$),
     $\lfloor 1/t \rfloor_+ = n$ holds across the **entire half-open cell** $\operatorname{Ioc}(1/(n+1), 1/n]$,
     so `fermiNymanGen (d : ℝ) t` is constant on $I_n$ and equal to:
     $$\operatorname{fermiCellMatrix}(d, n) := 2\left\lfloor \frac{n}{2d} \right\rfloor - \left\lfloor \frac{n}{d} \right\rfloor \in \{-1, 0\}.$$
   - The infinite matrix $\operatorname{fermiCellMatrix}(d, n)$ is **upper-triangular** with
     $\operatorname{fermiCellMatrix}(d, n) = 0$ for all $n < d$ and diagonal entries
     $\operatorname{fermiCellMatrix}(d, d) = -1$ for all $d \ge 1$.

2. **Dilated Möbius Step Combinators & Dyadic Resolvent Single-Cell Indicators (§2):**
   - For each cell index $k \ge 1$ and cutoff $N \ge 1$, the dilated Möbius combinator
     $$B_{k, N}(t) := -\sum_{m=1}^{\lfloor N/k \rfloor} \mu(m)\,\varphi_{k m}(t)$$
     evaluates on every cell $I_n = (1/(n+1), 1/n]$ ($1 \le n \le N$) to the exact dyadic step:
     $$B_{k, N}(t) = \mathbf{1}_{k \le n} - 2\,\mathbf{1}_{2k \le n}.$$
   - Forming the finite dyadic resolvent $\widetilde{B}_{k, N}(t) := \sum_{j=0}^N 2^j B_{2^j k, N}(t)$
     telescopes the dyadic steps on $1 \le n \le N$ to the pure threshold $\mathbf{1}_{k \le n}$,
     and its first difference $\widetilde{B}_{k, N}(t) - \widetilde{B}_{k+1, N}(t)$ equals the
     **exact single-cell indicator** $\mathbf{1}_{(1/(k+1), 1/k]}(t)$ on every cell $I_n$ ($1 \le n \le N$).

3. **Witness Dyadic Form Positivity & Top-Octave vs. Lower-Half Energy Balance (§3):**
   - For every integrable $v : \mathbb{R} \to \mathbb{C}$ on $(0, 1]$, the dyadic Hermitian form
     `dyadicForm v v` splits into half the difference between the lower-half energy on $(0, 1/2]$
     and the top-octave energy on $(1/2, 1]$:
     $$(\operatorname{dyadicForm}\,v\,v).\mathrm{re}
       = \frac{1}{2}\left(\int_0^{1/2} \|v(t)\|^2\,dt - \int_{1/2}^1 \|v(t)\|^2\,dt\right).$$
   - Consequently, `0 ≤ (dyadicForm w w).re` for all `IsFermiNymanWitness w` is equivalent to
     the top-octave energy domination bound $\int_{1/2}^1 \|w(t)\|^2\,dt \le \int_0^{1/2} \|w(t)\|^2\,dt$,
     which forces `witnessNegIndex = 0`, `rightStripMultiplicityCount = 0`, and `RiemannHypothesis`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.NymanMellin RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. Exact Cellular Piecewise-Constancy & Upper-Triangularity of `fermiNymanGen` -/

/-- **Top-Octave Vanishing of Higher Generators (`a ≥ 2`):**
Every Fermi-Nyman generator `fermiNymanGen a` with `2 ≤ a` vanishes identically on the top
dyadic octave `Ioc (1 / 2) 1`. -/
theorem fermiNymanGen_eq_zero_on_top_octave_of_two_le
    {a : ℝ} (ha : 2 ≤ a) {t : ℝ} (ht : t ∈ Ioc (1 / 2 : ℝ) 1) :
    fermiNymanGen a t = 0 := by
  have ha0 : 0 < a := by linarith
  have hinv : 1 / a < t := by
    have hle : 1 / a ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) ha
    exact lt_of_le_of_lt hle ht.1
  exact fermiNymanGen_eq_zero_of_inv_lt ha0 hinv

/-- On the half-open reciprocal cell `Ioc (1 / (n + 1)) (1 / n)` (`n ≥ 1`), the natural floor
`⌊1 / t⌋₊` is identically equal to `n`. -/
theorem nat_floor_inv_eq_on_reciprocal_cell {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    ⌊1 / t⌋₊ = n := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn1R : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have ht_pos : 0 < t := lt_of_le_of_lt (by positivity) ht.1
  have hlow : (n : ℝ) ≤ 1 / t := (le_div_iff₀ ht_pos).mpr
    (by linarith [(le_div_iff₀ hnR).mp ht.2])
  have hhigh : 1 / t < (n : ℝ) + 1 := (div_lt_iff₀ ht_pos).mpr
    (by linarith [(div_lt_iff₀ hn1R).mp ht.1])
  exact (Nat.floor_eq_iff (by positivity : 0 ≤ 1 / t)).mpr ⟨hlow, hhigh⟩

/-- The discrete cellular matrix of the Fermi-Nyman generators:
$$\operatorname{fermiCellMatrix}(d, n) := 2\left\lfloor \frac{n}{2d} \right\rfloor - \left\lfloor \frac{n}{d} \right\rfloor.$$ -/
def fermiCellMatrix (d n : ℕ) : ℝ :=
  2 * ((n / (2 * d) : ℕ) : ℝ) - ((n / d : ℕ) : ℝ)

/-- For every `t > 0` and `d : ℕ`, `fermiNymanGen (d : ℝ) t` depends on `t` only through the
discrete integer cell index `⌊1 / t⌋₊`:
$$\varphi_d(t) = \operatorname{fermiCellMatrix}(d, \lfloor 1 / t \rfloor_+).$$ -/
theorem fermiNymanGen_natCast_eq_fermiCellMatrix {d : ℕ} {t : ℝ} (ht : 0 < t) :
    fermiNymanGen (d : ℝ) t = ((fermiCellMatrix d ⌊1 / t⌋₊ : ℝ) : ℂ) := by
  rw [fermiNymanGen_eq_floor_difference]
  have h1 : (⌊(1 / t) / (d : ℝ)⌋ : ℝ) = ((⌊1 / t⌋₊ / d : ℕ) : ℝ) :=
    real_floor_div_eq_nat_div d (by positivity : 0 ≤ 1 / t)
  have h2 : (⌊(1 / (2 * t)) / (d : ℝ)⌋ : ℝ) = ((⌊1 / t⌋₊ / (2 * d) : ℕ) : ℝ) := by
    have heq : (1 / (2 * t)) / (d : ℝ) = (1 / t) / ((2 * d : ℕ) : ℝ) := by
      push_cast
      ring
    rw [heq, real_floor_div_eq_nat_div (2 * d) (by positivity : 0 ≤ 1 / t)]
  rw [h1, h2]
  unfold fermiCellMatrix
  rfl

/-- **Exact Cellular Piecewise-Constancy of `fermiNymanGen`:**
On every reciprocal cell `Ioc (1 / (n + 1)) (1 / n)` (`n ≥ 1`), `fermiNymanGen (d : ℝ) t` is
constant and equal to `fermiCellMatrix d n`. -/
theorem fermiNymanGen_eq_fermiCellMatrix_on_cell {d n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    fermiNymanGen (d : ℝ) t = ((fermiCellMatrix d n : ℝ) : ℂ) := by
  have ht_pos : 0 < t := lt_of_le_of_lt (by positivity) ht.1
  rw [fermiNymanGen_natCast_eq_fermiCellMatrix ht_pos,
    nat_floor_inv_eq_on_reciprocal_cell hn ht]

/-- **Upper-Triangularity of `fermiCellMatrix`:**
For all `n < d`, `fermiCellMatrix d n = 0`. -/
theorem fermiCellMatrix_eq_zero_of_lt {d n : ℕ} (h : n < d) :
    fermiCellMatrix d n = 0 := by
  have h2 : n < 2 * d := by omega
  unfold fermiCellMatrix
  rw [Nat.div_eq_of_lt h, Nat.div_eq_of_lt h2]
  simp

/-- **Unit Negative Diagonal of `fermiCellMatrix`:**
For every `d > 0`, `fermiCellMatrix d d = -1`. -/
theorem fermiCellMatrix_diag {d : ℕ} (hd : 0 < d) :
    fermiCellMatrix d d = -1 := by
  have h2 : d < 2 * d := by omega
  unfold fermiCellMatrix
  rw [Nat.div_self hd, Nat.div_eq_of_lt h2]
  norm_num

/-- On the sub-diagonal band `d ≤ n < 2d`, `fermiCellMatrix d n = -1`. -/
theorem fermiCellMatrix_eq_neg_one_of_band {d n : ℕ} (hd : d ≤ n) (h2 : n < 2 * d) :
    fermiCellMatrix d n = -1 := by
  have hd_pos : 0 < d := by omega
  have hdiv1 : n / d = 1 := by
    apply le_antisymm
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd_pos).mpr (by omega))
    · exact (Nat.le_div_iff_mul_le hd_pos).mpr (by omega)
  unfold fermiCellMatrix
  rw [hdiv1, Nat.div_eq_of_lt h2]
  norm_num

/-! ## §2. Dilated Möbius Step Combinators & Dyadic Resolvent Single-Cell Indicators -/

/-- Discrete Möbius floor inversion for multiples of `k`:
For `k > 0` and `1 ≤ n ≤ N`,
$$\sum_{m=1}^{\lfloor N/k \rfloor} \mu(m)\,\left\lfloor \frac{n}{k m} \right\rfloor
  = \begin{cases} 1 & \text{if } k \le n, \\ 0 & \text{if } n < k. \end{cases}$$ -/
theorem sum_moebius_div_mul_eq_ite {k N n : ℕ} (hk : 0 < k) (hnN : n ≤ N) :
    (∑ m ∈ Finset.Icc 1 (N / k), ((moebius m : ℤ) : ℝ) * ((n / (k * m) : ℕ) : ℝ)) =
      if k ≤ n then 1 else 0 := by
  have hdiv : ∀ m : ℕ, (n / (k * m) : ℕ) = (n / k) / m :=
    fun m => (Nat.div_div_eq_div_mul n k m).symm
  simp_rw [hdiv]
  have hfloor : ∀ m : ℕ, (((n / k) / m : ℕ) : ℝ) = (⌊((n / k : ℕ) : ℝ) / (m : ℝ)⌋ : ℝ) := by
    intro m
    have h := real_floor_div_eq_nat_div m (Nat.cast_nonneg (n / k))
    rw [Nat.floor_natCast] at h
    exact h.symm
  simp_rw [hfloor]
  have hle : ⌊((n / k : ℕ) : ℝ)⌋₊ ≤ N / k := by
    rw [Nat.floor_natCast]
    exact Nat.div_le_div_right hnN
  rw [sum_moebius_floor_truncated (N / k) (Nat.cast_nonneg (n / k)) hle]
  have hcond : (1 : ℝ) ≤ ((n / k : ℕ) : ℝ) ↔ k ≤ n := by
    rw [Nat.one_le_cast, Nat.le_div_iff_mul_le hk, one_mul]
  simp [hcond]

/-- The **dilated Möbius Fermi combinator** at scale `k` and cutoff `N`, belonging to the finite
span of `{fermiNymanGen a | 1 ≤ a ≤ N}`:
$$B_{k, N}(t) := -\sum_{m=1}^{\lfloor N/k \rfloor} \mu(m)\,\varphi_{k m}(t).$$ -/
def dilatedMobiusFermiCombinator (k N : ℕ) (t : ℝ) : ℂ :=
  -∑ m ∈ Finset.Icc 1 (N / k),
    ((moebius m : ℤ) : ℂ) * fermiNymanGen ((k * m : ℕ) : ℝ) t

/-- Discrete cell evaluation of `dilatedMobiusFermiCombinator`:
For every `k > 0`, `1 ≤ n ≤ N`, and `t ∈ Ioc (1 / (n + 1)) (1 / n)`,
$$B_{k, N}(t) = \mathbf{1}_{k \le n} - 2\,\mathbf{1}_{2k \le n}.$$ -/
theorem dilatedMobiusFermiCombinator_eq_dyadic_step_on_cell
    {k N n : ℕ} (hk : 0 < k) (hn : 0 < n) (hnN : n ≤ N)
    {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    dilatedMobiusFermiCombinator k N t =
      (((if k ≤ n then (1 : ℝ) else 0) - 2 * (if 2 * k ≤ n then (1 : ℝ) else 0) : ℝ) : ℂ) := by
  unfold dilatedMobiusFermiCombinator
  have hcell : ∀ m ∈ Finset.Icc 1 (N / k),
      fermiNymanGen ((k * m : ℕ) : ℝ) t = ((fermiCellMatrix (k * m) n : ℝ) : ℂ) :=
    fun m _ => fermiNymanGen_eq_fermiCellMatrix_on_cell hn ht
  rw [Finset.sum_congr rfl (fun m hm => by rw [hcell m hm])]
  have hcast :
      (-∑ m ∈ Finset.Icc 1 (N / k),
        ((moebius m : ℤ) : ℂ) * ((fermiCellMatrix (k * m) n : ℝ) : ℂ)) =
      (((∑ m ∈ Finset.Icc 1 (N / k),
          ((moebius m : ℤ) : ℝ) * ((n / (k * m) : ℕ) : ℝ)) -
        2 * (∑ m ∈ Finset.Icc 1 (N / k),
          ((moebius m : ℤ) : ℝ) * ((n / (2 * k * m) : ℕ) : ℝ)) : ℝ) : ℂ) := by
    unfold fermiCellMatrix
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [show 2 * (k * m) = 2 * k * m by ring]
    ring
  rw [hcast, sum_moebius_div_mul_eq_ite hk hnN]
  have h2sum :
      (∑ m ∈ Finset.Icc 1 (N / k),
        ((moebius m : ℤ) : ℝ) * ((n / (2 * k * m) : ℕ) : ℝ)) =
      if 2 * k ≤ n then 1 else 0 := by
    rw [← sum_moebius_div_mul_eq_ite (Nat.mul_pos (by decide) hk) hnN]
    apply (Finset.sum_subset (Finset.Icc_subset_Icc_right
      (Nat.div_le_div_left (by omega : k ≤ 2 * k) hk)) ?_).symm
    intro m hm hnot
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hgt : N / (2 * k) < m := by
      by_contra hle
      exact hnot (Finset.mem_Icc.mpr ⟨hm1, le_of_not_gt hle⟩)
    have hn_lt : n / (2 * k) < m := lt_of_le_of_lt (Nat.div_le_div_right hnN) hgt
    have hdiv0 : n / (2 * k * m) = 0 := by
      rw [← Nat.div_div_eq_div_mul]
      exact Nat.div_eq_of_lt hn_lt
    simp [hdiv0]
  rw [h2sum]

/-- Binary telescoping identity for dyadic step differences:
$$\sum_{j=0}^{J-1} 2^j \bigl(\mathbf{1}_{2^j k \le n} - 2\,\mathbf{1}_{2^{j+1} k \le n}\bigr)
  = \mathbf{1}_{k \le n} - 2^J\,\mathbf{1}_{2^J k \le n}.$$ -/
theorem sum_pow_two_dyadic_step_telescope (k n J : ℕ) :
    (∑ j ∈ Finset.range J,
      (2 : ℝ) ^ j * ((if 2 ^ j * k ≤ n then (1 : ℝ) else 0) -
        2 * (if 2 ^ (j + 1) * k ≤ n then (1 : ℝ) else 0))) =
      (if k ≤ n then (1 : ℝ) else 0) - (2 : ℝ) ^ J * (if 2 ^ J * k ≤ n then (1 : ℝ) else 0) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- The **dyadic-resolvent Möbius combinator** at cell threshold `k` and cutoff `N`:
$$\widetilde{B}_{k, N}(t) := \sum_{j=0}^N 2^j\,B_{2^j k, N}(t).$$ -/
def dyadicResolventCellThreshold (k N : ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), ((2 : ℂ) ^ j) * dilatedMobiusFermiCombinator (2 ^ j * k) N t

/-- **Exact Bulk Threshold Theorem:**
For every `k > 0`, `1 ≤ n ≤ N`, and `t ∈ Ioc (1 / (n + 1)) (1 / n)`,
`dyadicResolventCellThreshold k N t` evaluates to the pure step threshold `if k ≤ n then 1 else 0`. -/
theorem dyadicResolventCellThreshold_eq_ite_on_cell
    {k N n : ℕ} (hk : 0 < k) (hn : 0 < n) (hnN : n ≤ N)
    {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    dyadicResolventCellThreshold k N t = ((if k ≤ n then (1 : ℝ) else 0 : ℝ) : ℂ) := by
  unfold dyadicResolventCellThreshold
  have hterm : ∀ j ∈ Finset.range (N + 1),
      ((2 : ℂ) ^ j) * dilatedMobiusFermiCombinator (2 ^ j * k) N t =
      (((2 : ℝ) ^ j * ((if 2 ^ j * k ≤ n then (1 : ℝ) else 0) -
        2 * (if 2 ^ (j + 1) * k ≤ n then (1 : ℝ) else 0)) : ℝ) : ℂ) := by
    intro j _
    have h2jk : 0 < 2 ^ j * k := Nat.mul_pos (pow_pos (by decide) j) hk
    rw [dilatedMobiusFermiCombinator_eq_dyadic_step_on_cell h2jk hn hnN ht]
    rw [show 2 * (2 ^ j * k) = 2 ^ (j + 1) * k by ring]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum,
    sum_pow_two_dyadic_step_telescope k n (N + 1)]
  have hgt : n < 2 ^ (N + 1) * k := by
    calc
      n ≤ N := hnN
      _ < N + 1 := Nat.lt_succ_self N
      _ < 2 ^ (N + 1) := Nat.lt_pow_self (by decide : 1 < 2)
      _ ≤ 2 ^ (N + 1) * k := Nat.le_mul_of_pos_right _ hk
  rw [if_neg (not_le.mpr hgt)]
  simp

/-- The **single-cell Fermi combinator** for reciprocal cell `I_k = (1 / (k + 1), 1 / k]` at
cutoff `N`:
$$\operatorname{singleCellFermiCombinator}(k, N, t)
  := \widetilde{B}_{k, N}(t) - \widetilde{B}_{k + 1, N}(t).$$ -/
def singleCellFermiCombinator (k N : ℕ) (t : ℝ) : ℂ :=
  dyadicResolventCellThreshold k N t - dyadicResolventCellThreshold (k + 1) N t

/-- **Exact Single-Cell Kronecker Delta Theorem:**
For every `k > 0`, `1 ≤ n ≤ N`, and `t ∈ Ioc (1 / (n + 1)) (1 / n)`,
`singleCellFermiCombinator k N t` equals `1` on cell `n = k` and `0` on every other cell
`n ≠ k` (`1 ≤ n ≤ N`)! -/
theorem singleCellFermiCombinator_eq_kronecker_on_cell
    {k N n : ℕ} (hk : 0 < k) (hn : 0 < n) (hnN : n ≤ N)
    {t : ℝ} (ht : t ∈ Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    singleCellFermiCombinator k N t = if n = k then 1 else 0 := by
  unfold singleCellFermiCombinator
  rw [dyadicResolventCellThreshold_eq_ite_on_cell hk hn hnN ht,
    dyadicResolventCellThreshold_eq_ite_on_cell (Nat.succ_pos k) hn hnN ht]
  by_cases hnk : n = k
  · subst hnk
    simp
  · by_cases hle : k ≤ n
    · have hsucc : k + 1 ≤ n := by omega
      simp [hle, hsucc, hnk]
    · have hnsucc : ¬(k + 1 ≤ n) := by omega
      simp [hle, hnsucc, hnk]

/-! ## §3. Witness Dyadic Form Positivity & Top-Octave vs. Lower-Half Energy Balance -/

/-- **Octave Energy Split of `dyadicForm`:**
For any function `v : ℝ → ℂ` whose squared norm is integrable on `Ioc 0 1`, the real part of the
dyadic Hermitian form `dyadicForm v v` equals half the difference between the lower-half energy
on `(0, 1/2]` and the top-octave energy on `(1/2, 1]`:
$$(\operatorname{dyadicForm}\,v\,v).\mathrm{re}
  = \frac{1}{2}\left(\int_0^{1/2} \|v(t)\|^2\,dt - \int_{1/2}^1 \|v(t)\|^2\,dt\right).$$ -/
theorem dyadicForm_self_re_eq_half_octave_diff {v : ℝ → ℂ}
    (hv : IntegrableOn (fun t => ‖v t‖ ^ 2) (Ioc (0 : ℝ) 1)) :
    (dyadicForm v v).re =
      (1 / 2 : ℝ) * ((∫ t in Ioc (0 : ℝ) (1 / 2), ‖v t‖ ^ 2) -
        (∫ t in Ioc (1 / 2 : ℝ) 1, ‖v t‖ ^ 2)) := by
  rw [dyadicForm_self, Complex.ofReal_re]
  have hlow : IntegrableOn (fun t => ‖v t‖ ^ 2) (Ioc (0 : ℝ) (1 / 2)) :=
    hv.mono_set (Ioc_subset_Ioc_right (by norm_num))
  have hhigh : IntegrableOn (fun t => ‖v t‖ ^ 2) (Ioc (1 / 2 : ℝ) 1) :=
    hv.mono_set (Ioc_subset_Ioc_left (by norm_num))
  have hdisj : Disjoint (Ioc (0 : ℝ) (1 / 2)) (Ioc (1 / 2 : ℝ) 1) :=
    Set.disjoint_left.mpr (fun _ h1 h2 => (not_lt_of_ge h1.2) h2.1)
  have hunion : Ioc (0 : ℝ) (1 / 2) ∪ Ioc (1 / 2 : ℝ) 1 = Ioc (0 : ℝ) 1 :=
    Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)
  have hsplit : (∫ t in Ioc (0 : ℝ) 1, ‖v t‖ ^ 2) =
      (∫ t in Ioc (0 : ℝ) (1 / 2), ‖v t‖ ^ 2) + (∫ t in Ioc (1 / 2 : ℝ) 1, ‖v t‖ ^ 2) := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioc hlow hhigh]
  rw [hsplit]
  ring

/-- Non-negativity of `(dyadicForm v v).re` is equivalent to the top-octave energy bound
`∫_{1/2}^1 ‖v t‖^2 dt ≤ ∫_0^{1/2} ‖v t‖^2 dt`. -/
theorem dyadicForm_self_re_nonneg_iff_top_octave_le_lower_half {v : ℝ → ℂ}
    (hv : IntegrableOn (fun t => ‖v t‖ ^ 2) (Ioc (0 : ℝ) 1)) :
    0 ≤ (dyadicForm v v).re ↔
      (∫ t in Ioc (1 / 2 : ℝ) 1, ‖v t‖ ^ 2) ≤ (∫ t in Ioc (0 : ℝ) (1 / 2), ‖v t‖ ^ 2) := by
  rw [dyadicForm_self_re_eq_half_octave_diff hv]
  constructor <;> intro h <;> linarith

/-- **Top-Octave Energy Domination Implies `witnessNegIndex = 0` and `RiemannHypothesis`:**
If every Fermi-Nyman witness `w` has top-octave energy at most its lower-half tail energy
(`∫_{1/2}^1 ‖w t‖^2 dt ≤ ∫_0^{1/2} ‖w t‖^2 dt`), then `witnessNegIndex = 0`,
`rightStripMultiplicityCount = 0`, and `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_witness_top_octave_energy_le_lower_half
    (hdom : ∀ w : ℝ → ℂ, IsFermiNymanWitness w →
      (∫ t in Ioc (1 / 2 : ℝ) 1, ‖w t‖ ^ 2) ≤ (∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2)) :
    witnessNegIndex = 0 ∧ rightStripMultiplicityCount = 0 ∧ RiemannHypothesis := by
  have hneg0 : witnessNegIndex = 0 := by
    refine le_antisymm (iSup₂_le fun n hn => ?_) zero_le
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · exfalso
      obtain ⟨v, hvW, hvq⟩ := hn
      have hw := hvW ⟨0, hpos⟩
      have hnonneg : 0 ≤ (dyadicForm (v ⟨0, hpos⟩) (v ⟨0, hpos⟩)).re :=
        (dyadicForm_self_re_nonneg_iff_top_octave_le_lower_half hw.2.1).mpr
          (hdom (v ⟨0, hpos⟩) hw)
      have hminus1 := hvq ⟨0, hpos⟩ ⟨0, hpos⟩
      rw [if_pos rfl] at hminus1
      rw [hminus1] at hnonneg
      norm_num at hnonneg
  have hmult0 : rightStripMultiplicityCount = 0 := by
    rw [← witnessNegIndex_eq_rightStripMultiplicityCount, hneg0]
  exact ⟨hneg0, hmult0, riemannHypothesis_iff_witnessNegIndex_eq_zero.mpr hneg0⟩

/-- **Exact Equivalence Between Witness Top-Octave Domination and `RiemannHypothesis`:**
`RiemannHypothesis` holds if and only if for every `w : ℝ → ℂ` satisfying `IsFermiNymanWitness w`,
the top-octave energy on `(1/2, 1]` is bounded above by the lower-half energy on `(0, 1/2]`. -/
theorem riemannHypothesis_iff_witness_top_octave_energy_le_lower_half :
    RiemannHypothesis ↔
      ∀ w : ℝ → ℂ, IsFermiNymanWitness w →
        (∫ t in Ioc (1 / 2 : ℝ) 1, ‖w t‖ ^ 2) ≤ (∫ t in Ioc (0 : ℝ) (1 / 2), ‖w t‖ ^ 2) := by
  constructor
  · intro hRH w hw
    rw [← dyadicForm_self_re_nonneg_iff_top_octave_le_lower_half hw.2.1]
    have hhalf := riemannHypothesis_iff_fermiNymanWitness_halfMass.mp hRH w hw
    rw [dyadicForm_self, hhalf, sub_self, Complex.ofReal_zero, Complex.zero_re]
  · intro hdom
    exact (riemannHypothesis_of_witness_top_octave_energy_le_lower_half hdom).2.2

end

end GaloisForLFunctions.BiScaleUncertainty
