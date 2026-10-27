import GaloisForLFunctions.ArithmeticElectrostatics.TheStabilityLawAtAtomicResolution

/-!
# The gauge is invisible at atomic resolution

A sign twin of `ζ` replaces `Λ` by `ωΛ` for a completely multiplicative `ω` with `ω(n) = ±1` on
`n ≥ 1`. Its renormalized source differs from `ζ`'s by a margin `2 log² p` at every flipped prime
(`TheGaugeMarginOfTheRenormalizedSource`). This file shows that no such margin survives at the level
of Weil forms on atomic tests — narrow bumps at the points `log n`, `n ≤ N`.

* **The gauge is a diagonal of signs** (`twistedWeilPrimeKernel_eq`): the twin's prime kernel is
  `P_ω(m, n) = ω(n/m) P(m, n) = ω(m) ω(n) P(m, n)`, since `ω(n) = ω(m) ω(n/m)` and `ω(m)² = 1`.
* **Conjugacy of the atomic forms** (`twistedAtomicWeilForm_eq`, `sum_sq_gauge`): the twin's atomic
  prime form at `x` is `ζ`'s at `ωx`, and `x ↦ ωx` is an isometry. The two forms have the same
  bounds above and below (`twistedAtomicWeilForm_le_iff`, `le_twistedAtomicWeilForm_iff`): the
  Schur bound `2 log N + O(1)` and the arithmetic-point lower bound `√(log 2 (log N − C))` hold for
  every twin.
* **The twin's prime sum of an atomic test** (`twistedPrimeSum_atomicTest`): below the spacing, the
  lag pairings of `ωx` are those of `x` multiplied by `ω(k)`, so the twin's prime sum of the test
  with weights `x` is `ζ`'s prime sum of the test with weights `ωx`.
* **The stability law is gauge blind** (`twinMarkovEnergy_atomicTest_nonneg`): every sign twin has
  nonnegative archimedean-minus-prime form on every atomic test of width at most `atomicWidth N`.
* **The margin lives on the positive cone, on the wrong side** (`twistedAtomicWeilForm_le_of_nonneg`,
  `gaugeMargin_atomicWeilForm`, `twinMarkov_sub_markov_atomicTest`,
  `twinMarkov_sub_markov_pairWeights`): `M_ω(f) − M(f) = (∫ g²) Σ x_m x_n (1 − ω(m)ω(n)) P(m, n)`,
  nonnegative for nonnegative weights; on the two-atom test `1_{1} + 1_{p}` at a flipped prime it
  equals `2 Λ(p)/√p · ∫ f²` for every window `N ≥ p`. On nonnegative atomic tests `ζ` is the minimum
  of its gauge orbit, by a margin that does not collapse as primes enter.

So atomic resolution cannot separate `ζ` from any sign twin in `ζ`'s favour — for instance from the Liouville twin
`ζ(2s)/ζ(s)`, whose logarithmic derivative has poles at the zeros of `ζ`. The gauge charge is seen
by the source coefficient by coefficient, and by Weil forms only through lags `log k` that are not
exact ratios `log(m/n)` of atoms: at widths comparable to the spacing, where atoms overlap.
-/

noncomputable section

open MeasureTheory Finset RHTower ArithmeticFunction
open scoped Real

namespace GaloisForLFunctions.ArithmeticElectrostatics

open ArithmeticEffectivityTheory

variable {ω : ArithmeticFunction ℝ}

/-- A sign gauge squares to one on positive integers. -/
theorem gauge_mul_self (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) {n : ℕ} (hn : 0 < n) :
    ω n * ω n = 1 := by
  rcases hsign n hn with h | h <;> rw [h] <;> norm_num

/-- The **twin's prime kernel**: `ω(n/m) Λ(n/m)(n/m)^{−1/2}` on `m ∣ n`, `m ≠ n`, symmetric. -/
def twistedWeilPrimeKernel (ω : ArithmeticFunction ℝ) (m n : ℕ) : ℝ :=
  if m ∣ n ∧ m ≠ n then ω (n / m) * Λ (n / m) / Real.sqrt ((n / m : ℕ) : ℝ)
  else if n ∣ m ∧ n ≠ m then ω (m / n) * Λ (m / n) / Real.sqrt ((m / n : ℕ) : ℝ) else 0

/-- **The gauge is a diagonal of signs**: `P_ω(m, n) = ω(m) ω(n) P(m, n)`. -/
theorem twistedWeilPrimeKernel_eq (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    twistedWeilPrimeKernel ω m n = ω m * ω n * weilPrimeKernel m n := by
  unfold twistedWeilPrimeKernel weilPrimeKernel
  by_cases h1 : m ∣ n ∧ m ≠ n
  · rw [if_pos h1, if_pos h1]
    have hq : ω n = ω m * ω (n / m) := by rw [← hω, Nat.mul_div_cancel' h1.1]
    rw [hq]
    linear_combination (-(ω (n / m) * (Λ (n / m) / Real.sqrt ((n / m : ℕ) : ℝ)))) *
      gauge_mul_self hsign hm
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : n ∣ m ∧ n ≠ m
    · rw [if_pos h2, if_pos h2]
      have hq : ω m = ω n * ω (m / n) := by rw [← hω, Nat.mul_div_cancel' h2.1]
      rw [hq]
      linear_combination (-(ω (m / n) * (Λ (m / n) / Real.sqrt ((m / n : ℕ) : ℝ)))) *
        gauge_mul_self hsign hn
    · rw [if_neg h2, if_neg h2, mul_zero]

/-- The **twin's atomic prime form** on the atoms `log n`, `1 ≤ n ≤ N`. -/
def twistedAtomicWeilForm (ω : ArithmeticFunction ℝ) (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * twistedWeilPrimeKernel ω m n

/-- **Conjugacy**: the twin's atomic form at `x` is `ζ`'s at `ωx`. -/
theorem twistedAtomicWeilForm_eq (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (N : ℕ) (x : ℕ → ℝ) :
    twistedAtomicWeilForm ω N x = atomicWeilForm N (fun n => ω n * x n) := by
  unfold twistedAtomicWeilForm atomicWeilForm
  refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
  rw [twistedWeilPrimeKernel_eq hω hsign (mem_Icc.mp hm).1 (mem_Icc.mp hn).1]
  ring

/-- The gauge is an isometry of the atomic weights. -/
theorem sum_sq_gauge (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, (ω n * x n) ^ 2 = ∑ n ∈ Icc 1 N, x n ^ 2 :=
  sum_congr rfl fun n hn => by
    linear_combination x n ^ 2 * gauge_mul_self hsign (mem_Icc.mp hn).1

/-- The gauge is an involution of the atomic weights. -/
theorem atomicWeilForm_gauge_gauge (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (N : ℕ)
    (x : ℕ → ℝ) : atomicWeilForm N (fun n => ω n * (ω n * x n)) = atomicWeilForm N x := by
  have h : ∀ n ∈ Icc 1 N, ω n * (ω n * x n) = x n := fun n hn => by
    rw [← mul_assoc, gauge_mul_self hsign (mem_Icc.mp hn).1, one_mul]
  unfold atomicWeilForm
  exact sum_congr rfl fun m hm => sum_congr rfl fun n hn => by
    show ω m * (ω m * x m) * (ω n * (ω n * x n)) * _ = _
    rw [h m hm, h n hn]

/-- **No spectral margin from above**: a bound `κ` holds for the twin's atomic form iff it holds
for `ζ`'s. -/
theorem twistedAtomicWeilForm_le_iff (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (N : ℕ) (κ : ℝ) :
    (∀ x : ℕ → ℝ, twistedAtomicWeilForm ω N x ≤ κ * ∑ n ∈ Icc 1 N, x n ^ 2) ↔
      ∀ x : ℕ → ℝ, atomicWeilForm N x ≤ κ * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  constructor
  · intro h x
    have hx := h (fun n => ω n * x n)
    rwa [twistedAtomicWeilForm_eq hω hsign, atomicWeilForm_gauge_gauge hsign,
      sum_sq_gauge hsign] at hx
  · intro h x
    rw [twistedAtomicWeilForm_eq hω hsign, ← sum_sq_gauge hsign N x]
    exact h _

/-- **No spectral margin from below**: a lower bound `κ` holds for the twin's atomic form iff it
holds for `ζ`'s. -/
theorem le_twistedAtomicWeilForm_iff (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (N : ℕ) (κ : ℝ) :
    (∀ x : ℕ → ℝ, κ * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ twistedAtomicWeilForm ω N x) ↔
      ∀ x : ℕ → ℝ, κ * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ atomicWeilForm N x := by
  constructor
  · intro h x
    have hx := h (fun n => ω n * x n)
    rwa [twistedAtomicWeilForm_eq hω hsign, atomicWeilForm_gauge_gauge hsign,
      sum_sq_gauge hsign] at hx
  · intro h x
    rw [twistedAtomicWeilForm_eq hω hsign, ← sum_sq_gauge hsign N x]
    exact h _

/-- The Schur bound for every twin: `Σ x_m x_n P_ω(m, n) ≤ (2 log N + log 4 + 4) Σ x_n²`. -/
theorem twistedAtomicWeilForm_le (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (N : ℕ) (x : ℕ → ℝ) :
    twistedAtomicWeilForm ω N x ≤ (2 * Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2 :=
  (twistedAtomicWeilForm_le_iff hω hsign N _).mpr (atomicWeilForm_le N) x

/-- The arithmetic-point lower bound for every twin: a bound `κ` on the twin's atomic form has
`κ² ≥ log 2 (log N − log 4 − 4)`. -/
theorem log_two_mul_le_sq_of_twistedAtomicWeilForm_le (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) {N : ℕ} (hN : 2 ≤ N) {κ : ℝ}
    (h : ∀ x : ℕ → ℝ, twistedAtomicWeilForm ω N x ≤ κ * ∑ n ∈ Icc 1 N, x n ^ 2) :
    Real.log 2 * (Real.log N - (Real.log 4 + 4)) ≤ κ ^ 2 :=
  log_two_mul_le_sq_of_atomicWeilForm_le hN ((twistedAtomicWeilForm_le_iff hω hsign N κ).mp h)

/-! ### The twin's Weil form on atomic tests -/

/-- The **twin's prime sum** `Σ_k ω(k) Λ(k) k^{−1/2} (f⋆f̃(log k) + f⋆f̃(−log k))`. -/
def twistedPrimeSum (ω : ArithmeticFunction ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑' k : ℕ, ω k * vonMangoldtAtom k *
    ((∫ t, f t * f (t - Real.log k)) + ∫ t, f t * f (t + Real.log k))

/-- On exact Hecke pairs the gauge factors: `[m = nk] ω(k) x_m x_n = [m = nk] (ωx)_m (ωx)_n`. -/
theorem gauge_hecke_pairs (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (N k : ℕ) (x : ℕ → ℝ) :
    ω k * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n * k then x m * x n else 0) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if m = n * k then (ω m * x m) * (ω n * x n) else 0 := by
  rw [mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun n hn => ?_
  split_ifs with h
  · rw [h, hω]
    linear_combination (-(ω k * x (n * k) * x n)) * gauge_mul_self hsign (mem_Icc.mp hn).1
  · rw [mul_zero]

/-- **The twin's prime sum of an atomic test is `ζ`'s prime sum of the gauged test**, and equals
`(∫ g²)` times the twin's atomic prime form. -/
theorem twistedPrimeSum_atomicTest (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) {g : ℝ → ℝ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ}
    (hw : w < atomSpacing N) (x : ℕ → ℝ) :
    twistedPrimeSum ω (atomicTest N x g) = primeSum (atomicTest N (fun n => ω n * x n) g) ∧
      twistedPrimeSum ω (atomicTest N x g) = (∫ u, g u ^ 2) * twistedAtomicWeilForm ω N x := by
  have hterm : ∀ k : ℕ, ω k * vonMangoldtAtom k *
      ((∫ t, atomicTest N x g t * atomicTest N x g (t - Real.log k)) +
        ∫ t, atomicTest N x g t * atomicTest N x g (t + Real.log k)) =
      vonMangoldtAtom k *
      ((∫ t, atomicTest N (fun n => ω n * x n) g t *
          atomicTest N (fun n => ω n * x n) g (t - Real.log k)) +
        ∫ t, atomicTest N (fun n => ω n * x n) g t *
          atomicTest N (fun n => ω n * x n) g (t + Real.log k)) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [vonMangoldtAtom]
    rw [integral_atomicTest_mul_shift_neg hg hgc hgsupp hw _ hk,
      integral_atomicTest_mul_shift_pos hg hgc hgsupp hw _ hk,
      integral_atomicTest_mul_shift_neg hg hgc hgsupp hw _ hk,
      integral_atomicTest_mul_shift_pos hg hgc hgsupp hw _ hk]
    -- the `+log k` pairing is the `−log k` pairing with the roles of `m, n` exchanged
    have hpos : ∀ y : ℕ → ℝ, (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if n = m * k then y m * y n else 0) =
        ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if m = n * k then y m * y n else 0 := fun y => by
      rw [sum_comm]
      exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by split_ifs <;> ring
    rw [hpos x, hpos (fun n => ω n * x n), ← gauge_hecke_pairs hω hsign N k x]
    ring
  have h1 : twistedPrimeSum ω (atomicTest N x g) =
      primeSum (atomicTest N (fun n => ω n * x n) g) := by
    rw [twistedPrimeSum, primeSum]
    exact tsum_congr hterm
  refine ⟨h1, ?_⟩
  rw [h1, primeSum_atomicTest hg hgc hgsupp hw, twistedAtomicWeilForm_eq hω hsign]

/-- **The stability law is gauge blind**: for every sign twin, every atomic test of width at most
`atomicWidth N` at the points `log n`, `n ≤ N`, has nonnegative archimedean-minus-prime form. -/
theorem twinMarkovEnergy_atomicTest_nonneg (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) {g : ℝ → ℝ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N)
    (hw0 : 0 < w) (hw : w ≤ atomicWidth N) (x : ℕ → ℝ) :
    0 ≤ archForm (atomicTest N x g) - twistedPrimeSum ω (atomicTest N x g) := by
  obtain ⟨hw4, hcoef⟩ := atomicGain_nonneg hN hw0 hw
  have hw' : w < atomSpacing N := by linarith [atomSpacing_pos hN]
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  rw [archForm_eq_levyEnergy hf hfc, (twistedPrimeSum_atomicTest hω hsign hg hgc hgsupp hw' x).2]
  have hlevy := levyEnergy_atomicTest_ge hg hgsupp hN hw0 hw4 x
  have hsq := integral_atomicTest_sq hg hgc hgsupp hw' x
  have hW := twistedAtomicWeilForm_le hω hsign N x
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hprime : (∫ u, g u ^ 2) * twistedAtomicWeilForm ω N x ≤
      (2 * Real.log N + (Real.log 4 + 4)) * ∫ u, atomicTest N x g u ^ 2 := by
    rw [hsq]
    calc (∫ u, g u ^ 2) * twistedAtomicWeilForm ω N x
        ≤ (∫ u, g u ^ 2) * ((2 * Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2) :=
          mul_le_mul_of_nonneg_left hW hG
      _ = _ := by ring
  have hint : 0 ≤ ∫ u, atomicTest N x g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  nlinarith [mul_nonneg hcoef hint]

/-! ### The margin on the positive cone -/

/-- **The vacuum is extremal on the positive cone**: for nonnegative weights the twin's atomic prime
form is at most `ζ`'s, since `ω(m)ω(n) ≤ 1` and the kernel is nonnegative. -/
theorem twistedAtomicWeilForm_le_of_nonneg (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (N : ℕ) {x : ℕ → ℝ} (hx : ∀ n, 0 ≤ x n) :
    twistedAtomicWeilForm ω N x ≤ atomicWeilForm N x := by
  unfold twistedAtomicWeilForm atomicWeilForm
  refine sum_le_sum fun m hm => sum_le_sum fun n hn => ?_
  have hm1 := (mem_Icc.mp hm).1
  have hn1 := (mem_Icc.mp hn).1
  rw [twistedWeilPrimeKernel_eq hω hsign hm1 hn1]
  have hxx : 0 ≤ x m * x n * weilPrimeKernel m n :=
    mul_nonneg (mul_nonneg (hx m) (hx n)) (weilPrimeKernel_nonneg m n)
  have hωω : ω m * ω n ≤ 1 := by
    rcases hsign m hm1 with h | h <;> rcases hsign n hn1 with h' | h' <;> rw [h, h'] <;> norm_num
  calc x m * x n * (ω m * ω n * weilPrimeKernel m n)
      = (ω m * ω n) * (x m * x n * weilPrimeKernel m n) := by ring
    _ ≤ 1 * (x m * x n * weilPrimeKernel m n) := mul_le_mul_of_nonneg_right hωω hxx
    _ = x m * x n * weilPrimeKernel m n := one_mul _

/-- The atomic form only reads the weights on their support. -/
theorem atomicWeilForm_eq_of_support {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) {x : ℕ → ℝ}
    (hx : ∀ n, n ∉ S → x n = 0) :
    atomicWeilForm N x = ∑ m ∈ S, ∑ n ∈ S, x m * x n * weilPrimeKernel m n := by
  unfold atomicWeilForm
  calc ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * weilPrimeKernel m n
      = ∑ m ∈ S, ∑ n ∈ Icc 1 N, x m * x n * weilPrimeKernel m n :=
        (sum_subset hS fun m _ hm => sum_eq_zero fun n _ => by rw [hx m hm]; ring).symm
    _ = _ := sum_congr rfl fun m _ =>
        (sum_subset hS fun n _ hn => by rw [hx n hn]; ring).symm

/-- The **two-atom weights** `1_{1} + 1_{p}`: the arithmetic point and one prime. -/
def pairWeights (p : ℕ) : ℕ → ℝ := fun n => if n = 1 ∨ n = p then 1 else 0

theorem atomicWeilForm_pairWeights_scaled {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) (a b : ℝ) :
    atomicWeilForm N (fun n => (if n = 1 then a else if n = p then b else 0)) =
      2 * a * b * (Λ p / Real.sqrt p) := by
  have h1p : (1 : ℕ) ≠ p := hp.one_lt.ne
  have hS : ({1, p} : Finset ℕ) ⊆ Icc 1 N := by
    intro n hn
    rcases mem_insert.mp hn with rfl | hn
    · exact mem_Icc.mpr ⟨le_rfl, hp.one_lt.le.trans hpN⟩
    · rw [mem_singleton.mp hn]; exact mem_Icc.mpr ⟨hp.one_lt.le, hpN⟩
  rw [atomicWeilForm_eq_of_support hS (fun n hn => by
      rw [mem_insert, mem_singleton, not_or] at hn
      rw [if_neg hn.1, if_neg hn.2]),
    sum_pair h1p, sum_pair h1p, sum_pair h1p]
  simp only [↓reduceIte, h1p.symm, weilPrimeKernel_self]
  rw [weilPrimeKernel_comm p 1, weilPrimeKernel_one_left hp.two_le]
  ring

theorem atomicWeilForm_pairWeights {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) :
    atomicWeilForm N (pairWeights p) = 2 * (Λ p / Real.sqrt p) := by
  have h : pairWeights p = fun n => if n = 1 then (1 : ℝ) else if n = p then 1 else 0 := by
    funext n
    simp only [pairWeights]
    by_cases h1 : n = 1
    · simp [h1]
    · by_cases h2 : n = p <;> simp [h1, h2]
  rw [h, atomicWeilForm_pairWeights_scaled hp hpN]
  ring

theorem sum_sq_pairWeights {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) :
    ∑ n ∈ Icc 1 N, pairWeights p n ^ 2 = 2 := by
  have h1p : (1 : ℕ) ≠ p := hp.one_lt.ne
  have hS : ({1, p} : Finset ℕ) ⊆ Icc 1 N := by
    intro n hn
    rcases mem_insert.mp hn with rfl | hn
    · exact mem_Icc.mpr ⟨le_rfl, hp.one_lt.le.trans hpN⟩
    · rw [mem_singleton.mp hn]; exact mem_Icc.mpr ⟨hp.one_lt.le, hpN⟩
  rw [← sum_subset hS fun n _ hn => by
      rw [mem_insert, mem_singleton, not_or] at hn
      simp [pairWeights, hn.1, hn.2],
    sum_pair h1p]
  simp [pairWeights]
  norm_num

/-- `ω(1) = 1` for a sign gauge. -/
theorem gauge_one (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) : ω 1 = 1 := by
  have h := hω 1 1
  rw [one_mul] at h
  rcases hsign 1 one_pos with h1 | h1
  · exact h1
  · rw [h1] at h; norm_num at h

/-- **The margin law on growing windows**: at a flipped prime `p ≤ N`, the two-atom test
`1_{1} + 1_{p}` (mass `2`) has `ζ`'s atomic form exceeding the twin's by `4 Λ(p)/√p`, for every
`N ≥ p`. -/
theorem gaugeMargin_atomicWeilForm (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    (hflip : ω p = -1) :
    atomicWeilForm N (pairWeights p) - twistedAtomicWeilForm ω N (pairWeights p) =
        4 * (Λ p / Real.sqrt p) ∧ ∑ n ∈ Icc 1 N, pairWeights p n ^ 2 = 2 := by
  refine ⟨?_, sum_sq_pairWeights hp hpN⟩
  have hgauged : (fun n => ω n * pairWeights p n) =
      fun n => if n = 1 then (1 : ℝ) else if n = p then -1 else 0 := by
    funext n
    simp only [pairWeights]
    by_cases h1 : n = 1
    · rw [if_pos (Or.inl h1), if_pos h1, h1, gauge_one hω hsign, mul_one]
    · by_cases h2 : n = p
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2, h2, hflip, mul_one]
      · rw [if_neg (not_or.mpr ⟨h1, h2⟩), if_neg h1, if_neg h2, mul_zero]
  rw [twistedAtomicWeilForm_eq hω hsign, hgauged, atomicWeilForm_pairWeights_scaled hp hpN,
    atomicWeilForm_pairWeights hp hpN]
  ring

/-- **The twin's Weil form exceeds `ζ`'s on atomic tests by the charged pairs**: below the spacing,
`M_ω(f) − M(f) = (∫ g²)(Σ x_m x_n P(m, n) − Σ x_m x_n P_ω(m, n))`, nonnegative for nonnegative
weights, and equal to `2 Λ(p)/√p · ∫ f²` on the two-atom test at a flipped prime `p ≤ N`. -/
theorem twinMarkov_sub_markov_atomicTest (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) {g : ℝ → ℝ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ}
    (hw : w < atomSpacing N) (x : ℕ → ℝ) :
    (archForm (atomicTest N x g) - twistedPrimeSum ω (atomicTest N x g)) -
        markovEnergy (fun u => (atomicTest N x g u : ℂ)) =
      (∫ u, g u ^ 2) * (atomicWeilForm N x - twistedAtomicWeilForm ω N x) := by
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum (contDiff_atomicTest hg N x)
      (hasCompactSupport_atomicTest hgsupp N x), primeSum_atomicTest hg hgc hgsupp hw x,
    (twistedPrimeSum_atomicTest hω hsign hg hgc hgsupp hw x).2]
  ring

/-- On the two-atom test at a flipped prime the twin's Weil form exceeds `ζ`'s by
`2 Λ(p)/√p · ∫ f²`: `ζ` is the minimum of its gauge orbit there, with a margin that does not
depend on the window. -/
theorem twinMarkov_sub_markov_pairWeights (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) {g : ℝ → ℝ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N p : ℕ}
    (hw : w < atomSpacing N) (hp : p.Prime) (hpN : p ≤ N) (hflip : ω p = -1) :
    (archForm (atomicTest N (pairWeights p) g) - twistedPrimeSum ω (atomicTest N (pairWeights p) g)) -
        markovEnergy (fun u => (atomicTest N (pairWeights p) g u : ℂ)) =
      2 * (Λ p / Real.sqrt p) * ∫ u, atomicTest N (pairWeights p) g u ^ 2 := by
  obtain ⟨hmargin, hmass⟩ := gaugeMargin_atomicWeilForm hω hsign hp hpN hflip
  rw [twinMarkov_sub_markov_atomicTest hω hsign hg hgc hgsupp hw, hmargin,
    integral_atomicTest_sq hg hgc hgsupp hw, hmass]
  ring

end GaloisForLFunctions.ArithmeticElectrostatics
