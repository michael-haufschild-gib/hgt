import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheDiamagneticInequality

/-!
# The gauge enters through non-ratio lags

Beyond the spacing the atoms overlap, and the prime sum of an atomic test reads every lag `log k`
that comes within the width of a log-ratio `log(n/m)`. This file writes the overlap calculus at an
arbitrary width and locates the gauge in it.

Let `f_x = Σ_{n ≤ N} x_n g(· − log n)` with a bump `g` supported in `[0, w]` and autocorrelation
`G(t) = ∫ g(v) g(v + t) dv`, and let `s_{mn} = log n − log m`.

* **The overlap Gram** (`integral_atomicTest_sq_eq_gram`): `‖f_x‖² = Σ_{m,n} x_m x_n G(−s_{mn})`.
* **The overlap calculus** (`primeSum_atomicTest_eq_lags`, `twistedPrimeSum_atomicTest_eq_lags`):
  `primeSum f_x = Σ_k Λ_k Σ_{m,n} x_m x_n (G(−log k − s_{mn}) + G(log k − s_{mn}))`, and the same with
  `ω(k) Λ_k` for a twin. A term is a **ratio lag** when `n = km` (resp. `m = kn`) and a
  **non-ratio lag** otherwise; `G` vanishes unless `|log(km/n)| ≤ w` (resp. `|log(kn/m)| ≤ w`).
* **The gauge defect lives on non-ratio lags** (`gaugeFactor_eq_zero_of_ratio`,
  `twistedPrimeSum_sub_primeSum_gauge_eq`): for a completely multiplicative sign gauge `ω`,
  `twistedPrimeSum ω f_x − primeSum f_{ωx} = Σ_k Λ_k Σ_{m,n} (ω(k) − ω(m)ω(n)) x_m x_n (…)`, and the
  factor `ω(k) − ω(m)ω(n)` vanishes on every ratio lag. Only non-ratio lags carry the gauge.
* **Below the spacing there are none** (`nonRatio_lag_vanishes_below_spacing`): for `w < δ_N`
  every non-ratio term vanishes, which recovers the conjugacy of the twins at atomic resolution.
* **Beyond it they exist** (`exists_nonRatio_pair`): for every `N ≥ 3` there are atoms
  `m < n ≤ N` with `n ≠ 2m` whose log-ratio is within `4δ_N` of the lag `log 2`.

So the arithmetic gauge becomes visible to the prime form exactly when a lag `log k` falls within
the width of a log-ratio that is not `log k` itself — at overlap ratio of order one. Combined with
the diamagnetic inequality, a form margin in `ζ`'s favour must use either the pole or these
non-ratio lags.
-/

noncomputable section

open MeasureTheory Finset RHTower
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### The overlap Gram and the overlap calculus -/

/-- **The overlap Gram**: `‖f_x‖² = Σ_{m,n} x_m x_n G(−(log n − log m))`. -/
theorem integral_atomicTest_sq_eq_gram (hg : Continuous g) (hgc : HasCompactSupport g) (N : ℕ)
    (x : ℕ → ℝ) :
    ∫ u, atomicTest N x g u ^ 2 =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * bumpCorr g (-(Real.log n - Real.log m)) := by
  have h := integral_atomicTest_mul_shift hg hgc N x 0
  simp only [add_zero, zero_sub] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => by simp [sq])

/-- The lag form of order `k`: `Σ_{m,n} x_m x_n (G(−log k − s_{mn}) + G(log k − s_{mn}))`. -/
def lagForm (g : ℝ → ℝ) (N k : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n *
    (bumpCorr g (-Real.log k - (Real.log n - Real.log m)) +
      bumpCorr g (Real.log k - (Real.log n - Real.log m)))

/-- The two Hecke pairings of an atomic test at the lag `log k` are its lag form. -/
theorem pairings_atomicTest_eq_lagForm (hg : Continuous g) (hgc : HasCompactSupport g) (N k : ℕ)
    (x : ℕ → ℝ) :
    (∫ t, atomicTest N x g t * atomicTest N x g (t - Real.log k)) +
        ∫ t, atomicTest N x g t * atomicTest N x g (t + Real.log k) = lagForm g N k x := by
  have h1 := integral_atomicTest_mul_shift hg hgc N x (-Real.log k)
  have h2 := integral_atomicTest_mul_shift hg hgc N x (Real.log k)
  simp only [← sub_eq_add_neg] at h1
  rw [h1, h2, lagForm, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- **The overlap calculus for `ζ`**: `primeSum f_x = Σ_k Λ_k · lagForm_k(x)`. -/
theorem primeSum_atomicTest_eq_lags (hg : Continuous g) (hgc : HasCompactSupport g) (N : ℕ)
    (x : ℕ → ℝ) :
    primeSum (atomicTest N x g) = ∑' k : ℕ, vonMangoldtAtom k * lagForm g N k x := by
  rw [primeSum]
  exact tsum_congr fun k => by rw [pairings_atomicTest_eq_lagForm hg hgc]

/-- **The overlap calculus for a twin**: `twistedPrimeSum ω f_x = Σ_k ω(k) Λ_k · lagForm_k(x)`. -/
theorem twistedPrimeSum_atomicTest_eq_lags (ω : ArithmeticFunction ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (N : ℕ) (x : ℕ → ℝ) :
    twistedPrimeSum ω (atomicTest N x g) =
      ∑' k : ℕ, ω k * vonMangoldtAtom k * lagForm g N k x := by
  rw [twistedPrimeSum]
  exact tsum_congr fun k => by rw [pairings_atomicTest_eq_lagForm hg hgc]

/-! ### The gauge factor -/

variable {ω : ArithmeticFunction ℝ}

/-- **The gauge factor vanishes on ratio lags**: if `n = km` or `m = kn`, then
`ω(k) = ω(m) ω(n)` for a completely multiplicative sign gauge. -/
theorem gaugeFactor_eq_zero_of_ratio (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) {k m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : n = k * m ∨ m = k * n) : ω k - ω m * ω n = 0 := by
  have hsq : ∀ a, 0 < a → ω a * ω a = 1 := fun a ha => by
    rcases hsign a ha with h | h <;> rw [h] <;> norm_num
  rcases h with rfl | rfl
  · rw [hω, show ω m * (ω k * ω m) = ω k * (ω m * ω m) by ring, hsq m hm, mul_one, sub_self]
  · rw [hω, show ω k * ω n * ω n = ω k * (ω n * ω n) by ring, hsq n hn, mul_one, sub_self]

/-- **The gauge defect identity**: the twin's lag form minus `ζ`'s lag form of the gauged weights
is the lag form weighted by the gauge factor `ω(k) − ω(m)ω(n)`. -/
theorem lagForm_gauge_defect (N k : ℕ) (x : ℕ → ℝ) :
    ω k * lagForm g N k x - lagForm g N k (fun n => ω n * x n) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (ω k - ω m * ω n) * x m * x n *
        (bumpCorr g (-Real.log k - (Real.log n - Real.log m)) +
          bumpCorr g (Real.log k - (Real.log n - Real.log m))) := by
  rw [lagForm, lagForm, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- **The gauge defect lives on non-ratio lags**: in the defect identity every ratio-lag term
carries the factor `ω(k) − ω(m)ω(n) = 0`; what remains are the non-ratio lags. -/
theorem twistedPrimeSum_sub_primeSum_gauge_eq (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (hg : Continuous g) (hgc : HasCompactSupport g)
    (N : ℕ) (x : ℕ → ℝ)
    (hsum : Summable fun k : ℕ => ω k * vonMangoldtAtom k * lagForm g N k x)
    (hsum' : Summable fun k : ℕ => vonMangoldtAtom k * lagForm g N k (fun n => ω n * x n)) :
    twistedPrimeSum ω (atomicTest N x g) - primeSum (atomicTest N (fun n => ω n * x n) g) =
      ∑' k : ℕ, vonMangoldtAtom k * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (ω k - ω m * ω n) * x m * x n *
          ((if m = k * n then 0 else bumpCorr g (-Real.log k - (Real.log n - Real.log m))) +
            (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m)))) := by
  rw [twistedPrimeSum_atomicTest_eq_lags ω hg hgc, primeSum_atomicTest_eq_lags hg hgc,
    ← hsum.tsum_sub hsum']
  refine tsum_congr fun k => ?_
  rw [show ω k * vonMangoldtAtom k * lagForm g N k x -
      vonMangoldtAtom k * lagForm g N k (fun n => ω n * x n) =
      vonMangoldtAtom k * (ω k * lagForm g N k x - lagForm g N k (fun n => ω n * x n)) by ring,
    lagForm_gauge_defect]
  congr 1
  refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
  have hm0 := (mem_Icc.mp hm).1
  have hn0 := (mem_Icc.mp hn).1
  by_cases h1 : m = k * n
  · rw [gaugeFactor_eq_zero_of_ratio hω hsign hm0 hn0 (Or.inr h1)]; ring
  by_cases h2 : n = k * m
  · rw [gaugeFactor_eq_zero_of_ratio hω hsign hm0 hn0 (Or.inl h2)]; ring
  rw [if_neg h1, if_neg h2]

/-! ### Non-ratio lags below and beyond the spacing -/

/-- **Below the spacing there are no non-ratio lags**: for `w < δ_N`, atoms `m, n ≤ N` and
`k ≥ 1`, the lag `log k` meets the log-ratio `log(n/m)` within the width only if `n = km`. -/
theorem nonRatio_lag_vanishes_below_spacing (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N k m n : ℕ} (hw : w < atomSpacing N) (hk : 1 ≤ k) (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N)
    (h : n ≠ k * m) : bumpCorr g (Real.log k - (Real.log n - Real.log m)) = 0 := by
  obtain ⟨hm1, hmN⟩ := mem_Icc.mp hm
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  refine bumpCorr_eq_zero hgsupp ?_
  have hkm : 1 ≤ k * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hlog : Real.log k - (Real.log n - Real.log m) = Real.log (k * m : ℕ) - Real.log n := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]; ring
  rw [hlog]
  have hδ := atomSpacing_pos (hn1.trans hnN)
  rcases lt_or_gt_of_ne h with hlt | hgt
  · -- `n < km`: the smaller atom `n` is at most `N`
    have := atomSpacing_le_log_sub hn1 hnN hlt
    rw [abs_of_pos (by linarith)]
    linarith
  · -- `km < n ≤ N`
    have := atomSpacing_le_log_sub (N := N) hkm (by omega) hgt
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith

/-- **Beyond the spacing non-ratio lags exist**: for `N ≥ 3` there are atoms `m < n ≤ N`,
`n ≠ 2m`, whose log-ratio lies within `4δ_N` of the lag `log 2`. -/
theorem exists_nonRatio_pair {N : ℕ} (hN : 3 ≤ N) :
    ∃ m n : ℕ, 1 ≤ m ∧ m < n ∧ n ≤ N ∧ n ≠ 2 * m ∧
      |Real.log 2 - (Real.log n - Real.log m)| ≤ 4 * atomSpacing N := by
  -- the largest odd atom `n = 2j + 1 ≤ N` and `m = j + 1`: `2m = n + 1`
  set j := (N - 1) / 2
  have hj1 : 1 ≤ j := by omega
  have hnN : 2 * j + 1 ≤ N := by omega
  have hNn : N ≤ 2 * (2 * j + 1) := by omega
  refine ⟨j + 1, 2 * j + 1, by omega, by omega, hnN, by omega, ?_⟩
  have hn0 : (0 : ℝ) < 2 * j + 1 := by positivity
  have hm0 : (0 : ℝ) < j + 1 := by positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : Real.log 2 - (Real.log ((2 * j + 1 : ℕ) : ℝ) - Real.log ((j + 1 : ℕ) : ℝ)) =
      Real.log (1 + 1 / (2 * j + 1)) := by
    push_cast
    rw [show Real.log 2 - (Real.log (2 * j + 1) - Real.log (j + 1)) =
        Real.log (2 * (j + 1) / (2 * j + 1)) by
      rw [Real.log_div (by positivity) hn0.ne', Real.log_mul (by norm_num) hm0.ne']; ring]
    congr 1
    field_simp
    ring
  have hpos : (0 : ℝ) ≤ 1 / (2 * j + 1) := by positivity
  rw [hlog, abs_of_nonneg (Real.log_nonneg (by linarith))]
  -- `log(1 + 1/n) ≤ 1/n ≤ 2/N ≤ 4 log(1 + 1/N)`
  have h1 : Real.log (1 + 1 / (2 * j + 1)) ≤ 1 / (2 * j + 1) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (2 * j + 1) by positivity)
    linarith
  have h2 : 1 / (2 * (N : ℝ)) ≤ atomSpacing N := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + 1 / N by positivity)
    have e : 1 - (1 + 1 / (N : ℝ))⁻¹ = 1 / (N + 1) := by field_simp; ring
    rw [e] at h
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have : 1 / (2 * (N : ℝ)) ≤ 1 / (N + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    unfold atomSpacing
    linarith
  have hNj : (N : ℝ) ≤ 2 * (2 * j + 1) := by exact_mod_cast hNn
  have h3 : 1 / (2 * (j : ℝ) + 1) ≤ 4 * (1 / (2 * N)) := by
    rw [div_le_iff₀ hn0]
    field_simp
    linarith
  linarith

/-! ### Finitely many lags -/

/-- **Only finitely many lags meet the atoms**: for `log k > log N + w` every lag form of order `k`
vanishes, since the log-ratios of atoms `≤ N` lie in `[−log N, log N]`. -/
theorem lagForm_eq_zero_of_log_lt (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {N k : ℕ} (hk : Real.log N + w < Real.log k) (x : ℕ → ℝ) : lagForm g N k x = 0 := by
  unfold lagForm
  refine sum_eq_zero fun m hm => sum_eq_zero fun n hn => ?_
  obtain ⟨hm1, hmN⟩ := mem_Icc.mp hm
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hlm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hln : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hmN' : Real.log m ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hmN)
  have hnN' : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hnN)
  rw [bumpCorr_eq_zero hgsupp (t := -Real.log k - (Real.log n - Real.log m)) (by
      rw [abs_of_neg (by linarith)]; linarith),
    bumpCorr_eq_zero hgsupp (t := Real.log k - (Real.log n - Real.log m)) (by
      rw [abs_of_pos (by linarith)]; linarith), add_zero, mul_zero]

/-- The lag sums of an atomic test are finite: their terms vanish beyond `k ≥ ⌈N e^w⌉ + 1`. -/
theorem summable_lagForm (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) (N : ℕ)
    (x : ℕ → ℝ) (c : ℕ → ℝ) : Summable fun k : ℕ => c k * lagForm g N k x := by
  refine summable_of_ne_finset_zero (s := range (⌈(N : ℝ) * Real.exp w⌉₊ + 1)) fun k hk => ?_
  simp only [mem_range, not_lt] at hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hbig : (N : ℝ) * Real.exp w < k := by
    have := Nat.le_ceil ((N : ℝ) * Real.exp w)
    have h2 : ((⌈(N : ℝ) * Real.exp w⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at h2
    linarith
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- no atoms
    subst hN
    simp [lagForm]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log N + w < Real.log k := by
    rw [← Real.log_exp w, ← Real.log_mul hN0.ne' (Real.exp_pos w).ne']
    exact Real.log_lt_log (by positivity) hbig
  rw [lagForm_eq_zero_of_log_lt hgsupp hw hlog, mul_zero]

/-- **The gauge defect identity, unconditionally**: the summability premises of
`twistedPrimeSum_sub_primeSum_gauge_eq` hold for every bump supported in `[0, w]`. -/
theorem twistedPrimeSum_sub_primeSum_gauge_eq_of_supp (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) (N : ℕ) (x : ℕ → ℝ) :
    twistedPrimeSum ω (atomicTest N x g) - primeSum (atomicTest N (fun n => ω n * x n) g) =
      ∑' k : ℕ, vonMangoldtAtom k * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (ω k - ω m * ω n) * x m * x n *
          ((if m = k * n then 0 else bumpCorr g (-Real.log k - (Real.log n - Real.log m))) +
            (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m)))) :=
  twistedPrimeSum_sub_primeSum_gauge_eq hω hsign hg hgc N x
    (summable_lagForm hgsupp hw N x fun k => ω k * vonMangoldtAtom k)
    (summable_lagForm hgsupp hw N _ fun k => vonMangoldtAtom k)

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
