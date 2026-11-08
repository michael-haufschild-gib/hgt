import GaloisForLFunctions.SurfaceOfSpecZ.NoMetricOnTheProjectiveLineCarriesTheJets

/-!
# The point count of `Spec ℤ` and the Hasse–Weil test for its Frobenius graphs

On `C × C` the diagonal meets the graph of `Fⁿ` in `N_n = #C(𝔽_{qⁿ})` points, the trace is
`a_n = qⁿ + 1 − N_n`, and the Castelnuovo–Severi defect on the plane `⟨Δ, Γ_{Fⁿ}⟩` is the genus form
`g y² − a_n x y + g qⁿ x²`, nonnegative iff `|a_n| ≤ 2g q^{n/2}` (Hasse–Weil).

For `Spec ℤ` the intersection of `Γ_1` with `Γ_n` (`TheTwoHalfProducts`) is

  `N(n) = Γ_1 · Γ_n = Λ(n) + 1 + 1/(n² − 1)`   (`pointCount_eq`):

the prime `p` if `n = pᵏ`, one `𝔽₁`-cusp, and the jets of the trivial zeros. The `𝔽₁`-model `ℙ¹` has
`n + 1` points. The trace is `a(n) = n + 1 − N(n) = n − Λ(n) − 1/(n² − 1)` (`trace_eq`).

With a diagonal of finite genus `g`, `Γ_n² = 2gn·`(normalization), the defect on `y Γ_1 − x Γ_n` is
`2g y² − 2a(n) x y + 2g n x²`, nonnegative exactly when `a(n)² ≤ 4g² n` (`twoTermDefect_nonneg_iff`). Since
`a(n) ≥ n − log n − 1`, every finite genus fails for all large `n` (`exists_twoTermDefect_neg`):
`Spec ℤ` has `log p` points over `𝔽_{1^p}` where a curve of genus `g` would need `p + 1 − O(g√p)`,
so the genus of the surface with atomic Frobenius graphs is infinite. A smoothing of the atoms by a
test function performs the prime number theorem on average — it spreads the `log p` points into a
density that cancels the pole term `n` — and only then can the trace be `O(√n)`.

**The jets.** The term `1 + 1/(n² − 1) = 1/(1 − n^{−2})` is the even-sector Lefschetz trace of the
dilation `x ↦ n x` of `ℝ` at its fixed point: with `λ = eᵘ`, the full trace is `λ^{1/2}/(λ − 1)` and the
trace twisted by `x ↦ −x` is `λ^{1/2}/(λ + 1)`; half their sum is the archimedean Lévy density
(`archLevyDensity_eq_even_trace`). The odd sector carries the trivial zeros `−2k − 1` of odd Dirichlet
`L`-functions.
-/

open Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticEffectivityTheory

/-- The number of points of `Spec ℤ` over `𝔽_{1ⁿ}`: the intersection `Γ_1 · Γ_n`. -/
def pointCount (n : ℕ) : ℝ := frobeniusIntersection 1 n

/-- The trace of the Frobenius of degree `n`: `n + 1 − N(n)`. -/
def trace (n : ℕ) : ℝ := n + 1 - pointCount n

/-- **The point count**: the prime, one cusp, and the jets. -/
theorem pointCount_eq {n : ℕ} (hn : 2 ≤ n) :
    pointCount n = Λ n + 1 + 1 / ((n : ℝ) ^ 2 - 1) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [pointCount, frobeniusIntersection_eq one_pos (by omega) (by omega),
    orbitIntersection_eq one_pos (by omega) (by omega), if_neg (fun h => by
      have := Nat.le_of_dvd one_pos h; omega), if_pos (one_dvd n), gcdTwist_of_coprime
      (Nat.coprime_one_left n)]
  have hmin : min ((1 : ℕ) : ℝ) n = 1 := by push_cast; exact min_eq_left (by linarith)
  have hmax : max ((1 : ℕ) : ℝ) n = n := by push_cast; exact max_eq_right (by linarith)
  rw [hmin, hmax, Nat.totient_one, Nat.div_one]
  have hsq : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The trace: `a(n) = n − Λ(n) − 1/(n² − 1)`. -/
theorem trace_eq {n : ℕ} (hn : 2 ≤ n) : trace n = n - Λ n - 1 / ((n : ℝ) ^ 2 - 1) := by
  rw [trace, pointCount_eq hn]; ring

/-- The defect of `y Γ_1 − x Γ_n` with a diagonal of genus `g`. -/
def twoTermDefect (g : ℝ) (n : ℕ) (x y : ℝ) : ℝ :=
  2 * g * y ^ 2 - 2 * trace n * x * y + 2 * g * n * x ^ 2

/-- **The Hasse–Weil test**: the two-term defect is nonnegative iff `a(n)² ≤ 4 g² n`. -/
theorem twoTermDefect_nonneg_iff {g : ℝ} (hg : 0 < g) {n : ℕ} (hn : 0 < n) :
    (∀ x y : ℝ, 0 ≤ twoTermDefect g n x y) ↔ trace n ^ 2 ≤ 4 * g ^ 2 * n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    -- the probe `x = 1`, `y = a(n)/(2g)` is negative
    have := h 1 (trace n / (2 * g))
    unfold twoTermDefect at this
    have hval : 2 * g * (trace n / (2 * g)) ^ 2 - 2 * trace n * 1 * (trace n / (2 * g)) +
        2 * g * n * 1 ^ 2 = (4 * g ^ 2 * n - trace n ^ 2) / (2 * g) := by
      field_simp; ring
    rw [hval] at this
    have : (4 * g ^ 2 * n - trace n ^ 2) / (2 * g) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith
  · intro h x y
    unfold twoTermDefect
    have hsq : 0 ≤ (2 * g * y - trace n * x) ^ 2 := sq_nonneg _
    have hx : 0 ≤ (4 * g ^ 2 * n - trace n ^ 2) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have key : 2 * g * (2 * g * y ^ 2 - 2 * trace n * x * y + 2 * g * n * x ^ 2) =
        (2 * g * y - trace n * x) ^ 2 + (4 * g ^ 2 * n - trace n ^ 2) * x ^ 2 := by ring
    nlinarith [key, hsq, hx, hg]

/-- The trace grows like `n`: `a(n) ≥ n − log n − 1`. -/
theorem trace_ge {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) - Real.log n - 1 ≤ trace n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [trace_eq hn]
  have hΛ : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have hj : 1 / ((n : ℝ) ^ 2 - 1) ≤ 1 := by
    rw [div_le_one (by nlinarith)]; nlinarith
  linarith

/-- **No finite genus.** For every genus `g` the two-term defect is indefinite for all large `n`. -/
theorem exists_twoTermDefect_neg {g : ℝ} (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, ∃ x y : ℝ, twoTermDefect g n x y < 0 := by
  rw [eventually_atTop]
  refine ⟨max 2 ⌈(2 * g + 3) ^ 2⌉₊, fun n hn => ?_⟩
  have h2 : 2 ≤ n := le_of_max_le_left hn
  have hN : (2 * g + 3) ^ 2 ≤ (n : ℝ) := Nat.ceil_le.mp (le_of_max_le_right hn)
  set t := Real.sqrt n with ht
  have htn : t ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htg : 2 * g + 3 ≤ t := (Real.le_sqrt (by positivity) (Nat.cast_nonneg n)).mpr hN
  -- `log n = 2 log t ≤ 2t − 2`
  have hlog : Real.log n ≤ 2 * t - 2 := by
    have hpos : 0 < t := by linarith
    have := Real.log_le_sub_one_of_pos hpos
    rw [← htn, Real.log_pow]; push_cast; linarith
  have hbig : 2 * g * t < trace n := by
    have := trace_ge h2
    nlinarith
  have hfail : ¬ trace n ^ 2 ≤ 4 * g ^ 2 * n := by
    intro hle
    have h0 : 0 ≤ 2 * g * t := by positivity
    have : (2 * g * t) ^ 2 < trace n ^ 2 := by nlinarith
    nlinarith
  by_contra hall
  push Not at hall
  exact hfail ((twoTermDefect_nonneg_iff hg (by omega)).mp hall)

/-! ### The jets as the even trace of the dilation -/

/-- **The jets are the even-sector trace of the dilation of `ℝ`**: for `u > 0`, half the sum of
`e^{u/2}/(eᵘ − 1)` (the trace of `x ↦ eᵘ x`) and `e^{u/2}/(eᵘ + 1)` (twisted by `x ↦ −x`) is the
archimedean Lévy density. -/
theorem archLevyDensity_eq_even_trace {u : ℝ} (hu : 0 < u) :
    RHTower.archLevyDensity u =
      (Real.exp (u / 2) / (Real.exp u - 1) + Real.exp (u / 2) / (Real.exp u + 1)) / 2 := by
  set E := Real.exp (u / 2) with hE
  have hE1 : 1 < E := Real.one_lt_exp_iff.mpr (by linarith)
  have he : Real.exp u = E ^ 2 := by
    rw [hE, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hm : Real.exp (-u / 2) = E⁻¹ := by
    rw [hE, ← Real.exp_neg]; congr 1; ring
  have hm2 : Real.exp (-2 * u) = (E ^ 4)⁻¹ := by
    rw [hE, ← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  unfold RHTower.archLevyDensity
  rw [hm, hm2, he]
  have h0 : 0 < E := by linarith
  have h2 : E ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : E ^ 2 + 1 ≠ 0 := by positivity
  have h4 : E ^ 4 - 1 ≠ 0 := by
    have : 1 < E ^ 2 := by nlinarith
    nlinarith [this]
  rw [show (1 : ℝ) - (E ^ 4)⁻¹ = (E ^ 4 - 1) / E ^ 4 by field_simp]
  field_simp
  ring

end GaloisForLFunctions.SurfaceOfSpecZ
