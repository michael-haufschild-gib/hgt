import Mathlib
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares

/-!
# The Frobenius zonotope surface: the `𝔽₁`-model of the pole plane

Over `𝔽₁` the Frobenius of degree `n` is the power map `ψ_n(x) = xⁿ` of the torus `𝔾_m`. Its graph
`Γ_n : y = xⁿ` in `ℙ¹ × ℙ¹` has bidegree `(1, n)`, the bidegree of the Hecke cycle `T_n` of the
scaling surface. Two graphs `Γ_m, Γ_n` (`n < m`) meet

* at each of the two `𝔽₁`-points `0` and `∞` with multiplicity `min(m, n)`: `x^m − xⁿ` vanishes to
  order `n` at `0` (`rootMultiplicity_zero_X_pow_sub_X_pow`), and `∞` is symmetric;
* in the torus exactly at the `m − n` roots of unity of order dividing `m − n`
  (`torus_point_iff`, `card_nthRootsFinset_complex`);

so `Γ_m · Γ_n = 2 min(m, n) + |m − n| = m + n` (`two_mul_min_add_dist`): the Castelnuovo–Severi
defect of `ℙ¹ × ℙ¹` vanishes on the Frobenius span, the surface of a genus-zero curve.

**The zonotope surface.** Keeping only the torus points is Bernstein–Kushnirenko: the Newton
polygon of `y − xⁿ` is the segment from `(0, 1)` to `(n, 0)`, and two such segments span the
parallelogram of area `|m − n|` (`newtonSegment_det`). On Minkowski sums of Frobenius segments, with
the two coordinate segments as fibre classes (bidegree `(1, n)` again), the defect is

  `δ_Z(a) = 2 (Σ a_n)(Σ n a_n) − Σ a_m a_n |m − n| = 2 Σ_k (Σ_{n > k} a_n)²`

(`zonotopeDefect_eq`): twice a sum of squares of integer counts, the tails of the probe. This is the
Hodge index of the zonotope surface, proved by counting (`zonotopeDefect_nonneg`); on probes of total
mass zero the torus form is nonpositive (`torusForm_nonpos_of_sum_eq_zero`).

**The first archimedean channel.** Normalized by `√(mn)`, the cusp kernel is
`min(m, n)/√(mn) = e^{−|log m − log n|/2}` (`min_eq_sqrt_mul_exp`). This is the `k = 0` term of the
archimedean Lévy density `e^{−x/2}/(1 − e^{−2x}) = Σ_k e^{−(2k + ½)x}` of Weil's form, the channel of
the Gamma pole at `s = 0` (`archLevyDensity_eq_cusp_add`). The pole plane minus the torus count is
this channel: `2 cosh t − 2|sinh t| = 2 e^{−|t|}` (`two_cosh_sub_two_abs_sinh`).

So toric geometry over `𝔽₁` realizes the pole plane of the scaling surface and exactly one
archimedean channel, with Hodge index from lattice counts. It carries no prime and no trivial zero
`s = −2k`, `k ≥ 1`.
-/

open Polynomial Finset

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

/-! ### Two Frobenius graphs over `𝔽₁` -/

/-- `x^m − xⁿ = xⁿ (x^{m−n} − 1)` for `n ≤ m`. -/
theorem X_pow_sub_X_pow_of_le {R : Type*} [CommRing R] {m n : ℕ} (h : n ≤ m) :
    (X ^ m - X ^ n : R[X]) = X ^ n * (X ^ (m - n) - 1) := by
  rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h]

/-- **The cusp multiplicity.** The graphs `y = x^m` and `y = xⁿ`, `n < m`, meet at the `𝔽₁`-point
`x = 0` with multiplicity `n = min(m, n)`. -/
theorem rootMultiplicity_zero_X_pow_sub_X_pow {K : Type*} [Field K] {m n : ℕ} (h : n < m) :
    rootMultiplicity 0 (X ^ m - X ^ n : K[X]) = n := by
  have hk : 0 < m - n := Nat.sub_pos_of_lt h
  have hq : (X ^ (m - n) - 1 : K[X]) ≠ 0 := by
    intro h0
    have := congrArg (eval 0) h0
    simp [zero_pow hk.ne'] at this
  rw [X_pow_sub_X_pow_of_le h.le, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hq)]
  have h1 : rootMultiplicity 0 (X ^ n : K[X]) = n := by
    simpa using rootMultiplicity_X_sub_C_pow (0 : K) n
  have h2 : rootMultiplicity 0 (X ^ (m - n) - 1 : K[X]) = 0 :=
    rootMultiplicity_eq_zero (by simp [zero_pow hk.ne'])
  rw [h1, h2, add_zero]

/-- **The torus points.** A nonzero `x` lies on both graphs exactly when `x^{m−n} = 1`. -/
theorem torus_point_iff {K : Type*} [Field K] {m n : ℕ} (h : n ≤ m) {x : K} (hx : x ≠ 0) :
    x ^ m = x ^ n ↔ x ^ (m - n) = 1 := by
  have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx
  constructor
  · intro hmn
    have : x ^ n * x ^ (m - n) = x ^ n * 1 := by rw [← pow_add, Nat.add_sub_cancel' h, mul_one, hmn]
    exact mul_left_cancel₀ hxn this
  · intro h1
    rw [← Nat.add_sub_cancel' h, pow_add, h1, mul_one]

/-- Over `ℂ` there are exactly `k` roots of unity of order dividing `k`: the torus count. -/
theorem card_nthRootsFinset_complex {k : ℕ} (hk : 0 < k) :
    (nthRootsFinset k (1 : ℂ)).card = k :=
  (Complex.isPrimitiveRoot_exp k hk.ne').card_nthRootsFinset

/-- **The intersection count.** Two cusps of multiplicity `min(m, n)` and `|m − n|` torus points:
`Γ_m · Γ_n = m + n`, the bidegree pairing of `(1, m)` and `(1, n)`. -/
theorem two_mul_min_add_dist (m n : ℕ) : 2 * min m n + Nat.dist m n = m + n := by
  rcases le_total m n with h | h
  · rw [min_eq_left h, Nat.dist_eq_sub_of_le h]; omega
  · rw [min_eq_right h, Nat.dist_eq_sub_of_le_right h]; omega

/-- **Bernstein–Kushnirenko.** The Newton segments `(m, −1)` and `(n, −1)` of `y − x^m` and `y − xⁿ`
span a parallelogram of area `|m − n|`. -/
theorem newtonSegment_det (m n : ℤ) : |(m * (-1) - (-1) * n : ℤ)| = |m - n| := by
  rw [show m * (-1) - (-1) * n = -(m - n) by ring, abs_neg]

/-! ### Counts as squares -/

/-- The cusp multiplicity is a count: `min(m, n)` integers lie below both `m` and `n`. -/
theorem min_eq_sum_indicator {m n K : ℕ} (hm : m ≤ K) (hn : n ≤ K) :
    ((min m n : ℕ) : ℤ) =
      ∑ k ∈ range K, (if k < m then (1 : ℤ) else 0) * (if k < n then 1 else 0) := by
  have : ∀ k ∈ range K, ((if k < m then (1 : ℤ) else 0) * (if k < n then 1 else 0)) =
      if k < min m n then 1 else 0 := by
    intro k _
    by_cases h1 : k < m <;> by_cases h2 : k < n <;> simp [h1, h2]
  rw [sum_congr rfl this, ← sum_filter]
  have hfilt : (range K).filter (fun k => k < min m n) = range (min m n) := by
    ext k; simp only [mem_filter, mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨lt_of_lt_of_le h ((min_le_left _ _).trans hm), h⟩
  rw [hfilt]
  simp

variable (S : Finset ℕ) (a : ℕ → ℤ)

/-- The cusp form `Σ a_m a_n min(m, n)` of a probe supported on `S`. -/
def cuspForm : ℤ := ∑ m ∈ S, ∑ n ∈ S, a m * a n * ((min m n : ℕ) : ℤ)

/-- The torus form `Σ a_m a_n |m − n|`: the intersection form of the Frobenius zonotope surface. -/
def torusForm : ℤ := ∑ m ∈ S, ∑ n ∈ S, a m * a n * (Nat.dist m n : ℤ)

/-- The tail `Σ_{n ∈ S, n > k} a_n`: the number of Frobenius segments of slope index above `k`. -/
def tail (k : ℕ) : ℤ := ∑ n ∈ S, if k < n then a n else 0

/-- The two degrees of a probe: against the fibre classes, `Σ a_n` and `Σ n a_n`. -/
def degH : ℤ := ∑ n ∈ S, a n

def degV : ℤ := ∑ n ∈ S, (n : ℤ) * a n

/-- The Castelnuovo–Severi defect of the zonotope surface, `2 (x·H)(x·V) − x·x`. -/
def zonotopeDefect : ℤ := 2 * degH S a * degV S a - torusForm S a

/-- **The cusp form is a sum of squares of tails.** -/
theorem cuspForm_eq_sum_sq {K : ℕ} (hS : ∀ n ∈ S, n ≤ K) :
    cuspForm S a = ∑ k ∈ range K, tail S a k ^ 2 := by
  set F : ℕ → ℕ → ℤ := fun k n => if k < n then a n else 0 with hF
  have hexp : ∀ m ∈ S, ∀ n ∈ S, a m * a n * ((min m n : ℕ) : ℤ) =
      ∑ k ∈ range K, F k m * F k n := by
    intro m hm n hn
    rw [min_eq_sum_indicator (hS m hm) (hS n hn), mul_sum]
    refine sum_congr rfl fun k _ => ?_
    by_cases h1 : k < m <;> by_cases h2 : k < n <;> simp [hF, h1, h2]
  have hswap : ∀ m ∈ S, ∑ n ∈ S, ∑ k ∈ range K, F k m * F k n =
      ∑ k ∈ range K, ∑ n ∈ S, F k m * F k n := fun _ _ => sum_comm
  calc cuspForm S a = ∑ m ∈ S, ∑ n ∈ S, ∑ k ∈ range K, F k m * F k n :=
        sum_congr rfl fun m hm => sum_congr rfl fun n hn => hexp m hm n hn
    _ = ∑ k ∈ range K, ∑ m ∈ S, ∑ n ∈ S, F k m * F k n := by
        rw [sum_congr rfl hswap, sum_comm]
    _ = ∑ k ∈ range K, tail S a k ^ 2 := by
        refine sum_congr rfl fun k _ => ?_
        rw [sq, tail, sum_mul_sum]

/-- The cusp form is nonnegative. -/
theorem cuspForm_nonneg : 0 ≤ cuspForm S a := by
  obtain ⟨K, hK⟩ : ∃ K, ∀ n ∈ S, n ≤ K := ⟨S.sup id, fun n hn => le_sup (f := id) hn⟩
  rw [cuspForm_eq_sum_sq S a hK]
  exact sum_nonneg fun k _ => sq_nonneg _

/-- `|m − n| = m + n − 2 min(m, n)`. -/
theorem dist_eq_add_sub_two_min (m n : ℕ) :
    (Nat.dist m n : ℤ) = m + n - 2 * ((min m n : ℕ) : ℤ) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (two_mul_min_add_dist m n)
  push_cast at h ⊢
  linarith

/-- **The torus form**: bidegree pairing minus twice the cusp form. -/
theorem torusForm_eq : torusForm S a = 2 * degH S a * degV S a - 2 * cuspForm S a := by
  have hpt : ∀ m n : ℕ, a m * a n * (Nat.dist m n : ℤ) =
      a n * ((m : ℤ) * a m) + a m * ((n : ℤ) * a n) -
        2 * (a m * a n * ((min m n : ℕ) : ℤ)) := by
    intro m n; rw [dist_eq_add_sub_two_min]; ring
  have h1 : ∑ m ∈ S, ∑ n ∈ S, a n * ((m : ℤ) * a m) =
      (∑ n ∈ S, a n) * ∑ m ∈ S, (m : ℤ) * a m := by
    rw [sum_mul_sum, sum_comm]
  have h2 : ∑ m ∈ S, ∑ n ∈ S, a m * ((n : ℤ) * a n) =
      (∑ m ∈ S, a m) * ∑ n ∈ S, (n : ℤ) * a n := by
    rw [sum_mul_sum]
  have h3 : ∑ m ∈ S, ∑ n ∈ S, 2 * (a m * a n * ((min m n : ℕ) : ℤ)) = 2 * cuspForm S a := by
    rw [cuspForm, mul_sum]
    exact sum_congr rfl fun _ _ => (mul_sum _ _ _).symm
  unfold torusForm degH degV
  simp only [hpt, sum_sub_distrib, sum_add_distrib]
  rw [h1, h2, h3]
  ring

/-- **The defect of the zonotope surface is twice a sum of squares of integer counts.** -/
theorem zonotopeDefect_eq {K : ℕ} (hS : ∀ n ∈ S, n ≤ K) :
    zonotopeDefect S a = 2 * ∑ k ∈ range K, tail S a k ^ 2 := by
  rw [zonotopeDefect, torusForm_eq, cuspForm_eq_sum_sq S a hS]
  ring

/-- **Hodge index of the zonotope surface, by counting.** -/
theorem zonotopeDefect_nonneg : 0 ≤ zonotopeDefect S a := by
  rw [zonotopeDefect, torusForm_eq]
  linarith [cuspForm_nonneg S a]

/-- On probes of total mass zero (orthogonal to the fibre class `V`), the torus form is
nonpositive: `|m − n|` is a squared distance. -/
theorem torusForm_nonpos_of_sum_eq_zero (h : degH S a = 0) : torusForm S a ≤ 0 := by
  rw [torusForm_eq, h]
  linarith [cuspForm_nonneg S a]

/-! ### The normalized cusp kernel is the first archimedean channel -/

/-- `min(m, n) = √(mn) e^{−|log m − log n|/2}`. -/
theorem min_eq_sqrt_mul_exp {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    min m n = Real.sqrt (m * n) * Real.exp (-|Real.log m - Real.log n| / 2) := by
  wlog h : m ≤ n generalizing m n
  · rw [min_comm, mul_comm m n, abs_sub_comm]
    exact this hn hm (le_of_not_ge h)
  rw [min_eq_left h, abs_of_nonpos (by linarith [Real.log_le_log hm h])]
  have hexp : Real.exp (-(-(Real.log m - Real.log n)) / 2) = Real.sqrt (m / n) := by
    rw [show -(-(Real.log m - Real.log n)) / 2 = Real.log (m / n) / 2 by
      rw [Real.log_div hm.ne' hn.ne']; ring]
    rw [Real.sqrt_eq_rpow, ← Real.exp_log (div_pos hm hn), ← Real.exp_mul,
      Real.exp_log (div_pos hm hn)]
    ring_nf
  rw [hexp, ← Real.sqrt_mul (mul_pos hm hn).le, show m * n * (m / n) = m * m by field_simp,
    Real.sqrt_mul_self hm.le]

/-- **The pole plane minus the torus count is the first channel**: `2 cosh t − 2|sinh t| = 2e^{−|t|}`. -/
theorem two_cosh_sub_two_abs_sinh (t : ℝ) :
    2 * Real.cosh t - 2 * |Real.sinh t| = 2 * Real.exp (-|t|) := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr h), abs_of_nonneg h, Real.cosh_eq, Real.sinh_eq]
    ring
  · rw [abs_of_nonpos (Real.sinh_nonpos_iff.mpr h), abs_of_nonpos h, Real.cosh_eq, Real.sinh_eq]
    ring

/-- **The archimedean Lévy density is the cusp channel plus the trivial-zero channels**:
`e^{−x/2}/(1 − e^{−2x}) = e^{−x/2} + Σ_{k ≥ 1} e^{−(2k + ½)x}`. -/
theorem archLevyDensity_eq_cusp_add {x : ℝ} (hx : 0 < x) :
    RHTower.archLevyDensity x =
      Real.exp (-x / 2) + ∑' k : ℕ, Real.exp (-((2 * ((k + 1 : ℕ) : ℝ) + 1 / 2) * x)) := by
  have hsum : Summable fun k : ℕ => Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) := by
    have hr : Real.exp (-(2 * x)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    refine (summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left (Real.exp (-x / 2)) |>.congr
      fun k => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  rw [RHTower.archLevyDensity_eq_tsum hx, hsum.tsum_eq_zero_add]
  congr 1
  simp only [Nat.cast_zero, mul_zero, zero_add]
  ring_nf

end GaloisForLFunctions.SurfaceOfSpecZ
