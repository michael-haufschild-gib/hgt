import GaloisForLFunctions.WindowTowerOfSpecZ.TheAtomicLatticeOfAWindow
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTowerOfSmallExtensions
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheThetaH0OfSpecZ

/-!
# The Arakelov bundle of a window

The atomic lattice of a window of level `N` (atoms `b_m`, `m ≤ N`, of a profile with `‖φ‖ = 1`) is an
orthogonal sum of rank-one lattices: `⟨ι(δ_m), ι(δ_k)⟩ = δ_{mk}/m` (`integral_atomicEmbedding_single`).
The generator of the `m`-th summand has squared length `1/m`, so the summand is the Arakelov line
bundle `𝒪(½ log m)` on `Spec ℤ`: its Gaussian count at degree `d` is the theta `h⁰` of `Spec ℤ` at
`d + ½ log m` (`arithH0_add_half_log`, AOG `arithH0`). The window carries the Arakelov bundle

`ℰ_N = ⊕_{m ≤ N} 𝒪(½ log m)`, rank `N = ⌊e^A⌋`, `h⁰(ℰ_N, d) = Σ_{m ≤ N} h⁰_ℤ(d + ½ log m)`
(`windowBundleH0`).

* **Riemann–Roch for the window bundle** (`windowBundleH0_riemannRoch`):
  `h⁰(ℰ_N, d) − h⁰(ℰ_N^∨, −d) = N d + ½ log N!`, from Poisson summation on each summand.
* **Degree and slope** (`windowBundle_slope_le`): `deg ℰ_N = ½ log N!`, and the slope
  `deg/rank ≤ ½ log N ≤ A/2`: the window lattice has slope at most half the window length.

The Gamma factor enters as the Gaussian (theta) metric of `Spec ℤ` on each atom; the arithmetic of
the window acts on this bundle by the regular representation of the truncated Dirichlet ring.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticOrientationGeometry

variable {N : ℕ} {φ : ℝ → ℝ} {δ : ℝ}

/-- **The atomic lattice is an orthogonal sum**: `⟨ι(δ_m), ι(δ_k)⟩ = ‖φ‖²·δ_{mk}/m`. -/
theorem integral_atomicEmbedding_single (hφ : IsAtomProfile N δ φ) (hc : Continuous φ)
    {m k : ℕ} (hm : m ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) :
    ∫ u, atomicEmbedding N φ (single m 1) u * atomicEmbedding N φ (single k 1) u =
      if m = k then (∫ v, φ v ^ 2) / m else 0 := by
  rw [integral_atomicEmbedding_mul hφ hc]
  have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
  split_ifs with hmk
  · subst hmk
    rw [Finset.sum_eq_single_of_mem m hm fun j _ hj => by
      rw [single_apply, if_neg fun h => hj h.1, zero_mul, zero_div]]
    rw [single_apply_self hm0, one_mul, mul_div_assoc', mul_one]
  · rw [Finset.sum_eq_zero fun j _ => by
      rw [single_apply, single_apply]
      by_cases h1 : j = m
      · rw [if_neg fun h => hmk (h1.symm.trans h.1), mul_zero, zero_div]
      · rw [if_neg fun h => h1 h.1, zero_mul, zero_div], mul_zero]

/-- The summand `𝒪(½ log m)`: its Gaussian count at degree `d` is the theta count of the rank-one
lattice with generator of squared length `1/m`. -/
theorem arithH0_add_half_log {m : ℕ} (hm : 1 ≤ m) (d : ℝ) :
    arithH0 (d + Real.log m / 2) = Real.log (thetaSum (Real.exp (-2 * d) / m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [arithH0, show -2 * (d + Real.log m / 2) = -2 * d + -Real.log m by ring, Real.exp_add,
    Real.exp_neg, Real.exp_log hm0, div_eq_mul_inv]

/-- **The `h⁰` of the window bundle** `ℰ_N = ⊕_{m ≤ N} 𝒪(½ log m)`. -/
def windowBundleH0 (N : ℕ) (d : ℝ) : ℝ := ∑ m ∈ Finset.Icc 1 N, arithH0 (d + Real.log m / 2)

/-- The `h⁰` of the dual bundle `ℰ_N^∨ = ⊕_{m ≤ N} 𝒪(−½ log m)`. -/
def windowBundleDualH0 (N : ℕ) (d : ℝ) : ℝ := ∑ m ∈ Finset.Icc 1 N, arithH0 (d - Real.log m / 2)

theorem windowBundleH0_nonneg (N : ℕ) (d : ℝ) : 0 ≤ windowBundleH0 N d :=
  Finset.sum_nonneg fun m _ => Real.log_nonneg (one_le_thetaSum (Real.exp_pos _))

/-- `log N! = Σ_{m ≤ N} log m`. -/
theorem log_factorial_eq_sum (N : ℕ) : Real.log N.factorial = ∑ m ∈ Finset.Icc 1 N, Real.log m := by
  rw [← Finset.prod_Icc_id_eq_factorial, Nat.cast_prod, Real.log_prod]
  intro m hm
  have := (Finset.mem_Icc.mp hm).1
  exact_mod_cast (by omega : m ≠ 0)

/-- **Riemann–Roch for the window bundle**: `h⁰(ℰ_N, d) − h⁰(ℰ_N^∨, −d) = N d + ½ log N!`. -/
theorem windowBundleH0_riemannRoch (N : ℕ) (d : ℝ) :
    windowBundleH0 N d - windowBundleDualH0 N (-d) = N * d + Real.log N.factorial / 2 := by
  rw [windowBundleH0, windowBundleDualH0, ← Finset.sum_sub_distrib]
  have h : ∀ m ∈ Finset.Icc 1 N, arithH0 (d + Real.log m / 2) - arithH0 (-d - Real.log m / 2) =
      d + Real.log m / 2 := fun m _ => by
    rw [show -d - Real.log m / 2 = -(d + Real.log m / 2) by ring, arithH0_riemannRoch]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul, ← Finset.sum_div, ← log_factorial_eq_sum]
  simp

/-- **The slope of the window bundle is at most half the window length**:
`deg ℰ_N / rank ≤ ½ log N ≤ A/2` for `N = ⌊e^A⌋ ≥ 1`. -/
theorem windowBundle_slope_le {A : ℝ} (hN : 1 ≤ windowLevel A) :
    Real.log (windowLevel A).factorial / 2 ≤ windowLevel A * (A / 2) := by
  set N := windowLevel A
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogN : Real.log N ≤ A :=
    (Real.log_le_iff_le_exp hN0).mpr (Nat.floor_le (Real.exp_pos A).le)
  have hfac : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast Nat.factorial_le_pow N
  have hlog : Real.log N.factorial ≤ N * Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast Nat.factorial_pos N) hfac
  nlinarith

end GaloisForLFunctions.WindowTowerOfSpecZ
