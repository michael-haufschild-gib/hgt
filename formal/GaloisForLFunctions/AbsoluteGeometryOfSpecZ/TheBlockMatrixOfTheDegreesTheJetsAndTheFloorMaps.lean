import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The block matrix of the degrees, the jets and the floor maps

The blocks are the integer intervals `(a, a + 1]`, `a ≥ 1`. On them four elementary matrices are
defined, and their combination

  `blockMatrix Q a b = d(a) + d(b) + δ_{ab} ϱ(a) − J(a, b) − C_Q(a, b)`

is the matrix of Weil's form `𝔚_Q` on step packets (proved in the module on the matrix of a step
packet). The four parts:

* **degrees** `d(a) = log((a + 1)/a)` (`blockDegree`): the pole plane, `d ⊗ 1 + 1 ⊗ d`;
* **density** `ϱ(a) = ∫_a^{a+1} log(x/2π) dx + 1 − γ` (`blockDensity`), on the diagonal: the
  counterterm of the comb;
* **jets** `J(a, b) = ½(D(a + b + 1) + D(|b − a|))` (`blockJet`), with `D` the second difference of
  `n log n` (`xLogXDiff`);
* **contacts** `C_Q(a, b) = Σ_{k ≤ Q} (Λ(k)/k)·[⌊b/k⌋ = a]`, `a ≤ b` (`floorContact`): the graphs
  of the floor maps `b ↦ ⌊b/k⌋`. The block `b` lies in the `k`-fold dilate of the block `a` iff
  `⌊b/k⌋ = a`; for a prime `p` the maps `b ↦ ⌊b/p^j⌋` are the ancestors in the `p`-ary tree on
  the integers.

`windowClosed Q a b` is the closed form of `𝔚_Q` on the flat packet of the window `(a, b]`, and
the block matrix is its mixed second difference (`windowClosed_mixed`), with the diagonal
`windowClosed Q a (a + 1)` (`windowClosed_succ`).

A quadratic form whose matrix is entrywise within `ε` of a symmetric matrix `q`, and not below it
on the diagonal, is at least the form of `q` minus `ε J Σ σ_j²` (`sum_sum_mul_ge_of_close`).
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The four parts -/

/-- `n log n`. -/
def xLogX (n : ℕ) : ℝ := n * Real.log n

/-- The second difference of `n log n` at `n`; it vanishes at `n = 0`. -/
def xLogXDiff (n : ℕ) : ℝ := xLogX (n + 1) - 2 * xLogX n + xLogX (n - 1)

theorem xLogXDiff_zero : xLogXDiff 0 = 0 := by
  simp [xLogXDiff, xLogX]

/-- The degree of the block `(a, a + 1]`: the integral of `dx/x` over it. -/
def blockDegree (a : ℕ) : ℝ := Real.log ((a + 1 : ℕ) : ℝ) - Real.log a

/-- The density term of the block `(a, a + 1]`: the integral of `log(x/2π)` over it, plus
`1 − γ`. -/
def blockDensity (a : ℕ) : ℝ :=
  xLogX (a + 1) - xLogX a - (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))

/-- The jets between the blocks `(a, a + 1]` and `(b, b + 1]`, `a ≤ b`. -/
def blockJet (a b : ℕ) : ℝ := (xLogXDiff (a + b + 1) + xLogXDiff (b - a)) / 2

/-- The contacts between the blocks `a ≤ b`: the graphs of the floor maps `b ↦ ⌊b/k⌋`, `k ≤ Q`,
with the weights `Λ(k)/k`. -/
def floorContact (Q a b : ℕ) : ℝ := ∑ k ∈ Icc 2 Q, if b / k = a then (Λ k : ℝ) / k else 0

/-- The block matrix: degrees, density on the diagonal, minus jets, minus contacts. -/
def blockMatrix (Q a b : ℕ) : ℝ :=
  blockDegree a + blockDegree b + (if a = b then blockDensity a else 0) -
    blockJet (min a b) (max a b) - floorContact Q (min a b) (max a b)

theorem blockMatrix_comm (Q a b : ℕ) : blockMatrix Q a b = blockMatrix Q b a := by
  unfold blockMatrix
  rw [min_comm a b, max_comm a b]
  by_cases h : a = b
  · subst h
    rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    ring

theorem blockMatrix_of_lt {a b : ℕ} (hab : a < b) (Q : ℕ) :
    blockMatrix Q a b = blockDegree a + blockDegree b - blockJet a b - floorContact Q a b := by
  rw [blockMatrix, if_neg hab.ne, min_eq_left hab.le, max_eq_right hab.le, add_zero]

/-- No block of positive index is its own image under a floor map. -/
theorem floorContact_self {a : ℕ} (ha : 1 ≤ a) (Q : ℕ) : floorContact Q a a = 0 := by
  refine Finset.sum_eq_zero fun k hk => if_neg ?_
  exact (Nat.div_lt_self ha (Finset.mem_Icc.mp hk).1).ne

theorem blockMatrix_self {a : ℕ} (ha : 1 ≤ a) (Q : ℕ) :
    blockMatrix Q a a = 2 * blockDegree a + blockDensity a - blockJet a a := by
  rw [blockMatrix, if_pos rfl, min_self, max_self, floorContact_self ha]
  ring

/-! ### The closed form of a window -/

/-- Pole term and jets of the flat packet of the window `(a, b]`. -/
def windowSmooth (a b : ℝ) : ℝ :=
  2 * ((Real.log b - Real.log a) * (b - a)) -
    ((b - a) * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) + (b + a) * Real.log 2 +
      2 * a * Real.log a - (b + a) * Real.log (b + a) + (b - a) * Real.log (b - a))

/-- Weil's form `𝔚_Q` of the flat packet of the window `(a, b]` in closed form: pole term and
jets, minus the contacts of the window with its dilates. -/
def windowClosed (Q : ℕ) (a b : ℝ) : ℝ :=
  windowSmooth a b - 2 * ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * max (b / k - a) 0

theorem windowClosed_self {x : ℝ} (hx : 0 < x) (Q : ℕ) : windowClosed Q x x = 0 := by
  have hc : ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * max (x / k - x) 0 = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk1 : (1 : ℝ) ≤ k := by
      have := (Finset.mem_Icc.mp hk).1
      exact_mod_cast (by omega : 1 ≤ k)
    rw [max_eq_right (sub_nonpos.mpr (div_le_self hx.le hk1)), mul_zero]
  rw [windowClosed, hc, windowSmooth, show x + x = 2 * x by ring,
    Real.log_mul two_ne_zero hx.ne']
  ring

/-- The mixed second difference of pole term and jets, for an arbitrary function in place of
the logarithm. -/
theorem mixed_window_aux (L : ℝ → ℝ) (c t x y : ℝ) :
    ((2 * ((L (y + 1) - L x) * (y + 1 - x)) -
          ((y + 1 - x) * c + (y + 1 + x) * t + 2 * x * L x - (y + 1 + x) * L (y + 1 + x) +
            (y + 1 - x) * L (y + 1 - x))) +
        (2 * ((L y - L (x + 1)) * (y - (x + 1))) -
          ((y - (x + 1)) * c + (y + (x + 1)) * t + 2 * (x + 1) * L (x + 1) -
            (y + (x + 1)) * L (y + (x + 1)) + (y - (x + 1)) * L (y - (x + 1)))) -
        (2 * ((L y - L x) * (y - x)) -
          ((y - x) * c + (y + x) * t + 2 * x * L x - (y + x) * L (y + x) +
            (y - x) * L (y - x))) -
        (2 * ((L (y + 1) - L (x + 1)) * (y + 1 - (x + 1))) -
          ((y + 1 - (x + 1)) * c + (y + 1 + (x + 1)) * t + 2 * (x + 1) * L (x + 1) -
            (y + 1 + (x + 1)) * L (y + 1 + (x + 1)) +
            (y + 1 - (x + 1)) * L (y + 1 - (x + 1))))) / 2 =
      L (x + 1) - L x + (L (y + 1) - L y) -
        ((x + y + 1 + 1) * L (x + y + 1 + 1) - 2 * ((x + y + 1) * L (x + y + 1)) +
            (x + y) * L (x + y) +
          ((y - x + 1) * L (y - x + 1) - 2 * ((y - x) * L (y - x)) +
            (y - x - 1) * L (y - x - 1))) / 2 := by
  have e1 : y + 1 + x = x + y + 1 := by ring
  have e2 : y + (x + 1) = x + y + 1 := by ring
  have e3 : y + x = x + y := by ring
  have e4 : y + 1 + (x + 1) = x + y + 1 + 1 := by ring
  have e5 : y + 1 - x = y - x + 1 := by ring
  have e6 : y - (x + 1) = y - x - 1 := by ring
  have e7 : y + 1 - (x + 1) = y - x := by ring
  rw [e1, e2, e3, e4, e5, e6, e7]
  ring

/-- **Pole term and jets of two blocks**: the mixed second difference of `windowSmooth` at the
blocks `a < b` is the degrees minus the jets. -/
theorem windowSmooth_mixed {a b : ℕ} (hab : a < b) :
    (windowSmooth a ((b : ℝ) + 1) + windowSmooth ((a : ℝ) + 1) b - windowSmooth a b -
        windowSmooth ((a : ℝ) + 1) ((b : ℝ) + 1)) / 2 =
      blockDegree a + blockDegree b - blockJet a b := by
  have c1 : ((a + b + 1 + 1 : ℕ) : ℝ) = (a : ℝ) + b + 1 + 1 := by push_cast; ring
  have c2 : ((a + b + 1 : ℕ) : ℝ) = (a : ℝ) + b + 1 := by push_cast; ring
  have c3 : ((a + b : ℕ) : ℝ) = (a : ℝ) + b := by push_cast; ring
  have c4 : ((b - a + 1 : ℕ) : ℝ) = (b : ℝ) - a + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hab.le, Nat.cast_one]
  have c5 : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := Nat.cast_sub hab.le
  have c6 : ((b - a - 1 : ℕ) : ℝ) = (b : ℝ) - a - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hab.le, Nat.cast_one]
  have c7 : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
  have c8 : ((b + 1 : ℕ) : ℝ) = (b : ℝ) + 1 := by push_cast; ring
  simp only [windowSmooth]
  rw [mixed_window_aux Real.log (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))
    (Real.log 2) (a : ℝ) (b : ℝ)]
  simp only [blockDegree, blockJet, xLogXDiff, xLogX, Nat.add_sub_cancel, c1, c2, c3, c4, c5, c6,
    c7, c8]

/-- The mixed second difference of the overlap `(b/k − a)⁺` of a window with its `k`-fold
dilate is the graph of the floor map. -/
theorem max_mixed {k : ℕ} (hk : 1 ≤ k) (a b : ℕ) :
    max (((b : ℝ) + 1) / k - a) 0 + max ((b : ℝ) / k - ((a : ℝ) + 1)) 0 -
        max ((b : ℝ) / k - a) 0 - max (((b : ℝ) + 1) / k - ((a : ℝ) + 1)) 0 =
      if b / k = a then 1 / (k : ℝ) else 0 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hle : a ≤ b / k ↔ a * k ≤ b := Nat.le_div_iff_mul_le hk
  have hlt : b / k < a + 1 ↔ b < (a + 1) * k := Nat.div_lt_iff_lt_mul hk
  by_cases h1 : a * k ≤ b
  · have h1r : (a : ℝ) * k ≤ b := by exact_mod_cast h1
    have p1 : 0 ≤ ((b : ℝ) + 1) / k - a :=
      sub_nonneg.mpr ((le_div_iff₀ hk0).mpr (by linarith))
    have p3 : 0 ≤ (b : ℝ) / k - a := sub_nonneg.mpr ((le_div_iff₀ hk0).mpr h1r)
    by_cases h2 : b < (a + 1) * k
    · have hdiv : b / k = a := le_antisymm (Nat.lt_succ_iff.mp (hlt.mpr h2)) (hle.mpr h1)
      have h2r : (b : ℝ) + 1 ≤ ((a : ℝ) + 1) * k := by exact_mod_cast h2
      have p2 : (b : ℝ) / k - ((a : ℝ) + 1) ≤ 0 :=
        sub_nonpos.mpr ((div_le_iff₀ hk0).mpr (by linarith))
      have p4 : ((b : ℝ) + 1) / k - ((a : ℝ) + 1) ≤ 0 :=
        sub_nonpos.mpr ((div_le_iff₀ hk0).mpr h2r)
      rw [if_pos hdiv, max_eq_left p1, max_eq_right p2, max_eq_left p3, max_eq_right p4]
      field_simp
      ring
    · have hdiv : b / k ≠ a := fun h => h2 (hlt.mp (by omega))
      have h2r : ((a : ℝ) + 1) * k ≤ b := by exact_mod_cast not_lt.mp h2
      have p2 : 0 ≤ (b : ℝ) / k - ((a : ℝ) + 1) :=
        sub_nonneg.mpr ((le_div_iff₀ hk0).mpr h2r)
      have p4 : 0 ≤ ((b : ℝ) + 1) / k - ((a : ℝ) + 1) :=
        sub_nonneg.mpr ((le_div_iff₀ hk0).mpr (by linarith))
      rw [if_neg hdiv, max_eq_left p1, max_eq_left p2, max_eq_left p3, max_eq_left p4]
      ring
  · have hdiv : b / k ≠ a := fun h => h1 (hle.mp h.ge)
    have h1r : (b : ℝ) + 1 ≤ (a : ℝ) * k := by exact_mod_cast not_le.mp h1
    have p1 : ((b : ℝ) + 1) / k - a ≤ 0 := sub_nonpos.mpr ((div_le_iff₀ hk0).mpr h1r)
    have p2 : (b : ℝ) / k - ((a : ℝ) + 1) ≤ 0 :=
      sub_nonpos.mpr ((div_le_iff₀ hk0).mpr (by nlinarith))
    have p3 : (b : ℝ) / k - a ≤ 0 := sub_nonpos.mpr ((div_le_iff₀ hk0).mpr (by linarith))
    have p4 : ((b : ℝ) + 1) / k - ((a : ℝ) + 1) ≤ 0 :=
      sub_nonpos.mpr ((div_le_iff₀ hk0).mpr (by nlinarith))
    rw [if_neg hdiv, max_eq_right p1, max_eq_right p2, max_eq_right p3, max_eq_right p4]
    ring

/-- **The contacts of two blocks** are the graphs of the floor maps. -/
theorem contact_mixed (Q a b : ℕ) :
    ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * max (((b : ℝ) + 1) / k - a) 0 +
        ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * max ((b : ℝ) / k - ((a : ℝ) + 1)) 0 -
        ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * max ((b : ℝ) / k - a) 0 -
        ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * max (((b : ℝ) + 1) / k - ((a : ℝ) + 1)) 0 =
      floorContact Q a b := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, floorContact]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  rw [← mul_add, ← mul_sub, ← mul_sub, max_mixed hk1 a b]
  split_ifs
  · rw [mul_one_div]
  · rw [mul_zero]

/-- **The block matrix is the mixed second difference of the windows**, off the diagonal. -/
theorem windowClosed_mixed {a b : ℕ} (hab : a < b) (Q : ℕ) :
    (windowClosed Q a ((b : ℝ) + 1) + windowClosed Q ((a : ℝ) + 1) b - windowClosed Q a b -
        windowClosed Q ((a : ℝ) + 1) ((b : ℝ) + 1)) / 2 = blockMatrix Q a b := by
  have h1 := windowSmooth_mixed hab
  have h2 := contact_mixed Q a b
  rw [blockMatrix_of_lt hab]
  simp only [windowClosed]
  linarith

/-- **The diagonal of the block matrix** is the form of the flat packet of one block. -/
theorem windowClosed_succ {a : ℕ} (ha : 1 ≤ a) (Q : ℕ) :
    windowClosed Q a ((a : ℝ) + 1) = blockMatrix Q a a := by
  have hx : (0 : ℝ) < a := by exact_mod_cast ha
  have hc : ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * max (((a : ℝ) + 1) / k - a) 0 = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    rw [max_eq_right (sub_nonpos.mpr ((div_le_iff₀ (by linarith)).mpr (by nlinarith))), mul_zero]
  have l1 : Real.log ((a : ℝ) + 1 - a) = 0 := by
    rw [add_sub_cancel_left]
    exact Real.log_one
  have l2 : Real.log ((a + a + 1 + 1 : ℕ) : ℝ) = Real.log 2 + Real.log ((a : ℝ) + 1) := by
    rw [show ((a + a + 1 + 1 : ℕ) : ℝ) = 2 * ((a : ℝ) + 1) by push_cast; ring,
      Real.log_mul two_ne_zero (by positivity)]
  have l3 : Real.log ((a + a : ℕ) : ℝ) = Real.log 2 + Real.log a := by
    rw [show ((a + a : ℕ) : ℝ) = 2 * (a : ℝ) by push_cast; ring,
      Real.log_mul two_ne_zero hx.ne']
  have l4 : Real.log ((a + a + 1 : ℕ) : ℝ) = Real.log ((a : ℝ) + 1 + a) := by
    congr 1
    push_cast
    ring
  have c7 : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
  rw [windowClosed, hc, blockMatrix_self ha, blockJet, Nat.sub_self, xLogXDiff_zero]
  simp only [windowSmooth, blockDegree, blockDensity, xLogXDiff, xLogX, Nat.add_sub_cancel, l1,
    l2, l3, l4, c7]
  push_cast
  ring

/-! ### A matrix close to a table -/

/-- A quadratic form whose matrix `e` is within `ε` of a symmetric table `q` off the diagonal and
not below it on the diagonal is at least the form of `q` minus `ε J Σ σ_j²`. -/
theorem sum_sum_mul_ge_of_close {J : ℕ} (σ : ℕ → ℝ) (e q : ℕ → ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ j l, e j l = e l j) (hq : ∀ j l, q j l = q l j)
    (hd : ∀ j, j < J → q j j ≤ e j j)
    (ho : ∀ j l, j < l → l < J → |e j l - q j l| ≤ ε) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * q j l - ε * J * ∑ j ∈ range J, σ j ^ 2 ≤
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * e j l := by
  have ho' : ∀ j ∈ range J, ∀ l ∈ range J, j ≠ l → |e j l - q j l| ≤ ε := by
    intro j hj l hl hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact ho j l h (Finset.mem_range.mp hl)
    · rw [he j l, hq j l]
      exact ho l j h (Finset.mem_range.mp hj)
  have hterm : ∀ j ∈ range J, ∀ l ∈ range J,
      σ j * σ l * q j l - ε / 2 * (σ j ^ 2 + σ l ^ 2) ≤ σ j * σ l * e j l := by
    intro j hj l hl
    by_cases hjl : j = l
    · subst hjl
      have h1 := mul_nonneg (sub_nonneg.mpr (hd j (Finset.mem_range.mp hj))) (sq_nonneg (σ j))
      have h2 := mul_nonneg hε (sq_nonneg (σ j))
      linarith
    · have h := abs_le.mp (ho' j hj l hl hjl)
      have h1 := mul_nonneg (show 0 ≤ ε + (e j l - q j l) by linarith) (sq_nonneg (σ j + σ l))
      have h2 := mul_nonneg (show 0 ≤ ε - (e j l - q j l) by linarith) (sq_nonneg (σ j - σ l))
      linarith
  have hrow : ∀ j, ∑ l ∈ range J, ε / 2 * (σ j ^ 2 + σ l ^ 2) =
      ε / 2 * (J * σ j ^ 2 + ∑ l ∈ range J, σ l ^ 2) := fun j => by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hsum : ∑ j ∈ range J, ∑ l ∈ range J, ε / 2 * (σ j ^ 2 + σ l ^ 2) =
      ε * J * ∑ j ∈ range J, σ j ^ 2 := by
    rw [Finset.sum_congr rfl fun j _ => hrow j, ← Finset.mul_sum, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hle := Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun l hl => hterm j hj l hl
  simp only [Finset.sum_sub_distrib] at hle
  rw [hsum] at hle
  exact hle

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
