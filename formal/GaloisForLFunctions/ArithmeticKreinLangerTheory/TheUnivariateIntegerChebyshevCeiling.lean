import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.MvPolynomial.Degrees
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheStepanovMethodOverZ

/-!
# The univariate integer Chebyshev ceiling

Integer polynomials on `[0, 1]` produce prime-counting bounds through the integrality floor
`log (1 / ∫₀¹ P) ≤ ψ(n + 1)` (`ArithmeticEffectivityTheory.log_inv_integral_le_psi`). Whenever the
size of `P` on `[0, 1]` is controlled by its uniform norm, the exponential decay rate is capped by
the integer Chebyshev constant `t_ℤ([0, 1])`: no nonzero `P ∈ ℤ[X]` of degree at most `n` can have
`sup_{x ∈ [0, 1]} |P(x)| ≤ exp(-(87/100) n)`.

**Mechanism (`exists_Ioo_gt_univariate_chebyshev_cap`).** Iterating the Gorshkov–Wirsing rational
map `R(u) = u(1 - u) / (1 - 3 u(1 - u))` produces integer polynomials `F_k = 2 p_k - q_k ∈ ℤ[X]`
of degree `2^k` whose root sets `Z_k = {x ∈ (0, 1) : R^[k](x) = 1/2}` have cardinality `2^k` and
are pairwise disjoint (`R(1/2) = 1`, `R(1) = 0`, `R(0) = 0`). The leading coefficients `b_k` satisfy
`81 b_{k+1} ≤ 89 b_k²` for `k ≥ 3`, whence `b_k ≤ (2.382)^{2^k} < exp((87/100) · 2^k)`. Given a
nonzero `P ∈ ℤ[X]` of degree at most `n`, `P` has at most `n` real roots, so by the pigeonhole
principle some `Z_k` (`0 ≤ k ≤ n`) contains no root of `P`. The integer resultant
`Res_{2^k, n}(F_k, P)` is then nonzero, so `1 ≤ b_k^n ∏_{α ∈ Z_k} |P(α)|`, forcing
`|P(α)| > exp(-(87/100) n)` at some `α ∈ Z_k ⊂ (0, 1)`.

Diagonal specialization `t ↦ (t, …, t)` extends the same bound to `[0, 1]^σ` for every
multivariate integer polynomial of total degree at most `n` with nonvanishing diagonal restriction
(`exists_cube_gt_of_mvPolynomial_totalDegree_le`).
-/

open Finset Polynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-! ### The Gorshkov–Wirsing rational map and its inverse branches -/

/-- The Gorshkov–Wirsing rational map `R(u) = u(1 - u) / (1 - 3 u(1 - u))` on `[0, 1]`. -/
def gorshkovMap (u : ℝ) : ℝ :=
  u * (1 - u) / (1 - 3 * u * (1 - u))

/-- Left inverse branch `L(y) = 1/2 - √((1 - y) / (4(1 + 3y)))`, mapping `(0, 1)` into `(0, 1/2)`. -/
def gorshkovLeftInv (y : ℝ) : ℝ :=
  1 / 2 - Real.sqrt ((1 - y) / (4 * (1 + 3 * y)))

/-- Right inverse branch `U(y) = 1/2 + √((1 - y) / (4(1 + 3y)))`, mapping `(0, 1)` into `(1/2, 1)`. -/
def gorshkovRightInv (y : ℝ) : ℝ :=
  1 / 2 + Real.sqrt ((1 - y) / (4 * (1 + 3 * y)))

theorem gorshkovMap_denom_ge_quarter (u : ℝ) : 1 / 4 ≤ 1 - 3 * u * (1 - u) := by
  nlinarith [sq_nonneg (2 * u - 1)]

theorem gorshkovMap_denom_pos (u : ℝ) : 0 < 1 - 3 * u * (1 - u) :=
  lt_of_lt_of_le (by norm_num) (gorshkovMap_denom_ge_quarter u)

theorem gorshkovMap_mem_Icc {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    gorshkovMap u ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := gorshkovMap_denom_pos u
  refine ⟨div_nonneg (mul_nonneg hu.1 (by linarith [hu.2])) hd.le, ?_⟩
  rw [gorshkovMap, div_le_one hd]
  nlinarith [sq_nonneg (2 * u - 1)]

theorem gorshkovIter_mem_Icc (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    gorshkovMap^[k] x ∈ Set.Icc (0 : ℝ) 1 := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact gorshkovMap_mem_Icc ih

@[simp] theorem gorshkovMap_zero : gorshkovMap 0 = 0 := by norm_num [gorshkovMap]

@[simp] theorem gorshkovMap_one : gorshkovMap 1 = 0 := by norm_num [gorshkovMap]

@[simp] theorem gorshkovMap_half : gorshkovMap (1 / 2) = 1 := by norm_num [gorshkovMap]

theorem gorshkovIter_zero (k : ℕ) : gorshkovMap^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, gorshkovMap_zero]

theorem gorshkovIter_half_succ_ne_half (j : ℕ) :
    gorshkovMap^[j + 1] (1 / 2 : ℝ) ≠ 1 / 2 := by
  rcases j with _ | i
  · norm_num [gorshkovMap]
  · rw [show i + 1 + 1 = i + 2 from rfl, Function.iterate_add_apply]
    have h2 : gorshkovMap^[2] (1 / 2 : ℝ) = 0 := by
      norm_num [Function.iterate_succ_apply', gorshkovMap]
    rw [h2, gorshkovIter_zero]
    norm_num

private lemma gorshkov_radicand_bounds {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    0 < (1 - y) / (4 * (1 + 3 * y)) ∧ (1 - y) / (4 * (1 + 3 * y)) < (1 / 2 : ℝ) ^ 2 := by
  have h1 : 0 < 1 - y := by linarith [hy.2]
  have h2 : 0 < 4 * (1 + 3 * y) := by linarith [hy.1]
  refine ⟨div_pos h1 h2, ?_⟩
  rw [div_lt_iff₀ h2]
  nlinarith [hy.1]

theorem gorshkovLeftInv_mem_Ioo {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    gorshkovLeftInv y ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
  obtain ⟨hpos, hlt⟩ := gorshkov_radicand_bounds hy
  have hspos : 0 < Real.sqrt ((1 - y) / (4 * (1 + 3 * y))) := Real.sqrt_pos.mpr hpos
  have hslt : Real.sqrt ((1 - y) / (4 * (1 + 3 * y))) < 1 / 2 :=
    (Real.sqrt_lt' (by norm_num)).mpr hlt
  exact ⟨by unfold gorshkovLeftInv; linarith, by unfold gorshkovLeftInv; linarith⟩

theorem gorshkovRightInv_mem_Ioo {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    gorshkovRightInv y ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
  obtain ⟨hpos, hlt⟩ := gorshkov_radicand_bounds hy
  have hspos : 0 < Real.sqrt ((1 - y) / (4 * (1 + 3 * y))) := Real.sqrt_pos.mpr hpos
  have hslt : Real.sqrt ((1 - y) / (4 * (1 + 3 * y))) < 1 / 2 :=
    (Real.sqrt_lt' (by norm_num)).mpr hlt
  exact ⟨by unfold gorshkovRightInv; linarith, by unfold gorshkovRightInv; linarith⟩

theorem gorshkovMap_leftInv {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    gorshkovMap (gorshkovLeftInv y) = y := by
  obtain ⟨hpos, _⟩ := gorshkov_radicand_bounds hy
  have hsq : Real.sqrt ((1 - y) / (4 * (1 + 3 * y))) ^ 2 = (1 - y) / (4 * (1 + 3 * y)) :=
    Real.sq_sqrt hpos.le
  have hd : (1 : ℝ) + 3 * y ≠ 0 := by linarith [hy.1]
  have h4d : 4 * (1 + 3 * y) ≠ 0 := by linarith [hy.1]
  have hprod : gorshkovLeftInv y * (1 - gorshkovLeftInv y) = y / (1 + 3 * y) := by
    unfold gorshkovLeftInv
    calc (1 / 2 - Real.sqrt ((1 - y) / (4 * (1 + 3 * y)))) *
          (1 - (1 / 2 - Real.sqrt ((1 - y) / (4 * (1 + 3 * y)))))
        = 1 / 4 - Real.sqrt ((1 - y) / (4 * (1 + 3 * y))) ^ 2 := by ring
      _ = 1 / 4 - (1 - y) / (4 * (1 + 3 * y)) := by rw [hsq]
      _ = y / (1 + 3 * y) := by
          rw [div_sub_div _ _ (by norm_num) h4d, div_eq_div_iff (by positivity) hd]
          ring
  have hden : 1 - 3 * (y / (1 + 3 * y)) = 1 / (1 + 3 * y) := by
    rw [← mul_div_assoc, one_sub_div hd]
    ring
  unfold gorshkovMap
  rw [show 3 * gorshkovLeftInv y * (1 - gorshkovLeftInv y) =
    3 * (gorshkovLeftInv y * (1 - gorshkovLeftInv y)) by ring, hprod, hden,
    div_div_eq_mul_div, div_one]
  exact div_mul_cancel₀ y hd

theorem gorshkovMap_rightInv {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    gorshkovMap (gorshkovRightInv y) = y := by
  obtain ⟨hpos, _⟩ := gorshkov_radicand_bounds hy
  have hsq : Real.sqrt ((1 - y) / (4 * (1 + 3 * y))) ^ 2 = (1 - y) / (4 * (1 + 3 * y)) :=
    Real.sq_sqrt hpos.le
  have hd : (1 : ℝ) + 3 * y ≠ 0 := by linarith [hy.1]
  have h4d : 4 * (1 + 3 * y) ≠ 0 := by linarith [hy.1]
  have hprod : gorshkovRightInv y * (1 - gorshkovRightInv y) = y / (1 + 3 * y) := by
    unfold gorshkovRightInv
    calc (1 / 2 + Real.sqrt ((1 - y) / (4 * (1 + 3 * y)))) *
          (1 - (1 / 2 + Real.sqrt ((1 - y) / (4 * (1 + 3 * y)))))
        = 1 / 4 - Real.sqrt ((1 - y) / (4 * (1 + 3 * y))) ^ 2 := by ring
      _ = 1 / 4 - (1 - y) / (4 * (1 + 3 * y)) := by rw [hsq]
      _ = y / (1 + 3 * y) := by
          rw [div_sub_div _ _ (by norm_num) h4d, div_eq_div_iff (by positivity) hd]
          ring
  have hden : 1 - 3 * (y / (1 + 3 * y)) = 1 / (1 + 3 * y) := by
    rw [← mul_div_assoc, one_sub_div hd]
    ring
  unfold gorshkovMap
  rw [show 3 * gorshkovRightInv y * (1 - gorshkovRightInv y) =
    3 * (gorshkovRightInv y * (1 - gorshkovRightInv y)) by ring, hprod, hden,
    div_div_eq_mul_div, div_one]
  exact div_mul_cancel₀ y hd

/-! ### The integer polynomial tower and its disjoint root sets -/

/-- Numerator and denominator polynomials `(p_k, q_k)` of `R^[k]`. -/
def gorshkovPQ : ℕ → ℤ[X] × ℤ[X]
  | 0 => (X, 1)
  | k + 1 =>
    let pq := gorshkovPQ k
    (pq.1 * (pq.2 - pq.1), pq.2 ^ 2 - 3 * pq.1 * (pq.2 - pq.1))

/-- The Gorshkov–Wirsing polynomial `F_k = 2 p_k - q_k ∈ ℤ[X]`. -/
def gorshkovPoly (k : ℕ) : ℤ[X] :=
  2 * (gorshkovPQ k).1 - (gorshkovPQ k).2

/-- The finite set `Z_k = R^{-k}(1/2) ⊂ (0, 1)` of `2^k` real roots of `F_k`. -/
def gorshkovRoots : ℕ → Finset ℝ
  | 0 => {1 / 2}
  | k + 1 =>
    (gorshkovRoots k).image gorshkovLeftInv ∪ (gorshkovRoots k).image gorshkovRightInv

theorem aeval_gorshkovPQ (k : ℕ) (x : ℝ) :
    0 < aeval x (gorshkovPQ k).2 ∧
      aeval x (gorshkovPQ k).1 = gorshkovMap^[k] x * aeval x (gorshkovPQ k).2 := by
  induction k with
  | zero => simp [gorshkovPQ]
  | succ k ih =>
    obtain ⟨hqpos, hp⟩ := ih
    set u := gorshkovMap^[k] x with hu_def
    have hd := gorshkovMap_denom_pos u
    simp only [gorshkovPQ, map_mul, map_sub, map_pow, map_ofNat]
    have hq2 : aeval x (gorshkovPQ k).2 ^ 2 -
        3 * aeval x (gorshkovPQ k).1 * (aeval x (gorshkovPQ k).2 - aeval x (gorshkovPQ k).1) =
        aeval x (gorshkovPQ k).2 ^ 2 * (1 - 3 * u * (1 - u)) := by
      rw [hp]; ring
    rw [hq2]
    refine ⟨mul_pos (pow_pos hqpos 2) hd, ?_⟩
    rw [hp, Function.iterate_succ_apply', ← hu_def, gorshkovMap,
      div_mul_eq_mul_div, eq_div_iff hd.ne']
    ring

theorem aeval_gorshkovPoly_eq_zero_iff (k : ℕ) (x : ℝ) :
    aeval x (gorshkovPoly k) = 0 ↔ gorshkovMap^[k] x = 1 / 2 := by
  obtain ⟨hqpos, hp⟩ := aeval_gorshkovPQ k x
  simp only [gorshkovPoly, map_sub, map_mul, map_ofNat, hp]
  rw [show 2 * (gorshkovMap^[k] x * aeval x (gorshkovPQ k).2) - aeval x (gorshkovPQ k).2 =
    (2 * gorshkovMap^[k] x - 1) * aeval x (gorshkovPQ k).2 by ring,
    mul_eq_zero, or_iff_left hqpos.ne']
  constructor <;> intro h <;> linarith

theorem mem_gorshkovRoots_props (k : ℕ) {x : ℝ} (hx : x ∈ gorshkovRoots k) :
    x ∈ Set.Ioo (0 : ℝ) 1 ∧ gorshkovMap^[k] x = 1 / 2 := by
  induction k generalizing x with
  | zero =>
    simp only [gorshkovRoots, mem_singleton] at hx
    subst hx
    exact ⟨⟨by norm_num, by norm_num⟩, rfl⟩
  | succ k ih =>
    simp only [gorshkovRoots, mem_union, mem_image] at hx
    rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · obtain ⟨hyI, hyit⟩ := ih hy
      have hL := gorshkovLeftInv_mem_Ioo hyI
      refine ⟨⟨hL.1, by linarith [hL.2]⟩, ?_⟩
      rw [Function.iterate_succ_apply, gorshkovMap_leftInv hyI, hyit]
    · obtain ⟨hyI, hyit⟩ := ih hy
      have hR := gorshkovRightInv_mem_Ioo hyI
      refine ⟨⟨by linarith [hR.1], hR.2⟩, ?_⟩
      rw [Function.iterate_succ_apply, gorshkovMap_rightInv hyI, hyit]

theorem aeval_eq_zero_of_mem_gorshkovRoots {k : ℕ} {x : ℝ} (hx : x ∈ gorshkovRoots k) :
    aeval x (gorshkovPoly k) = 0 :=
  (aeval_gorshkovPoly_eq_zero_iff k x).mpr (mem_gorshkovRoots_props k hx).2

theorem card_gorshkovRoots (k : ℕ) : (gorshkovRoots k).card = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [gorshkovRoots]
    have hdisj : Disjoint ((gorshkovRoots k).image gorshkovLeftInv)
        ((gorshkovRoots k).image gorshkovRightInv) := by
      rw [Finset.disjoint_left]
      intro z hzL hzR
      obtain ⟨y₁, hy₁, rfl⟩ := mem_image.mp hzL
      obtain ⟨y₂, hy₂, heq⟩ := mem_image.mp hzR
      have h1 := (gorshkovLeftInv_mem_Ioo (mem_gorshkovRoots_props k hy₁).1).2
      have h2 := (gorshkovRightInv_mem_Ioo (mem_gorshkovRoots_props k hy₂).1).1
      linarith
    have hinjL : Set.InjOn gorshkovLeftInv (gorshkovRoots k) := by
      intro y₁ hy₁ y₂ hy₂ heq
      have h := congrArg gorshkovMap heq
      rwa [gorshkovMap_leftInv (mem_gorshkovRoots_props k hy₁).1,
        gorshkovMap_leftInv (mem_gorshkovRoots_props k hy₂).1] at h
    have hinjR : Set.InjOn gorshkovRightInv (gorshkovRoots k) := by
      intro y₁ hy₁ y₂ hy₂ heq
      have h := congrArg gorshkovMap heq
      rwa [gorshkovMap_rightInv (mem_gorshkovRoots_props k hy₁).1,
        gorshkovMap_rightInv (mem_gorshkovRoots_props k hy₂).1] at h
    rw [card_union_of_disjoint hdisj, card_image_of_injOn hinjL, card_image_of_injOn hinjR,
      ih, pow_succ]
    ring

theorem disjoint_gorshkovRoots {k m : ℕ} (hkm : k ≠ m) :
    Disjoint (gorshkovRoots k) (gorshkovRoots m) := by
  suffices ∀ a b : ℕ, a < b → Disjoint (gorshkovRoots a) (gorshkovRoots b) by
    rcases lt_or_gt_of_ne hkm with h | h
    · exact this k m h
    · exact (this m k h).symm
  intro a b hab
  rw [Finset.disjoint_left]
  intro x hxa hxb
  have ha := (mem_gorshkovRoots_props a hxa).2
  have hb := (mem_gorshkovRoots_props b hxb).2
  have hb' : b = (b - a - 1 + 1) + a := by omega
  rw [hb', Function.iterate_add_apply, ha] at hb
  exact gorshkovIter_half_succ_ne_half (b - a - 1) hb

/-! ### Degree, leading coefficient, and complete splitting -/

private lemma coeff_mul_top {R : Type*} [Semiring R] (f g : R[X]) {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    (f * g).coeff (m + n) = f.coeff m * g.coeff n := by
  rw [Polynomial.coeff_mul, Finset.sum_eq_single (m, n)]
  · intro x hx hne
    rcases lt_or_ge m x.1 with h1 | h1
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hf.trans_lt h1), zero_mul]
    · have hsum : x.1 + x.2 = m + n := Finset.mem_antidiagonal.mp hx
      have h2 : n < x.2 := by
        by_contra! hle
        have hx1 : x.1 = m := by omega
        have hx2 : x.2 = n := by omega
        exact hne (Prod.ext hx1 hx2)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hg.trans_lt h2), mul_zero]
  · intro h
    exfalso
    exact h (Finset.mem_antidiagonal.mpr rfl)

/-- Unsigned top-degree coefficients `(a_j, c_j)` of `(-p_{j+1}, q_{j+1})`. -/
def gorshkovAC : ℕ → ℕ × ℕ
  | 0 => (1, 3)
  | j + 1 =>
    let ac := gorshkovAC j
    (ac.1 * (ac.2 + ac.1), ac.2 ^ 2 + 3 * ac.1 * (ac.2 + ac.1))

theorem gorshkovPQ_succ (k : ℕ) :
    gorshkovPQ (k + 1) =
      ((gorshkovPQ k).1 * ((gorshkovPQ k).2 - (gorshkovPQ k).1),
        (gorshkovPQ k).2 ^ 2 - 3 * (gorshkovPQ k).1 * ((gorshkovPQ k).2 - (gorshkovPQ k).1)) := rfl

theorem gorshkovAC_succ (j : ℕ) :
    gorshkovAC (j + 1) =
      ((gorshkovAC j).1 * ((gorshkovAC j).2 + (gorshkovAC j).1),
        (gorshkovAC j).2 ^ 2 + 3 * (gorshkovAC j).1 * ((gorshkovAC j).2 + (gorshkovAC j).1)) := rfl

/-- Absolute leading coefficient `b_k = |coeff(F_k, 2^k)|`. -/
def gorshkovLeadAbs : ℕ → ℕ
  | 0 => 2
  | j + 1 => 2 * (gorshkovAC j).1 + (gorshkovAC j).2

theorem gorshkovLeadAbs_succ (j : ℕ) :
    gorshkovLeadAbs (j + 1) = 2 * (gorshkovAC j).1 + (gorshkovAC j).2 := rfl

theorem gorshkovAC_pos (j : ℕ) : 0 < (gorshkovAC j).1 ∧ 0 < (gorshkovAC j).2 := by
  induction j with
  | zero => decide
  | succ j ih =>
    obtain ⟨ha, hc⟩ := ih
    rw [gorshkovAC_succ]
    exact ⟨Nat.mul_pos ha (by omega), by positivity⟩

theorem gorshkovLeadAbs_pos (k : ℕ) : 0 < gorshkovLeadAbs k := by
  rcases k with _ | j
  · decide
  · obtain ⟨ha, hc⟩ := gorshkovAC_pos j
    rw [gorshkovLeadAbs_succ]
    omega

theorem natDegree_gorshkovPQ_le (k : ℕ) :
    (gorshkovPQ k).1.natDegree ≤ 2 ^ k ∧ (gorshkovPQ k).2.natDegree ≤ 2 ^ k := by
  induction k with
  | zero => simp [gorshkovPQ]
  | succ k ih =>
    obtain ⟨hp, hq⟩ := ih
    rw [gorshkovPQ_succ]
    have hsub : ((gorshkovPQ k).2 - (gorshkovPQ k).1).natDegree ≤ 2 ^ k :=
      (natDegree_sub_le _ _).trans (max_le hq hp)
    have hmul : ((gorshkovPQ k).1 * ((gorshkovPQ k).2 - (gorshkovPQ k).1)).natDegree ≤
        2 ^ (k + 1) :=
      natDegree_mul_le.trans (by rw [pow_succ]; omega)
    have hsq : ((gorshkovPQ k).2 ^ 2).natDegree ≤ 2 ^ (k + 1) :=
      (natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hq)).trans_eq (by rw [pow_succ]; ring)
    have h3 : (3 * (gorshkovPQ k).1 * ((gorshkovPQ k).2 - (gorshkovPQ k).1)).natDegree ≤
        2 ^ (k + 1) := by
      rw [mul_assoc]
      refine natDegree_mul_le.trans ?_
      have hc3 : (3 : ℤ[X]).natDegree = 0 := by simp
      rw [hc3, zero_add]
      exact hmul
    exact ⟨hmul, (natDegree_sub_le _ _).trans (max_le hsq h3)⟩

theorem natDegree_gorshkovPoly_le (k : ℕ) : (gorshkovPoly k).natDegree ≤ 2 ^ k := by
  obtain ⟨hp, hq⟩ := natDegree_gorshkovPQ_le k
  refine (natDegree_sub_le _ _).trans (max_le ?_ hq)
  refine natDegree_mul_le.trans ?_
  have hc2 : (2 : ℤ[X]).natDegree = 0 := by simp
  rw [hc2, zero_add]
  exact hp

theorem coeff_gorshkovPQ_succ (j : ℕ) :
    (gorshkovPQ (j + 1)).1.coeff (2 ^ (j + 1)) = -((gorshkovAC j).1 : ℤ) ∧
      (gorshkovPQ (j + 1)).2.coeff (2 ^ (j + 1)) = ((gorshkovAC j).2 : ℤ) := by
  induction j with
  | zero =>
    simp only [gorshkovPQ, gorshkovAC]
    have h1 : (X * (1 - X) : ℤ[X]) = -X ^ 2 + X := by ring
    have h2 : ((1 : ℤ[X]) ^ 2 - 3 * X * (1 - X)) = 3 * X ^ 2 - 3 * X + 1 := by ring
    rw [h1, h2]
    simp [coeff_X_pow, coeff_X, coeff_one]
  | succ j ih =>
    obtain ⟨hA, hC⟩ := ih
    obtain ⟨hp, hq⟩ := natDegree_gorshkovPQ_le (j + 1)
    have hsub : ((gorshkovPQ (j + 1)).2 - (gorshkovPQ (j + 1)).1).natDegree ≤ 2 ^ (j + 1) :=
      (natDegree_sub_le _ _).trans (max_le hq hp)
    have hpow : 2 ^ (j + 2) = 2 ^ (j + 1) + 2 ^ (j + 1) := by ring
    rw [gorshkovPQ_succ (j + 1), gorshkovAC_succ j, hpow]
    dsimp only
    have hm1 := coeff_mul_top (gorshkovPQ (j + 1)).1
      ((gorshkovPQ (j + 1)).2 - (gorshkovPQ (j + 1)).1) hp hsub
    have hm2 := coeff_mul_top (gorshkovPQ (j + 1)).2 (gorshkovPQ (j + 1)).2 hq hq
    rw [sq, mul_assoc, coeff_sub, coeff_ofNat_mul, hm1, hm2, coeff_sub, hA, hC]
    push_cast
    exact ⟨by ring, by ring⟩

theorem abs_coeff_gorshkovPoly (k : ℕ) :
    |((gorshkovPoly k).coeff (2 ^ k) : ℝ)| = gorshkovLeadAbs k := by
  rcases k with _ | j
  · simp [gorshkovPoly, gorshkovPQ, gorshkovLeadAbs, coeff_one]
  · obtain ⟨hA, hC⟩ := coeff_gorshkovPQ_succ j
    rw [gorshkovPoly, gorshkovLeadAbs_succ, coeff_sub, coeff_ofNat_mul, hA, hC]
    push_cast
    rw [show 2 * -((gorshkovAC j).1 : ℝ) - ((gorshkovAC j).2 : ℝ) =
      -(2 * ((gorshkovAC j).1 : ℝ) + ((gorshkovAC j).2 : ℝ)) by ring, abs_neg,
      abs_of_nonneg (by positivity)]

theorem natDegree_map_gorshkovPoly (k : ℕ) :
    ((gorshkovPoly k).map (algebraMap ℤ ℝ)).natDegree = 2 ^ k := by
  apply le_antisymm
  · exact (natDegree_map_le).trans (natDegree_gorshkovPoly_le k)
  · apply le_natDegree_of_ne_zero
    rw [coeff_map]
    intro h0
    have habs := abs_coeff_gorshkovPoly k
    change |algebraMap ℤ ℝ ((gorshkovPoly k).coeff (2 ^ k))| = _ at habs
    rw [h0, abs_zero] at habs
    exact (gorshkovLeadAbs_pos k).ne' (by exact_mod_cast habs.symm)

theorem abs_leadingCoeff_map_gorshkovPoly (k : ℕ) :
    |((gorshkovPoly k).map (algebraMap ℤ ℝ)).leadingCoeff| = gorshkovLeadAbs k := by
  rw [leadingCoeff, natDegree_map_gorshkovPoly, coeff_map]
  exact abs_coeff_gorshkovPoly k

theorem roots_map_gorshkovPoly (k : ℕ) :
    ((gorshkovPoly k).map (algebraMap ℤ ℝ)).roots = (gorshkovRoots k).val := by
  set f := (gorshkovPoly k).map (algebraMap ℤ ℝ)
  have hf_deg : f.natDegree = 2 ^ k := natDegree_map_gorshkovPoly k
  have hf_ne : f ≠ 0 := by
    intro h0
    have : f.leadingCoeff = 0 := by simp [h0]
    have habs := abs_leadingCoeff_map_gorshkovPoly k
    rw [this, abs_zero] at habs
    exact (gorshkovLeadAbs_pos k).ne' (by exact_mod_cast habs.symm)
  have hle : (gorshkovRoots k).val ≤ f.roots := by
    rw [Multiset.le_iff_count]
    intro α
    by_cases hα : α ∈ gorshkovRoots k
    · have h1 : Multiset.count α (gorshkovRoots k).val ≤ 1 :=
        Multiset.nodup_iff_count_le_one.mp (gorshkovRoots k).nodup α
      have hroot : α ∈ f.roots := by
        rw [mem_roots hf_ne, IsRoot.def, eval_map]
        exact aeval_eq_zero_of_mem_gorshkovRoots hα
      exact h1.trans (Multiset.one_le_count_iff_mem.mpr hroot)
    · simp [Multiset.count_eq_zero.mpr hα]
  exact (Multiset.eq_of_le_of_card_le hle
    (f.card_roots'.trans (by rw [hf_deg, ← card_gorshkovRoots k]; rfl))).symm

theorem splits_map_gorshkovPoly (k : ℕ) :
    ((gorshkovPoly k).map (algebraMap ℤ ℝ)).Splits := by
  rw [Polynomial.splits_iff_card_roots, roots_map_gorshkovPoly, natDegree_map_gorshkovPoly]
  exact card_gorshkovRoots k

/-! ### Growth bound on the leading coefficients -/

theorem seven_mul_le_gorshkovAC (m : ℕ) :
    7 * (gorshkovAC (m + 2)).1 ≤ (gorshkovAC (m + 2)).2 := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 from rfl, gorshkovAC_succ]
    dsimp only
    nlinarith

theorem gorshkovLeadAbs_recurrence_bound (m : ℕ) :
    81 * gorshkovLeadAbs (m + 4) ≤ 89 * (gorshkovLeadAbs (m + 3)) ^ 2 := by
  have h7 := seven_mul_le_gorshkovAC m
  rw [show m + 4 = (m + 3) + 1 from rfl, gorshkovLeadAbs_succ,
    show m + 3 = (m + 2) + 1 from rfl, gorshkovLeadAbs_succ, gorshkovAC_succ]
  dsimp only
  nlinarith

theorem gorshkovLeadAbs_le_pow_succ3 (m : ℕ) :
    (89 / 81 : ℝ) * gorshkovLeadAbs (m + 3) ≤ (2382 / 1000 : ℝ) ^ (2 ^ (m + 3)) := by
  induction m with
  | zero =>
    have hb3 : gorshkovLeadAbs 3 = 941 := rfl
    rw [hb3]
    norm_num
  | succ m ih =>
    have hrec : (81 : ℝ) * gorshkovLeadAbs (m + 4) ≤ 89 * (gorshkovLeadAbs (m + 3) : ℝ) ^ 2 := by
      exact_mod_cast gorshkovLeadAbs_recurrence_bound m
    have hstep : (89 / 81 : ℝ) * gorshkovLeadAbs (m + 4) ≤
        ((89 / 81 : ℝ) * gorshkovLeadAbs (m + 3)) ^ 2 := by nlinarith
    refine hstep.trans ?_
    calc ((89 / 81 : ℝ) * gorshkovLeadAbs (m + 3)) ^ 2
        ≤ ((2382 / 1000 : ℝ) ^ (2 ^ (m + 3))) ^ 2 :=
          pow_le_pow_left₀ (by positivity) ih 2
      _ = (2382 / 1000 : ℝ) ^ (2 ^ (m + 4)) := by
          rw [← pow_mul, show 2 ^ (m + 3) * 2 = 2 ^ (m + 4) by ring]

theorem gorshkovLeadAbs_le_pow (k : ℕ) :
    (gorshkovLeadAbs k : ℝ) ≤ (2382 / 1000 : ℝ) ^ (2 ^ k) := by
  rcases k with _ | _ | _ | m
  · have : gorshkovLeadAbs 0 = 2 := rfl; rw [this]; norm_num
  · have : gorshkovLeadAbs 1 = 5 := rfl; rw [this]; norm_num
  · have : gorshkovLeadAbs 2 = 29 := rfl; rw [this]; norm_num
  · have h := gorshkovLeadAbs_le_pow_succ3 m
    have hb : (0 : ℝ) ≤ gorshkovLeadAbs (m + 3) := Nat.cast_nonneg _
    linarith

theorem base_lt_exp_87_div_100 : (2382 / 1000 : ℝ) < Real.exp (87 / 100) := by
  have h := Real.sum_le_exp_of_nonneg (x := (87 / 100 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem gorshkovLeadAbs_lt_exp (k : ℕ) :
    (gorshkovLeadAbs k : ℝ) < Real.exp ((87 / 100 : ℝ) * (2 ^ k : ℝ)) := by
  calc (gorshkovLeadAbs k : ℝ)
      ≤ (2382 / 1000 : ℝ) ^ (2 ^ k) := gorshkovLeadAbs_le_pow k
    _ < (Real.exp (87 / 100)) ^ (2 ^ k) :=
        pow_lt_pow_left₀ base_lt_exp_87_div_100 (by norm_num) (pow_ne_zero k (by norm_num))
    _ = Real.exp ((87 / 100 : ℝ) * (2 ^ k : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-! ### The resultant pigeonhole bound and the univariate/cube ceiling -/

/-- **Univariate integer Chebyshev ceiling on `(0, 1)`.** Every nonzero `P ∈ ℤ[X]` of degree at
most `n` (`n ≥ 1`) exceeds `exp(-(87/100) n)` in absolute value at some point of `(0, 1)`. -/
theorem exists_Ioo_gt_univariate_chebyshev_cap (P : ℤ[X]) {n : ℕ} (hP : P ≠ 0) (hn : 1 ≤ n)
    (hdeg : P.natDegree ≤ n) :
    ∃ x ∈ Set.Ioo (0 : ℝ) 1, Real.exp (-(87 / 100 : ℝ) * n) < |aeval x P| := by
  set g := P.map (algebraMap ℤ ℝ)
  have hg_ne : g ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective_int (algebraMap ℤ ℝ))).mpr hP
  have hg_deg : g.natDegree ≤ n := natDegree_map_le.trans hdeg
  -- Pigeonhole across the `n + 1` disjoint root sets `Z_0, …, Z_n`
  have hex : ∃ k : ℕ, k ≤ n ∧ ∀ α ∈ gorshkovRoots k, g.eval α ≠ 0 := by
    by_contra! hbad
    have hbad' : ∀ k : Fin (n + 1), ∃ α ∈ gorshkovRoots k.1, g.eval α = 0 := fun k =>
      hbad k.1 (Nat.lt_succ_iff.mp k.2)
    choose root hroot_mem hroot_zero using hbad'
    have hinj : Function.Injective root := by
      intro k₁ k₂ heq
      by_contra hne
      have hne' : k₁.1 ≠ k₂.1 := fun h => hne (Fin.ext h)
      exact Finset.disjoint_left.mp (disjoint_gorshkovRoots hne')
        (hroot_mem k₁) (heq ▸ hroot_mem k₂)
    have hsub : (Finset.univ.image root) ⊆ g.roots.toFinset := by
      intro α hα
      obtain ⟨k, _, rfl⟩ := mem_image.mp hα
      exact Multiset.mem_toFinset.mpr ((mem_roots hg_ne).mpr (hroot_zero k))
    have hcard1 : n + 1 ≤ (Finset.univ.image root).card := by
      rw [card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hcard2 : g.roots.toFinset.card ≤ n :=
      (Multiset.toFinset_card_le _).trans (g.card_roots'.trans hg_deg)
    exact absurd (hcard1.trans ((card_le_card hsub).trans hcard2)) (by omega)
  obtain ⟨k, _, hk⟩ := hex
  set f := (gorshkovPoly k).map (algebraMap ℤ ℝ)
  have hres := Polynomial.resultant_eq_prod_eval f g n hg_deg (splits_map_gorshkovPoly k)
  rw [natDegree_map_gorshkovPoly k, Polynomial.resultant_map_map] at hres
  have hprod_eq : (Multiset.map g.eval f.roots).prod = ∏ α ∈ gorshkovRoots k, aeval α P := by
    rw [roots_map_gorshkovPoly k]
    simp only [Finset.prod, g, eval_map, ← aeval_def]
  rw [hprod_eq] at hres
  have hlead_pos : 0 < |f.leadingCoeff| := by
    rw [abs_leadingCoeff_map_gorshkovPoly]
    exact_mod_cast gorshkovLeadAbs_pos k
  have hprod_ne : ∏ α ∈ gorshkovRoots k, aeval α P ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun α hα => ?_
    have := hk α hα
    rwa [eval_map, ← aeval_def] at this
  have hres_int_ne : (gorshkovPoly k).resultant P (2 ^ k) n ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hres
    exact mul_ne_zero (pow_ne_zero n (abs_pos.mp hlead_pos)) hprod_ne hres.symm
  have hres_ge_one : (1 : ℝ) ≤ |algebraMap ℤ ℝ ((gorshkovPoly k).resultant P (2 ^ k) n)| := by
    have h1 : (1 : ℤ) ≤ |(gorshkovPoly k).resultant P (2 ^ k) n| := Int.one_le_abs hres_int_ne
    have h2 : (1 : ℝ) ≤ (|(gorshkovPoly k).resultant P (2 ^ k) n| : ℝ) := by exact_mod_cast h1
    simpa [Int.cast_abs] using h2
  rw [hres, abs_mul, abs_pow, abs_leadingCoeff_map_gorshkovPoly, abs_prod] at hres_ge_one
  by_contra! hsmall
  have hα_le : ∀ α ∈ gorshkovRoots k, |aeval α P| ≤ Real.exp (-(87 / 100 : ℝ) * n) := fun α hα =>
    hsmall α (mem_gorshkovRoots_props k hα).1
  have hprod_le : ∏ α ∈ gorshkovRoots k, |aeval α P| ≤
      (Real.exp (-(87 / 100 : ℝ) * n)) ^ (2 ^ k) := by
    calc ∏ α ∈ gorshkovRoots k, |aeval α P|
        ≤ ∏ _ ∈ gorshkovRoots k, Real.exp (-(87 / 100 : ℝ) * n) :=
          prod_le_prod (fun _ _ => abs_nonneg _) hα_le
      _ = (Real.exp (-(87 / 100 : ℝ) * n)) ^ (2 ^ k) := by
          rw [prod_const, card_gorshkovRoots]
  have hlead_lt : (gorshkovLeadAbs k : ℝ) ^ n <
      (Real.exp ((87 / 100 : ℝ) * (2 ^ k : ℝ))) ^ n :=
    pow_lt_pow_left₀ (gorshkovLeadAbs_lt_exp k) (Nat.cast_nonneg _) (by omega)
  have hlt_one : (gorshkovLeadAbs k : ℝ) ^ n * ∏ α ∈ gorshkovRoots k, |aeval α P| < 1 := by
    calc (gorshkovLeadAbs k : ℝ) ^ n * ∏ α ∈ gorshkovRoots k, |aeval α P|
        ≤ (gorshkovLeadAbs k : ℝ) ^ n * (Real.exp (-(87 / 100 : ℝ) * n)) ^ (2 ^ k) :=
          mul_le_mul_of_nonneg_left hprod_le (by positivity)
      _ < (Real.exp ((87 / 100 : ℝ) * (2 ^ k : ℝ))) ^ n *
            (Real.exp (-(87 / 100 : ℝ) * n)) ^ (2 ^ k) :=
          mul_lt_mul_of_pos_right hlead_lt (by positivity)
      _ = 1 := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
          convert Real.exp_zero using 1
          push_cast
          ring
  linarith

/-- **Univariate integer Chebyshev ceiling on `[0, 1]`.** -/
theorem exists_Icc_gt_univariate_chebyshev_cap (P : ℤ[X]) {n : ℕ} (hP : P ≠ 0) (hn : 1 ≤ n)
    (hdeg : P.natDegree ≤ n) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, Real.exp (-(87 / 100 : ℝ) * n) < |aeval x P| := by
  obtain ⟨x, hx, hgt⟩ := exists_Ioo_gt_univariate_chebyshev_cap P hP hn hdeg
  exact ⟨x, Set.Ioo_subset_Icc_self hx, hgt⟩

/-- **Sup-norm certificates on `[0, 1]` are strictly capped below `87/100 < 89/100 < 1`.** If `M`
dominates `|P|` on `[0, 1]` for a nonzero `P ∈ ℤ[X]` of degree at most `n` (`n ≥ 1`), then
`log (1 / M) < (87/100) n`. -/
theorem sup_certified_log_inv_lt (P : ℤ[X]) {n : ℕ} (hP : P ≠ 0) (hn : 1 ≤ n)
    (hdeg : P.natDegree ≤ n) {M : ℝ} (hM : ∀ x ∈ Set.Icc (0 : ℝ) 1, |aeval x P| ≤ M) :
    Real.log (1 / M) < (87 / 100 : ℝ) * n := by
  obtain ⟨x, hx, hgt⟩ := exists_Icc_gt_univariate_chebyshev_cap P hP hn hdeg
  have hexp_lt : Real.exp (-(87 / 100 : ℝ) * n) < M := hgt.trans_le (hM x hx)
  have hMpos : 0 < M := lt_trans (Real.exp_pos _) hexp_lt
  have hdiv : 1 / M < Real.exp ((87 / 100 : ℝ) * n) := by
    rw [div_lt_iff₀ hMpos]
    calc (1 : ℝ)
        = Real.exp ((87 / 100 : ℝ) * n) * Real.exp (-(87 / 100 : ℝ) * n) := by
          rw [← Real.exp_add]; simp
      _ < Real.exp ((87 / 100 : ℝ) * n) * M :=
          mul_lt_mul_of_pos_left hexp_lt (Real.exp_pos _)
  calc Real.log (1 / M)
      < Real.log (Real.exp ((87 / 100 : ℝ) * n)) := Real.log_lt_log (by positivity) hdiv
    _ = (87 / 100 : ℝ) * n := Real.log_exp _

/-- Diagonal specialization `(X_i ↦ X)` sends a multivariate polynomial of total degree `≤ n` to a
univariate polynomial of degree `≤ n`. -/
theorem natDegree_diagonal_mvPolynomial_le {σ : Type*} (Q : MvPolynomial σ ℤ) :
    (MvPolynomial.aeval (fun _ : σ => (X : ℤ[X])) Q).natDegree ≤ Q.totalDegree := by
  classical
  have hprod : ∀ s : σ →₀ ℕ, (s.prod fun _ e => (X : ℤ[X]) ^ e) = X ^ (s.sum fun _ e => e) :=
    fun s => by rw [Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum]
  conv_lhs => rw [Q.as_sum, map_sum]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun s hs => ?_⟩
  dsimp only [Function.comp_apply]
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_apply, hprod s]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [MvPolynomial.totalDegree]
  exact (Polynomial.natDegree_X_pow_le _).trans
    (Finset.le_sup (f := fun t : σ →₀ ℕ => t.sum fun _ e => e) hs)

/-- **Diagonal ceiling on `[0, 1]^σ`.** Every `Q ∈ ℤ[X_i : i ∈ σ]` of total degree at most `n`
(`n ≥ 1`) with nonvanishing diagonal restriction exceeds `exp(-(87/100) n)` on `(0, 1)^σ`. -/
theorem exists_cube_gt_of_mvPolynomial_totalDegree_le {σ : Type*} (Q : MvPolynomial σ ℤ) {n : ℕ}
    (hn : 1 ≤ n) (hdeg : Q.totalDegree ≤ n)
    (hdiag : MvPolynomial.aeval (fun _ : σ => (X : ℤ[X])) Q ≠ 0) :
    ∃ v : σ → ℝ, (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) ∧
      Real.exp (-(87 / 100 : ℝ) * n) < |MvPolynomial.aeval v Q| := by
  set P : ℤ[X] := MvPolynomial.aeval (fun _ : σ => (X : ℤ[X])) Q
  obtain ⟨t, ht, hgt⟩ := exists_Icc_gt_univariate_chebyshev_cap P hdiag hn
    ((natDegree_diagonal_mvPolynomial_le Q).trans hdeg)
  refine ⟨fun _ => t, fun _ => ht, ?_⟩
  have heval : aeval t P = MvPolynomial.aeval (fun _ : σ => t) Q := by
    change ((aeval t).comp (MvPolynomial.aeval fun _ : σ => (X : ℤ[X]))) Q = _
    congr 1
    ext i
    simp
  rwa [← heval]

#print axioms exists_Ioo_gt_univariate_chebyshev_cap
#print axioms sup_certified_log_inv_lt
#print axioms exists_cube_gt_of_mvPolynomial_totalDegree_le

end GaloisForLFunctions.ArithmeticKreinLangerTheory
