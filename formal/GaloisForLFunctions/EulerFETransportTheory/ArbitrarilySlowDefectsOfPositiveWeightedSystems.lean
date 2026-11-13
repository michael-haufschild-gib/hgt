import GaloisForLFunctions.EulerFETransportTheory.RieszCountOfAContinuedEulerProduct
import GaloisForLFunctions.EulerFETransportTheory.PointMassDiscretizationsOfALaplaceDensity
import GaloisForLFunctions.EulerFETransportTheory.PolynomialStripContinuationsLieInTheHamburgerClass

/-!
# Arbitrarily slow FE defects of positive-weighted Beurling systems

**Theorem II.3** (`exists_positiveWeighted_beurling_slow_defect`).  Let `Φ → ∞`, `μ < 1/2`,
`0 < ν < 3μ - 1` (so `μ > 1/3`) and `γ ∈ ℝ`.  There is a countable family of generators
`p_i = e^{u_i} ≥ e^{10}`, locally finite, with `ℚ`-independent logarithms and positive real
weights `w_i`, whose Euler product `ζ_P(s) = Π_i (1 - p_i^{-s})^{-w_i}` (absolutely convergent
on `Re s > 1`)

* continues to `Re s > 1/3` as `G(s)/(s - 1)`, `G` holomorphic, `G(1) = A > 0`, with zeros at
  `1 - μ ± iγ`;
* has integer count `N(x) = A x + O(x^{4/5})`;
* lies in the Hamburger strip class with critical-line FE defect `‖g(t)‖ ≤ Φ(|t|)` for large `|t|`.

The construction discretizes the Möbius-inverted over-regular density `π₀` (zeta function
`ζ_c e^{-I₀}`, `ζ_c = overRegularZeta`) into point masses on cells of length `1/M_m` in the block
`J_m = (u₀ + m, u₀ + m + 1]`.  Then `ζ_P = ζ_c e^{-I₀ + E}` with `E = Σ_m E_m`; at height `τ` the
blocks with `T_m ≤ τ` contribute at most `B_m = 4 e^{-2(u₀+m)/5} ∫_{J_m} π₀` and the others at most
`2^{-(m+3)}`, because `M_m` is chosen with `T_m`.  The heights `T_k` are chosen from `Φ`, so that
`|ζ_P| ≤ X_k/8` on `[T_k, T_{k+1})` while `Φ ≥ X_k` there.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.ArithmeticPositiveDuality RHTower.BeurlingOverRegularIntegers
open GaloisForLFunctions.EulerFETransportTheory.MobiusInverted
open GaloisForLFunctions.EulerFETransportTheory.Discretization

noncomputable section

namespace GaloisForLFunctions.EulerFETransportTheory.SlowDefect

/-! ## The rational factor `(s - 1) ζ_c(s)` -/

/-- `G_c(s) = (s - 1) ζ_c(s) = ((s - (1-μ))² + γ²)(s + 4μ - 1)/((s + p₁)(s + p₂))`. -/
def contG (μ ν γ : ℝ) (s : ℂ) : ℂ :=
  ((s - (1 - μ)) ^ 2 + (γ : ℂ) ^ 2) * (s + (4 * μ - 1)) /
    ((s + (3 * μ - 1 - ν)) * (s + (3 * μ - 1 + ν)))

theorem add_ne_zero_of_re {s : ℂ} {p : ℝ} (h : 0 < s.re + p) : s + (p : ℂ) ≠ 0 := fun h0 => by
  have := congrArg Complex.re h0
  simp at this
  linarith

theorem sub_one_mul_overRegularZeta {μ ν γ : ℝ} (hp₁ : 0 < 3 * μ - 1 - ν)
    (hp₂ : 0 < 3 * μ - 1 + ν) {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * overRegularZeta μ ν γ s = contG μ ν γ s := by
  have h1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have h2 := add_ne_zero_of_re (s := s) (p := 3 * μ - 1 - ν) (by linarith)
  have h3 := add_ne_zero_of_re (s := s) (p := 3 * μ - 1 + ν) (by linarith)
  push_cast at h2 h3
  rw [overRegularZeta, contG]
  field_simp

/-- `G_c` is holomorphic on `Re s > 1/3`: the poles `-p₁, -p₂` lie to the left of `0`. -/
theorem differentiableOn_contG {μ ν γ : ℝ} (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) :
    DifferentiableOn ℂ (contG μ ν γ) {s : ℂ | 1 / 3 < s.re} := by
  intro s hs
  have h2 := add_ne_zero_of_re (s := s) (p := 3 * μ - 1 - ν) (by simp at hs; linarith)
  have h3 := add_ne_zero_of_re (s := s) (p := 3 * μ - 1 + ν) (by simp at hs; linarith)
  push_cast at h2 h3
  unfold contG
  exact ((by fun_prop : Differentiable ℂ fun s : ℂ =>
    ((s - (1 - μ)) ^ 2 + (γ : ℂ) ^ 2) * (s + (4 * μ - 1))) s).differentiableWithinAt.div
    ((by fun_prop : Differentiable ℂ fun s : ℂ =>
      (s + (3 * μ - 1 - ν)) * (s + (3 * μ - 1 + ν))) s).differentiableWithinAt
    (mul_ne_zero h2 h3)

/-- The zeros `1 - μ ± iγ`. -/
theorem contG_zero (μ ν γ : ℝ) :
    contG μ ν γ (((1 - μ : ℝ) : ℂ) + γ * I) = 0 ∧ contG μ ν γ (((1 - μ : ℝ) : ℂ) - γ * I) = 0 := by
  constructor
  · have h : ((((1 - μ : ℝ) : ℂ) + γ * I) - (1 - μ)) ^ 2 + (γ : ℂ) ^ 2 = 0 := by
      push_cast; linear_combination ((γ : ℂ) ^ 2) * Complex.I_sq
    rw [contG, h, zero_mul, zero_div]
  · have h : ((((1 - μ : ℝ) : ℂ) - γ * I) - (1 - μ)) ^ 2 + (γ : ℂ) ^ 2 = 0 := by
      push_cast; linear_combination ((γ : ℂ) ^ 2) * Complex.I_sq
    rw [contG, h, zero_mul, zero_div]

theorem contG_one {μ ν γ : ℝ} :
    contG μ ν γ 1 = (((μ ^ 2 + γ ^ 2) * (4 * μ) / ((3 * μ - ν) * (3 * μ + ν)) : ℝ) : ℂ) := by
  rw [contG]
  push_cast
  ring_nf

/-- A denominator factor on the strip: `‖s + p‖ ≥ (1 + |Im s|)/5`. -/
theorem norm_add_ge {s : ℂ} (hs : 2 / 5 ≤ s.re) {p : ℝ} (hp : 0 ≤ p) :
    (1 + |s.im|) / 5 ≤ ‖s + (p : ℂ)‖ := by
  have h1 := Complex.abs_re_le_norm (s + p)
  have h2 := Complex.abs_im_le_norm (s + p)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im,
    add_zero] at h1 h2
  rw [abs_of_pos (by linarith)] at h1
  linarith [abs_nonneg s.im]

/-- A numerator factor on the strip: `‖s - c‖ ≤ (2 + ‖c‖)(1 + |Im s|)`. -/
theorem norm_sub_le_strip {s : ℂ} (hs1 : 2 / 5 ≤ s.re) (hs2 : s.re ≤ 2) (c : ℂ) :
    ‖s - c‖ ≤ (2 + ‖c‖) * (1 + |s.im|) := by
  have h := Complex.norm_le_abs_re_add_abs_im s
  have hre : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith, hs2⟩
  have h2 := norm_sub_le s c
  nlinarith [mul_nonneg (norm_nonneg c) (abs_nonneg s.im), abs_nonneg s.im]

/-- `‖G_c(s)‖ ≤ 75 (3 + |γ|)² (1 + |Im s|)` on `2/5 ≤ Re s ≤ 2`. -/
theorem norm_contG_le {μ ν γ : ℝ} (hμ0 : 0 < μ) (hμh : μ ≤ 1 / 2) (hp₁ : 0 < 3 * μ - 1 - ν)
    (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1) {s : ℂ} (hs1 : 2 / 5 ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖contG μ ν γ s‖ ≤ 75 * (3 + |γ|) ^ 2 * (1 + |s.im|) := by
  set τ := 1 + |s.im| with hτ
  have hτ1 : 1 ≤ τ := by rw [hτ]; linarith [abs_nonneg s.im]
  set ρ : ℂ := ((1 - μ : ℝ) : ℂ) + γ * I with hρ
  have hρn : ‖ρ‖ ≤ 1 + |γ| := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hρn' : ‖(starRingEnd ℂ) ρ‖ ≤ 1 + |γ| := by rw [Complex.norm_conj]; exact hρn
  have hfac : (s - (1 - μ)) ^ 2 + (γ : ℂ) ^ 2 = (s - ρ) * (s - (starRingEnd ℂ) ρ) := by
    rw [hρ]
    simp only [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I]
    push_cast
    linear_combination ((γ : ℂ) ^ 2) * Complex.I_sq
  have hn1 := norm_sub_le_strip hs1 hs2 ρ
  have hn2 := norm_sub_le_strip hs1 hs2 ((starRingEnd ℂ) ρ)
  have hn3 : ‖s + ((4 * μ - 1 : ℝ) : ℂ)‖ ≤ 3 * τ := by
    have := norm_sub_le_strip hs1 hs2 (-((4 * μ - 1 : ℝ) : ℂ))
    rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos h4] at this
    nlinarith
  have hd1 := norm_add_ge hs1 hp₁.le
  have hd2 := norm_add_ge hs1 hp₂.le
  have hnum : ‖((s - (1 - μ)) ^ 2 + (γ : ℂ) ^ 2) * (s + (4 * μ - 1))‖ ≤
      3 * (3 + |γ|) ^ 2 * τ ^ 3 := by
    rw [hfac, norm_mul, norm_mul]
    have e : s + (4 * μ - 1 : ℂ) = s + ((4 * μ - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    have b1 : ‖s - ρ‖ ≤ (3 + |γ|) * τ :=
      hn1.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
    have b2 : ‖s - (starRingEnd ℂ) ρ‖ ≤ (3 + |γ|) * τ :=
      hn2.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
    calc ‖s - ρ‖ * ‖s - (starRingEnd ℂ) ρ‖ * ‖s + ((4 * μ - 1 : ℝ) : ℂ)‖
        ≤ ((3 + |γ|) * τ) * ((3 + |γ|) * τ) * (3 * τ) := by gcongr
      _ = 3 * (3 + |γ|) ^ 2 * τ ^ 3 := by ring
  have hden : (τ / 5) ^ 2 ≤ ‖(s + (3 * μ - 1 - ν)) * (s + (3 * μ - 1 + ν))‖ := by
    rw [norm_mul]
    have e1 : s + (3 * μ - 1 - ν : ℂ) = s + ((3 * μ - 1 - ν : ℝ) : ℂ) := by push_cast; ring
    have e2 : s + (3 * μ - 1 + ν : ℂ) = s + ((3 * μ - 1 + ν : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, sq]
    exact mul_le_mul hd1 hd2 (by positivity) (norm_nonneg _)
  rw [contG, norm_div]
  calc ‖((s - (1 - μ)) ^ 2 + (γ : ℂ) ^ 2) * (s + (4 * μ - 1))‖ /
        ‖(s + (3 * μ - 1 - ν)) * (s + (3 * μ - 1 + ν))‖
      ≤ 3 * (3 + |γ|) ^ 2 * τ ^ 3 / (τ / 5) ^ 2 :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 75 * (3 + |γ|) ^ 2 * τ := by field_simp; ring

/-- `‖G_c(s)/(s - 1)‖ ≤ 150 (3 + |γ|)²` on `2/5 ≤ Re s ≤ 2`, `|Im s| ≥ 1`. -/
theorem norm_contG_div_le {μ ν γ : ℝ} (hμ0 : 0 < μ) (hμh : μ ≤ 1 / 2) (hp₁ : 0 < 3 * μ - 1 - ν)
    (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1) {s : ℂ} (hs1 : 2 / 5 ≤ s.re) (hs2 : s.re ≤ 2)
    (hτ : 1 ≤ |s.im|) : ‖contG μ ν γ s / (s - 1)‖ ≤ 150 * (3 + |γ|) ^ 2 := by
  have hG := norm_contG_le (γ := γ) hμ0 hμh hp₁ hp₂ h4 hs1 hs2
  have him : |s.im| ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1); simpa using this
  have hpos : 0 < ‖s - 1‖ := by linarith
  rw [norm_div, div_le_iff₀ hpos]
  calc ‖contG μ ν γ s‖ ≤ 75 * (3 + |γ|) ^ 2 * (1 + |s.im|) := hG
    _ ≤ 150 * (3 + |γ|) ^ 2 * ‖s - 1‖ := by nlinarith [sq_nonneg (3 + |γ|)]

/-! ## Heights chosen from `Φ` -/

/-- Heights `T_k ↑ ∞` with `X_k² ≤ T_k` and `Φ ≥ X_k` beyond `T_k/2`. -/
theorem exists_heights {Φ : ℝ → ℝ} (hΦ : Tendsto Φ atTop atTop) (X : ℕ → ℝ) :
    ∃ T : ℕ → ℝ, 1 ≤ T 0 ∧ (∀ k, T k + 1 ≤ T (k + 1)) ∧ (∀ k, X k ^ 2 ≤ T k) ∧
      ∀ k t, T k / 2 ≤ t → X k ≤ Φ t := by
  choose A hA using fun k => eventually_atTop.mp (tendsto_atTop.mp hΦ (X k))
  refine ⟨fun k => (k : ℝ) + 1 + ∑ j ∈ Finset.range (k + 1), (X j ^ 2 + 2 * |A j|), ?_, ?_, ?_, ?_⟩
  · simp only [Nat.cast_zero, zero_add, Finset.sum_range_one]
    nlinarith [sq_nonneg (X 0), abs_nonneg (A 0)]
  · intro k
    simp only [Finset.sum_range_succ (n := k + 1)]
    push_cast
    nlinarith [sq_nonneg (X (k + 1)), abs_nonneg (A (k + 1))]
  · intro k
    have h := Finset.single_le_sum (f := fun j => X j ^ 2 + 2 * |A j|)
      (fun j _ => by positivity) (Finset.self_mem_range_succ k)
    nlinarith [abs_nonneg (A k), (k.cast_nonneg : (0 : ℝ) ≤ k)]
  · intro k t ht
    refine hA k t ?_
    have h := Finset.single_le_sum (f := fun j => X j ^ 2 + 2 * |A j|)
      (fun j _ => by positivity) (Finset.self_mem_range_succ k)
    nlinarith [le_abs_self (A k), sq_nonneg (X k), (k.cast_nonneg : (0 : ℝ) ≤ k)]

/-- Splitting a nonnegative series at `k`: `Σ_m E_m ≤ Σ_{m<k} B_m + 1/4` when `E_m ≤ B_m` below `k`
and `E_m ≤ 2^{-(m+3)}` from `k` on. -/
theorem tsum_le_split {E B : ℕ → ℝ} (hE0 : ∀ m, 0 ≤ E m) {k : ℕ} (hlow : ∀ m < k, E m ≤ B m)
    (hhigh : ∀ m, k ≤ m → E m ≤ (1 / 2) ^ (m + 3)) :
    Summable E ∧ ∑' m, E m ≤ ∑ m ∈ Finset.range k, B m + 1 / 4 := by
  set F : ℕ → ℝ := fun m => (if m < k then B m else 0) + (1 / 2) ^ (m + 3) with hF
  have hgeo : HasSum (fun m : ℕ => ((1 : ℝ) / 2) ^ (m + 3)) (1 / 4) := by
    have h := hasSum_geometric_two.mul_left (((1 : ℝ) / 2) ^ 3)
    rw [show ((1 : ℝ) / 2) ^ 3 * 2 = 1 / 4 by norm_num] at h
    exact h.congr_fun fun m => by rw [pow_add]; ring
  have hfin : HasSum (fun m : ℕ => if m < k then B m else 0) (∑ m ∈ Finset.range k, B m) := by
    have : HasSum (fun m : ℕ => if m < k then B m else 0)
        (∑ m ∈ Finset.range k, if m < k then B m else 0) :=
      hasSum_sum_of_ne_finset_zero fun m hm => by
        rw [Finset.mem_range] at hm; rw [if_neg hm]
    convert this using 1
    exact Finset.sum_congr rfl fun m hm => by rw [if_pos (Finset.mem_range.mp hm)]
  have hFs : HasSum F (∑ m ∈ Finset.range k, B m + 1 / 4) := hfin.add hgeo
  have hle : ∀ m, E m ≤ F m := fun m => by
    simp only [hF]
    by_cases hm : m < k
    · rw [if_pos hm]
      have h1 := hlow m hm
      have h2 : (0 : ℝ) ≤ (1 / 2) ^ (m + 3) := by positivity
      linarith
    · rw [if_neg hm, zero_add]; exact hhigh m (not_lt.mp hm)
  have hs : Summable E := Summable.of_nonneg_of_le hE0 hle hFs.summable
  exact ⟨hs, (hs.tsum_le_tsum hle hFs.summable).trans_eq hFs.tsum_eq⟩

/-! ## The continued Euler product -/

/-- `(s - 1) ζ_P(s) = G_c(s) e^{-I₀(s) + E(s)}`. -/
def theG (μ ν γ : ℝ) (M : ℕ → ℕ) (u : Cell M → ℝ) (s : ℂ) : ℂ :=
  contG μ ν γ s * cexp (-headLaplace μ ν γ s +
    discretizationError (cutPoint μ) M (invertedDensity μ ν γ) u s)

/-- The prime measure of the discretized system. -/
abbrev primeMeasure (μ ν γ : ℝ) (M : ℕ → ℕ) (u : Cell M → ℝ) : Measure ℝ :=
  eulerPrimeMeasure u (cellWeight (cutPoint μ) M (invertedDensity μ ν γ))

/-! ## Bounds at a height -/

/-- The block mass `∫_{J_m} π₀`. -/
def blockMass (μ ν γ : ℝ) (m : ℕ) : ℝ :=
  ∫ y in (cutPoint μ + m)..(cutPoint μ + m + 1), invertedDensity μ ν γ y

/-- The crude block constant `B_m = 4 e^{-2(u₀+m)/5} ∫_{J_m} π₀`. -/
def crudeConst (μ ν γ : ℝ) (m : ℕ) : ℝ :=
  4 * Real.exp (-(2 / 5 * (cutPoint μ + m))) * blockMass μ ν γ m

/-- `C_c = 150 (3 + |γ|)²`. -/
def contConst (γ : ℝ) : ℝ := 150 * (3 + |γ|) ^ 2

/-- The level `X_k = 8 C_c exp(I₀ + 1 + Σ_{m ≤ k} B_m)`. -/
def levelX (μ ν γ : ℝ) (k : ℕ) : ℝ :=
  8 * contConst γ * Real.exp (headMass μ ν γ + 1 + ∑ m ∈ Finset.range (k + 1), crudeConst μ ν γ m)

theorem levelX_nonneg (μ ν γ : ℝ) (k : ℕ) : 0 ≤ levelX μ ν γ k := by
  unfold levelX contConst; positivity

theorem one_le_contConst (γ : ℝ) : 1 ≤ contConst γ := by
  unfold contConst; nlinarith [abs_nonneg γ, sq_nonneg (3 + |γ|)]

theorem le_heights {T : ℕ → ℝ} (hT0 : 1 ≤ T 0) (hTstep : ∀ k, T k + 1 ≤ T (k + 1)) (k : ℕ) :
    (k : ℝ) + 1 ≤ T k := by
  induction k with
  | zero => simpa using hT0
  | succ k ih => push_cast; linarith [hTstep k]

theorem norm_cexp_le_norm {w : ℂ} : ‖cexp w‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (Complex.re_le_norm w)

section System

variable {μ ν γ : ℝ} (hμ2 : μ < 1 / 2) (hν0 : 0 < ν) (hν : ν < 3 * μ - 1)
  {M : ℕ → ℕ} {u : Cell M → ℝ} (hM : ∀ m, 1 ≤ M m)
  (hu : ∀ i : Cell M, u i ∈ Icc (node (cutPoint μ) M i.1 i.2) (node (cutPoint μ) M i.1 (i.2 + 1)))
include hμ2 hν0 hν

theorem u_pos (i : Cell M) (hu : ∀ i : Cell M,
    u i ∈ Icc (node (cutPoint μ) M i.1 i.2) (node (cutPoint μ) M i.1 (i.2 + 1))) :
    20 < u i := by
  have h := twenty_lt_cutPoint (by linarith : 0 < μ) hμ2
  have := le_node (M := M) (cutPoint μ) i.1 i.2
  linarith [(hu i).1, (i.1.cast_nonneg : (0 : ℝ) ≤ i.1)]

include hM hu in
/-- `G = G_c e^{-I₀ + E}` is holomorphic on `Re s > 1/3`. -/
theorem differentiableOn_theG (hMbig : ∀ m : ℕ, Real.exp (cutPoint μ + m) ≤ M m) :
    DifferentiableOn ℂ (theG μ ν γ M u) {s : ℂ | 1 / 3 < s.re} := by
  have hμ0 : 0 < μ := by linarith
  have hp₁ : 0 < 3 * μ - 1 - ν := by linarith
  have hp₂ : 0 < 3 * μ - 1 + ν := by linarith
  have h4 : 0 < 4 * μ - 1 := by linarith
  have hu₀ := twenty_lt_cutPoint hμ0 hμ2
  have hE := differentiableOn_discretizationError (measurable_invertedDensity μ ν γ hμ0)
    (invertedDensity_nonneg hμ0 hμ2 hp₁ hp₂ h4) (invertedDensity_le_exp hμ0 hμ2 hp₁ hp₂ h4) hM hu
    (by linarith) hMbig
  exact (differentiableOn_contG hp₁ hp₂).mul
    (((differentiable_headLaplace hμ0 hp₁.le hp₂.le h4.le).differentiableOn.neg.add hE).cexp)

include hM hu in
/-- **The Euler identity** on `Re s > 1`: the log-Euler series converges to `∫ u^{-s} dP`,
`ζ_P = exp ∫ u^{-s} dP`, and `(s - 1) ζ_P(s) = G(s)`. -/
theorem euler_identity {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : Cell M × ℕ =>
        ((cellWeight (cutPoint μ) M (invertedDensity μ ν γ) p.1 / ((p.2 : ℝ) + 1) : ℝ) : ℂ) *
          cexp (-(s * ((((p.2 : ℝ) + 1) * u p.1 : ℝ) : ℂ))))
      (measureDirichlet (primeMeasure μ ν γ M u) s) ∧
    measureDirichlet (beurlingIntegerMeasure (primeMeasure μ ν γ M u)) s =
      cexp (measureDirichlet (primeMeasure μ ν γ M u) s) ∧
    theG μ ν γ M u s =
      (s - 1) * measureDirichlet (beurlingIntegerMeasure (primeMeasure μ ν γ M u)) s := by
  have hμ0 : 0 < μ := by linarith
  have hp₁ : 0 < 3 * μ - 1 - ν := by linarith
  have hp₂ : 0 < 3 * μ - 1 + ν := by linarith
  have h4 : 0 < 4 * μ - 1 := by linarith
  have hu₀ := twenty_lt_cutPoint hμ0 hμ2
  have hπm := measurable_invertedDensity μ ν γ hμ0
  have hπ0 := invertedDensity_nonneg (γ := γ) hμ0 hμ2 hp₁ hp₂ h4
  have hπle := invertedDensity_le_exp (γ := γ) hμ0 hμ2 hp₁ hp₂ h4
  have hD := measureDirichlet_eulerPrimeMeasure hπm hπ0 hπle hM hu (by linarith) hs
  have hP : primeMeasure μ ν γ M u (Iic 1) = 0 :=
    eulerPrimeMeasure_Iic_one fun i => by linarith [u_pos hμ2 hν0 hν i hu]
  have hmom := integrable_rpow_neg_eulerPrimeMeasure hπm hπ0 hπle hM hu (by linarith) hs
  have hexp : measureDirichlet (beurlingIntegerMeasure (primeMeasure μ ν γ M u)) s =
      cexp (measureDirichlet (primeMeasure μ ν γ M u) s) :=
    measureDirichlet_beurlingIntegerMeasure hP hmom
  refine ⟨hD.1, hexp, ?_⟩
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  rw [hexp, hD.2, ← laplace_cutDensity_eq_tsum hμ0 hμ2 hp₁ hp₂ h4 hs, Complex.exp_add,
    cexp_laplace_cutDensity hμ0 hp₁.le hp₂.le h4.le hs, theG,
    ← sub_one_mul_overRegularZeta hp₁ hp₂ hs, Complex.exp_add]
  ring

/-- **The residue is positive**: `G(1) = A > 0`. -/
theorem exists_theG_one_eq :
    ∃ A : ℝ, 0 < A ∧ theG μ ν γ M u 1 = A := by
  have hμ0 : 0 < μ := by linarith
  have hp₁ : 0 < 3 * μ - 1 - ν := by linarith
  have hp₂ : 0 < 3 * μ - 1 + ν := by linarith
  have h4 : 0 < 4 * μ - 1 := by linarith
  obtain ⟨e, he⟩ := exists_discretizationError_one_eq (u₀ := cutPoint μ) (M := M) (u := u)
    (π := invertedDensity μ ν γ)
  have hI : headLaplace μ ν γ 1 = ((∫ v in Ioc 0 (cutPoint μ),
      Real.exp (-v) * primeDensity μ ν γ v : ℝ) : ℂ) := by
    rw [headLaplace, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
    push_cast
    ring_nf
  set c : ℝ := (μ ^ 2 + γ ^ 2) * (4 * μ) / ((3 * μ - ν) * (3 * μ + ν)) with hc
  have hc0 : 0 < c := by
    have h1 : 0 < 3 * μ - ν := by linarith
    have h2 : 0 < 3 * μ + ν := by linarith
    positivity
  refine ⟨c * Real.exp (-(∫ v in Ioc 0 (cutPoint μ), Real.exp (-v) * primeDensity μ ν γ v) + e),
    by positivity, ?_⟩
  rw [theG, contG_one, he, hI, hc]
  push_cast
  ring

omit hμ2 hν0 hν in
/-- The zeros `1 - μ ± iγ`. -/
theorem theG_zero :
    theG μ ν γ M u (((1 - μ : ℝ) : ℂ) + γ * I) = 0 ∧
      theG μ ν γ M u (((1 - μ : ℝ) : ℂ) - γ * I) = 0 := by
  rw [theG, theG, (contG_zero μ ν γ).1, (contG_zero μ ν γ).2, zero_mul, zero_mul]
  exact ⟨rfl, rfl⟩

include hM hu in
/-- At height `|Im s| < T_k` the error is at most `Σ_{m<k} B_m + 1/4`. -/
theorem norm_discretizationError_le {T : ℕ → ℝ} (hTmono : Monotone T)
    (hMfine : ∀ m : ℕ, 2 ^ (m + 4) * (2 + 2 * T m) *
      (Real.exp (-(2 / 5 * (cutPoint μ + m))) * blockMass μ ν γ m) ≤ M m)
    {s : ℂ} (hs1 : 2 / 5 ≤ s.re) (hs2 : s.re ≤ 2) {k : ℕ} (hk : |s.im| < T k) :
    ‖discretizationError (cutPoint μ) M (invertedDensity μ ν γ) u s‖ ≤
      ∑ m ∈ Finset.range k, crudeConst μ ν γ m + 1 / 4 := by
  have hμ0 : 0 < μ := by linarith
  have hp₁ : 0 < 3 * μ - 1 - ν := by linarith
  have hp₂ : 0 < 3 * μ - 1 + ν := by linarith
  have h4 : 0 < 4 * μ - 1 := by linarith
  have hu₀ := twenty_lt_cutPoint hμ0 hμ2
  have hπm := measurable_invertedDensity μ ν γ hμ0
  have hπ0 := invertedDensity_nonneg (γ := γ) hμ0 hμ2 hp₁ hp₂ h4
  have hπle := invertedDensity_le_exp (γ := γ) hμ0 hμ2 hp₁ hp₂ h4
  have hσu : 1 ≤ 2 / 5 * cutPoint μ := by linarith
  obtain ⟨hsum, hb⟩ := tsum_le_split (k := k)
    (E := fun m => ‖blockError (cutPoint μ) M (invertedDensity μ ν γ) u m s‖)
    (B := crudeConst μ ν γ) (fun m => norm_nonneg _)
    (fun m _ => norm_blockError_le hπm hπ0 hπle hM hu (by linarith) (σ₀ := 2 / 5) (by norm_num)
      hσu hs1 m)
    (fun m hm => by
      have hfine := norm_blockError_le_fine hπm hπ0 hπle hM hu (by linarith) (σ₀ := 2 / 5)
        (by norm_num) hσu hs1 m
      have hI0 : 0 ≤ blockMass μ ν γ m := integral_block_nonneg hπ0 (u₀ := cutPoint μ) m
      set κ := Real.exp (-(2 / 5 * (cutPoint μ + m))) * blockMass μ ν γ m with hκ
      have hκ0 : 0 ≤ κ := mul_nonneg (Real.exp_pos _).le hI0
      have hTm : |s.im| < T m := lt_of_lt_of_le hk (hTmono hm)
      have hsn : ‖s‖ ≤ 2 + 2 * T m := by
        have h := Complex.norm_le_abs_re_add_abs_im s
        have hre : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith, hs2⟩
        linarith [abs_nonneg s.im]
      have hM0 : (0 : ℝ) < M m := by have := hM m; positivity
      have h2 : ((1 : ℝ) / 2) ^ (m + 3) * 2 ^ (m + 4) = 2 := by
        rw [pow_succ (2 : ℝ) (m + 3), ← mul_assoc, ← mul_pow]; norm_num
      have key : 2 * ((2 + 2 * T m) * κ) ≤ (1 / 2) ^ (m + 3) * M m := by
        calc 2 * ((2 + 2 * T m) * κ) = ((1 / 2) ^ (m + 3) * 2 ^ (m + 4)) * ((2 + 2 * T m) * κ) := by
              rw [h2]
          _ = (1 / 2) ^ (m + 3) * (2 ^ (m + 4) * (2 + 2 * T m) * κ) := by ring
          _ ≤ (1 / 2) ^ (m + 3) * M m := mul_le_mul_of_nonneg_left (hMfine m) (by positivity)
      refine hfine.trans ?_
      calc 2 * (‖s‖ / M m) * Real.exp (-(2 / 5 * (cutPoint μ + m))) *
            ∫ y in (cutPoint μ + m)..(cutPoint μ + m + 1), invertedDensity μ ν γ y
          = 2 * (‖s‖ * κ) / M m := by rw [hκ, blockMass]; ring
        _ ≤ 2 * ((2 + 2 * T m) * κ) / M m := by
            gcongr
        _ ≤ (1 / 2) ^ (m + 3) := by rw [div_le_iff₀ hM0]; exact key)
  unfold discretizationError
  exact (norm_tsum_le_tsum_norm hsum).trans hb

include hM hu in
/-- **Above `T_0`**: on `|Im s| = τ ≥ T_0` there is `k` with `T_k ≤ τ` and
`‖e^{-I₀ + E}‖ ≤ X_k/(8 C_c)`. -/
theorem exists_height_bound {T : ℕ → ℝ} (hT0 : 1 ≤ T 0) (hTstep : ∀ k, T k + 1 ≤ T (k + 1))
    (hMfine : ∀ m : ℕ, 2 ^ (m + 4) * (2 + 2 * T m) *
      (Real.exp (-(2 / 5 * (cutPoint μ + m))) * blockMass μ ν γ m) ≤ M m)
    {τ : ℝ} (hτ : T 0 ≤ τ) :
    ∃ k, T k ≤ τ ∧ ∀ s : ℂ, 2 / 5 ≤ s.re → s.re ≤ 2 → |s.im| = τ →
      ‖cexp (-headLaplace μ ν γ s +
          discretizationError (cutPoint μ) M (invertedDensity μ ν γ) u s)‖ ≤
        levelX μ ν γ k / (8 * contConst γ) := by
  classical
  have hμ0 : 0 < μ := by linarith
  have hp₁ : 0 < 3 * μ - 1 - ν := by linarith
  have hp₂ : 0 < 3 * μ - 1 + ν := by linarith
  have h4 : 0 < 4 * μ - 1 := by linarith
  have hTmono : Monotone T := monotone_nat_of_le_succ fun k => by linarith [hTstep k]
  have hex : ∃ k, τ < T k := ⟨⌈τ⌉₊, lt_of_lt_of_le (by linarith [Nat.le_ceil τ])
    (le_heights hT0 hTstep ⌈τ⌉₊)⟩
  set k₁ := Nat.find hex with hk₁
  have hk₁0 : k₁ ≠ 0 := fun h => by
    have := Nat.find_spec hex
    rw [← hk₁, h] at this
    linarith
  obtain ⟨k, hk⟩ : ∃ k, k₁ = k + 1 := ⟨k₁ - 1, by omega⟩
  refine ⟨k, ?_, fun s hs1 hs2 hsτ => ?_⟩
  · have := Nat.find_min hex (show k < Nat.find hex by rw [← hk₁, hk]; omega)
    linarith
  have hE := norm_discretizationError_le hμ2 hν0 hν hM hu hTmono hMfine hs1 hs2
    (k := k₁) (by rw [hsτ]; exact Nat.find_spec hex)
  rw [hk] at hE
  have hI := norm_headLaplace_le (γ := γ) hμ0 hp₁.le hp₂.le h4.le (s := s) (by linarith)
  have hC := one_le_contConst γ
  rw [levelX, mul_div_cancel_left₀ _ (by positivity)]
  refine norm_cexp_le_norm.trans (Real.exp_le_exp.mpr ?_)
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  linarith

include hM hu in
/-- **Below `T_0`**: on `|Im s| < T_0`, `‖e^{-I₀ + E}‖ ≤ e^{I₀(0) + 1/4}`. -/
theorem norm_cexp_le_low {T : ℕ → ℝ} (hTstep : ∀ k, T k + 1 ≤ T (k + 1))
    (hMfine : ∀ m : ℕ, 2 ^ (m + 4) * (2 + 2 * T m) *
      (Real.exp (-(2 / 5 * (cutPoint μ + m))) * blockMass μ ν γ m) ≤ M m)
    {s : ℂ} (hs1 : 2 / 5 ≤ s.re) (hs2 : s.re ≤ 2) (hτ : |s.im| < T 0) :
    ‖cexp (-headLaplace μ ν γ s + discretizationError (cutPoint μ) M (invertedDensity μ ν γ) u s)‖ ≤
      Real.exp (headMass μ ν γ + 1 / 4) := by
  have hμ0 : 0 < μ := by linarith
  have hp₁ : 0 < 3 * μ - 1 - ν := by linarith
  have hp₂ : 0 < 3 * μ - 1 + ν := by linarith
  have h4 : 0 < 4 * μ - 1 := by linarith
  have hTmono : Monotone T := monotone_nat_of_le_succ fun k => by linarith [hTstep k]
  have hE := norm_discretizationError_le hμ2 hν0 hν hM hu hTmono hMfine hs1 hs2 hτ
  have hI := norm_headLaplace_le (γ := γ) hμ0 hp₁.le hp₂.le h4.le (s := s) (by linarith)
  simp only [Finset.range_zero, Finset.sum_empty, zero_add] at hE
  refine norm_cexp_le_norm.trans (Real.exp_le_exp.mpr ?_)
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  linarith

include hM hu in
/-- **Polynomial bound** `‖G(s)‖ ≤ K (1 + |Im s|)^{3/2}` on `2/5 ≤ Re s ≤ 2`. -/
theorem exists_norm_theG_le {T : ℕ → ℝ} (hT0 : 1 ≤ T 0) (hTstep : ∀ k, T k + 1 ≤ T (k + 1))
    (hTX : ∀ k, levelX μ ν γ k ^ 2 ≤ T k)
    (hMfine : ∀ m : ℕ, 2 ^ (m + 4) * (2 + 2 * T m) *
      (Real.exp (-(2 / 5 * (cutPoint μ + m))) * blockMass μ ν γ m) ≤ M m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 2 / 5 ≤ s.re → s.re ≤ 2 →
      ‖theG μ ν γ M u s‖ ≤ K * (1 + |s.im|) ^ (3 / 2 : ℝ) := by
  have hμ0 : 0 < μ := by linarith
  have hp₁ : 0 < 3 * μ - 1 - ν := by linarith
  have hp₂ : 0 < 3 * μ - 1 + ν := by linarith
  have h4 : 0 < 4 * μ - 1 := by linarith
  set e := Real.exp (headMass μ ν γ + 1 / 4) with he
  refine ⟨75 * (3 + |γ|) ^ 2 * (e + 1), by positivity, fun s hs1 hs2 => ?_⟩
  set τ := |s.im| with hτdef
  have hτ0 : 0 ≤ τ := abs_nonneg _
  have hr1 : 1 ≤ (1 + τ) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  -- `‖e^{-I₀ + E}‖ ≤ (e + 1)(1 + τ)^{1/2}`
  have hexp : ‖cexp (-headLaplace μ ν γ s +
      discretizationError (cutPoint μ) M (invertedDensity μ ν γ) u s)‖ ≤
        (e + 1) * (1 + τ) ^ (1 / 2 : ℝ) := by
    rcases lt_or_ge τ (T 0) with hlow | hhigh
    · refine (norm_cexp_le_low hμ2 hν0 hν hM hu hTstep hMfine hs1 hs2 hlow).trans ?_
      nlinarith [Real.exp_pos (headMass μ ν γ + 1 / 4)]
    · obtain ⟨k, hkτ, hb⟩ := exists_height_bound hμ2 hν0 hν hM hu hT0 hTstep hMfine hhigh
      refine (hb s hs1 hs2 rfl).trans ?_
      have hX0 := levelX_nonneg μ ν γ k
      have hC := one_le_contConst γ
      have h1 : levelX μ ν γ k / (8 * contConst γ) ≤ levelX μ ν γ k :=
        div_le_self hX0 (by linarith)
      have h2 : levelX μ ν γ k ≤ Real.sqrt (T k) := Real.le_sqrt_of_sq_le (hTX k)
      have h3 : Real.sqrt (T k) ≤ (1 + τ) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt (by linarith)
      nlinarith [Real.exp_pos (headMass μ ν γ + 1 / 4)]
  have hG := norm_contG_le (γ := γ) hμ0 hμ2.le hp₁ hp₂ h4 hs1 hs2
  rw [theG, norm_mul]
  have hpow : (1 + τ) ^ (3 / 2 : ℝ) = (1 + τ) * (1 + τ) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  rw [hpow]
  calc ‖contG μ ν γ s‖ * ‖cexp (-headLaplace μ ν γ s +
        discretizationError (cutPoint μ) M (invertedDensity μ ν γ) u s)‖
      ≤ (75 * (3 + |γ|) ^ 2 * (1 + τ)) * ((e + 1) * (1 + τ) ^ (1 / 2 : ℝ)) :=
        mul_le_mul hG hexp (norm_nonneg _) (by positivity)
    _ = 75 * (3 + |γ|) ^ 2 * (e + 1) * ((1 + τ) * (1 + τ) ^ (1 / 2 : ℝ)) := by ring

include hM hu in
/-- **The defect scale**: on `|Im s| = τ ≥ T_0`, `‖G(s)/(s - 1)‖ ≤ X_k/8` with `T_k ≤ τ`. -/
theorem exists_norm_theG_div_le {T : ℕ → ℝ} (hT0 : 1 ≤ T 0) (hTstep : ∀ k, T k + 1 ≤ T (k + 1))
    (hMfine : ∀ m : ℕ, 2 ^ (m + 4) * (2 + 2 * T m) *
      (Real.exp (-(2 / 5 * (cutPoint μ + m))) * blockMass μ ν γ m) ≤ M m)
    {τ : ℝ} (hτ : T 0 ≤ τ) :
    ∃ k, T k ≤ τ ∧ ∀ s : ℂ, 2 / 5 ≤ s.re → s.re ≤ 2 → |s.im| = τ →
      ‖theG μ ν γ M u s / (s - 1)‖ ≤ levelX μ ν γ k / 8 := by
  have hμ0 : 0 < μ := by linarith
  have hp₁ : 0 < 3 * μ - 1 - ν := by linarith
  have hp₂ : 0 < 3 * μ - 1 + ν := by linarith
  have h4 : 0 < 4 * μ - 1 := by linarith
  obtain ⟨k, hkτ, hb⟩ := exists_height_bound hμ2 hν0 hν hM hu hT0 hTstep hMfine hτ
  refine ⟨k, hkτ, fun s hs1 hs2 hsτ => ?_⟩
  have hC := one_le_contConst γ
  have hcd := norm_contG_div_le (γ := γ) hμ0 hμ2.le hp₁ hp₂ h4 hs1 hs2 (by linarith)
  have e : theG μ ν γ M u s / (s - 1) = contG μ ν γ s / (s - 1) * cexp (-headLaplace μ ν γ s +
      discretizationError (cutPoint μ) M (invertedDensity μ ν γ) u s) := by
    rw [theG]; ring
  rw [e, norm_mul]
  calc ‖contG μ ν γ s / (s - 1)‖ * ‖cexp (-headLaplace μ ν γ s +
        discretizationError (cutPoint μ) M (invertedDensity μ ν γ) u s)‖
      ≤ contConst γ * (levelX μ ν γ k / (8 * contConst γ)) :=
        mul_le_mul hcd (hb s hs1 hs2 hsτ) (norm_nonneg _) (by linarith)
    _ = levelX μ ν γ k / 8 := by field_simp

end System

/-! ## Theorem II.3 -/

/-- The critical-line FE defect is at most the two continued values: `|χ| = 1` on the line. -/
theorem norm_stripDefect_le (G : ℂ → ℂ) (t : ℝ) :
    ‖stripDefect G t‖ ≤ ‖G ((1 / 2 : ℂ) + (2 * t : ℝ) * I) / ((1 / 2 : ℂ) + (2 * t : ℝ) * I - 1)‖ +
      ‖G (1 - ((1 / 2 : ℂ) + (2 * t : ℝ) * I)) / (1 - ((1 / 2 : ℂ) + (2 * t : ℝ) * I) - 1)‖ := by
  set s : ℂ := (1 / 2 : ℂ) + (2 * t : ℝ) * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hre]; norm_num)
  have hχ : ‖Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s‖ = 1 := by
    rw [norm_div, norm_Gammaℝ_one_sub_of_re_eq_half hre, div_self (norm_ne_zero_iff.mpr hΓ)]
  rw [stripDefect, ← hs]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, hχ, one_mul]

/-- **Theorem II.3.**  For every `Φ → ∞` and every `μ < 1/2`, `0 < ν < 3μ - 1` (so `μ > 1/3`),
`γ ∈ ℝ` there is a countable positive-weighted Beurling system with `ℚ`-independent generator
logarithms `u_i ≥ 10`, whose Euler product `ζ_P = Π_i (1 - e^{-s u_i})^{-w_i}` continues to
`Re s > 1/3` as `G(s)/(s - 1)` (`G(1) = A > 0`, zeros `1 - μ ± iγ`), has integer count
`A x + O(x^{4/5})`, and lies in the Hamburger strip class with critical-line defect
`‖g(t)‖ ≤ Φ(|t|)` for `|t| ≥ T₀`. -/
theorem exists_positiveWeighted_beurling_slow_defect {Φ : ℝ → ℝ} (hΦ : Tendsto Φ atTop atTop)
    {μ ν γ : ℝ} (hμ2 : μ < 1 / 2) (hν0 : 0 < ν) (hν : ν < 3 * μ - 1) :
    ∃ (ι : Type) (_ : Countable ι) (u w : ι → ℝ),
      (∀ i, 10 ≤ u i) ∧ (∀ i, 0 < w i) ∧ (∀ X : ℝ, {i | u i ≤ X}.Finite) ∧
      LinearIndependent ℚ u ∧
      ∃ (A K T₀ : ℝ) (G : ℂ → ℂ), 0 < A ∧
        (∀ s : ℂ, 1 < s.re →
          HasSum (fun p : ι × ℕ => ((w p.1 / ((p.2 : ℝ) + 1) : ℝ) : ℂ) *
              cexp (-(s * ((((p.2 : ℝ) + 1) * u p.1 : ℝ) : ℂ))))
            (measureDirichlet (eulerPrimeMeasure u w) s) ∧
          measureDirichlet (beurlingIntegerMeasure (eulerPrimeMeasure u w)) s =
            cexp (measureDirichlet (eulerPrimeMeasure u w) s)) ∧
        DifferentiableOn ℂ G {s : ℂ | 1 / 3 < s.re} ∧
        (∀ s : ℂ, 1 < s.re →
          G s = (s - 1) * measureDirichlet (beurlingIntegerMeasure (eulerPrimeMeasure u w)) s) ∧
        G 1 = A ∧ G (((1 - μ : ℝ) : ℂ) + γ * I) = 0 ∧ G (((1 - μ : ℝ) : ℂ) - γ * I) = 0 ∧
        (∀ x : ℝ, 1 ≤ x → beurlingIntegerMeasure (eulerPrimeMeasure u w) (Icc 1 x) < ⊤ ∧
          |(beurlingIntegerMeasure (eulerPrimeMeasure u w)).real (Icc 1 x) - A * x| ≤
            K * x ^ (4 / 5 : ℝ)) ∧
        HamburgerStripDefect (measureDirichlet (beurlingIntegerMeasure (eulerPrimeMeasure u w)))
          ((A : ℂ) / 2) (stripDefect G) ∧
        ∀ t : ℝ, T₀ ≤ |t| → ‖stripDefect G t‖ ≤ Φ |t| := by
  have hμ0 : 0 < μ := by linarith
  have hp₁ : 0 < 3 * μ - 1 - ν := by linarith
  have hp₂ : 0 < 3 * μ - 1 + ν := by linarith
  have h4 : 0 < 4 * μ - 1 := by linarith
  have hu₀ := twenty_lt_cutPoint hμ0 hμ2
  have hπm := measurable_invertedDensity μ ν γ hμ0
  have hπ0 := invertedDensity_nonneg (γ := γ) hμ0 hμ2 hp₁ hp₂ h4
  have hπle := invertedDensity_le_exp (γ := γ) hμ0 hμ2 hp₁ hp₂ h4
  -- heights and cell counts
  obtain ⟨T, hT0, hTstep, hTX, hTΦ⟩ := exists_heights hΦ (levelX μ ν γ)
  have hTmono : Monotone T := monotone_nat_of_le_succ fun k => by linarith [hTstep k]
  have hTnn : ∀ m, 0 ≤ T m := fun m => by linarith [hTmono (Nat.zero_le m)]
  set M : ℕ → ℕ := fun m => ⌈Real.exp (cutPoint μ + m) + 2 ^ (m + 4) * (2 + 2 * T m) *
    (Real.exp (-(2 / 5 * (cutPoint μ + m))) * blockMass μ ν γ m)⌉₊ + 1 with hMdef
  have hM : ∀ m, 1 ≤ M m := fun m => Nat.le_add_left 1 _
  have hfine0 : ∀ m : ℕ, 0 ≤ 2 ^ (m + 4) * (2 + 2 * T m) *
      (Real.exp (-(2 / 5 * (cutPoint μ + m))) * blockMass μ ν γ m) := fun m => by
    have := integral_block_nonneg hπ0 (u₀ := cutPoint μ) m
    have := hTnn m
    unfold blockMass
    positivity
  have hMge : ∀ m : ℕ, Real.exp (cutPoint μ + m) + 2 ^ (m + 4) * (2 + 2 * T m) *
      (Real.exp (-(2 / 5 * (cutPoint μ + m))) * blockMass μ ν γ m) ≤ M m := fun m => by
    refine (Nat.le_ceil _).trans ?_
    simp only [hMdef]
    push_cast
    linarith
  have hMbig : ∀ m : ℕ, Real.exp (cutPoint μ + m) ≤ M m := fun m => by
    linarith [hMge m, hfine0 m]
  have hMfine : ∀ m : ℕ, 2 ^ (m + 4) * (2 + 2 * T m) *
      (Real.exp (-(2 / 5 * (cutPoint μ + m))) * blockMass μ ν γ m) ≤ M m := fun m => by
    linarith [hMge m, Real.exp_pos (cutPoint μ + m)]
  -- `ℚ`-independent points in the cells
  obtain ⟨u, hu, hli⟩ := exists_linearIndependent_mem_Ioo (ι := Cell M)
    (a := fun i => node (cutPoint μ) M i.1 i.2) (b := fun i => node (cutPoint μ) M i.1 (i.2 + 1))
    (fun i => by
      have h1 := le_node (M := M) (cutPoint μ) i.1 i.2
      have h2 : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg _
      show 0 < node (cutPoint μ) M i.1 i.2
      linarith)
    (fun i => by
      have h := node_succ_sub (M := M) (cutPoint μ) i.1 i.2
      have hM0 : (0 : ℝ) < 1 / M i.1 := by have := hM i.1; positivity
      linarith)
  have hu' : ∀ i : Cell M, u i ∈ Icc (node (cutPoint μ) M i.1 i.2)
      (node (cutPoint μ) M i.1 (i.2 + 1)) := fun i => Ioo_subset_Icc_self (hu i)
  set P := primeMeasure μ ν γ M u with hPdef
  set G := theG μ ν γ M u with hGdef
  have hP1 : P (Iic 1) = 0 :=
    eulerPrimeMeasure_Iic_one fun i => by linarith [u_pos hμ2 hν0 hν i hu']
  haveI : SFinite (beurlingIntegerMeasure P) := by unfold beurlingIntegerMeasure; infer_instance
  have hsupp : beurlingIntegerMeasure P (Iio 1) = 0 := beurlingIntegerMeasure_Iio_one_eq_zero hP1
  have hmom : Integrable (fun x : ℝ => 1 / x ^ 2) (beurlingIntegerMeasure P) := by
    have h := integrable_rpow_neg_beurlingIntegerMeasure hP1 (σ := 2)
      (integrable_rpow_neg_eulerPrimeMeasure hπm hπ0 hπle hM hu' (by linarith) (by norm_num))
    refine h.congr ?_
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with x hx
    rw [Real.rpow_neg (by linarith), one_div]
    norm_cast
  have hGd := differentiableOn_theG (γ := γ) hμ2 hν0 hν hM hu' hMbig
  have hGZ : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * measureDirichlet (beurlingIntegerMeasure P) s :=
    fun s hs => (euler_identity (γ := γ) hμ2 hν0 hν hM hu' hs).2.2
  obtain ⟨K₀, hK₀, hGb⟩ := exists_norm_theG_le (γ := γ) hμ2 hν0 hν hM hu' hT0 hTstep hTX hMfine
  obtain ⟨A, hA0, hA⟩ := exists_theG_one_eq (γ := γ) hμ2 hν0 hν (M := M) (u := u)
  replace hA : G 1 = A := hA
  -- the count
  obtain ⟨K, -, hcount⟩ :=
    exists_abs_count_sub_le hsupp hmom (σ₁ := 1 / 3) (by norm_num) hGd hGZ hGb
  have hGre : (G 1).re = A := by rw [hA]; simp
  -- the Hamburger strip class
  have hstrip : ∀ s ∈ HTGeometry.verticalStrip (1 / 2) (3 / 2), 2 / 5 ≤ s.re ∧ s.re ≤ 2 := by
    intro s hs
    rw [HTGeometry.mem_verticalStrip] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hHam := hamburgerStripDefect_of_stripContinuation (Z := measureDirichlet
    (beurlingIntegerMeasure P)) (G := G) (C₀ := K₀) (N₀ := 2)
    (hGd.continuousOn.mono fun s hs => by
      show 1 / 3 < s.re; linarith [(hstrip s hs).1])
    (hGd.mono fun s hs => by show 1 / 3 < s.re; linarith [hs.1])
    (fun s hs => hGZ s (by rw [hs]; norm_num))
    (fun s hs => by
      refine (hGb s (hstrip s hs).1 (hstrip s hs).2).trans
        (mul_le_mul_of_nonneg_left ?_ hK₀)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s.im]) (by norm_num))
  rw [hA] at hHam
  refine ⟨Cell M, inferInstance, u, cellWeight (cutPoint μ) M (invertedDensity μ ν γ),
    fun i => by linarith [u_pos hμ2 hν0 hν i hu'],
    fun i => cellWeight_pos hπm hπ0 hπle hM
      (fun y hy => invertedDensity_pos hμ0 hμ2 hp₁ hp₂ h4 hy) i, ?_, hli,
    A, K, T 0, G, hA0, fun s hs => ⟨(euler_identity (γ := γ) hμ2 hν0 hν hM hu' hs).1,
      (euler_identity (γ := γ) hμ2 hν0 hν hM hu' hs).2.1⟩, hGd, hGZ, hA,
    (theG_zero (μ := μ) (ν := ν) (γ := γ) (M := M) (u := u)).1,
    (theG_zero (μ := μ) (ν := ν) (γ := γ) (M := M) (u := u)).2,
    fun x hx => by rw [← hGre]; exact hcount x hx, hHam, fun t ht => ?_⟩
  · -- local finiteness
    intro X
    refine (Finset.finite_toSet ((Finset.range (⌊X⌋₊ + 1)).sigma fun m => Finset.univ)).subset ?_
    intro i hi
    simp only [Set.mem_setOf_eq] at hi
    simp only [Finset.coe_sigma, Finset.coe_range, Finset.coe_univ, Set.mem_sigma_iff,
      Set.mem_Iio, Set.mem_univ, and_true]
    have h1 := le_node (M := M) (cutPoint μ) i.1 i.2
    have h2 : (i.1 : ℝ) ≤ X := by linarith [(hu' i).1]
    have h3 : i.1 ≤ ⌊X⌋₊ := Nat.le_floor h2
    omega
  · -- the defect bound
    have hτ : T 0 ≤ 2 * |t| := by linarith [hT0, abs_nonneg t]
    obtain ⟨k, hkτ, hb⟩ := exists_norm_theG_div_le (γ := γ) hμ2 hν0 hν hM hu' hT0 hTstep hMfine hτ
    have h1 := hb ((1 / 2 : ℂ) + (2 * t : ℝ) * I) (by simp; norm_num) (by simp; norm_num)
      (by simp [abs_mul])
    have h2 := hb (1 - ((1 / 2 : ℂ) + (2 * t : ℝ) * I)) (by simp; norm_num) (by simp; norm_num)
      (by simp [abs_mul])
    have hΦk := hTΦ k |t| (by linarith)
    have hX0 := levelX_nonneg μ ν γ k
    calc ‖stripDefect G t‖ ≤ levelX μ ν γ k / 8 + levelX μ ν γ k / 8 :=
          (norm_stripDefect_le G t).trans (add_le_add h1 h2)
      _ ≤ levelX μ ν γ k := by linarith
      _ ≤ Φ |t| := hΦk

end GaloisForLFunctions.EulerFETransportTheory.SlowDefect
