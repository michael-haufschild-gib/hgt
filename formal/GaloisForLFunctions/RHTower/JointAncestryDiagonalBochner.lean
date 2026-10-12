import GaloisForLFunctions.RHTower.DiagonalLaurentCoefficients
import GaloisForLFunctions.RHTower.JointAncestryProductComplexity

/-!
# The diagonal Bochner bound for JAS product tests

Take a finite set `P` of primes `p > X`, all with `log p ∈ [u, u + h]`, and test the JAS product
aggregate at level `σ` with the uniform vectors `z_p = r e^{−iθ}`.  Each Bernoulli factor is
`(1 + r²)(1 + a_p(p^{ρ−½} e^{iθ} + p^{−(ρ−½)} e^{−iθ}))` with `a_p = r/(1 + r²) · p^{−σ}`.  Positivity
for every `θ` and Bochner's inequality on the circle give `|ĉ₁ + conj ĉ₋₁| ≤ 2 Re ĉ₀`.  The
coefficients are computed zero by zero: write `p^{ρ−½} = B_ρ β_p`, with `B_ρ = e^{(ρ−½)u}` and
`|β_p^{±1}| ≤ e^{h/2}`, and apply the weighted remainder bound of `DiagonalLaurentCoefficients`.

**Theorem** (`abs_sum_weilLagFunctionReal_le_of_jasProductPositiveAbove`).  If `|Re ρ − ½| ≤ α`
for every zero and `u ≥ 0`, then
`|Σ_{p ∈ P} a_p Φ(log p)| ≤ Φ(0) + (Σ_ρ |w_ρ|) · R · (1 + e^{αu})`, where
`R = ∏(1 + 2a_p e^{h/2}) − 1 − 2 Σ a_p e^{h/2}` is quadratic in the total weight.  So a positive
product test on many primes in a narrow window bounds the window average of the lag function at
level `0`.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- `p^{ρ−½}`. -/
def diagX (q : XiZeroCopy) (p : Nat.Primes) : ℂ := cexp ((Real.log p : ℂ) * ((q.1 : ℂ) - 1 / 2))

/-- `p^{−(ρ−½)}`. -/
def diagY (q : XiZeroCopy) (p : Nat.Primes) : ℂ := cexp (-((Real.log p : ℂ) * ((q.1 : ℂ) - 1 / 2)))

/-- The weights `a_p = r/(1 + r²) · p^{−σ}`. -/
def diagA (σ r : ℝ) (p : Nat.Primes) : ℝ := r / (1 + r ^ 2) * Real.exp (-σ * Real.log p)

theorem diagA_nonneg {σ r : ℝ} (hr : 0 ≤ r) (p : Nat.Primes) : 0 ≤ diagA σ r p := by
  unfold diagA; positivity

/-- The Bernoulli factor at the uniform vector `r e^{−iθ}`. -/
theorem jasBernoulliFactor_diag (q : XiZeroCopy) (σ r : ℝ) (p : Nat.Primes) (N j : ℕ) :
    jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) ((r : ℂ) * unitRoot N ^ (-(j : ℤ))) =
      ((1 + r ^ 2 : ℝ) : ℂ) * (1 + (diagA σ r p : ℂ) *
        (diagX q p * unitRoot N ^ (j : ℤ) + diagY q p * unitRoot N ^ (-(j : ℤ)))) := by
  have h1 : (0 : ℝ) < 1 + r ^ 2 := by positivity
  have hconj : conj ((r : ℂ) * unitRoot N ^ (-(j : ℤ))) = (r : ℂ) * unitRoot N ^ (j : ℤ) := by
    rw [map_mul, Complex.conj_ofReal, conj_unitRoot_zpow, neg_neg]
  have hprod : unitRoot N ^ (-(j : ℤ)) * unitRoot N ^ (j : ℤ) = 1 := by
    rw [← zpow_add₀ (unitRoot_ne_zero N)]; simp
  have hA : jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p =
      (Real.exp (-σ * Real.log p) : ℂ) * diagY q p := by
    unfold jasHoloA diagY; rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  have hB : jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p =
      (Real.exp (-σ * Real.log p) : ℂ) * diagX q p := by
    unfold jasHoloB diagX; rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  have hne : (1 + (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h1.ne'
  have key : (1 + (r : ℂ) ^ 2) * (diagA σ r p : ℂ) = (r : ℂ) * (Real.exp (-σ * Real.log p) : ℂ) := by
    unfold diagA
    push_cast
    field_simp
  unfold jasBernoulliFactor
  rw [hconj, hA, hB, show ((1 + r ^ 2 : ℝ) : ℂ) = 1 + (r : ℂ) ^ 2 by push_cast; ring]
  linear_combination (r : ℂ) ^ 2 * hprod -
    (diagX q p * unitRoot N ^ (j : ℤ) + diagY q p * unitRoot N ^ (-(j : ℤ))) * key

theorem prod_jasBernoulliFactor_diag (q : XiZeroCopy) (σ r : ℝ) (P : Finset Nat.Primes) (N j : ℕ) :
    ∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) ((r : ℂ) * unitRoot N ^ (-(j : ℤ))) =
      ((1 + r ^ 2 : ℝ) : ℂ) ^ P.card * diagProd (diagA σ r) (diagX q) (diagY q) P.toList N j := by
  rw [Finset.prod_congr rfl fun p _ => jasBernoulliFactor_diag q σ r p N j, Finset.prod_mul_distrib,
    Finset.prod_const, diagProd, Finset.prod_map_toList]

/-! ## Norm bounds -/

theorem norm_diagX_le (q : XiZeroCopy) (p : Nat.Primes) :
    ‖diagX q p‖ ≤ Real.exp (1 / 2 * Real.log p) := by
  rw [diagX, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hL := log_prime_pos p
  have := xiZeroCopy_re_lt_one q
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    zero_mul, sub_zero]
  norm_num
  nlinarith

theorem norm_diagY_le (q : XiZeroCopy) (p : Nat.Primes) :
    ‖diagY q p‖ ≤ Real.exp (1 / 2 * Real.log p) := by
  rw [diagY, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hL := log_prime_pos p
  have := xiZeroCopy_re_pos q
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    zero_mul, sub_zero]
  norm_num
  nlinarith

theorem norm_diagProd_le (q : XiZeroCopy) {σ r : ℝ} (hr : 0 ≤ r) (P : Finset Nat.Primes) (N j : ℕ) :
    ‖diagProd (diagA σ r) (diagX q) (diagY q) P.toList N j‖ ≤
      ∏ p ∈ P, (1 + 2 * diagA σ r p * Real.exp (1 / 2 * Real.log p)) := by
  rw [diagProd, Finset.prod_map_toList]
  refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => ?_)
  have ha := diagA_nonneg (σ := σ) hr p
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  have h2 : ‖diagX q p * unitRoot N ^ (j : ℤ) + diagY q p * unitRoot N ^ (-(j : ℤ))‖ ≤
      2 * Real.exp (1 / 2 * Real.log p) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_unitRoot_zpow, norm_unitRoot_zpow, mul_one, mul_one]
    linarith [norm_diagX_le q p, norm_diagY_le q p]
  nlinarith

/-! ## The aggregate and its positivity -/

/-- The JAS aggregate of the uniform test at the `j`-th root of unity, normalized by `(1+r²)^{|P|}`. -/
def diagAggregate (σ r : ℝ) (P : Finset Nat.Primes) (N j : ℕ) : ℂ :=
  ∑' q : XiZeroCopy,
    diagProd (diagA σ r) (diagX q) (diagY q) P.toList N j / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))

theorem summable_diagProd_div {σ r : ℝ} (hr : 0 ≤ r) (P : Finset Nat.Primes) (N j : ℕ) :
    Summable fun q : XiZeroCopy =>
      diagProd (diagA σ r) (diagX q) (diagY q) P.toList N j / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
  refine Summable.of_norm_bounded
    (summable_inv_mul_one_sub.norm.mul_left (∏ p ∈ P, (1 + 2 * diagA σ r p *
      Real.exp (1 / 2 * Real.log p)))) fun q => ?_
  rw [div_eq_mul_one_div, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_diagProd_le q hr P N j) (norm_nonneg _)

/-- Product positivity on one prime set `P` with a constant test vector `z_p = z`. -/
def JasConstProductPositiveOn (P : Finset Nat.Primes) (σ : ℝ) : Prop :=
  ∀ z : ℂ, 0 ≤ (∑' q : XiZeroCopy,
    (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) z) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re

theorem JasProductPositiveAbove.constOn {X : ℕ} {σ : ℝ} (h : JasProductPositiveAbove X σ)
    {P : Finset Nat.Primes} (hP : ∀ p ∈ P, X < (p : ℕ)) : JasConstProductPositiveOn P σ :=
  fun z => h P hP fun _ => z

theorem re_diagAggregate_nonneg {σ : ℝ} {P : Finset Nat.Primes} (h : JasConstProductPositiveOn P σ)
    (r : ℝ) (N j : ℕ) : 0 ≤ (diagAggregate σ r P N j).re := by
  have h0 := h ((r : ℂ) * unitRoot N ^ (-(j : ℤ)))
  have e : ∀ q : XiZeroCopy, (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) ((r : ℂ) * unitRoot N ^ (-(j : ℤ)))) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
      (((1 + r ^ 2) ^ P.card : ℝ) : ℂ) *
        (diagProd (diagA σ r) (diagX q) (diagY q) P.toList N j / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
    intro q
    rw [prod_jasBernoulliFactor_diag]
    push_cast
    ring
  simp only [e] at h0
  rw [tsum_mul_left, Complex.re_ofReal_mul] at h0
  have hc : 0 < ((1 + r ^ 2) ^ P.card : ℝ) := by positivity
  unfold diagAggregate
  exact nonneg_of_mul_nonneg_right h0 hc

/-! ## Interchange with the zero sum -/

theorem diagFourier_tsum {F : XiZeroCopy → ℕ → ℂ} (hF : ∀ j, Summable fun q => F q j) (N : ℕ)
    (m : ℤ) : diagFourier (fun j => ∑' q, F q j) N m = ∑' q, diagFourier (F q) N m := by
  unfold diagFourier
  have h1 : ∀ j : ℕ, (∑' q, F q j) * unitRoot N ^ (-(j : ℤ) * m) =
      ∑' q, F q j * unitRoot N ^ (-(j : ℤ) * m) := fun j => tsum_mul_right.symm
  simp_rw [h1]
  rw [← Summable.tsum_finsetSum (fun j _ => (hF j).mul_right _), ← tsum_mul_left]

theorem diagFourier_div_const (D : ℕ → ℂ) (c : ℂ) (N : ℕ) (m : ℤ) :
    diagFourier (fun j => D j / c) N m = diagFourier D N m / c := by
  unfold diagFourier
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  ring

theorem diagFourier_diagAggregate {σ r : ℝ} (hr : 0 ≤ r) (P : Finset Nat.Primes) {m : ℤ}
    (hm : |m| ≤ 1) :
    diagFourier (diagAggregate σ r P (P.card + 2)) (P.card + 2) m =
      ∑' q : XiZeroCopy, laurentCoef (diagA σ r) (diagX q) (diagY q) P.toList m /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
  have h1 := diagFourier_tsum (F := fun q j =>
    diagProd (diagA σ r) (diagX q) (diagY q) P.toList (P.card + 2) j / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))
    (fun j => summable_diagProd_div hr P _ j) (P.card + 2) m
  unfold diagAggregate
  rw [h1]
  refine tsum_congr fun q => ?_
  rw [diagFourier_div_const, diagFourier_diagProd_eq _ _ _ (by omega)]
  rw [Finset.length_toList]
  push_cast
  linarith

/-! ## The bound -/

theorem norm_diagX_le_window (q : XiZeroCopy) (p : Nat.Primes) {u h : ℝ}
    (hw : u ≤ Real.log p ∧ Real.log p ≤ u + h) :
    ‖diagX q p‖ ≤ Real.exp (h / 2) * Real.exp (((q.1 : ℂ).re - 1 / 2) * u) := by
  rw [diagX, Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := xiZeroCopy_re_pos q
  have h2 := xiZeroCopy_re_lt_one q
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, zero_mul,
    sub_zero]
  norm_num
  nlinarith [hw.1, hw.2]

theorem norm_diagY_le_window (q : XiZeroCopy) (p : Nat.Primes) {u h : ℝ}
    (hw : u ≤ Real.log p ∧ Real.log p ≤ u + h) :
    ‖diagY q p‖ ≤ Real.exp (h / 2) * (Real.exp (((q.1 : ℂ).re - 1 / 2) * u))⁻¹ := by
  rw [diagY, Complex.norm_exp, ← Real.exp_neg, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := xiZeroCopy_re_pos q
  have h2 := xiZeroCopy_re_lt_one q
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    zero_mul, sub_zero]
  norm_num
  nlinarith [hw.1, hw.2]

/-- **The diagonal Bochner bound.**  If the product tests with constant vectors are positive on a
set `P` of primes with `log p ∈ [u, u + h]`, then
`|Σ_P a_p Φ(log p)| ≤ Φ(0) + (Σ_ρ|w_ρ|)·R·(1 + e^{αu})`, where
`R = ∏(1 + 2a_p e^{h/2}) − 1 − 2Σ a_p e^{h/2}` and `|Re ρ − ½| ≤ α`. -/
theorem abs_sum_weilLagFunctionReal_le_of_constPositive {σ : ℝ} {α u h r : ℝ}
    (hα : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α) (hu : 0 ≤ u) (hr : 0 ≤ r)
    (P : Finset Nat.Primes) (hpos : JasConstProductPositiveOn P σ)
    (hwin : ∀ p ∈ P, u ≤ Real.log p ∧ Real.log p ≤ u + h) :
    |∑ p ∈ P, diagA σ r p * weilLagFunctionReal (Real.log p)| ≤
      poleSharpConstant + lagWeightTotal *
        ((∏ p ∈ P, (1 + 2 * (diagA σ r p * Real.exp (h / 2)))) - 1 -
          2 * ∑ p ∈ P, diagA σ r p * Real.exp (h / 2)) * (1 + Real.exp (α * u)) := by
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (∏ p ∈ P, (1 + 2 * (diagA σ r p * Real.exp (h / 2)))) - 1 -
      2 * ∑ p ∈ P, diagA σ r p * Real.exp (h / 2) := ⟨_, rfl⟩
  rw [← hRdef]
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = P.card + 2 := ⟨_, rfl⟩
  have hN : N ≠ 0 := by omega
  -- per-zero remainder bounds
  have hrem : ∀ (q : XiZeroCopy) (m : ℤ),
      ‖laurentRem (diagA σ r) (diagX q) (diagY q) P.toList m‖ ≤
        Real.exp (((q.1 : ℂ).re - 1 / 2) * u) ^ m * R := by
    intro q m
    have hB := Real.exp_pos (((q.1 : ℂ).re - 1 / 2) * u)
    have := norm_laurentRem_le (diagA σ r) (diagX q) (diagY q)
      (fun p => diagA σ r p * Real.exp (h / 2)) hB P.toList
      (fun p _ => mul_nonneg (diagA_nonneg hr p) (Real.exp_pos _).le)
      (fun p hp => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (diagA_nonneg hr p),
          mul_assoc]
        exact mul_le_mul_of_nonneg_left (norm_diagX_le_window q p
          (hwin p (Finset.mem_toList.mp hp))) (diagA_nonneg hr p))
      (fun p hp => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (diagA_nonneg hr p),
          mul_assoc]
        exact mul_le_mul_of_nonneg_left (norm_diagY_le_window q p
          (hwin p (Finset.mem_toList.mp hp))) (diagA_nonneg hr p)) m
    rwa [Finset.prod_map_toList, Finset.sum_map_toList, ← hRdef] at this
  have hR0 : 0 ≤ R := by
    have := one_add_sum_le_prod_one_add P (fun p => 2 * (diagA σ r p * Real.exp (h / 2)))
      (fun p _ => mul_nonneg (by norm_num) (mul_nonneg (diagA_nonneg hr p) (Real.exp_pos _).le))
    rw [hRdef, Finset.mul_sum]
    linarith
  have hBm : ∀ (q : XiZeroCopy) (m : ℤ), |m| ≤ 1 →
      Real.exp (((q.1 : ℂ).re - 1 / 2) * u) ^ m ≤ Real.exp (α * u) := by
    intro q m hm
    have hq := abs_le.mp (hα q)
    have hα0 : 0 ≤ α := (abs_nonneg _).trans (hα q)
    rcases (show m = -1 ∨ m = 0 ∨ m = 1 by rcases abs_le.mp hm with ⟨h1, h2⟩; omega) with
      rfl | rfl | rfl
    · rw [zpow_neg_one, ← Real.exp_neg]
      exact Real.exp_le_exp.mpr (by nlinarith)
    · rw [zpow_zero]; exact Real.one_le_exp (mul_nonneg hα0 hu)
    · rw [zpow_one]; exact Real.exp_le_exp.mpr (by nlinarith)
  have hremB : ∀ (q : XiZeroCopy) (m : ℤ), |m| ≤ 1 →
      ‖laurentRem (diagA σ r) (diagX q) (diagY q) P.toList m‖ ≤ Real.exp (α * u) * R :=
    fun q m hm => (hrem q m).trans (mul_le_mul_of_nonneg_right (hBm q m hm) hR0)
  -- the coefficients of the aggregate
  have hT : ∀ j < N, 0 ≤ (diagAggregate σ r P N j).re :=
    fun j _ => re_diagAggregate_nonneg hpos r N j
  have hBoch := norm_diagFourier_one_add_conj_le hN hT
  have hc : ∀ m : ℤ, |m| ≤ 1 → diagFourier (diagAggregate σ r P N) N m =
      ∑' q : XiZeroCopy, laurentCoef (diagA σ r) (diagX q) (diagY q) P.toList m /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
    intro m hm; rw [hNdef]; exact diagFourier_diagAggregate hr P hm
  rw [hc 1 (by norm_num), hc (-1) (by norm_num), hc 0 (by norm_num)] at hBoch
  -- splitting off the constant and linear parts
  have hsplit : ∀ (q : XiZeroCopy) (m : ℤ),
      laurentCoef (diagA σ r) (diagX q) (diagY q) P.toList m =
        laurentMain (diagA σ r) (diagX q) (diagY q) P.toList m +
          laurentRem (diagA σ r) (diagX q) (diagY q) P.toList m := fun q m => by
    rw [laurentRem]; ring
  have hm0 : ∀ q : XiZeroCopy, laurentMain (diagA σ r) (diagX q) (diagY q) P.toList 0 = 1 := by
    intro q; simp [laurentMain]
  have hm1 : ∀ q : XiZeroCopy, laurentMain (diagA σ r) (diagX q) (diagY q) P.toList 1 =
      ∑ p ∈ P, (diagA σ r p : ℂ) * diagX q p := by
    intro q; simp [laurentMain, Finset.sum_map_toList]
  have hmm1 : ∀ q : XiZeroCopy, laurentMain (diagA σ r) (diagX q) (diagY q) P.toList (-1) =
      ∑ p ∈ P, (diagA σ r p : ℂ) * diagY q p := by
    intro q; simp [laurentMain, Finset.sum_map_toList]
  simp only [hsplit, hm0, hm1, hmm1, add_div] at hBoch
  -- summability
  have hw : Summable fun q : XiZeroCopy => 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) :=
    summable_inv_mul_one_sub
  have hremS : ∀ m : ℤ, |m| ≤ 1 → Summable fun q : XiZeroCopy =>
      laurentRem (diagA σ r) (diagX q) (diagY q) P.toList m / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
    intro m hm
    refine Summable.of_norm_bounded (hw.norm.mul_left (Real.exp (α * u) * R)) fun q => ?_
    rw [div_eq_mul_one_div, norm_mul]
    exact mul_le_mul_of_nonneg_right (hremB q m hm) (norm_nonneg _)
  have hXS : ∀ p : Nat.Primes, Summable fun q : XiZeroCopy =>
      diagX q p / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := fun p => by
    refine Summable.of_norm_bounded (hw.norm.mul_left (Real.exp (1 / 2 * Real.log p))) fun q => ?_
    rw [div_eq_mul_one_div, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_diagX_le q p) (norm_nonneg _)
  have hYS : ∀ p : Nat.Primes, Summable fun q : XiZeroCopy =>
      diagY q p / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := fun p => by
    refine Summable.of_norm_bounded (hw.norm.mul_left (Real.exp (1 / 2 * Real.log p))) fun q => ?_
    rw [div_eq_mul_one_div, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_diagY_le q p) (norm_nonneg _)
  -- the linear parts are the lag function at the primes
  have hlin : ∀ (D : XiZeroCopy → Nat.Primes → ℂ), (∀ p, Summable fun q =>
      D q p / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) →
      ∑' q : XiZeroCopy, (∑ p ∈ P, (diagA σ r p : ℂ) * D q p) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
        ∑ p ∈ P, (diagA σ r p : ℂ) * ∑' q : XiZeroCopy, D q p / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
    intro D hD
    simp_rw [Finset.sum_div, mul_div_assoc]
    rw [Summable.tsum_finsetSum fun p _ => (hD p).mul_left _]
    exact Finset.sum_congr rfl fun p _ => tsum_mul_left
  have hΦX : ∀ p : Nat.Primes, ∑' q : XiZeroCopy, diagX q p / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
      (weilLagFunctionReal (Real.log p) : ℂ) := fun p => by
    rw [← weilLagFunction_eq_ofReal]; rfl
  have hΦY : ∀ p : Nat.Primes, ∑' q : XiZeroCopy, diagY q p / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
      (weilLagFunctionReal (Real.log p) : ℂ) := fun p => by
    rw [← weilLagFunction_eq_ofReal, ← weilLagFunction_neg]
    unfold weilLagFunction diagY
    refine tsum_congr fun q => ?_
    congr 2
    push_cast
    ring
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ p ∈ P, diagA σ r p * weilLagFunctionReal (Real.log p) :=
    ⟨_, rfl⟩
  have hAc : ∑ p ∈ P, (diagA σ r p : ℂ) * (weilLagFunctionReal (Real.log p) : ℂ) = (A : ℂ) := by
    rw [hAdef]; push_cast; rfl
  have hX1 := hlin diagX hXS
  have hY1 := hlin diagY hYS
  simp only [hΦX, hΦY, hAc] at hX1 hY1
  have h1 : (∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) = (poleSharpConstant : ℂ) :=
    tsum_inv_zero_mul_one_sub_zero
  obtain ⟨Z0, hZ0⟩ : ∃ Z, Z = ∑' q : XiZeroCopy,
      laurentRem (diagA σ r) (diagX q) (diagY q) P.toList 0 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) :=
    ⟨_, rfl⟩
  obtain ⟨Z1, hZ1⟩ : ∃ Z, Z = ∑' q : XiZeroCopy,
      laurentRem (diagA σ r) (diagX q) (diagY q) P.toList 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) :=
    ⟨_, rfl⟩
  obtain ⟨Zm, hZm⟩ : ∃ Z, Z = ∑' q : XiZeroCopy,
      laurentRem (diagA σ r) (diagX q) (diagY q) P.toList (-1) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) :=
    ⟨_, rfl⟩
  have hXsum : Summable fun q : XiZeroCopy =>
      (∑ p ∈ P, (diagA σ r p : ℂ) * diagX q p) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
    simp_rw [Finset.sum_div, mul_div_assoc]
    exact summable_sum fun p _ => (hXS p).mul_left _
  have hYsum : Summable fun q : XiZeroCopy =>
      (∑ p ∈ P, (diagA σ r p : ℂ) * diagY q p) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
    simp_rw [Finset.sum_div, mul_div_assoc]
    exact summable_sum fun p _ => (hYS p).mul_left _
  rw [hw.tsum_add (hremS 0 (by norm_num)), hXsum.tsum_add (hremS 1 (by norm_num)),
    hYsum.tsum_add (hremS (-1) (by norm_num)), h1, hX1, hY1, ← hZ0, ← hZ1, ← hZm] at hBoch
  -- bounds on the remainders
  have hZb : ∀ m : ℤ, |m| ≤ 1 → ‖∑' q : XiZeroCopy,
      laurentRem (diagA σ r) (diagX q) (diagY q) P.toList m / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
        Real.exp (α * u) * R * lagWeightTotal := by
    intro m hm
    refine (norm_tsum_le_tsum_norm (hremS m hm).norm).trans ?_
    rw [lagWeightTotal, ← tsum_mul_left]
    refine (hremS m hm).norm.tsum_le_tsum (fun q => ?_) (summable_norm_lagWeight.mul_left _)
    rw [div_eq_mul_one_div, norm_mul]
    exact mul_le_mul_of_nonneg_right (hremB q m hm) (norm_nonneg _)
  have hZ0b : ‖Z0‖ ≤ R * lagWeightTotal := by
    rw [hZ0]
    refine (norm_tsum_le_tsum_norm (hremS 0 (by norm_num)).norm).trans ?_
    rw [lagWeightTotal, ← tsum_mul_left]
    refine (hremS 0 (by norm_num)).norm.tsum_le_tsum (fun q => ?_)
      (summable_norm_lagWeight.mul_left _)
    rw [div_eq_mul_one_div, norm_mul]
    have := hrem q 0
    rw [zpow_zero, one_mul] at this
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hZ1b := hZb 1 (by norm_num)
  have hZmb := hZb (-1) (by norm_num)
  rw [← hZ1] at hZ1b
  rw [← hZm] at hZmb
  -- assemble
  have hW := lagWeightTotal_nonneg
  have hre0 : ((poleSharpConstant : ℂ) + Z0).re ≤ poleSharpConstant + R * lagWeightTotal := by
    rw [Complex.add_re, Complex.ofReal_re]
    linarith [Complex.re_le_norm Z0]
  have hconjA : (starRingEnd ℂ) ((A : ℂ) + Zm) = (A : ℂ) + (starRingEnd ℂ) Zm := by
    rw [map_add, Complex.conj_ofReal]
  rw [hconjA] at hBoch
  have h2A : ‖(2 * A : ℝ)‖ ≤ ‖(A : ℂ) + Z1 + ((A : ℂ) + (starRingEnd ℂ) Zm)‖ + ‖Z1‖ + ‖Zm‖ := by
    have e : ((2 * A : ℝ) : ℂ) = ((A : ℂ) + Z1 + ((A : ℂ) + (starRingEnd ℂ) Zm)) - Z1 -
        (starRingEnd ℂ) Zm := by push_cast; ring
    rw [← Complex.norm_real, e]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_conj]
    linarith [norm_sub_le ((A : ℂ) + Z1 + ((A : ℂ) + (starRingEnd ℂ) Zm)) Z1]
  rw [Real.norm_eq_abs, abs_mul, abs_two] at h2A
  rw [← hAdef]
  nlinarith [hBoch, hre0, hZ1b, hZmb, h2A]

theorem abs_sum_weilLagFunctionReal_le_of_jasProductPositiveAbove {X : ℕ} {σ : ℝ}
    (hpos : JasProductPositiveAbove X σ) {α u h r : ℝ}
    (hα : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α) (hu : 0 ≤ u) (hr : 0 ≤ r)
    (P : Finset Nat.Primes) (hP : ∀ p ∈ P, X < (p : ℕ))
    (hwin : ∀ p ∈ P, u ≤ Real.log p ∧ Real.log p ≤ u + h) :
    |∑ p ∈ P, diagA σ r p * weilLagFunctionReal (Real.log p)| ≤
      poleSharpConstant + lagWeightTotal *
        ((∏ p ∈ P, (1 + 2 * (diagA σ r p * Real.exp (h / 2)))) - 1 -
          2 * ∑ p ∈ P, diagA σ r p * Real.exp (h / 2)) * (1 + Real.exp (α * u)) :=
  abs_sum_weilLagFunctionReal_le_of_constPositive hα hu hr P (hpos.constOn hP) hwin

end

end RHTower
