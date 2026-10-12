import GaloisForLFunctions.RHTower.JointAncestryWeightedLagGrowth

/-!
# The diagonal Bochner bound for dressed JAS product tests

The dressed JAS aggregate of a finite prime set `P` at level `σ` and vector `z` is

`Σ_ρ g(ρ)/(ρ(1−ρ)) · ∏_{p ∈ P} (1 + z_p p^{−(ρ+σ−½)} + z̄_p p^{−(½−ρ+σ)} + |z_p|²)`.

On the critical line `g` is real (from `g(s̄) = conj g(s)` and `g(1 − s) = g(s)`), so on RH the
aggregate is nonnegative whenever `g > 0` at the zeros.

**Theorem** (`abs_sum_dLagReal_le_of_weightedConstPositive`).  If the dressed tests with a constant
vector are positive on a set `P` of primes with `log p ∈ [u, u + h]`, and `|Re ρ − ½| ≤ α`, then
`|Σ_P a_p Φ_g(log p)| ≤ Φ_g(0) + V·R·(1 + e^{αu})`, where `V = Σ_ρ |g(ρ)|/|ρ(1−ρ)|` and
`R = ∏(1 + 2a_p e^{h/2}) − 1 − 2Σa_p e^{h/2}`.  The proof is the undressed one with the dressed
weights: Bochner's inequality on the circle for the uniform vectors `r e^{−iθ}`, and the weighted
Laurent remainder bound zero by zero.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

variable (D : LagDressing)

/-- The dressed aggregate of the uniform test at the `j`-th root of unity, normalized by
`(1+r²)^{|P|}`. -/
def dDiagAggregate (σ r : ℝ) (P : Finset Nat.Primes) (N j : ℕ) : ℂ :=
  ∑' q : XiZeroCopy, diagProd (diagA σ r) (diagX q) (diagY q) P.toList N j * D.weight q

theorem summable_diagProd_mul_weight {σ r : ℝ} (hr : 0 ≤ r) (P : Finset Nat.Primes) (N j : ℕ) :
    Summable fun q : XiZeroCopy =>
      diagProd (diagA σ r) (diagX q) (diagY q) P.toList N j * D.weight q := by
  refine Summable.of_norm_bounded
    (D.summable_norm_weight.mul_left (∏ p ∈ P, (1 + 2 * diagA σ r p *
      Real.exp (1 / 2 * Real.log p)))) fun q => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_diagProd_le q hr P N j) (norm_nonneg _)

/-- Dressed product positivity on one prime set `P` with a constant test vector. -/
def JasWeightedConstPositiveOn (P : Finset Nat.Primes) (σ : ℝ) : Prop :=
  ∀ z : ℂ, 0 ≤ (∑' q : XiZeroCopy,
    (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) z) * D.weight q).re

/-- Dressed product positivity on every finite set of primes above `X`. -/
def JasWeightedProductPositiveAbove (X : ℕ) (σ : ℝ) : Prop :=
  ∀ (P : Finset Nat.Primes), (∀ p ∈ P, X < (p : ℕ)) → ∀ z : Nat.Primes → ℂ, 0 ≤ (∑' q : XiZeroCopy,
    (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) * D.weight q).re

theorem JasWeightedProductPositiveAbove.constOn {D : LagDressing} {X : ℕ} {σ : ℝ}
    (h : JasWeightedProductPositiveAbove D X σ) {P : Finset Nat.Primes}
    (hP : ∀ p ∈ P, X < (p : ℕ)) : JasWeightedConstPositiveOn D P σ :=
  fun z => h P hP fun _ => z

theorem re_dDiagAggregate_nonneg {σ : ℝ} {P : Finset Nat.Primes}
    (h : JasWeightedConstPositiveOn D P σ) (r : ℝ) (N j : ℕ) :
    0 ≤ (dDiagAggregate D σ r P N j).re := by
  have h0 := h ((r : ℂ) * unitRoot N ^ (-(j : ℤ)))
  have e : ∀ q : XiZeroCopy, (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) ((r : ℂ) * unitRoot N ^ (-(j : ℤ)))) * D.weight q =
      (((1 + r ^ 2) ^ P.card : ℝ) : ℂ) *
        (diagProd (diagA σ r) (diagX q) (diagY q) P.toList N j * D.weight q) := by
    intro q
    rw [prod_jasBernoulliFactor_diag]
    push_cast
    ring
  simp only [e] at h0
  rw [tsum_mul_left, Complex.re_ofReal_mul] at h0
  have hc : 0 < ((1 + r ^ 2) ^ P.card : ℝ) := by positivity
  unfold dDiagAggregate
  exact nonneg_of_mul_nonneg_right h0 hc

theorem diagFourier_mul_const (F : ℕ → ℂ) (c : ℂ) (N : ℕ) (m : ℤ) :
    diagFourier (fun j => F j * c) N m = diagFourier F N m * c := by
  unfold diagFourier
  beta_reduce
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem diagFourier_dDiagAggregate {σ r : ℝ} (hr : 0 ≤ r) (P : Finset Nat.Primes) {m : ℤ}
    (hm : |m| ≤ 1) :
    diagFourier (dDiagAggregate D σ r P (P.card + 2)) (P.card + 2) m =
      ∑' q : XiZeroCopy, laurentCoef (diagA σ r) (diagX q) (diagY q) P.toList m * D.weight q := by
  have h1 := diagFourier_tsum (F := fun q j =>
    diagProd (diagA σ r) (diagX q) (diagY q) P.toList (P.card + 2) j * D.weight q)
    (fun j => summable_diagProd_mul_weight D hr P _ j) (P.card + 2) m
  unfold dDiagAggregate
  rw [h1]
  refine tsum_congr fun q => ?_
  rw [diagFourier_mul_const, diagFourier_diagProd_eq _ _ _ (by omega)]
  rw [Finset.length_toList]
  push_cast
  linarith

theorem abs_sum_dLagReal_le_of_weightedConstPositive {σ : ℝ} {α u h r : ℝ}
    (hα : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α) (hu : 0 ≤ u) (hr : 0 ≤ r)
    (P : Finset Nat.Primes) (hpos : JasWeightedConstPositiveOn D P σ)
    (hwin : ∀ p ∈ P, u ≤ Real.log p ∧ Real.log p ≤ u + h) :
    |∑ p ∈ P, diagA σ r p * dLagReal D (Real.log p)| ≤
      dLagReal D 0 + D.total *
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
  have hT : ∀ j < N, 0 ≤ (dDiagAggregate D σ r P N j).re :=
    fun j _ => re_dDiagAggregate_nonneg D hpos r N j
  have hBoch := norm_diagFourier_one_add_conj_le hN hT
  have hc : ∀ m : ℤ, |m| ≤ 1 → diagFourier (dDiagAggregate D σ r P N) N m =
      ∑' q : XiZeroCopy, laurentCoef (diagA σ r) (diagX q) (diagY q) P.toList m * D.weight q := by
    intro m hm; rw [hNdef]; exact diagFourier_dDiagAggregate D hr P hm
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
  simp only [hsplit, hm0, hm1, hmm1, add_mul] at hBoch
  -- summability
  have hw : Summable fun q : XiZeroCopy => 1 * D.weight q := by
    simpa using D.summable_norm_weight.of_norm
  have hremS : ∀ m : ℤ, |m| ≤ 1 → Summable fun q : XiZeroCopy =>
      laurentRem (diagA σ r) (diagX q) (diagY q) P.toList m * D.weight q := by
    intro m hm
    refine Summable.of_norm_bounded (D.summable_norm_weight.mul_left (Real.exp (α * u) * R)) fun q => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hremB q m hm) (norm_nonneg _)
  have hXS : ∀ p : Nat.Primes, Summable fun q : XiZeroCopy =>
      diagX q p * D.weight q := fun p => by
    refine Summable.of_norm_bounded (D.summable_norm_weight.mul_left (Real.exp (1 / 2 * Real.log p))) fun q => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_diagX_le q p) (norm_nonneg _)
  have hYS : ∀ p : Nat.Primes, Summable fun q : XiZeroCopy =>
      diagY q p * D.weight q := fun p => by
    refine Summable.of_norm_bounded (D.summable_norm_weight.mul_left (Real.exp (1 / 2 * Real.log p))) fun q => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_diagY_le q p) (norm_nonneg _)
  -- the linear parts are the lag function at the primes
  have hlin : ∀ (Fq : XiZeroCopy → Nat.Primes → ℂ), (∀ p, Summable fun q =>
      Fq q p * D.weight q) →
      ∑' q : XiZeroCopy, (∑ p ∈ P, (diagA σ r p : ℂ) * Fq q p) * D.weight q =
        ∑ p ∈ P, (diagA σ r p : ℂ) * ∑' q : XiZeroCopy, Fq q p * D.weight q := by
    intro Fq hD
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Summable.tsum_finsetSum fun p _ => (hD p).mul_left _]
    exact Finset.sum_congr rfl fun p _ => tsum_mul_left
  have hΦX : ∀ p : Nat.Primes, ∑' q : XiZeroCopy, diagX q p * D.weight q =
      (dLagReal D (Real.log p) : ℂ) := fun p => by
    rw [← dLag_eq_ofReal]; rfl
  have hΦY : ∀ p : Nat.Primes, ∑' q : XiZeroCopy, diagY q p * D.weight q =
      (dLagReal D (Real.log p) : ℂ) := fun p => by
    rw [← dLag_eq_ofReal, ← dLag_neg]
    unfold dLag diagY
    refine tsum_congr fun q => ?_
    congr 2
    push_cast
    ring
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ p ∈ P, diagA σ r p * dLagReal D (Real.log p) :=
    ⟨_, rfl⟩
  have hAc : ∑ p ∈ P, (diagA σ r p : ℂ) * (dLagReal D (Real.log p) : ℂ) = (A : ℂ) := by
    rw [hAdef]; push_cast; rfl
  have hX1 := hlin diagX hXS
  have hY1 := hlin diagY hYS
  simp only [hΦX, hΦY, hAc] at hX1 hY1
  have h1 : (∑' q : XiZeroCopy, 1 * D.weight q) = (dLagReal D 0 : ℂ) := by
    rw [← dLag_eq_ofReal, dLag_zero]; simp
  obtain ⟨Z0, hZ0⟩ : ∃ Z, Z = ∑' q : XiZeroCopy,
      laurentRem (diagA σ r) (diagX q) (diagY q) P.toList 0 * D.weight q :=
    ⟨_, rfl⟩
  obtain ⟨Z1, hZ1⟩ : ∃ Z, Z = ∑' q : XiZeroCopy,
      laurentRem (diagA σ r) (diagX q) (diagY q) P.toList 1 * D.weight q :=
    ⟨_, rfl⟩
  obtain ⟨Zm, hZm⟩ : ∃ Z, Z = ∑' q : XiZeroCopy,
      laurentRem (diagA σ r) (diagX q) (diagY q) P.toList (-1) * D.weight q :=
    ⟨_, rfl⟩
  have hXsum : Summable fun q : XiZeroCopy =>
      (∑ p ∈ P, (diagA σ r p : ℂ) * diagX q p) * D.weight q := by
    simp_rw [Finset.sum_mul, mul_assoc]
    exact summable_sum fun p _ => (hXS p).mul_left _
  have hYsum : Summable fun q : XiZeroCopy =>
      (∑ p ∈ P, (diagA σ r p : ℂ) * diagY q p) * D.weight q := by
    simp_rw [Finset.sum_mul, mul_assoc]
    exact summable_sum fun p _ => (hYS p).mul_left _
  rw [hw.tsum_add (hremS 0 (by norm_num)), hXsum.tsum_add (hremS 1 (by norm_num)),
    hYsum.tsum_add (hremS (-1) (by norm_num)), h1, hX1, hY1, ← hZ0, ← hZ1, ← hZm] at hBoch
  -- bounds on the remainders
  have hZb : ∀ m : ℤ, |m| ≤ 1 → ‖∑' q : XiZeroCopy,
      laurentRem (diagA σ r) (diagX q) (diagY q) P.toList m * D.weight q‖ ≤
        Real.exp (α * u) * R * D.total := by
    intro m hm
    refine (norm_tsum_le_tsum_norm (hremS m hm).norm).trans ?_
    rw [LagDressing.total, ← tsum_mul_left]
    refine (hremS m hm).norm.tsum_le_tsum (fun q => ?_) (D.summable_norm_weight.mul_left _)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hremB q m hm) (norm_nonneg _)
  have hZ0b : ‖Z0‖ ≤ R * D.total := by
    rw [hZ0]
    refine (norm_tsum_le_tsum_norm (hremS 0 (by norm_num)).norm).trans ?_
    rw [LagDressing.total, ← tsum_mul_left]
    refine (hremS 0 (by norm_num)).norm.tsum_le_tsum (fun q => ?_)
      (D.summable_norm_weight.mul_left _)
    rw [norm_mul]
    have := hrem q 0
    rw [zpow_zero, one_mul] at this
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hZ1b := hZb 1 (by norm_num)
  have hZmb := hZb (-1) (by norm_num)
  rw [← hZ1] at hZ1b
  rw [← hZm] at hZmb
  -- assemble
  have hW := D.total_nonneg
  have hre0 : ((dLagReal D 0 : ℂ) + Z0).re ≤ dLagReal D 0 + R * D.total := by
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


end

end RHTower
