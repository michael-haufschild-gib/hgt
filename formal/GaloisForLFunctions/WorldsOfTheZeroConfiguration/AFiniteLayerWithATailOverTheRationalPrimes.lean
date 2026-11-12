import GaloisForLFunctions.WorldsOfTheZeroConfiguration.EveryFiniteLayerIsRealizedByATwoSidedEdit
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheSquareTargetOfAHalfScaleCopy
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite

/-!
# A finite layer with a tail over the rational primes

Does a finite top layer force the other zeros to the line?  Not for an Euler product over the
rational primes with multiplicities `0, 1, 2`, integer norms and a count rate.

Let `1/4 < a ≤ 3/10` and `a + 1/2 < Re ρ ≤ 9/10`.  The target

`m(k) = −2 Re k^{ρ−1} + [k = j²] 2 Λ(j) j^{2a} − k^{a−1/2}`

(`tailTarget`) has Dirichlet series `−ζ(s+1−ρ) − ζ(s+1−ρ̄) − 2ζ′/ζ(2s−2a) − ζ(s+1/2−a)`, so the
prescribed factor is `L(s) = (s − ρ)(s − ρ̄) · u(2s − 2a)`, `u(w) = (w − 1)ζ(w)` (`tailFactor`):
the pole of `ζ(2s − 2a)` at `a + 1/2` is paid by the smooth deletion `k^{a−1/2}`.

**Theorem** (`exists_isEdit_finite_layer_with_tail`).  The greedy edit of `tailTarget ρ a` has

`(s − 1) ζ_B(s) = (s − 1) ζ(s) · C (s − ρ)(s − ρ̄) u(2s − 2a) e^{H(s)}`

with `H` holomorphic on `Re s > 1/2` (`IsTailTwin`) and count `A x + O(x^β)` for every
`β > Re ρ`.  Its fake zeros right of the line are `ρ`, `ρ̄` and the points `a + z/2`, `z` a zero of
`ζ` (`IsTailTwin.hasFakeZeroSet`).  The tail `{a + z/2}` has infinitely many points right of the
line (`tailSet_infinite`), all with `Re s < a + 1/2 < Re ρ` (`tailSet_re_lt`): an isolated pair
on top and infinitely many zeros below it that do not approach the line.

The spikes of the target at the squares have size `O(k^{2/5})` and there are at most
`(n − b)/√n + 1` of them in `(b, n]`, so they stay inside the discrepancy `O(√n)`.
-/

open Complex Filter Topology Finset
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open ArithmeticFunction (vonMangoldt)

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration

open PrimeEdits TwoSidedEdits SquareTarget

/-- The target of a pair with a half-scale tail. -/
def tailTarget (ρ : ℂ) (a : ℝ) (k : ℕ) : ℝ := target ρ k + sqTarget a k - (k : ℝ) ^ (a - 1 / 2)

/-- The factor of a pair with a half-scale tail: `(s − ρ)(s − ρ̄) · u(2s − 2a)`. -/
def tailFactor (ρ : ℂ) (a : ℝ) (s : ℂ) : ℂ :=
  (s - ρ) * (s - (starRingEnd ℂ) ρ) * zetaResidueUnit (2 * s - 2 * (a : ℂ))

/-- `B` is a **twin of `ζ` with the pair `ρ, ρ̄` and the half-scale tail at `a`**. -/
def IsTailTwin (B : BeurlingSystem) (ρ : ℂ) (a : ℝ) : Prop :=
  ∃ (C : ℂ) (H : ℂ → ℂ), C ≠ 0 ∧ DifferentiableOn ℂ H {s : ℂ | 1 / 2 < s.re} ∧
    ∀ s : ℂ, 1 < s.re → (s - 1) * B.zetaSeriesC s =
      zetaResidueUnit s * (C * tailFactor ρ a s * Complex.exp (H s))

/-- The tail: the zeros of `u(2s − 2a)` right of the line, the points `a + z/2`. -/
def tailSet (a : ℝ) : Set ℂ :=
  {z : ℂ | 1 / 2 < z.re ∧ zetaResidueUnit (2 * z - 2 * (a : ℂ)) = 0}

/-! ## The target -/

theorem tailTarget_zero {ρ : ℂ} {a : ℝ} (hρ1 : ρ.re < 1) (ha : a < 1 / 2) :
    tailTarget ρ a 0 = 0 := by
  rw [tailTarget, target_zero hρ1, sqTarget_zero, Nat.cast_zero,
    Real.zero_rpow (sub_ne_zero.mpr (ne_of_lt ha))]
  ring

theorem abs_tailTarget_le {ρ : ℂ} {a η : ℝ} (hη1 : η ≤ 1 - ρ.re) (hη2 : η ≤ 1 / 2 - a) {k : ℕ}
    (hk : 1 ≤ k) : |tailTarget ρ a k| ≤ 3 * (k : ℝ) ^ (-η) + sqTarget a k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : |target ρ k| ≤ 2 * (k : ℝ) ^ (-η) := by
    have h := Real.rpow_le_rpow_of_exponent_le hk1 (show ρ.re - 1 ≤ -η by linarith)
    linarith [abs_target_le ρ hk]
  have h2 : (k : ℝ) ^ (a - 1 / 2) ≤ (k : ℝ) ^ (-η) :=
    Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
  have h3 : 0 ≤ (k : ℝ) ^ (a - 1 / 2) := Real.rpow_nonneg (by linarith) _
  have h4 := sqTarget_nonneg a k
  unfold tailTarget
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (target ρ k)]
  · linarith [le_abs_self (target ρ k)]

/-- The spikes of an interval beyond the threshold `n^{1/10} ≥ 80`. -/
theorem sum_Ioc_sqTarget_le' {a : ℝ} (ha : 1 / 4 < a) (ha2 : a ≤ 3 / 10) {b n : ℕ} (hbn : b ≤ n)
    (hn : 1 ≤ n) :
    ∑ k ∈ Ioc b n, sqTarget a k ≤
      ((n : ℝ) - b) * (10 * (n : ℝ) ^ (-(1 / 10 : ℝ))) + 10 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set ε : ℝ := (1 - 2 * a) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε5 : 1 / 5 ≤ ε := by rw [hε]; linarith
  have hsq := sum_Ioc_sqTarget_le a hε0 (by rw [hε]; linarith) hbn (by omega : 0 < n)
  set S : ℝ := Real.sqrt n with hS
  set P : ℝ := (n : ℝ) ^ ((2 * a + ε) / 2) with hP
  have hS0 : 0 < S := Real.sqrt_pos.mpr hn0
  have hP0 : 0 ≤ P := Real.rpow_nonneg hn0.le _
  have hSpow : S = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow n
  -- `P ≤ √n · n^{−1/10}` and `P ≤ √n`
  have hP1 : P ≤ S * (n : ℝ) ^ (-(1 / 10 : ℝ)) := by
    rw [hSpow, ← Real.rpow_add hn0]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by rw [hε]; linarith)
  have hP2 : P ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by rw [hε]; linarith)
  have hc : 2 / ε ≤ 10 := by
    rw [div_le_iff₀ hε0]; linarith
  have hc0 : 0 ≤ 2 / ε := by positivity
  have hPS : P / S ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) := by
    rw [div_le_iff₀ hS0]; linarith
  have hsplit : (((n : ℝ) - b) / S + 1) * (2 / ε * P) =
      ((n : ℝ) - b) * (2 / ε * (P / S)) + 2 / ε * P := by
    field_simp
  have hℓ : 0 ≤ (n : ℝ) - b := sub_nonneg.mpr (by exact_mod_cast hbn)
  have hn10 : 0 ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hn0.le _
  have hPS0 : 0 ≤ P / S := div_nonneg hP0 hS0.le
  have h1 : 2 / ε * (P / S) ≤ 10 * (n : ℝ) ^ (-(1 / 10 : ℝ)) :=
    mul_le_mul hc hPS hPS0 (by norm_num)
  have h2 : 2 / ε * P ≤ 10 * (n : ℝ) ^ (1 / 2 : ℝ) := mul_le_mul hc hP2 hP0 (by norm_num)
  calc ∑ k ∈ Ioc b n, sqTarget a k ≤ (((n : ℝ) - b) / S + 1) * (2 / ε * P) := hsq
    _ = ((n : ℝ) - b) * (2 / ε * (P / S)) + 2 / ε * P := hsplit
    _ ≤ ((n : ℝ) - b) * (10 * (n : ℝ) ^ (-(1 / 10 : ℝ))) + 10 * (n : ℝ) ^ (1 / 2 : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hℓ) h2

/-- **The discrepancy of the edit of a pair with a tail is `O(√n)`.** -/
theorem exists_abs_gdisc_tailTarget_le {ρ : ℂ} {a : ℝ} (ha : 1 / 4 < a) (ha2 : a ≤ 3 / 10)
    (hρ : ρ.re ≤ 9 / 10) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → |gdisc (tailTarget ρ a) n| ≤ K * (n : ℝ) ^ (1 / 2 : ℝ) := by
  obtain ⟨X, -, hwin⟩ := RHTower.exists_theta_window_lower_seventeenThirtieths
    (α := 3 / 5) (by norm_num) (by norm_num)
  obtain ⟨n₁, hX, hn₁1, hF1, hF2⟩ := exists_nat_forall_le_rpow (X := X) (A₁ := 80) (A₂ := 4)
    (e₁ := 1 / 10) (e₂ := 1 - 3 / 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hn₁ : 1 ≤ n₁ := by exact_mod_cast hn₁1
  -- every term is at most `3 k^{−1/10}` plus its spike
  have hterm : ∀ k : ℕ, 1 ≤ k →
      |tailTarget ρ a k| ≤ 3 * (k : ℝ) ^ (-(1 / 10 : ℝ)) + sqTarget a k := fun k hk =>
    abs_tailTarget_le (by linarith) (by linarith) hk
  have hsum : ∀ b n : ℕ, n₁ ≤ b → b ≤ n → ∀ δ : ℝ,
      (∀ k ∈ Ioc b n, 3 * (k : ℝ) ^ (-(1 / 10 : ℝ)) ≤ δ) →
      ∑ k ∈ Ioc b n, |tailTarget ρ a k| ≤ ((n : ℝ) - b) * δ +
        (((n : ℝ) - b) * (10 * (n : ℝ) ^ (-(1 / 10 : ℝ))) + 10 * (n : ℝ) ^ (1 / 2 : ℝ)) := by
    intro b n hb hbn δ hδ
    calc ∑ k ∈ Ioc b n, |tailTarget ρ a k|
        ≤ ∑ k ∈ Ioc b n, (3 * (k : ℝ) ^ (-(1 / 10 : ℝ)) + sqTarget a k) :=
          Finset.sum_le_sum fun k hk => hterm k (by have := (Finset.mem_Ioc.mp hk).1; omega)
      _ = ∑ k ∈ Ioc b n, 3 * (k : ℝ) ^ (-(1 / 10 : ℝ)) + ∑ k ∈ Ioc b n, sqTarget a k :=
          Finset.sum_add_distrib
      _ ≤ _ := add_le_add (sum_Ioc_le_of_le hbn hδ)
          (sum_Ioc_sqTarget_le' ha ha2 hbn (hn₁.trans (hb.trans hbn)))
  -- beyond `n₁`: `n^{−1/10} ≤ 1/80`
  have hsmall : ∀ x : ℝ, (n₁ : ℝ) ≤ x → x ^ (-(1 / 10 : ℝ)) ≤ 1 / 80 := by
    intro x hx
    have hx0 : 0 < x := by linarith
    rw [Real.rpow_neg hx0.le, show (1 / 80 : ℝ) = 80⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) (hF1 x hx)
  refine exists_abs_gdisc_le_rpow (c := 1 / 2) (by norm_num) hwin hX (K₁ := 42) (by norm_num)
    (fun b n hb hbn => ?_) (fun b n hb hbn hshort => ?_)
  · -- long intervals
    have hn₁n : (n₁ : ℝ) ≤ n := by exact_mod_cast hb.trans hbn
    have hℓ : 0 ≤ (n : ℝ) - b := sub_nonneg.mpr (by exact_mod_cast hbn)
    have h := hsum b n hb hbn (1 / 8) (fun k hk => by
      have hkr : (n₁ : ℝ) ≤ k := by exact_mod_cast hb.trans (Finset.mem_Ioc.mp hk).1.le
      linarith [hsmall k hkr])
    have h2 := mul_le_mul_of_nonneg_left (hsmall n hn₁n) hℓ
    have h3 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    linarith
  · -- short intervals
    have hn : 0 < n := by omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn₁n : (n₁ : ℝ) ≤ n := by exact_mod_cast hb.trans hbn
    have hn10 : 0 ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hn0.le _
    have h := hsum b n hb hbn (6 * (n : ℝ) ^ (-(1 / 10 : ℝ))) (fun k hk => by
      have h2 := rpow_neg_le_of_short (α := 3 / 5) (η := 1 / 10) (by norm_num) (by norm_num) hn
        (hF2 n hn₁n) hshort (Finset.mem_Ioc.mp hk).1
      linarith)
    have hnn : (n : ℝ) ^ (3 / 5 : ℝ) * (n : ℝ) ^ (-(1 / 10 : ℝ)) = (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hn0]; norm_num
    have hprod := mul_le_mul_of_nonneg_right hshort hn10
    nlinarith

/-- The mass of the target is `O(n^{Re ρ})`. -/
theorem sum_abs_tailTarget_le {ρ : ℂ} {a : ℝ} (ha0 : 0 < a) (hκ : a + 1 / 2 < ρ.re)
    (hρ1 : ρ.re < 1) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Ioc 0 n, |tailTarget ρ a k| ≤
      (2 / ρ.re + 4 / (2 * (ρ.re - (a + 1 / 2))) + 1 / (a + 1 / 2)) * (n : ℝ) ^ ρ.re := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set ε : ℝ := 2 * (ρ.re - (a + 1 / 2)) with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hterm : ∀ k ∈ Ioc 0 n,
      |tailTarget ρ a k| ≤ |target ρ k| + sqTarget a k + (k : ℝ) ^ (a - 1 / 2) := by
    intro k _
    have h3 : 0 ≤ (k : ℝ) ^ (a - 1 / 2) := Real.rpow_nonneg (Nat.cast_nonneg k) _
    have h4 := sqTarget_nonneg a k
    unfold tailTarget
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (target ρ k)]
    · linarith [le_abs_self (target ρ k)]
  have h1 := sum_abs_target_le (ρ := ρ) (by linarith) hρ1 n
  -- the spikes
  have h2 : ∑ k ∈ Ioc 0 n, sqTarget a k ≤ 4 / ε * (n : ℝ) ^ ρ.re := by
    have hsq := sum_Ioc_sqTarget_le a hε0 (by rw [hε]; linarith) (Nat.zero_le n)
      (by omega : 0 < n)
    have hS0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hS1 : 1 ≤ Real.sqrt n := by
      rw [Real.sqrt_eq_rpow]; exact Real.one_le_rpow hn1 (by norm_num)
    have hdiv : ((n : ℝ) - ((0 : ℕ) : ℝ)) / Real.sqrt n = Real.sqrt n := by
      rw [Nat.cast_zero, sub_zero, Real.div_sqrt]
    have hW : Real.sqrt n * (n : ℝ) ^ ((2 * a + ε) / 2) = (n : ℝ) ^ ρ.re := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
      congr 1
      rw [hε]; ring
    have hW0 : 0 ≤ 2 / ε * (n : ℝ) ^ ((2 * a + ε) / 2) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg hn0.le _)
    rw [hdiv] at hsq
    calc ∑ k ∈ Ioc 0 n, sqTarget a k
        ≤ (Real.sqrt n + 1) * (2 / ε * (n : ℝ) ^ ((2 * a + ε) / 2)) := hsq
      _ ≤ (2 * Real.sqrt n) * (2 / ε * (n : ℝ) ^ ((2 * a + ε) / 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) hW0
      _ = 4 / ε * (Real.sqrt n * (n : ℝ) ^ ((2 * a + ε) / 2)) := by ring
      _ = 4 / ε * (n : ℝ) ^ ρ.re := by rw [hW]
  -- the smooth deletion
  have h3 : ∑ k ∈ Ioc 0 n, (k : ℝ) ^ (a - 1 / 2) ≤ 1 / (a + 1 / 2) * (n : ℝ) ^ ρ.re := by
    have hI : Ioc 0 n = Icc 1 n := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    have h := RHTower.BeurlingDeletion.DeletionData.sum_rpow_le (α := a + 1 / 2) (by linarith)
      (by linarith) n
    rw [show a + 1 / 2 - 1 = a - 1 / 2 by ring] at h
    rw [hI]
    have hpow : (n : ℝ) ^ (a + 1 / 2) ≤ (n : ℝ) ^ ρ.re :=
      Real.rpow_le_rpow_of_exponent_le hn1 hκ.le
    calc ∑ k ∈ Icc 1 n, (k : ℝ) ^ (a - 1 / 2) ≤ (n : ℝ) ^ (a + 1 / 2) / (a + 1 / 2) := h
      _ = 1 / (a + 1 / 2) * (n : ℝ) ^ (a + 1 / 2) := by ring
      _ ≤ 1 / (a + 1 / 2) * (n : ℝ) ^ ρ.re :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  calc ∑ k ∈ Ioc 0 n, |tailTarget ρ a k|
      ≤ ∑ k ∈ Ioc 0 n, (|target ρ k| + sqTarget a k + (k : ℝ) ^ (a - 1 / 2)) :=
        Finset.sum_le_sum hterm
    _ = ∑ k ∈ Ioc 0 n, |target ρ k| + ∑ k ∈ Ioc 0 n, sqTarget a k +
          ∑ k ∈ Ioc 0 n, (k : ℝ) ^ (a - 1 / 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ 2 / ρ.re * (n : ℝ) ^ ρ.re + 4 / ε * (n : ℝ) ^ ρ.re +
          1 / (a + 1 / 2) * (n : ℝ) ^ ρ.re := add_le_add (add_le_add h1 h2) h3
    _ = (2 / ρ.re + 4 / ε + 1 / (a + 1 / 2)) * (n : ℝ) ^ ρ.re := by ring

/-! ## The Dirichlet series and the factor -/

theorem lseriesHasSum_tailTarget {ρ : ℂ} {a : ℝ} (ha : a < 1 / 2) (hρ1 : ρ.re < 1) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesHasSum (fun k : ℕ => (tailTarget ρ a k : ℂ)) s
      (-(riemannZeta (s - (ρ - 1)) + riemannZeta (s - ((starRingEnd ℂ) ρ - 1))) +
        2 * LSeries (fun n : ℕ => (vonMangoldt n : ℂ)) (2 * s - 2 * (a : ℂ)) -
        riemannZeta (s - ((a : ℂ) - 1 / 2))) := by
  have hfun : (fun k : ℕ => (tailTarget ρ a k : ℂ)) =
      (fun k : ℕ => (target ρ k : ℂ)) + (fun k : ℕ => (sqTarget a k : ℂ)) -
        fun k : ℕ => (k : ℂ) ^ ((a : ℂ) - 1 / 2) := by
    funext k
    have hpow : (((k : ℝ) ^ (a - 1 / 2) : ℝ) : ℂ) = (k : ℂ) ^ ((a : ℂ) - 1 / 2) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg k), Complex.ofReal_natCast]
      push_cast
      rfl
    simp only [Pi.add_apply, Pi.sub_apply, tailTarget]
    rw [← hpow]
    push_cast
    rfl
  have hw : 1 < (2 * s - 2 * (a : ℂ)).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_zero]
    linarith
  have h3 : 1 < (s - ((a : ℂ) - 1 / 2)).re := by
    have : ((a : ℂ) - 1 / 2).re = a - 1 / 2 := by simp
    rw [Complex.sub_re, this]
    linarith
  rw [hfun]
  exact ((lseriesHasSum_target (ρ := ρ) (s := s) (by linarith)).add
    (lseriesHasSum_sqTarget hw)).sub (lseriesHasSum_cpow h3)

theorem differentiable_tailFactor (ρ : ℂ) (a : ℝ) : Differentiable ℂ (tailFactor ρ a) := by
  unfold tailFactor
  exact ((differentiable_id.sub_const ρ).mul (differentiable_id.sub_const _)).mul
    (differentiable_zetaResidueUnit.comp ((differentiable_id.const_mul 2).sub_const _))

/-- The logarithmic derivative of the factor against the target. -/
theorem logDeriv_tailFactor_eq {ρ : ℂ} {a : ℝ} (ha : a < 1 / 2) (hρ1 : ρ.re < 1) {s : ℂ}
    (hs : 1 < s.re) :
    tailFactor ρ a s ≠ 0 ∧ DifferentiableAt ℂ (tailFactor ρ a) s ∧
      logDeriv (tailFactor ρ a) s = -LSeries (fun k : ℕ => (tailTarget ρ a k : ℂ)) s -
        (PrimeEdits.zetaRegular (s - (ρ - 1)) +
          PrimeEdits.zetaRegular (s - ((starRingEnd ℂ) ρ - 1)) +
          PrimeEdits.zetaRegular (s - ((a : ℂ) - 1 / 2))) := by
  set w : ℂ := 2 * s - 2 * (a : ℂ) with hw
  have hwre : 1 < w.re := by
    rw [hw]
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_zero]
    linarith
  have hw1 : w ≠ 1 := fun h => by rw [h] at hwre; norm_num at hwre
  have hζw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre.le
  have hu : zetaResidueUnit w ≠ 0 := by
    rw [zetaResidueUnit_of_ne hw1]
    exact mul_ne_zero (sub_ne_zero.mpr hw1) hζw
  obtain ⟨hp0, hpd, hplog⟩ := logDeriv_pair_eq (ρ := ρ) (s := s) hρ1 hs
  -- the half-scale factor
  have hlin : DifferentiableAt ℂ (fun z : ℂ => 2 * z - 2 * (a : ℂ)) s :=
    (differentiableAt_id.const_mul 2).sub_const _
  have hlind : deriv (fun z : ℂ => 2 * z - 2 * (a : ℂ)) s = 2 := by
    have h : HasDerivAt (fun z : ℂ => 2 * z - 2 * (a : ℂ)) (2 * 1) s :=
      ((hasDerivAt_id s).const_mul 2).sub_const _
    rw [h.deriv, mul_one]
  have hgd : DifferentiableAt ℂ (fun z : ℂ => zetaResidueUnit (2 * z - 2 * (a : ℂ))) s :=
    (differentiable_zetaResidueUnit _).comp s hlin
  have hglog : logDeriv (fun z : ℂ => zetaResidueUnit (2 * z - 2 * (a : ℂ))) s =
      logDeriv zetaResidueUnit w * 2 := by
    have h := logDeriv_comp (f := zetaResidueUnit) (g := fun z : ℂ => 2 * z - 2 * (a : ℂ))
      (x := s) (differentiable_zetaResidueUnit _) hlin
    rw [hlind] at h
    exact h
  have e1 : logDeriv (tailFactor ρ a) s =
      logDeriv (fun z : ℂ => (z - ρ) * (z - (starRingEnd ℂ) ρ)) s +
        logDeriv zetaResidueUnit w * 2 := by
    rw [← hglog]
    exact logDeriv_mul s hp0 hu hpd hgd
  have e2 : logDeriv zetaResidueUnit w =
      -LSeries (fun n : ℕ => (vonMangoldt n : ℂ)) w + (w - 1)⁻¹ := by
    have h1 := logDeriv_zeta_eq hw1 hu
    have h2 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hwre
    rw [logDeriv_apply] at h1
    rw [h2]
    linear_combination -h1
  have hT := lseriesHasSum_target (ρ := ρ) (s := s) (by linarith)
  have e4 : LSeries (fun k : ℕ => (tailTarget ρ a k : ℂ)) s =
      LSeries (fun k : ℕ => (target ρ k : ℂ)) s +
        2 * LSeries (fun n : ℕ => (vonMangoldt n : ℂ)) w -
        riemannZeta (s - ((a : ℂ) - 1 / 2)) := by
    rw [(lseriesHasSum_tailTarget ha hρ1 hs).LSeries_eq, hT.LSeries_eq]
  have h3ne : s - ((a : ℂ) - 1 / 2) ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    have hre : ((a : ℂ) - 1 / 2).re = a - 1 / 2 := by simp
    rw [Complex.sub_re, hre, Complex.one_re] at h'
    linarith
  have e5 := riemannZeta_eq_zetaRegular h3ne
  have h3ne' : s - ((a : ℂ) - 1 / 2) - 1 ≠ 0 := sub_ne_zero.mpr h3ne
  have e6 : (w - 1)⁻¹ * 2 = (s - ((a : ℂ) - 1 / 2) - 1)⁻¹ := by
    have hw' : w - 1 = 2 * (s - ((a : ℂ) - 1 / 2) - 1) := by rw [hw]; ring
    rw [hw']
    field_simp
  refine ⟨mul_ne_zero hp0 hu, (differentiable_tailFactor ρ a).differentiableAt, ?_⟩
  rw [e1, e2, hplog, e4, e5]
  linear_combination e6

/-! ## The twin with a tail -/

/-- **The greedy edit of a pair with a half-scale tail is a twin of `ζ` with that pair and
tail.** -/
theorem isTailTwin_editSystem {ρ : ℂ} {a : ℝ} (ha : 1 / 4 < a) (ha2 : a ≤ 3 / 10)
    (hρ : ρ.re ≤ 9 / 10) :
    IsTailTwin (editSystem (gedit (tailTarget ρ a))) ρ a := by
  have ha' : a < 1 / 2 := by linarith
  have hρ1 : ρ.re < 1 := by linarith
  obtain ⟨K₀, hK₀, hdisc⟩ := exists_abs_gdisc_tailTarget_le (ρ := ρ) ha ha2 hρ
  have hΦ₀ : DifferentiableOn ℂ (fun s : ℂ => PrimeEdits.zetaRegular (s - (ρ - 1)) +
      PrimeEdits.zetaRegular (s - ((starRingEnd ℂ) ρ - 1)) +
      PrimeEdits.zetaRegular (s - ((a : ℂ) - 1 / 2))) {s : ℂ | (1 / 2 : ℝ) < s.re} :=
    (((PrimeEdits.differentiable_zetaRegular.comp (differentiable_id.sub_const _)).add
      (PrimeEdits.differentiable_zetaRegular.comp (differentiable_id.sub_const _))).add
      (PrimeEdits.differentiable_zetaRegular.comp
        (differentiable_id.sub_const _))).differentiableOn
  obtain ⟨C, K, hC, hK, hfac⟩ := exists_exp_geditSeries_eq (m := tailTarget ρ a)
    (tailTarget_zero hρ1 ha') hK₀ (c := 1 / 2) (by norm_num) (by norm_num) hdisc
    (fun s hs => (lseriesHasSum_tailTarget ha' hρ1 hs).LSeriesSummable)
    (L := tailFactor ρ a) hΦ₀ (fun s hs => logDeriv_tailFactor_eq ha' hρ1 hs)
  have he := isEdit_gedit (tailTarget ρ a)
  refine ⟨C, fun s => K s + editRem (gedit (tailTarget ρ a)) s, hC,
    hK.add (differentiableOn_editRem he), fun s hs => ?_⟩
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have hEK : Complex.exp (LSeries (fun k => (gedit (tailTarget ρ a) k : ℂ)) s +
      editRem (gedit (tailTarget ρ a)) s) =
      C * tailFactor ρ a s * Complex.exp (K s + editRem (gedit (tailTarget ρ a)) s) := by
    rw [Complex.exp_add, hfac s hs, Complex.exp_add]
    ring
  rw [editSystem_zetaSeriesC he hs, hEK, zetaResidueUnit_of_ne hs1]
  ring

/-- The continuation of `(s − 1) ζ_B(s)` of a twin with a tail. -/
theorem IsTailTwin.exists_continuation {B : BeurlingSystem} {ρ : ℂ} {a : ℝ}
    (h : IsTailTwin B ρ a) :
    ∃ (C : ℂ) (H : ℂ → ℂ), C ≠ 0 ∧
      DifferentiableOn ℂ (fun s => zetaResidueUnit s *
        (C * tailFactor ρ a s * Complex.exp (H s))) {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → (s - 1) * B.zetaSeriesC s =
        zetaResidueUnit s * (C * tailFactor ρ a s * Complex.exp (H s)) := by
  obtain ⟨C, H, hC, hH, hfac⟩ := h
  refine ⟨C, H, hC, differentiable_zetaResidueUnit.differentiableOn.mul ?_, hfac⟩
  exact ((differentiableOn_const C).mul (differentiable_tailFactor ρ a).differentiableOn).mul
    hH.cexp

/-- The fake zeros of a twin with a tail: the pair and the zeros of `u(2s − 2a)`. -/
theorem IsTailTwin.hasFakeZeroSet {B : BeurlingSystem} {ρ : ℂ} {a : ℝ} (h : IsTailTwin B ρ a) :
    HasFakeZeroSet B
      ({ρ, (starRingEnd ℂ) ρ} ∪ {z : ℂ | zetaResidueUnit (2 * z - 2 * (a : ℂ)) = 0}) := by
  obtain ⟨C, H, hC, hdiff, hfac⟩ := h.exists_continuation
  refine ⟨_, hdiff, fun s hs => (hfac s hs).symm, fun z _ hz1 hzζ => ?_⟩
  have hzu : zetaResidueUnit z ≠ 0 := by
    rw [zetaResidueUnit_of_ne hz1]
    exact mul_ne_zero (sub_ne_zero.mpr hz1) hzζ
  simp only [tailFactor, mul_eq_zero, hzu, hC, Complex.exp_ne_zero, false_or, or_false,
    sub_eq_zero, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]

/-! ## The tail -/

/-- Every point of the tail lies left of `a + 1/2`. -/
theorem tailSet_re_lt {a : ℝ} {z : ℂ} (hz : z ∈ tailSet a) : z.re < a + 1 / 2 := by
  obtain ⟨-, hu⟩ := hz
  set w : ℂ := 2 * z - 2 * (a : ℂ) with hw
  have hw1 : w ≠ 1 := fun h => by
    rw [h, zetaResidueUnit_one] at hu
    exact one_ne_zero hu
  rw [zetaResidueUnit_of_ne hw1] at hu
  have hζ : riemannZeta w = 0 := (mul_eq_zero.mp hu).resolve_left (sub_ne_zero.mpr hw1)
  have hre : w.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ
  have hwre : w.re = 2 * z.re - 2 * a := by
    rw [hw]
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_zero]
  linarith

theorem riemannXi_one_sub' (z : ℂ) : riemannXi (1 - z) = riemannXi z := by
  rw [riemannXi, riemannXi, completedRiemannZeta₀_one_sub]
  ring

/-- A zero of `ξ` is a zero of `u(w) = (w − 1) ζ(w)`. -/
theorem zetaResidueUnit_eq_zero_of_riemannXi {z : ℂ} (hz : riemannXi z = 0) :
    zetaResidueUnit z = 0 := by
  have hz0 : z ≠ 0 := fun h => by
    rw [h, riemannXi_zero] at hz
    norm_num at hz
  have hz1 : z ≠ 1 := fun h => by
    rw [h, riemannXi_one] at hz
    norm_num at hz
  rw [riemannXi_eq_mul_completedRiemannZeta hz0 hz1] at hz
  have hΛ : completedRiemannZeta z = 0 := by
    have h := (div_eq_zero_iff.mp hz).resolve_right (by norm_num)
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hz0 (sub_ne_zero.mpr hz1))
  rw [zetaResidueUnit_of_ne hz1, riemannZeta_def_of_ne_zero hz0, hΛ, zero_div, mul_zero]

/-- **The tail is infinite**: for `a > 1/4` infinitely many points `a + z/2` lie right of the
line. -/
theorem tailSet_infinite {a : ℝ} (ha : 1 / 4 < a) : (tailSet a).Infinite := by
  -- the zeros of `ξ` in the closed right half of the strip
  set A : Set ℂ := {z : ℂ | riemannXi z = 0 ∧ 1 / 2 ≤ z.re} with hA
  have hAinf : A.Infinite := by
    intro hfin
    refine riemannXi_zeroSet_infinite ((hfin.union (hfin.image fun z : ℂ => 1 - z)).subset ?_)
    intro z hz
    have hz' : riemannXi z = 0 := hz
    by_cases h : 1 / 2 ≤ z.re
    · exact Or.inl ⟨hz', h⟩
    · refine Or.inr ⟨1 - z, ⟨by rw [riemannXi_one_sub']; exact hz', ?_⟩, by ring⟩
      have h' : z.re < 1 / 2 := not_le.mp h
      rw [Complex.sub_re, Complex.one_re]
      linarith
  have hinj : Function.Injective fun z : ℂ => (a : ℂ) + z / 2 := by
    intro z₁ z₂ h
    have h' : z₁ / 2 = z₂ / 2 := add_left_cancel h
    field_simp at h'
    exact h'
  refine (hAinf.image hinj.injOn).mono ?_
  rintro _ ⟨z, ⟨hz, hre⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · have hr : ((a : ℂ) + z / 2).re = a + z.re / 2 := by simp
    rw [hr]
    linarith
  · rw [show 2 * ((a : ℂ) + z / 2) - 2 * (a : ℂ) = z by ring]
    exact zetaResidueUnit_eq_zero_of_riemannXi hz

/-! ## A finite layer with a tail -/

/-- **A finite layer with a tail over the rational primes.**  For `1/4 < a ≤ 3/10`,
`a + 1/2 < Re ρ ≤ 9/10` and `β ∈ (Re ρ, 1)` there is a two-sided edit of the rational primes with
count `A x + O(x^β)` whose zeta function is that of `ζ` times `(s − ρ)(s − ρ̄) u(2s − 2a)` and a
zero-free factor.  Its fake zeros right of the line are the pair `ρ, ρ̄` and the tail
`{a + z/2 : ζ(z) = 0}`; the tail is infinite and lies in `Re s < a + 1/2 < Re ρ`. -/
theorem exists_isEdit_finite_layer_with_tail {ρ : ℂ} {a : ℝ} (ha : 1 / 4 < a) (ha2 : a ≤ 3 / 10)
    (hρ0 : a + 1 / 2 < ρ.re) (hρ : ρ.re ≤ 9 / 10) {β : ℝ} (hβ : ρ.re < β) (hβ1 : β < 1) :
    ∃ e : ℕ → ℤ, IsEdit e ∧
      (∃ A C : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x →
        |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) ∧
      IsTailTwin (editSystem e) ρ a ∧
      HasFakeZeroSet (editSystem e)
        ({ρ, (starRingEnd ℂ) ρ} ∪ {z : ℂ | zetaResidueUnit (2 * z - 2 * (a : ℂ)) = 0}) ∧
      (tailSet a).Infinite ∧ ∀ z ∈ tailSet a, z.re < ρ.re := by
  have htwin := isTailTwin_editSystem (ρ := ρ) ha ha2 hρ
  refine ⟨gedit (tailTarget ρ a), isEdit_gedit _, ?_, htwin, htwin.hasFakeZeroSet,
    tailSet_infinite ha, fun z hz => lt_trans (tailSet_re_lt hz) hρ0⟩
  refine editSystem_count (by linarith) hβ1 (summable_abs_gedit_rpow (θ := ρ.re) (by linarith)
    (K := 2 / ρ.re + 4 / (2 * (ρ.re - (a + 1 / 2))) + 1 / (a + 1 / 2)) ?_ (fun n hn => ?_) hβ)
  · have h1 : 0 < ρ.re := by linarith
    have h2 : 0 < ρ.re - (a + 1 / 2) := by linarith
    have h3 : 0 < a + 1 / 2 := by linarith
    positivity
  · exact sum_abs_tailTarget_le (by linarith) hρ0 (by linarith) hn

end GaloisForLFunctions.WorldsOfTheZeroConfiguration
