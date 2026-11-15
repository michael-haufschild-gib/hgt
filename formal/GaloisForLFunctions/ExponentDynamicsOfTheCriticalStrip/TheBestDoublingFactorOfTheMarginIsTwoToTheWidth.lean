import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle

/-!
# The best doubling factor of the margin is two to the width

A **level law** along a block-size law `ρ` is a function `a(K)` such that the neutral matrix of
every window `(ρ(K), (3K + 1)ρ(K)]`, raised by `a(K)`, has at most one negative square. A
**doubling law with factor `λ`** is a monotone level law with `a(2K) ≤ λ a(K) + c`: a stage map
from ratio `K` to ratio `2K` with loss factor `λ`. The trivial factor of the window calculus is
`√2`. This module computes the best one, with no hypothesis on the zeros.

* **Stage calculus** (`le_rpow_logb_of_doubling`): a monotone sequence with
  `a(2K) ≤ λ a(K) + c`, `λ > 1`, is `O(K^{log₂ λ})`.
* **A doubling law is a half-plane** (`zetaZeroWidth_le_logb_of_doublingLaw`): along block sizes
  `ρ(K) ≥ K¹⁰`, a doubling law with factor `λ` gives `sup |Re ρ − ½| ≤ log₂ λ`.
* **Every factor above `2^w` occurs** (`doublingLaw_of_zetaZeroWidth_lt`), and every factor above
  `2^{3/8}` occurs with no hypothesis (`doublingLaw_of_three_eighths_lt`).
* **Ruler** (`isRuler_doublingLaw`) and **best factor** (`sInf_doublingLaw_eq_two_rpow_zetaZeroWidth`):
  for `K¹⁰ ≤ ρ(K) ≤ K^A` the infimum of the factors of the doubling laws is `2^w`.

A doubling law is thus neither weaker nor stronger than a zero-free half-plane: a proof of a
factor below `2^{3/8}` from the calculus of the windows is a proof of a half-plane beyond the
known one, and no factor below `2^w` exists.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry (hermNegIndex)
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg
  zetaZeroWidth_le_three_eighths)
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

noncomputable section

/-! ### 1. Stage calculus: a doubling inequality is a power law -/

/-- Along the powers of two a doubling inequality iterates: with `d = c/(λ − 1)`,
`a(2ⁿ) + d ≤ (a(1) + d) λⁿ`. -/
theorem doubling_pow_two {a : ℕ → ℝ} {lam c : ℝ} (hlam : 1 < lam)
    (hd : ∀ K, 1 ≤ K → a (2 * K) ≤ lam * a K + c) (n : ℕ) :
    a (2 ^ n) + c / (lam - 1) ≤ (a 1 + c / (lam - 1)) * lam ^ n := by
  have hl : 0 < lam - 1 := by linarith
  have hcd : c + c / (lam - 1) = lam * (c / (lam - 1)) := by
    field_simp
    ring
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := hd (2 ^ n) (Nat.one_le_two_pow)
    have h2 : a (2 ^ (n + 1)) = a (2 * 2 ^ n) := by rw [pow_succ, mul_comm]
    have h3 := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ lam)
    have h4 : lam * ((a 1 + c / (lam - 1)) * lam ^ n) = (a 1 + c / (lam - 1)) * lam ^ (n + 1) := by
      rw [pow_succ]
      ring
    rw [h2]
    linarith

/-- `λ^m = (2^m)^{log₂ λ}`. -/
theorem pow_eq_two_pow_rpow_logb {lam : ℝ} (hlam : 0 < lam) (m : ℕ) :
    lam ^ m = ((2 : ℝ) ^ m) ^ Real.logb 2 lam := by
  have h2 : (2 : ℝ) ^ Real.logb 2 lam = lam :=
    Real.rpow_logb (by norm_num) (by norm_num) hlam
  calc lam ^ m = ((2 : ℝ) ^ Real.logb 2 lam) ^ m := by rw [h2]
    _ = (2 : ℝ) ^ (Real.logb 2 lam * (m : ℝ)) := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    _ = (2 : ℝ) ^ ((m : ℝ) * Real.logb 2 lam) := by rw [mul_comm]
    _ = ((2 : ℝ) ^ m) ^ Real.logb 2 lam := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- **A doubling inequality is a power law.** A monotone sequence with `a(2K) ≤ λ a(K) + c` for
all `K ≥ 1` and `λ > 1` satisfies `a(K) ≤ λ (|a(1)| + 2|c|/(λ − 1)) K^{log₂ λ}`. -/
theorem le_rpow_logb_of_doubling {a : ℕ → ℝ} {lam c : ℝ} (hlam : 1 < lam) (hmono : Monotone a)
    (hd : ∀ K, 1 ≤ K → a (2 * K) ≤ lam * a K + c) (K : ℕ) (hK : 1 ≤ K) :
    a K ≤ lam * (|a 1| + 2 * |c| / (lam - 1)) * (K : ℝ) ^ Real.logb 2 lam := by
  have hl : 0 < lam - 1 := by linarith
  have hlam0 : 0 < lam := by linarith
  have hθ : 0 ≤ Real.logb 2 lam := Real.logb_nonneg (by norm_num) hlam.le
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.log 2 K := ⟨_, rfl⟩
  have hlo : 2 ^ m ≤ K := by
    rw [hm]
    exact Nat.pow_log_le_self 2 (by omega)
  have hhi : K ≤ 2 ^ (m + 1) := by
    rw [hm]
    exact (Nat.lt_pow_succ_log_self (by norm_num) K).le
  -- the level at the next power of two
  have h1 := doubling_pow_two hlam hd (m + 1)
  have h2 : a K ≤ a (2 ^ (m + 1)) := hmono hhi
  -- the power of the factor against the power of the ratio
  have h3 : lam ^ m ≤ (K : ℝ) ^ Real.logb 2 lam := by
    rw [pow_eq_two_pow_rpow_logb hlam0 m]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlo) hθ
  have hpow1 : (1 : ℝ) ≤ lam ^ (m + 1) := one_le_pow₀ hlam.le
  have hd0 : 0 ≤ |c| / (lam - 1) := div_nonneg (abs_nonneg c) hl.le
  have hdabs : |c / (lam - 1)| = |c| / (lam - 1) := by rw [abs_div, abs_of_pos hl]
  have hB : (a 1 + c / (lam - 1)) * lam ^ (m + 1) - c / (lam - 1) ≤
      (|a 1| + 2 * |c| / (lam - 1)) * lam ^ (m + 1) := by
    have e1 : a 1 + c / (lam - 1) ≤ |a 1| + |c| / (lam - 1) := by
      rw [← hdabs]
      exact add_le_add (le_abs_self _) (le_abs_self _)
    have e2 := mul_le_mul_of_nonneg_right e1 (by linarith : (0 : ℝ) ≤ lam ^ (m + 1))
    have e3 : -(c / (lam - 1)) ≤ |c| / (lam - 1) * lam ^ (m + 1) := by
      have e4 : -(c / (lam - 1)) ≤ |c| / (lam - 1) := by
        rw [← hdabs]
        exact neg_le_abs _
      have e5 := mul_le_mul_of_nonneg_left hpow1 hd0
      linarith
    have e6 : (|a 1| + 2 * |c| / (lam - 1)) * lam ^ (m + 1) =
        (|a 1| + |c| / (lam - 1)) * lam ^ (m + 1) + |c| / (lam - 1) * lam ^ (m + 1) := by ring
    linarith
  have hB0 : 0 ≤ |a 1| + 2 * |c| / (lam - 1) :=
    add_nonneg (abs_nonneg _) (div_nonneg (by positivity) hl.le)
  have h4 : (|a 1| + 2 * |c| / (lam - 1)) * lam ^ (m + 1) ≤
      lam * (|a 1| + 2 * |c| / (lam - 1)) * (K : ℝ) ^ Real.logb 2 lam := by
    have e := mul_le_mul_of_nonneg_left h3 (mul_nonneg hlam0.le hB0)
    have e' : (|a 1| + 2 * |c| / (lam - 1)) * lam ^ (m + 1) =
        lam * (|a 1| + 2 * |c| / (lam - 1)) * lam ^ m := by
      rw [pow_succ]
      ring
    linarith
  linarith

/-! ### 2. Level laws and doubling laws -/

/-- A **level law** along a block-size law `ρ`: the neutral part of every window
`(ρ(K), (3K + 1)ρ(K)]` plus `a(K)` has at most one negative square. -/
def IsLevelLaw (ρ : ℕ → ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ K : ℕ, 1 ≤ K →
    hermNegIndex ((neutralWindow (3 * K + 1) (ρ K) (3 * K * ρ K) +
      Matrix.diagonal fun _ => a K).map (↑) :
        Matrix (Fin (3 * K * ρ K)) (Fin (3 * K * ρ K)) ℂ) ≤ 1

/-- A **doubling law with factor `lam`**: a monotone level law whose level at the ratio `2K` is
at most `lam` times its level at `K` plus a constant. -/
def DoublingLaw (ρ : ℕ → ℕ) (lam : ℝ) : Prop :=
  ∃ a : ℕ → ℝ, ∃ c : ℝ, Monotone a ∧ (∀ K, 1 ≤ K → a (2 * K) ≤ lam * a K + c) ∧ IsLevelLaw ρ a

/-- Raising the levels keeps a level law. -/
theorem IsLevelLaw.mono {ρ : ℕ → ℕ} {a b : ℕ → ℝ} (h : IsLevelLaw ρ a)
    (hab : ∀ K, 1 ≤ K → a K ≤ b K) : IsLevelLaw ρ b := fun K hK =>
  (GreenCalculusOfThePrimeFreeWindow.hermNegIndex_add_diagonal_mono
    (neutralWindow (3 * K + 1) (ρ K) (3 * K * ρ K)) (hab K hK)).trans (h K hK)

/-- The margin law of rate `β` is a level law with levels `C K^β`. -/
theorem marginLaw_iff_exists_isLevelLaw {ρ : ℕ → ℕ} {β : ℝ} :
    MarginLaw ρ β ↔ ∃ C : ℝ, IsLevelLaw ρ fun K => C * (K : ℝ) ^ β :=
  Iff.rfl

/-- **A doubling law with factor `lam` is a margin law of rate `log₂ lam`.** -/
theorem marginLaw_of_doublingLaw {ρ : ℕ → ℕ} {lam : ℝ} (hlam : 1 < lam)
    (h : DoublingLaw ρ lam) : MarginLaw ρ (Real.logb 2 lam) := by
  obtain ⟨a, c, hmono, hd, hlev⟩ := h
  exact marginLaw_iff_exists_isLevelLaw.mpr
    ⟨lam * (|a 1| + 2 * |c| / (lam - 1)), hlev.mono (le_rpow_logb_of_doubling hlam hmono hd)⟩

/-- **A margin law of rate `β ≥ 0` is a doubling law with factor `2^β`**, with no additive
term: the levels `max(C, 0) K^β`. -/
theorem doublingLaw_of_marginLaw {ρ : ℕ → ℕ} {β : ℝ} (hβ : 0 ≤ β) (h : MarginLaw ρ β) :
    DoublingLaw ρ ((2 : ℝ) ^ β) := by
  obtain ⟨C, hC⟩ := marginLaw_iff_exists_isLevelLaw.mp h
  refine ⟨fun K => max C 0 * (K : ℝ) ^ β, 0, fun K K' hKK' => ?_, fun K _ => ?_,
    hC.mono fun K _ => ?_⟩
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg K) (by exact_mod_cast hKK') hβ) (le_max_right C 0)
  · have e : (((2 * K : ℕ)) : ℝ) ^ β = (2 : ℝ) ^ β * (K : ℝ) ^ β := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) (Nat.cast_nonneg K)]
    show max C 0 * (((2 * K : ℕ)) : ℝ) ^ β ≤ (2 : ℝ) ^ β * (max C 0 * (K : ℝ) ^ β) + 0
    rw [e]
    exact le_of_eq (by ring)
  · exact mul_le_mul_of_nonneg_right (le_max_left C 0)
      (Real.rpow_nonneg (Nat.cast_nonneg K) β)

/-! ### 3. The best factor -/

/-- **A doubling law is a half-plane.** Along block sizes at least the tenth power of the
ratio, a doubling law with factor `lam > 1` gives `sup |Re ρ − ½| ≤ log₂ lam`. -/
theorem zetaZeroWidth_le_logb_of_doublingLaw {ρ : ℕ → ℕ} (hρ : ∀ K, K ^ 10 ≤ ρ K) {lam : ℝ}
    (hlam : 1 < lam) (h : DoublingLaw ρ lam) : zetaZeroWidth ≤ Real.logb 2 lam :=
  zetaZeroWidth_le_of_marginLaw hρ (Real.logb_nonneg (by norm_num) hlam.le)
    (marginLaw_of_doublingLaw hlam h)

/-- **Every factor above `2^w` occurs**, along block sizes at most polynomial in the ratio. -/
theorem doublingLaw_of_zetaZeroWidth_lt {ρ : ℕ → ℕ} (hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K) {A : ℕ}
    (hρA : ∀ K, ρ K ≤ K ^ A) {β : ℝ} (hβ : zetaZeroWidth < β) : DoublingLaw ρ ((2 : ℝ) ^ β) :=
  doublingLaw_of_marginLaw (zetaZeroWidth_nonneg.trans hβ.le)
    (marginLaw_of_zetaZeroWidth_lt hρ₁ hρA hβ)

/-- **The window calculus has a stage map below the trivial factor**: a doubling law with
factor `2^β` for every `β > 3/8`, with no hypothesis on the zeros. -/
theorem doublingLaw_of_three_eighths_lt {ρ : ℕ → ℕ} (hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K) {A : ℕ}
    (hρA : ∀ K, ρ K ≤ K ^ A) {β : ℝ} (hβ : 3 / 8 < β) : DoublingLaw ρ ((2 : ℝ) ^ β) :=
  doublingLaw_of_zetaZeroWidth_lt hρ₁ hρA (lt_of_le_of_lt zetaZeroWidth_le_three_eighths hβ)

/-- **The doubling laws of the margin are a ruler.** Along a block-size law with
`K¹⁰ ≤ ρ(K) ≤ K^A`, the zero width is at most `β` iff a doubling law holds with every factor
`2^{β + ε}`. -/
theorem isRuler_doublingLaw {ρ : ℕ → ℕ} (hρ : ∀ K, K ^ 10 ≤ ρ K) {A : ℕ}
    (hρA : ∀ K, ρ K ≤ K ^ A) :
    IsRuler zetaZeroWidth (Set.Ici 0) fun β =>
      ∀ ε : ℝ, 0 < ε → DoublingLaw ρ ((2 : ℝ) ^ (β + ε)) := by
  have hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K := fun K hK => lt_of_lt_of_le (pow_pos hK 10) (hρ K)
  intro β hβ
  have hβ0 : 0 ≤ β := hβ
  constructor
  · intro hw ε hε
    exact doublingLaw_of_zetaZeroWidth_lt hρ₁ hρA (by linarith)
  · intro h
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 := zetaZeroWidth_le_logb_of_doublingLaw hρ
      (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by linarith : 0 < β + ε)) (h ε hε)
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at h1

/-- **The best doubling factor of the margin is `2^w`**: along a block-size law with
`K¹⁰ ≤ ρ(K) ≤ K^A`, the infimum of the factors `lam > 1` of the doubling laws is two to the power
`sup |Re ρ − ½|`. -/
theorem sInf_doublingLaw_eq_two_rpow_zetaZeroWidth {ρ : ℕ → ℕ} (hρ : ∀ K, K ^ 10 ≤ ρ K) {A : ℕ}
    (hρA : ∀ K, ρ K ≤ K ^ A) :
    sInf {lam : ℝ | 1 < lam ∧ DoublingLaw ρ lam} = (2 : ℝ) ^ zetaZeroWidth := by
  have hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K := fun K hK => lt_of_lt_of_le (pow_pos hK 10) (hρ K)
  have hw0 := zetaZeroWidth_nonneg
  have hmem : ∀ ε : ℝ, 0 < ε →
      (2 : ℝ) ^ (zetaZeroWidth + ε) ∈ {lam : ℝ | 1 < lam ∧ DoublingLaw ρ lam} := fun ε hε =>
    ⟨Real.one_lt_rpow (by norm_num) (by linarith),
      doublingLaw_of_zetaZeroWidth_lt hρ₁ hρA (by linarith)⟩
  have hbdd : BddBelow {lam : ℝ | 1 < lam ∧ DoublingLaw ρ lam} := ⟨1, fun lam h => h.1.le⟩
  have hlow : (2 : ℝ) ^ zetaZeroWidth ≤ sInf {lam : ℝ | 1 < lam ∧ DoublingLaw ρ lam} := by
    refine le_csInf ⟨_, hmem 1 one_pos⟩ fun lam hl => ?_
    have h1 := zetaZeroWidth_le_logb_of_doublingLaw hρ hl.1 hl.2
    have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h1
    rwa [Real.rpow_logb (by norm_num) (by norm_num) (by linarith [hl.1])] at h2
  refine le_antisymm ?_ hlow
  by_contra hcon
  rw [not_le] at hcon
  -- a factor strictly between `2^w` and the infimum
  have hs0 : 0 < sInf {lam : ℝ | 1 < lam ∧ DoublingLaw ρ lam} :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hlow
  obtain ⟨β, hβ⟩ : ∃ β, β = Real.logb 2 (sInf {lam : ℝ | 1 < lam ∧ DoublingLaw ρ lam}) :=
    ⟨_, rfl⟩
  have hwβ : zetaZeroWidth < β := by
    have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      (Real.rpow_pos_of_pos (by norm_num) zetaZeroWidth) hcon
    rwa [Real.logb_rpow (by norm_num) (by norm_num), ← hβ] at h
  have h1 := csInf_le hbdd (hmem ((β - zetaZeroWidth) / 2) (by linarith))
  have h2 : (2 : ℝ) ^ (zetaZeroWidth + (β - zetaZeroWidth) / 2) < (2 : ℝ) ^ β :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ β = sInf {lam : ℝ | 1 < lam ∧ DoublingLaw ρ lam} := by
    rw [hβ, Real.rpow_logb (by norm_num) (by norm_num) hs0]
  rw [h3] at h2
  linarith

/-- The zero width vanishes iff the margin has doubling laws with every factor above one. -/
theorem zetaZeroWidth_eq_zero_iff_forall_doublingLaw {ρ : ℕ → ℕ} (hρ : ∀ K, K ^ 10 ≤ ρ K)
    {A : ℕ} (hρA : ∀ K, ρ K ≤ K ^ A) :
    zetaZeroWidth = 0 ↔ ∀ lam : ℝ, 1 < lam → DoublingLaw ρ lam := by
  have hρ₁ : ∀ K, 1 ≤ K → 1 ≤ ρ K := fun K hK => lt_of_lt_of_le (pow_pos hK 10) (hρ K)
  constructor
  · intro hw lam hlam
    have hθ : 0 < Real.logb 2 lam := Real.logb_pos (by norm_num) hlam
    have h := doublingLaw_of_zetaZeroWidth_lt hρ₁ hρA (β := Real.logb 2 lam) (by rw [hw]; exact hθ)
    rwa [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)] at h
  · intro h
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) zetaZeroWidth_nonneg
    have h1 := zetaZeroWidth_le_logb_of_doublingLaw hρ
      (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hε) (h _ (Real.one_lt_rpow (by norm_num) hε))
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at h1
    linarith

#print axioms zetaZeroWidth_le_logb_of_doublingLaw
#print axioms doublingLaw_of_three_eighths_lt
#print axioms sInf_doublingLaw_eq_two_rpow_zetaZeroWidth

end

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
