import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurface
import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity

/-!
# On nonnegative tests `ζ` is the worst twin

The explicit formula is affine in the source: for prime weights `w` and `λ`,

`W_w(k) − W_λ(k) = Σ_{n ≥ 2} (λ(n) − w(n)) n^{−1/2} (k(log n) + k(−log n))`
(`weilFullFunctional_sub_eq`).

So on a test whose **atoms** `Re(k(log n) + k(−log n))` are nonnegative, Weil's functional is
antitone in the source (`re_weilFullFunctional_le_of_le`). The autocorrelation `f ⋆ f̃` of a
nonnegative test is nonnegative (`re_weilTest_nonneg`), so:

* **`ζ` is the worst twin on nonnegative tests** (`re_weilFullFunctional_vonMangoldt_le_of_nonneg`).
  For every real `f ≥ 0` and every weight `w ≤ Λ` — every sign twin `εΛ`, the Liouville twin `λΛ`
  (`liouvilleTwin_le`), every truncation, the prime-free weight `0` — the form of `Λ` is at most the
  form of `w`. Positivity of `ζ`'s form on nonnegative tests therefore transfers to all of them
  (`weilPositive_nonneg_transfers`): it is an upper-bound (sieve) statement about the size of `Λ`
  and cannot see the sign of any atom.
* **Sign-changing atoms reverse the order** (`flipTwin_lt`). If an atom of `k` at `n₀` with
  `Λ(n₀) > 0` is negative, flipping the sign of `Λ(n₀)` strictly lowers the form: `ζ` is no longer
  extremal in its orbit.

So a positivity statement that is specific to `ζ` among its sign twins must be tested on
autocorrelations that change sign at prime-power logarithms: it is a cancellation statement, carried
by gauge-charged information, as the gauge principle requires.
-/

open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open ArithmeticCastelnuovoSeveri _root_.RHTower Zeta23

/-- The prime atom `n^{−1/2}(k(log n) + k(−log n))` weight of a source, as it enters the functional. -/
def primeCoeff (w : ℕ → ℝ) (n : ℕ) : ℝ := if 2 ≤ n then w n / Real.sqrt n else 0

/-- **The explicit formula is affine in the source.** -/
theorem weilFullFunctional_sub_eq (w lam : ℕ → ℝ) {k : ℝ → ℂ} (hk : HasCompactSupport k) :
    weilFullFunctional w k - weilFullFunctional lam k =
      ∑' n : ℕ, ((primeCoeff lam n - primeCoeff w n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
  rw [weilFullFunctional_eq_sub w hk, weilFullFunctional_eq_sub lam hk]
  have h1 := summable_primeAtoms
    (fun n => if 2 ≤ n then (w n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n else 0) hk
  have h2 := summable_primeAtoms
    (fun n => if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n else 0) hk
  rw [sub_sub_sub_cancel_left, ← h2.tsum_sub h1]
  refine tsum_congr fun n => ?_
  by_cases hn : 2 ≤ n
  · simp only [primeCoeff, if_pos hn]; push_cast; ring
  · simp only [primeCoeff, if_neg hn]; push_cast; ring

/-- **Antitone in the source on nonnegative atoms.** If `w ≤ λ` on `n ≥ 2` and every atom of `k` is
nonnegative, then `Re W_λ(k) ≤ Re W_w(k)`. -/
theorem re_weilFullFunctional_le_of_le {w lam : ℕ → ℝ} (hwl : ∀ n, 2 ≤ n → w n ≤ lam n)
    {k : ℝ → ℂ} (hk : HasCompactSupport k)
    (hatoms : ∀ n : ℕ, 2 ≤ n → 0 ≤ (k (Real.log n) + k (-Real.log n)).re) :
    (weilFullFunctional lam k).re ≤ (weilFullFunctional w k).re := by
  have hsum := summable_primeAtoms (fun n => primeCoeff lam n - primeCoeff w n) hk
  have h := congrArg Complex.re (weilFullFunctional_sub_eq w lam hk)
  rw [Complex.sub_re, Complex.re_tsum hsum] at h
  have hnn : 0 ≤ ∑' n : ℕ, (((primeCoeff lam n - primeCoeff w n : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n))).re := by
    refine tsum_nonneg fun n => ?_
    rw [Complex.re_ofReal_mul]
    by_cases hn : 2 ≤ n
    · refine mul_nonneg ?_ (hatoms n hn)
      simp only [primeCoeff, if_pos hn]
      rw [← sub_div]
      exact div_nonneg (sub_nonneg.mpr (hwl n hn)) (Real.sqrt_nonneg _)
    · simp [primeCoeff, if_neg hn]
  linarith

/-- The autocorrelation of a nonnegative test is nonnegative. -/
theorem re_weilTest_nonneg {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) (x : ℝ) :
    0 ≤ (EF.weilTest (cx f) (cx f) x).re := by
  rw [WeilSpectral.weilTest_apply]
  have : (fun u => cx f u * conj (cx f (u - x))) = fun u => ((f u * f (u - x) : ℝ) : ℂ) := by
    funext u; simp [cx]
  rw [this, integral_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun u => mul_nonneg (hf u) (hf _)

/-- **`ζ` is the worst twin on nonnegative tests.** For a nonnegative compactly supported test `f`
and every weight `w ≤ Λ`, the form of `Λ` on `f ⋆ f̃` is at most that of `w`. -/
theorem re_weilFullFunctional_vonMangoldt_le_of_nonneg {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u)
    (hfc : HasCompactSupport f) {w : ℕ → ℝ}
    (hw : ∀ n, 2 ≤ n → w n ≤ ArithmeticFunction.vonMangoldt n) :
    (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (cx f) (cx f))).re ≤
      (weilFullFunctional w (EF.weilTest (cx f) (cx f))).re := by
  refine re_weilFullFunctional_le_of_le hw
    (EF.weilTest_hasCompactSupport (cx_hasCompactSupport hfc) (cx_hasCompactSupport hfc))
    fun n _ => ?_
  rw [Complex.add_re]
  exact add_nonneg (re_weilTest_nonneg hf _) (re_weilTest_nonneg hf _)

/-- The Liouville twin `λ(n)Λ(n)`, `λ(n) = (−1)^{Ω(n)}`. -/
def liouvilleTwin (n : ℕ) : ℝ :=
  (-1) ^ (ArithmeticFunction.cardFactors n) * ArithmeticFunction.vonMangoldt n

theorem liouvilleTwin_le (n : ℕ) : liouvilleTwin n ≤ ArithmeticFunction.vonMangoldt n := by
  have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  rcases neg_one_pow_eq_or ℝ (ArithmeticFunction.cardFactors n) with h | h <;>
    simp only [liouvilleTwin, h] <;> linarith

/-- **Positivity on nonnegative tests transfers to every dominated source**: the Liouville twin,
every sign twin, every truncation and the prime-free weight inherit it from `Λ`. -/
theorem weilPositive_nonneg_transfers
    (hζ : ∀ f : ℝ → ℝ, (∀ u, 0 ≤ f u) → ContDiff ℝ 2 f → HasCompactSupport f →
      0 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (cx f) (cx f))).re)
    {w : ℕ → ℝ} (hw : ∀ n, 2 ≤ n → w n ≤ ArithmeticFunction.vonMangoldt n)
    {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) (hf2 : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ (weilFullFunctional w (EF.weilTest (cx f) (cx f))).re :=
  (hζ f hf hf2 hfc).trans (re_weilFullFunctional_vonMangoldt_le_of_nonneg hf hfc hw)

/-- The twin of `Λ` with the sign of the atom at `n₀` flipped. -/
def flipTwin (n₀ : ℕ) (n : ℕ) : ℝ :=
  if n = n₀ then -ArithmeticFunction.vonMangoldt n else ArithmeticFunction.vonMangoldt n

/-- **Sign-changing atoms reverse the order.** If the atom of `k` at `n₀ ≥ 2` is negative and
`Λ(n₀) > 0`, the twin with the sign of `Λ(n₀)` flipped has strictly smaller form than `ζ`. -/
theorem flipTwin_lt {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hΛ : 0 < ArithmeticFunction.vonMangoldt n₀)
    {k : ℝ → ℂ} (hk : HasCompactSupport k)
    (hneg : (k (Real.log n₀) + k (-Real.log n₀)).re < 0) :
    (weilFullFunctional (flipTwin n₀) k).re <
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) k).re := by
  have hsum := summable_primeAtoms (fun n => primeCoeff (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) n -
    primeCoeff (flipTwin n₀) n) hk
  have h := congrArg Complex.re (weilFullFunctional_sub_eq (flipTwin n₀)
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) hk)
  rw [Complex.sub_re, Complex.re_tsum hsum] at h
  have hterm : ∀ n, n ≠ n₀ → (((primeCoeff (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) n -
      primeCoeff (flipTwin n₀) n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re = 0 := by
    intro n hn
    simp [primeCoeff, flipTwin, hn]
  rw [tsum_eq_single n₀ hterm] at h
  have hval : (((primeCoeff (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) n₀ -
      primeCoeff (flipTwin n₀) n₀ : ℝ) : ℂ) * (k (Real.log n₀) + k (-Real.log n₀))).re =
      2 * ArithmeticFunction.vonMangoldt n₀ / Real.sqrt n₀ *
        (k (Real.log n₀) + k (-Real.log n₀)).re := by
    rw [Complex.re_ofReal_mul]
    simp only [primeCoeff, flipTwin, if_pos hn₀, if_pos rfl]
    ring
  rw [hval] at h
  have hpos : 0 < 2 * ArithmeticFunction.vonMangoldt n₀ / Real.sqrt n₀ :=
    div_pos (by linarith) (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀)))
  have := mul_neg_of_pos_of_neg hpos hneg
  linarith

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
