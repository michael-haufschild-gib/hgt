import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Monotonicity of the heat trace and the extension of an on-diagonal bound

Lemma 2.3 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), upgrades a bound valid on `(0,1]` to one valid for all positive
times with the sentence "since `k(t,x,x)` is decreasing in `t`, we deduce
`k(t,x,x) ≤ C₀(n,Λ)(t^{−n} + 1)` for all `t > 0`".

Both halves of that step are elementary and are proved here: the on-diagonal heat kernel is a
spectral sum `Σ e^{−tλ}|φ|²` with nonnegative weights and hence antitone in `t`, and an antitone
function bounded by `C t^{−n}` on `(0,1]` obeys `C(t^{−n} + 1)` everywhere.
-/

open Set Real

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- **The on-diagonal heat trace is antitone.**

A spectral sum `Σ e^{−tλᵢ} aᵢ` with nonnegative spectrum and nonnegative weights decreases in the
time variable. -/
theorem antitoneOn_tsum_exp_neg_mul {ι : Type*} {lam a : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (ha : ∀ i, 0 ≤ a i)
    (hsum : ∀ t ∈ Ioi (0 : ℝ), Summable fun i => Real.exp (-(t * lam i)) * a i) :
    AntitoneOn (fun t => ∑' i, Real.exp (-(t * lam i)) * a i) (Ioi (0 : ℝ)) := by
  intro t₁ ht₁ t₂ ht₂ hle
  refine (hsum t₂ ht₂).tsum_le_tsum (fun i => ?_) (hsum t₁ ht₁)
  refine mul_le_mul_of_nonneg_right ?_ (ha i)
  refine Real.exp_le_exp.mpr ?_
  have : t₁ * lam i ≤ t₂ * lam i := mul_le_mul_of_nonneg_right hle (hlam i)
  linarith

/-- **Lemma 2.3's extension step.**

An antitone function bounded by `C t^{−n}` on `(0,1]` is bounded by `C(t^{−n} + 1)` on all of
`(0,∞)`. -/
theorem le_mul_add_one_of_antitoneOn {f : ℝ → ℝ} {C : ℝ} {n : ℕ} (hC : 0 ≤ C)
    (hanti : AntitoneOn f (Ioi (0 : ℝ)))
    (hbd : ∀ t ∈ Ioc (0 : ℝ) 1, f t ≤ C / t ^ n) :
    ∀ t ∈ Ioi (0 : ℝ), f t ≤ C * (1 / t ^ n + 1) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  have hpow : (0 : ℝ) < t ^ n := pow_pos ht0 n
  rcases le_or_gt t 1 with h1 | h1
  · have hle := hbd t ⟨ht0, h1⟩
    have hrw : C / t ^ n = C * (1 / t ^ n) := by ring
    rw [hrw] at hle
    refine hle.trans ?_
    have hnn : (0 : ℝ) ≤ 1 / t ^ n := by positivity
    nlinarith [hC, hnn]
  · have hone : f t ≤ f 1 := hanti (by norm_num) ht h1.le
    have hf1 : f 1 ≤ C := by
      have := hbd 1 ⟨by norm_num, le_refl 1⟩
      simpa using this
    have hnn : (0 : ℝ) ≤ 1 / t ^ n := by positivity
    nlinarith [hone, hf1, hC, hnn]

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
