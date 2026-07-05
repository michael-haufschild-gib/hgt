/-
# SpurDrift — the doc 27 weight flow and its hierarchy (task #143 / #138 substrate)

Doc 27 (27-drift-hierarchy.md) §1–2 `[PROVED HERE]` identities. Flat grading: one-variable
calculus + a finite-sum telescoping; doc 27 §1 does the derivations, nothing here is new
mathematics.

Original coordinate `c`, a section zero `α`, weight `η(c) = c/(c − α)`:

* `weight_hasDerivAt` — **the weight flow** `η′ = −η(η − 1)/c` (doc 27 §1). The logistic
  transport law, from the quotient rule.
* `weight_mul_pred_pos` — `w := η(η − 1) > 0` whenever `η ∉ [0,1]` (charge passed `η > 1`
  or charge ahead `η < 0`): the Calogero kernel positivity (doc 27 §0).
* `powerSum_hasDerivAt` — **the transport hierarchy** `p_r′ = −(r/c)(p_{r+1} − p_r)` for the
  power sums `p_r = Σ_k η_k^r` (doc 27 §1), by differentiating termwise and telescoping.

Log-time coordinate `t = log c`, log-zeros `t_k = log α_k`, `η_k(t) = ½ + ½ coth((t−t_k)/2)`:

* `logWeight_mul_one_sub` — the **Calogero kernel identity** `η(1 − η) = −¼ csch²((t−t_k)/2)`
  (doc 27 §1), from `coth² − 1 = csch²`.
* `logWeight_hasDerivAt` — the **autonomous logistic flow** `η̇ = η(1 − η)` in log-time
  (doc 27 §1): the weight flow becomes translation-invariant, the whole outer problem reduces
  to electrostatics of `{t_k}`.
-/
import GaloisForLFunctions.RHTower.SpurLattice

noncomputable section

namespace RHTower

open Finset

variable {ι : Type*}

/-- The weight `η_k(c) = c/(c − α_k)` (doc 27 §0). -/
def weight (α c : ℝ) : ℝ := c / (c - α)

/-- **The weight flow** `η′ = −η(η − 1)/c` (doc 27 §1): the logistic transport law. -/
theorem weight_hasDerivAt {α c : ℝ} (hc : c ≠ 0) (hca : c ≠ α) :
    HasDerivAt (weight α) (-(weight α c) * (weight α c - 1) / c) c := by
  have hca' : c - α ≠ 0 := sub_ne_zero.mpr hca
  have hd : HasDerivAt (fun c => c / (c - α)) ((1 * (c - α) - c * 1) / (c - α) ^ 2) c :=
    (hasDerivAt_id c).div ((hasDerivAt_id c).sub_const α) hca'
  have halg : (1 * (c - α) - c * 1) / (c - α) ^ 2
      = -(weight α c) * (weight α c - 1) / c := by
    unfold weight; field_simp; ring
  rw [← halg]; exact hd

/-- `w := η(η − 1) > 0` whenever the weight lies outside `[0,1]` — charge passed (`η > 1`) or
charge ahead (`η < 0`) (doc 27 §0). -/
theorem weight_mul_pred_pos {η : ℝ} (h : η < 0 ∨ 1 < η) : 0 < η * (η - 1) := by
  rcases h with h | h
  · exact mul_pos_of_neg_of_neg h (by linarith)
  · exact mul_pos (by linarith) (by linarith)

/-- The power sum `p_r(c) = Σ_k η_k(c)^r` (doc 27 §0). -/
def powerSum (α : ι → ℝ) (s : Finset ι) (r : ℕ) (c : ℝ) : ℝ :=
  ∑ k ∈ s, (weight (α k) c) ^ r

/-- **The transport hierarchy** `p_{r+1}′ = −((r+1)/c)(p_{r+2} − p_{r+1})` (doc 27 §1):
differentiate `η_k^{r+1}` termwise (`= (r+1)η_k^r·η_k′`), substitute the weight flow
(`η_k^r·η_k(η_k−1) = η_k^{r+2} − η_k^{r+1}`), and telescope the sum. -/
theorem powerSum_hasDerivAt {α : ι → ℝ} {s : Finset ι} {c : ℝ} (r : ℕ)
    (hc : c ≠ 0) (hca : ∀ k ∈ s, c ≠ α k) :
    HasDerivAt (powerSum α s (r + 1))
      (-((r + 1 : ℝ) / c) * (powerSum α s (r + 2) c - powerSum α s (r + 1) c)) c := by
  -- termwise derivative
  have hterm : ∀ k ∈ s, HasDerivAt (fun c => (weight (α k) c) ^ (r + 1))
      (-((r + 1 : ℝ) / c) * ((weight (α k) c) ^ (r + 2) - (weight (α k) c) ^ (r + 1))) c := by
    intro k hk
    have hw := (weight_hasDerivAt hc (hca k hk)).pow (r + 1)
    have hval : ((r + 1 : ℕ) : ℝ) * (weight (α k) c) ^ (r + 1 - 1)
          * (-(weight (α k) c) * (weight (α k) c - 1) / c)
        = -((r + 1 : ℝ) / c)
          * ((weight (α k) c) ^ (r + 2) - (weight (α k) c) ^ (r + 1)) := by
      have hpow : (weight (α k) c) ^ (r + 1 - 1) = (weight (α k) c) ^ r := by
        rw [Nat.add_sub_cancel]
      rw [hpow, pow_succ (weight (α k) c) (r + 1), pow_succ (weight (α k) c) r]
      push_cast
      ring
    rw [← hval]; exact hw
  -- assemble the RHS sum as −((r+1)/c)(p_{r+2} − p_{r+1})
  have hrhs : (∑ k ∈ s, -((r + 1 : ℝ) / c)
        * ((weight (α k) c) ^ (r + 2) - (weight (α k) c) ^ (r + 1)))
      = -((r + 1 : ℝ) / c) * (powerSum α s (r + 2) c - powerSum α s (r + 1) c) := by
    unfold powerSum
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [← hrhs]
  have hsum := HasDerivAt.sum hterm
  have hfun : powerSum α s (r + 1) = ∑ k ∈ s, (fun c => (weight (α k) c) ^ (r + 1)) := by
    funext c'; simp only [powerSum, Finset.sum_apply]
  rw [hfun]; exact hsum

/-- The log-time weight `η_k(t) = ½ + ½ coth((t − t_k)/2)` (doc 27 §1). -/
def logWeight (tk t : ℝ) : ℝ := 1 / 2 + (1 / 2) * rcoth ((t - tk) / 2)

/-- **Calogero kernel identity** `η(1 − η) = −¼ csch²((t − t_k)/2)` (doc 27 §1), from
`coth² − 1 = csch²`. -/
theorem logWeight_mul_one_sub {tk t : ℝ} (h : t ≠ tk) :
    logWeight tk t * (1 - logWeight tk t) = -(1 / 4) * (rcsch ((t - tk) / 2)) ^ 2 := by
  have hu : (t - tk) / 2 ≠ 0 := div_ne_zero (sub_ne_zero.mpr h) two_ne_zero
  have hs : Real.sinh ((t - tk) / 2) ≠ 0 := Real.sinh_ne_zero.mpr hu
  have hcothsq : (rcoth ((t - tk) / 2)) ^ 2 - (rcsch ((t - tk) / 2)) ^ 2 = 1 := by
    unfold rcoth rcsch
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq ((t - tk) / 2)]
  unfold logWeight
  linear_combination (-(1 : ℝ) / 4) * hcothsq

/-- **Autonomous logistic flow** `η̇ = η(1 − η)` in log-time (doc 27 §1): the weight flow is
translation-invariant, reducing the outer problem to electrostatics of the log-zeros `{t_k}`. -/
theorem logWeight_hasDerivAt {tk t : ℝ} (h : t ≠ tk) :
    HasDerivAt (logWeight tk) (logWeight tk t * (1 - logWeight tk t)) t := by
  have hu : (t - tk) / 2 ≠ 0 := div_ne_zero (sub_ne_zero.mpr h) two_ne_zero
  have hinner : HasDerivAt (fun t => (t - tk) / 2) (1 / 2 : ℝ) t := by
    simpa using ((hasDerivAt_id t).sub_const tk).div_const 2
  have hcomp : HasDerivAt (fun t => rcoth ((t - tk) / 2))
      (-(rcsch ((t - tk) / 2)) ^ 2 * (1 / 2)) t := by
    simpa [Function.comp] using (rcoth_hasDerivAt hu).comp t hinner
  have hL : HasDerivAt (logWeight tk)
      ((1 / 2) * (-(rcsch ((t - tk) / 2)) ^ 2 * (1 / 2))) t :=
    (hcomp.const_mul (1 / 2 : ℝ)).const_add (1 / 2 : ℝ)
  rw [logWeight_mul_one_sub h]
  convert hL using 1
  ring
