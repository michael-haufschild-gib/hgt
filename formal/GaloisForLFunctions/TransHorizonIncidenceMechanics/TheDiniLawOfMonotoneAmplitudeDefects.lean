import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheDiniLawOfCompletelyMonotoneAmplitudeDefects
import GaloisForLFunctions.RHTower.JointAncestryHalfPlaneExistence

/-!
# The Dini law of monotone amplitude defects

A defect that decreases along the primes is a completely monotone defect up to summable
critical-line mass, so it obeys the Dini law with an intrinsic profile
(`receiverBounded_monotoneDefectPattern_iff`): if `d` is antitone on the primes, `0 ≤ d ≤ 2`,
`d(p) → 0` and `t₀ > 0`, the half-damped weight of `f(p) = (1 − d(p)) cos(t₀ log p)` is paid iff
`∫_0^1 exp(−P_d(ρ)) dρ/ρ < ∞` or `ζ(1/2 + it₀) = 0`, where `P_d(ρ) = Σ_p d(p) p^{−1−ρ}`
(`primeProfile`).

* **One step costs bounded mass** (`sum_abs_step_sub_rpow_le`): for `R ≥ 2` and
  `s = min(½, 1/log R)`, `Σ_p |1_{p<R} − p^{−s}|/p ≤ 12`. Below `R`, `1 − p^{−s} ≤ 3 s log p · p^{−s}`
  because `s log p ≤ 1`; above `R`, `1 ≤ log p / log R`; and `Σ_p log p · p^{−1−s} ≤ 1/s + 1`.
* **Step defects are completely monotone up to summable mass**
  (`summable_abs_stepDefect_sub_cmDefect`): `Σ_k w_k 1_{p<R_k}` and `Σ_k w_k p^{−s_k}` differ by a
  prime sequence of finite mass `Σ_p |·|/p`. A defect antitone along the primes with limit `0` is
  the step defect with `w_k = d(q_k) − d(q_{k+1})`, `R_k = q_k + 1`, `q_k` the `k`-th prime
  (`stepDefect_monotoneSteps`).
* **The intrinsic profile** (`exists_abs_primeProfile_sub_defectProfile_le`):
  `Σ_p g(p) p^{−1−ρ} = Σ_k w_k Σ_p p^{−1−ρ−s_k} = Λ(ρ) + O(1)` by Mertens at the pole, so the two
  Dini densities are comparable.

The amplitude defects left open at half damping are therefore the non-monotone ones.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Steps, shifts and the intrinsic profile -/

/-- The step defect `d(x) = Σ_k w_k 1_{x < R_k}`. -/
def stepDefect (w R : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k, w k * if x < R k then 1 else 0

/-- The shift attached to the `k`-th step: `s_k = min(½, 1/log R_k)`. -/
def stepShift (R : ℕ → ℝ) (k : ℕ) : ℝ := min (1 / 2) (1 / Real.log (R k))

/-- The step-defect pattern `f(p) = (1 − d(p)) cos(t₀ log p)`. -/
def stepPattern (t₀ : ℝ) (w R : ℕ → ℝ) : ℕ →*₀ ℝ :=
  primeValueHom fun p => (1 - stepDefect w R p) * Real.cos (t₀ * Real.log p)

theorem stepPattern_prime (t₀ : ℝ) (w R : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    stepPattern t₀ w R p = (1 - stepDefect w R p) * Real.cos (t₀ * Real.log p) :=
  primeValueHom_prime _ hp

/-- The intrinsic profile `P_d(ρ) = Σ_p d(p) p^{−1−ρ}`. -/
def primeProfile (d : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, d p * ((p : ℕ) : ℝ) ^ (-(1 + ρ))

variable {w R : ℕ → ℝ}

theorem admissibleDefect_stepShift (hw : ∀ k, 0 ≤ w k) (hws : Summable w) (hR : ∀ k, 2 ≤ R k) :
    AdmissibleDefect w (stepShift R) where
  nonneg := hw
  summable := hws
  pos k := lt_min (by norm_num) (one_div_pos.mpr (Real.log_pos (by linarith [hR k])))
  le_half _ := min_le_left _ _

theorem summable_step (hw : ∀ k, 0 ≤ w k) (hws : Summable w) (x : ℝ) :
    Summable fun k => w k * if x < R k then (1 : ℝ) else 0 :=
  hws.of_nonneg_of_le (fun k => mul_nonneg (hw k) (by split_ifs <;> norm_num))
    fun k => mul_le_of_le_one_right (hw k) (by split_ifs <;> norm_num)

theorem stepDefect_nonneg (hw : ∀ k, 0 ≤ w k) (x : ℝ) : 0 ≤ stepDefect w R x :=
  tsum_nonneg fun k => mul_nonneg (hw k) (by split_ifs <;> norm_num)

theorem stepDefect_le (hw : ∀ k, 0 ≤ w k) (hws : Summable w) (x : ℝ) :
    stepDefect w R x ≤ ∑' k, w k :=
  (summable_step hw hws x).tsum_le_tsum
    (fun k => mul_le_of_le_one_right (hw k) (by split_ifs <;> norm_num)) hws

theorem abs_stepPattern_le (hw : ∀ k, 0 ≤ w k) (hws : Summable w) (hW : ∑' k, w k ≤ 2)
    (t₀ : ℝ) (n : ℕ) : |stepPattern t₀ w R n| ≤ 1 :=
  abs_patternHom_le_one _ (fun p hp => by
    rw [stepPattern_prime t₀ w R hp, abs_mul]
    have h0 := stepDefect_nonneg (R := R) hw p
    have h2 := stepDefect_le (R := R) hw hws p
    exact mul_le_one₀ (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg _)
      (Real.abs_cos_le_one _)) n

/-! ### One step costs bounded mass -/

/-- `Σ_{p ∈ u} log p · p^{−1−s} ≤ 1/s + 1` for `0 < s ≤ 1`, over the primes of any finite `u`. -/
theorem sum_log_mul_rpow_le (u : Finset ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∑ n ∈ u, (if n.Prime then Real.log n * (n : ℝ) ^ (-(1 + s)) else 0) ≤ 1 / s + 1 := by
  have h := RHTower.sum_log_mul_exp_neg_le (u.subtype Nat.Prime) (s := 1 + s) (by linarith)
    (by linarith)
  rw [show 1 + s - 1 = s by ring] at h
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
  refine (Finset.sum_congr rfl fun p _ => ?_).trans_le h
  rw [Real.rpow_def_of_pos (by exact_mod_cast p.2.pos), mul_comm (Real.log _) (-(1 + s))]

/-- **One step costs bounded mass.** For `R ≥ 2` and `s = min(½, 1/log R)`,
`Σ_{p ∈ u} |1_{p<R} − p^{−s}|/p ≤ 12` over the primes of every finite `u`. -/
theorem sum_abs_step_sub_rpow_le {R : ℝ} (hR : 2 ≤ R) (u : Finset ℕ) :
    ∑ n ∈ u, (if n.Prime then
      |(if (n : ℝ) < R then 1 else 0) - (n : ℝ) ^ (-min (1 / 2) (1 / Real.log R))| / n
        else 0) ≤ 12 := by
  set s := min (1 / 2 : ℝ) (1 / Real.log R) with hs_def
  set L := Real.log R
  have hl2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL : 1 / 2 < L := lt_of_lt_of_le hl2 (Real.log_le_log (by norm_num) hR)
  have hL0 : 0 < L := by linarith
  have hs : 0 < s := lt_min (by norm_num) (one_div_pos.mpr hL0)
  have hs2 : s ≤ 1 / 2 := min_le_left _ _
  have hsL : s * L ≤ 1 :=
    calc s * L ≤ 1 / L * L := mul_le_mul_of_nonneg_right (min_le_right _ _) hL0.le
      _ = 1 := by rw [one_div, inv_mul_cancel₀ hL0.ne']
  have hinvs : 1 / s ≤ 2 + L := by
    rcases min_choice (1 / 2 : ℝ) (1 / L) with h | h
    · rw [← hs_def] at h; rw [h]; norm_num; linarith
    · rw [← hs_def] at h; rw [h, one_div_one_div]; linarith
  have hinvL : 1 / L ≤ 2 := by
    rw [div_le_iff₀ hL0]; linarith
  have hexp3 : (1 : ℝ) / 3 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 1) (lt_trans Real.exp_one_lt_d9 (by norm_num)).le
  -- termwise: `|1_{p<R} − p^{−s}|/p ≤ (3s + 1/log R) log p · p^{−1−s}`
  have hterm : ∀ n ∈ u, (if n.Prime then |(if (n : ℝ) < R then 1 else 0) - (n : ℝ) ^ (-s)| / n
      else 0) ≤ (3 * s + 1 / L) *
        (if n.Prime then Real.log n * (n : ℝ) ^ (-(1 + s)) else 0) := by
    intro n _
    by_cases hn : n.Prime
    · simp only [if_pos hn]
      have hp1 : (1 : ℝ) < n := by exact_mod_cast hn.one_lt
      have hp0 : (0 : ℝ) < n := by linarith
      have hlogp : 0 < Real.log n := Real.log_pos hp1
      have hsplit : (n : ℝ) ^ (-(1 + s)) = (n : ℝ) ^ (-s) / n := by
        rw [show -(1 + s) = -s - 1 by ring, Real.rpow_sub hp0, Real.rpow_one]
      have hA := Real.rpow_pos_of_pos hp0 (-s)
      rw [hsplit]
      by_cases hnR : (n : ℝ) < R
      · -- below the step: `1 − p^{−s} ≤ s log p ≤ 3 s log p · p^{−s}`
        rw [if_pos hnR]
        have hexp : (n : ℝ) ^ (-s) = Real.exp (-(s * Real.log n)) := by
          rw [Real.rpow_def_of_pos hp0]; ring_nf
        have hlogpR : Real.log n ≤ L := Real.log_le_log hp0 hnR.le
        have hx : s * Real.log n ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hlogpR hs.le) hsL
        have h1 : 1 - (n : ℝ) ^ (-s) ≤ s * Real.log n := by
          rw [hexp]; linarith [Real.add_one_le_exp (-(s * Real.log n))]
        have h3 : (1 : ℝ) / 3 ≤ (n : ℝ) ^ (-s) := by
          rw [hexp]; exact hexp3.trans (Real.exp_le_exp.mpr (by linarith))
        have hps1 : (n : ℝ) ^ (-s) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by linarith)
        have hmain : 1 - (n : ℝ) ^ (-s) ≤ 3 * s * Real.log n * (n : ℝ) ^ (-s) := by
          have := mul_nonneg (sub_nonneg.mpr h3) (mul_nonneg hs.le hlogp.le)
          nlinarith
        rw [abs_of_nonneg (by linarith)]
        calc (1 - (n : ℝ) ^ (-s)) / n ≤ 3 * s * Real.log n * (n : ℝ) ^ (-s) / n :=
              div_le_div_of_nonneg_right hmain hp0.le
          _ = 3 * s * (Real.log n * ((n : ℝ) ^ (-s) / n)) := by ring
          _ ≤ (3 * s + 1 / L) * (Real.log n * ((n : ℝ) ^ (-s) / n)) :=
              mul_le_mul_of_nonneg_right (by linarith [one_div_pos.mpr hL0]) (by positivity)
      · -- above the step: `1 ≤ log p / log R`
        rw [if_neg hnR, zero_sub, abs_neg, abs_of_pos hA]
        have hle : L ≤ Real.log n := Real.log_le_log (by linarith) (not_lt.mp hnR)
        have h1 : 1 ≤ 1 / L * Real.log n := by
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hL0, one_mul]; exact hle
        calc (n : ℝ) ^ (-s) / n = 1 * ((n : ℝ) ^ (-s) / n) := (one_mul _).symm
          _ ≤ (1 / L * Real.log n) * ((n : ℝ) ^ (-s) / n) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = 1 / L * (Real.log n * ((n : ℝ) ^ (-s) / n)) := by ring
          _ ≤ (3 * s + 1 / L) * (Real.log n * ((n : ℝ) ^ (-s) / n)) :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    · simp [hn]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hsum := sum_log_mul_rpow_le u hs (by linarith)
  have hcoef : 0 ≤ 3 * s + 1 / L := by positivity
  calc (3 * s + 1 / L) * ∑ n ∈ u, (if n.Prime then Real.log n * (n : ℝ) ^ (-(1 + s)) else 0)
      ≤ (3 * s + 1 / L) * (1 / s + 1) := mul_le_mul_of_nonneg_left hsum hcoef
    _ = 3 + 3 * s + 1 / L * (1 / s) + 1 / L := by
        have hs1 : s * (1 / s) = 1 := by rw [mul_one_div, div_self hs.ne']
        linear_combination 3 * hs1
    _ ≤ 12 := by
        have := mul_le_mul_of_nonneg_left hinvs (one_div_pos.mpr hL0).le
        have hLL : 1 / L * L = 1 := by rw [one_div, inv_mul_cancel₀ hL0.ne']
        nlinarith

/-! ### Step defects are completely monotone up to summable mass -/

/-- The termwise majorant `Σ_k w_k |1_{n<R_k} − n^{−s_k}|/n` on primes. -/
theorem summable_stepMajorant (hw : ∀ k, 0 ≤ w k) (hws : Summable w) (hR : ∀ k, 2 ≤ R k) :
    Summable fun n : ℕ => ∑' k, w k * (if n.Prime then
      |(if (n : ℝ) < R k then 1 else 0) - (n : ℝ) ^ (-stepShift R k)| / n else 0) := by
  have hnn : ∀ n k : ℕ, 0 ≤ (if n.Prime then
      |(if (n : ℝ) < R k then 1 else 0) - (n : ℝ) ^ (-stepShift R k)| / n else (0 : ℝ)) :=
    fun n k => by split_ifs <;> positivity
  have hle : ∀ n k : ℕ, (if n.Prime then
      |(if (n : ℝ) < R k then 1 else 0) - (n : ℝ) ^ (-stepShift R k)| / n else (0 : ℝ)) ≤ 12 := by
    intro n k
    have := sum_abs_step_sub_rpow_le (hR k) {n}
    rwa [Finset.sum_singleton] at this
  have hsk : ∀ n : ℕ, Summable fun k => w k * (if n.Prime then
      |(if (n : ℝ) < R k then 1 else 0) - (n : ℝ) ^ (-stepShift R k)| / n else 0) :=
    fun n => (hws.mul_right 12).of_nonneg_of_le (fun k => mul_nonneg (hw k) (hnn n k))
      fun k => mul_le_mul_of_nonneg_left (hle n k) (hw k)
  refine summable_of_sum_le (c := ∑' k, w k * 12) (fun n => tsum_nonneg fun k =>
    mul_nonneg (hw k) (hnn n k)) fun u => ?_
  rw [← Summable.tsum_finsetSum fun n _ => hsk n]
  refine ((summable_sum fun n _ => hsk n).tsum_le_tsum (fun k => ?_) (hws.mul_right 12))
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_abs_step_sub_rpow_le (hR k) u) (hw k)

/-- `|d(n) − g(n)| ≤ Σ_k w_k |1_{n<R_k} − n^{−s_k}|` for the step defect `d` and its
completely monotone companion `g = Σ_k w_k n^{−s_k}`. -/
theorem abs_stepDefect_sub_cmDefect_le (hw : ∀ k, 0 ≤ w k) (hws : Summable w)
    (hR : ∀ k, 2 ≤ R k) {x : ℝ} (hx : 1 ≤ x) :
    |stepDefect w R x - cmDefect w (stepShift R) x| ≤
      ∑' k, w k * |(if x < R k then 1 else 0) - x ^ (-stepShift R k)| := by
  have hd := admissibleDefect_stepShift hw hws hR
  have hs1 := summable_step (R := R) hw hws x
  have hs2 := hd.summable_mul_rpow hx
  have habs : Summable fun k => w k * |(if x < R k then 1 else 0) - x ^ (-stepShift R k)| :=
    (hws.mul_right 2).of_nonneg_of_le (fun k => mul_nonneg (hw k) (abs_nonneg _)) fun k => by
      refine mul_le_mul_of_nonneg_left ?_ (hw k)
      have h0 := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) (-stepShift R k)
      have h1 := Real.rpow_le_one_of_one_le_of_nonpos (z := -stepShift R k) hx
        (by linarith [hd.pos k])
      rw [abs_le]; constructor <;> split_ifs <;> linarith
  rw [stepDefect, cmDefect, ← hs1.tsum_sub hs2, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun k => ?_))
  · exact habs.congr fun k => by rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (hw k)]
  · rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (hw k)]

/-- **Step defects are completely monotone up to summable mass**:
`Σ_p |d(p) − g(p)|/p < ∞`. -/
theorem summable_abs_stepDefect_sub_cmDefect (hw : ∀ k, 0 ≤ w k) (hws : Summable w)
    (hR : ∀ k, 2 ≤ R k) :
    Summable fun n : ℕ => if n.Prime then
      |stepDefect w R n - cmDefect w (stepShift R) n| / n else 0 := by
  refine (summable_stepMajorant hw hws hR).of_nonneg_of_le
    (fun n => by split_ifs <;> positivity) fun n => ?_
  split_ifs with hn
  · have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn.one_lt.le
    have hn0 : (0 : ℝ) < n := by linarith
    rw [div_le_iff₀ hn0, ← tsum_mul_right]
    refine (abs_stepDefect_sub_cmDefect_le hw hws hR hx).trans (le_of_eq (tsum_congr fun k => ?_))
    rw [mul_assoc, div_mul_cancel₀ _ hn0.ne']
  · simp

/-! ### The Dini law for step defects -/

theorem summable_stepPattern_sub_defectPattern (hw : ∀ k, 0 ≤ w k) (hws : Summable w)
    (hR : ∀ k, 2 ≤ R k) (t₀ : ℝ) :
    Summable (fun p : ℕ => if p.Prime then
      |stepPattern t₀ w R p - defectPattern 1 t₀ w (stepShift R) p| *
        (p : ℝ) ^ (-(1 / 2 + 1 / 2 : ℝ)) else 0) := by
  refine (summable_abs_stepDefect_sub_cmDefect hw hws hR).of_nonneg_of_le
    (fun p => by split_ifs <;> positivity) fun p => ?_
  split_ifs with hp
  · rw [stepPattern_prime t₀ w R hp, defectPattern_prime 1 t₀ hp,
      show (-(1 / 2 + 1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one, ← div_eq_mul_inv,
      one_mul, ← sub_mul, abs_mul,
      show 1 - stepDefect w R (p : ℝ) - (1 - cmDefect w (stepShift R) (p : ℝ)) =
        -(stepDefect w R p - cmDefect w (stepShift R) p) by ring, abs_neg]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)) (Nat.cast_nonneg _)
  · exact le_rfl

/-- **The Dini law for step defects**, with the explicit profile of the shifts
`s_k = min(½, 1/log R_k)`. -/
theorem receiverBounded_stepPattern_iff (hw : ∀ k, 0 ≤ w k) (hws : Summable w)
    (hR : ∀ k, 2 ≤ R k) (hW : ∑' k, w k ≤ 2) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ReceiverBounded (dampedSignWeight (stepPattern t₀ w R) (1 / 2)) ↔
      IntegrableOn (diniDensity 1 w (stepShift R)) (Ioc 0 1) ∨
        riemannZeta (1 / 2 + t₀ * I) = 0 := by
  have hd := admissibleDefect_stepShift hw hws hR
  have hcW : (1 : ℝ) * ∑' k, w k ≤ 2 := by rwa [one_mul]
  rw [receiverBounded_iff_of_summable_prime_diff
    (fun p _ => abs_defectPattern_le hd zero_le_one hcW t₀ p)
    (fun p _ => abs_stepPattern_le hw hws hW t₀ p) (by norm_num)
    (summable_stepPattern_sub_defectPattern hw hws hR t₀)]
  exact receiverBounded_defectWeight_iff hd zero_le_one hcW ht₀

/-! ### The intrinsic profile -/

/-- **Mertens at the pole on `(1, 5/2]`**: `|Σ_p p^{−1−x} − log(1/x)| ≤ C` for `0 < x ≤ 3/2`. -/
theorem exists_abs_tsum_primes_rpow_sub_log_le :
    ∃ C : ℝ, ∀ x : ℝ, 0 < x → x ≤ 3 / 2 →
      |∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + x)) - Real.log x⁻¹| ≤ C := by
  refine ⟨2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) + Real.log (3 / 2) +
    ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) + Real.log 2, fun x hx hx3 => ?_⟩
  have hS₂ : 0 ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
    tsum_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hS₃ : 0 ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) :=
    tsum_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hl32 : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases lt_or_ge x (1 / 2) with hxs | hxl
  · have h := abs_tsum_primes_rpow_sub_log_le (w := 1 + x) (by linarith) (by linarith)
    rw [show 1 + x - 1 = x by ring, one_div] at h
    linarith
  · -- away from the pole both terms are bounded
    have hsum : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(1 + x)) :=
      Nat.Primes.summable_rpow.mpr (by linarith)
    have h0 : 0 ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + x)) :=
      tsum_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h1 : ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + x)) ≤
        ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) :=
      hsum.tsum_le_tsum (fun p => Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast p.2.one_lt.le) (by linarith))
        (Nat.Primes.summable_rpow.mpr (by norm_num))
    have hlog : |Real.log x⁻¹| ≤ Real.log 2 := by
      rw [Real.log_inv, abs_neg, abs_le]
      constructor
      · have := Real.log_le_log (by norm_num) hxl
        rw [one_div, Real.log_inv] at this; linarith
      · have := Real.log_le_log hx (show x ≤ 2 by linarith)
        linarith
    obtain ⟨hl1, hl2'⟩ := abs_le.mp hlog
    rw [abs_le]
    constructor <;> linarith

/-- `Σ_p g(p) p^{−1−ρ} = Σ_k w_k Σ_p p^{−1−ρ−s_k}` for a completely monotone defect `g`. -/
theorem primeProfile_cmDefect {w s : ℕ → ℝ} (hd : AdmissibleDefect w s) {ρ : ℝ} (hρ : 0 < ρ) :
    primeProfile (fun n : ℕ => cmDefect w s n) ρ =
      ∑' k, w k * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + (s k + ρ))) := by
  set f : ℕ → Nat.Primes → ℝ := fun k p => w k * ((p : ℕ) : ℝ) ^ (-(1 + (s k + ρ))) with hf
  have hQ : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(1 + ρ)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hfk : ∀ k, Summable (f k) := fun k =>
    (Nat.Primes.summable_rpow.mpr (by linarith [hd.pos k])).mul_left _
  have hfle : ∀ k, ∑' p, f k p ≤ w k * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + ρ)) := by
    intro k
    rw [hf]
    dsimp only
    rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ((Nat.Primes.summable_rpow.mpr
      (by linarith [hd.pos k])).tsum_le_tsum (fun p => Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast p.2.one_lt.le) (by linarith [hd.pos k])) hQ) (hd.nonneg k)
  have hf0 : 0 ≤ Function.uncurry f := fun kp =>
    mul_nonneg (hd.nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hunc : Summable (Function.uncurry f) :=
    (summable_prod_of_nonneg hf0).mpr ⟨hfk, (hd.summable.mul_right _).of_nonneg_of_le
      (fun k => tsum_nonneg fun p => hf0 (k, p)) hfle⟩
  have hp : ∀ p : Nat.Primes, cmDefect w s p * ((p : ℕ) : ℝ) ^ (-(1 + ρ)) = ∑' k, f k p := by
    intro p
    have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    rw [cmDefect, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    rw [hf, mul_assoc, ← Real.rpow_add hp0, show -s k + -(1 + ρ) = -(1 + (s k + ρ)) by ring]
  simp only [primeProfile]
  rw [tsum_congr hp, hunc.tsum_comm]
  exact tsum_congr fun k => by rw [hf]; exact tsum_mul_left

/-- **The intrinsic profile of a completely monotone defect** is its Dini profile up to `O(1)`:
`|Σ_p g(p) p^{−1−ρ} − Λ(ρ)| ≤ C` on `(0, 1]`. -/
theorem exists_abs_primeProfile_cmDefect_sub_le {w s : ℕ → ℝ} (hd : AdmissibleDefect w s) :
    ∃ C : ℝ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      |primeProfile (fun n : ℕ => cmDefect w s n) ρ - defectProfile w s ρ| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_tsum_primes_rpow_sub_log_le
  refine ⟨(∑' k, w k) * C, fun ρ hρ hρ1 => ?_⟩
  have hx : ∀ k, 0 < s k + ρ := fun k => by linarith [hd.pos k]
  have hx3 : ∀ k, s k + ρ ≤ 3 / 2 := fun k => by linarith [hd.le_half k]
  have hS1 : Summable fun k => w k * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + (s k + ρ))) := by
    refine (hd.summable.mul_right (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + ρ)))).of_nonneg_of_le
      (fun k => mul_nonneg (hd.nonneg k) (tsum_nonneg fun p =>
        Real.rpow_nonneg (Nat.cast_nonneg _) _)) fun k => mul_le_mul_of_nonneg_left
        ((Nat.Primes.summable_rpow.mpr (by linarith [hd.pos k])).tsum_le_tsum
          (fun p => Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le)
            (by linarith [hd.pos k])) (Nat.Primes.summable_rpow.mpr (by linarith)))
        (hd.nonneg k)
  have hle : ∀ k, ‖w k * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + (s k + ρ))) -
      w k * Real.log (s k + ρ)⁻¹‖ ≤ w k * C := fun k => by
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (hd.nonneg k)]
    exact mul_le_mul_of_nonneg_left (hC _ (hx k) (hx3 k)) (hd.nonneg k)
  have hnorm : Summable fun k => ‖w k * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + (s k + ρ))) -
      w k * Real.log (s k + ρ)⁻¹‖ :=
    (hd.summable.mul_right C).of_nonneg_of_le (fun k => norm_nonneg _) hle
  rw [primeProfile_cmDefect hd hρ, defectProfile, ← hS1.tsum_sub (summable_defectProfile hd hρ),
    ← Real.norm_eq_abs, ← tsum_mul_right]
  exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hle (hd.summable.mul_right C))

/-- Two defects within summable mass `Σ_p |d − d'|/p` have intrinsic profiles within that mass. -/
theorem abs_primeProfile_sub_le {d d' : ℕ → ℝ} (hd : ∀ p : ℕ, p.Prime → |d p| ≤ 2)
    (hd' : ∀ p : ℕ, p.Prime → |d' p| ≤ 2)
    (hsum : Summable fun n : ℕ => if n.Prime then |d n - d' n| / n else 0) {ρ : ℝ} (hρ : 0 < ρ) :
    |primeProfile d ρ - primeProfile d' ρ| ≤
      ∑' n : ℕ, (if n.Prime then |d n - d' n| / n else 0) := by
  have hQ : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(1 + ρ)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hs : ∀ e : ℕ → ℝ, (∀ p : ℕ, p.Prime → |e p| ≤ 2) →
      Summable fun p : Nat.Primes => e p * ((p : ℕ) : ℝ) ^ (-(1 + ρ)) := fun e he =>
    (hQ.mul_left 2).of_norm_bounded fun p => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact mul_le_mul_of_nonneg_right (he p p.2) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hP : Summable fun p : Nat.Primes => |d p - d' p| / ((p : ℕ) : ℝ) := by
    refine (hsum.comp_injective Nat.Primes.coe_nat_injective).congr fun p => ?_
    simp only [Function.comp_apply, if_pos p.2]
  have hle : ∀ p : Nat.Primes, ‖(d p - d' p) * ((p : ℕ) : ℝ) ^ (-(1 + ρ))‖ ≤
      |d p - d' p| / ((p : ℕ) : ℝ) := fun p => by
    have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.one_lt.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      div_eq_mul_inv, ← Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))
      (abs_nonneg _)
  have hT0 : ∀ n : ℕ, 0 ≤ (if n.Prime then |d n - d' n| / n else (0 : ℝ)) := fun n => by
    split_ifs <;> positivity
  have hcomp := tsum_comp_le_tsum_of_inj hsum hT0 Nat.Primes.coe_nat_injective
  have hcomp' : ∑' p : Nat.Primes, |d p - d' p| / ((p : ℕ) : ℝ) =
      ∑' p : Nat.Primes, (fun n : ℕ => if n.Prime then |d n - d' n| / n else (0 : ℝ)) p :=
    tsum_congr fun p => by simp only [if_pos p.2]
  rw [primeProfile, primeProfile, ← (hs d hd).tsum_sub (hs d' hd'), ← Real.norm_eq_abs]
  simp_rw [← sub_mul]
  refine (norm_tsum_le_tsum_norm (hP.of_nonneg_of_le (fun p => norm_nonneg _) hle)).trans ?_
  refine (Summable.tsum_le_tsum hle (hP.of_nonneg_of_le (fun p => norm_nonneg _) hle) hP).trans ?_
  rw [hcomp']
  exact hcomp

/-- **Comparable profiles give the same Dini integrability.** If `|P − Λ| ≤ C` on `(0, 1]` and `P`
is antitone there, `e^{−P(ρ)}/ρ` and `e^{−Λ(ρ)}/ρ` are integrable on `(0, 1]` together. -/
theorem integrableOn_exp_neg_div_iff {w s : ℕ → ℝ} (hd : AdmissibleDefect w s) {P : ℝ → ℝ} {C : ℝ}
    (hP : AntitoneOn P (Ioc 0 1))
    (hC : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → |P ρ - defectProfile w s ρ| ≤ C) :
    IntegrableOn (fun ρ => Real.exp (-P ρ) / ρ) (Ioc 0 1) ↔
      IntegrableOn (diniDensity 1 w s) (Ioc 0 1) := by
  have hmeasP : AEStronglyMeasurable (fun ρ => Real.exp (-P ρ) / ρ) (volume.restrict (Ioc 0 1)) := by
    have hmono : MonotoneOn (fun ρ => Real.exp (-P ρ)) (Ioc 0 1) := fun x hx y hy hxy =>
      Real.exp_le_exp.mpr (by linarith [hP hx hy hxy])
    exact ((aemeasurable_restrict_of_monotoneOn measurableSet_Ioc hmono).div
      aemeasurable_id).aestronglyMeasurable
  have hmeasD : AEStronglyMeasurable (diniDensity 1 w s) (volume.restrict (Ioc 0 1)) :=
    ((aemeasurable_diniDensity hd zero_le_one).mono_measure
      (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)).aestronglyMeasurable
  have hpt : ∀ ρ ∈ Ioc (0 : ℝ) 1, Real.exp (-P ρ) / ρ ≤ Real.exp C * diniDensity 1 w s ρ ∧
      diniDensity 1 w s ρ ≤ Real.exp C * (Real.exp (-P ρ) / ρ) := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := abs_le.mp (hC ρ hρ.1 hρ.2)
    rw [diniDensity, one_mul, mul_div_assoc', mul_div_assoc', ← Real.exp_add, ← Real.exp_add]
    exact ⟨div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hρ.1.le,
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hρ.1.le⟩
  constructor
  · intro hI
    refine Integrable.mono' (hI.const_mul (Real.exp C)) hmeasD ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ρ hρ
    rw [Real.norm_eq_abs, abs_of_nonneg (diniDensity_nonneg 1 hρ.1.le)]
    exact (hpt ρ hρ).2
  · intro hI
    refine Integrable.mono' (hI.const_mul (Real.exp C)) hmeasP ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ρ hρ
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le hρ.1.le)]
    exact (hpt ρ hρ).1

/-- The intrinsic profile of a nonnegative defect is antitone in `ρ > 0`. -/
theorem primeProfile_antitoneOn {d : ℕ → ℝ} (hd0 : ∀ p : ℕ, p.Prime → 0 ≤ d p)
    (hd2 : ∀ p : ℕ, p.Prime → d p ≤ 2) : AntitoneOn (primeProfile d) (Ioc 0 1) := by
  intro x hx y hy hxy
  have hs : ∀ z : ℝ, 0 < z → Summable fun p : Nat.Primes => d p * ((p : ℕ) : ℝ) ^ (-(1 + z)) :=
    fun z hz => ((Nat.Primes.summable_rpow.mpr (by linarith)).mul_left 2).of_nonneg_of_le
      (fun p => mul_nonneg (hd0 p p.2) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      fun p => mul_le_mul_of_nonneg_right (hd2 p p.2) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact (hs y hy.1).tsum_le_tsum (fun p => mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) (by linarith))
    (hd0 p p.2)) (hs x hx.1)

/-- **The Dini law for step defects with the intrinsic profile.** -/
theorem receiverBounded_stepPattern_iff_primeProfile (hw : ∀ k, 0 ≤ w k) (hws : Summable w)
    (hR : ∀ k, 2 ≤ R k) (hW : ∑' k, w k ≤ 2) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ReceiverBounded (dampedSignWeight (stepPattern t₀ w R) (1 / 2)) ↔
      IntegrableOn (fun ρ => Real.exp (-primeProfile (fun n : ℕ => stepDefect w R n) ρ) / ρ)
        (Ioc 0 1) ∨
        riemannZeta (1 / 2 + t₀ * I) = 0 := by
  have hd := admissibleDefect_stepShift hw hws hR
  obtain ⟨C, hC⟩ := exists_abs_primeProfile_cmDefect_sub_le hd
  have hstep0 := stepDefect_nonneg (R := R) hw
  have hstep2 : ∀ x : ℝ, stepDefect w R x ≤ 2 := fun x => (stepDefect_le hw hws x).trans hW
  have hcm : ∀ p : ℕ, p.Prime → |cmDefect w (stepShift R) p| ≤ 2 := fun p hp => by
    have h0 := cmDefect_nonneg hd (x := p) (by exact_mod_cast hp.one_lt.le)
    have h1 := cmDefect_le hd (x := p) (by exact_mod_cast hp.one_lt.le)
    rw [abs_of_nonneg h0]; linarith
  have hM := fun ρ (hρ : 0 < ρ) => abs_primeProfile_sub_le (ρ := ρ)
    (d := fun n => stepDefect w R n) (d' := fun n => cmDefect w (stepShift R) n)
    (fun p _ => (abs_of_nonneg (hstep0 _)).trans_le (hstep2 _)) hcm
    (summable_abs_stepDefect_sub_cmDefect hw hws hR) hρ
  rw [receiverBounded_stepPattern_iff hw hws hR hW ht₀,
    integrableOn_exp_neg_div_iff hd (C := ∑' n : ℕ, (if n.Prime then
      |stepDefect w R n - cmDefect w (stepShift R) n| / n else 0) + C)
      (primeProfile_antitoneOn (d := fun n : ℕ => stepDefect w R n) (fun p _ => hstep0 _)
        fun p _ => hstep2 _)
      fun ρ hρ hρ1 => ?_]
  have h1 := hM ρ hρ
  have h2 := hC ρ hρ hρ1
  have := abs_sub_le (primeProfile (fun n : ℕ => stepDefect w R n) ρ)
    (primeProfile (fun n : ℕ => cmDefect w (stepShift R) n) ρ) (defectProfile w (stepShift R) ρ)
  exact this.trans (add_le_add h1 h2)

/-! ### Monotone defects -/

/-- The `k`-th prime. -/
abbrev nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/-- The steps of a defect along the primes: `w_k = d(q_k) − d(q_{k+1})`. -/
def monotoneSteps (d : ℕ → ℝ) (k : ℕ) : ℝ := d (nthPrime k) - d (nthPrime (k + 1))

/-- The step thresholds `R_k = q_k + 1`. -/
def monotoneThresholds (k : ℕ) : ℝ := (nthPrime k : ℝ) + 1

theorem nthPrime_prime (k : ℕ) : (nthPrime k).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k

theorem nthPrime_strictMono : StrictMono nthPrime := Nat.nth_strictMono Nat.infinite_setOf_prime

/-- The tail sums of the steps telescope: `Σ_{j} w_{j+m} = d(q_m)` when `d → 0` along the
primes. -/
theorem hasSum_monotoneSteps_add {d : ℕ → ℝ}
    (hanti : ∀ p q : ℕ, p.Prime → q.Prime → p ≤ q → d q ≤ d p)
    (hlim : ∀ η > 0, ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p → |d p| < η) (m : ℕ) :
    HasSum (fun j => monotoneSteps d (j + m)) (d (nthPrime m)) := by
  have hnn : ∀ j, 0 ≤ monotoneSteps d (j + m) := fun j => sub_nonneg.mpr
    (hanti _ _ (nthPrime_prime _) (nthPrime_prime _) (nthPrime_strictMono (by omega)).le)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have htel : ∀ N, ∑ j ∈ Finset.range N, monotoneSteps d (j + m) =
      d (nthPrime m) - d (nthPrime (m + N)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, monotoneSteps, show N + m = m + N by ring,
        show m + N + 1 = m + (N + 1) by ring]
      ring
  simp_rw [htel]
  have hq : Tendsto (fun N => d (nthPrime (m + N))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N₀, hN₀⟩ := hlim η hη
    refine ⟨N₀, fun N hN => ?_⟩
    rw [Real.dist_eq, sub_zero]
    refine hN₀ _ (nthPrime_prime _) (le_trans hN ?_)
    exact (nthPrime_strictMono.id_le (m + N)).trans' (Nat.le_add_left N m)
  simpa using hq.const_sub (d (nthPrime m))

/-- **A defect antitone along the primes is a step defect.** -/
theorem stepDefect_monotoneSteps {d : ℕ → ℝ}
    (hanti : ∀ p q : ℕ, p.Prime → q.Prime → p ≤ q → d q ≤ d p)
    (hlim : ∀ η > 0, ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p → |d p| < η) {p : ℕ} (hp : p.Prime) :
    stepDefect (monotoneSteps d) monotoneThresholds p = d p := by
  set m := Nat.count Nat.Prime p
  have hqm : nthPrime m = p := Nat.nth_count hp
  have hind : ∀ k, ((p : ℝ) < monotoneThresholds k) ↔ m ≤ k := by
    intro k
    rw [monotoneThresholds, ← hqm, ← nthPrime_strictMono.le_iff_le]
    constructor
    · intro h
      have h' : nthPrime m < nthPrime k + 1 := by exact_mod_cast h
      omega
    · intro h
      have h' : nthPrime m < nthPrime k + 1 := by omega
      exact_mod_cast h'
  have hS := hasSum_monotoneSteps_add hanti hlim m
  have hsum : Summable fun k => monotoneSteps d k * if (p : ℝ) < monotoneThresholds k then 1 else 0 :=
    by
      refine (summable_nat_add_iff m).mp ?_
      exact hS.summable.congr fun j => by
        simp only [if_pos ((hind (j + m)).mpr (by omega)), mul_one]
  have hS' : HasSum (fun j => monotoneSteps d (j + m)) (d p) := by rw [← hqm]; exact hS
  rw [stepDefect, ← hsum.sum_add_tsum_nat_add m, Finset.sum_eq_zero fun k hk => by
    rw [if_neg (fun h => absurd ((hind k).mp h) (by simp at hk; omega)), mul_zero], zero_add,
    ← hS'.tsum_eq]
  exact tsum_congr fun j => by rw [if_pos ((hind _).mpr (by omega)), mul_one]

/-- The monotone-defect pattern `f(p) = (1 − d(p)) cos(t₀ log p)`. -/
def monotoneDefectPattern (t₀ : ℝ) (d : ℕ → ℝ) : ℕ →*₀ ℝ :=
  primeValueHom fun p => (1 - d p) * Real.cos (t₀ * Real.log p)

theorem monotoneDefectPattern_prime (t₀ : ℝ) (d : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    monotoneDefectPattern t₀ d p = (1 - d p) * Real.cos (t₀ * Real.log p) :=
  primeValueHom_prime _ hp

/-- **The Dini law of monotone amplitude defects.** Let `d` be antitone along the primes with
`0 ≤ d ≤ 2` and `d(p) → 0`, and `t₀ > 0`. The half-damped weight of
`f(p) = (1 − d(p)) cos(t₀ log p)` is paid iff `∫_0^1 exp(−Σ_p d(p) p^{−1−ρ}) dρ/ρ < ∞` or
`ζ(1/2 + it₀) = 0`. -/
theorem receiverBounded_monotoneDefectPattern_iff {d : ℕ → ℝ}
    (hd0 : ∀ p : ℕ, p.Prime → 0 ≤ d p) (hd2 : ∀ p : ℕ, p.Prime → d p ≤ 2)
    (hanti : ∀ p q : ℕ, p.Prime → q.Prime → p ≤ q → d q ≤ d p)
    (hlim : ∀ η > 0, ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p → |d p| < η) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ReceiverBounded (dampedSignWeight (monotoneDefectPattern t₀ d) (1 / 2)) ↔
      IntegrableOn (fun ρ => Real.exp (-primeProfile d ρ) / ρ) (Ioc 0 1) ∨
        riemannZeta (1 / 2 + t₀ * I) = 0 := by
  have hw : ∀ k, 0 ≤ monotoneSteps d k := fun k => sub_nonneg.mpr
    (hanti _ _ (nthPrime_prime _) (nthPrime_prime _) (nthPrime_strictMono (Nat.lt_succ_self k)).le)
  have hS := hasSum_monotoneSteps_add hanti hlim 0
  simp only [add_zero] at hS
  have hws := hS.summable
  have hR : ∀ k, 2 ≤ monotoneThresholds k := fun k => by
    have := (nthPrime_prime k).two_le
    rw [monotoneThresholds]
    have : (2 : ℝ) ≤ nthPrime k := by exact_mod_cast this
    linarith
  have hW : ∑' k, monotoneSteps d k ≤ 2 := by rw [hS.tsum_eq]; exact hd2 _ (nthPrime_prime 0)
  have hval := fun p (hp : Nat.Prime p) => stepDefect_monotoneSteps hanti hlim hp
  have hf : ∀ p : ℕ, p.Prime → |stepPattern t₀ (monotoneSteps d) monotoneThresholds p| ≤ 1 :=
    fun p _ => abs_stepPattern_le hw hws hW t₀ p
  have hf' : ∀ p : ℕ, p.Prime → |monotoneDefectPattern t₀ d p| ≤ 1 := fun p hp => by
    rw [monotoneDefectPattern_prime t₀ d hp, abs_mul]
    exact mul_le_one₀ (abs_le.mpr ⟨by linarith [hd2 p hp], by linarith [hd0 p hp]⟩)
      (abs_nonneg _) (Real.abs_cos_le_one _)
  have hdiff : Summable (fun p : ℕ => if p.Prime then
      |monotoneDefectPattern t₀ d p - stepPattern t₀ (monotoneSteps d) monotoneThresholds p| *
        (p : ℝ) ^ (-(1 / 2 + 1 / 2 : ℝ)) else 0) := by
    have hzero : (fun p : ℕ => if p.Prime then
        |monotoneDefectPattern t₀ d p - stepPattern t₀ (monotoneSteps d) monotoneThresholds p| *
          (p : ℝ) ^ (-(1 / 2 + 1 / 2 : ℝ)) else 0) = fun _ => 0 := by
      funext p
      split_ifs with hp
      · rw [monotoneDefectPattern_prime t₀ d hp, stepPattern_prime t₀ _ _ hp, hval p hp, sub_self,
          abs_zero, zero_mul]
      · rfl
    rw [hzero]
    exact summable_zero
  have hprof : primeProfile (fun n : ℕ => stepDefect (monotoneSteps d) monotoneThresholds n) =
      primeProfile d := by
    funext ρ
    simp only [primeProfile]
    exact tsum_congr fun p => by rw [hval _ p.2]
  rw [receiverBounded_iff_of_summable_prime_diff hf hf' (by norm_num) hdiff,
    receiverBounded_stepPattern_iff_primeProfile hw hws hR hW ht₀, hprof]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
