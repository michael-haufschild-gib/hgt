import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-!
# The elliptic-gamma logarithmic-derivative kernel

The logarithmic derivative of the standard double-product elliptic gamma function is assembled
from the two rational atoms in `ellipticGammaLogSummand`.  This file proves the exact finite
telescoping identities under multiplication of the elliptic variable by either nome.  The only
uncancelled terms are the expected one-dimensional theta boundary and two terminal tails.  These
identities are the algebraic core of the two elliptic-gamma increment equations; subsequent modules
will prove convergence and send the terminal tails to zero.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- The logarithmic-derivative atom `t/(1-t)`. -/
def ellipticGammaLogAtom (t : ℂ) : ℂ := t / (1 - t)

/-- The numerator-side argument in the elliptic-gamma double product. -/
def ellipticGammaForwardArgument (p q x : ℂ) (j k : ℕ) : ℂ :=
  p ^ (j + 1) * q ^ (k + 1) / x

/-- The denominator-side argument in the elliptic-gamma double product. -/
def ellipticGammaBackwardArgument (p q x : ℂ) (j k : ℕ) : ℂ :=
  p ^ j * q ^ k * x

/-- One logarithmic-derivative summand of the elliptic-gamma double product. -/
def ellipticGammaLogSummand (p q x : ℂ) (j k : ℕ) : ℂ :=
  ellipticGammaLogAtom (ellipticGammaForwardArgument p q x j k) +
    ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x j k)

theorem ellipticGammaForwardArgument_mul_p_zero
    {p q x : ℂ} (hp : p ≠ 0) (hx : x ≠ 0) (k : ℕ) :
    ellipticGammaForwardArgument p q (p * x) 0 k = q ^ (k + 1) / x := by
  simp only [ellipticGammaForwardArgument, zero_add, pow_one]
  field_simp [hp, hx]

theorem ellipticGammaForwardArgument_mul_p_succ
    {p q x : ℂ} (hp : p ≠ 0) (hx : x ≠ 0) (j k : ℕ) :
    ellipticGammaForwardArgument p q (p * x) (j + 1) k =
      ellipticGammaForwardArgument p q x j k := by
  simp only [ellipticGammaForwardArgument]
  field_simp
  ring

theorem ellipticGammaBackwardArgument_mul_p
    (p q x : ℂ) (j k : ℕ) :
    ellipticGammaBackwardArgument p q (p * x) j k =
      ellipticGammaBackwardArgument p q x (j + 1) k := by
  simp [ellipticGammaBackwardArgument, pow_succ]
  ring

theorem ellipticGammaLogSummand_mul_p_zero
    {p q x : ℂ} (hp : p ≠ 0) (hx : x ≠ 0) (k : ℕ) :
    ellipticGammaLogSummand p q (p * x) 0 k =
      ellipticGammaLogAtom (q ^ (k + 1) / x) +
        ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x 1 k) := by
  simp [ellipticGammaLogSummand,
    ellipticGammaForwardArgument_mul_p_zero hp hx,
    ellipticGammaBackwardArgument_mul_p]

theorem ellipticGammaLogSummand_mul_p_succ
    {p q x : ℂ} (hp : p ≠ 0) (hx : x ≠ 0) (j k : ℕ) :
    ellipticGammaLogSummand p q (p * x) (j + 1) k =
      ellipticGammaLogAtom (ellipticGammaForwardArgument p q x j k) +
        ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x (j + 2) k) := by
  rw [ellipticGammaLogSummand,
    ellipticGammaForwardArgument_mul_p_succ hp hx,
    ellipticGammaBackwardArgument_mul_p]

/-- Exact finite telescoping in the first nome direction. -/
theorem ellipticGammaLogSummand_sum_mul_p
    {p q x : ℂ} (hp : p ≠ 0) (hx : x ≠ 0) (N k : ℕ) :
    (∑ j ∈ Finset.range (N + 1), ellipticGammaLogSummand p q (p * x) j k) -
        ∑ j ∈ Finset.range (N + 1), ellipticGammaLogSummand p q x j k =
      ellipticGammaLogAtom (q ^ (k + 1) / x) -
        ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x 0 k) -
        ellipticGammaLogAtom (ellipticGammaForwardArgument p q x N k) +
        ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x (N + 1) k) := by
  induction N with
  | zero =>
      simp only [Nat.zero_add, Finset.sum_range_one]
      rw [ellipticGammaLogSummand_mul_p_zero hp hx]
      simp only [ellipticGammaLogSummand]
      ring
  | succ N ih =>
      calc
        (∑ j ∈ Finset.range (N.succ + 1), ellipticGammaLogSummand p q (p * x) j k) -
              ∑ j ∈ Finset.range (N.succ + 1), ellipticGammaLogSummand p q x j k =
            ((∑ j ∈ Finset.range (N + 1), ellipticGammaLogSummand p q (p * x) j k) -
              ∑ j ∈ Finset.range (N + 1), ellipticGammaLogSummand p q x j k) +
              (ellipticGammaLogSummand p q (p * x) (N + 1) k -
                ellipticGammaLogSummand p q x (N + 1) k) := by
            conv_lhs =>
              congr
              · rw [show N.succ + 1 = (N + 1) + 1 by omega, Finset.sum_range_succ]
              · rw [show N.succ + 1 = (N + 1) + 1 by omega, Finset.sum_range_succ]
            ring
        _ = ellipticGammaLogAtom (q ^ (k + 1) / x) -
              ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x 0 k) -
              ellipticGammaLogAtom (ellipticGammaForwardArgument p q x (N + 1) k) +
              ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x (N + 2) k) := by
            rw [ih, ellipticGammaLogSummand_mul_p_succ hp hx]
            simp only [ellipticGammaLogSummand]
            ring

theorem ellipticGammaForwardArgument_mul_q_zero
    {p q x : ℂ} (hq : q ≠ 0) (hx : x ≠ 0) (j : ℕ) :
    ellipticGammaForwardArgument p q (q * x) j 0 = p ^ (j + 1) / x := by
  simp only [ellipticGammaForwardArgument, zero_add, pow_one]
  field_simp [hq, hx]

theorem ellipticGammaForwardArgument_mul_q_succ
    {p q x : ℂ} (hq : q ≠ 0) (hx : x ≠ 0) (j k : ℕ) :
    ellipticGammaForwardArgument p q (q * x) j (k + 1) =
      ellipticGammaForwardArgument p q x j k := by
  simp only [ellipticGammaForwardArgument]
  field_simp
  ring

theorem ellipticGammaBackwardArgument_mul_q
    (p q x : ℂ) (j k : ℕ) :
    ellipticGammaBackwardArgument p q (q * x) j k =
      ellipticGammaBackwardArgument p q x j (k + 1) := by
  simp [ellipticGammaBackwardArgument, pow_succ]
  ring

/-- Exact finite telescoping in the second nome direction. -/
theorem ellipticGammaLogSummand_sum_mul_q
    {p q x : ℂ} (hq : q ≠ 0) (hx : x ≠ 0) (M j : ℕ) :
    (∑ k ∈ Finset.range (M + 1), ellipticGammaLogSummand p q (q * x) j k) -
        ∑ k ∈ Finset.range (M + 1), ellipticGammaLogSummand p q x j k =
      ellipticGammaLogAtom (p ^ (j + 1) / x) -
        ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x j 0) -
        ellipticGammaLogAtom (ellipticGammaForwardArgument p q x j M) +
        ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x j (M + 1)) := by
  induction M with
  | zero =>
      simp [ellipticGammaLogSummand, ellipticGammaForwardArgument_mul_q_zero hq hx,
        ellipticGammaBackwardArgument_mul_q]
      ring
  | succ M ih =>
      calc
        (∑ k ∈ Finset.range (M.succ + 1), ellipticGammaLogSummand p q (q * x) j k) -
              ∑ k ∈ Finset.range (M.succ + 1), ellipticGammaLogSummand p q x j k =
            ((∑ k ∈ Finset.range (M + 1), ellipticGammaLogSummand p q (q * x) j k) -
              ∑ k ∈ Finset.range (M + 1), ellipticGammaLogSummand p q x j k) +
              (ellipticGammaLogSummand p q (q * x) j (M + 1) -
                ellipticGammaLogSummand p q x j (M + 1)) := by
            conv_lhs =>
              congr
              · rw [show M.succ + 1 = (M + 1) + 1 by omega, Finset.sum_range_succ]
              · rw [show M.succ + 1 = (M + 1) + 1 by omega, Finset.sum_range_succ]
            ring
        _ = ellipticGammaLogAtom (p ^ (j + 1) / x) -
              ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x j 0) -
              ellipticGammaLogAtom (ellipticGammaForwardArgument p q x j (M + 1)) +
              ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x j (M + 2)) := by
            rw [ih, ellipticGammaLogSummand]
            rw [ellipticGammaForwardArgument_mul_q_succ hq hx,
              ellipticGammaBackwardArgument_mul_q]
            simp only [ellipticGammaLogSummand]
            ring

/-- Near zero, the logarithmic atom is bounded by twice its argument. This is the comparison
estimate used for normal convergence of the double kernel. -/
theorem norm_ellipticGammaLogAtom_le_two_mul {t : ℂ} (ht : ‖t‖ ≤ (1 : ℝ) / 2) :
    ‖ellipticGammaLogAtom t‖ ≤ 2 * ‖t‖ := by
  have hden : (1 : ℝ) / 2 ≤ ‖1 - t‖ := by
    have h := norm_sub_norm_le (1 : ℂ) t
    rw [norm_one] at h
    linarith
  have hdenPos : 0 < ‖1 - t‖ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hden
  rw [ellipticGammaLogAtom, norm_div, div_le_iff₀ hdenPos]
  nlinarith [norm_nonneg t]

/-- A summable family of arguments remains summable after applying the logarithmic atom.
Only a cofinite tail needs the local estimate; the finitely many exceptional terms are harmless. -/
theorem summable_ellipticGammaLogAtom_of_summable_norm {ι : Type*} {t : ι → ℂ}
    (ht : Summable (fun i => ‖t i‖)) :
    Summable (fun i => ellipticGammaLogAtom (t i)) := by
  apply (ht.mul_left 2).of_norm_bounded_eventually
  filter_upwards [ht.tendsto_cofinite_zero.eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 2)] with i hi
  exact norm_ellipticGammaLogAtom_le_two_mul hi

/-- Absolute summability of the numerator-side half of the elliptic-gamma kernel. -/
theorem summable_norm_ellipticGammaForwardArgument
    {p q x : ℂ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    Summable (fun jk : ℕ × ℕ => ‖ellipticGammaForwardArgument p q x jk.1 jk.2‖) := by
  have hp0 : 0 ≤ ‖p‖ := norm_nonneg p
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hpGeom : Summable (fun j : ℕ => ‖p‖ ^ (j + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_lt_one hp0 hp).mul_left ‖p‖
  have hqGeom : Summable (fun k : ℕ => ‖q‖ ^ (k + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_lt_one hq0 hq).mul_left ‖q‖
  have hprod : Summable (fun jk : ℕ × ℕ =>
      ‖p‖ ^ (jk.1 + 1) * ‖q‖ ^ (jk.2 + 1)) :=
    hpGeom.mul_of_nonneg hqGeom (fun _ => pow_nonneg hp0 _) (fun _ => pow_nonneg hq0 _)
  have hscaled := hprod.mul_right ‖x‖⁻¹
  apply hscaled.congr
  intro jk
  simp [ellipticGammaForwardArgument, div_eq_mul_inv]

/-- Absolute summability of the denominator-side half of the elliptic-gamma kernel. -/
theorem summable_norm_ellipticGammaBackwardArgument
    {p q x : ℂ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    Summable (fun jk : ℕ × ℕ => ‖ellipticGammaBackwardArgument p q x jk.1 jk.2‖) := by
  have hp0 : 0 ≤ ‖p‖ := norm_nonneg p
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hpGeom : Summable (fun j : ℕ => ‖p‖ ^ j) :=
    summable_geometric_of_lt_one hp0 hp
  have hqGeom : Summable (fun k : ℕ => ‖q‖ ^ k) :=
    summable_geometric_of_lt_one hq0 hq
  have hprod : Summable (fun jk : ℕ × ℕ => ‖p‖ ^ jk.1 * ‖q‖ ^ jk.2) :=
    hpGeom.mul_of_nonneg hqGeom (fun _ => pow_nonneg hp0 _) (fun _ => pow_nonneg hq0 _)
  have hscaled := hprod.mul_right ‖x‖
  apply hscaled.congr
  intro jk
  simp [ellipticGammaBackwardArgument]

/-- The full logarithmic-derivative double kernel is absolutely summable. -/
theorem summable_ellipticGammaLogSummand
    {p q x : ℂ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    Summable (fun jk : ℕ × ℕ => ellipticGammaLogSummand p q x jk.1 jk.2) := by
  exact (summable_ellipticGammaLogAtom_of_summable_norm
      (summable_norm_ellipticGammaForwardArgument hp hq)).add
    (summable_ellipticGammaLogAtom_of_summable_norm
      (summable_norm_ellipticGammaBackwardArgument hp hq))

/-- The pointwise logarithmic-derivative kernel of the elliptic gamma double product. -/
def ellipticGammaLogKernel (p q x : ℂ) : ℂ :=
  ∑' jk : ℕ × ℕ, ellipticGammaLogSummand p q x jk.1 jk.2

theorem ellipticGammaLogAtom_tendsto_zero :
    Filter.Tendsto ellipticGammaLogAtom (nhds (0 : ℂ)) (nhds 0) := by
  have hcont : ContinuousAt (fun t : ℂ => t / (1 - t)) 0 :=
    continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by norm_num)
  simpa [ellipticGammaLogAtom] using hcont.tendsto

theorem ellipticGammaForwardArgument_tendsto_zero_first
    {p q x : ℂ} (hp : ‖p‖ < 1) (k : ℕ) :
    Filter.Tendsto (fun N => ellipticGammaForwardArgument p q x N k)
      Filter.atTop (nhds 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp
  have h := ((hpow.mul_const p).mul_const (q ^ (k + 1))).div_const x
  simpa [ellipticGammaForwardArgument, pow_succ, mul_assoc] using h

theorem ellipticGammaBackwardArgument_tendsto_zero_first
    {p q x : ℂ} (hp : ‖p‖ < 1) (k : ℕ) :
    Filter.Tendsto (fun N => ellipticGammaBackwardArgument p q x (N + 1) k)
      Filter.atTop (nhds 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp
  have h := ((hpow.mul_const p).mul_const (q ^ k)).mul_const x
  simpa [ellipticGammaBackwardArgument, pow_succ, mul_assoc] using h

/-- The two terminal tails in first-nome finite telescoping vanish. -/
theorem ellipticGammaLogTerminalTails_tendsto_zero_first
    {p q x : ℂ} (hp : ‖p‖ < 1) (k : ℕ) :
    Filter.Tendsto
      (fun N => -ellipticGammaLogAtom (ellipticGammaForwardArgument p q x N k) +
        ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x (N + 1) k))
      Filter.atTop (nhds 0) := by
  have hforward : Filter.Tendsto
      (fun N => ellipticGammaLogAtom (ellipticGammaForwardArgument p q x N k))
      Filter.atTop (nhds 0) := ellipticGammaLogAtom_tendsto_zero.comp
    (ellipticGammaForwardArgument_tendsto_zero_first (q := q) (x := x) hp k)
  have hbackward : Filter.Tendsto
      (fun N => ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x (N + 1) k))
      Filter.atTop (nhds 0) := ellipticGammaLogAtom_tendsto_zero.comp
    (ellipticGammaBackwardArgument_tendsto_zero_first (q := q) (x := x) hp k)
  simpa using hforward.neg.add hbackward

theorem ellipticGammaForwardArgument_tendsto_zero_second
    {p q x : ℂ} (hq : ‖q‖ < 1) (j : ℕ) :
    Filter.Tendsto (fun M => ellipticGammaForwardArgument p q x j M)
      Filter.atTop (nhds 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  have h := ((hpow.mul_const q).const_mul (p ^ (j + 1))).div_const x
  simpa [ellipticGammaForwardArgument, pow_succ, mul_assoc] using h

theorem ellipticGammaBackwardArgument_tendsto_zero_second
    {p q x : ℂ} (hq : ‖q‖ < 1) (j : ℕ) :
    Filter.Tendsto (fun M => ellipticGammaBackwardArgument p q x j (M + 1))
      Filter.atTop (nhds 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  have h := ((hpow.mul_const q).const_mul (p ^ j)).mul_const x
  simpa [ellipticGammaBackwardArgument, pow_succ, mul_assoc] using h

/-- The two terminal tails in second-nome finite telescoping vanish. -/
theorem ellipticGammaLogTerminalTails_tendsto_zero_second
    {p q x : ℂ} (hq : ‖q‖ < 1) (j : ℕ) :
    Filter.Tendsto
      (fun M => -ellipticGammaLogAtom (ellipticGammaForwardArgument p q x j M) +
        ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x j (M + 1)))
      Filter.atTop (nhds 0) := by
  have hforward : Filter.Tendsto
      (fun M => ellipticGammaLogAtom (ellipticGammaForwardArgument p q x j M))
      Filter.atTop (nhds 0) := ellipticGammaLogAtom_tendsto_zero.comp
    (ellipticGammaForwardArgument_tendsto_zero_second (p := p) (x := x) hq j)
  have hbackward : Filter.Tendsto
      (fun M => ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x j (M + 1)))
      Filter.atTop (nhds 0) := ellipticGammaLogAtom_tendsto_zero.comp
    (ellipticGammaBackwardArgument_tendsto_zero_second (p := p) (x := x) hq j)
  simpa using hforward.neg.add hbackward

/-- One summand of the multiplicative logarithmic derivative of the Jacobi theta product. -/
def ellipticThetaLogSummand (q x : ℂ) (k : ℕ) : ℂ :=
  ellipticGammaLogAtom (q ^ (k + 1) / x) - ellipticGammaLogAtom (q ^ k * x)

/-- The multiplicative logarithmic derivative of the Jacobi theta product, defined by its
absolutely convergent series. -/
def ellipticThetaLogKernel (q x : ℂ) : ℂ :=
  ∑' k : ℕ, ellipticThetaLogSummand q x k

/-- Absolute summability of the theta boundary series. -/
theorem summable_ellipticThetaLogSummand {q x : ℂ} (hq : ‖q‖ < 1) :
    Summable (ellipticThetaLogSummand q x) := by
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hforwardNorm : Summable (fun k : ℕ => ‖q ^ (k + 1) / x‖) := by
    have hgeom : Summable (fun k : ℕ => ‖q‖ ^ (k + 1)) := by
      simpa [pow_succ, mul_comm] using
        (summable_geometric_of_lt_one hq0 hq).mul_left ‖q‖
    have hscaled := hgeom.mul_right ‖x‖⁻¹
    apply hscaled.congr
    intro k
    simp [div_eq_mul_inv]
  have hbackwardNorm : Summable (fun k : ℕ => ‖q ^ k * x‖) := by
    have hgeom : Summable (fun k : ℕ => ‖q‖ ^ k) :=
      summable_geometric_of_lt_one hq0 hq
    have hscaled := hgeom.mul_right ‖x‖
    apply hscaled.congr
    intro k
    simp
  exact (summable_ellipticGammaLogAtom_of_summable_norm hforwardNorm).sub
    (summable_ellipticGammaLogAtom_of_summable_norm hbackwardNorm)

theorem summable_ellipticThetaForwardLogAtom {q x : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun k : ℕ => ellipticGammaLogAtom (q ^ k / x)) := by
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hgeom : Summable (fun k : ℕ => ‖q‖ ^ k) :=
    summable_geometric_of_lt_one hq0 hq
  have hscaled := hgeom.mul_right ‖x‖⁻¹
  apply summable_ellipticGammaLogAtom_of_summable_norm
  apply hscaled.congr
  intro k
  simp [div_eq_mul_inv]

theorem summable_ellipticThetaBackwardLogAtom {q x : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun k : ℕ => ellipticGammaLogAtom (q ^ k * x)) := by
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hgeom : Summable (fun k : ℕ => ‖q‖ ^ k) :=
    summable_geometric_of_lt_one hq0 hq
  have hscaled := hgeom.mul_right ‖x‖
  apply summable_ellipticGammaLogAtom_of_summable_norm
  apply hscaled.congr
  intro k
  simp

/-- The theta-product logarithmic kernel has the exact multiplicative quasiperiod law away from
the boundary pole `x = 1`. This is derived from its convergent series, not assumed from theta. -/
theorem ellipticThetaLogKernel_mul_q_sub
    {q x : ℂ} (hq0 : q ≠ 0) (hx : x ≠ 0) (hx1 : x ≠ 1) (hq : ‖q‖ < 1) :
    ellipticThetaLogKernel q (q * x) - ellipticThetaLogKernel q x = -1 := by
  have hf := summable_ellipticThetaForwardLogAtom (q := q) (x := x) hq
  have hb := summable_ellipticThetaBackwardLogAtom (q := q) (x := x) hq
  have hfShift : Summable (fun k : ℕ =>
      ellipticGammaLogAtom (q ^ (k + 1) / x)) := by
    simpa [Function.comp_def] using hf.comp_injective (i := fun k : ℕ => k + 1)
      (fun _ _ h => Nat.add_right_cancel h)
  have hfQ : Summable (fun k : ℕ =>
      ellipticGammaLogAtom (q ^ (k + 1) / (q * x))) := by
    have h := summable_ellipticThetaForwardLogAtom (q := q) (x := q * x) hq
    simpa [Function.comp_def] using h.comp_injective (i := fun k : ℕ => k + 1)
      (fun _ _ h => Nat.add_right_cancel h)
  have hbQ := summable_ellipticThetaBackwardLogAtom (q := q) (x := q * x) hq
  rw [ellipticThetaLogKernel, ellipticThetaLogKernel]
  simp_rw [ellipticThetaLogSummand]
  rw [hfQ.tsum_sub hbQ, hfShift.tsum_sub hb]
  have hforwardShift :
      (∑' k : ℕ, ellipticGammaLogAtom (q ^ k / x)) =
        ellipticGammaLogAtom (1 / x) +
          ∑' k : ℕ, ellipticGammaLogAtom (q ^ (k + 1) / x) := by
    simpa using hf.tsum_eq_zero_add
  have hbackwardShift :
      (∑' k : ℕ, ellipticGammaLogAtom (q ^ k * x)) =
        ellipticGammaLogAtom x +
          ∑' k : ℕ, ellipticGammaLogAtom (q ^ (k + 1) * x) := by
    simpa using hb.tsum_eq_zero_add
  have hforwardQ :
      (∑' k : ℕ, ellipticGammaLogAtom (q ^ (k + 1) / (q * x))) =
        ∑' k : ℕ, ellipticGammaLogAtom (q ^ k / x) := by
    apply tsum_congr
    intro k
    congr 1
    field_simp
    ring
  have hbackwardQ :
      (∑' k : ℕ, ellipticGammaLogAtom (q ^ k * (q * x))) =
        ∑' k : ℕ, ellipticGammaLogAtom (q ^ (k + 1) * x) := by
    apply tsum_congr
    intro k
    congr 1
    simp [pow_succ]
    ring
  rw [hforwardQ, hbackwardQ, hforwardShift, hbackwardShift]
  ring_nf
  rw [ellipticGammaLogAtom, ellipticGammaLogAtom]
  have h1x : (1 : ℂ) - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  have hx1sub : x - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hx1
  field_simp [h1x, hx1sub, hx]
  ring

/-- Infinite first-coordinate telescoping: a fiber of the double kernel changes by exactly one
theta-boundary summand under `x ↦ p*x`. -/
theorem ellipticGammaLogSummand_tsum_mul_p_fiber
    {p q x : ℂ} (hp0 : p ≠ 0) (hx : x ≠ 0) (hp : ‖p‖ < 1) (hq : ‖q‖ < 1)
    (k : ℕ) :
    (∑' j : ℕ, ellipticGammaLogSummand p q (p * x) j k) -
        ∑' j : ℕ, ellipticGammaLogSummand p q x j k =
      ellipticGammaLogAtom (q ^ (k + 1) / x) -
        ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x 0 k) := by
  have hmul : Summable (fun j : ℕ => ellipticGammaLogSummand p q (p * x) j k) :=
    (summable_ellipticGammaLogSummand
      (p := p) (q := q) (x := p * x) hp hq).prod_symm.prod_factor k
  have hbase : Summable (fun j : ℕ => ellipticGammaLogSummand p q x j k) :=
    (summable_ellipticGammaLogSummand
      (p := p) (q := q) (x := x) hp hq).prod_symm.prod_factor k
  have hL : Filter.Tendsto
      (fun N => (∑ j ∈ Finset.range (N + 1), ellipticGammaLogSummand p q (p * x) j k) -
        ∑ j ∈ Finset.range (N + 1), ellipticGammaLogSummand p q x j k)
      Filter.atTop
      (nhds ((∑' j : ℕ, ellipticGammaLogSummand p q (p * x) j k) -
        ∑' j : ℕ, ellipticGammaLogSummand p q x j k)) := by
    apply Filter.Tendsto.sub
    · simpa only using hmul.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    · simpa only using hbase.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hR : Filter.Tendsto
      (fun N => ellipticGammaLogAtom (q ^ (k + 1) / x) -
        ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x 0 k) +
        (-ellipticGammaLogAtom (ellipticGammaForwardArgument p q x N k) +
          ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x (N + 1) k)))
      Filter.atTop
      (nhds (ellipticGammaLogAtom (q ^ (k + 1) / x) -
        ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x 0 k))) := by
    simpa using tendsto_const_nhds.add
      (ellipticGammaLogTerminalTails_tendsto_zero_first hp k)
  apply tendsto_nhds_unique hL
  apply hR.congr'
  filter_upwards [] with N
  rw [ellipticGammaLogSummand_sum_mul_p hp0 hx]
  ring

/-- Fubini decomposition of the absolutely convergent double kernel into second-coordinate
fibers. -/
theorem ellipticGammaLogKernel_eq_tsum_fibers
    {p q x : ℂ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    ellipticGammaLogKernel p q x =
      ∑' k : ℕ, ∑' j : ℕ, ellipticGammaLogSummand p q x j k := by
  have h := summable_ellipticGammaLogSummand (p := p) (q := q) (x := x) hp hq
  rw [ellipticGammaLogKernel]
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq
    (fun jk : ℕ × ℕ => ellipticGammaLogSummand p q x jk.1 jk.2)]
  exact h.prod_symm.tsum_prod

/-- The double kernel is symmetric in its two nomes. -/
theorem ellipticGammaLogSummand_swap (p q x : ℂ) (j k : ℕ) :
    ellipticGammaLogSummand p q x j k = ellipticGammaLogSummand q p x k j := by
  simp [ellipticGammaLogSummand, ellipticGammaForwardArgument,
    ellipticGammaBackwardArgument, mul_comm]

/-- Nome symmetry of the full elliptic-gamma logarithmic kernel. -/
theorem ellipticGammaLogKernel_swap (p q x : ℂ) :
    ellipticGammaLogKernel p q x = ellipticGammaLogKernel q p x := by
  rw [ellipticGammaLogKernel, ellipticGammaLogKernel]
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq
    (fun jk : ℕ × ℕ => ellipticGammaLogSummand q p x jk.1 jk.2)]
  apply tsum_congr
  intro jk
  exact ellipticGammaLogSummand_swap p q x jk.1 jk.2

/-- The first elliptic-gamma increment equation, constructed directly from the double product:
under `x ↦ p*x`, the logarithmic kernel changes by the theta logarithmic kernel with nome `q`. -/
theorem ellipticGammaLogKernel_mul_p_sub
    {p q x : ℂ} (hp0 : p ≠ 0) (hx : x ≠ 0) (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    ellipticGammaLogKernel p q (p * x) - ellipticGammaLogKernel p q x =
      ellipticThetaLogKernel q x := by
  rw [ellipticGammaLogKernel_eq_tsum_fibers hp hq,
    ellipticGammaLogKernel_eq_tsum_fibers hp hq, ellipticThetaLogKernel]
  have hmul : Summable (fun k : ℕ =>
      ∑' j : ℕ, ellipticGammaLogSummand p q (p * x) j k) := by
    simpa using (summable_ellipticGammaLogSummand
      (p := p) (q := q) (x := p * x) hp hq).prod_symm.prod
  have hbase : Summable (fun k : ℕ =>
      ∑' j : ℕ, ellipticGammaLogSummand p q x j k) := by
    simpa using (summable_ellipticGammaLogSummand
      (p := p) (q := q) (x := x) hp hq).prod_symm.prod
  rw [← hmul.tsum_sub hbase]
  apply tsum_congr
  intro k
  rw [ellipticGammaLogSummand_tsum_mul_p_fiber hp0 hx hp hq k]
  simp [ellipticThetaLogSummand, ellipticGammaBackwardArgument]

/-- The polarized second elliptic-gamma increment equation follows from nome symmetry: under
`x ↦ q*x`, the logarithmic kernel changes by the theta logarithmic kernel with nome `p`. -/
theorem ellipticGammaLogKernel_mul_q_sub
    {p q x : ℂ} (hq0 : q ≠ 0) (hx : x ≠ 0) (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    ellipticGammaLogKernel p q (q * x) - ellipticGammaLogKernel p q x =
      ellipticThetaLogKernel p x := by
  rw [ellipticGammaLogKernel_swap p q (q * x), ellipticGammaLogKernel_swap p q x]
  exact ellipticGammaLogKernel_mul_p_sub hq0 hx hq hp

end

end GaloisForLFunctions
