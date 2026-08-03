import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A coherent position/Euler square is excluded by one boundary packet

Four independent pieces of the exclusion.

* `star_combo_expand` — the completion-of-squares identity for a self-adjoint `X` and a skew-adjoint
  `Z`: `star (X - Z) * (X - Z) = X² - [X, Z] + (star Z) Z`.  Pure `⋆`-ring algebra; with
  `star_smul_selfAdjoint` and `star_smul_skewAdjoint` it applies to `a • X` and `b • Z`, which is the
  balanced form of the identity.
* `norm_sub_smul_sq_of_inner_eq_zero` and `two_mul_norm_mul_norm_le` — on a packet where the two
  outputs are orthogonal the square splits, and the split is bounded below by `2‖Xf‖‖Zf‖` for every
  balancing scalar.  So no choice of `α` can be cheap.
* `fwdShift`, `bwdShift`, `bwdShift_eq_zero_of_support`, `integral_fwdShift_mul_eq_zero`,
  `commutatorForm_eq_zero` — the fixed boundary packet: for a vector supported in `(0, δ)` and shifts
  of length exceeding `δ`, the backward shift annihilates the packet and the forward shift leaves its
  support, so the whole prime commutator form vanishes on it.  No measure theory beyond
  `integral_zero`, because the integrand is identically zero.
* `not_exists_coherent_square` — the exclusion: a form with a fixed finite value on the packet cannot
  equal a coherent square plus a nonnegative remainder once the square's lower bound diverges, no
  matter how the balancing scalar depends on the aperture.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology MeasureTheory Set

/-! ## The completion-of-squares identity -/

/-- **Equation (15).**  With `X` self-adjoint and `Z` skew-adjoint the mixed square expands with the
commutator as the only cross term. -/
theorem star_combo_expand {R : Type*} [Ring R] [StarRing R] (X Z : R)
    (hX : star X = X) (hZ : star Z = -Z) :
    star (X - Z) * (X - Z) = X * X - (X * Z - Z * X) + star Z * Z := by
  have hstar : star (X - Z) = X + Z := by
    rw [star_sub, hX, hZ, sub_neg_eq_add]
  rw [hstar, hZ]
  noncomm_ring

/-- Scaling by a real preserves self-adjointness. -/
theorem star_smul_selfAdjoint {R : Type*} [Ring R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R]
    (a : ℝ) {X : R} (hX : star X = X) : star (a • X) = a • X := by
  rw [star_smul, hX, star_trivial]

/-- Scaling by a real preserves skew-adjointness.  Together with `star_combo_expand` applied to
`a • X` and `b • Z` this is `(15)` for an arbitrary balancing scalar. -/
theorem star_smul_skewAdjoint {R : Type*} [Ring R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R]
    (b : ℝ) {Z : R} (hZ : star Z = -Z) : star (b • Z) = -(b • Z) := by
  rw [star_smul, hZ, star_trivial, smul_neg]

/-! ## The orthogonal split and its lower bound -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On a packet where the two outputs are orthogonal the mixed square splits exactly. -/
theorem norm_sub_smul_sq_of_inner_eq_zero {u v : E} (h : inner ℝ u v = (0 : ℝ)) (a b : ℝ) :
    ‖a • u - b • v‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 + b ^ 2 * ‖v‖ ^ 2 := by
  have hsq : ‖a • u - b • v‖ ^ 2
      = ‖a • u‖ ^ 2 - 2 * inner ℝ (a • u) (b • v) + ‖b • v‖ ^ 2 := norm_sub_sq_real _ _
  rw [hsq, real_inner_smul_left, real_inner_smul_right, h, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs]
  rw [mul_pow, mul_pow, sq_abs, sq_abs]
  ring

/-- **Equation (16).**  Every balancing scalar pays at least `2‖u‖‖v‖`. -/
theorem two_mul_norm_mul_norm_le {u v : E} (h : inner ℝ u v = (0 : ℝ)) {a b : ℝ}
    (hab : a * b = 1) : 2 * (‖u‖ * ‖v‖) ≤ ‖a • u - b • v‖ ^ 2 := by
  rw [norm_sub_smul_sq_of_inner_eq_zero h]
  have hsq : 0 ≤ (a * ‖u‖ - b * ‖v‖) ^ 2 := sq_nonneg _
  have habs : a * b * (‖u‖ * ‖v‖) = ‖u‖ * ‖v‖ := by rw [hab, one_mul]
  nlinarith [hsq, habs]

/-! ## The fixed boundary packet -/

/-- The aperture-restricted forward shift. -/
def fwdShift (A h : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => if h ≤ x ∧ x ≤ A then f (x - h) else 0

/-- The aperture-restricted backward shift, the adjoint of `fwdShift`. -/
def bwdShift (A h : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => if 0 ≤ x ∧ x + h ≤ A then f (x + h) else 0

/-- **Equation (7), backward half.**  A shift longer than the packet width annihilates the packet. -/
theorem bwdShift_eq_zero_of_support {A h delta : ℝ} {f : ℝ → ℝ}
    (hf : ∀ x, f x ≠ 0 → x ∈ Ioo 0 delta) (hh : delta ≤ h) :
    bwdShift A h f = fun _ => 0 := by
  funext x
  simp only [bwdShift]
  by_cases hx : 0 ≤ x ∧ x + h ≤ A
  · rw [if_pos hx]
    by_contra hne
    obtain ⟨_, hlt⟩ := hf (x + h) hne
    linarith [hx.1]
  · rw [if_neg hx]

/-- **Equation (7), forward half.**  The forward shift leaves the packet's support, so its pairing
with the packet vanishes identically. -/
theorem fwdShift_mul_eq_zero {A h delta : ℝ} {f : ℝ → ℝ}
    (hf : ∀ x, f x ≠ 0 → x ∈ Ioo 0 delta) (hh : delta ≤ h) (x : ℝ) :
    fwdShift A h f x * f x = 0 := by
  by_cases hx : f x = 0
  · rw [hx, mul_zero]
  · obtain ⟨_, hlt⟩ := hf x hx
    have hnot : ¬ (h ≤ x ∧ x ≤ A) := by
      intro hc
      linarith [hc.1]
    simp only [fwdShift, if_neg hnot, zero_mul]

theorem integral_fwdShift_mul_eq_zero {A h delta : ℝ} {f : ℝ → ℝ}
    (hf : ∀ x, f x ≠ 0 → x ∈ Ioo 0 delta) (hh : delta ≤ h) :
    (∫ x : ℝ, fwdShift A h f x * f x) = 0 := by
  have hzero : (fun x : ℝ => fwdShift A h f x * f x) = fun _ : ℝ => (0 : ℝ) :=
    funext fun x => fwdShift_mul_eq_zero hf hh x
  rw [hzero, integral_zero]

/-- **Equation (8).**  The whole prime commutator form vanishes on the packet: every shift is longer
than the packet width, so both the forward and the backward channel contribute nothing. -/
theorem commutatorForm_eq_zero {A delta : ℝ} {f : ℝ → ℝ} {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (hh : ι → ℝ) (hf : ∀ x, f x ≠ 0 → x ∈ Ioo 0 delta)
    (hlong : ∀ n ∈ s, delta ≤ hh n) :
    (∫ x : ℝ, (∑ n ∈ s, c n * (fwdShift A (hh n) f x + bwdShift A (hh n) f x)) * f x) = 0 := by
  have hzero : (fun x : ℝ =>
      (∑ n ∈ s, c n * (fwdShift A (hh n) f x + bwdShift A (hh n) f x)) * f x)
      = fun _ : ℝ => (0 : ℝ) := by
    funext x
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun n hn => ?_
    have hb : bwdShift A (hh n) f x = 0 := by
      rw [bwdShift_eq_zero_of_support hf (hlong n hn)]
    have hfwd : fwdShift A (hh n) f x * f x = 0 :=
      fwdShift_mul_eq_zero hf (hlong n hn) x
    calc c n * (fwdShift A (hh n) f x + bwdShift A (hh n) f x) * f x
        = c n * (fwdShift A (hh n) f x * f x) + c n * (bwdShift A (hh n) f x * f x) := by ring
      _ = 0 := by rw [hfwd, hb]; ring
  rw [hzero, integral_zero]

/-! ## The exclusion -/

/-- **Equations (17)–(19).**  A form whose value on the packet is a fixed finite constant cannot be a
coherent square plus a nonnegative remainder once the square's lower bound diverges — for any
aperture-dependent balancing scalar. -/
theorem not_exists_coherent_square {q sq rem lower : ℕ → ℝ}
    (hq : ∀ j, q j = sq j + rem j) (hrem : ∀ j, 0 ≤ rem j)
    (hsq : ∀ j, lower j ≤ sq j) (hconst : ∃ c : ℝ, ∀ j, q j = c)
    (hdiv : Tendsto lower atTop atTop) : False := by
  obtain ⟨c, hc⟩ := hconst
  obtain ⟨j, hj⟩ := (hdiv.eventually_gt_atTop c).exists
  have h1 : lower j ≤ sq j := hsq j
  have h2 : sq j ≤ q j := by
    have := hrem j
    have := hq j
    linarith
  have h3 : q j = c := hc j
  linarith

end GaloisForLFunctions.RHTower

end
