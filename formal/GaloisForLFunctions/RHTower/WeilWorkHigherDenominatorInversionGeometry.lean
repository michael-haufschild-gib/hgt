import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorScaledBessel
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual geometry of the boundary inversion

These phase, scale and weight are the real coordinate, Bessel argument scale and
square-root height factor of `-1/(x+i*y)`, after horizontal evenness. Their spatial
jets extend continuously to height zero away from the origin. The phase speed is
strictly negative on every positive compact test support at sufficiently small height.
-/

noncomputable section

open Set

namespace RHTower.WeilHigherDenominator

def inversionBoundaryPhase (y x : ℝ) : ℝ := x / (x ^ 2 + y ^ 2)
def inversionBoundarySpeed (y x : ℝ) : ℝ := (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2
def inversionBoundarySpeedD (y x : ℝ) : ℝ :=
  2 * x * (x ^ 2 - 3 * y ^ 2) / (x ^ 2 + y ^ 2) ^ 3
def inversionBoundarySpeedDD (y x : ℝ) : ℝ :=
  -6 * (x ^ 4 - 6 * x ^ 2 * y ^ 2 + y ^ 4) / (x ^ 2 + y ^ 2) ^ 4
def inversionBoundaryScale (y x : ℝ) : ℝ := 2 * Real.pi / (x ^ 2 + y ^ 2)
def inversionBoundaryScaleD (y x : ℝ) : ℝ := -4 * Real.pi * x / (x ^ 2 + y ^ 2) ^ 2
def inversionBoundaryScaleDD (y x : ℝ) : ℝ :=
  4 * Real.pi * (3 * x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 3
def inversionBoundaryWeight (y x : ℝ) : ℝ := (x ^ 2 + y ^ 2) ^ (-(1 / 2 : ℝ))
def inversionBoundaryWeightD (y x : ℝ) : ℝ := -x * (x ^ 2 + y ^ 2) ^ (-(3 / 2 : ℝ))
def inversionBoundaryWeightDD (y x : ℝ) : ℝ :=
  -(x ^ 2 + y ^ 2) ^ (-(3 / 2 : ℝ)) +
    3 * x ^ 2 * (x ^ 2 + y ^ 2) ^ (-(5 / 2 : ℝ))

theorem inversionBoundaryDenom_pos {x : ℝ} (hx : 0 < x) (y : ℝ) :
    0 < x ^ 2 + y ^ 2 := by nlinarith [sq_pos_of_pos hx, sq_nonneg y]

private lemma inversionBoundaryDenom_deriv (y x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
  simpa using ((hasDerivAt_id x).pow 2).add_const (y ^ 2)

theorem hasDerivAt_inversionBoundaryPhase {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (inversionBoundaryPhase y) (inversionBoundarySpeed y x) x := by
  refine ((hasDerivAt_id x).div (inversionBoundaryDenom_deriv y x)
    (inversionBoundaryDenom_pos hx y).ne').congr_deriv ?_
  dsimp [inversionBoundarySpeed]
  ring

theorem hasDerivAt_inversionBoundarySpeed {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (inversionBoundarySpeed y) (inversionBoundarySpeedD y x) x := by
  have hd := inversionBoundaryDenom_deriv y x
  have hn : HasDerivAt (fun t : ℝ => y ^ 2 - t ^ 2) (-2 * x) x := by
    simpa using ((hasDerivAt_id x).pow 2).const_sub (y ^ 2)
  refine (hn.div (hd.pow 2) (pow_ne_zero 2 (inversionBoundaryDenom_pos hx y).ne')).congr_deriv ?_
  dsimp [inversionBoundarySpeedD]
  field_simp [(inversionBoundaryDenom_pos hx y).ne']
  ring

theorem hasDerivAt_inversionBoundarySpeedD {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (inversionBoundarySpeedD y) (inversionBoundarySpeedDD y x) x := by
  have hd := inversionBoundaryDenom_deriv y x
  have hn := ((hasDerivAt_id x).const_mul 2).mul
    (((hasDerivAt_id x).pow 2).sub_const (3 * y ^ 2))
  refine (hn.div (hd.pow 3) (pow_ne_zero 3 (inversionBoundaryDenom_pos hx y).ne')).congr_deriv ?_
  dsimp [inversionBoundarySpeedDD]
  field_simp [(inversionBoundaryDenom_pos hx y).ne']
  ring

theorem inversionBoundaryScale_pos {x : ℝ} (hx : 0 < x) (y : ℝ) :
    0 < inversionBoundaryScale y x :=
  div_pos (by positivity) (inversionBoundaryDenom_pos hx y)

theorem hasDerivAt_inversionBoundaryScale {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (inversionBoundaryScale y) (inversionBoundaryScaleD y x) x := by
  refine ((hasDerivAt_const x (2 * Real.pi)).div (inversionBoundaryDenom_deriv y x)
    (inversionBoundaryDenom_pos hx y).ne').congr_deriv ?_
  dsimp [inversionBoundaryScaleD]
  ring

theorem hasDerivAt_inversionBoundaryScaleD {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (inversionBoundaryScaleD y) (inversionBoundaryScaleDD y x) x := by
  refine (((hasDerivAt_id x).const_mul (-4 * Real.pi)).div
    ((inversionBoundaryDenom_deriv y x).pow 2)
    (pow_ne_zero 2 (inversionBoundaryDenom_pos hx y).ne')).congr_deriv ?_
  dsimp [inversionBoundaryScaleDD]
  field_simp [(inversionBoundaryDenom_pos hx y).ne']
  ring

theorem hasDerivAt_inversionBoundaryWeight {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (inversionBoundaryWeight y) (inversionBoundaryWeightD y x) x := by
  refine ((inversionBoundaryDenom_deriv y x).rpow_const
    (p := -(1 / 2 : ℝ)) (Or.inl (inversionBoundaryDenom_pos hx y).ne')).congr_deriv ?_
  simp only [inversionBoundaryWeightD,
    show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num]
  ring

theorem hasDerivAt_inversionBoundaryWeightD {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (inversionBoundaryWeightD y) (inversionBoundaryWeightDD y x) x := by
  have hp := (inversionBoundaryDenom_deriv y x).rpow_const
    (p := -(3 / 2 : ℝ)) (Or.inl (inversionBoundaryDenom_pos hx y).ne')
  refine ((hasDerivAt_id x).neg.mul hp).congr_deriv ?_
  norm_num [inversionBoundaryWeightDD]
  ring

/-- On a positive compact interval, every sufficiently low inversion path is nonstationary. -/
theorem inversionBoundarySpeed_neg {a x y : ℝ} (ha : 0 < a) (hx : a ≤ x)
    (hy : 0 ≤ y) (hy₁ : y ≤ a / 2) : inversionBoundarySpeed y x < 0 := by
  have hx0 := ha.trans_le hx
  apply div_neg_of_neg_of_pos _ (sq_pos_of_pos (inversionBoundaryDenom_pos hx0 y))
  have hxy : y < x := by linarith
  nlinarith

/-- One continuous budget records all geometric factors consumed by two integrations by parts. -/
def inversionBoundaryJetBudget (y x : ℝ) : ℝ :=
  |inversionBoundaryWeight y x| + |inversionBoundaryWeightD y x| +
    |inversionBoundaryWeightDD y x| + |1 / inversionBoundarySpeed y x| +
    |inversionBoundarySpeedD y x| + |inversionBoundarySpeedDD y x| +
    |inversionBoundaryScaleD y x / inversionBoundaryScale y x| +
    |inversionBoundaryScaleDD y x / inversionBoundaryScale y x| +
    |1 / inversionBoundaryScale y x|

theorem continuousOn_inversionBoundaryJetBudget {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun p : ℝ × ℝ => inversionBoundaryJetBudget p.2 p.1)
      (Icc a b ×ˢ Icc 0 (a / 2)) := by
  let K := Icc a b ×ˢ Icc 0 (a / 2)
  have hd : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) K := by fun_prop
  have hd0 : ∀ p ∈ K, p.1 ^ 2 + p.2 ^ 2 ≠ 0 := by
    intro p hp
    exact (inversionBoundaryDenom_pos (ha.trans_le hp.1.1) p.2).ne'
  have hp (r : ℝ) : ContinuousOn (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) ^ r) K :=
    hd.rpow_const fun p h => Or.inl (hd0 p h)
  have hv : ContinuousOn (fun p : ℝ × ℝ => inversionBoundarySpeed p.2 p.1) K := by
    exact (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ 2 - p.1 ^ 2) K).div
      (hd.pow 2) fun p h => pow_ne_zero 2 (hd0 p h)
  have hv0 : ∀ p ∈ K, inversionBoundarySpeed p.2 p.1 ≠ 0 := by
    intro p h
    exact (inversionBoundarySpeed_neg ha h.1.1 h.2.1 h.2.2).ne
  have hc : ContinuousOn (fun p : ℝ × ℝ => inversionBoundaryScale p.2 p.1) K :=
    continuousOn_const.div hd hd0
  have hc0 : ∀ p ∈ K, inversionBoundaryScale p.2 p.1 ≠ 0 := by
    intro p h
    exact (inversionBoundaryScale_pos (ha.trans_le h.1.1) p.2).ne'
  have hv₁ : ContinuousOn (fun p : ℝ × ℝ => inversionBoundarySpeedD p.2 p.1) K :=
    (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => 2 * p.1 * (p.1 ^ 2 - 3 * p.2 ^ 2)) K).div
      (hd.pow 3) fun p h => pow_ne_zero 3 (hd0 p h)
  have hv₂ : ContinuousOn (fun p : ℝ × ℝ => inversionBoundarySpeedDD p.2 p.1) K :=
    (by fun_prop : ContinuousOn (fun p : ℝ × ℝ =>
      -6 * (p.1 ^ 4 - 6 * p.1 ^ 2 * p.2 ^ 2 + p.2 ^ 4)) K).div
      (hd.pow 4) fun p h => pow_ne_zero 4 (hd0 p h)
  have hc₁ : ContinuousOn (fun p : ℝ × ℝ => inversionBoundaryScaleD p.2 p.1) K :=
    (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => -4 * Real.pi * p.1) K).div
      (hd.pow 2) fun p h => pow_ne_zero 2 (hd0 p h)
  have hc₂ : ContinuousOn (fun p : ℝ × ℝ => inversionBoundaryScaleDD p.2 p.1) K :=
    (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => 4 * Real.pi * (3 * p.1 ^ 2 - p.2 ^ 2)) K).div
      (hd.pow 3) fun p h => pow_ne_zero 3 (hd0 p h)
  have hw : ContinuousOn (fun p : ℝ × ℝ => inversionBoundaryWeight p.2 p.1) K := hp _
  have hw₁ : ContinuousOn (fun p : ℝ × ℝ => inversionBoundaryWeightD p.2 p.1) K :=
    (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => -p.1) K).mul (hp _)
  have hw₂ : ContinuousOn (fun p : ℝ × ℝ => inversionBoundaryWeightDD p.2 p.1) K :=
    (hp _).neg.add ((by fun_prop : ContinuousOn (fun p : ℝ × ℝ => 3 * p.1 ^ 2) K).mul (hp _))
  exact ((((((((hw.abs.add hw₁.abs).add hw₂.abs).add
    (continuousOn_const.div hv hv0).abs).add hv₁.abs).add hv₂.abs).add
      (hc₁.div hc hc0).abs).add (hc₂.div hc hc0).abs).add (continuousOn_const.div hc hc0).abs)

/-- All inversion-geometry factors have a single bound uniform down to height zero. -/
theorem exists_inversionBoundaryJetBudget_bound {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc a b, ∀ y ∈ Icc 0 (a / 2),
      inversionBoundaryJetBudget y x ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (continuousOn_inversionBoundaryJetBudget (b := b) ha)
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx y hy => ?_⟩
  have h := hC (x, y) ⟨hx, hy⟩
  simp only [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

end RHTower.WeilHigherDenominator
