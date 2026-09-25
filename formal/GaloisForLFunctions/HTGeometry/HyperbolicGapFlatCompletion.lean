import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Hyperbolic-gap flat completion

The difference between two `cosh` prime potentials is the positive
hyperbolic-sinc correction of a linear height gap times a sum-phase `sinh`.
This is the algebraic step behind the source-level flat completion of an
equal-depth Gamma prime pair.  It does not construct a Sonin operator or
control a Calkin norm.
-/

namespace HTGeometry

open Filter Topology

noncomputable section

/-- The hyperbolic sinc, including its removable value at zero. -/
def hyperbolicGapSinc (t : ℝ) : ℝ :=
  if t = 0 then 1 else Real.sinh t / t

theorem mul_hyperbolicGapSinc (t : ℝ) :
    t * hyperbolicGapSinc t = Real.sinh t := by
  by_cases ht : t = 0
  · simp [hyperbolicGapSinc, ht]
  · rw [hyperbolicGapSinc, if_neg ht]
    field_simp [ht]

/-- Away from coincidence, the unique flat gap factor strictly exceeds one. -/
theorem hyperbolicGapSinc_gt_one_of_pos {t : ℝ} (ht : 0 < t) :
    1 < hyperbolicGapSinc t := by
  have hs : t < Real.sinh t := Real.self_lt_sinh_iff.mpr ht
  rw [hyperbolicGapSinc, if_neg ht.ne']
  exact (one_lt_div ht).mpr hs

theorem hyperbolicGapSinc_even (t : ℝ) :
    hyperbolicGapSinc (-t) = hyperbolicGapSinc t := by
  by_cases ht : t = 0
  · simp [hyperbolicGapSinc, ht]
  · rw [hyperbolicGapSinc, hyperbolicGapSinc,
      if_neg (neg_ne_zero.mpr ht), if_neg ht, Real.sinh_neg]
    ring

theorem hyperbolicGapSinc_gt_one_of_ne_zero {t : ℝ} (ht : t ≠ 0) :
    1 < hyperbolicGapSinc t := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have h := hyperbolicGapSinc_gt_one_of_pos (neg_pos.mpr hneg)
    rwa [hyperbolicGapSinc_even] at h
  · exact hyperbolicGapSinc_gt_one_of_pos hpos

/-- The two-point Schur kernel with diagonal `1` and off-diagonal gap sinc
has a negative direction `(1,-1)` and a positive direction `(1,1)`.
Entrywise positivity therefore does not give an operator-positive transport. -/
theorem hyperbolicGapSinc_pair_indefinite {t : ℝ} (ht : t ≠ 0) :
    (1 + 2 * hyperbolicGapSinc t * (-1) + (-1)^2 : ℝ) < 0 ∧
    0 < (1 + 2 * hyperbolicGapSinc t * 1 + 1^2 : ℝ) := by
  have h := hyperbolicGapSinc_gt_one_of_ne_zero ht
  constructor <;> nlinarith

private theorem cosh_gap_identity (g x y : ℝ) :
    Real.cosh (g * y) - Real.cosh (g * x) =
      2 * Real.sinh (g * (x + y) / 2) * Real.sinh (g * (y - x) / 2) := by
  let a : ℝ := g * (x + y) / 2
  let b : ℝ := g * (y - x) / 2
  have hy : g * y = a + b := by dsimp [a, b]; ring
  have hx : g * x = a - b := by dsimp [a, b]; ring
  rw [hy, hx, Real.cosh_add, Real.cosh_sub]
  dsimp [a, b]
  ring

/-- The flat completion of the linear-gap, sum-phase pair kernel. -/
def flatGapEdge (g x y : ℝ) : ℝ :=
  g * ((y - x) * Real.sinh (g * (x + y) / 2) *
    hyperbolicGapSinc (g * (y - x) / 2))

/-- The completed pair is exactly a one-particle potential difference. -/
theorem flatGapEdge_eq_cosh_sub (g x y : ℝ) :
    flatGapEdge g x y = Real.cosh (g * y) - Real.cosh (g * x) := by
  have hs := mul_hyperbolicGapSinc (g * (y - x) / 2)
  have h := cosh_gap_identity g x y
  calc
    flatGapEdge g x y =
      2 * Real.sinh (g * (x + y) / 2) *
        ((g * (y - x) / 2) * hyperbolicGapSinc (g * (y - x) / 2)) := by
          unfold flatGapEdge
          ring
    _ = 2 * Real.sinh (g * (x + y) / 2) * Real.sinh (g * (y - x) / 2) := by
          rw [hs]
    _ = _ := h.symm

/-- Every three-point holonomy of the corrected pair vanishes. -/
theorem flatGapEdge_triangle (g x y z : ℝ) :
    flatGapEdge g x y + flatGapEdge g y z = flatGapEdge g x z := by
  rw [flatGapEdge_eq_cosh_sub, flatGapEdge_eq_cosh_sub,
    flatGapEdge_eq_cosh_sub]
  ring

/-- Grade differentiation of the flat one-particle potential. -/
theorem hasDerivAt_cosh_grade (x g : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cosh (t * x))
      (x * Real.sinh (g * x)) g := by
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
    (Real.hasDerivAt_cosh (g * x)).comp g
      ((hasDerivAt_id g).mul_const x)

private theorem exp_slope_right (a : ℝ) :
    Tendsto (fun e : ℝ => (Real.exp (a * e) - 1) / e)
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  have hd : HasDerivAt (fun e : ℝ => Real.exp (a * e)) a 0 := by
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_exp (a * (0 : ℝ))).comp 0
        ((hasDerivAt_id (0 : ℝ)).const_mul a)
  have hsub : Set.Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := by
    intro e he
    simp only [Set.mem_Ioi, Set.mem_compl_iff, Set.mem_singleton_iff] at he ⊢
    exact ne_of_gt he
  have h := hd.tendsto_slope_zero.mono_left (nhdsWithin_mono 0 hsub)
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- Normalization at coincidence fixes the continuous exponential gap
cocycle. This is the analytic rigidity step in the prime-only flat-completion
argument; prime-ratio density supplies the cocycle itself. -/
theorem exponentialGapCocycle_rigidity (a : ℝ) (ha : 0 < a) (A : ℝ → ℝ)
    (hcoc : ∀ d e : ℝ, 0 < d → 0 < e →
      A (d + e) = A d + Real.exp (a * d) * A e)
    (hnorm : Tendsto (fun e : ℝ => A e / e)
      (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    ∀ d : ℝ, 0 < d → A d = (Real.exp (a * d) - 1) / a := by
  intro d hd
  have hcross (e : ℝ) (he : 0 < e) :
      A d * (Real.exp (a * e) - 1) =
        A e * (Real.exp (a * d) - 1) := by
    have h1 := hcoc d e hd he
    have h2 := hcoc e d he hd
    rw [add_comm e d] at h2
    nlinarith
  have hquot (e : ℝ) (he : 0 < e) :
      A d * ((Real.exp (a * e) - 1) / e) =
        (A e / e) * (Real.exp (a * d) - 1) := by
    apply (mul_right_cancel₀ he.ne')
    field_simp [he.ne']
    exact hcross e he
  have hevent :
      (fun e : ℝ => A d * ((Real.exp (a * e) - 1) / e)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun e : ℝ => (A e / e) * (Real.exp (a * d) - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with e he
    exact hquot e he
  have hleft : Tendsto (fun e : ℝ => A d * ((Real.exp (a * e) - 1) / e))
      (𝓝[>] (0 : ℝ)) (𝓝 (A d * a)) :=
    tendsto_const_nhds.mul (exp_slope_right a)
  have hright : Tendsto (fun e : ℝ => (A e / e) * (Real.exp (a * d) - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 * (Real.exp (a * d) - 1))) :=
    hnorm.mul tendsto_const_nhds
  have heq : A d * a = 1 * (Real.exp (a * d) - 1) :=
    tendsto_nhds_unique (hleft.congr' hevent) hright
  apply (eq_div_iff ha.ne').2
  simpa only [one_mul, mul_comm] using heq

end

end HTGeometry
