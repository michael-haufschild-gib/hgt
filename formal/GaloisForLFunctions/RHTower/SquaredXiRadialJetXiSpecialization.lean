import GaloisForLFunctions.RHTower.CompletedRadialSourcePolynomial
import GaloisForLFunctions.RHTower.SquaredXiRadialJetIdentity
import GaloisForLFunctions.RHTower.SquaredXiCompleteMonotonicity

/-!
# The radial-jet identity for the completed Xi

The abstract radial-jet identity holds for any globally smooth real profile.  The completed Xi
logarithmic derivative is such a profile: `xi` is entire and has no zero on the real axis, so its
real logarithmic derivative is smooth at every order on all of `ℝ`.

Specializing the identity gives the card's completed source polynomial

`Q_n w = sum_j (-1)^j b_{n,j} w^j L^(j)(1/2 + w)`,   `L = xi'/xi`,

together with its exact radial meaning: the radial operator `D = (2w)^{-1} d/dw` iterated `n` times
on the profile `F w = L(1/2+w)/w` is twice the `n`-th derivative of the squared-coordinate field
`g y = xi'(1/2+sqrt y)/(2 sqrt y * xi(1/2+sqrt y))` at `y = w^(2 : ℕ)`.  Hence

`Q_n w = (-1)^n 2^{n+1} w^{2n+1} g^{(n)}(w^(2 : ℕ))`,

so `Q_n w < 0` and `(-1)^n g^{(n)}(w^(2 : ℕ)) < 0` are the same statement.  Combined with the
unconditional complete monotonicity of `g` through order eighteen, this makes the completed source
jet strictly positive at every positive radius through that order: the order-fourteen witness
window of the reduction is empty.
-/

open Set Filter

namespace RHTower

noncomputable section

/-! ### Global smoothness of the Xi logarithmic derivative on the real axis -/

/-- `xi` has no zero on the real axis. -/
theorem xi_ofReal_ne_zero (x : ℝ) : xi (x : ℂ) ≠ 0 := by
  have h := xi_ofReal_shift_ne_zero (x - 1 / 2)
  have hcast : (1 : ℂ) / 2 + ((x - 1 / 2 : ℝ) : ℂ) = (x : ℂ) := by push_cast; ring
  rwa [hcast] at h

/-- The real trace of `xi'/xi` is smooth at every order on the whole real axis: `xi` is entire and
zero-free there, so `xi'/xi` is holomorphic on an open neighbourhood of `ℝ`. -/
theorem contDiff_xiRayLogDeriv (n : WithTop ℕ∞) : ContDiff ℝ n xiRayLogDeriv := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hopen : IsOpen {z : ℂ | xi z ≠ 0} := isOpen_ne.preimage xi_differentiable.continuous
  have hdiff : DifferentiableOn ℂ xiLogDeriv {z : ℂ | xi z ≠ 0} := by
    intro z hz
    have hd : DifferentiableAt ℂ (deriv xi) z := xi_differentiable.deriv z
    exact (hd.div (xi_differentiable z) hz).differentiableWithinAt
  exact GaloisForLFunctions.HTGeometry.contDiffAt_re_comp_ofReal hopen hdiff
    (xi_ofReal_ne_zero x) n

/-! ### The radial profile of the Xi logarithmic derivative -/

theorem xiRayLogDeriv_shift (v : ℝ) : xiRayLogDeriv (1 / 2 + v) = xiRealLogDeriv v := by
  have hcast : (((1 / 2 + v : ℝ)) : ℂ) = 1 / 2 + (v : ℂ) := by push_cast; ring
  rw [xiRayLogDeriv, xiRealLogDeriv, hcast]
  rfl

theorem radialProfile_xiRayLogDeriv {v : ℝ} (hv : 0 < v) :
    radialProfile xiRayLogDeriv v = 2 * squaredXiRadialField (v ^ (2 : ℕ)) := by
  have hv0 : v ≠ 0 := ne_of_gt hv
  rw [radialProfile, xiRayLogDeriv_shift, squaredXiRadialField_sq_eq hv]
  field_simp

/-! ### The radial operator -/

theorem radialOp_iterate_congr_of_pos (n : ℕ) {f g : ℝ → ℝ}
    (h : ∀ v : ℝ, 0 < v → f v = g v) : ∀ {w : ℝ}, 0 < w →
      (radialOp)^[n] f w = (radialOp)^[n] g w := by
  induction n with
  | zero =>
      intro w hw
      simpa using h w hw
  | succ n ih =>
      intro w hw
      have hEq : (radialOp)^[n] f =ᶠ[nhds w] (radialOp)^[n] g := by
        filter_upwards [Ioi_mem_nhds hw] with v hv using ih hv
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', radialOp, radialOp,
        hEq.deriv_eq]

theorem radialOp_iterate_const_mul (n : ℕ) (c : ℝ) (g : ℝ → ℝ) (w : ℝ) :
    (radialOp)^[n] (fun v => c * g v) w = c * (radialOp)^[n] g w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', radialOp, radialOp,
        show (radialOp)^[n] (fun v => c * g v) = fun v => c * (radialOp)^[n] g v from funext ih,
        deriv_const_mul_field]
      ring

/-- Every iterated derivative of the squared-coordinate field is again differentiable on the
positive ray. -/
theorem hasDerivAt_iteratedDeriv_squaredXiRadialField (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (iteratedDeriv n squaredXiRadialField)
      (iteratedDeriv (n + 1) squaredXiRadialField y) y := by
  have hEq : iteratedDeriv n squaredXiRadialField =ᶠ[nhds y]
      (fun v : ℝ => (-1 : ℝ) ^ n * (n.factorial : ℝ) / 2 *
        (xiShiftedReciprocalMoment v n).re) := by
    filter_upwards [Ioi_mem_nhds hy] with v hv using iteratedDeriv_squaredXiRadialField n hv
  have hd := (hasDerivAt_re_xiShiftedReciprocalMoment hy n).const_mul
    ((-1 : ℝ) ^ n * (n.factorial : ℝ) / 2)
  have hval : iteratedDeriv (n + 1) squaredXiRadialField y
      = (-1 : ℝ) ^ n * (n.factorial : ℝ) / 2 *
          (-((n : ℝ) + 1) * (xiShiftedReciprocalMoment y (n + 1)).re) := by
    rw [iteratedDeriv_succ, hEq.deriv_eq, hd.deriv]
  rw [hval]
  exact hd.congr_of_eventuallyEq hEq

/-- The radial operator is the pullback of `d/dy` under `y = w^(2 : ℕ)`. -/
theorem radialOp_iterate_comp_sq (n : ℕ) : ∀ {w : ℝ}, 0 < w →
    (radialOp)^[n] (fun v : ℝ => squaredXiRadialField (v ^ (2 : ℕ))) w
      = iteratedDeriv n squaredXiRadialField (w ^ (2 : ℕ)) := by
  induction n with
  | zero =>
      intro w _
      simp
  | succ n ih =>
      intro w hw
      have hw0 : w ≠ 0 := ne_of_gt hw
      have hEq : (radialOp)^[n] (fun v : ℝ => squaredXiRadialField (v ^ (2 : ℕ))) =ᶠ[nhds w]
          fun v : ℝ => iteratedDeriv n squaredXiRadialField (v ^ (2 : ℕ)) := by
        filter_upwards [Ioi_mem_nhds hw] with v hv using ih hv
      have hsq : HasDerivAt (fun v : ℝ => v ^ (2 : ℕ)) (2 * w) w := by
        simpa using hasDerivAt_pow 2 w
      have hcomp : HasDerivAt (fun v : ℝ => iteratedDeriv n squaredXiRadialField (v ^ (2 : ℕ)))
          (iteratedDeriv (n + 1) squaredXiRadialField (w ^ (2 : ℕ)) * (2 * w)) w :=
        HasDerivAt.comp w (hasDerivAt_iteratedDeriv_squaredXiRadialField n (by positivity)) hsq
      rw [Function.iterate_succ_apply', radialOp, hEq.deriv_eq, hcomp.deriv]
      field_simp

/-- **Equation (4) for the completed Xi.**  The iterated radial operator on the profile of
`xi'/xi` is twice the `n`-th derivative of the squared-coordinate field. -/
theorem radialOp_iterate_radialProfile_xi (n : ℕ) {w : ℝ} (hw : 0 < w) :
    (radialOp)^[n] (radialProfile xiRayLogDeriv) w
      = 2 * iteratedDeriv n squaredXiRadialField (w ^ (2 : ℕ)) := by
  rw [radialOp_iterate_congr_of_pos n (g := fun v : ℝ => 2 * squaredXiRadialField (v ^ (2 : ℕ)))
      (fun v hv => radialProfile_xiRayLogDeriv hv) hw,
    radialOp_iterate_const_mul n 2 (fun v : ℝ => squaredXiRadialField (v ^ (2 : ℕ))) w,
    radialOp_iterate_comp_sq n hw]

/-! ### The completed source polynomial -/

/-- The completed source polynomial `Q_n w = sum_j (-1)^j b_{n,j} w^j L^(j)(1/2+w)` of the
reduction, with `L = xi'/xi`. -/
def completedSourceJet (n : ℕ) (w : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ j * (squaredRadialJetWeight n j : ℝ) * w ^ j *
      iteratedDeriv j xiRayLogDeriv (1 / 2 + w)

/-- **Equations (4)–(5) and (7) for the completed Xi.**  The completed source polynomial is the
positively rescaled alternating squared-coordinate derivative of the radial field, so `Q_n w < 0`
and `(-1)^n g^(n)(w^(2 : ℕ)) < 0` are the same statement. -/
theorem completedSourceJet_eq (n : ℕ) {w : ℝ} (hw : 0 < w) :
    completedSourceJet n w
      = (-1 : ℝ) ^ n * 2 ^ (n + 1) * w ^ (2 * n + 1) *
          iteratedDeriv n squaredXiRadialField (w ^ (2 : ℕ)) := by
  rw [completedSourceJet, ← radialJet_positive_rescaling (contDiff_xiRayLogDeriv ⊤) n w hw,
    radialOp_iterate_radialProfile_xi n hw]
  ring

/-- **The completed source jet is strictly positive through order eighteen**, at every positive
radius and unconditionally.  No negative witness exists below order nineteen. -/
theorem completedSourceJet_pos {n : ℕ} (hn : n ≤ 18) {w : ℝ} (hw : 0 < w) :
    0 < completedSourceJet n w := by
  have hy : (0:ℝ) < w ^ (2 : ℕ) := by positivity
  have hpos := alternating_iteratedDeriv_squaredXiRadialField_pos hy hn
  have hscale : (0:ℝ) < 2 ^ (n + 1) * w ^ (2 * n + 1) := by positivity
  rw [completedSourceJet_eq n hw,
    show (-1 : ℝ) ^ n * 2 ^ (n + 1) * w ^ (2 * n + 1) *
        iteratedDeriv n squaredXiRadialField (w ^ (2 : ℕ))
      = (2 ^ (n + 1) * w ^ (2 * n + 1)) *
        ((-1 : ℝ) ^ n * iteratedDeriv n squaredXiRadialField (w ^ (2 : ℕ))) from by ring]
  exact mul_pos hscale hpos

/-- **The order-fourteen witness window is empty.**  The reduction's target inequality
`Q_14 w < 0` fails at every positive radius. -/
theorem completedSourceJet_orderFourteen_pos {w : ℝ} (hw : 0 < w) :
    0 < completedSourceJet 14 w :=
  completedSourceJet_pos (by norm_num) hw

theorem not_completedSourceJet_neg_of_le_eighteen {n : ℕ} (hn : n ≤ 18) {w : ℝ} (hw : 0 < w) :
    ¬ completedSourceJet n w < 0 :=
  not_lt.mpr (completedSourceJet_pos hn hw).le

end

end RHTower
