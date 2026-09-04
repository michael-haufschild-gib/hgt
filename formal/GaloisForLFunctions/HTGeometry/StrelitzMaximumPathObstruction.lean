import GaloisForLFunctions.HTGeometry.StrelitzMaximumPathDerivative
import GaloisForLFunctions.HTGeometry.StrelitzSublinearDerivativeObstruction

/-!
# Sublinear obstruction on a smooth maximum-modulus path

The exact maximum-path derivative is `normSq(v) / Re(v)`.  In the open right half-plane this is
at least `‖v‖`.  Consequently any nonzero limit of the second jet after normalization by a
nonnegative power of the first jet gives a fixed positive derivative floor, including the boundary
case where the limiting edge root has zero real part.  Such a branch cannot remain sublinear.
-/

open Set Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- In the open right half-plane, the Strelitz maximum-path derivative dominates the norm of the
second Euler jet. -/
theorem norm_le_normSq_div_re {v : ℂ} (hv : 0 < v.re) :
    ‖v‖ ≤ Complex.normSq v / v.re := by
  rw [le_div_iff₀ hv]
  rw [← Complex.sq_norm]
  have hre : v.re ≤ ‖v‖ :=
    (le_abs_self v.re).trans (Complex.abs_re_le_norm v)
  simpa [pow_two, mul_comm] using
    (mul_le_mul_of_nonneg_right hre (norm_nonneg v))

/-- A nonzero normalized second jet in the open right half-plane forces a positive derivative
floor, even when its limiting real part vanishes. -/
theorem not_tendsto_div_zero_of_normalized_rightHalfPlane_secondJet
    {K : ℝ → ℝ} {v : ℝ → ℂ} {x0 p : ℝ} {c : ℂ}
    (hcont : ContinuousOn K (Ici x0))
    (hderiv : ∀ x ∈ Ioi x0,
      HasDerivAt K (Complex.normSq (v x) / (v x).re) x)
    (hKTop : Tendsto K atTop atTop)
    (hp : 0 ≤ p) (hc : c ≠ 0)
    (hvpos : ∀ x ∈ Ioi x0, 0 < (v x).re)
    (hnormalized : Tendsto (fun x => v x / ((K x ^ p : ℝ) : ℂ)) atTop (nhds c)) :
    ¬ Tendsto (fun x => K x / x) atTop (nhds 0) := by
  have hcNorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hnorm : ∀ᶠ x : ℝ in atTop,
      ‖c‖ / 2 < ‖v x / ((K x ^ p : ℝ) : ℂ)‖ :=
    (tendsto_order.1 hnormalized.norm).1 _ (by linarith)
  have hKone : ∀ᶠ x : ℝ in atTop, 1 ≤ K x := hKTop.eventually_ge_atTop 1
  obtain ⟨x1, hx1⟩ := eventually_atTop.1 (hnorm.and hKone)
  let x2 := max x0 x1
  have hK2 : 0 ≤ K x2 := by
    exact zero_le_one.trans (hx1 x2 (le_max_right _ _)).2
  have hcont2 : ContinuousOn K (Ici x2) :=
    hcont.mono fun x hx => (le_max_left x0 x1).trans hx
  have hderiv2 : ∀ x ∈ Ioi x2,
      HasDerivAt K (Complex.normSq (v x) / (v x).re) x := by
    intro x hx
    exact hderiv x ((le_max_left x0 x1).trans_lt hx)
  have hlower2 : ∀ x ∈ Ioi x2,
      ‖c‖ / 2 ≤ Complex.normSq (v x) / (v x).re := by
    intro x hx
    have hx0 : x ∈ Ioi x0 := (le_max_left x0 x1).trans_lt hx
    have hx1' : x1 ≤ x := (le_max_right x0 x1).trans hx.le
    have hKx : 1 ≤ K x := (hx1 x hx1').2
    have hKpos : 0 < K x := zero_lt_one.trans_le hKx
    have hpowPos : 0 < K x ^ p := Real.rpow_pos_of_pos hKpos p
    have hpowOne : 1 ≤ K x ^ p := Real.one_le_rpow hKx hp
    have hnorm' := (hx1 x hx1').1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpowPos] at hnorm'
    have hscaled : ‖c‖ / 2 * K x ^ p < ‖v x‖ :=
      (lt_div_iff₀ hpowPos).mp hnorm'
    have hbase : ‖c‖ / 2 ≤ ‖v x‖ := by
      have hcHalf : 0 ≤ ‖c‖ / 2 := div_nonneg (norm_nonneg c) (by norm_num)
      simpa using (mul_le_mul_of_nonneg_left hpowOne hcHalf).trans hscaled.le
    exact hbase.trans (norm_le_normSq_div_re (hvpos x hx0))
  exact not_tendsto_div_zero_of_deriv_ge_pos hK2 (by positivity) hcont2 hderiv2 hlower2

variable {a : ℕ → ℂ}

/-- A smooth maximum-modulus branch with a nonzero nonnegative-power normalized second-jet limit
cannot have sublinear first Euler jet. -/
theorem not_tendsto_div_zero_of_strelitzMaximumPath_normalizedSecondJet
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {θ θ' : ℝ → ℝ} {x0 p : ℝ} {c : ℂ}
    (hθ : ∀ x ∈ Ici x0, HasDerivAt θ (θ' x) x)
    (hmax : ∀ x ∈ Ici x0, ∀ᶠ s : ℝ in nhds x,
      strelitzLogPolarPath θ s ∈ circleMaximumSet (coeffFun a))
    (hvpos : ∀ x ∈ Ici x0,
      0 < (eulerLogDerivSecond (coeffFun a) (strelitzLogPolarPath θ x)).re)
    (hKTop : Tendsto
      (fun x => (eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ x)).re)
      atTop atTop)
    (hp : 0 ≤ p) (hc : c ≠ 0)
    (hnormalized : Tendsto (fun x =>
      eulerLogDerivSecond (coeffFun a) (strelitzLogPolarPath θ x) /
        ((((eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ x)).re ^ p : ℝ) : ℂ)))
      atTop (nhds c)) :
    ¬ Tendsto (fun x =>
      (eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ x)).re / x)
      atTop (nhds 0) := by
  let K : ℝ → ℝ := fun x =>
    (eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ x)).re
  let v : ℝ → ℂ := fun x =>
    eulerLogDerivSecond (coeffFun a) (strelitzLogPolarPath θ x)
  have hderivAll : ∀ x ∈ Ici x0,
      HasDerivAt K (Complex.normSq (v x) / (v x).re) x := by
    intro x hx
    exact hasDerivAt_re_eulerLogDeriv_strelitzMaximumPath
      ha hn₀ (hθ x hx) (hmax x hx) (hvpos x hx)
  have hcont : ContinuousOn K (Ici x0) := by
    intro x hx
    exact (hderivAll x hx).continuousAt.continuousWithinAt
  exact not_tendsto_div_zero_of_normalized_rightHalfPlane_secondJet
    hcont (fun x hx => hderivAll x (show x0 ≤ x from hx.le)) hKTop hp hc
      (fun x hx => hvpos x (show x0 ≤ x from hx.le)) hnormalized

end

end GaloisForLFunctions.HTGeometry
