import GaloisForLFunctions.HTGeometry.LinearSecondOrderComparison

/-!
# Uniform limits of a family of perturbed linear second-order equations

The Grönwall comparison bound is monotone in the endpoint, so it holds uniformly on the whole
window.  If the coefficient perturbations vanish along a filter, the solutions therefore converge
uniformly, and their integrals over the window converge with them.

The amplitude bound `B` enters linearly, so the estimate is useful exactly when the family's phase
pairs are uniformly bounded — which for a linear equation follows from its own a priori bound.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The comparison bound taken at the right endpoint dominates the whole window. -/
theorem phasePair_dist_le_uniform
    {u u' u'' v v' v'' P Pc Qc : ℝ → ℝ} {a b Lp εp εq B : ℝ} (hab : a ≤ b)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' (v'' x) x)
    (hequ : ∀ x ∈ Icc a b, u'' x = Pc x * u x + Qc x * u' x)
    (heqv : ∀ x ∈ Icc a b, v'' x = P x * v x)
    (hP : ∀ x ∈ Icc a b, |P x| ≤ Lp)
    (hεp : ∀ x ∈ Icc a b, |Pc x - P x| ≤ εp) (hεq : ∀ x ∈ Icc a b, |Qc x| ≤ εq)
    (hB : ∀ x ∈ Icc a b, max |u x| |u' x| ≤ B)
    (h0 : u a = v a) (h0' : u' a = v' a) :
    ∀ x ∈ Icc a b, max |u x - v x| |u' x - v' x|
      ≤ ((εp + εq) * B / max 1 Lp) * (Real.exp (max 1 Lp * (b - a)) - 1) := by
  have hεpn : (0 : ℝ) ≤ εp := le_trans (abs_nonneg _) (hεp a ⟨le_rfl, hab⟩)
  have hεqn : (0 : ℝ) ≤ εq := le_trans (abs_nonneg _) (hεq a ⟨le_rfl, hab⟩)
  have hBn : (0 : ℝ) ≤ B := le_trans (le_trans (abs_nonneg _) (le_max_left _ _))
    (hB a ⟨le_rfl, hab⟩)
  have hL1 : (1 : ℝ) ≤ max 1 Lp := le_max_left _ _
  have hLpos : (0 : ℝ) < max 1 Lp := lt_of_lt_of_le one_pos hL1
  have hcoef : (0 : ℝ) ≤ (εp + εq) * B / max 1 Lp := by positivity
  intro x hx
  refine le_trans (phasePair_dist_le hab hu hu' hv hv' hequ heqv hP hεp hεq hB h0 h0' x hx) ?_
  have hmono : Real.exp (max 1 Lp * (x - a)) ≤ Real.exp (max 1 Lp * (b - a)) := by
    apply Real.exp_le_exp.2
    have : x - a ≤ b - a := by linarith [hx.2]
    exact mul_le_mul_of_nonneg_left this hLpos.le
  exact mul_le_mul_of_nonneg_left (by linarith) hcoef

/-- **Uniform convergence.**  Vanishing coefficient perturbations force the solutions to converge
uniformly on the window, with the explicit Grönwall envelope. -/
theorem tendsto_sup_dist_of_coeff_tendsto
    {ι : Type*} {L : Filter ι} {Lp B a b : ℝ} {εp εq : ι → ℝ}
    (hεp : Tendsto εp L (𝓝 0)) (hεq : Tendsto εq L (𝓝 0)) :
    Tendsto (fun i => ((εp i + εq i) * B / max 1 Lp)
      * (Real.exp (max 1 Lp * (b - a)) - 1)) L (𝓝 0) := by
  have hsum : Tendsto (fun i => εp i + εq i) L (𝓝 0) := by
    simpa using hεp.add hεq
  have hscaled : Tendsto (fun i => (εp i + εq i) * B / max 1 Lp) L (𝓝 0) := by
    have := (hsum.mul_const B).div_const (max 1 Lp)
    simpa using this
  have := hscaled.mul_const (Real.exp (max 1 Lp * (b - a)) - 1)
  simpa using this

/-- A uniform pointwise bound on a difference bounds the difference of the integrals. -/
theorem abs_intervalIntegral_sub_le_of_uniform
    {f g : ℝ → ℝ} {a b E : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (uIcc a b)) (hg : ContinuousOn g (uIcc a b))
    (h : ∀ x ∈ Icc a b, |f x - g x| ≤ E) :
    |(∫ x in a..b, f x) - ∫ x in a..b, g x| ≤ E * (b - a) := by
  have hfi : IntervalIntegrable f MeasureTheory.volume a b := hf.intervalIntegrable
  have hgi : IntervalIntegrable g MeasureTheory.volume a b := hg.intervalIntegrable
  rw [← intervalIntegral.integral_sub hfi hgi]
  have hbound : ∀ x ∈ Set.uIoc a b, ‖f x - g x‖ ≤ E := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    exact h x ⟨le_of_lt hx.1, hx.2⟩
  have := intervalIntegral.norm_integral_le_of_norm_le_const (C := E) hbound
  rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at this

end GaloisForLFunctions.HTGeometry
