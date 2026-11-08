import GaloisForLFunctions.ZeroConfigurationGeometry.HeatTimeSpreadsTheConfiguration
import GaloisForLFunctions.Bottcher.AlgebraicBranch
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The velocity of a polynomial heat zero

The finite heat series satisfies the backward heat equation in complex time.
The analytic implicit-function theorem therefore gives each simple zero a
branch whose velocity is the quotient of the second and first spatial
derivatives. Factoring the polynomial identifies this quotient with the
reciprocal field of the remaining zeros.
-/

open Polynomial Filter Topology
open GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

private theorem heatFlow_eq_initial_add (t : ℂ) (p : ℂ[X]) :
    heatFlow t p = p + ∑ k ∈ Finset.range p.natDegree,
      C ((-t) ^ (k + 1) / ((k + 1).factorial : ℂ)) * derivative^[2 * (k + 1)] p := by
  rw [heatFlow, Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, C_1, one_mul,
    mul_zero, Function.iterate_zero, id_eq]
  ring

private theorem heatFlow_spatial_second (t z : ℂ) (p : ℂ[X]) :
    ((heatFlow t p).derivative.derivative).eval z =
      ∑ k ∈ Finset.range p.natDegree,
        ((-t) ^ k / (k.factorial : ℂ)) * (derivative^[2 * (k + 1)] p).eval z := by
  have hi (k : ℕ) : derivative (derivative (derivative^[2 * k] p)) =
      derivative^[2 * (k + 1)] p := by
    rw [show 2 * (k + 1) = 2 + 2 * k by omega, Function.iterate_add_apply]
    rfl
  simp only [heatFlow, derivative_sum, derivative_C_mul, eval_finsetSum,
    eval_mul, eval_C, hi]
  rw [Finset.sum_range_succ, iterate_derivative_eq_zero (by omega), eval_zero,
    mul_zero, add_zero]

private theorem hasDerivAt_heat_coefficient_succ (k : ℕ) (t : ℂ) :
    HasDerivAt (fun u : ℂ => (-u) ^ (k + 1) / ((k + 1).factorial : ℂ))
      (-((-t) ^ k / (k.factorial : ℂ))) t := by
  have hd := (((hasDerivAt_id t).neg).pow (k + 1)).div_const ((k + 1).factorial : ℂ)
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq] at hd
  refine hd.congr_deriv ?_
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp

/-- The polynomial heat series satisfies the backward heat equation at every complex time. -/
theorem hasDerivAt_heatFlow_eval_time (p : ℂ[X]) (t z : ℂ) :
    HasDerivAt (fun u : ℂ => (heatFlow u p).eval z)
      (-((heatFlow t p).derivative.derivative).eval z) t := by
  have hs := HasDerivAt.sum (u := Finset.range p.natDegree)
    (fun k _ => (hasDerivAt_heat_coefficient_succ k t).mul_const
      ((derivative^[2 * (k + 1)] p).eval z))
  have hd := (hasDerivAt_const t (p.eval z)).add hs
  have hd' := hd.congr_deriv (show
      (0 + ∑ k ∈ Finset.range p.natDegree,
        -((-t) ^ k / (k.factorial : ℂ)) * (derivative^[2 * (k + 1)] p).eval z) =
        -((heatFlow t p).derivative.derivative).eval z by
    rw [heatFlow_spatial_second, zero_add]
    simp only [neg_mul, Finset.sum_neg_distrib])
  apply hd'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun u => by
    simp only [heatFlow_eq_initial_add, eval_add, eval_finsetSum, eval_mul, eval_C,
      Finset.sum_apply, Pi.add_apply]

/-- Joint analyticity of polynomial heat in its time and space variables. -/
theorem contDiff_heatFlow_eval (p : ℂ[X]) :
    ContDiff ℂ ⊤ (fun u : ℂ × ℂ => (heatFlow u.1 p).eval u.2) := by
  simp only [heatFlow, eval_finsetSum, eval_mul, eval_C]
  apply ContDiff.sum
  intro k _
  have hpoly : ContDiff ℂ ⊤ (fun u : ℂ × ℂ => (aeval u.2) (derivative^[2 * k] p)) :=
    (Polynomial.contDiff_aeval (𝕜 := ℂ) (derivative^[2 * k] p) ⊤).comp contDiff_snd
  have hc : ContDiff ℂ ⊤ (fun u : ℂ × ℂ => (-u.1) ^ k / (k.factorial : ℂ)) := by
    fun_prop
  simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using
    hc.mul hpoly

#print axioms hasDerivAt_heatFlow_eval_time
#print axioms contDiff_heatFlow_eval

/-- Every simple polynomial heat zero lies on an analytic branch with the
velocity forced by the backward heat equation. -/
theorem exists_analytic_polynomial_heat_zero_branch (p : ℂ[X]) {t a : ℂ}
    (hz : (heatFlow t p).eval a = 0)
    (hsimple : (heatFlow t p).derivative.eval a ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g t ∧ g t = a ∧
      HasDerivAt g (((heatFlow t p).derivative.derivative).eval a /
        (heatFlow t p).derivative.eval a) t ∧
      ∀ᶠ u in 𝓝 t, (heatFlow u p).eval (g u) = 0 := by
  let F : ℂ × ℂ → ℂ := fun u => (heatFlow u.1 p).eval u.2
  have hF : ContDiff ℂ ⊤ F := contDiff_heatFlow_eval p
  obtain ⟨g, hg, hg0, hroot⟩ := Bottcher.exists_analyticAt_branch_of_hasDerivAt
    hF.contDiffAt hz ((heatFlow t p).hasDerivAt a) hsimple
  let L := fderiv ℂ F (t, a)
  have hL : HasFDerivAt F L (t, a) :=
    (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
  have htime : L (1, 0) = -((heatFlow t p).derivative.derivative).eval a := by
    have h := hL.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t a))
    exact h.unique (hasDerivAt_heatFlow_eval_time p t a)
  have hspace : L (0, 1) = (heatFlow t p).derivative.eval a := by
    have h := hL.comp_hasDerivAt a
      ((hasDerivAt_const a t).prodMk (hasDerivAt_id a))
    exact h.unique ((heatFlow t p).hasDerivAt a)
  have hLbase : HasFDerivAt F L (t, g t) := by rwa [hg0]
  have hgder := hg.differentiableAt.hasDerivAt
  have hchain := hLbase.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hgder)
  have hzero : HasDerivAt (fun u => F (u, g u)) 0 t :=
    (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq hroot
  have hlinzero : L (1, deriv g t) = 0 := hchain.unique hzero
  have hsplit : L (1, deriv g t) = L (1, 0) + deriv g t * L (0, 1) := by
    rw [show ((1, deriv g t) : ℂ × ℂ) =
      (1, 0) + deriv g t • (0, 1) by ext <;> simp,
      map_add, map_smul]
    rfl
  rw [hsplit, htime, hspace] at hlinzero
  have hv : deriv g t = ((heatFlow t p).derivative.derivative).eval a /
      (heatFlow t p).derivative.eval a := by
    apply (eq_div_iff hsimple).mpr
    linear_combination hlinzero
  exact ⟨g, hg, hg0, by rw [← hv]; exact hgder, hroot⟩

/-- Restricting complex time gives the actual real-time zero velocity. -/
theorem exists_polynomial_heat_zero_branch (p : ℂ[X]) {t : ℝ} {a : ℂ}
    (hz : (heatFlow (t : ℂ) p).eval a = 0)
    (hsimple : (heatFlow (t : ℂ) p).derivative.eval a ≠ 0) :
    ∃ g : ℝ → ℂ, g t = a ∧
      HasDerivAt g (((heatFlow (t : ℂ) p).derivative.derivative).eval a /
        (heatFlow (t : ℂ) p).derivative.eval a) t ∧
      ∀ᶠ u : ℝ in 𝓝 t, (heatFlow (u : ℂ) p).eval (g u) = 0 := by
  obtain ⟨g, _, hg0, hgd, hroot⟩ := exists_analytic_polynomial_heat_zero_branch p hz hsimple
  exact ⟨fun u => g (u : ℂ), hg0, hgd.comp_ofReal,
    Complex.continuous_ofReal.continuousAt.tendsto.eventually hroot⟩

#print axioms exists_analytic_polynomial_heat_zero_branch
#print axioms exists_polynomial_heat_zero_branch

/-- At a root of a finite product, the second derivative is twice the first
derivative times the reciprocal field of the other roots. -/
theorem eval_second_derivative_finset_roots (S : Finset ℂ) {a : ℂ} (ha : a ∈ S) :
    (derivative (derivative (∏ b ∈ S, (X - C b)))).eval a =
      2 * (derivative (∏ b ∈ S, (X - C b))).eval a *
        ∑ b ∈ S.erase a, (a - b)⁻¹ := by
  classical
  let Q := ∏ b ∈ S.erase a, (X - C b)
  have hfac : (∏ b ∈ S, (X - C b)) = (X - C a) * Q :=
    (Finset.mul_prod_erase S _ ha).symm
  have hQ : Q.derivative.eval a = Q.eval a * ∑ b ∈ S.erase a, (a - b)⁻¹ := by
    dsimp only [Q]
    rw [derivative_prod_finset, eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [derivative_X_sub_C, mul_one, eval_prod, eval_prod]
    have hn : a - b ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hb).1.symm
    have hprod : (∏ c ∈ S.erase a, eval a (X - C c)) =
        (∏ c ∈ (S.erase a).erase b, eval a (X - C c)) * (a - b) := by
      simpa only [eval_sub, eval_X, eval_C] using
        (Finset.prod_erase_mul (S.erase a) (fun c : ℂ => eval a ((X : ℂ[X]) - C c)) hb).symm
    rw [hprod, mul_assoc, mul_inv_cancel₀ hn, mul_one]
  rw [hfac, derivative_mul, derivative_X_sub_C, one_mul, derivative_add,
    derivative_mul, derivative_X_sub_C, one_mul]
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  rw [hQ]
  ring

/-- For a polynomial with distinct roots, its heat-velocity quotient is the
full reciprocal field; the self term is zero under totalized inversion. -/
theorem polynomial_heat_quotient_eq_reciprocal_field {p : ℂ[X]} {a : ℂ}
    (hnodup : p.roots.Nodup) (ha : a ∈ p.roots)
    (hsimple : p.derivative.eval a ≠ 0) :
    p.derivative.derivative.eval a / p.derivative.eval a =
      2 * ∑ b ∈ p.roots.toFinset, (a - b)⁻¹ := by
  classical
  let S := p.roots.toFinset
  let P := ∏ b ∈ S, (X - C b)
  have haS : a ∈ S := Multiset.mem_toFinset.mpr ha
  have hroots : p.roots = S.val := by
    change p.roots = p.roots.toFinset.val
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  have hfac : p = C p.leadingCoeff * P := by
    have h := (IsAlgClosed.splits p).eq_prod_roots
    rw [hroots] at h
    exact h
  have hfirst : p.derivative.eval a = p.leadingCoeff * P.derivative.eval a := by
    conv_lhs => rw [hfac, derivative_C_mul, eval_mul, eval_C]
  have hsecond : p.derivative.derivative.eval a =
      p.leadingCoeff * P.derivative.derivative.eval a := by
    conv_lhs => rw [hfac, derivative_C_mul, derivative_C_mul, eval_mul, eval_C]
  have hfield : (∑ b ∈ S.erase a, (a - b)⁻¹) = ∑ b ∈ S, (a - b)⁻¹ := by
    simpa only [sub_self, inv_zero, add_zero] using
      Finset.sum_erase_add S (fun b => (a - b)⁻¹) haS
  apply (div_eq_iff hsimple).mpr
  rw [hfirst, hsecond, show P.derivative.derivative.eval a =
    2 * P.derivative.eval a * ∑ b ∈ S.erase a, (a - b)⁻¹ from
      eval_second_derivative_finset_roots S haS, hfield]
  ring

/-- Actual simple polynomial heat branches move by twice the reciprocal field. -/
theorem exists_polynomial_heat_reciprocal_branch (p : ℂ[X]) {t : ℝ} {a : ℂ}
    (hnodup : (heatFlow (t : ℂ) p).roots.Nodup)
    (ha : a ∈ (heatFlow (t : ℂ) p).roots)
    (hsimple : (heatFlow (t : ℂ) p).derivative.eval a ≠ 0) :
    ∃ g : ℝ → ℂ, g t = a ∧
      HasDerivAt g (2 * ∑ b ∈ (heatFlow (t : ℂ) p).roots.toFinset, (a - b)⁻¹) t ∧
      ∀ᶠ u : ℝ in 𝓝 t, (heatFlow (u : ℂ) p).eval (g u) = 0 := by
  have hp : heatFlow (t : ℂ) p ≠ 0 := by
    intro h
    apply hsimple
    rw [h, derivative_zero, eval_zero]
  obtain ⟨g, hg0, hgd, hroot⟩ := exists_polynomial_heat_zero_branch p
    ((mem_roots hp).mp ha) hsimple
  rw [polynomial_heat_quotient_eq_reciprocal_field hnodup ha hsimple] at hgd
  exact ⟨g, hg0, hgd, hroot⟩

#print axioms polynomial_heat_quotient_eq_reciprocal_field
#print axioms exists_polynomial_heat_reciprocal_branch

end

end GaloisForLFunctions.ArithmeticElectrostatics
