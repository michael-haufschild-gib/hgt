import GaloisForLFunctions.RHTower.Sieve.DampedTwistPerron
import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistEdgeAssembly

/-!
# The twisted damped smoothed sum, bounded by the four edges

The damped analogue of `Sieve/MoebiusTwistEdgeAssembly`.  The shifted integrand
`s ↦ dampedInvZeta P t (s + iτ) · W s` is the shifted `invZeta` integrand times the shifted Euler
correction, and the latter is holomorphic on the rectangle because `Re (s + iτ) = Re s > 0` there.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

/-- The shifted Euler correction is holomorphic on the rectangle. -/
theorem differentiableOn_prod_dampedEulerFactor_shift_rect {P : Finset ℕ}
    (hP : ∀ q ∈ P, 2 ≤ q) (t τ : ℝ) {c d T : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    DifferentiableOn ℂ
      (fun s => ∏ p ∈ P, dampedEulerFactor t p (s + (τ : ℂ) * Complex.I))
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | insert a Q ha ih =>
      have hfun : (fun s : ℂ => ∏ p ∈ insert a Q, dampedEulerFactor t p (s + (τ : ℂ) * Complex.I))
          = fun s : ℂ => dampedEulerFactor t a (s + (τ : ℂ) * Complex.I)
            * ∏ p ∈ Q, dampedEulerFactor t p (s + (τ : ℂ) * Complex.I) := by
        funext s
        rw [Finset.prod_insert ha]
      rw [hfun]
      have ha2 : 2 ≤ a := hP a (Finset.mem_insert_self a Q)
      have hone : DifferentiableOn ℂ
          (fun s : ℂ => dampedEulerFactor t a (s + (τ : ℂ) * Complex.I))
          (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
        have hpow : DifferentiableOn ℂ
            (fun s : ℂ => ((a : ℂ)) ^ (-(s + (τ : ℂ) * Complex.I)))
            (Set.uIcc c d ×ℂ Set.uIcc (-T) T) :=
          ((differentiable_natCast_cpow_neg ha2).comp
            (differentiable_id.add_const _)).differentiableOn
        have hne : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T,
            (1 : ℂ) - ((a : ℂ)) ^ (-(s + (τ : ℂ) * Complex.I)) ≠ 0 := by
          intro s hs
          have hre : s.re ∈ Set.uIcc c d := hs.1
          rw [Set.uIcc_of_le hcd, Set.mem_Icc] at hre
          refine one_sub_cpow_ne_zero_of_pos_re ha2 ?_
          have : (s + (τ : ℂ) * Complex.I).re = s.re := by simp
          rw [this]
          linarith [hre.1]
        exact ((differentiableOn_const (1 : ℂ)).sub (hpow.const_mul ((t : ℝ) : ℂ))).div
          ((differentiableOn_const (1 : ℂ)).sub hpow) hne
      exact hone.mul (ih (fun q hq => hP q (Finset.mem_insert_of_mem hq)))

/-- **The shifted damped integrand is holomorphic on the rectangle.** -/
theorem differentiableOn_dampedInvZetaTwistW_rect {P : Finset ℕ} (hP : ∀ q ∈ P, 2 ≤ q)
    (t τ : ℝ) {N H : ℝ} (hH : 0 < H) {c d T : ℝ} (hc : 0 < c) (hcd : c ≤ d) (hT : 0 ≤ T)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ
      (fun s => dampedInvZeta P t (s + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s)
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
  have hbase := differentiableOn_invZetaTwistW_rect (N := N) hH τ hc hcd hT hzf
  have hprod := differentiableOn_prod_dampedEulerFactor_shift_rect hP t τ (T := T) hc hcd
  have hfun : (fun s : ℂ => dampedInvZeta P t (s + (τ : ℂ) * Complex.I)
      * mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s)
      = fun s : ℂ => (invZeta (s + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s)
        * ∏ p ∈ P, dampedEulerFactor t p (s + (τ : ℂ) * Complex.I) := by
    funext s
    rw [dampedInvZeta]
    ring
  rw [hfun]
  exact hbase.mul hprod

end

end RHTower.Sieve
