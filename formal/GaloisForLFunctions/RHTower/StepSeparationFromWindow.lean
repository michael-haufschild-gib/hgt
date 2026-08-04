import GaloisForLFunctions.RHTower.FloorAndLargeSelection
import GaloisForLFunctions.HTGeometry.PrefixStateIndependence
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval
import GaloisForLFunctions.HTGeometry.OneVariableMvPolynomial

/-!
# The separation reduced to a window comparison

The selection produces, for each window `[r, r+1]`, a point carrying a floor for the coefficient and a
value of the new state dominating any prescribed one.  What remains of a growth separation is then a
comparison on that window, with the point already given.

The analytic obligation therefore no longer involves constructing a point: only an inequality between
the floor, the joint scale of the earlier states and the new state's value has to be verified.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- **The separation from a window comparison.**  With the coefficient nonvanishing at the origin, a
comparison valid on some window for each level gives the growth separation. -/
theorem stepSeparation_of_window {m : ℕ} {X : Fin m → ℂ → ℂ} {F : ℂ → ℂ}
    (hXan : ∀ j : Fin m, AnalyticOnNhd ℂ (X j) (Set.univ : Set ℂ))
    (hFd : Differentiable ℂ F)
    (hcoeff0 : ∀ A : MvPolynomial (Fin m) ℂ, A ≠ 0 →
      MvPolynomial.eval (fun j => X j 0) A ≠ 0)
    (hwin : ∀ A : MvPolynomial (Fin m) ℂ, A ≠ 0 → ∀ c : ℝ, 0 ≤ c →
      ∃ (r : ℝ) (w : ℂ), 0 < r ∧ ‖w‖ ≤ r ∧
        ∀ (z : ℂ) (ε : ℝ), r ≤ ‖z‖ → ‖z‖ ≤ r + 1 → 0 < ε →
          ε ≤ ‖MvPolynomial.eval (fun j => X j z) A‖ → ‖F w‖ ≤ ‖F z‖ →
          c * (1 + (∑ j : Fin m, Real.posLog ‖X j z‖) + Real.posLog ε⁻¹)
            < Real.posLog ‖F z‖) :
    StepSeparation X F := by
  intro A hA c hc
  obtain ⟨r, w, hr, hw, hcomp⟩ := hwin A hA c hc
  have hgan : AnalyticOnNhd ℂ (fun z => MvPolynomial.eval (fun j => X j z) A)
      (Set.univ : Set ℂ) := analyticOnNhd_eval_mvPolynomial X hXan A
  obtain ⟨z, ε, hε0, hfloor, hlarge, hzr, hzr1⟩ :=
    exists_point_floor_and_large hgan (hcoeff0 A hA) hFd hr hw
  exact ⟨z, ε, hε0, hfloor, hcomp z ε hzr hzr1 hε0 hfloor hlarge⟩

/-- **The separation from a window comparison, with the correct nonvanishing hypothesis.**  Only that
each nonzero coefficient is not identically zero along the states is required — which is exactly the
independence of the earlier states.  The centre of the window is produced by the selection. -/
theorem stepSeparation_of_window_of_ne {m : ℕ} {X : Fin m → ℂ → ℂ} {F : ℂ → ℂ}
    (hXan : ∀ j : Fin m, AnalyticOnNhd ℂ (X j) (Set.univ : Set ℂ))
    (hFd : Differentiable ℂ F)
    (hcoeffne : ∀ A : MvPolynomial (Fin m) ℂ, A ≠ 0 →
      ∃ c : ℂ, MvPolynomial.eval (fun j => X j c) A ≠ 0)
    (hwin : ∀ A : MvPolynomial (Fin m) ℂ, A ≠ 0 → ∀ c : ℝ, 0 ≤ c →
      ∃ r : ℝ, 0 < r ∧
        ∀ (cen z : ℂ) (ε : ℝ), r ≤ ‖z - cen‖ → ‖z - cen‖ ≤ r + 1 → 0 < ε →
          ε ≤ ‖MvPolynomial.eval (fun j => X j z) A‖ →
          (∀ w : ℂ, ‖w - cen‖ ≤ r → ‖F w‖ ≤ ‖F z‖) →
          c * (1 + (∑ j : Fin m, Real.posLog ‖X j z‖) + Real.posLog ε⁻¹)
            < Real.posLog ‖F z‖) :
    StepSeparation X F := by
  intro A hA c hc
  obtain ⟨r, hr, hcomp⟩ := hwin A hA c hc
  have hgan : AnalyticOnNhd ℂ (fun z => MvPolynomial.eval (fun j => X j z) A)
      (Set.univ : Set ℂ) := analyticOnNhd_eval_mvPolynomial X hXan A
  obtain ⟨cen, z, ε, hε0, hfloor, h1, h2, hmax⟩ :=
    exists_point_floor_and_large_of_ne hgan (hcoeffne A hA) hFd hr
  exact ⟨z, ε, hε0, hfloor, hcomp cen z ε h1 h2 hε0 hfloor hmax⟩

/-! ## The induction with no independence hypothesis

The nonvanishing hypothesis of the window theorem is the induction's own conclusion one level down,
so the whole state-independence induction can be run from the window comparison alone. -/

/-- **State independence from window comparisons alone.** -/
theorem noRelation_prefixFamily_of_window (Y : ℕ → ℂ → ℂ)
    (hYan : ∀ k : ℕ, AnalyticOnNhd ℂ (Y k) (Set.univ : Set ℂ))
    (hwin : ∀ m : ℕ, ∀ A : MvPolynomial (Fin m) ℂ, A ≠ 0 → ∀ c : ℝ, 0 ≤ c →
      ∃ r : ℝ, 0 < r ∧
        ∀ (cen z : ℂ) (ε : ℝ), r ≤ ‖z - cen‖ → ‖z - cen‖ ≤ r + 1 → 0 < ε →
          ε ≤ ‖MvPolynomial.eval (fun j => prefixFamily Y m j z) A‖ →
          (∀ w : ℂ, ‖w - cen‖ ≤ r → ‖Y m w‖ ≤ ‖Y m z‖) →
          c * (1 + (∑ j : Fin m, Real.posLog ‖prefixFamily Y m j z‖) + Real.posLog ε⁻¹)
            < Real.posLog ‖Y m z‖)
    (m : ℕ) :
    ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
      ¬ (∀ z : ℂ, MvPolynomial.eval (fun j => prefixFamily Y m j z) P = 0) := by
  induction m with
  | zero =>
      intro P hP hrel
      apply hP
      have heq : (MvPolynomial.eval (fun j => prefixFamily Y 0 j (0 : ℂ)) :
            MvPolynomial (Fin 0) ℂ →+* ℂ)
          = (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0) : MvPolynomial (Fin 0) ℂ →+* ℂ) :=
        eval_empty_eq _
      have hz : (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0) : MvPolynomial (Fin 0) ℂ →+* ℂ) P = 0 := by
        rw [← heq]
        exact hrel 0
      exact (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0)).injective (by simpa using hz)
  | succ m ih =>
      intro P hP hrel
      have hcoeffne : ∀ A : MvPolynomial (Fin m) ℂ, A ≠ 0 →
          ∃ c : ℂ, MvPolynomial.eval (fun j => prefixFamily Y m j c) A ≠ 0 := by
        intro A hA
        by_contra hcon
        refine ih A hA ?_
        intro c
        by_contra hc
        exact hcon ⟨c, hc⟩
      have hYd : Differentiable ℂ (Y m) :=
        fun z => (hYan m z (Set.mem_univ z)).differentiableAt
      have hsep : StepSeparation (prefixFamily Y m) (Y m) :=
        stepSeparation_of_window_of_ne (fun j => hYan _) hYd hcoeffne (hwin m)
      refine noRelation_snoc ih hsep P hP ?_
      intro z
      rw [prefixFamily_snoc]
      exact hrel z

end RHTower
