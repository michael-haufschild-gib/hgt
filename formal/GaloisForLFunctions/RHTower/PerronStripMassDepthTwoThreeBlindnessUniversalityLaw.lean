import GaloisForLFunctions.RHTower.PerronStripMassDischarge
import GaloisForLFunctions.RHTower.DirichletDepthTwoThreeZeroTransitionUniversalityLaw

/-!
# Perron strip mass is blind to the depth-two/three zero transition

Depth-two and depth-three finite Dirichlet carriers both satisfy the fully discharged Perron
strip-mass interface.  After raising their explicit bounds to one common envelope, their zero
phases still disagree maximally: depth two is right-half-plane zero-free, whereas depth three has
open-strip zeros at arbitrarily large heights.
-/

namespace RHTower

noncomputable section

/-- `HasPerronStripMassAt` is monotone in its terminal scalar mass bound. -/
theorem HasPerronStripMassAt.mono_bound
    {F : ℂ → ℂ} {c δ L L' : ℝ} {n M : ℕ}
    (hmass : HasPerronStripMassAt F c n δ M L)
    (hLL' : L ≤ L') :
    HasPerronStripMassAt F c n δ M L' :=
  ⟨hmass.1, hmass.2.1, hmass.2.2.1, hmass.2.2.2.trans hLL'⟩

/-- One explicit Perron mass envelope shared by the depth-two and depth-three carriers. -/
noncomputable def dirichletDepthTwoThreePerronCommonBudget
    (n M : ℕ) (δ : ℝ) : ℝ :=
  max
    (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) *
      (dirichletPolyPerronBudget 2 M * Real.pi))
    (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) *
      (dirichletPolyPerronBudget 3 M * Real.pi))

/-- The false inference isolated by the depth-three carrier: a fixed Perron strip-mass envelope
would force every carrier satisfying it to become zero-free high in the open critical strip. -/
def PerronStripMassForcesEventualOpenStripZeroFreeAt
    (c : ℝ) (n : ℕ) (δ : ℝ) (M : ℕ) (L : ℝ) : Prop :=
  ∀ F : ℂ → ℂ, HasPerronStripMassAt F c n δ M L →
    ∃ B : ℝ, ∀ s : ℂ,
      0 < s.re → s.re < 1 → B ≤ s.im → F s ≠ 0

/-- **Perron strip-mass depth blindness.**  At every admissible contour, depth two and depth three
obey one common explicit strip-mass envelope, but they realize opposite zero phases.  Consequently
the aggregate Perron mass interface cannot by itself force eventual open-strip zero-freeness. -/
theorem perronStripMass_depthTwoThree_blindnessUniversality
    {c δ : ℝ} {n M : ℕ}
    (hc : 0 < c) (hn : 1 ≤ n) (hM : 2 ≤ M)
    (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    HasPerronStripMassAt (dirichletPoly 2) c n δ M
        (dirichletDepthTwoThreePerronCommonBudget n M δ) ∧
    HasPerronStripMassAt (dirichletPoly 3) c n δ M
        (dirichletDepthTwoThreePerronCommonBudget n M δ) ∧
    (∀ s : ℂ, 0 < s.re → dirichletPoly 2 s ≠ 0) ∧
    (∀ B : ℝ, ∃ s : ℂ,
      0 < s.re ∧ s.re < 1 ∧ B ≤ s.im ∧ dirichletPoly 3 s = 0) ∧
    ¬ PerronStripMassForcesEventualOpenStripZeroFreeAt c n δ M
        (dirichletDepthTwoThreePerronCommonBudget n M δ) := by
  have hmass2 :
      HasPerronStripMassAt (dirichletPoly 2) c n δ M
        (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) *
          (dirichletPolyPerronBudget 2 M * Real.pi)) :=
    dirichletPoly_hasPerronStripMassAt 2 hc hn hM hδ0 hδn
  have hmass3 :
      HasPerronStripMassAt (dirichletPoly 3) c n δ M
        (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) *
          (dirichletPolyPerronBudget 3 M * Real.pi)) :=
    dirichletPoly_hasPerronStripMassAt 3 hc hn hM hδ0 hδn
  have hmass2Common :
      HasPerronStripMassAt (dirichletPoly 2) c n δ M
        (dirichletDepthTwoThreePerronCommonBudget n M δ) :=
    hmass2.mono_bound (by
      exact le_max_left _ _)
  have hmass3Common :
      HasPerronStripMassAt (dirichletPoly 3) c n δ M
        (dirichletDepthTwoThreePerronCommonBudget n M δ) :=
    hmass3.mono_bound (by
      exact le_max_right _ _)
  have htransition := dirichletDepth_two_three_zeroTransition_universality
  refine ⟨hmass2Common, hmass3Common, htransition.1, htransition.2.2, ?_⟩
  intro hforce
  obtain ⟨B, hzeroFree⟩ := hforce (dirichletPoly 3) hmass3Common
  obtain ⟨s, hs0, hs1, hsB, hsZero⟩ := htransition.2.2 B
  exact hzeroFree s hs0 hs1 hsB hsZero

end

end RHTower
