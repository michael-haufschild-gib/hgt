import GaloisForLFunctions.HTGeometry.CompactEllipticPoleFiniteness

/-!
# Punctured-local pole-orbit boundary obstruction

Meromorphic functions are naturally equal on punctured neighborhoods, since their assigned values
at poles are irrelevant.  This file strengthens the pole-orbit boundary obstruction and its theta
specialization from literal pointwise equality to punctured-local equality at every orbit point.
-/

open Filter Topology Set Function

namespace GaloisForLFunctions

noncomputable section

/-- A finitely supported meromorphic shift coboundary cannot have singleton pole support even when
the asserted identity is given only on punctured neighborhoods of the orbit points. -/
theorem shiftCoboundary_not_singleton_poleOrbit_of_eventuallyEq
    (g f : ℂ → ℂ) (p q : ℂ)
    (hg : ∀ n : ℤ, MeromorphicAt g (additiveOrbitPoint p q n))
    (hfg : ∀ n : ℤ, f =ᶠ[𝓝[≠] additiveOrbitPoint p q n]
      (fun z => g (z + q) - g z))
    (hfinite : (poleIndexSet g p q).Finite)
    (hfpole : meromorphicOrderAt f p < 0)
    (hunique : ∀ n : ℤ,
      meromorphicOrderAt f (additiveOrbitPoint p q n) < 0 → n = 0) : False := by
  let df : ℂ → ℂ := fun z => g (z + q) - g z
  apply shiftCoboundary_not_singleton_poleOrbit g df p q hg (fun _ => rfl) hfinite
  · rw [← show additiveOrbitPoint p q 0 = p by simp [additiveOrbitPoint]]
    rw [← meromorphicOrderAt_congr (hfg 0)]
    simpa [additiveOrbitPoint] using hfpole
  · intro n hn
    apply hunique n
    rw [meromorphicOrderAt_congr (hfg n)]
    exact hn

/-- The differentiated nonresonant theta defect is not punctured-locally equal on its distinguished
orbit to a shift coboundary of a globally elliptic meromorphic function. -/
theorem thetaDifferentialOperator_ne_ellipticShiftCoboundary_of_eventuallyEq
    {L : Polynomial ℂ} (hL : L ≠ 0) {τ q h : ℂ} (hτ : 0 < τ.im)
    (hq : ThetaTranslationNontorsion τ q)
    (hnonres : ThetaTranslationNonresonant τ q h)
    (g : ℂ → ℂ) (hg : MeromorphicOn g Set.univ)
    (hperiodOne : Function.Periodic g 1)
    (hperiodTau : Function.Periodic g τ)
    (heq : ∀ n : ℤ,
      constantCoeffDifferentialOperator L (thetaLogDerivDefect h · τ) =ᶠ[
        𝓝[≠] additiveOrbitPoint (thetaHalfPeriod τ - h) q n]
        (fun z => g (z + q) - g z)) : False := by
  apply shiftCoboundary_not_singleton_poleOrbit_of_eventuallyEq g
    (constantCoeffDifferentialOperator L (thetaLogDerivDefect h · τ))
    (thetaHalfPeriod τ - h) q
  · intro n
    exact hg _ (Set.mem_univ _)
  · exact heq
  · exact poleIndexSet_finite_of_elliptic hτ hg hperiodOne hperiodTau hq
  · apply (constantCoeffDifferentialOperator_thetaLogDerivDefect_pole_iff
      hL hτ (thetaNonlatticeShift_of_translationNonresonant hnonres)).2
    right
    exact ⟨0, 0, by simp⟩
  · intro n hnPole
    obtain hbase | hshift :=
      (constantCoeffDifferentialOperator_thetaLogDerivDefect_pole_iff
        hL hτ (thetaNonlatticeShift_of_translationNonresonant hnonres)).1 hnPole
    · obtain ⟨a, b, hab⟩ := hbase
      exfalso
      apply hnonres
      refine ⟨-a, -b, n, ?_⟩
      dsimp [additiveOrbitPoint] at hab
      push_cast
      linear_combination -hab
    · obtain ⟨a, b, hab⟩ := hshift
      apply hq a b n
      dsimp [additiveOrbitPoint] at hab
      linear_combination hab

end

end GaloisForLFunctions
