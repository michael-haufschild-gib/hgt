import GaloisForLFunctions.RHTower.XiGammaShapeCompleteMonotonicity
import GaloisForLFunctions.HTGeometry.GeneralDirichletCompletelyMonotone

/-!
# Completely monotone extension of the Xi Gamma-shape trace is the Riemann hypothesis

The Gamma--Meixner frequencies are strictly increasing in the prime scale, so the safe Xi
prime-seam trace is a general Dirichlet series with distinct nonnegative frequencies and
nonnegative coefficients.  A completely monotone extension of its safe germ to the whole positive
shape axis therefore forces convergence at every positive shape, which contradicts the divergence
produced by any off-line divisor copy.

Conversely the Riemann hypothesis makes every prime seam vanish, so the trace is identically zero
and the zero tower is an extension whose Hankel kernel is positive semidefinite everywhere.

Positivity of the Hankel kernel alone is not enough: `exp_hankel_nonneg` together with
`exp_not_completelyMonotone` exhibits a positive semidefinite Hankel kernel with negative
generator frequency.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The frequencies are distinct -/

/-- The Gamma--Meixner frequency is strictly increasing on the integers above zero. -/
theorem xiMeixnerFrequency_lt_of_lt {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    xiMeixnerFrequency m < xiMeixnerFrequency n := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hlt : Real.log (m : ℝ) < Real.log (n : ℝ) :=
    Real.log_lt_log hm0 (by exact_mod_cast hmn)
  have hcosh : Real.cosh (2 * Real.log (m : ℝ)) < Real.cosh (2 * Real.log (n : ℝ)) := by
    refine Real.cosh_lt_cosh.mpr ?_
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * Real.log (m : ℝ)),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * Real.log (n : ℝ))]
    linarith
  have hlog := Real.log_lt_log (Real.cosh_pos _) hcosh
  rw [xiMeixnerFrequency, xiMeixnerFrequency]
  linarith

/-- Distinct primes carry distinct Gamma--Meixner frequencies. -/
theorem xiGammaShapeFrequency_injective : Function.Injective xiGammaShapeFrequency := by
  intro p q hpq
  simp only [xiGammaShapeFrequency] at hpq
  by_contra hne
  have hne' : (p : ℕ) ≠ (q : ℕ) := fun h => hne (Subtype.ext h)
  rcases lt_or_gt_of_ne hne' with h | h
  · exact absurd hpq (ne_of_lt (xiMeixnerFrequency_lt_of_lt p.prop.one_lt.le h))
  · exact absurd hpq.symm (ne_of_lt (xiMeixnerFrequency_lt_of_lt q.prop.one_lt.le h))

/-! ## The criterion -/

/-- **The completely monotone extension criterion.**  A finite completely monotone extension of the
safe Gamma-shape germ to the whole positive shape axis is the Riemann hypothesis. -/
theorem riemannHypothesis_of_xiGammaShapeRealTrace_completelyMonotone
    {F : ℕ → ℝ → ℝ} (hF : CompletelyMonotoneTower F)
    (hagree : ∀ θ : ℝ, 1 < θ → F 0 θ = xiGammaShapeRealTrace θ) :
    RiemannHypothesis := by
  by_contra hcon
  rw [xiSpectralPoint_im_eq_zero_iff_rh] at hcon
  push Not at hcon
  obtain ⟨q₀, hq₀⟩ := hcon
  have hoff : ((q₀.1 : ℂ)).re ≠ 1 / 2 := by
    intro h
    apply hq₀
    rw [xiSpectralPoint_im_eq, h]
    ring
  have hδpos : 0 < |2 * ((q₀.1 : ℂ)).re - 1| / 2 := by
    have hne : |2 * ((q₀.1 : ℂ)).re - 1| ≠ 0 := by
      rw [abs_ne_zero]
      intro h
      exact hoff (by linarith)
    have := abs_nonneg (2 * ((q₀.1 : ℂ)).re - 1)
    positivity
  refine not_summable_xiGammaShapeTwist_of_offLine hoff
    (summable_gdTwistTerm_of_completelyMonotoneTower xiGammaShapeCoefficient_nonneg
      xiGammaShapeFrequency_nonneg xiGammaShapeFrequency_injective
      (fun θ hθ => summable_xiGammaShapeTwist hθ) hF (fun θ hθ => ?_) hδpos)
  rw [hagree θ hθ, xiGammaShapeRealTrace]

/-- The zero tower is completely monotone. -/
theorem completelyMonotoneTower_zero :
    CompletelyMonotoneTower (fun _ _ => (0 : ℝ)) where
  hasDeriv := fun _ x _ => hasDerivAt_const x 0
  sign := fun _ _ _ => by simp

/-- Under the Riemann hypothesis every prime seam vanishes, so the trace is identically zero. -/
theorem xiGammaShapeRealTrace_eq_zero_of_rh (hRH : RiemannHypothesis) (θ : ℝ) :
    xiGammaShapeRealTrace θ = 0 := by
  have hzero : ∀ p : Nat.Primes,
      gdTwistTerm xiGammaShapeCoefficient xiGammaShapeFrequency θ 0 p = 0 := by
    intro p
    rw [gdTwistTerm, xiGammaShapeCoefficient_eq_zero_of_rh hRH p]
    ring
  rw [xiGammaShapeRealTrace, gdRealSeries, tsum_congr hzero, tsum_zero]

/-- **Scalar form.**  The Riemann hypothesis is exactly the existence of a finite completely
monotone extension of the safe Gamma-shape germ. -/
theorem riemannHypothesis_iff_xiGammaShapeRealTrace_completelyMonotone :
    RiemannHypothesis ↔
      ∃ F : ℕ → ℝ → ℝ, CompletelyMonotoneTower F ∧
        ∀ θ : ℝ, 1 < θ → F 0 θ = xiGammaShapeRealTrace θ := by
  constructor
  · intro hRH
    exact ⟨fun _ _ => 0, completelyMonotoneTower_zero,
      fun θ _ => (xiGammaShapeRealTrace_eq_zero_of_rh hRH θ).symm⟩
  · rintro ⟨F, hF, hagree⟩
    exact riemannHypothesis_of_xiGammaShapeRealTrace_completelyMonotone hF hagree

/-- **Kernel form.**  The Riemann hypothesis is exactly the existence of an extension of the safe
Gamma-shape germ whose radial Hankel kernel is positive semidefinite at every positive shape and
whose generator is completely monotone.  The generator condition cannot be dropped. -/
theorem riemannHypothesis_iff_xiGammaShapeRealTrace_hankel_extension :
    RiemannHypothesis ↔
      ∃ F : ℕ → ℝ → ℝ, CompletelyMonotoneTower F ∧
        (∀ θ : ℝ, 1 < θ → F 0 θ = xiGammaShapeRealTrace θ) ∧
        ∀ (n : ℕ) (θ c : Fin n → ℝ), (∀ i, 0 < θ i) →
          0 ≤ ∑ i, ∑ j, c i * F 0 (θ i + θ j) * c j := by
  constructor
  · intro hRH
    refine ⟨fun _ _ => 0, completelyMonotoneTower_zero,
      fun θ _ => (xiGammaShapeRealTrace_eq_zero_of_rh hRH θ).symm, fun n θ c _ => ?_⟩
    simp
  · rintro ⟨F, hF, hagree, -⟩
    exact riemannHypothesis_of_xiGammaShapeRealTrace_completelyMonotone hF hagree

end

end RHTower
