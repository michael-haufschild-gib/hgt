import GaloisForLFunctions.HTGeometry.KleinGordonBandStrong

/-!
# The strong Cauchy problem on a band is well posed

The band solution of the previous file is twice differentiable and satisfies
`∂ₜ²u = −⟨D⟩²_R u + Wu`. Dividing that identity twice by the frequency turns it into the corpus's own
strong-solution predicate: `⟨D⟩⁻²∂ₜ²u = −u + ⟨D⟩⁻²Wu`, because `⟨D⟩⁻²⟨D⟩²_R` is the band projection
and the solution lives on the band.

So the band solution is a `SolvesKGSource` in the sense of statement 74, and the uniqueness theorem
proved there — by the energy method, with no smoothing hypothesis of its own — applies verbatim. What
was missing before was not uniqueness but *existence*: the strong theory could only produce solutions
for a smoothing perturbation. On a band it produces them for any bounded one, so the strong Cauchy
problem is well posed there.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section BandWellPosed

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The band solution is a strong solution** in the sense of statement 74. -/
theorem solvesKGSource_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b) (R : ℝ)
    (x y : Lp ℂ 2 (volume : Measure E)) :
    SolvesKGSource (kgBandOp W₀ R)
      (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y))
      (kgFieldVel (kgBandOp W₀ R) (kgFreqLowOp R x) (kgLowPassOp R y))
      (fun t => -(kgFreqSqLowOp R (kgFieldMild (kgBandOp W₀ R)
            (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) t))
        + kgBandOp W₀ R (kgFieldMild (kgBandOp W₀ R)
            (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) t)) := by
  have hWb : ‖kgBandOp W₀ R‖ ≤ b := norm_kgBandOp_le hb0 hW R
  refine ⟨fun t => hasDerivAt_kgFieldMild hb0 hWb (kgFreqLowOp R x) (kgLowPassOp R y) t,
    fun t => hasDerivAt_kgFieldVel_band hb0 hW R x y t, fun t => ?_⟩
  have hband : kgLowPassOp R (kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x))
      (kgLowPassOp R y) t)
      = kgFieldMild (kgBandOp W₀ R) (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) t := by
    rw [kgFreqInvOp_kgFreqLowOp]
    exact kgBandOp_lowPass_invariant hb0 hW R x y t
  rw [map_add, map_add, map_neg, map_neg, kgFreqInvOp_sq_kgFreqSqLowOp, hband]

/-- **Uniqueness of the strong solution on a band.** -/
theorem eq_of_solvesKGSource_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b) (R : ℝ)
    {u₁ v₁ a₁ u₂ v₂ a₂ : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h₁ : SolvesKGSource (kgBandOp W₀ R) u₁ v₁ a₁)
    (h₂ : SolvesKGSource (kgBandOp W₀ R) u₂ v₂ a₂)
    (hu0 : u₁ 0 = u₂ 0) (hv0 : v₁ 0 = v₂ 0) (t : ℝ) : u₁ t = u₂ t :=
  eq_of_solvesKGSource hb0 (norm_kgBandOp_le hb0 hW R) h₁ h₂ hu0 hv0 t

/-- **The strong Cauchy problem on a band is well posed.** For band-limited data and any bounded
perturbation compressed to the band there is a strong solution with those data, and it is the only
one. -/
theorem exists_unique_solvesKGSource_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b) (R : ℝ)
    (x y : Lp ℂ 2 (volume : Measure E)) :
    ∃ u v a : ℝ → Lp ℂ 2 (volume : Measure E),
      SolvesKGSource (kgBandOp W₀ R) u v a ∧ u 0 = kgLowPassOp R x ∧ v 0 = kgLowPassOp R y ∧
        ∀ u' v' a' : ℝ → Lp ℂ 2 (volume : Measure E),
          SolvesKGSource (kgBandOp W₀ R) u' v' a' → u' 0 = kgLowPassOp R x →
            v' 0 = kgLowPassOp R y → ∀ t : ℝ, u' t = u t := by
  have hWb : ‖kgBandOp W₀ R‖ ≤ b := norm_kgBandOp_le hb0 hW R
  refine ⟨_, _, _, solvesKGSource_band hb0 hW R x y, ?_, ?_, ?_⟩
  · rw [kgFieldMild_zero hb0 hWb, kgFreqInvOp_kgFreqLowOp]
  · rw [kgFieldVel, intervalIntegral.integral_same, kgSinOp_zero, kgCosOp_zero]
    simp
  · intro u' v' a' h' hu0 hv0 t
    refine eq_of_solvesKGSource_band hb0 hW R h' (solvesKGSource_band hb0 hW R x y) ?_ ?_ t
    · rw [hu0, kgFieldMild_zero hb0 hWb, kgFreqInvOp_kgFreqLowOp]
    · rw [hv0, kgFieldVel, intervalIntegral.integral_same, kgSinOp_zero, kgCosOp_zero]
      simp

end BandWellPosed

end GaloisForLFunctions.HTGeometry
