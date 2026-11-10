import GaloisForLFunctions.ZeroConfigurationGeometry.TheCriticalProjectionPreservesTheCounts
import GaloisForLFunctions.ZeroConfigurationGeometry.MixedDepthsHideBeyondTheInghamScale
import GaloisForLFunctions.SquareRootThreshold.HodgeClassificationOfFiniteOffLineSets
import GaloisForLFunctions.SquareRootThreshold.EvenAndOddTwoBumpTestsDecideTheCriticalLine

/-!
# Adding the exact zeta-density background

The horizontal projection of the zeta divisor has exactly zeta's
ordinate counts and a bounded lag trace. Adding it to an off-line
configuration adds those counts exactly and changes the trace by a
uniformly bounded amount.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open SquareRootThreshold Zeta23 _root_.RHTower.LocalCountFalsifier

/-- An on-line configuration has lag amplitude at most its mass at zero. -/
theorem norm_lagStructure_le_zero_of_onLine {Z : ZeroConfig} (hZ : TemperedConfig Z)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) :
    ‖lagStructure Z b v‖ ≤ (lagStructure Z b 0).re := by
  have hp (u : ℝ) (hu : 0 ≤ u) : ‖lagStructure Z b u‖ ≤ (lagStructure Z b 0).re :=
    norm_lagStructure_le_re_zero_of_weil_nonneg Z hZ hb hbs hu le_rfl
      (fun f _ _ => weil_nonneg_of_onLine Z hon f)
  rcases le_or_gt 0 v with hv | hv
  · exact hp v hv
  · have he := congrArg (fun z : ℂ => ‖z‖) (conj_lagStructure_neg Z hZ hb hbs v)
    rw [Complex.norm_conj] at he
    exact he.symm.trans_le (hp (-v) (neg_nonneg.mpr hv.le))

/-- Absolutely convergent lag traces add under a disjoint superposition. -/
theorem lagStructure_superpose {Z₁ Z₂ : ZeroConfig} (hd : Disjoint Z₁.carrier Z₂.carrier)
    (h₁ : TemperedConfig Z₁) (h₂ : TemperedConfig Z₂) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) :
    lagStructure (superpose Z₁ Z₂) b v = lagStructure Z₁ b v + lagStructure Z₂ b v := by
  let F : ℂ → ℂ := fun ρ => ((superpose Z₁ Z₂).mult ρ : ℂ) *
    paperFT (EF.weilTest b b) (gammaOf ρ) * cexp (I * gammaOf ρ * v)
  have hs₁ : HasSum (F ∘ ((↑) : Z₁.carrier → ℂ)) (lagStructure Z₁ b v) :=
    (summable_lagStructure Z₁ h₁ hb hbs v).hasSum.congr_fun fun ρ => by
      simp only [F, Function.comp_apply, superpose_mult_left hd ρ.property]
  have hs₂ : HasSum (F ∘ ((↑) : Z₂.carrier → ℂ)) (lagStructure Z₂ b v) :=
    (summable_lagStructure Z₂ h₂ hb hbs v).hasSum.congr_fun fun ρ => by
      simp only [F, Function.comp_apply, superpose_mult_right hd ρ.property]
  exact (HasSum.add_disjoint hd hs₁ hs₂).tsum_eq

/-- The exact zeta-density configuration obtained without assuming RH. -/
def zetaDensityBackground : ZeroConfig := criticalProjectionConfig zetaZeroConfig

theorem zetaDensityBackground_N (T₁ T₂ : ℝ) :
    zetaDensityBackground.N T₁ T₂ = zetaZeroConfig.N T₁ T₂ :=
  criticalProjectionConfig_N zetaZeroConfig T₁ T₂

theorem zetaDensityBackground_tempered : TemperedConfig zetaDensityBackground :=
  temperedConfig_criticalProjection_zeta

/-- The exact-density background contributes a uniformly bounded complex trace. -/
theorem zetaDensityBackground_trace_bound {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b)
    {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) :
    ‖lagStructure zetaDensityBackground b v‖ ≤
      (lagStructure zetaDensityBackground b 0).re :=
  norm_lagStructure_le_zero_of_onLine zetaDensityBackground_tempered
    (criticalProjectionConfig_onLine zetaZeroConfig) hb hbs v

theorem disjoint_zetaDensityBackground_of_offLine {Z : ZeroConfig}
    (hoff : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2) :
    Disjoint Z.carrier zetaDensityBackground.carrier := by
  apply Set.disjoint_left.mpr
  intro ρ hρ hbg
  exact hoff ρ hρ (criticalProjectionConfig_onLine zetaZeroConfig ρ hbg)

/-- Superposition adds zeta's exact ordinate counts to those of the original configuration. -/
theorem N_add_zetaDensityBackground (Z : ZeroConfig) (T₁ T₂ : ℝ) :
    (superpose Z zetaDensityBackground).N T₁ T₂ =
      Z.N T₁ T₂ + zetaZeroConfig.N T₁ T₂ := by
  rw [N_superpose, zetaDensityBackground_N]

/-- Adding the zeta-density background changes an off-line trace by a bounded amount. -/
theorem trace_sub_le_add_zetaDensityBackground {Z : ZeroConfig} (hZ : TemperedConfig Z)
    (hoff : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2) {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b)
    {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) :
    ‖lagStructure (superpose Z zetaDensityBackground) b v - lagStructure Z b v‖ ≤
      (lagStructure zetaDensityBackground b 0).re := by
  rw [lagStructure_superpose (disjoint_zetaDensityBackground_of_offLine hoff) hZ
    zetaDensityBackground_tempered hb hbs v, add_sub_cancel_left]
  exact zetaDensityBackground_trace_bound hb hbs v

#print axioms zetaDensityBackground_trace_bound
#print axioms N_add_zetaDensityBackground
#print axioms trace_sub_le_add_zetaDensityBackground

end GaloisForLFunctions.ZeroConfigurationGeometry
