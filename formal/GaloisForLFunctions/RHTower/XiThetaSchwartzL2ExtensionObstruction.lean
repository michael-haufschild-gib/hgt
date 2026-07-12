import GaloisForLFunctions.SchwartzSesquilinear
import GaloisForLFunctions.RHTower.XiThetaL2MetricSingularity

/-!
# The Hedenmalm Schwartz metric has no ordinary `L²` extension

Momentum symmetry makes a continuous Schwartz sesquilinear form invariant
under simultaneous real translation.  If the form annihilates the actual
theta source and extends continuously to ordinary `L²(R)`, then the extension
inherits both properties.  Ordinary `L²` cyclicity of the theta source forces
the extension, and hence the original Schwartz form, to vanish.

Thus every nonzero Hedenmalm orientation form is forced to be singular with
respect to the ordinary `L²` topology.
-/

open Complex MeasureTheory Set
open scoped ENNReal SchwartzMap

namespace RHTower

noncomputable section

/-- The two right-translation implementations on Schwartz space agree. -/
theorem mellinL2_schwartzTranslate_eq_translateCLM (a : ℝ) (f : 𝓢(ℝ, ℂ)) :
    MellinL2.schwartzTranslate a f = SchwartzMap.translateCLM ℂ a f := by
  ext x
  rfl

/-- A momentum-symmetric theta-null Schwartz form admitting a jointly
continuous ordinary-`L²` extension vanishes identically. -/
theorem xiThetaSchwartzForm_eq_zero_of_l2_extension
    (QS : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (Q2 : ContinuousSesquilinearForm XiThetaL2)
    (hMomentum : QS.MomentumSymmetric)
    (hThetaNull : ∀ v : 𝓢(ℝ, ℂ), QS xiThetaSchwartzSource v = 0)
    (hExtension : ∀ u v : 𝓢(ℝ, ℂ),
      Q2 (u.toLp 2 volume) (v.toLp 2 volume) = QS u v) :
    ∀ u v : 𝓢(ℝ, ℂ), QS u v = 0 := by
  have hdense : DenseRange
      (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
      ENNReal.ofNat_ne_top
  have hinvariant : XiThetaL2TranslationInvariant Q2 := by
    intro a u v
    let P : XiThetaL2 → XiThetaL2 → Prop := fun x y ↦
      Q2 (MellinL2.additiveTranslationUnitary a x)
          (MellinL2.additiveTranslationUnitary a y) = Q2 x y
    apply DenseRange.induction_on₂ (p := P) hdense
    · apply isClosed_eq
      · exact Q2.continuous.comp
          (((MellinL2.additiveTranslationUnitary a).continuous.comp continuous_fst).prodMk
            ((MellinL2.additiveTranslationUnitary a).continuous.comp continuous_snd))
      · exact Q2.continuous
    · intro f g
      dsimp [P]
      rw [MellinL2.additiveTranslation_toLp, MellinL2.additiveTranslation_toLp,
        hExtension, hExtension,
        mellinL2_schwartzTranslate_eq_translateCLM,
        mellinL2_schwartzTranslate_eq_translateCLM]
      exact QS.translate_pair_invariant hMomentum f g a
  have hnullL2 : ∀ v : XiThetaL2, Q2 xiThetaSourceL2 v = 0 := by
    intro v
    let P : XiThetaL2 → Prop := fun w ↦ Q2 xiThetaSourceL2 w = 0
    apply DenseRange.induction_on (p := P) hdense v
    · exact isClosed_eq
        (Q2.continuous.comp (continuous_const.prodMk continuous_id))
        continuous_const
    · intro f
      dsimp [P]
      rw [xiThetaSourceL2, hExtension]
      exact hThetaNull f
  have hzero := xiThetaL2_continuousForm_eq_zero Q2 hinvariant hnullL2
  intro u v
  rw [← hExtension]
  exact hzero _ _

/-- No nonzero momentum-symmetric theta-null Schwartz form has a jointly
continuous extension to ordinary `L²(R)`. -/
theorem not_exists_nonzero_xiThetaSchwartzForm_l2_extension :
    ¬ ∃ (QS : SchwartzMap.ContinuousSchwartzSesquilinearForm)
        (Q2 : ContinuousSesquilinearForm XiThetaL2),
      QS.MomentumSymmetric ∧
      (∀ v : 𝓢(ℝ, ℂ), QS xiThetaSchwartzSource v = 0) ∧
      (∀ u v : 𝓢(ℝ, ℂ), Q2 (u.toLp 2 volume) (v.toLp 2 volume) = QS u v) ∧
      ∃ u v : 𝓢(ℝ, ℂ), QS u v ≠ 0 := by
  rintro ⟨QS, Q2, hMomentum, hThetaNull, hExtension, u, v, huv⟩
  exact huv (xiThetaSchwartzForm_eq_zero_of_l2_extension
    QS Q2 hMomentum hThetaNull hExtension u v)

end

end RHTower
