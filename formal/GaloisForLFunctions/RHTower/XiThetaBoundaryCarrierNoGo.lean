import GaloisForLFunctions.RHTower.XiThetaL2Cyclicity

/-!
# Route K: continuous boundary-carrier no-go

The completed theta source is cyclic under real translation in ordinary
`L²(R)`.  Consequently, a continuous full-domain reporter on any normed
completion with dense `L²` image cannot both annihilate the complete source
orbit and retain nonzero boundary data.

This closes the regular Hausdorff-completion branch of Route K.  It does not
exclude a genuinely partial or discontinuous boundary relation, nor a carrier
in which ordinary `L²` has nondense image.
-/

namespace RHTower

noncomputable section

/-- **Theta boundary-carrier collapse.**  Let `j` embed the ordinary theta
`L²` carrier densely in a normed boundary carrier.  Every continuous linear
reporter which kills all translated theta-source vectors is zero. -/
theorem xiTheta_continuousBoundaryReporter_eq_zero
    {B Y : Type*}
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (j : XiThetaL2 →L[ℂ] B) (hj : DenseRange j)
    (q : B →L[ℂ] Y)
    (hkill : ∀ a : ℝ, q (j (xiThetaTranslationOrbit a)) = 0) :
    q = 0 :=
  continuousBoundaryReporter_eq_zero_of_cyclic_denseRange
    xiThetaTranslationOrbit isCyclicFamily_xiThetaTranslationOrbit
    j hj q hkill

/-- **Route K boundary-carrier trichotomy, continuous category.**  A nonzero
continuous reporter either lives on a carrier whose ordinary-`L²` image is
not dense or detects at least one translate of the theta source.  Thus a
nonzero reporter on a dense completion cannot kill the complete cyclic bulk. -/
theorem xiTheta_nonzero_continuousBoundaryReporter_forces_escape
    {B Y : Type*}
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (j : XiThetaL2 →L[ℂ] B) (q : B →L[ℂ] Y) (hq : q ≠ 0) :
    ¬ DenseRange j ∨ ∃ a : ℝ, q (j (xiThetaTranslationOrbit a)) ≠ 0 := by
  by_cases hj : DenseRange j
  · right
    by_contra hnone
    push_neg at hnone
    exact hq (xiTheta_continuousBoundaryReporter_eq_zero j hj q hnone)
  · exact Or.inl hj

/-- No nonzero continuous boundary reporter on a dense completion can
annihilate the full translated theta source. -/
theorem not_exists_nonzero_xiTheta_continuousBoundaryReporter_denseCompletion :
    ¬ ∃ (B Y : Type) (_ : NormedAddCommGroup B) (_ : NormedSpace ℂ B)
        (_ : NormedAddCommGroup Y) (_ : NormedSpace ℂ Y)
        (j : XiThetaL2 →L[ℂ] B) (q : B →L[ℂ] Y),
      DenseRange j ∧ q ≠ 0 ∧
        ∀ a : ℝ, q (j (xiThetaTranslationOrbit a)) = 0 := by
  rintro ⟨B, Y, iB, sB, iY, sY, j, q, hj, hq, hkill⟩
  letI : NormedAddCommGroup B := iB
  letI : NormedSpace ℂ B := sB
  letI : NormedAddCommGroup Y := iY
  letI : NormedSpace ℂ Y := sY
  exact hq (xiTheta_continuousBoundaryReporter_eq_zero j hj q hkill)

end

end RHTower
