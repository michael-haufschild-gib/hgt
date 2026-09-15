import GaloisForLFunctions.RHTower.MobiusGammaXiCoupledErrorDebtCancellationDichotomy

/-!
# G-CE real-reflection cancellation is physical-ray erasure

The scalar-controller dichotomy is complex-linear.  The apparent escape is to use the
real-linear antiunitary reflection `z ↦ -conj z`: the actual G-CE Ward coefficient might lie on a
real symmetry axis, in which case reflection visibly cancels it without being `-I` on all complex
scalars.

This module closes that escape.  On every positive real Ward node, Schwarz pairing makes the
literal completed Ward response real.  Reflection therefore cancels not one selected critical
charge but the entire physical real Ward ray.  At the critical coefficient it also transfers the
same exact graph debt to its hidden antisymmetric port.  Thus real reflection is anti-linear
physical-ray erasure, not a source-selective pre-scalar producer.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- The real-linear antiunitary candidate for cancelling a real physical Ward value. -/
def mobiusGammaXiRealReflection (z : ℂ) : ℂ :=
  -(starRingEnd ℂ) z

/-- Visible residual after the real-reflection candidate. -/
def mobiusGammaXiRealReflectionResidual (z : ℂ) : ℂ :=
  z + mobiusGammaXiRealReflection z

/-- A real-linear scalar controller erases the full physical Ward ray when it acts as the
opposite on every real source value. -/
def mobiusGammaXiRealLinearDebtControllerErasesPhysicalRay (T : ℂ →ₗ[ℝ] ℂ) : Prop :=
  ∀ r : ℝ, T (r : ℂ) = -(r : ℂ)

/-- Visible critical residual of a real-linear scalar controller. -/
def mobiusGammaXiRealLinearControlledCriticalResidual (T : ℂ →ₗ[ℝ] ℂ) : ℂ :=
  mobiusGammaXiCoupledErrorCriticalCoefficient +
    T mobiusGammaXiCoupledErrorCriticalCoefficient

/-- A complete Schwarz pair is conjugation-fixed at every real Ward node. -/
theorem star_xiAntiCausalWardSchwarzPairResponse_of_real
    (q : XiRightUpperZeroCopy) (t : ℝ) :
    (starRingEnd ℂ) (xiAntiCausalWardSchwarzPairResponse q (t : ℂ)) =
      xiAntiCausalWardSchwarzPairResponse q (t : ℂ) := by
  rw [xiAntiCausalWardSchwarzPairResponse]
  simp only [map_mul, map_add, map_inv₀, xiRightCenteredZero_conj,
    starRingEnd_apply, star_star]
  rw [Complex.star_def, Complex.conj_ofNat, Complex.conj_ofReal]
  ring

/-- Every complete Schwarz-pair contribution has zero imaginary part on the physical ray. -/
theorem im_xiAntiCausalWardSchwarzPairResponse_of_real
    (q : XiRightUpperZeroCopy) (t : ℝ) :
    (xiAntiCausalWardSchwarzPairResponse q (t : ℂ)).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← Complex.star_def]
  exact star_xiAntiCausalWardSchwarzPairResponse_of_real q t

/-- **Physical-ray reality law.**  The literal completed anti-causal Ward response is real at
every positive real node. -/
theorem im_continuedXiAntiCausalWardResponse_of_real
    {t : ℝ} (ht : 0 < t) :
    (continuedXiAntiCausalWardResponse (t : ℂ)).im = 0 := by
  have hsum := summable_xiAntiCausalWardSchwarzPairResponse (w := (t : ℂ))
    (by simpa using ht)
  rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs (by simpa using ht),
    Complex.im_tsum hsum]
  have hzero : (fun q : XiRightUpperZeroCopy =>
      (xiAntiCausalWardSchwarzPairResponse q (t : ℂ)).im) = fun _ => 0 := by
    funext q
    exact im_xiAntiCausalWardSchwarzPairResponse_of_real q t
  rw [hzero, tsum_zero]

/-- The actual critical G-CE Ward charge lies on the real physical symmetry axis. -/
theorem mobiusGammaXiCoupledErrorCriticalCoefficient_im_eq_zero :
    mobiusGammaXiCoupledErrorCriticalCoefficient.im = 0 := by
  simpa [mobiusGammaXiCoupledErrorCriticalCoefficient] using
    (im_continuedXiAntiCausalWardResponse_of_real (t := (1 / 2 : ℝ))
      (by norm_num))

/-- Reflection fixes the critical charge before its explicit opposite sign is applied. -/
theorem star_mobiusGammaXiCoupledErrorCriticalCoefficient :
    (starRingEnd ℂ) mobiusGammaXiCoupledErrorCriticalCoefficient =
      mobiusGammaXiCoupledErrorCriticalCoefficient := by
  rw [starRingEnd_apply, Complex.star_def, Complex.conj_eq_iff_im]
  exact mobiusGammaXiCoupledErrorCriticalCoefficient_im_eq_zero

/-- A nonzero value on the real symmetry axis spans the complete physical real ray. -/
private theorem real_smul_eq_of_im_eq_zero
    (d : ℂ) (hdim : d.im = 0) (hdne : d ≠ 0) (r : ℝ) :
    (r / d.re : ℝ) • d = (r : ℂ) := by
  have hdre : d.re ≠ 0 := by
    intro hre
    apply hdne
    apply Complex.ext <;> simp [hre, hdim]
  rw [Algebra.smul_def]
  have hd : d = (d.re : ℂ) := by
    rw [← Complex.conj_eq_iff_re, Complex.conj_eq_iff_im]
    exact hdim
  rw [hd, ← Complex.ofReal_div]
  field_simp [hdre]

/-- **Real-linear scalar-controller dichotomy.**  Even after admitting anti-linear behaviour,
cancelling the actual critical charge either proves RH or erases the entire physical real Ward
ray.  Thus real reflection is not an escape from source-selective G-CE cancellation. -/
theorem mobiusGammaXiRealLinearDebtController_cancellation_iff_rh_or_physicalRayErasure
    (T : ℂ →ₗ[ℝ] ℂ) :
    mobiusGammaXiRealLinearControlledCriticalResidual T = 0 ↔
      RiemannHypothesis ∨ mobiusGammaXiRealLinearDebtControllerErasesPhysicalRay T := by
  let d := mobiusGammaXiCoupledErrorCriticalCoefficient
  constructor
  · intro hcancel
    by_cases hd : d = 0
    · left
      exact continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh.mp
        (by simpa [d, mobiusGammaXiCoupledErrorCriticalCoefficient] using hd)
    · right
      intro r
      have hTd : T d = -d := by
        dsimp only [mobiusGammaXiRealLinearControlledCriticalResidual, d] at hcancel
        linear_combination hcancel
      have hrd : (r / d.re : ℝ) • d = (r : ℂ) :=
        real_smul_eq_of_im_eq_zero d
          (by simpa [d] using mobiusGammaXiCoupledErrorCriticalCoefficient_im_eq_zero) hd r
      rw [← hrd, T.map_smul, hTd]
      simpa [smul_neg] using congrArg Neg.neg hrd
  · rintro (hRH | herase)
    · have hd : mobiusGammaXiCoupledErrorCriticalCoefficient = 0 := by
        exact continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh.mpr hRH
      simp [mobiusGammaXiRealLinearControlledCriticalResidual, hd]
    · rw [mobiusGammaXiRealLinearControlledCriticalResidual]
      have hd : mobiusGammaXiCoupledErrorCriticalCoefficient =
          (mobiusGammaXiCoupledErrorCriticalCoefficient.re : ℂ) := by
        rw [← Complex.conj_eq_iff_re, Complex.conj_eq_iff_im]
        exact mobiusGammaXiCoupledErrorCriticalCoefficient_im_eq_zero
      rw [hd, herase]
      ring

/-- The antiunitary candidate erases every positive-real physical Ward response, not only the
critical charge. -/
theorem mobiusGammaXiRealReflectionResidual_ward_real_eq_zero
    {t : ℝ} (ht : 0 < t) :
    mobiusGammaXiRealReflectionResidual
      (continuedXiAntiCausalWardResponse (t : ℂ)) = 0 := by
  rw [mobiusGammaXiRealReflectionResidual, mobiusGammaXiRealReflection,
    starRingEnd_apply, Complex.star_def,
    (Complex.conj_eq_iff_im.mpr (im_continuedXiAntiCausalWardResponse_of_real ht))]
  ring

/-- At the critical value, the reflection controller has exactly one copy of the original graph
debt as energy. -/
theorem mobiusGammaXiRealReflection_critical_energy_eq_debt :
    Complex.normSq
        (mobiusGammaXiRealReflection mobiusGammaXiCoupledErrorCriticalCoefficient) =
      mobiusGammaXiCoupledErrorSingularGraphDebt := by
  rw [mobiusGammaXiRealReflection, Complex.normSq_neg,
    Complex.normSq_conj]
  rfl

/-- **Real-reflection transfer law.**  The visible critical residual is zero, but the hidden
antisymmetric port carries twice the exact singular graph debt. -/
theorem mobiusGammaXiRealReflection_exactPhysicalRayErasure :
    mobiusGammaXiRealReflectionResidual
        mobiusGammaXiCoupledErrorCriticalCoefficient = 0 ∧
      Complex.normSq
          (mobiusGammaXiRealReflection
            mobiusGammaXiCoupledErrorCriticalCoefficient) =
        mobiusGammaXiCoupledErrorSingularGraphDebt ∧
      (1 / 2 : ℝ) * Complex.normSq
          (mobiusGammaXiCoupledErrorCriticalCoefficient -
            mobiusGammaXiRealReflection
              mobiusGammaXiCoupledErrorCriticalCoefficient) =
        2 * mobiusGammaXiCoupledErrorSingularGraphDebt := by
  refine ⟨?_, mobiusGammaXiRealReflection_critical_energy_eq_debt, ?_⟩
  · rw [mobiusGammaXiRealReflectionResidual,
      mobiusGammaXiRealReflection,
      star_mobiusGammaXiCoupledErrorCriticalCoefficient]
    ring
  · rw [mobiusGammaXiRealReflection,
      star_mobiusGammaXiCoupledErrorCriticalCoefficient]
    have htwice :
        mobiusGammaXiCoupledErrorCriticalCoefficient -
            -mobiusGammaXiCoupledErrorCriticalCoefficient =
          (2 : ℂ) * mobiusGammaXiCoupledErrorCriticalCoefficient := by
      ring
    rw [htwice, Complex.normSq_mul, Complex.normSq_ofNat]
    simp only [mobiusGammaXiCoupledErrorSingularGraphDebt]
    ring

end RHTower
