import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesMellinResponse
import GaloisForLFunctions.RHTower.CCM.CCMFirstClockLandauCompleteness

/-!
# No fixed Köthe vector can be the completed Stokes landing

Every Mellin response of one fixed nuclear height-Köthe vector is entire in the spectral
parameter.  The completed Xi logarithmic derivative has a genuine simple pole at every centered
Xi zero.  Therefore no fixed source vector can supply the physical completed landing, even locally
on a punctured neighborhood of one Xi divisor point.

The missing object after the projective P-G61/P-G62 crossing is consequently forced into the
strong dual/corona boundary.  This is stronger than the finite-atomic spectral-trace no-go: source
vectors may have infinite support, but rapid height decay still removes every divisor pole.
-/

open Complex Filter Topology Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Every centered Mellin jet of a nuclear height-Köthe vector is analytic at every spectral
parameter. -/
theorem analyticAt_deningerMellinJet
    (z : ℂ) (j : ℕ) (a : DeningerHeightKothe) :
    AnalyticAt ℂ (fun w : ℂ => deningerMellinJet w j a) z := by
  let R : ℝ := |(z - 1 / 2).re| + 1
  let U : Set ℂ := {w | |(w - 1 / 2).re| < R}
  have hR : |(z - 1 / 2).re| < R := by
    dsimp only [R]
    linarith
  have hUopen : IsOpen U := by
    exact isOpen_lt
      (continuous_abs.comp
        (Complex.continuous_re.comp (continuous_id.sub continuous_const)))
      continuous_const
  have hzU : z ∈ U := hR
  obtain ⟨k : ℕ, hk : R + (j : ℝ) < (k : ℝ)⟩ :=
    exists_nat_gt (R + (j : ℝ))
  have hdiff (m : DeningerPrimeLattice) : DifferentiableOn ℂ
      (fun w : ℂ => deningerMellinSymbol w j m *
        (a : DeningerPrimeLattice → ℂ) m) U := by
    unfold deningerMellinSymbol
    fun_prop
  have hbound (m : DeningerPrimeLattice) (w : ℂ) (hw : w ∈ U) :
      ‖deningerMellinSymbol w j m *
          (a : DeningerPrimeLattice → ℂ) m‖ ≤
        deningerHeight m ^ k * ‖(a : DeningerPrimeLattice → ℂ) m‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply deningerMellinSymbol_norm_le
    change |(w - 1 / 2).re| < R at hw
    linarith
  have hdifferentiable : DifferentiableOn ℂ
      (fun w : ℂ => ∑' m : DeningerPrimeLattice,
        deningerMellinSymbol w j m *
          (a : DeningerPrimeLattice → ℂ) m) U :=
    differentiableOn_tsum_of_summable_norm
      (deningerHeightSeminorm_summable a k) hdiff hUopen hbound
  change AnalyticAt ℂ (fun w : ℂ => ∑' m : DeningerPrimeLattice,
    deningerMellinSymbol w j m *
      (a : DeningerPrimeLattice → ℂ) m) z
  exact (hdifferentiable.analyticOnNhd hUopen) z hzU

/-- Every fixed-vector critical Stokes response is entire in its phase parameter. -/
theorem analyticAt_gammaSewnMobiusApertureStokesMellinResponse_one
    (z : ℂ) (j : ℕ) (a : DeningerHeightKothe) :
    AnalyticAt ℂ
      (fun w : ℂ => gammaSewnMobiusApertureStokesMellinResponse 1 w j a) z := by
  exact analyticAt_deningerMellinJet z j
    (gammaSewnMobiusApertureStokesKotheClosedOperator 1 a)

/-- **Strong fixed-vector landing no-go.**  At every actual centered Xi divisor point, no fixed
nuclear source vector response can agree with the completed logarithmic derivative even on a
punctured neighborhood. -/
theorem not_eventuallyEq_gammaSewnMobiusApertureStokesMellinResponse_one_logDeriv_XiC
    (q : XiZeroCopy) (j : ℕ) (a : DeningerHeightKothe) :
    ¬ (fun w : ℂ => gammaSewnMobiusApertureStokesMellinResponse 1 w j a) =ᶠ[
        𝓝[≠] (xiSpectralPoint q)] logDeriv XiC := by
  intro heq
  have han : AnalyticAt ℂ
      (fun w : ℂ => gammaSewnMobiusApertureStokesMellinResponse 1 w j a)
      (xiSpectralPoint q) :=
    analyticAt_gammaSewnMobiusApertureStokesMellinResponse_one
      (xiSpectralPoint q) j a
  have hnonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt
      (fun w : ℂ => gammaSewnMobiusApertureStokesMellinResponse 1 w j a)
      (xiSpectralPoint q) := han.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_congr heq,
    meromorphicOrderAt_logDeriv_XiC_eq_neg_one
      (XiC_xiSpectralPoint_eq_zero q)] at hnonneg
  have hlt : (((-1 : ℤ) : WithTop ℤ)) < 0 :=
    WithTop.coe_lt_coe.mpr (by omega)
  exact (not_le_of_gt hlt) hnonneg

/-- In particular, no fixed nuclear vector gives the global completed Xi logarithmic derivative. -/
theorem gammaSewnMobiusApertureStokesMellinResponse_one_ne_logDeriv_XiC
    (q : XiZeroCopy) (j : ℕ) (a : DeningerHeightKothe) :
    ¬ ∀ w : ℂ,
      gammaSewnMobiusApertureStokesMellinResponse 1 w j a = logDeriv XiC w := by
  intro h
  apply not_eventuallyEq_gammaSewnMobiusApertureStokesMellinResponse_one_logDeriv_XiC q j a
  filter_upwards with w
  exact h w

end RHTower
