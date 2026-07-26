import GaloisForLFunctions.RHTower.DeningerDivisorFlow
import Mathlib.Data.Finsupp.Order

/-!
# Semisimplified arithmetic cohomology and the exact Hodge compatibility gate

The local source quotient has multiplicity-bounded jets and its Frobenius has a nilpotent
Jordan part.  Its multiplicity-exact associated graded keeps the same local copy index but lets
Frobenius act by the support eigenvalue on every graded copy.  This is definitionally the finite
multiplicity-copy carrier of the divisor target.

On this graded carrier the functional-equation reflection gives compact-support Poincare duality.
Reflection followed by coefficient conjugation is a bijective positive Hodge identification
unconditionally.  Its Frobenius intertwining law is equivalent to RH.  Thus positivity itself is
not the missing datum on the semisimplification; arithmetic invariance of the positive Hodge
identification is the exact purity theorem still required.
-/

open Complex

namespace RHTower

noncomputable section

/-- Multiplicity-exact algebraic associated-graded carrier of source local jets. -/
abbrev DeningerArithmeticGradedH1 := DeningerDivisorH1

/-- Finite-support boundary of the multiplicity-exact associated-graded source jets. -/
abbrev DeningerArithmeticGradedSourceJetTest := XiZeroCopy →₀ ℂ

/-- The source jet-copy index is definitionally the multiplicity-exact Xi divisor-copy index. -/
def deningerArithmeticGradedH1EquivSourceJets :
    DeningerArithmeticGradedH1 ≃ₗ[ℂ]
      DeningerArithmeticGradedSourceJetTest :=
  LinearEquiv.refl ℂ DeningerArithmeticGradedSourceJetTest

/-- Semisimple graded Frobenius: every local graded copy has the support eigenvalue. -/
def deningerArithmeticGradedTheta :
    Module.End ℂ DeningerArithmeticGradedH1 :=
  deningerDivisorTheta

/-- Poincare pairing between graded ordinary and compact-support copies. -/
def deningerArithmeticGradedPoincare :
    LinearMap.BilinForm ℂ DeningerArithmeticGradedH1 :=
  deningerDivisorCupTrace

/-- Positive Hodge identification: coefficient conjugation followed by FE reflection. -/
def deningerArithmeticGradedHodgeStar :
    DeningerArithmeticGradedH1 ≃ₛₗ[starRingEnd ℂ]
      DeningerArithmeticGradedH1 :=
  (Finsupp.mapRange.linearEquiv (starLinearEquiv ℂ)).trans
    (Finsupp.domLCongr xiZeroCopyReflectEquiv)

theorem xiZeroCopyReflectEquiv_symm_apply (q : XiZeroCopy) :
    xiZeroCopyReflectEquiv.symm q = xiZeroCopyReflectEquiv q := by
  apply xiZeroCopyReflectEquiv.injective
  rw [xiZeroCopyReflectEquiv.apply_symm_apply,
    xiZeroCopyReflectEquiv_apply_apply]

@[simp]
theorem deningerArithmeticGradedHodgeStar_apply
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    deningerArithmeticGradedHodgeStar a q =
      (starRingEnd ℂ) (a (xiZeroCopyReflectEquiv q)) := by
  change
    (starRingEnd ℂ) (a (xiZeroCopyReflectEquiv.symm q)) =
      (starRingEnd ℂ) (a (xiZeroCopyReflectEquiv q))
  rw [xiZeroCopyReflectEquiv_symm_apply]

/-- The positive Hodge identification is involutive. -/
theorem deningerArithmeticGradedHodgeStar_sq
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedHodgeStar
      (deningerArithmeticGradedHodgeStar a) = a := by
  ext q
  simp [deningerArithmeticGradedHodgeStar_apply,
    xiZeroCopyReflectEquiv_apply_apply]

/-- Coordinate-sum formula for the graded Poincare pairing. -/
theorem deningerArithmeticGradedPoincare_eq_sum
    (a b : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedPoincare a b =
      a.sum fun q c => c * b (xiZeroCopyReflectEquiv q) := by
  classical
  rw [deningerArithmeticGradedPoincare, deningerDivisorCupTrace]
  have hlin :=
    Finsupp.linearCombination_apply
      (R := ℂ)
      (v := fun q : XiZeroCopy =>
        Finsupp.lapply (R := ℂ) (M := ℂ)
          (xiZeroCopyReflectEquiv q)) a
  calc
    ((Finsupp.linearCombination ℂ fun q =>
        Finsupp.lapply (xiZeroCopyReflectEquiv q)) a) b =
        (a.sum fun i c =>
          c • Finsupp.lapply (R := ℂ) (M := ℂ)
            (xiZeroCopyReflectEquiv i)) b :=
      congrArg
        (fun f : DeningerArithmeticGradedH1 →ₗ[ℂ] ℂ => f b)
        hlin
    _ = a.sum fun q c => c * b (xiZeroCopyReflectEquiv q) := by
      simp [Finsupp.sum, smul_eq_mul]

/-- Cup followed by Hodge star is the finite sum of coefficient norm-squares. -/
theorem deningerArithmeticGradedPoincare_hodgeStar_self
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedPoincare a
        (deningerArithmeticGradedHodgeStar a) =
      a.sum fun _ c => (Complex.normSq c : ℂ) := by
  rw [deningerArithmeticGradedPoincare_eq_sum]
  apply Finsupp.sum_congr
  intro q _hq
  rw [deningerArithmeticGradedHodgeStar_apply,
    xiZeroCopyReflectEquiv_apply_apply, Complex.mul_conj]

/-- Real diagonal of the graded Hodge metric. -/
theorem deningerArithmeticGradedPoincare_hodgeStar_self_re
    (a : DeningerArithmeticGradedH1) :
    (deningerArithmeticGradedPoincare a
        (deningerArithmeticGradedHodgeStar a)).re =
      a.sum fun _ c => Complex.normSq c := by
  rw [deningerArithmeticGradedPoincare_hodgeStar_self]
  simp [Finsupp.sum]

/-- The graded Hodge metric is positive definite without RH. -/
theorem deningerArithmeticGradedHodge_positive
    {a : DeningerArithmeticGradedH1} (ha : a ≠ 0) :
    0 < (deningerArithmeticGradedPoincare a
      (deningerArithmeticGradedHodgeStar a)).re := by
  rw [deningerArithmeticGradedPoincare_hodgeStar_self_re]
  apply Finsupp.sum_pos
  · intro q hq
    exact Complex.normSq_pos.mpr (Finsupp.mem_support_iff.mp hq)
  · exact ha

/-- The graded Frobenius obeys the weight-one Poincare derivation law. -/
theorem deningerArithmeticGradedTheta_poincare
    (a b : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedPoincare
          (deningerArithmeticGradedTheta a) b +
        deningerArithmeticGradedPoincare a
          (deningerArithmeticGradedTheta b) =
      deningerArithmeticGradedPoincare a b :=
  deningerDivisorTheta_cup a b

/-- Exact coordinate defect in Frobenius/Hodge compatibility. -/
theorem deningerArithmeticGradedTheta_hodgeStar_defect
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    (deningerArithmeticGradedTheta
        (deningerArithmeticGradedHodgeStar a)) q -
      deningerArithmeticGradedHodgeStar
        (deningerArithmeticGradedTheta a) q =
      (deningerDivisorThetaEigen q -
          (starRingEnd ℂ)
            (deningerDivisorThetaEigen
              (xiZeroCopyReflectEquiv q))) *
        (starRingEnd ℂ) (a (xiZeroCopyReflectEquiv q)) := by
  change
    (deningerDivisorTheta
        (deningerArithmeticGradedHodgeStar a)) q -
      deningerArithmeticGradedHodgeStar
        (deningerDivisorTheta a) q = _
  simp only [deningerDivisorTheta, finsuppDiagonal_apply]
  rw [deningerArithmeticGradedHodgeStar_apply a q,
    deningerArithmeticGradedHodgeStar_apply
      (finsuppDiagonal deningerDivisorThetaEigen a) q]
  simp only [finsuppDiagonal_apply, map_mul]
  ring

/-- RH makes the positive graded Hodge identification Frobenius-compatible. -/
theorem deningerArithmeticGradedTheta_hodgeStar_of_riemannHypothesis
    (hRH : RiemannHypothesis) (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedTheta
        (deningerArithmeticGradedHodgeStar a) =
      deningerArithmeticGradedHodgeStar
        (deningerArithmeticGradedTheta a) := by
  ext q
  change
    (deningerDivisorTheta
        (deningerArithmeticGradedHodgeStar a)) q =
      deningerArithmeticGradedHodgeStar
        (deningerDivisorTheta a) q
  simp only [deningerDivisorTheta, finsuppDiagonal_apply]
  rw [deningerArithmeticGradedHodgeStar_apply a q,
    deningerArithmeticGradedHodgeStar_apply
      (finsuppDiagonal deningerDivisorThetaEigen a) q]
  simp only [finsuppDiagonal_apply, map_mul]
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH
    (xiZeroCopyReflectEquiv q)
  have hspectral :
      xiSpectralPoint q = -(t : ℂ) := by
    have hreflect :=
      xiSpectralPoint_reflect (xiZeroCopyReflectEquiv q)
    rw [xiZeroCopyReflectEquiv_apply_apply, ht] at hreflect
    exact hreflect
  have hlambda :
      deningerDivisorThetaEigen q =
        (starRingEnd ℂ)
          (deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q)) := by
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 :=
      map_ofNat (starRingEnd ℂ) 2
    rw [deningerDivisorThetaEigen_eq, deningerDivisorThetaEigen_eq,
      ht, hspectral]
    simp [htwo]
  rw [hlambda]

/-- Frobenius compatibility of the positive graded Hodge identification forces RH. -/
theorem riemannHypothesis_of_deningerArithmeticGradedTheta_hodgeStar
    (hcompat : ∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedTheta
          (deningerArithmeticGradedHodgeStar a) =
        deningerArithmeticGradedHodgeStar
          (deningerArithmeticGradedTheta a)) :
    RiemannHypothesis := by
  have hreal :
      ∀ q : XiZeroCopy, ∃ t : ℝ, xiSpectralPoint q = (t : ℂ) := by
    intro q
    have h := hcompat (Finsupp.single q 1)
    have hq :
        deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) =
          (starRingEnd ℂ) (deningerDivisorThetaEigen q) := by
      have hzero :
          (deningerArithmeticGradedTheta
              (deningerArithmeticGradedHodgeStar (Finsupp.single q 1)))
                (xiZeroCopyReflectEquiv q) -
            deningerArithmeticGradedHodgeStar
                (deningerArithmeticGradedTheta (Finsupp.single q 1))
                (xiZeroCopyReflectEquiv q) = 0 := by
        rw [h]
        ring
      have hdefect :=
        deningerArithmeticGradedTheta_hodgeStar_defect
          (Finsupp.single q 1) (xiZeroCopyReflectEquiv q)
      rw [hzero] at hdefect
      simp [xiZeroCopyReflectEquiv_apply_apply] at hdefect
      exact sub_eq_zero.mp hdefect.symm
    have hweight := deningerDivisorThetaEigen_add_reflect q
    have hconj :
        deningerDivisorThetaEigen q +
          (starRingEnd ℂ) (deningerDivisorThetaEigen q) = 1 := by
      rw [← hq]
      exact hweight
    have hre := congrArg Complex.re hconj
    have hlambda : (deningerDivisorThetaEigen q).re = 1 / 2 := by
      simp only [add_re, conj_re, one_re] at hre
      linarith
    have him : (xiSpectralPoint q).im = 0 := by
      rw [deningerDivisorThetaEigen_eq] at hlambda
      simp [mul_re] at hlambda
      linarith
    exact
      ⟨(xiSpectralPoint q).re,
        Complex.ext (by simp) (by simpa using him)⟩
  rw [rh_iff_xi_ne_zero_right]
  intro z hz hzero
  let ρ : XiDivisorSupport :=
    ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hpos := xi_divisor_pos_on_support ρ
  have hn :
      0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨ρ, ⟨0, hn⟩⟩
  obtain ⟨t, ht⟩ := hreal q
  have him := congrArg Complex.im ht
  have hre : z.re = 1 / 2 := by
    dsimp only [q, ρ, xiSpectralPoint] at him
    simp at him
    linarith
  exact (ne_of_gt (mem_rightHalf.mp hz)) hre

/-- Exact Deninger purity gate on multiplicity-exact semisimplified arithmetic cohomology. -/
theorem deningerArithmeticGradedTheta_hodgeStar_iff_riemannHypothesis :
    (∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedTheta
          (deningerArithmeticGradedHodgeStar a) =
        deningerArithmeticGradedHodgeStar
          (deningerArithmeticGradedTheta a)) ↔
      RiemannHypothesis :=
  ⟨riemannHypothesis_of_deningerArithmeticGradedTheta_hodgeStar,
    deningerArithmeticGradedTheta_hodgeStar_of_riemannHypothesis⟩

end

end RHTower
