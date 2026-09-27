import GaloisForLFunctions.RHTower.CCMSmoothSourceRecentering
import GaloisForLFunctions.RHTower.ThetaIntegerLogGapPolarization
import GaloisForLFunctions.RHTower.CCMRestrictedWeilGroundParity
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarBumpSources
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarInverse

/-!
# Full quadratic structure and local coercivity in translated ground coordinates

The parallelogram law is transported from the existing restricted Weil form,
using the exact smooth-source bridge. The small-support positive gap is uniform
over all centers and ambient apertures in physical theta ground mass.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem ccmSmoothSourceFormVector_eq_add_smul {a : SuzukiPositiveAperture}
    (u v w : CCMComplexSmoothInteriorSource a) (s : ℂ)
    (hw : ∀ x, w x = u x + s * v x) :
    w.toCCMFormVector = u.toCCMFormVector + s • v.toCCMFormVector := by
  have he : w = u.combo v u s 0 := by
    apply CCMComplexSmoothInteriorSource.eq_of_coe_eq
    funext x
    simp only [CCMComplexSmoothInteriorSource.combo_apply, zero_mul, add_zero, hw]
  rw [he, CCMComplexSmoothInteriorSource.combo_toCCMFormVector, zero_smul, add_zero]

theorem ccmCompactRealProfileEnergy_eq (a : SuzukiPositiveAperture)
    (phi : 𝓢(ℝ, ℝ)) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Ioo (-a.1) a.1) :
    ccmRestrictedWeilSourceQuadratic a
        (ccmThetaSourceOfCompactRealProfile a phi hc hs).toCCMFormVector =
      thetaRealArithmeticQuadratic phi := by
  rw [ccmRestrictedWeilSourceQuadratic_eq_thetaFullArithmetic,
    ccmThetaGroundProfile_ofCompactRealProfile]
  rfl

theorem thetaRealArithmeticQuadratic_compact_parallelogram
    (phi psi : 𝓢(ℝ, ℝ)) (hpc : HasCompactSupport phi) (hqc : HasCompactSupport psi) :
    thetaRealArithmeticQuadratic (phi + psi) + thetaRealArithmeticQuadratic (phi - psi) =
      2 * thetaRealArithmeticQuadratic phi + 2 * thetaRealArithmeticQuadratic psi := by
  obtain ⟨A, hA, hbound⟩ := (hpc.union hqc).isBounded.exists_pos_norm_lt
  let a : SuzukiPositiveAperture := ⟨A, hA⟩
  have hps : tsupport phi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x (Or.inl hx))
  have hqs : tsupport psi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x (Or.inr hx))
  have hadd : tsupport (phi + psi) ⊆ Ioo (-a.1) a.1 :=
    (tsupport_add phi psi).trans (union_subset hps hqs)
  have hsub : tsupport (phi - psi) ⊆ Ioo (-a.1) a.1 :=
    (tsupport_sub phi psi).trans (union_subset hps hqs)
  let u := ccmThetaSourceOfCompactRealProfile a phi hpc hps
  let v := ccmThetaSourceOfCompactRealProfile a psi hqc hqs
  let w := ccmThetaSourceOfCompactRealProfile a (phi + psi) (hpc.add hqc) hadd
  let z := ccmThetaSourceOfCompactRealProfile a (phi - psi) (hpc.sub hqc) hsub
  have hw : w.toCCMFormVector = u.toCCMFormVector + v.toCCMFormVector := by
    have h := ccmSmoothSourceFormVector_eq_add_smul u v w 1 (fun x => by
      simp only [u, v, w, ccmThetaSourceOfCompactRealProfile_apply, add_apply,
        Complex.ofReal_add, one_mul]
      ring)
    simpa only [one_smul] using h
  have hz : z.toCCMFormVector = u.toCCMFormVector - v.toCCMFormVector := by
    have h := ccmSmoothSourceFormVector_eq_add_smul u v z (-1) (fun x => by
      simp only [u, v, z, ccmThetaSourceOfCompactRealProfile_apply, sub_apply,
        Complex.ofReal_sub]
      ring)
    simpa only [neg_one_smul, sub_eq_add_neg] using h
  have h := ccmRestrictedWeilSourceQuadratic_parallelogram a u.toCCMFormVector v.toCCMFormVector
  rw [← hw, ← hz] at h
  simpa only [u, v, w, z, ccmCompactRealProfileEnergy_eq] using h

theorem thetaGroundNormSq_nonneg (chi : 𝓢(ℝ, ℂ)) : 0 ≤ thetaGroundNormSq chi :=
  integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- A genuine diagonal lower bound for every compact real profile in any translated small ball. -/
theorem exists_thetaReal_center_independent_gap :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (phi : 𝓢(ℝ, ℝ)), HasCompactSupport phi → ∀ c : ℝ,
        tsupport phi ⊆ Metric.ball c delta →
        C * thetaGroundNormSq (thetaComplexify phi) ≤ thetaRealArithmeticQuadratic phi := by
  obtain ⟨delta, C, hd, hC, hgap⟩ := exists_ccmSmoothSource_center_independent_gap
  refine ⟨delta, C, hd, hC, fun phi hc c hs => ?_⟩
  obtain ⟨A, hA, hbound⟩ := hc.isBounded.exists_pos_norm_lt
  let a : SuzukiPositiveAperture := ⟨A, hA⟩
  have hps : tsupport phi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x hx)
  let u := ccmThetaSourceOfCompactRealProfile a phi hc hps
  have hts : tsupport u = tsupport phi := by
    change closure (Function.support u) = closure (Function.support phi)
    rw [show Function.support u = Function.support phi from
      support_ccmThetaSourceOfCompactRealProfile a phi hc hps]
  have h := hgap a u c (by rwa [hts])
  rwa [← thetaGroundNormSq_compactReal_eq_physical a phi hc hps,
    ccmCompactRealProfileEnergy_eq] at h

end RHTower
