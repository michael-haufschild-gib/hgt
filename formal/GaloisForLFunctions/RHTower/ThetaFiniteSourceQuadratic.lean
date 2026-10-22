import GaloisForLFunctions.RHTower.CCM.CCMSmoothFiniteSum
import GaloisForLFunctions.RHTower.CCM.CCMPrimeFrustratedTriangle

/-!
# Finite full quadratic expansion for arbitrary compact real profiles

Every compact profile family is placed in one actual CCM aperture. Literal
smooth-source addition transports its complete quadratic to the finite matrix
of full arithmetic polarizations.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem hasCompactSupport_schwartz_finite_sum {ι : Type*} [Fintype ι]
    (phi : ι → 𝓢(ℝ, ℝ)) (hc : ∀ i, HasCompactSupport (phi i)) :
    HasCompactSupport (⇑(∑ i, phi i)) := by
  convert! (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => hc i)) using 1
  funext x
  simp

theorem thetaRealWeilPolar_compact_self (phi : 𝓢(ℝ, ℝ)) (hc : HasCompactSupport phi) :
    thetaRealWeilPolar phi phi = thetaRealArithmeticQuadratic phi := by
  obtain ⟨A, hA, hbound⟩ := hc.isBounded.exists_pos_norm_lt
  let a : SuzukiPositiveAperture := ⟨A, hA⟩
  have hs : tsupport phi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x hx)
  rw [← ccmWeilRealPolar_compactReal_eq a phi phi hc hc hs hs,
    ccmWeilRealPolar_self, ccmCompactRealProfileEnergy_eq]

theorem thetaRealWeilPolar_compact_symm (phi psi : 𝓢(ℝ, ℝ))
    (hc : HasCompactSupport phi) (hd : HasCompactSupport psi) :
    thetaRealWeilPolar phi psi = thetaRealWeilPolar psi phi := by
  obtain ⟨A, hA, hbound⟩ := (hc.union hd).isBounded.exists_pos_norm_lt
  let a : SuzukiPositiveAperture := ⟨A, hA⟩
  have hs : tsupport phi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x (Or.inl hx))
  have ht : tsupport psi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x (Or.inr hx))
  rw [← ccmWeilRealPolar_compactReal_eq a phi psi hc hd hs ht,
    ← ccmWeilRealPolar_compactReal_eq a psi phi hd hc ht hs]
  exact ccmWeilRealPolar_symm a _ _

theorem thetaRealArithmeticQuadratic_finite_sum {ι : Type*} [Fintype ι]
    (phi : ι → 𝓢(ℝ, ℝ)) (hc : ∀ i, HasCompactSupport (phi i)) :
    thetaRealArithmeticQuadratic (∑ i, phi i) =
      ∑ i, ∑ j, thetaRealWeilPolar (phi i) (phi j) := by
  have hcSum := hasCompactSupport_schwartz_finite_sum phi hc
  obtain ⟨A, hA, hbound⟩ := ((isCompact_iUnion hc).union hcSum).isBounded.exists_pos_norm_lt
  let a : SuzukiPositiveAperture := ⟨A, hA⟩
  have hs (i : ι) : tsupport (phi i) ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by
      simpa only [Real.norm_eq_abs] using hbound x (Or.inl (mem_iUnion.mpr ⟨i, hx⟩)))
  have hsSum : tsupport (⇑(∑ i, phi i)) ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x (Or.inr hx))
  let u := fun i => ccmThetaSourceOfCompactRealProfile a (phi i) (hc i) (hs i)
  have he : ccmThetaSourceOfCompactRealProfile a (∑ i, phi i) hcSum hsSum =
      ccmSmoothFiniteSum u (fun _ => 1) := by
    apply CCMComplexSmoothInteriorSource.eq_of_coe_eq
    funext x
    simp only [ccmThetaSourceOfCompactRealProfile_apply, ccmSmoothFiniteSum_apply,
      one_mul, u, sum_apply, Complex.ofReal_sum, Finset.mul_sum]
  calc
    _ = ccmRestrictedWeilSourceQuadratic a
        (ccmThetaSourceOfCompactRealProfile a (∑ i, phi i) hcSum hsSum).toCCMFormVector :=
      (ccmCompactRealProfileEnergy_eq a _ hcSum hsSum).symm
    _ = ccmRestrictedWeilSourceQuadratic a (∑ i, (u i).toCCMFormVector) := by
      rw [he, ccmSmoothFiniteSum_toCCMFormVector]
      simp only [one_smul]
    _ = ∑ i, ∑ j, ccmWeilRealPolar a (u i).toCCMFormVector (u j).toCCMFormVector := by
      simpa only [Complex.ofReal_one, one_smul, finiteSignedQuadratic, mul_one] using
        ccmRestrictedWeilSourceQuadratic_real_sum a (fun i => (u i).toCCMFormVector) (fun _ => 1)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact ccmWeilRealPolar_compactReal_eq a (phi i) (phi j) (hc i) (hc j) (hs i) (hs j)

end RHTower
