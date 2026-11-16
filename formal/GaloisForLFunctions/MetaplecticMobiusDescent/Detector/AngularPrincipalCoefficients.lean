import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.MarkedIdealSeries
import GaloisForLFunctions.FamilyContinuationTheory.TheSexticGrossencharacterFactorizesTheProbeCorrection

/-!
# Direct angular coefficients of the principal cubic source

An angular character on the completed arithmetic index preserves sixth-power frequency
invariance. At a prime it changes the numerator character by weight ℓ and the correction
character by weight 6ℓ, leaving the free sixth-power frequency coordinate unchanged.
-/

open Complex
open scoped BigOperators Classical ComplexConjugate
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection
open GaloisForLFunctions.FamilyContinuationTheory
namespace ProbePhysical
open ProbeRow ProbeEuler CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => Eisenstein.O

/-- Angular weight on the completed source index, with its frequency unchanged. -/
def directAngularBareCoefficient (ℓ : ℕ) (η : HeckeFamily.Character) (I : Ideal Eis)
    (hI : primaryIdealGenerator I≠0) (A s : Eis) (hA : A≠0) (H : Eis) : ℂ :=
  elemPsiSix A^ℓ * bareSourceCoefficient η I hI A s hA H

theorem directAngularBareCoefficient_sixth_frequency (ℓ : ℕ) (η : HeckeFamily.Character)
    (I : Ideal Eis) (hI : primaryIdealGenerator I≠0) (A s : Eis)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : Eis) (hcop : IsCoprime v (A*s)) :
    directAngularBareCoefficient ℓ η I hI A s
      (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (v^6*H)=
    directAngularBareCoefficient ℓ η I hI A s
      (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H := by
  unfold directAngularBareCoefficient
  rw [bareSourceCoefficient_sixth_frequency η I hI A s hA hs v H hcop]

theorem directAngularBareCoefficient_norm (ℓ : ℕ) (η : HeckeFamily.Character)
    (I : Ideal Eis) (hI : CubicSieve.Admissible I) (A s : Eis)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s})) (H : Eis) :
    ‖directAngularBareCoefficient ℓ η I hI.2 A s
      (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H‖≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  rw [directAngularBareCoefficient,norm_mul,norm_pow]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one A))).trans
    (bareSourceCoefficient_norm_le η I hI A s hA hs H)

/-- Weight on a prime and its cubic block separates through the exact local scalar. -/
lemma sourceWeightedScalar_angular (v : ℂ) (ℓ : ℕ) (Q : ℝ)
    (eta a gamma1 C omega x w z scalar : ℂ) (e l k m : ℕ) :
    v^((e+3*l)*ℓ)*sourceWeightedScalar Q eta a gamma1 C omega x w z scalar e l k m=
      sourceWeightedScalar Q (v^ℓ*eta) (v^(3*ℓ)*a) gamma1 C omega x w z scalar e l k m := by
  unfold sourceWeightedScalar
  rw [show (e+3*l)*ℓ=ℓ*e+(3*ℓ)*l by ring]
  simp only [pow_add,pow_mul,mul_pow]
  ring

lemma sourcePrincipalTerm_angular (v : ℂ) (ℓ : ℕ) (p : Eis) (hp : Prime p)
    [(Ideal.span {p} : Ideal Eis).IsMaximal] (hg : lambda∉Ideal.span {p})
    (eta a x w z : ℂ) (e l k m : ℕ) :
    v^((e+3*l)*ℓ)*sourcePrincipalTerm p hp hg eta a x w z e l k m=
      sourcePrincipalTerm p hp hg (v^ℓ*eta) (v^(3*ℓ)*a) x w z e l k m :=
  sourceWeightedScalar_angular v ℓ _ eta a _ _ _ x w z _ e l k m

/-- The direct angular prime coefficient retains the original frequency Mellin variable. -/
theorem directAngularBareCoefficient_weighted_prime (ℓ : ℕ) (η : HeckeFamily.Character)
    (p : Eis) (hp : Prime p) [(Ideal.span {p} : Ideal Eis).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (hchar : ringChar (Eis⧸Ideal.span {p})≠2)
    (hprimary : lambda^2∣p-1) (hs : Supported (Ideal.span {p}))
    (e l k m : ℕ) (he : e≤1) (hI : primaryIdealGenerator (Ideal.span {p^e})≠0)
    (x w z : ℂ) :
    directAngularBareCoefficient ℓ η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (p^(6*m))*
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ))=
    sourcePrincipalTerm p hp hg (elemPsiSix p^ℓ*targetMonoid η p)
      (elemPsiSix p^(3*ℓ)*actualACube η p) x w z e l k m := by
  rw [directAngularBareCoefficient,map_pow,←pow_mul,mul_assoc,
    bareSourceCoefficient_weighted_prime η p hp hg hchar hprimary hs e l k m he hI x w z]
  exact sourcePrincipalTerm_angular (elemPsiSix p) ℓ p hp hg _ _ x w z e l k m

lemma elemPsiSix_eq_star_angularFactor_pow (p : Eis) :
    elemPsiSix p=star (CompletedGauss.angularFactor p)^6 := by
  simp only [elemPsiSix_apply,complexUnitConj_apply,CompletedGauss.angularFactor,
    star_div₀,Complex.star_def,Complex.conj_ofReal]

/-- The angular source of weight ℓ has the correction character of weight 6ℓ+1. -/
lemma angular_actualACube_sq (ℓ : ℕ) (η : HeckeFamily.Character) (p : Eis) :
    (elemPsiSix p^(3*ℓ)*actualACube η p)^2=
      elemPsiSix p^(6*ℓ+1)*HeckeFamily.elementCoeff η p^6 := by
  rw [mul_pow,actualACube_sq,actualAPhase,←elemPsiSix_eq_star_angularFactor_pow,
    ←pow_mul,pow_succ]
  rw [show (3*ℓ)*2=6*ℓ by ring]
  ring

/-- The prime-local series with direct angular weight on the completed index. -/
def directAngularPrimeSeries (ℓ : ℕ) (η : HeckeFamily.Character)
    (p : Eis) (hp : Prime p) [(Ideal.span {p} : Ideal Eis).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m,
    elemPsiSix p^((e.val+3*l)*ℓ)*
      sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e.val l k m

lemma directAngularPrimeSeries_eq (ℓ : ℕ) (η : HeckeFamily.Character)
    (p : Eis) (hp : Prime p) [(Ideal.span {p} : Ideal Eis).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (x w z : ℂ) :
    directAngularPrimeSeries ℓ η p hp hg x w z=
      sourcePrincipalSeries p hp hg (elemPsiSix p^ℓ*targetMonoid η p)
        (elemPsiSix p^(3*ℓ)*actualACube η p) x w z := by
  simp only [directAngularPrimeSeries,sourcePrincipalTerm_angular,sourcePrincipalSeries]

/-- Exact prime-local factorization: the free sixth-power factor stays spherical. -/
theorem directAngularPrimeSeries_rational (ℓ : ℕ) (η : HeckeFamily.Character)
    (p : Eis) (hp : Prime p) [(Ideal.span {p} : Ideal Eis).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (hc : ringChar (Eis⧸Ideal.span {p})≠2)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    directAngularPrimeSeries ℓ η p hp hg x w z=
      (1-(elemPsiSix p^ℓ*targetMonoid η p)*(Q:ℂ)^(-x))/
        ((1-(Q:ℂ)^(-6*z))*(1-(Q:ℂ)^(-w)))*
      unramifiedClosed Q (elemPsiSix p^(6*ℓ+1)*HeckeFamily.elementCoeff η p^6)
        (elemPsiSix p^ℓ*targetMonoid η p) 1 x w z := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ2 : 2≤Q := by
    have hn : (2:ℕ)≤Ideal.absNorm (Ideal.span {p}) := HeckeIdealSeries.prime_norm_two_le
      ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩
    dsimp only [Q]
    exact_mod_cast hn
  have hQ0 : 0<Q := by linarith only [hQ2]
  have hQ1 : 1<Q := by linarith only [hQ2]
  have hchar : ‖elemPsiSix p^ℓ*targetMonoid η p‖≤1 := by
    rw [norm_mul,norm_pow]
    exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one p))
      (targetMonoid_norm_le_one η p) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hphase : ‖(elemPsiSix p^(3*ℓ)*actualACube η p)^2‖≤1 := by
    rw [angular_actualACube_sq,norm_mul,norm_pow,norm_pow]
    exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one p))
      (pow_le_one₀ (norm_nonneg _) (targetMonoid_norm_le_one η p))
      (by positivity) zero_le_one).trans_eq (one_mul 1)
  have hV : ‖coordV Q z‖<1 := by
    rw [coordV_norm Q hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith only [hz])
  have hR : ‖coordR Q ((elemPsiSix p^(3*ℓ)*actualACube η p)^2) x z‖<1 := by
    apply (coordR_norm_le Q hQ0 _ x z hphase).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith only [hx,hz])
  have hW : ‖coordW Q 1 w‖<1 := by
    apply (coordW_norm_le Q hQ0 1 w (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith only [hw])
  have hD : 1-coordD Q (elemPsiSix p^ℓ*targetMonoid η p) 1 x≠0 := by
    apply one_sub_ne_zero_of_norm_lt_one
    apply (coordD_norm_le Q hQ0 _ 1 x hchar (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith only [hx])
  rw [directAngularPrimeSeries_eq,sourcePrincipalSeries_eq p hp hg hc _ _ _ _ _ hV hR hW,
    principalFullSeries_euler_identity p hp hg hc _ _ _ _ _ hV hR hW hD,
    angular_actualACube_sq]
  simp only [coordD,coordV,coordW,star_one,mul_one,one_mul]

end
end ProbePhysical
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
