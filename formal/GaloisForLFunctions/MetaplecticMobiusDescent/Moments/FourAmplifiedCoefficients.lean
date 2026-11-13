/-
The four amplified coefficients adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.SecondChildPowerBudgets

/-!
# The four amplified coefficients

Main and error powers and source coefficients of the first amplified stage with the power
reference identity; part rows and energies of the second energy split; source input
reindexing.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstAmplifiedFourCoefficients
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein 
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedAllowance
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstMixedExceptionalLow CenteredMomentFirstMixedDiagonal
open CenteredMomentSuccessorPaidParameters
local notation "O"=> Eisenstein.O
local notation "Ray"=> RayFourExpansion.RayCharacter

def reference (q V C Z allowance:ℝ):ℝ:=q*(V/C)^2*Z^allowance

def mainCores (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ):Fin 4→ℝ:=
  ![(V/C)*q*(V/C)*Z^(ell+deficit/6+paid)/reference q V C Z allowance,
    (V/C)*(V/C)^((1:ℝ)/3)*Kmain^((5:ℝ)/6)*Z^(-2*max r 0/3)/reference q V C Z allowance,
    (V/C)*Kmain*(V/C)^eps/reference q V C Z allowance,
    (V/C)*Kmain*Z^(-saving)/reference q V C Z allowance]

def errorCores (p:O)(k:ℕ)(q V C Z allowance Kerror deficit paid eps saving r:ℝ):Fin 4→ℝ:=
  ![(V/C)*localErrorCost p (k-1)*q*Z^(errorMoving p Z k)*
      (V/C/(normValue p)^k)*Z^(errorRemoval p Z k+deficit/6+paid)/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*(V/C/(normValue p)^k)^((1:ℝ)/3)*
      Kerror^((5:ℝ)/6)*Z^(-2*max r 0/3)/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*Kerror*(V/C/(normValue p)^k)^eps/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*Kerror*Z^(-saving)/reference q V C Z allowance]

def averagedCoefficients (P:Finset (Ideal O))(mainFactor:ℝ)(H main:Fin 4→ℝ)
    (error:elementPool P→Fin 3→Ray→Fin 4→ℝ):Fin 4→ℝ:=fun j=>
  (56/(P.card:ℝ))*(mainFactor*H j*main j+
    ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)

lemma actual_valuation_mass : (∑i:Fin 3,16*(errorIndex i+2:ℝ)^2)=1872 := by
  norm_num [Fin.sum_univ_succ,errorIndex]

theorem actual_error_average (P:Finset (Ideal O))(hne:P.Nonempty)
    (hp:∀Q∈P,Prime Q)(hbad:∀Q∈P,Q∉fixedBadPrimes)
    (f:elementPool P→Fin 3→Ray→ℝ)(E:ℝ)(_hE:0≤ E)
    (hf:∀p i χ,f p i χ≤ E):
    (1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
      16*(errorIndex i+2:ℝ)^2*∑χ:Ray,f p i χ)≤
        1872*(Fintype.card Ray:ℝ)*E := by
  have hn:(0:ℝ)< P.card:=by exact_mod_cast hne.card_pos
  have hc:Fintype.card (elementPool P)=P.card:=by
    rw [Fintype.card_coe,elementPool_card P hp hbad]
  have hh:(∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,f p i χ)≤
      ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,E:=by
    apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _=> hf p i χ)) (by positivity)
  apply (mul_le_mul_of_nonneg_left hh (by positivity:0≤1/(P.card:ℝ))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←Finset.sum_mul,actual_valuation_mass,hc]
  field_simp

lemma main_paid_core (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ)
    (hq:0< q)(hV:0< V)(hC:0< C)(hZ:1< Z)(hB:0≤ allowance)(hdef:0≤ deficit):
    Z^(-ell)*mainCores q V C Z allowance Kmain ell deficit paid eps saving r 0≤
      Z^(deficit+paid) := by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hx:0< V/C:=div_pos hV hC
  have he:mainCores q V C Z allowance Kmain ell deficit paid eps saving r 0=
      Z^(ell+deficit/6+paid-allowance):=by
    dsimp [mainCores,reference]
    rw [Real.rpow_sub hz]
    field_simp
  rw [he,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

lemma error_paid_core (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)
    (q V C Z allowance Kerror deficit paid eps saving r:ℝ)
    (hq:0< q)(hV:0< V)(hC:0< C)(hZ:1< Z)(hB:0≤ allowance)(hdef:0≤ deficit):
    errorCores p k q V C Z allowance Kerror deficit paid eps saving r 0≤ Z^(deficit+paid) := by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hx:0< V/C:=div_pos hV hC
  have hpv:=normValue_pos p hp
  have hw:=actual_error_weight p hp Z hZ k hk
  have hs:localErrorCost p (k-1)*Z^(errorMoving p Z k)≤1:=by
    have hh:=mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hz.le (errorMoving p Z k))
    rw [←Real.rpow_add hz,neg_add_cancel,Real.rpow_zero] at hh
    exact hh
  have he:errorCores p k q V C Z allowance Kerror deficit paid eps saving r 0=
      (localErrorCost p (k-1)*Z^(errorMoving p Z k))*Z^(deficit/6+paid-allowance):=by
    dsimp [errorCores,reference]
    rw [Real.rpow_sub hz,show errorRemoval p Z k+deficit/6+paid=
      errorRemoval p Z k+(deficit/6+paid) by ring,Real.rpow_add hz,errorRemoval_power p hp Z hZ k]
    field_simp
  rw [he]
  calc
    _≤1*Z^(deficit/6+paid-allowance):=mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hz.le _)
    _≤ Z^(deficit+paid):=by rw [one_mul];apply Real.rpow_le_rpow_of_exponent_le hZ.le;linarith

theorem actual_main_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving r Mdecl Mcap:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hs:0≤ sigma)(heps:0≤ eps)(hM:0≤ Mdecl)
    (hcap:Mdecl≤ Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤ Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D}):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    ∀j:Fin 4,Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kmain (sigma/3) (Mdecl-M0) paid eps saving r j≤
      Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j) := by
  dsimp only
  have hz:0< Z:=zero_lt_one.trans hZ
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hr:0< mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  have havg:Z^(-sigma/3)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hZ.le (by linarith)
  have hA:Real.logb Z V≤ Mdecl:=by linarith
  have hAcap:Real.logb Z V≤ Mcap:=hA.trans hcap
  intro j
  fin_cases j
  · have hh:=main_paid_core (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector,neg_div] using hh
  · have hh:=actual_main_exceptional_reference η τ C D
      (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve r hZ hmod hK hV
    have ht:Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 1≤
        Z^(Real.logb Z V-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+
          4*sigma/3+5*(delta+reserve)/6):=by
      convert hh using 1 ; dsimp [mainCores,reference] ; ring
    apply ht.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith
  · have hh:=actual_main_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve eps hK hV hZ heps hmod
    have hc0:0≤ mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 2:=by
      dsimp [mainCores,reference];positivity
    apply (mul_le_mul_of_nonneg_right havg hc0).trans
    rw [one_mul]
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    have he:=mul_le_mul_of_nonneg_left hAcap heps
    linarith
  · have hh:=actual_main_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve 0 hK hV hZ (by norm_num) hmod
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    have hcore:mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          2*sigma+delta+reserve)*Z^(-saving):=by
      convert ht using 1 <;> first | rfl | (dsimp [mainCores,reference]; ring)
    have ht':=mul_le_mul_of_nonneg_left hcore (Real.rpow_nonneg hz.le (-sigma/3))
    apply ht'.trans
    calc
      _≤1*(Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          2*sigma+delta+reserve)*Z^(-saving)):=mul_le_mul_of_nonneg_right havg (by positivity)
      _≤ _:=by
        rw [one_mul,←Real.rpow_add hz]
        apply Real.rpow_le_rpow_of_exponent_le hZ.le
        dsimp [lossVector]
        linarith

theorem actual_error_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving r Mdecl Mcap:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hs:0≤ sigma)(heps:0≤ eps)(hM:0≤ Mdecl)
    (hcap:Mdecl≤ Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤ Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))(hbad:fixedBadPrimes⊆Sbad)
    (p:O)(hp:p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k;
    ∀j:Fin 4,errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kerror (Mdecl-M0) paid eps saving r j≤
      Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j) := by
  dsimp only
  have hz:0< Z:=zero_lt_one.trans hZ
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hpdata:=elementPool_data _ (fun Q hQ=>(primePool_data M H Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad _ _ _ Q hQ).2) p hp
  have hp0:p≠0:=hpdata.1.ne_zero
  have hr:0< errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by unfold errorCommonRadius;positivity
  have hA:Real.logb Z V≤ Mdecl:=by linarith
  have hAcap:Real.logb Z V≤ Mcap:=hA.trans hcap
  intro j
  fin_cases j
  · have hh:=error_paid_core p hp0 k hk (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
      (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector] using hh
  · have hh:=actual_error_exceptional_reference η τ C D
      (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve r hZ hmod M H Sbad hbad p hp k hk hK hV
    have ht:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 1≤
        Z^(Real.logb Z V-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+
          3*sigma/2+5*(delta+reserve)/6):=by
      convert hh using 1 ; dsimp [errorCores,reference] ; ring
    apply ht.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith
  · have hh:=actual_error_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve eps hK hV hZ heps hmod p hp0 k hk
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    have he:=mul_le_mul_of_nonneg_left hAcap heps
    linarith
  · have hh:=actual_error_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve 0 hK hV hZ (by norm_num) hmod p hp0 k hk
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    have hcore:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          sigma+delta+reserve)*Z^(-saving):=by
      convert ht using 1 <;> first | rfl | (dsimp [errorCores,reference]; ring)
    apply hcore.trans
    rw [←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith

def sourceCoefficients (P:Finset (Ideal O))(mainFactor:ℝ)(amain:Fin 4→ℝ)
    (aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ):Fin 4→ℝ:=fun j=>
  (56/(P.card:ℝ))*(mainFactor*amain j+
    ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*localErrorCost p (errorIndex i)*
      ∑χ:Ray,aerror p i χ j*((normValue p)^(errorIndex i+1))^(-alpha j))

lemma shortened_power (V q:ℝ)(k:ℕ)(alpha:ℝ)(hV:0≤ V)(hq:0≤ q):
    (V/q^k)^alpha=V^alpha*(q^k)^(-alpha):=by
  rw [Real.div_rpow hV (pow_nonneg hq k),Real.rpow_neg (pow_nonneg hq k),div_eq_mul_inv]

theorem source_coefficients_identity (P:Finset (Ideal O))(mainFactor V:ℝ)(hV:0≤ V)
    (amain:Fin 4→ℝ)(aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ):
    (∑j:Fin 4,sourceCoefficients P mainFactor amain aerror alpha j*V^(alpha j))=
    (56/(P.card:ℝ))*(mainFactor*(∑j:Fin 4,amain j*V^(alpha j))+
      ∑p:elementPool P,∑i:Fin 3,(16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
        (errorIndex i+2:ℝ)*∑χ:Ray,∑j:Fin 4,aerror p i χ j*
          (V/(normValue p)^(errorIndex i+1))^(alpha j)) := by
  have hnorm:∀p:O,0≤ normValue p:=by intro p;unfold normValue;positivity
  let f:=fun (j:Fin 4) (p:elementPool P) (i:Fin 3) (χ:Ray)=>
    16*(errorIndex i+2:ℝ)^2*localErrorCost p (errorIndex i)*
      (aerror p i χ j*((normValue p)^(errorIndex i+1))^(-alpha j))*V^(alpha j)
  have hswap:(∑j:Fin 4,∑p:elementPool P,∑i:Fin 3,∑χ:Ray,f j p i χ)=
      ∑p:elementPool P,∑i:Fin 3,∑χ:Ray,∑j:Fin 4,f j p i χ:=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  calc
    _=(56/(P.card:ℝ))*∑j:Fin 4,
        (mainFactor*amain j*V^(alpha j)+
          (∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*localErrorCost p (errorIndex i)*
            ∑χ:Ray,aerror p i χ j*((normValue p)^(errorIndex i+1))^(-alpha j))*V^(alpha j)):=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      unfold sourceCoefficients
      ring
    _=(56/(P.card:ℝ))*(mainFactor*(∑j:Fin 4,amain j*V^(alpha j))+
        ∑j:Fin 4,∑p:elementPool P,∑i:Fin 3,∑χ:Ray,f j p i χ):=by
      congr 1
      rw [Finset.sum_add_distrib]
      congr 1
      · simp only [Finset.mul_sum,mul_assoc]
      · simp only [f,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    _=(56/(P.card:ℝ))*(mainFactor*(∑j:Fin 4,amain j*V^(alpha j))+
        ∑p:elementPool P,∑i:Fin 3,∑χ:Ray,∑j:Fin 4,f j p i χ):=by rw [hswap]
    _=_:=by
      congr 2
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [shortened_power V (normValue p) _ _ hV (hnorm _)]
      dsimp [f]
      ring

theorem averaged_coefficients_bound (P:Finset (Ideal O))(hne:P.Nonempty)
    (hp:∀Q∈P,Prime Q)(hbad:∀Q∈P,Q∉fixedBadPrimes)
    (Z ell primeLoss mainFactor:ℝ)(hZ:1< Z)(hloss:0≤ primeLoss)
    (hfactor:0≤ mainFactor)(hcard:Z^(ell-primeLoss)≤(P.card:ℝ))
    (H main loss:Fin 4→ℝ)(error:elementPool P→Fin 3→Ray→Fin 4→ℝ)
    (hH:∀j,0≤ H j)(hm:∀j,Z^(-ell)*main j≤ Z^(loss j))
    (he:∀p i χ j,error p i χ j≤ Z^(loss j)):
    ∀j,averagedCoefficients P mainFactor H main error j≤
      56*(mainFactor+1872*(Fintype.card Ray:ℝ))*H j*Z^(loss j+primeLoss) := by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hn:(0:ℝ)< P.card:=by exact_mod_cast hne.card_pos
  have hinv:(1/(P.card:ℝ))≤ Z^(-ell+primeLoss):=by
    have hh:=one_div_le_one_div_of_le (Real.rpow_pos_of_pos hz _) hcard
    simpa [one_div,←Real.rpow_neg hz.le,neg_sub,sub_eq_add_neg,add_comm] using hh
  intro j
  have hm':main j≤ Z^(ell+loss j):=by
    have hh:=mul_le_mul_of_nonneg_left (hm j) (Real.rpow_nonneg hz.le ell)
    rw [←mul_assoc,←Real.rpow_add hz,add_neg_cancel,Real.rpow_zero,one_mul,
      ←Real.rpow_add hz] at hh
    exact hh
  have hmain:(1/(P.card:ℝ))*main j≤ Z^(loss j+primeLoss):=by
    calc
      _≤(1/(P.card:ℝ))*Z^(ell+loss j):=mul_le_mul_of_nonneg_left hm' (by positivity)
      _≤ Z^(-ell+primeLoss)*Z^(ell+loss j):=mul_le_mul_of_nonneg_right hinv (by positivity)
      _=Z^(loss j+primeLoss):=by rw [←Real.rpow_add hz];congr 1;ring
  have herr:=actual_error_average P hne hp hbad (fun p i χ=> H j*error p i χ j)
    (H j*Z^(loss j)) (mul_nonneg (hH j) (Real.rpow_nonneg hz.le _)) (fun p i χ=> mul_le_mul_of_nonneg_left (he p i χ j) (hH j))
  have hl:Z^(loss j)≤ Z^(loss j+primeLoss):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have herr':(1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
      16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)≤
      1872*(Fintype.card Ray:ℝ)*(H j*Z^(loss j+primeLoss)):=
    herr.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl (hH j)) (by positivity))
  calc
    _=56*(mainFactor*H j*((1/(P.card:ℝ))*main j)+
      (1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
        16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)):=by
      unfold averagedCoefficients;ring
    _≤56*(mainFactor*H j*Z^(loss j+primeLoss)+
      1872*(Fintype.card Ray:ℝ)*(H j*Z^(loss j+primeLoss))):=by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hmain (mul_nonneg hfactor (hH j))) herr') (by norm_num)
    _=_:=by ring

/-- The four averaged coefficients obey the declared low-height loss bounds. -/
theorem actual_low_four_coefficients
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hs:0< sigma)(heps:0≤ eps)(hM:0≤ Mdecl)
    (hcap:Mdecl≤ Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤ Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)(hloss:0≤ primeLoss)(hMamp:0≤ Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (H:Fin 4→ℝ)(hH:∀j,0≤ H j)(rmain:ℝ)
    (rerror:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3)))→Fin 3→Ray→ℝ):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z;
    let main:=mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-M0) paid eps saving rmain;
    let error:=fun (p:elementPool P) (i:Fin 3) (χ:Ray)=>
      errorCores p (errorIndex i+1) (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
        (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ))
          sigma delta reserve p (errorIndex i+1)) (Mdecl-M0) paid eps saving (rerror p i χ);
    ∀j,averagedCoefficients P ((Mamp+2*sigma)/(sigma/6)) H main error j≤
      56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
        Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss) := by
  dsimp only
  have hz:0< Z:=zero_lt_one.trans hZ
  have hne:(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).Nonempty:=by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.rpow_pos_of_pos hz (sigma/3-primeLoss)).trans_le hcard
  have hmain:=actual_main_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
    rmain Mdecl Mcap hK hV hZ hs.le heps hM hcap hactual hlow hmod
  have herror:=fun (p:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))))
      (i:Fin 3) (χ:Ray)=>
    actual_error_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
      (rerror p i χ) Mdecl Mcap hK hV hZ hs.le heps hM hcap hactual hlow hmod
      M Hray Sbad hbad p p.property (errorIndex i+1)
      (by fin_cases i <;> norm_num [errorIndex])
  exact averaged_coefficients_bound _ hne
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).2)
    Z (sigma/3) primeLoss ((Mamp+2*sigma)/(sigma/6)) hZ hloss
    (div_nonneg (by linarith) (by positivity)) hcard H _ _ _ hH
    (by simpa only [neg_div] using hmain) herror

theorem source_normalized_identity (P:Finset (Ideal O))(mainFactor b V C q Z allowance eps:ℝ)
    (N:ℕ)(alpha:Fin 4→ℝ)(amain:Fin 4→ℝ)
    (aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)
    (hV:0< V)(hC:0< C)(hq:0< q)(hZ:0< Z):
    ∀j,CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
        (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C ^ eps*(b^N)^(alpha j)*averagedCoefficients P mainFactor (fun _=>1)
        (fun j=>(V/C)*amain j*(V/C)^(alpha j)/reference q V C Z allowance)
        (fun p i χ j=>(V/C)*localErrorCost p (errorIndex i)*aerror p i χ j*
          (V/C/(normValue p)^(errorIndex i+1))^(alpha j)/reference q V C Z allowance) j := by
  have hx:0< V/C:=div_pos hV hC
  have hnorm:∀p:O,0≤ normValue p:=by intro p;unfold normValue;positivity
  intro j
  have hden:reference q V C Z allowance≠0:=by unfold reference;positivity
  have he:CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
      (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C ^ eps*(b^N)^(alpha j)*((V/C)*sourceCoefficients P mainFactor amain aerror alpha j*
        (V/C)^(alpha j)/reference q V C Z allowance):=by
    unfold CenteredMomentFirstCommonReferencePower.normalizedPower reference
    rw [Real.rpow_sub hx,Real.rpow_one,Real.rpow_neg hZ.le]
    field_simp
  rw [he]
  congr 1
  unfold sourceCoefficients averagedCoefficients
  simp only [one_mul]
  simp only [shortened_power (V/C) _ _ _ hx.le (hnorm _)]
  simp only [div_eq_mul_inv,mul_add,add_mul,Finset.mul_sum,Finset.sum_mul]
  ring_nf

theorem eventually_prime_average_gates
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
    (Sbad:Finset (Ideal O))(sigma primeLoss:ℝ)(hs:0< sigma)(hloss:0< primeLoss):
    ∀ᶠ Z:ℝ in Filter.atTop,1< Z ∧
      (primePool M H Sbad (1/2) 1 (Z^(sigma/3))).Nonempty ∧
      Z^(sigma/3-primeLoss)≤(primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card := by
  filter_upwards [eventually_actual_pool_card M H hH Sbad (sigma/3) primeLoss (by positivity) hloss,
    Filter.eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_,hc⟩
  apply Finset.card_pos.mp
  exact_mod_cast (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/3-primeLoss)).trans_le hc

lemma source_coefficients_nonneg (P:Finset (Ideal O))(mainFactor:ℝ)(hmain:0≤ mainFactor)
    (amain:Fin 4→ℝ)(aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ)
    (ha:∀j,0≤ amain j)(he:∀p i χ j,0≤ aerror p i χ j):
    ∀j,0≤ sourceCoefficients P mainFactor amain aerror alpha j := by
  intro j
  have hc:∀p:O,∀n:ℕ,0≤ localErrorCost p n:=by
    intro p n
    have hn:0≤ normValue p:=by unfold normValue;positivity
    unfold localErrorCost
    split <;> positivity
  unfold sourceCoefficients
  apply mul_nonneg (by positivity)
  apply add_nonneg (mul_nonneg hmain (ha j))
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (mul_nonneg (by positivity) (hc p (errorIndex i)))
  apply Finset.sum_nonneg
  intro χ _
  exact mul_nonneg (he p i χ j) (Real.rpow_nonneg (by unfold normValue;positivity) _)

def mainPowers (q Z Kmain ell deficit paid saving r:ℝ):Fin 4→ℝ:=
  ![q*Z^(ell+deficit/6+paid),Kmain^((5:ℝ)/6)*Z^(-2*max r 0/3),Kmain,Kmain*Z^(-saving)]

def errorPowers (p:O)(k:ℕ)(q Z Kerror deficit paid saving r:ℝ):Fin 4→ℝ:=
  ![q*Z^(errorMoving p Z k)*Z^(errorRemoval p Z k+deficit/6+paid),
    Kerror^((5:ℝ)/6)*Z^(-2*max r 0/3),Kerror,Kerror*Z^(-saving)]

lemma main_core_power (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ):
    ∀j,mainCores q V C Z allowance Kmain ell deficit paid eps saving r j=
      (V/C)*mainPowers q Z Kmain ell deficit paid saving r j*
        (V/C)^(CenteredMomentSecondChildPowerBudget.powers eps j)/reference q V C Z allowance := by
  intro j
  fin_cases j <;> simp [mainCores,mainPowers,CenteredMomentSecondChildPowerBudget.powers] <;> ring

lemma error_core_power (p:O)(k:ℕ)(q V C Z allowance Kerror deficit paid eps saving r:ℝ):
    ∀j,errorCores p k q V C Z allowance Kerror deficit paid eps saving r j=
      (V/C)*localErrorCost p (k-1)*errorPowers p k q Z Kerror deficit paid saving r j*
        (V/C/(normValue p)^k)^(CenteredMomentSecondChildPowerBudget.powers eps j)/reference q V C Z allowance := by
  intro j
  fin_cases j <;> simp [errorCores,errorPowers,CenteredMomentSecondChildPowerBudget.powers] <;> ring

theorem actual_power_reference_identity (P:Finset (Ideal O))(mainFactor b V C q Z allowance eps:ℝ)
    (N:ℕ)(H:Fin 4→ℝ)(Kmain ell deficit paid saving rmain:ℝ)
    (Kerror rerror:elementPool P→Fin 3→Ray→ℝ)
    (hV:0< V)(hC:0< C)(hq:0< q)(hZ:0< Z):
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=> H j*mainPowers q Z Kmain ell deficit paid saving rmain j;
    let aerror:=fun (p:elementPool P) (i:Fin 3) (χ:Ray) (j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) q Z (Kerror p i χ) deficit paid saving (rerror p i χ) j;
    ∀j,CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
      (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C ^ eps*(b^N)^(alpha j)*averagedCoefficients P mainFactor H
        (mainCores q V C Z allowance Kmain ell deficit paid eps saving rmain)
        (fun p i χ=> errorCores p (errorIndex i+1) q V C Z allowance (Kerror p i χ)
          deficit paid eps saving (rerror p i χ)) j := by
  dsimp only
  intro j
  rw [source_normalized_identity P mainFactor b V C q Z allowance eps N _ _ _ hV hC hq hZ j]
  congr 1
  unfold averagedCoefficients
  simp only [one_mul]
  rw [main_core_power]
  congr 2
  · ring
  · apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro χ _
    rw [error_core_power]
    simp only [Nat.add_sub_cancel]
    ring

end CenteredMomentFirstAmplifiedFourCoefficients

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentSecondActivePhysicalDictionary
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorColumns
open CenteredMomentSecondSectorFrequency CenteredMomentActiveSource
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentSecondWholeKernel CenteredMomentLogDyadic
open CenteredMomentSecondSectorRetained CenteredMomentSmooth
local notation "O"=> Eisenstein.O

 theorem sectorPool_active (C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(β:Ideal O→ℂ):
    sectorPool C hC (activeSource S β)=(sectorPool C hC S).filter (fun I=>β (C*I)≠0):=by
  ext I
  simp only [sectorPool,Finset.mem_filter,mem_residualPool,supportedColumns_active]
  tauto

 theorem sector_sum_active (C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(β f:Ideal O→ℂ)
    (hf:∀I,β (C*I)=0→f I=0):
    (∑I∈sectorPool C hC (activeSource S β),f I)=∑I∈sectorPool C hC S,f I:=by
  rw [sectorPool_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h:β (C*I)=0
  · simp only [h,ne_eq,not_true_eq_false,ite_false,hf I h]
  · simp only [h,ne_eq,not_false_eq_true,ite_true]

 theorem sector_pair_sum_active (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(f:Ideal O→Ideal O→ℂ)
    (hleft:∀I J,β (C*I)=0→f I J=0)(hright:∀I J,β (D*J)=0→f I J=0):
    (∑I∈sectorPool C hC (activeSource S β),∑J∈sectorPool D hD (activeSource S β),f I J)=
      ∑I∈sectorPool C hC S,∑J∈sectorPool D hD S,f I J:=by
  simp_rw [sector_sum_active D hD S β _ (fun J h=> hright _ J h)]
  apply sector_sum_active C hC S β
  intro I h
  exact Finset.sum_eq_zero (fun J hJ=> hleft I J h)

 theorem sectorFrequency_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(F:O→Ideal O→Ideal O→ℂ)(z:O):
    sectorFrequency η t S β C D hC hD F z=
      sectorFrequency η t (activeSource S β) β C D hC hD F z:=by
  let f:Ideal O→Ideal O→ℂ:=fun I J=>
    if hI:Supported (C*I) then if hJ:Supported (D*J) then
      (if IsCoprime I J then idealCorrelation (C*I) (D*J) hI hJ z else 0)*
        ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*F z I J
      else 0 else 0
  have he (T:Finset (Ideal O)):
      sectorFrequency η t T β C D hC hD F z=
        ∑I∈sectorPool C hC.1 T,∑J∈sectorPool D hD.1 T,f I J:=by
    calc
      _=∑I:sectorPool C hC.1 T,∑J:sectorPool D hD.1 T,f I J:=by
        unfold sectorFrequency
        apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro J hJ
        have hc:Supported (C*I):=(supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 T I⟩
        have hd:Supported (D*J):=(supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 T J⟩
        simp only [f,dif_pos hc,dif_pos hd]
      _=_:=by
        simp_rw [Finset.sum_coe_sort]
        exact Finset.sum_coe_sort (sectorPool C hC.1 T)
          (fun I=>∑J∈sectorPool D hD.1 T,f I J)
  rw [he S,he (activeSource S β)]
  symm
  apply sector_pair_sum_active C D hC.1 hD.1 S β f
  · intro I J h
    simp only [f,h,zero_mul,mul_zero]
    split_ifs <;> rfl
  · intro I J h
    simp only [f,h,zero_mul,star_zero,mul_zero]
    split_ifs <;> rfl

 theorem physicalBlock_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t (activeSource S β) β C D hC hD U R rows W K n:=by
  unfold physicalBlock
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  exact sectorFrequency_active η t S β C D hC hD
    (fun j I J=> physicalKernel C D W K R j I J*
      ((dyadicWeight (n 0) (secondEffectiveScale C D
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K)*
        dyadicWeight (n 1) (normValue z)*dyadicWeight (n 2) (I.absNorm:ℝ)*
        dyadicWeight (n 3) (J.absNorm:ℝ):ℝ):ℂ)) _

 theorem normalizedBlock_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    normalizedBlock η t S β C D hC hD U R rows W K n=
      normalizedBlock η t (activeSource S β) β C D hC hD U R rows W K n:=by
  unfold normalizedBlock
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  exact sectorFrequency_active η t S β C D hC hD
    (fun _ I J=> wholeKernel W (fun _=> logAnnulus)
      (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
      (Real.log (secondEffectiveScale C D
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/dyadicScale (n 0)))
      (Real.log (normValue z/dyadicScale (n 1)))
      (Real.log ((I.absNorm:ℝ)/dyadicScale (n 2)))
      (Real.log ((J.absNorm:ℝ)/dyadicScale (n 3)))) _

end CenteredMomentSecondActivePhysicalDictionary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentSecondEnergySplit
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentRestrictedEnergy
open CenteredMomentChildRows RayFourExpansion
local notation "O"=> Eisenstein.O

lemma physicalBlock_filter_split (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)(p:O→Prop):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (rows.filter p) W K n+
      physicalBlock η t S β C D hC hD U R (rows.filter (fun z=>¬p z)) W K n:=by
  unfold physicalBlock
  exact (Finset.sum_filter_add_sum_filter_not rows p _).symm

def sourceRows (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):Finset O:=
  liveRows C D U R (retainedRows R (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))

lemma sourceRows_nonzero (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)
    (z:O)(hz:z∈sourceRows C D U R):z≠0:=
  (liveRows_geometry C D U R _ z hz).2.1

def partRows (exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):Finset O:=
  (sourceRows C D U R).filter (fun z=> if exceptional then
    CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z
    else nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z)

lemma partRows_false (η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):
    partRows false η χ Q m C D U R=(sourceRows C D U R).filter (fun z=>
      ¬CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z):=by
  ext z
  simp only [partRows,Bool.false_eq_true,ite_false,Finset.mem_filter,nonexceptional]
  exact ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,sourceRows_nonzero C D U R z h.1,h.2⟩⟩

def partEnergy (exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ):ℂ:=
  ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          W K (fun i=>(n i:ℤ))

theorem original_energy_split (η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ)(hK:0< K)
    (hH:∀I∈S,β I≠0→(I.absNorm:ℝ)≤ H):
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      partEnergy true η χ Q m t S β W K Tsec Z ξ H+
      partEnergy false η χ Q m t S β W K Tsec Z ξ H:=by
  rw [original_live_blocks η t S β W K Tsec Z ξ H hK hH]
  unfold partEnergy
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [partRows_false]
  exact physicalBlock_filter_split η t (activeSource S β) β p.val.1 p.val.2 _ _ U
    (frequencyRadius Tsec Z ξ) (sourceRows p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ)) W K _ _

theorem partEnergy_norm_le (exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ):
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖≤
  ∑p∈liveLabels η S β,
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          W K (fun i=>(n i:ℤ))‖
 :=by
  unfold partEnergy
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    (common_height_norm_le_one η t _ _
      (commonLabels_supported (activeSource S β) _ _ p.property).1.1
      (commonLabels_supported (activeSource S β) _ _ p.property).2.1)).trans
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro U hU
  exact norm_sum_le _ _

end CenteredMomentSecondEnergySplit

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CenteredMomentSecondSupportedChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound CenteredMomentSecondDivisorSupport CenteredMomentSourceRow
open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSecondOriginalChildren
local notation "O" => Eisenstein.O

theorem paired_rows_filter_right
    (D:Ideal O) (hD:Supported D) (S:Finset (Ideal O)) (β:Ideal O→ℂ) (Hsource:ℝ)
    (hβ:∀I,β I≠0→(I.absNorm:ℝ)≤ Hsource)
    (η:Character) (t:ℝ) (A:O) (ξ:RayCharacter)
    (v:Ideal O→sectorPool D hD.1 S→ℂ) (argument:O→O)
    (Ds:Finset (Ideal O)) (rows:Finset O) (scalar:Ideal O→ℂ) (left:Ideal O→O→ℂ) :
    (∑L∈Ds,scalar L*∑z∈rows,left L z*star
      (rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=> divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*v L I)
        (argument z)))=
    ∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ)),
      scalar L*∑z∈rows,left L z*star
      (rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=> divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*v L I)
        (argument z)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hL
  by_cases hn:(L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ)
  · rw [if_pos hn]
  · rw [if_neg hn]
    have hz:=right_divisor_row_zero D hD S β Hsource hβ L (lt_of_not_ge hn) η t A ξ
    simp only [hz,star_zero,mul_zero,Finset.sum_const_zero]

theorem right_source_energy_zero
    (D:Ideal O) (hD:Supported D) (S:Finset (Ideal O)) (β:Ideal O→ℂ) (Hsource:ℝ)
    (hβ:∀I,β I≠0→(I.absNorm:ℝ)≤ Hsource)
    (L:Ideal O) (hL:Hsource/(D.absNorm:ℝ)< L.absNorm)
    (keep:O→Prop) (f:Ideal O→ℂ) (Φ:𝓢(ℝ,ℂ)) (H:ℝ) :
    sourceRestrictedEnergy keep (residualPool D hD.1 S)
      (fun I=> if IsCoprime D I ∧ L∣I then β (D*I) else 0) f Φ H=0 := by
  have hc (I:supportedColumns (residualPool D hD.1 S)) :
      (if IsCoprime D (I:Ideal O) ∧ L∣(I:Ideal O) then β (D*I) else 0)=0 := by
    split_ifs with hi
    · by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (Finset.mem_filter.mp I.property).2.1 β Hsource hβ hn hi.2)
    · rfl
  simp only [sourceRestrictedEnergy,restrictedEnergy,rowPolynomial,hc,zero_mul,
    Finset.sum_const_zero,norm_zero,zero_pow (by decide:2≠0),ite_self,tsum_zero]

theorem actual_block_from_supported_envelopes (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C0:ℝ,0< C0 ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀r:ℝ,0< r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
        (C D:Ideal O) (hC:Supported C) (hD:Supported D),
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I)) →
      ∀Hsource:ℝ,(∀I,β I≠0→(I.absNorm:ℝ)≤ Hsource) →
      Hsource/(D.absNorm:ℝ)≤ Z^B →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0< X → 0< Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤ Ideal.span {(72:O)} →
      lambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),0< H →
      (∀z:O,0≤(Φ (normValue z/H)).re) → (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤ E₁ → 0≤ E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ) → Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool C hC.1 S)
          (fun I=> if IsCoprime C I ∧ L∣I then β (C*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤(E₁/(Ideal.absNorm L:ℝ))*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ) → Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool D hD.1 S)
          (fun I=> if IsCoprime D I ∧ L∣I then β (D*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤(E₂/(Ideal.absNorm L:ℝ))*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=> logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        C0*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨K,hK,hkernel⟩:=CenteredMomentSecondSquarefreeBlock.actual_block_from_squarefree_source W decay J₁ J₂
  obtain ⟨Cm,hCm,hmass⟩:=CenteredMomentMobiusHarmonicMass.full_mass_subpower B δ hB hδ
  refine ⟨max 1 K*Cm,mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hCm,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t S β C D hC hD hCD U A hτ Hsource hβ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  let live (L:Ideal O):Prop:=(L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ)
  let Ds:=divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O))
  let coarse (L:Ideal O):ℝ:=SchwartzPlanePoisson.diagonalControl Φ*max 1 H*
    (∑I∈residualPool C hC.1 S,‖if IsCoprime C I ∧ L∣I then β (C*I) else 0‖)^2
  have hcoarse (L:Ideal O):0≤ coarse L:=
    mul_nonneg (mul_nonneg (SchwartzPlanePoisson.diagonalControl_nonneg Φ) (by positivity)) (sq_nonneg _)
  let F₁:Ideal O→ℝ:=fun L=> if live L then E₁/(L.absNorm:ℝ) else coarse L
  let F₂:Ideal O→ℝ:=fun L=> if live L then E₂/(L.absNorm:ℝ) else 0
  have hF₁ (L:Ideal O):0≤ F₁ L:=by
    dsimp only [F₁];split_ifs
    · exact div_nonneg hE₁ (Nat.cast_nonneg _)
    · exact hcoarse L
  have hF₂ (L:Ideal O):0≤ F₂ L:=by
    dsimp only [F₂];split_ifs
    · exact div_nonneg hE₂ (Nat.cast_nonneg _)
    · exact le_rfl
  have hk:=hkernel r hr η τ t S β C D hC hD hCD U hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor F₁ F₂ hF₁ hF₂
    (by
      intro L hL hsf χ v
      by_cases hl:live L
      · simpa only [F₁,if_pos hl] using hleft L hL hl hsf χ v
      · have hh:=CenteredMomentSourceAbsoluteEnvelope.actual_source_absolute (residualPool C hC.1 S)
          (fun I=> if IsCoprime C I ∧ L∣I then β (C*I) else 0) (τ χ) v
          (nonexceptional η χ Q m A) Φ H hH
        exact hh.trans (by simpa only [F₁,if_neg hl] using
          le_mul_of_one_le_right (hcoarse L) (one_le_pow₀ (by linarith [norm_nonneg v]) (n:=2*J₁))))
    (by
      intro L hL hsf χ v
      by_cases hl:live L
      · simpa only [F₂,if_pos hl] using hright L hL hl hsf χ v
      · rw [right_source_energy_zero D hD S β Hsource hβ L (lt_of_not_ge hl)]
        simp only [F₂,if_neg hl,zero_mul,le_refl])
  have he:(∑L∈Ds,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
      (windowBudget J₁ t (F₁ L)*windowBudget J₂ t (F₂ L)))=
      (∑L∈Ds.filter live,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂):=by
    rw [Finset.sum_mul,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L hL
    by_cases hl:live L
    · rw [if_pos hl]
      simp only [F₁,F₂,if_pos hl]
      rw [CenteredMomentSecondHarmonicBudget.paired_divisor J₁ J₂ t E₁ E₂ _ (Nat.cast_nonneg _)]
      ring
    · have hl' : ¬(L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ):=hl
      simp only [F₂,live,if_neg hl',windowBudget,Real.sqrt_zero,zero_mul,mul_zero]
  have hmass':(∑L∈Ds.filter live,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))≤ Cm*Z^δ:=
    hZ.2 (Ds.filter live) (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hn)
  apply hk.trans
  change K*(∑L∈Ds,_)≤ _
  rw [he]
  calc
    _≤ K*(Cm*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂)):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmass'
        (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _))) hK
    _≤ max 1 K*(Cm*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂)):=
      mul_le_mul_of_nonneg_right (le_max_right _ _)
        (mul_nonneg (mul_nonneg hCm.le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
          (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))
    _=_:=by ring

variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem actual_block_from_supported_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C0 Ce:ℝ,0< C0 ∧ 0< Ce ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀r:ℝ,0< r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (s:Input ι),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤ Z^B → (Ideal.absNorm D:ℝ)≤ Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I)) →
      ∀Hsource:ℝ,(∀I,β I≠0→(I.absNorm:ℝ)≤ Hsource) →
      Hsource/(D.absNorm:ℝ)≤ Z^B →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0< X → 0< Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤ Ideal.span {(72:O)} →
      lambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),∀hH:0< H,
      ∀hΦ:(∀z:O,0≤(Φ (normValue z/H)).re), (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤ E₁ → 0≤ E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤ E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤ E₂*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=> logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        C0*Z^δ*(windowBudget J₁ t (core s C Ce Z δ E₁)*windowBudget J₂ t (core s D Ce Z δ E₂)) := by
  obtain ⟨Ce,hCe,hsource⟩:=actual_height_envelope lo hi B δ hB hδ
  obtain ⟨C0,hC0,hkernel⟩:=actual_block_from_supported_envelopes W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,Ce,hC0,hCe,?_⟩
  filter_upwards [hkernel] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t s hlo hhi R0 seed S β C D hC hD hsC hsD hnC hnD hCD U A hτ Hsource hβ hn
    R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hcore (G:Ideal O) (E:ℝ) (hE:0≤ E):0≤ core s G Ce Z δ E:=by
    unfold core
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCe.le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
      (mul_nonneg (profileCost_nonneg s) hE))
      (mul_nonneg (mul_nonneg s.X₁_pos.le s.X₂_pos.le) (Finset.prod_nonneg (fun i _=>(s.P_pos i).le)))) (Nat.cast_nonneg _)
  apply hZ.2 r hr η τ t S β C D hC hD hCD U hτ Hsource hβ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor (core s C Ce Z δ E₁) (core s D Ce Z δ E₂)
    (hcore C E₁ hE₁) (hcore D E₂ hE₂)
  · intro L hL hcap hsf χ v
    have hNL: (Ideal.absNorm L:ℝ)≤ Z^B:=hcap.trans hn
    have hh:=hsource s hlo hhi (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) C hC R0 seed L hsC hsf
      E₁ Z hE₁ hZ.1 hnC hNL J₁ (τ χ) v (hleft L hL hcap hsf χ v)
    simpa only [envelope_eq_core,sourceRadial,S,β,A] using hh
  · intro L hL hcap hsf χ v
    have hNL: (Ideal.absNorm L:ℝ)≤ Z^B:=hcap.trans hn
    have hh:=hsource s hlo hhi (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) D hD R0 seed L hsD hsf
      E₂ Z hE₂ hZ.1 hnD hNL J₂ (τ χ) v (hright L hL hcap hsf χ v)
    simpa only [envelope_eq_core,sourceRadial,S,β,A] using hh

end CenteredMomentSecondSupportedChildren

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CenteredMomentSecondNonexceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => Eisenstein.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

lemma paired_sqrt (A E₁ E₂ c d:ℝ) (hA:0≤ A) (hE₁:0≤ E₁) (hE₂:0≤ E₂)
    (hc:0< c) (_hd:0< d) :
    Real.sqrt (A*E₁/c)*Real.sqrt (A*E₂/d)=A/Real.sqrt (c*d)*Real.sqrt (E₁*E₂) := by
  rw [←Real.sqrt_mul (div_nonneg (mul_nonneg hA hE₁) hc.le)]
  rw [show A*E₁/c*(A*E₂/d)=A^2*(E₁*E₂)/(c*d) by ring]
  rw [Real.sqrt_div (mul_nonneg (sq_nonneg A) (mul_nonneg hE₁ hE₂)),
    Real.sqrt_mul (sq_nonneg A),Real.sqrt_sq hA]
  ring

omit [DecidableEq ι] in
theorem paired_core_budget (s:Input ι) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (Ce Z δ E₁ E₂ t:ℝ) (hCe:0≤ Ce) (hZ:0≤ Z) (hE₁:0≤ E₁) (hE₂:0≤ E₂)
    (J₁ J₂:ℕ) :
    windowBudget J₁ t (core s C Ce Z δ E₁)*windowBudget J₂ t (core s D Ce Z δ E₂)=
      (Ce*Z^δ*profileCost s*volume s.toData)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
        Real.sqrt (E₁*E₂)*heightEnvelope t^(J₁+J₂)*profileMoment J₁*profileMoment J₂ := by
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hA:0≤ Ce*Z^δ*profileCost s*volume s.toData:=by
    exact mul_nonneg (mul_nonneg (mul_nonneg hCe (Real.rpow_nonneg hZ _)) (profileCost_nonneg s)) (volume_pos s.toData).le
  have he (G:Ideal O) (E:ℝ):core s G Ce Z δ E=
      (Ce*Z^δ*profileCost s*volume s.toData)*E/(G.absNorm:ℝ):=by
    unfold core CenteredMomentExceptionalAmplitudePair.volume
    ring
  rw [he C E₁,he D E₂]
  simp only [windowBudget,pow_add]
  have hh:=paired_sqrt _ E₁ E₂ _ _ hA hE₁ hE₂ hc hd
  calc
    _=(Real.sqrt (_*E₁/(C.absNorm:ℝ))*Real.sqrt (_*E₂/(D.absNorm:ℝ)))*
      (heightEnvelope t^J₁*heightEnvelope t^J₂)*profileMoment J₁*profileMoment J₂:=by ring
    _=_:=by rw [hh]

theorem actual_physical_from_supported_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C0 Ce:ℝ,0< C0 ∧ 0< Ce ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀Kphys:ℝ,0< Kphys → ∀n:Fin 4→ℤ,
      let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (s:Input ι),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤ Z^B → (Ideal.absNorm D:ℝ)≤ Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I)) →
      ∀Hsource:ℝ,(∀I,β I≠0→(I.absNorm:ℝ)≤ Hsource) →
      Hsource/(D.absNorm:ℝ)≤ Z^B →
      ∀(R:ℝ) (rows:Finset O),
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤ Ideal.span {(72:O)} →
      lambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),∀hH:0< H,
      ∀hΦ:(∀z:O,0≤(Φ (normValue z/H)).re), (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤ E₁ → 0≤ E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤ E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤ E₂*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock η t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        (C0*Ce)*Z^(2*δ)*profileCost s*(outerScalar C D Kphys n*normalizer C D U)/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(1+r)^decay := by
  obtain ⟨C0,Ce,hC0,hCe,hkernel⟩:=actual_block_from_supported_children lo hi W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,Ce,hC0,hCe,?_⟩
  filter_upwards [hkernel] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n r η τ t s hlo hhi R0 seed S β C D hC hD hsC hsD hnC hnD hCD U A hτ Hsource hβ hn
    R rows Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hr:0< r:=div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hpow:0<(1+r)^decay:=pow_pos (by linarith) _
  have hh:=hZ.2 r hr η τ t s hlo hhi R0 seed C D hC hD hsC hsD hnC hnD hCD U hτ Hsource hβ hn
    R rows (fun _=> Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
    (fun z=> Real.log (normValue z/dyadicScale (n 1)))
    (dyadicScale (n 2)) (dyadicScale (n 3)) (dyadicScale_pos _) (dyadicScale_pos _)
    Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  change (1+r)^decay*‖normalizedBlock η t S β C D hC hD U R rows W Kphys n‖≤ _ at hh
  rw [paired_core_budget s C D hC hD Ce Z δ E₁ E₂ t hCe.le
    (zero_lt_one.trans hZ.1).le hE₁ hE₂ J₁ J₂] at hh
  have ho:0≤ outerScalar C D Kphys n:=by unfold outerScalar;positivity
  have hno:0≤ normalizer C D U:=(normalizer_pos C D hC U).le
  have hnrows:∀z∈rows,z≠0:=fun z hz=>(hrows z hz).1
  have hp:=mul_le_mul_of_nonneg_left hh (mul_nonneg ho hno)
  have hphys:‖physicalBlock η t S β C D hC hD U R rows W Kphys n‖=
      outerScalar C D Kphys n*normalizer C D U*
        ‖normalizedBlock η t S β C D hC hD U R rows W Kphys n‖:=by
    rw [physicalBlock_eq η t S β C D hC hD U R rows hnrows W Kphys hKphys n,
      norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno]
  rw [hphys]
  apply (div_le_iff₀ (volume_pos s.toData)).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpow).mpr
  have hzz:Z^(2*δ)=Z^δ*Z^δ:=by
    rw [show 2*δ=δ+δ by ring,Real.rpow_add (zero_lt_one.trans hZ.1)]
  rw [hzz]
  convert hp using 1 <;> first | rfl | ring

end CenteredMomentSecondNonexceptionalPhysical

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => Eisenstein.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair

lemma sourceRadial_eq_canonical {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (hm:m≠0)(hml:lambda∣m)(hm2:(2:O)∣m)(n:Fin 4→ℤ):
    sourceRadial (nonexceptional η χ Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))
      ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=> ballProfile_nonneg _)=
      canonicalRadial (τ χ) Q n:=by
  have he:nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)=
      (fun z=> z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z):=by
    funext z
    exact propext (h.nonexceptional_iff χ Q m z hm hml hm2)
  simp only [canonicalRadial,he]

theorem actual_canonical_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C0 Ce:ℝ,0< C0 ∧ 0< Ce ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀Kphys:ℝ,0< Kphys → ∀n:Fin 4→ℤ,
      let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
      ∀(s:Input ι) (τ:RayCharacter→Character),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤ Z^B → (Ideal.absNorm D:ℝ)≤ Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let _A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      Family s.η C D hC hD U τ →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B →
      ∀R:ℝ,
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤ Ideal.span {(72:O)} →
      m≠0 → lambda∣m → (2:O)∣m →
      ∀E₁ E₂:ℝ,
      0≤ E₁ → 0≤ E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (canonicalRadial (τ χ) Q n) L a≤ E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (canonicalRadial (τ χ) Q n) L a≤ E₂*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock s.η s.t S β C D hC hD U R
        (partRows false s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        (C0*Ce)*Z^(2*δ)*profileCost s*(outerScalar C D Kphys n*normalizer C D U)/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(1+r)^decay :=by
  obtain ⟨C0,Ce,hC0,hCe,hbound⟩:=
    CenteredMomentSecondNonexceptionalPhysical.actual_physical_from_supported_children
      lo hi W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,Ce,hC0,hCe,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n r s τ hlo hhi R0 seed S β C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH R Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂ hleft hright
  let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  let rows:=partRows false s.η χ₀ Q m C D U R
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤ sourceRadius s:=by
    intro I hi
    exact (original_column_norm s R0 seed I hz1 hz2 hi).2
  have hHD:sourceRadius s/(D.absNorm:ℝ)≤ Z^B:=by
    have hDN:1≤(D.absNorm:ℝ):=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
    by_cases hp:0≤ sourceRadius s
    · exact (div_le_self hp hDN).trans hH
    · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hp) (Nat.cast_nonneg _)).trans
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  have hrows:∀z∈dyadicRows rows n,nonexceptional s.η χ₀ Q m A z:=by
    intro z hz
    have hh:=Finset.mem_filter.mp ((dyadicRows_subset rows n) hz)
    simpa only [rows,partRows,Bool.false_eq_true,ite_false] using hh.2
  have hmajor:∀z∈dyadicRows rows n,1≤(ballProfile (normValue z/dyadicScale (n 1))).re:=by
    intro z hz
    have hb:=ballProfile_majorizes (dyadicScale (n 1)) (dyadicScale_pos _) z
      (dyadicRows_norm rows n z hz).2.le
    simpa only [normValue_eq_embedding] using hb
  have hleft':∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
      ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
        (sourceRadial (nonexceptional s.η χ Q m A) ballProfile (dyadicScale (n 1))
          (dyadicScale_pos _) (fun z=> ballProfile_nonneg _)) L a≤ E₁*(1+‖v‖)^(2*J₁):=by
    intro L hL hLN hsf χ v b a ha
    rw [sourceRadial_eq_canonical hf χ Q m hm hml hm2 n]
    exact hleft L hL hLN hsf χ v b a ha
  have hright':∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
      ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
        (sourceRadial (nonexceptional s.η χ Q m A) ballProfile (dyadicScale (n 1))
          (dyadicScale_pos _) (fun z=> ballProfile_nonneg _)) L a≤ E₂*(1+‖v‖)^(2*J₂):=by
    intro L hL hLN hsf χ v b a ha
    rw [sourceRadial_eq_canonical hf χ Q m hm hml hm2 n]
    exact hright L hL hLN hsf χ v b a ha
  have hh:=hZ.2 Kphys hKphys n s.η τ s.t s hlo hhi R0 seed C D hC hD hsC hsD hNC hND hCD U
    hf.height_eq (sourceRadius s) hβ hHD R (dyadicRows rows n) Q m χ₀ hQ hml hm2 hrows
    ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun z=> ballProfile_nonneg _) hmajor
    E₁ E₂ hE₁ hE₂ hleft' hright'
  rwa [←physicalBlock_dyadic_rows] at hh

end CenteredMomentSecondNonexceptionalChosenBlock

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CenteredMomentSecondNonexceptionalCost
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => Eisenstein.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondRadicalBudget

theorem actual_canonical_child_cost (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃Ck:ℝ,0< Ck ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀Kphys:ℝ,0< Kphys → ∀n:Fin 4→ℤ,
      let _r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
      ∀(s:Input ι) (τ:RayCharacter→Character),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤ Z^B → (Ideal.absNorm D:ℝ)≤ Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let _A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      Family s.η C D hC hD U τ →
      s.W₁ 0=0 → s.W₂ 0=0 → 0≤ sourceRadius s → sourceRadius s≤ Z^B →
      ∀R:ℝ,
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤ Ideal.span {(72:O)} →
      m≠0 → lambda∣m → (2:O)∣m →
      ∀E₁ E₂:ℝ,
      0≤ E₁ → 0≤ E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (canonicalRadial (τ χ) Q n) L a≤ E₁*((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (canonicalRadial (τ χ) Q n) L a≤ E₂*((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock s.η s.t S β C D hC hD U R
        (partRows false s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        Ck*Z^(2*δ)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂ :=by
  obtain ⟨C0,Ce,hC0,hCe,hbound⟩:=actual_canonical_children lo hi W 1 J₁ J₂ B δ hB hδ
  have hfixed:(0:ℝ)< fixedFactor:=by exact_mod_cast fixedFactor_pos
  refine ⟨4*(fixedFactor:ℝ)*(C0*Ce),by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n s τ hlo hhi R0 seed S β C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH0 hH R Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂ hleft hright
  let rows:=partRows false s.η χ₀ Q m C D U R
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hp:=profileCost_nonneg s
  have hhgt:=heightEnvelope_pos s.t
  have hpm1:=profileMoment_nonneg J₁
  have hpm2:=profileMoment_nonneg J₂
  by_cases hzero:physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n=0
  · rw [hzero,norm_zero,zero_div]
    positivity
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤ sourceRadius s:=
    fun I hi=>(original_column_norm s R0 seed I hz1 hz2 hi).2
  let E:=childEnvelope s.η C D U n
  have hdyad:0< dyadicScale (n 1):=dyadicScale_pos _
  have hE:0≤ E:=by unfold E childEnvelope;positivity
  have hτ:∀χ:RayCharacter,((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)≤ E:=
    family_child_envelope hf s.t S β R rows W Kphys hKphys n hzero
  have hl:∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
      ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) C R0 b) (canonicalRadial (τ χ) Q n) L a≤
        (E₁*E)*(1+‖v‖)^(2*J₁):=by
    intro L hL hLN hsf χ v b a ha
    apply (hleft L hL hLN hsf χ v b a ha).trans
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hτ χ) hE₁)
      (show 0≤(1+‖v‖)^(2*J₁) by positivity)
    simpa only [mul_assoc] using hh
  have hr:∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
      ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) D R0 b) (canonicalRadial (τ χ) Q n) L a≤
        (E₂*E)*(1+‖v‖)^(2*J₂):=by
    intro L hL hLN hsf χ v b a ha
    apply (hright L hL hLN hsf χ v b a ha).trans
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hτ χ) hE₂)
      (show 0≤(1+‖v‖)^(2*J₂) by positivity)
    simpa only [mul_assoc] using hh
  have hh:=hZ.2 Kphys hKphys n s τ hlo hhi R0 seed C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH R Q m χ₀ hQ hm hml hm2 (E₁*E) (E₂*E) (mul_nonneg hE₁ hE) (mul_nonneg hE₂ hE) hl hr
  have hsqrt:Real.sqrt ((E₁*E)*(E₂*E))=E*Real.sqrt (E₁*E₂):=by
    rw [show (E₁*E)*(E₂*E)=E^2*(E₁*E₂) by ring,
      Real.sqrt_mul (sq_nonneg E),Real.sqrt_sq hE]
  simp only [pow_one,hsqrt] at hh
  have hscalar:=actual_source_envelope_scalar s.η s.t S β C D hC hD U R rows W Kphys hKphys n
    (sourceRadius s) hβ hzero
  let F:ℝ:=(C0*Ce)*Z^(2*δ)*profileCost s*Real.sqrt (E₁*E₂)*
    heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂
  have hF:0≤ F:=by dsimp only [F];positivity
  have hsc:=mul_le_mul_of_nonneg_left hscalar hF
  apply hh.trans
  convert hsc using 1 <;> dsimp only [F,E] <;> ring

end CenteredMomentSecondNonexceptionalCost

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentSecondNonexceptionalAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentFirstSectors CenteredMomentSourceRow RayFourExpansion
local notation "O"=> Eisenstein.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma live_harmonic_sum_le (η:Character)(S:Finset (Ideal O))(β:Ideal O→ℂ)(K R H:ℝ):
    (∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑_n:SourceBlocks p.val.1 p.val.2 U K R H,pairWeight p.val.1 p.val.2)≤
    ∑q:ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2:=by
  rw [CenteredMomentSecondBlockHarmonicMass.active_blocks_sum_eq]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun p _ _=> Finset.sum_nonneg (fun U _=> mul_nonneg (Nat.cast_nonneg _) (pairWeight_nonneg _ _)))

theorem part_energy_harmonic_bound (exceptional:Bool)(η:Character)(χ:RayCharacter)
    (Q:Ideal O)(m:O)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H V E:ℝ)(hV:0< V)(hE:0≤ E)
    (hb:∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤ E*pairWeight p.val.1 p.val.2):
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤
      E*(∑q:ActiveBlocks S β K (frequencyRadius Tsec Z ξ) H,
        pairWeight q.1.1.val.1 q.1.1.val.2):=by
  apply (div_le_div_of_nonneg_right
    (partEnergy_norm_le exceptional η χ Q m t S β W K Tsec Z ξ H) hV.le).trans
  simp only [Finset.sum_div]
  calc
    _≤∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          E*pairWeight p.val.1 p.val.2:=by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro n hn
      exact hb p hp U n
    _=E*(∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          pairWeight p.val.1 p.val.2):=by simp only [Finset.mul_sum]
    _≤ _:=mul_le_mul_of_nonneg_left (live_harmonic_sum_le η S β K (frequencyRadius Tsec Z ξ) H) hE

theorem source_part_harmonic_bound (B L Cr ε:ℝ)(hB:0≤ B)(hL:0≤ L)
    (hCr:0< Cr)(hε:0<ε):
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in Filter.atTop,
    ∀(seed:Ideal O),Squarefree seed → seed≠0 →
    ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
    (∀I∈S,β I≠0→seed∣I) → (∀I∈S,β I≠0→(I.absNorm:ℝ)≤ Z^B) →
    ∀(exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)(W:𝓢(ℝ,ℂ))
      (K Tsec ξ H V E:ℝ),0< K → frequencyRadius Tsec Z ξ≤ Cr*Z^L → H≤ Z^B → 0< V → 0≤ E →
    (∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤ E*pairWeight p.val.1 p.val.2) →
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤ E*(C*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C,hC,hmass⟩:=actual_block_harmonic_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hmass] with Z hZ
  intro seed hs hs0 S β hmask hnorm exceptional η χ Q m t W K Tsec ξ H V E hK hR hH hV hE hb
  exact (part_energy_harmonic_bound exceptional η χ Q m t S β W K Tsec Z ξ H V E hV hE hb).trans
    (mul_le_mul_of_nonneg_left (hZ seed hs hs0 S β hmask hnorm K
      (frequencyRadius Tsec Z ξ) H hK hR hH) hE)

end CenteredMomentSecondNonexceptionalAggregate

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentSecondNonexceptionalLiveSource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open  CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem original_nonexceptional_energy (lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (B L Cr δ ε:ℝ)(hB:0≤ B)(hL:0≤ L)(hCr:0< Cr)(hδ:0<δ)(hε:0<ε) :
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀s:Input ι,(∀i,s.lo i=lo i)→(∀i,s.hi i=hi i)→
      s.W₁ 0=0→s.W₂ 0=0→0≤ sourceRadius s→sourceRadius s≤ Z^B→
    ∀R0 seed:Ideal O,Squarefree seed→seed≠0→
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀(χ₀:RayCharacter)(Q:Ideal O)(m:O),Q≤ Ideal.span {(72:O)}→
      m≠0→lambda∣m→(2:O)∣m→
    ∀Kphys Tsec ξ:ℝ,0< Kphys→frequencyRadius Tsec Z ξ≤ Cr*Z^L→
    ∀E₁ E₂:ℝ,0≤ E₁→0≤ E₂→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₂))→
    ‖partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
      C*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ) := by
  obtain ⟨Ck,hCk,hblock⟩:=actual_canonical_child_cost lo hi W J₁ J₂ B δ hB hδ
  obtain ⟨Cm,hCm,hmass⟩:=source_part_harmonic_bound B L Cr ε hB hL hCr hε
  refine ⟨Ck*Cm,mul_pos hCk hCm,?_⟩
  filter_upwards [hblock,hmass] with Z hZ hmassZ
  refine ⟨hZ.1,?_⟩
  intro s hlo hhi hz1 hz2 hH0 hH R0 seed hseed hseed0 S β
  have hg (q:ActiveLabel S β):=actual_common_gates s R0 seed hseed hz1 hz2 q.val.1 q.val.2 q.property
  have hs (q:ActiveLabel S β):=commonLabels_supported (activeSource S β) _ _ q.property
  choose τ hf using fun (q:ActiveLabel S β) (U:Finset (CommonIndex q.val.1 q.val.2))=>
    exists_exceptional_family s.η q.val.1 q.val.2 (hs q).1 (hs q).2 (hg q).2.2.1 U
  refine ⟨τ,hf,?_⟩
  intro χ₀ Q m hQ hm hml hm2 Kphys Tsec ξ hKphys hR E₁ E₂ hE₁ hE₂ hleft hright
  let F:=Ck*Z^(2*δ)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
    Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂
  have hF:0≤ F:=by
    have hp:=profileCost_nonneg s
    have ht:=heightEnvelope_pos s.t
    have hm1:=profileMoment_nonneg J₁
    have hm2:=profileMoment_nonneg J₂
    have hz:0< Z:=zero_lt_one.trans hZ.1
    dsimp only [F]
    positivity
  have hsum:=hmassZ seed hseed hseed0 S β
    (fun I _ hI=> original_column_mask s R0 seed I hI)
    (fun I _ hI=>(original_column_norm s R0 seed I hz1 hz2 hI).2.trans hH)
    false s.η χ₀ Q m s.t W Kphys Tsec ξ (sourceRadius s) (volume s.toData) F
    hKphys hR hH (volume_pos s.toData) hF
  have hlocal:∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      ‖physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))‖/volume s.toData≤ F*pairWeight q.val.1 q.val.2:=by
    intro q hq U n
    by_cases hzero:physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))=0
    · rw [hzero,norm_zero,zero_div]
      exact mul_nonneg hF (pairWeight_nonneg _ _)
    · have hh:=hZ.2 Kphys hKphys (fun i=>(n i:ℤ)) s (τ q U) hlo hhi R0 seed
        q.val.1 q.val.2 (hs q).1 (hs q).2 (hg q).2.2.2.1 (hg q).2.2.2.2.1
        ((hg q).2.2.2.2.2.1.trans hH) ((hg q).2.2.2.2.2.2.trans hH) (hg q).2.2.1 U (hf q U)
        hz1 hz2 hH0 hH (frequencyRadius Tsec Z ξ) Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂
        (hleft q hq U n hzero) (hright q hq U n hzero)
      rw [←physicalBlock_active]
      exact hh.trans_eq (by dsimp only [F,pairWeight];ring)
  have hh:=hsum hlocal
  apply hh.trans_eq
  have hp:Z^(2*δ)*Z^ε=Z^(2*δ+ε):=by rw [Real.rpow_add (zero_lt_one.trans hZ.1)]
  dsimp only [F]
  calc
    _=(Ck*Cm)*(Z^(2*δ)*Z^ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(seed.absNorm:ℝ):=by ring
    _=_:=by rw [hp]
end CenteredMomentSecondNonexceptionalLiveSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentSourceInputReindex
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstAmplificationChoice CenteredMomentOriginalChildEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
local notation "O" => Eisenstein.O
variable {α β : Type*} [Fintype α] [Fintype β]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _
local instance : DecidableEq (β⊕Fin 2) := Classical.decEq _

def reindex (e : α≃β) (s : Input α) : Input β where
  η := s.η
  m := s.m
  A := s.A
  t := s.t
  slots := fun i=> s.slots (e.symm i)
  prime := fun i=> s.prime (e.symm i)
  ν := fun i=> s.ν (e.symm i)
  W := fun i=> s.W (e.symm i)
  lo := fun i=> s.lo (e.symm i)
  hi := fun i=> s.hi (e.symm i)
  P := fun i=> s.P (e.symm i)
  lo_pos := fun i=> s.lo_pos (e.symm i)
  P_pos := fun i=> s.P_pos (e.symm i)
  support := fun i=> s.support (e.symm i)
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  M := fun i=> s.M (e.symm i)
  M_ge_one := fun i=> s.M_ge_one (e.symm i)
  coefficient_bound := fun i=> s.coefficient_bound (e.symm i)
  b₁ := s.b₁
  b₂ := s.b₂
  support₁ := s.support₁
  support₂ := s.support₂
  X₁_pos := s.X₁_pos
  X₂_pos := s.X₂_pos
  Y₁_pos := s.Y₁_pos
  Y₂_pos := s.Y₂_pos
  same_product := s.same_product
  rows := s.rows
  weight := s.weight
  weight_nonneg := s.weight_nonneg
  plain₁ := s.plain₁
  plain₂ := s.plain₂
  plain₁_ne := s.plain₁_ne
  plain₂_ne := s.plain₂_ne
  coverage₁ := s.coverage₁
  coverage₂ := s.coverage₂
  ν_bound := fun i=> s.ν_bound (e.symm i)
  W_bound := fun i=> s.W_bound (e.symm i)
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i=> s.lower_le (e.symm i)
  upper_ge := fun i=> s.upper_ge (e.symm i)

def tupleMap (e : α≃β) : Tuple α≃Tuple β :=
  (e.sumCongr (Equiv.refl (Fin 2))).arrowCongr (Equiv.refl (Ideal O))

omit [Fintype α] [Fintype β] in
lemma tupleMap_apply (e : α≃β) (v : Tuple α) (j : β⊕Fin 2) :
    tupleMap e v j = v ((e.sumCongr (Equiv.refl (Fin 2))).symm j) := rfl

lemma tupleMap_product (e : α≃β) (v : Tuple α) :
    finiteTupleProduct (tupleMap e v)=finiteTupleProduct v :=
  (e.sumCongr (Equiv.refl (Fin 2))).symm.prod_comp v

lemma pools_map (e : α≃β) (s : Input α) :
    (Fintype.piFinset s.pools).image (tupleMap e) = Fintype.piFinset (reindex e s).pools := by
  ext v
  simp only [Finset.mem_image,Fintype.mem_piFinset]
  constructor
  · rintro ⟨w,hw,rfl⟩ j
    cases j with
    | inl i => exact hw (Sum.inl (e.symm i))
    | inr i => exact hw (Sum.inr i)
  · intro hv
    refine ⟨(tupleMap e).symm v,?_,(tupleMap e).apply_symm_apply v⟩
    intro j
    cases j with
    | inl i => simpa [tupleMap,Input.pools,reindex] using hv (Sum.inl (e i))
    | inr i => exact hv (Sum.inr i)

lemma profile_map (e : α≃β) (s : Input α) (R seed : Ideal O) (v : Tuple α) :
    (original (reindex e s) R seed).profile (tupleMap e v) =
      (original s R seed).profile v := by
  simp only [OriginalData.profile,original,reindex,profileCoefficient,tupleMap_product,
    tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Equiv.refl_symm,
    Equiv.refl_apply,Sum.map_inl,Sum.map_inr]
  congr 3
  exact e.symm.prod_comp (fun i=> s.ν i (v (Sum.inl i))*
    s.W i ((Ideal.absNorm (v (Sum.inl i)):ℝ)/s.P i))

lemma columns_map (e : α≃β) (s : Input α) (R seed : Ideal O) :
    (original (reindex e s) R seed).columns=(original s R seed).columns := by
  unfold OriginalData.columns
  change finiteColumns (Fintype.piFinset (reindex e s).pools)=finiteColumns (Fintype.piFinset s.pools)
  rw [←pools_map,finiteColumns,Finset.image_image]
  congr 1
  funext v
  exact tupleMap_product e v

lemma coefficient_map (e : α≃β) (s : Input α) (R seed : Ideal O) :
    (original (reindex e s) R seed).beta=(original s R seed).beta := by
  funext I
  unfold OriginalData.beta finiteColumnCoefficient
  change (∑v∈(Fintype.piFinset (reindex e s).pools).filter (fun v=> finiteTupleProduct v=I),
    (original (reindex e s) R seed).profile v)=_
  rw [←pools_map,Finset.filter_image]
  rw [Finset.sum_image (fun v _ w _ h => (tupleMap e).injective h)]
  simp only [tupleMap_product,profile_map]
  rfl

lemma volume_map (e : α≃β) (s : Input α) : volume (reindex e s)=volume s := by
  simp only [CenteredMomentAmplificationChildInput.volume,reindex,e.symm.prod_comp]

lemma controls_map (e : α≃β) (s : Input α) :
    (∏i,(reindex e s).M i)=(∏i,s.M i) ∧
    (∏i,(reindex e s).lo i)=(∏i,s.lo i) ∧
    (∏i,(reindex e s).hi i)=(∏i,s.hi i) := by
  simp only [reindex,e.symm.prod_comp,and_self]

lemma sourceRadius_map (e : α≃β) (s : Input α) :
    CenteredMomentOriginalCommonHarmonic.sourceRadius (reindex e s)=
      CenteredMomentOriginalCommonHarmonic.sourceRadius s := by
  simp only [CenteredMomentOriginalCommonHarmonic.sourceRadius,reindex,e.symm.prod_comp]

theorem normalizedGaussSource_map (e : α≃β) (s : Input α) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource (reindex e s) R seed W K=normalizedGaussSource s R seed W K := by
  unfold normalizedGaussSource
  rw [columns_map,coefficient_map,volume_map]
  rfl

def imageInput (e : α↪β) (T : Finset α) (s : Input T) : Input (T.map e) :=
  reindex (CenteredMomentEnergyReindex.subsetMapEquiv e T) s

omit [Fintype α] [Fintype β] in
lemma imageInput_lo (e : α↪β) (T : Finset α) (s : Input T) (i : T) :
    (imageInput e T s).lo ((CenteredMomentEnergyReindex.subsetMapEquiv e T) i)=s.lo i := by
  simp only [imageInput,reindex,Equiv.symm_apply_apply]

omit [Fintype α] [Fintype β] in
lemma imageInput_hi (e : α↪β) (T : Finset α) (s : Input T) (i : T) :
    (imageInput e T s).hi ((CenteredMomentEnergyReindex.subsetMapEquiv e T) i)=s.hi i := by
  simp only [imageInput,reindex,Equiv.symm_apply_apply]

omit [Fintype α] [Fintype β] in
lemma imageInput_normalized (e : α↪β) (T : Finset α) (s : Input T)
    (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource (imageInput e T s) R seed W K=normalizedGaussSource s R seed W K :=
  normalizedGaussSource_map (CenteredMomentEnergyReindex.subsetMapEquiv e T) s R seed W K

def allocatedImage (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Input ((liveIndices B.val).map e) :=
  imageInput e (liveIndices B.val) (child s C R B τ t)

omit [Fintype β] in
lemma allocatedImage_ranges (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (lo hi : β→ℝ) (hlo : ∀i,s.lo i=lo (e i)) (hhi : ∀i,s.hi i=hi (e i)) :
    (∀j,(allocatedImage e s C R B τ t).lo j=lo j.val) ∧
    (∀j,(allocatedImage e s C R B τ t).hi j=hi j.val) := by
  constructor
  · intro j
    obtain ⟨i,rfl⟩:=(CenteredMomentEnergyReindex.subsetMapEquiv e (liveIndices B.val)).surjective j
    rw [allocatedImage,imageInput_lo]
    exact hlo i.val
  · intro j
    obtain ⟨i,rfl⟩:=(CenteredMomentEnergyReindex.subsetMapEquiv e (liveIndices B.val)).surjective j
    rw [allocatedImage,imageInput_hi]
    exact hhi i.val

omit [Fintype β] in
theorem allocatedImage_normalized (e : α↪β) (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource (allocatedImage e s C R B τ t) (R*C) seed W K =
      childNormalizedGaussSource s C R seed B τ t W K :=
  imageInput_normalized e (liveIndices B.val) (child s C R B τ t) (R*C) seed W K

end CenteredMomentSourceInputReindex

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
