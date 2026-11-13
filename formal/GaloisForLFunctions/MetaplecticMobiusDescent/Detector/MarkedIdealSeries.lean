/-
Marked ideal series adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.LocalGammaFactors

/-!
# Marked ideal series

Prime ideals, high valuations and the marked ideal high series with its local factors; rational
local factors and the L-function factorization of the marked high source.
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
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open  CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => Eisenstein.O

theorem bareSourceCoefficient_prime_formula (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k j : ℕ) (he : e≤1)
    (hI : primaryIdealGenerator (Ideal.span {p^e})≠0) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (p^j) =
    (-1:ℂ)^e * ((localGamma p hp.ne_zero hg 1)⁻¹)^e * (targetMonoid η p)^e *
      (star (CompletedGauss.angularFactor p)^3 * (targetMonoid η p)^3 *
        star (localGamma p hp.ne_zero hg 3))^l *
      (complexSexticChar (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j := by
  have ho := odd_of_supported p hs
  have hself := reciprocitySign_self_eq_sextic_neg_one p hp.ne_zero hg hchar ho
  have hstar : star (complexSexticChar (Ideal.span {p}) hg (-1))=
      complexSexticChar (Ideal.span {p}) hg (-1) := by
    rw [←hself,reciprocitySign_star]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_prime_power_small p hp hg hprimary e he hI,
    bareCongruenceCoefficient_all_prime_powers p hp hg,
    angularFactor_pow,map_pow,
    G_completed_prime_power p ho e l he,
    G_cube_eq_localGamma p hp.ne_zero hg hchar ho,
    reciprocitySign_pow_left p _ (odd_pow p ho k),reciprocitySign_pow_right p p ho,
    hself]
  change _ = _
  simp only [star_mul,star_pow,hstar]
  change (targetMonoid η p)^(e+3*l) * star (CompletedGauss.angularFactor p)^(e+3*l) *
    (localGamma p hp.ne_zero hg 2^e *
      ((complexSexticChar (Ideal.span {p}) hg (-1))^(e*l+l.choose 2) *
        (star (localGamma p hp.ne_zero hg 3)^l * star (G p)^e)) *
      (((complexSexticChar (Ideal.span {p}) hg (-1))^k)^(e+3*l) *
        sourceScalar p hp hg (e+3*l) k j)) = _
  calc
    _ = (localGamma p hp.ne_zero hg 2 * star (CompletedGauss.angularFactor p) * star (G p))^e *
      (targetMonoid η p)^e *
      (star (CompletedGauss.angularFactor p)^3*(targetMonoid η p)^3*
        star (localGamma p hp.ne_zero hg 3))^l *
      (complexSexticChar (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j := by
        simp only [pow_add,pow_mul,mul_pow]
        ring
    _ = _ := by
      rw [corrected_prime_cubic_signal p hp.ne_zero hg hchar hprimary hs]
      rw [neg_eq_neg_one_mul ((localGamma p hp.ne_zero hg 1)⁻¹),mul_pow]

theorem bareSourceCoefficient_weighted_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1)
    (hI : primaryIdealGenerator (Ideal.span {p^e})≠0) (x w z : ℂ) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (p^(6*m)) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  rw [bareSourceCoefficient_prime_formula η p hp hg hchar hprimary hs e l k (6*m) he hI]
  unfold sourcePrincipalTerm sourceWeightedScalar
  simp only [zpow_neg,zpow_natCast,←inv_pow,Complex.ofReal_natCast]
  have hpdiag := source_signed_phase
    (actualACube η p*star (localGamma p hp.ne_zero hg 3))
    (complexSexticChar (Ideal.span {p}) hg (-1)) (complexSexticChar_neg_one_sq _ hg) e l k
  simp only [localCubePhase] at hpdiag
  have ha : actualACube η p=
      star (CompletedGauss.angularFactor p)^3*(targetMonoid η p)^3 := rfl
  rw [ha] at hpdiag ⊢
  calc
    _ = ((-1:ℂ)^e*((localGamma p hp.ne_zero hg 1)⁻¹)^e*(targetMonoid η p)^e) *
      ((star (CompletedGauss.angularFactor p)^3*(targetMonoid η p)^3*
        star (localGamma p hp.ne_zero hg 3))^l *
        (complexSexticChar (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2)) *
      sourceScalar p hp hg (e+3*l) k (6*m) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) := by ring
    _ = _ := by rw [←hpdiag]; ring

end ProbePhysical
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
open CompletedGauss  GaussianShiftedPartition CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation 
local notation "O" => Eisenstein.O

lemma finite_fourier_invariant_unit {R : Type*} [CommRing R] [Fintype R]
    (F : R→ℂ) (ψ : AddChar R ℂ) (u : Rˣ) (hF : ∀ x,F ((u:R)*x)=F x) (H : R) :
    (∑ x,F x*ψ (((u:R)*H)*x)) = ∑ x,F x*ψ (H*x) := by
  symm
  rw [← Equiv.sum_comp u.mulLeft (fun x=> F x*ψ (H*x))]
  simp only [Units.mulLeft_apply,hF]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  congr 1
  ring

lemma supported_sixth_value (A v : O) (hA : Supported (Ideal.span {A}))
    (hcop : IsCoprime A v) : idealRowHom (v^6) (Ideal.span {A})=1 := by
  rw [idealRowHom_sixth_mask _ _ ((supported_iff_native _).mp hA), if_pos ((Ideal.isCoprime_span_singleton_iff A v).mpr hcop)]

theorem barePhysicalFourier_sixth_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A*s)) :
    barePhysicalFourier A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) (v^6*H) =
      barePhysicalFourier A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) H := by
  have hAs := mul_ne_zero (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs)
  let := finiteEisensteinQuotientOfNonzero hAs
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let u := residueUnit (A*s) (v^6) hcop.pow_left.symm
  have hF (x : Residue (A*s)) :
      movingQuotient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) ((u:Residue (A*s))*x) =
        movingQuotient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) x := by
    rw [show (u:Residue (A*s))=Ideal.Quotient.mk _ (v^6) by rfl,
      movingQuotient_unit_scale A s hs (v^6) hcop.of_mul_right_right.pow_left,
      supported_sixth_value A v hA hcop.of_mul_right_left.symm,
      supported_sixth_value s v hs hcop.of_mul_right_right.symm,inv_one,one_mul,one_mul]
  have he := finite_fourier_invariant_unit (movingQuotient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs))
    (primitiveTrace (A*s) hAs) u hF (Ideal.Quotient.mk _ H)
  unfold barePhysicalFourier elementFourier
  simp only [tsum_fintype]
  change (∑ x,movingQuotient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) x *
    primitiveTrace (A*s) hAs (Ideal.Quotient.mk _ (v^6*H)*x)) =
    ∑ x,movingQuotient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) x *
      primitiveTrace (A*s) hAs (Ideal.Quotient.mk _ H*x)
  simpa only [u,residueUnit_coe,map_mul] using he

theorem bareCongruenceCoefficient_sixth_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A*s)) :
    bareCongruenceCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (v^6*H) =
      bareCongruenceCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H := by
  have he := barePhysicalFourier_sixth_frequency A s hA hs v H hcop
  simp only [barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs))
  exact mul_left_cancel₀ hn he

theorem bareSourceCoefficient_sixth_frequency (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryIdealGenerator I≠0) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A*s)) :
    bareSourceCoefficient η I hI A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (v^6*H) =
      bareSourceCoefficient η I hI A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H := by
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [bareCongruenceCoefficient_sixth_frequency A s hA hs v H hcop]

theorem bareSourceCoefficient_product_frequency (η : HeckeFamily.Character) (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryIdealGenerator I})) (hd : Supported (Ideal.span {primaryIdealGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : lambda^2∣primaryIdealGenerator I-1) (hpd : lambda^2∣primaryIdealGenerator J-1)
    (hpn : lambda^2∣n-1) (hpm : lambda^2∣m-1)
    (hps : lambda^2∣s-1) (hpr : lambda^2∣r-1)
    (hcop : IsCoprime ((primaryIdealGenerator I*n^3)*s) ((primaryIdealGenerator J*m^3)*r)) (a b : O)
    (hba : IsCoprime b ((primaryIdealGenerator I*n^3)*s))
    (hab : IsCoprime a ((primaryIdealGenerator J*m^3)*r)) :
    let A := primaryIdealGenerator I*n^3
    let B := primaryIdealGenerator J*m^3
    let hA := CenteredMomentSupportedCorrelation.supported_element_ne_zero A (supported_completed _ _ hc hn)
    let hB := CenteredMomentSupportedCorrelation.supported_element_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) ((a*b)^6) =
      bareSourceCoefficient η I hI.2 A s hA (a^6) * bareSourceCoefficient η J hJ.2 B r hB (b^6) := by
  have he := bareSourceCoefficient_product η I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop ((a*b)^6)
  dsimp only at he ⊢
  have hi := bareSourceCoefficient_sixth_frequency η I hI.2 (primaryIdealGenerator I*n^3) s
    (supported_completed _ _ hc hn) hs b (a^6) hba
  have hj := bareSourceCoefficient_sixth_frequency η J hJ.2 (primaryIdealGenerator J*m^3) r
    (supported_completed _ _ hd hm) hr a (b^6) hab
  rw [show b^6*a^6=(a*b)^6 by ring] at hi
  rw [show a^6*b^6=(a*b)^6 by ring] at hj
  rw [hi,hj] at he
  exact he

end ProbePhysical
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open  CubicEisenstein
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def highSupport (I J K L : Id) : Prop :=
  Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L

lemma highSupport_mul (I J K L I' J' K' L' : Id) (hcop : IsCoprime I I') :
    highSupport (I*I') (J*J') (K*K') (L*L') ↔
      highSupport I J K L ∧ highSupport I' J' K' L' := by
  simp only [highSupport, squarefree_mul_iff, supported_mul_iff]
  have hc := hcop.isRelPrime
  tauto

lemma primaryIdealGenerator_coprime (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hcop : IsCoprime I J) : IsCoprime (primaryIdealGenerator I) (primaryIdealGenerator J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rwa [CenteredMomentSourceRow.primary_span_supported I hI,
    CenteredMomentSourceRow.primary_span_supported J hJ]

lemma completed_block_dvd_cube (I J K L : Id) : I*J^3*K ∣ (I*J*K*L)^3 := by
  refine ⟨I ^ 2*K^2*L^3,?_⟩
  ring

lemma first_block_dvd (I J K L : Id) : I ∣ I*J*K*L := by
  refine ⟨J*K*L,?_⟩
  ring

lemma last_block_dvd (I J K L : Id) : L ∣ I*J*K*L := by
  refine ⟨I*J*K,?_⟩
  ring

theorem bareIdealHighCoefficient_mul (η : HeckeFamily.Character)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighCoefficient η 1 (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighCoefficient η 1 I J K L * bareIdealHighCoefficient η 1 I' J' K' L' := by
  have hII := hcop.mono (first_block_dvd I J K L) (first_block_dvd I' J' K' L')
  by_cases h : highSupport I J K L ∧ highSupport I' J' K' L'
  · have hprod := (highSupport_mul I J K L I' J' K' L' hII).mpr h
    rcases h with ⟨h,h'⟩
    have hsA := (supported_mul_iff (I*J^3) K).mpr
      ⟨(supported_mul_iff I (J^3)).mpr ⟨h.2.1,supported_pow h.2.2.1 3⟩,h.2.2.2.1⟩
    have hsB := (supported_mul_iff (I'*J'^3) K').mpr
      ⟨(supported_mul_iff I' (J'^3)).mpr ⟨h'.2.1,supported_pow h'.2.2.1 3⟩,h'.2.2.2.1⟩
    have hc3 : IsCoprime ((I*J*K*L)^3) ((I'*J'*K'*L')^3) := hcop.pow_left.pow_right
    have hab := primaryIdealGenerator_coprime _ _ hsA hsB
      (hc3.mono (completed_block_dvd_cube I J K L) (completed_block_dvd_cube I' J' K' L'))
    have hba := primaryIdealGenerator_coprime _ _ h'.2.2.2.2 hsA
      (hcop.symm.pow_right.mono (last_block_dvd I' J' K' L') (completed_block_dvd_cube I J K L))
    have hab' := primaryIdealGenerator_coprime _ _ h.2.2.2.2 hsB
      (hcop.pow_right.mono (last_block_dvd I J K L) (completed_block_dvd_cube I' J' K' L'))
    simp only [primaryIdealGenerator_mul,primaryIdealGenerator_pow] at hab hba hab'
    have he := bareSourceCoefficient_product_frequency η I I'
      ⟨h.1,supported_primaryIdealGenerator_ne_zero I h.2.1⟩
      ⟨h'.1,supported_primaryIdealGenerator_ne_zero I' h'.2.1⟩
      ⟨hprod.1,supported_primaryIdealGenerator_ne_zero (I*I') hprod.2.1⟩ hII
      (primaryIdealGenerator J) (primaryIdealGenerator J') (primaryIdealGenerator K) (primaryIdealGenerator K')
      ((supported_span_primaryIdealGenerator_iff I).mpr h.2.1)
      ((supported_span_primaryIdealGenerator_iff I').mpr h'.2.1)
      ((supported_span_primaryIdealGenerator_iff J).mpr h.2.2.1)
      ((supported_span_primaryIdealGenerator_iff J').mpr h'.2.2.1)
      ((supported_span_primaryIdealGenerator_iff K).mpr h.2.2.2.1)
      ((supported_span_primaryIdealGenerator_iff K').mpr h'.2.2.2.1)
      (primaryIdealGenerator_spec I (supported_primaryIdealGenerator_ne_zero I h.2.1)).2
      (primaryIdealGenerator_spec I' (supported_primaryIdealGenerator_ne_zero I' h'.2.1)).2
      (primaryIdealGenerator_spec J (supported_primaryIdealGenerator_ne_zero J h.2.2.1)).2
      (primaryIdealGenerator_spec J' (supported_primaryIdealGenerator_ne_zero J' h'.2.2.1)).2
      (primaryIdealGenerator_spec K (supported_primaryIdealGenerator_ne_zero K h.2.2.2.1)).2
      (primaryIdealGenerator_spec K' (supported_primaryIdealGenerator_ne_zero K' h'.2.2.2.1)).2
      hab (primaryIdealGenerator L) (primaryIdealGenerator L') hba hab'
    unfold highSupport at hprod h h'
    unfold bareIdealHighCoefficient
    rw [dif_pos hprod,dif_pos h,dif_pos h']
    simp only [primaryIdealGenerator_mul,one_mul]
    dsimp only at he
    convert he using 1 <;> first | rfl | ring
  · have hprod := mt (highSupport_mul I J K L I' J' K' L' hII).mp h
    unfold highSupport at hprod
    unfold bareIdealHighCoefficient
    rw [dif_neg hprod]
    by_cases hi : highSupport I J K L
    · have hj : ¬highSupport I' J' K' L' := fun hj=> h ⟨hi,hj⟩
      unfold highSupport at hj
      rw [dif_neg hj,mul_zero]
    · unfold highSupport at hi
      rw [dif_neg hi,zero_mul]

lemma fullIdealWeight_mul (s : ℂ) (I J : Id) :
    fullIdealWeight s (I*J)=fullIdealWeight s I*fullIdealWeight s J :=
  (IdealEuler.normWeight s).map_mul I J

theorem bareIdealHighSummand_mul (η : HeckeFamily.Character) (x w z : ℂ)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighSummand η 1 x w z (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighSummand η 1 x w z I J K L * bareIdealHighSummand η 1 x w z I' J' K' L' := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_mul η I J K L I' J' K' L' hcop,
    fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul]
  ring

end ProbePhysical
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CubicEisenstein ProbePhase  
local notation "O" => Eisenstein.O

lemma angularFactor_one : CompletedGauss.angularFactor (1:O)=1 := by
  simp only [CompletedGauss.angularFactor,map_one,norm_one,Complex.ofReal_one,div_one]

@[simp] theorem bareIdealHighCoefficient_one (η : HeckeFamily.Character) :
    bareIdealHighCoefficient η 1 1 1 1 1=1 := by
  have hs := CenteredMomentAddedZero.supported_one_ideal
  have hg : Squarefree (1:Ideal O) ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 :=
    ⟨squarefree_one,hs,hs,hs,hs⟩
  unfold bareIdealHighCoefficient
  rw [dif_pos hg]
  simp only [primaryIdealGenerator_one,one_pow,one_mul]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_one,ProbePhase.G_one,angularFactor_one]
  have ho := odd_of_supported (1:O) (by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top];exact hs)
  rw [reciprocitySign_one_left (1:O) ho,
    bareCongruenceCoefficient_inner_one 1 one_ne_zero,outerQuotient_mk]
  simp only [map_one,star_one,one_mul,Ideal.span_singleton_one,←Ideal.one_eq_top]

@[simp] theorem bareIdealHighSummand_one (η : HeckeFamily.Character) (x w z : ℂ) :
    bareIdealHighSummand η 1 x w z 1 1 1 1=1 := by
  have hw (t : ℂ) : fullIdealWeight t (1:Ideal O)=1 := (IdealEuler.normWeight t).map_one
  simp only [bareIdealHighSummand,bareIdealHighCoefficient_one,hw,one_mul]

end ProbePhysical
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein UniqueFactorizationMonoid
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

abbrev PrimeIdeal := {P : Id // Prime P}

def primeValuations (I : Id) : PrimeIdeal →₀ ℕ :=
  (factorization I).subtypeDomain Prime

def idealFromValuations (v : PrimeIdeal →₀ ℕ) : Id :=
  v.prod (fun P n=> P.val^n)

lemma idealFromValuations_ne_zero (v : PrimeIdeal →₀ ℕ) : idealFromValuations v≠0 := by
  unfold idealFromValuations Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr (fun P hP=> pow_ne_zero _ P.property.ne_zero)

@[simp] lemma primeValuations_apply (I : Id) (P : PrimeIdeal) :
    primeValuations I P=(normalizedFactors I).count P.val := by
  simp only [primeValuations,Finsupp.subtypeDomain_apply,factorization_eq_count]

@[simp] lemma primeValuations_one : primeValuations 1=0 := by
  simp only [primeValuations,factorization_one,Finsupp.subtypeDomain_zero]

lemma primeValuations_mul (I J : Id) (hI : I≠0) (hJ : J≠0) :
    primeValuations (I*J)=primeValuations I+primeValuations J := by
  simp only [primeValuations,factorization_mul hI hJ,Finsupp.subtypeDomain_add]

@[simp] lemma primeValuations_prime (P : PrimeIdeal) :
    primeValuations P.val=Finsupp.single P 1 := by
  ext Q
  simp only [primeValuations_apply,normalizedFactors_irreducible P.property.irreducible,
    normalize_eq,Multiset.count_singleton,Finsupp.single_apply]
  by_cases h : Q=P
  · subst Q
    simp
  · have hv : Q.val≠P.val := fun hh=> h (Subtype.ext hh)
    simp [Ne.symm h,hv]

lemma primeValuations_pow (I : Id) (n : ℕ) :
    primeValuations (I ^ n)=n • primeValuations I := by
  ext P
  simp only [primeValuations_apply,normalizedFactors_pow,Multiset.count_nsmul,
    Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]

@[simp] lemma idealFromValuations_zero : idealFromValuations 0=1 := by
  simp [idealFromValuations]

lemma idealFromValuations_add (v w : PrimeIdeal →₀ ℕ) :
    idealFromValuations (v+w)=idealFromValuations v*idealFromValuations w := by
  exact Finsupp.prod_add_index' (fun _=> pow_zero _) (fun _ _ _=> pow_add _ _ _)

@[simp] lemma idealFromValuations_single (P : PrimeIdeal) (n : ℕ) :
    idealFromValuations (Finsupp.single P n)=P.val^n := by
  simp [idealFromValuations]

@[simp] theorem primeValuations_idealFromValuations (v : PrimeIdeal →₀ ℕ) :
    primeValuations (idealFromValuations v)=v := by
  induction v using Finsupp.induction with
  | zero => simp only [idealFromValuations_zero,primeValuations_one]
  | @single_add P n v hP hn ih =>
    rw [idealFromValuations_add,primeValuations_mul _ _
      (idealFromValuations_ne_zero _) (idealFromValuations_ne_zero _),ih]
    simp only [idealFromValuations_single,primeValuations_pow,primeValuations_prime,
      Finsupp.smul_single,smul_eq_mul,mul_one]

@[simp] theorem idealFromValuations_primeValuations (I : Id) (hI : I≠0) :
    idealFromValuations (primeValuations I)=I := by
  have hs : ∀ P∈(factorization I).support,Prime P := by
    intro P hP
    exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp (by simpa using hP))
  unfold idealFromValuations primeValuations
  rw [Finsupp.prod_subtypeDomain_index hs]
  simp only [Finsupp.prod,support_factorization,factorization_eq_count]
  rw [← Finset.prod_multiset_count_of_subset _ _ (Finset.Subset.refl _)]
  exact Ideal.prod_normalizedFactors_eq_self hI

def nonzeroIdealValuationEquiv : {I : Id // I≠0} ≃ (PrimeIdeal →₀ ℕ) where
  toFun I := primeValuations I.val
  invFun v := ⟨idealFromValuations v,idealFromValuations_ne_zero v⟩
  left_inv I := Subtype.ext (idealFromValuations_primeValuations I.val I.property)
  right_inv := primeValuations_idealFromValuations

lemma prime_coprime_idealFromValuations (P : PrimeIdeal) (v : PrimeIdeal →₀ ℕ)
    (hP : v P=0) : IsCoprime P.val (idealFromValuations v) := by
  apply IsCoprime.prod_right
  intro Q hQ
  apply IsCoprime.pow_right
  apply primeIdeal_coprime
  intro hh
  subst Q
  exact Finsupp.mem_support_iff.mp hQ hP

def finsuppPairEquiv {α β γ : Type*} [Zero β] [Zero γ] :
    ((α→₀β)×(α→₀γ)) ≃ (α→₀(β×γ)) where
  toFun v := Finsupp.zipWith Prod.mk rfl v.1 v.2
  invFun v := (v.mapRange Prod.fst rfl,v.mapRange Prod.snd rfl)
  left_inv v := by
    apply Prod.ext <;> ext a <;> rfl
  right_inv v := by
    apply Finsupp.ext
    intro a
    exact Prod.eta (v a)

abbrev HighValuation := (ℕ×ℕ)×(ℕ×ℕ)
abbrev NonzeroIdeal := {I : Id // I≠0}

def highValuationEquiv : ((NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal)) ≃
    (PrimeIdeal→₀HighValuation) :=
  (Equiv.prodCongr
    (Equiv.prodCongr nonzeroIdealValuationEquiv nonzeroIdealValuationEquiv)
    (Equiv.prodCongr nonzeroIdealValuationEquiv nonzeroIdealValuationEquiv)).trans
      ((Equiv.prodCongr finsuppPairEquiv finsuppPairEquiv).trans finsuppPairEquiv)

@[simp] lemma highValuationEquiv_apply
    (a : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal)) (P : PrimeIdeal) :
    highValuationEquiv a P =
      ((primeValuations a.1.1.val P,primeValuations a.1.2.val P),
        (primeValuations a.2.1.val P,primeValuations a.2.2.val P)) := rfl

end ProbePhysical
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace ProbeEulerFinsupp

lemma finitePi_fin {β : Type*} (n : ℕ) (f : Fin n→β→ℂ)
    (hf : ∀ i,Summable (fun b=>‖f i b‖)) :
    Summable (fun v : Fin n→β => ‖∏ i,f i (v i)‖) ∧
      (∑' v : Fin n→β,∏ i,f i (v i))=∏ i,∑' b,f i b := by
  induction n with
  | zero =>
    constructor
    · exact (hasSum_fintype _).summable
    · simp
  | succ n ih =>
    have ht := ih (fun i=> f i.succ) (fun i=> hf i.succ)
    let e := Fin.consEquiv (fun _ : Fin (n+1)=>β)
    have he (v : β×(Fin n→β)) :
        (∏ i,f i (e v i))=f 0 v.1*(∏ i,f i.succ (v.2 i)) := by
      rw [Fin.prod_univ_succ]
      rfl
    constructor
    · rw [←e.summable_iff]
      simp only [Function.comp_def,he]
      have hm : Summable (fun v : β×(Fin n→β)=>‖f 0 v.1‖ * ‖∏ i : Fin n,f i.succ (v.2 i)‖) :=
        (hf 0).mul_of_nonneg ht.1 (fun _=> norm_nonneg _) (fun _=> norm_nonneg _)
      simpa only [norm_mul] using hm
    · rw [←e.tsum_eq (fun v=>∏ i,f i (v i))]
      simp only [he]
      rw [←tsum_mul_tsum_of_summable_norm (f:=f 0)
        (g:=fun v : Fin n→β=>∏ i : Fin n,f i.succ (v i)) (hf 0) ht.1,ht.2,Fin.prod_univ_succ]

lemma finitePi {α β : Type*} [Fintype α] (f : α→β→ℂ)
    (hf : ∀ i,Summable (fun b=>‖f i b‖)) :
    Summable (fun v : α→β => ‖∏ i,f i (v i)‖) ∧
      (∑' v : α→β,∏ i,f i (v i))=∏ i,∑' b,f i b := by
  let e := Fintype.equivFin α
  let d := Equiv.arrowCongr e.symm (Equiv.refl β)
  have h := finitePi_fin (Fintype.card α) (fun i=> f (e.symm i)) (fun i=> hf (e.symm i))
  have hd (v : Fin (Fintype.card α)→β) :
      (∏ i,f i (d v i))=∏ j,f (e.symm j) (v j) := by
    apply Fintype.prod_equiv e
    intro i
    simp only [d,Equiv.arrowCongr_apply,Equiv.symm_symm,Equiv.refl_apply,e.symm_apply_apply,Function.comp_apply]
  constructor
  · rw [←d.summable_iff]
    simpa only [Function.comp_def,hd] using h.1
  · rw [←d.tsum_eq (fun v=>∏ i,f i (v i))]
    simp only [hd]
    rw [h.2]
    exact e.symm.prod_comp (fun i=>∑' b,f i b)

variable {α β : Type*} [AddCommMonoid β]

lemma finiteEuler (f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hf : ∀a,Summable (fun b=>‖f a b‖)) (S : Finset α) :
    (∑' v : {v : α→₀β // (v.support:Set α)⊆S},v.val.prod f)=
      ∏ a∈S,∑' b,f a b := by
  let e : {v : α→₀β // (v.support:Set α)⊆S} ≃ (S→β) :=
    (Finsupp.restrictSupportEquiv (S:Set α) β).trans Finsupp.equivFunOnFinite
  have he (v : {v : α→₀β // (v.support:Set α)⊆S}) :
      v.val.prod f=∏ a:S,f a.val (e v a) := by
    rw [←Finsupp.prod_subtypeDomain_index (p:=fun a=> a∈S) (fun a ha=> v.property ha)]
    exact Finsupp.prod_fintype _ _ (fun a=> h0 a.val)
  simp_rw [he]
  rw [e.tsum_eq (fun v : S→β=>∏ a:S,f a.val (v a))]
  rw [(finitePi (fun a:S=> f a.val) (fun a=> hf a.val)).2]
  exact Finset.prod_coe_sort S (fun a=>∑' b,f a b)

theorem hasProd_of_summable (f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hs : Summable (fun v : α→₀β=>‖v.prod f‖)) :
    HasProd (fun a=>∑' b,f a b) (∑' v : α→₀β,v.prod f) := by
  have hf (a : α) : Summable (fun b=>‖f a b‖) := by
    have hh := hs.comp_injective (Finsupp.single_injective a)
    simpa only [Function.comp_def,Finsupp.prod_single_index (h0 a)] using hh
  have ht : Tendsto (fun S : Finset α=>∑' v : α→₀β,
      if v.support⊆S then v.prod f else 0) atTop (𝓝 (∑' v : α→₀β,v.prod f)) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · intro v
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop v.support] with S hS
      simp only [if_pos hS]
    · apply Filter.Eventually.of_forall
      intro S v
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (v.prod f)
  have he (S : Finset α) : (∑' v : α→₀β,if v.support⊆S then v.prod f else 0)=
      ∏a∈S,∑' b,f a b := by
    rw [←finiteEuler f h0 hf S]
    trans ∑' v : α→₀β, {v : α→₀β | (v.support:Set α)⊆S}.indicator (fun v=> v.prod f) v
    · apply tsum_congr
      intro v
      simp only [Set.indicator,Set.mem_setOf_eq,Finset.coe_subset]
    · exact (tsum_subtype {v : α→₀β | (v.support:Set α)⊆S} (fun v=> v.prod f)).symm
  change Tendsto (fun S : Finset α=>∏a∈S,∑' b,f a b) atTop _
  simpa only [he] using ht

end ProbeEulerFinsupp
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

abbrev HighIdeal := (Id×Id)×(Id×Id)

def highIdeals (v : PrimeIdeal→₀HighValuation) : HighIdeal :=
  ((idealFromValuations (v.mapRange (fun b=> b.1.1) rfl),
    idealFromValuations (v.mapRange (fun b=> b.1.2) rfl)),
   (idealFromValuations (v.mapRange (fun b=> b.2.1) rfl),
    idealFromValuations (v.mapRange (fun b=> b.2.2) rfl)))

lemma highIdeals_eq_equiv (v : PrimeIdeal→₀HighValuation) :
    highIdeals v =
      (((highValuationEquiv.symm v).1.1.val,(highValuationEquiv.symm v).1.2.val),
       ((highValuationEquiv.symm v).2.1.val,(highValuationEquiv.symm v).2.2.val)) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    apply congrArg idealFromValuations
    ext P
    rfl

lemma highIdeals_injective : Function.Injective highIdeals := by
  intro v w h
  apply highValuationEquiv.symm.injective
  rw [highIdeals_eq_equiv,highIdeals_eq_equiv] at h
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun b : HighIdeal=> b.1.1) h)
    · exact Subtype.ext (congrArg (fun b : HighIdeal=> b.1.2) h)
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun b : HighIdeal=> b.2.1) h)
    · exact Subtype.ext (congrArg (fun b : HighIdeal=> b.2.2) h)

lemma highIdeals_zero : highIdeals 0=1 := by
  simp only [highIdeals,Finsupp.mapRange_zero,idealFromValuations_zero]
  rfl

lemma highIdeals_single (P : PrimeIdeal) (b : HighValuation) :
    highIdeals (Finsupp.single P b)=((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2)) := by
  simp only [highIdeals,Finsupp.mapRange_single,idealFromValuations_single]

lemma highIdeals_add (v w : PrimeIdeal→₀HighValuation) :
    highIdeals (v+w)=highIdeals v*highIdeals w := by
  have hproj (f : HighValuation→ℕ) (hf0 : f 0=0) (hf : ∀a b,f (a+b)=f a+f b) :
      (v+w).mapRange f hf0=v.mapRange f hf0+w.mapRange f hf0 := by
    ext P
    simp only [Finsupp.mapRange_apply,Finsupp.add_apply,hf]
  simp only [highIdeals,hproj (fun b=> b.1.1) rfl (fun _ _=> rfl),
    hproj (fun b=> b.1.2) rfl (fun _ _=> rfl),hproj (fun b=> b.2.1) rfl (fun _ _=> rfl),
    hproj (fun b=> b.2.2) rfl (fun _ _=> rfl),idealFromValuations_add]
  rfl

lemma prime_coprime_highIdeals (P : PrimeIdeal) (v : PrimeIdeal→₀HighValuation)
    (hv : v P=0) : IsCoprime P.val
      ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) := by
  have hc (f : HighValuation→ℕ) (hf0 : f 0=0) :
      IsCoprime P.val (idealFromValuations (v.mapRange f hf0)) := by
    apply prime_coprime_idealFromValuations
    simp only [Finsupp.mapRange_apply,hv,hf0]
  exact ((hc _ rfl).mul_right (hc _ rfl)).mul_right (hc _ rfl) |>.mul_right (hc _ rfl)

def highValuationTerm (η : HeckeFamily.Character) (x w z : ℂ)
    (v : PrimeIdeal→₀HighValuation) : ℂ :=
  bareIdealHighSummand η 1 x w z (highIdeals v).1.1 (highIdeals v).1.2
    (highIdeals v).2.1 (highIdeals v).2.2

def highPrimeTerm (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  bareIdealHighSummand η 1 x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)

lemma highPrimeTerm_zero (η : HeckeFamily.Character) (x w z : ℂ) (P : PrimeIdeal) :
    highPrimeTerm η x w z P 0=1 := by
  simp only [highPrimeTerm,Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_one]

theorem highValuationTerm_eq_prod (η : HeckeFamily.Character) (x w z : ℂ)
    (v : PrimeIdeal→₀HighValuation) :
    highValuationTerm η x w z v=v.prod (highPrimeTerm η x w z) := by
  induction v using Finsupp.induction with
  | zero =>
    simp only [highValuationTerm,highIdeals_zero,Prod.fst_one,Prod.snd_one,
      bareIdealHighSummand_one,Finsupp.prod_zero_index]
  | @single_add P b v hP hb ih =>
    have hv : v P=0 := Finsupp.notMem_support_iff.mp hP
    have hc := prime_coprime_highIdeals P v hv
    have hpow : IsCoprime (P.val^b.1.1*P.val^b.1.2*P.val^b.2.1*P.val^b.2.2)
        ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) :=
      ((hc.pow_left.mul_left hc.pow_left).mul_left hc.pow_left).mul_left hc.pow_left
    have hd : Disjoint (Finsupp.single P b).support v.support := by
      rw [Finsupp.support_single _ hb]
      exact Finset.disjoint_singleton_left.mpr hP
    rw [Finsupp.prod_add_index_of_disjoint hd,Finsupp.prod_single_index (highPrimeTerm_zero η x w z P),←ih]
    unfold highValuationTerm
    rw [highIdeals_add,highIdeals_single]
    exact bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hpow

theorem highValuationTerm_summable_norm (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    Summable (fun v : PrimeIdeal→₀HighValuation=>‖highValuationTerm η x w z v‖) :=
  (bareIdealHighSummand_summable η 1 x w z hx hw hz).norm.comp_injective highIdeals_injective

end ProbePhysical
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open  CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => Eisenstein.O

lemma primaryIdealGenerator_prime_power (p : O) (hp : p≠0) (hprimary : lambda^2∣p-1) (e : ℕ) :
    primaryIdealGenerator ((Ideal.span {p})^e)=p^e := by
  rw [primaryIdealGenerator_pow,primaryIdealGenerator_span p hp hprimary]

lemma prime_power_small_squarefree (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (e : ℕ) (he : e≤1) :
    Squarefree ((Ideal.span {p})^e) := by
  have hP : Prime (Ideal.span {p}:Ideal O) :=
    Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero) inferInstance
  have hcases : e=0 ∨ e=1 := by omega
  rcases hcases with rfl|rfl
  · simpa only [pow_zero] using (squarefree_one : Squarefree (1:Ideal O))
  · simpa only [pow_one] using hP.squarefree

theorem bareIdealHighCoefficient_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) :
    bareIdealHighCoefficient η 1 ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    bareSourceCoefficient η (Ideal.span {p^e})
      (by rw [← Ideal.span_singleton_pow,primaryIdealGenerator_prime_power p hp.ne_zero hprimary e];
          exact pow_ne_zero _ hp.ne_zero)
      (p^(e+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^(6*m)) := by
  have hguard : Squarefree ((Ideal.span {p})^e) ∧ Supported ((Ideal.span {p})^e) ∧
      Supported ((Ideal.span {p})^l) ∧ Supported ((Ideal.span {p})^k) ∧ Supported ((Ideal.span {p})^m) :=
    ⟨prime_power_small_squarefree p hp e he,supported_pow hs e,supported_pow hs l,supported_pow hs k,supported_pow hs m⟩
  unfold bareIdealHighCoefficient
  rw [dif_pos hguard]
  simp only [primaryIdealGenerator_prime_power p hp.ne_zero hprimary,one_mul]
  have hA : p^e*(p^l)^3=p^(e+3*l) := by rw [←pow_mul,Nat.mul_comm l 3,←pow_add]
  have hH : (p^m)^6=p^(6*m) := by rw [←pow_mul,Nat.mul_comm m 6]
  simp only [hA,hH,Ideal.span_singleton_pow]

lemma fullIdealWeight_power (s : ℂ) (I : Ideal O) (n : ℕ) :
    fullIdealWeight s (I ^ n)=fullIdealWeight s I ^ n := (IdealEuler.normWeight s).map_pow I n

lemma prime_spectral_weights (p : O) (hp : p≠0) (e l k m : ℕ) (x w z : ℂ) :
    fullIdealWeight (x+1/2) ((Ideal.span {p})^e) *
      fullIdealWeight (1+3*x) ((Ideal.span {p})^l) *
      fullIdealWeight w ((Ideal.span {p})^k) * fullIdealWeight (6*z) ((Ideal.span {p})^m) =
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) := by
  have hI : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp
  have hQ : (Ideal.absNorm (Ideal.span {p}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hI
  simp only [fullIdealWeight_power]
  simp only [fullIdealWeight,if_neg hI]
  rw [←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,
    ←Complex.cpow_add _ _ hQ,←Complex.cpow_add _ _ hQ,←Complex.cpow_add _ _ hQ]
  congr 1
  ring

theorem bareIdealHighSummand_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) (x w z : ℂ) :
    bareIdealHighSummand η 1 x w z ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_at_prime η p hp hprimary hs e l k m he]
  have hw := prime_spectral_weights p hp.ne_zero e l k m x w z
  simp only [mul_assoc] at hw ⊢
  rw [hw]
  simpa only [mul_assoc] using
    bareSourceCoefficient_weighted_prime η p hp hg hchar hprimary hs e l k m he _ x w z

def idealHighLocalFactor (η : HeckeFamily.Character) (P : Ideal O) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m,
    bareIdealHighSummand η 1 x w z (P^e.val) (P^l) (P^k) (P^m)

theorem idealHighLocalFactor_eq_source (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (x w z : ℂ) :
    idealHighLocalFactor η (Ideal.span {p}) x w z =
      sourcePrincipalSeries p hp hg (targetMonoid η p) (actualACube η p) x w z := by
  unfold idealHighLocalFactor sourcePrincipalSeries
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact bareIdealHighSummand_at_prime η p hp hg hchar hprimary hs e.val l k m (by omega) x w z

theorem idealHighLocalFactor_euler_identity (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    idealHighLocalFactor η (Ideal.span {p}) x w z =
      (1-coordD Q (targetMonoid η p) 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q ((actualACube η p)^2) (targetMonoid η p) 1 x w z := by
  rw [idealHighLocalFactor_eq_source η p hp hg hchar hprimary hs]
  exact sourcePrincipalSeries_euler_identity p hp hg hchar _ _ x w z hV hR hW hD

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma bareIdealHighSummand_support (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (I J K L : Id) (h : bareIdealHighSummand η u x w z I J K L≠0) :
    highSupport I J K L := by
  by_contra hn
  apply h
  unfold highSupport at hn
  simp only [bareIdealHighSummand,bareIdealHighCoefficient,dif_neg hn,zero_mul]

theorem highValuationTerm_tsum_eq (η : HeckeFamily.Character) (x w z : ℂ) :
    (∑'v : PrimeIdeal→₀HighValuation,highValuationTerm η x w z v)=
      bareIdealHighSeries η 1 x w z := by
  unfold highValuationTerm bareIdealHighSeries
  apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
    bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
  intro a ha
  have hs := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 ha
  let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
    ((⟨a.1.1,hs.2.1.1⟩,⟨a.1.2,hs.2.2.1.1⟩),
      (⟨a.2.1,hs.2.2.2.1.1⟩,⟨a.2.2,hs.2.2.2.2.1⟩))
  refine ⟨highValuationEquiv b,?_⟩
  rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]

theorem bareIdealHighSeries_hasProd (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,highPrimeTerm η x w z P b)
      (bareIdealHighSeries η 1 x w z) := by
  have hs := highValuationTerm_summable_norm η x w z hx hw hz
  simp only [highValuationTerm_eq_prod] at hs
  have he := ProbeEulerFinsupp.hasProd_of_summable (highPrimeTerm η x w z)
    (highPrimeTerm_zero η x w z) hs
  simpa only [←highValuationTerm_eq_prod,highValuationTerm_tsum_eq] using he

theorem bareIdealHighSeries_eq_tprod (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    bareIdealHighSeries η 1 x w z =
      ∏' P : PrimeIdeal,∑' b : HighValuation,highPrimeTerm η x w z P b :=
  (bareIdealHighSeries_hasProd η x w z hx hw hz).tprod_eq.symm

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CanonicalQuadraticSieve CanonicalRowCompletion
open  ProbeEuler ProbePrimePower ProbeRow
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma highPrimeTerm_summable_norm (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) (P : PrimeIdeal) :
    Summable (fun b : HighValuation=>‖highPrimeTerm η x w z P b‖) := by
  have hs := (highValuationTerm_summable_norm η x w z hx hw hz).comp_injective
    (Finsupp.single_injective P)
  simpa only [Function.comp_def,highValuationTerm_eq_prod,
    Finsupp.prod_single_index (highPrimeTerm_zero η x w z P)] using hs

lemma highPrimeTerm_zero_of_two_le (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (e l k m : ℕ) (he : 2≤ e) :
    highPrimeTerm η x w z P ((e,l),(k,m))=0 := by
  by_contra hn
  have hs := bareIdealHighSummand_support η 1 x w z (P.val^e) (P.val^l) (P.val^k) (P.val^m) hn
  have hc := hs.1.eq_zero_or_one_of_pow_of_not_isUnit P.property.not_unit
  omega

theorem highPrimeTerm_tsum_eq_localFactor (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,highPrimeTerm η x w z P b)=
      idealHighLocalFactor η P.val x w z := by
  have hs := (highPrimeTerm_summable_norm η x w z hx hw hz P).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) :
      (∑' b : ℕ×ℕ, highPrimeTerm η x w z P ((e,l),b))=
        ∑' k,∑' m,highPrimeTerm η x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=> by
    have hh : 2≤ e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [highPrimeTerm_zero_of_two_le η x w z P e _ _ _ hh,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

theorem bareIdealHighSeries_hasProd_localFactor (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    HasProd (fun P : PrimeIdeal=> idealHighLocalFactor η P.val x w z)
      (bareIdealHighSeries η 1 x w z) := by
  have h := bareIdealHighSeries_hasProd η x w z hx hw hz
  simpa only [highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz] using h

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open Eisenstein CompletedGauss ProbeCompleted
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def highIdealMask (S : Finset Id) (D I J K L : Id) : ℂ :=
  completedMask S D I J *
    (if ∀ P∈S,¬P∣K then 1 else 0) * (if ∀ P∈S,¬P∣L then 1 else 0)

lemma highIdealMask_norm_le_one (S : Finset Id) (D I J K L : Id) :
    ‖highIdealMask S D I J K L‖≤1 := by
  unfold highIdealMask
  split_ifs <;> simp only [mul_one,mul_zero,norm_zero]
  · exact completedMask_norm_le_one S D I J
  all_goals norm_num

def markedIdealHighSummand (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) : ℂ :=
  highIdealMask S D I J K L * bareIdealHighSummand η u x w z I J K L

lemma markedIdealHighSummand_norm_le (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) :
    ‖markedIdealHighSummand S D η u x w z I J K L‖≤‖bareIdealHighSummand η u x w z I J K L‖ := by
  rw [markedIdealHighSummand,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (highIdealMask_norm_le_one S D I J K L)

theorem markedIdealHighSummand_summable (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    Summable (fun p : (Id×Id)×(Id×Id) =>
      markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _=> norm_nonneg _)
    (fun p=> markedIdealHighSummand_norm_le S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2)
    (bareIdealHighSummand_summable η u x w z hx hw hz).norm

def markedIdealHighSeries (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) : ℂ :=
  ∑' p : (Id×Id)×(Id×Id), markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma highArray_val_prod (F : HighIdeal→ℂ) (h1 : F 1=1)
    (hmul : ∀ a b : HighIdeal,
      IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2) → F (a*b)=F a*F b)
    (v : PrimeIdeal→₀HighValuation) :
    F (highIdeals v)=v.prod (fun P b=> F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) := by
  have hzero (P : PrimeIdeal) : F ((P.val^0,P.val^0),(P.val^0,P.val^0))=1 := by
    simp only [pow_zero]
    change F (1 : HighIdeal)=1
    exact h1
  induction v using Finsupp.induction with
  | zero => simp only [highIdeals_zero,h1,Finsupp.prod_zero_index]
  | @single_add P b v hP hb ih =>
    have hc := prime_coprime_highIdeals P v (Finsupp.notMem_support_iff.mp hP)
    have hpow : IsCoprime (P.val^b.1.1*P.val^b.1.2*P.val^b.2.1*P.val^b.2.2)
        ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) :=
      ((hc.pow_left.mul_left hc.pow_left).mul_left hc.pow_left).mul_left hc.pow_left
    have hd : Disjoint (Finsupp.single P b).support v.support := by
      rw [Finsupp.support_single _ hb]
      exact Finset.disjoint_singleton_left.mpr hP
    rw [Finsupp.prod_add_index_of_disjoint hd,Finsupp.prod_single_index (hzero P),←ih,
      highIdeals_add,highIdeals_single]
    exact hmul _ _ hpow

theorem highArray_hasProd (F : HighIdeal→ℂ) (h1 : F 1=1)
    (hmul : ∀ a b : HighIdeal,
      IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2) → F (a*b)=F a*F b)
    (hzero : ∀ a : HighIdeal,F a≠0 → a.1.1≠0 ∧ a.1.2≠0 ∧ a.2.1≠0 ∧ a.2.2≠0)
    (hs : Summable (fun a=>‖F a‖)) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) (∑' a,F a) := by
  have hv := hs.comp_injective highIdeals_injective
  have hp := highArray_val_prod F h1 hmul
  simp only [Function.comp_def,hp] at hv
  have hlocal (P : PrimeIdeal) : F ((P.val^0,P.val^0),(P.val^0,P.val^0))=1 := by
    simp only [pow_zero]
    change F (1 : HighIdeal)=1
    exact h1
  have he := ProbeEulerFinsupp.hasProd_of_summable
    (fun (P : PrimeIdeal) (b : HighValuation)=> F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) hlocal hv
  have hsum : (∑' v : PrimeIdeal→₀HighValuation,F (highIdeals v))=∑' a,F a := by
    apply highIdeals_injective.tsum_eq
    intro a ha
    have hn := hzero a ha
    let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
      ((⟨a.1.1,hn.1⟩,⟨a.1.2,hn.2.1⟩),(⟨a.2.1,hn.2.2.1⟩,⟨a.2.2,hn.2.2.2⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [←hp,hsum] using he

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein ProbeCompleted CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma outside_mul (S : Finset Id) (hS : ∀P∈S,Prime P) (A B : Id) :
    (∀P∈S,¬P∣A*B) ↔ (∀P∈S,¬P∣A) ∧ (∀P∈S,¬P∣B) := by
  constructor
  · intro h
    constructor
    · intro P hP hd
      exact h P hP ((hS P hP).dvd_mul.mpr (Or.inl hd))
    · intro P hP hd
      exact h P hP ((hS P hP).dvd_mul.mpr (Or.inr hd))
  · rintro ⟨hA,hB⟩ P hP hd
    exact ((hS P hP).dvd_mul.mp hd).elim (hA P hP) (hB P hP)

lemma outside_cube (S : Finset Id) (hS : ∀P∈S,Prime P) (A : Id) :
    (∀P∈S,¬P∣A^3) ↔ ∀P∈S,¬P∣A := by
  constructor
  · intro h P hP hd
    exact h P hP (dvd_trans hd (dvd_pow_self A (by decide : (3:ℕ)≠0)))
  · intro h P hP hd
    exact h P hP ((hS P hP).dvd_of_dvd_pow hd)

def highExclusion (S : Finset Id) (hS : ∀P∈S,Prime P) : Id→*ℂ where
  toFun A := if ∀P∈S,¬P∣A then 1 else 0
  map_one' := by
    rw [if_pos]
    intro P hP hd
    exact (hS P hP).not_unit (isUnit_of_dvd_one hd)
  map_mul' A B := by
    simp only [outside_mul S hS A B]
    split_ifs <;> simp_all

lemma highExclusion_cube (S : Finset Id) (hS : ∀P∈S,Prime P) (A : Id) :
    highExclusion S hS (A^3)=highExclusion S hS A := by
  change (if ∀P∈S,¬P∣A^3 then (1:ℂ) else 0)=_
  simp only [outside_cube S hS]
  rfl

theorem highIdealMask_unmarked (S : Finset Id) (hS : ∀P∈S,Prime P) (I J K L : Id) :
    highIdealMask S 1 I J K L =
      highExclusion S hS I*highExclusion S hS J*highExclusion S hS K*highExclusion S hS L := by
  have he : completedMask S 1 I J=highExclusion S hS (I*J^3) := by
    simp only [completedMask,one_dvd,true_and]
    rfl
  unfold highIdealMask
  rw [he,map_mul,highExclusion_cube]
  rfl

lemma highIdealMask_unmarked_one (S : Finset Id) (hS : ∀P∈S,Prime P) :
    highIdealMask S 1 1 1 1 1=1 := by
  rw [highIdealMask_unmarked S hS]
  simp only [map_one,one_mul]

lemma highIdealMask_unmarked_mul (S : Finset Id) (hS : ∀P∈S,Prime P)
    (a b : HighIdeal) :
    highIdealMask S 1 (a.1.1*b.1.1) (a.1.2*b.1.2) (a.2.1*b.2.1) (a.2.2*b.2.2)=
      highIdealMask S 1 a.1.1 a.1.2 a.2.1 a.2.2 * highIdealMask S 1 b.1.1 b.1.2 b.2.1 b.2.2 := by
  simp only [highIdealMask_unmarked S hS,map_mul]
  ring

theorem excludedIdealHighSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      markedIdealHighSummand S 1 η 1 x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (markedIdealHighSeries S 1 η 1 x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=> markedIdealHighSummand S 1 η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · simp only [Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
      highIdealMask_unmarked_one S hS,bareIdealHighSummand_one,one_mul]
  · intro a b hc
    simp only [Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
      highIdealMask_unmarked_mul S hS a b,
      bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hc]
    ring
  · intro a ha
    have hh : bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hs := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (markedIdealHighSummand_summable S 1 η 1 x w z hx hw hz).norm

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace ProbeEulerFinsupp
variable {α β : Type*} [AddCommMonoid β]

def markedArray (T : Finset α) (m f : α→β→ℂ) (v : α→₀β) : ℂ :=
  (∏a∈T,m a (v a))*v.prod f

def markedLocal (T : Finset α) (m f : α→β→ℂ) (a : α) (b : β) : ℂ :=
  (if a∈T then m a b else 1)*f a b

lemma markedArray_finite (T S : Finset α) (hTS : T⊆S) (m f : α→β→ℂ)
    (h0 : ∀a,f a 0=1) (v : α→₀β) (hv : v.support⊆S) :
    markedArray T m f v=∏a∈S,markedLocal T m f a (v a) := by
  simp only [markedArray,markedLocal,Finset.prod_mul_distrib]
  congr 1
  · symm
    rw [←Finset.prod_subset hTS]
    · apply Finset.prod_congr rfl
      intro a ha
      simp only [if_pos ha]
    · intro a ha hna
      simp only [if_neg hna]
  · exact Finsupp.prod_of_support_subset v hv _ (fun a _=> h0 a)

lemma markedArray_norm_le (T : Finset α) (m f : α→β→ℂ)
    (hm : ∀a∈T,∀b,‖m a b‖≤1) (v : α→₀β) :
    ‖markedArray T m f v‖≤‖v.prod f‖ := by
  rw [markedArray,norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _=> norm_nonneg _) (fun a ha=> hm a ha _)

lemma marked_finiteEuler (T S : Finset α) (hTS : T⊆S) (m f : α→β→ℂ)
    (h0 : ∀a,f a 0=1) (hf : ∀a,Summable (fun b=>‖f a b‖))
    (hm : ∀a∈T,∀b,‖m a b‖≤1) :
    (∑'v : {v : α→₀β // (v.support:Set α)⊆S},markedArray T m f v.val)=
      ∏a∈S,∑'b,markedLocal T m f a b := by
  let e : {v : α→₀β // (v.support:Set α)⊆S} ≃ (S→β) :=
    (Finsupp.restrictSupportEquiv (S:Set α) β).trans Finsupp.equivFunOnFinite
  have he (v : {v : α→₀β // (v.support:Set α)⊆S}) :
      markedArray T m f v.val=∏a:S,markedLocal T m f a.val (e v a) := by
    rw [markedArray_finite T S hTS m f h0 v.val v.property]
    exact (Finset.prod_coe_sort S _).symm
  have hg (a : α) : Summable (fun b=>‖markedLocal T m f a b‖) := by
    apply Summable.of_nonneg_of_le (fun _=> norm_nonneg _) _ (hf a)
    intro b
    rw [markedLocal,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    split_ifs with ha
    · exact hm a ha b
    · simp
  simp_rw [he]
  rw [e.tsum_eq (fun v : S→β=>∏a:S,markedLocal T m f a.val (v a))]
  rw [(finitePi (fun a:S=> markedLocal T m f a.val) (fun a=> hg a.val)).2]
  exact Finset.prod_coe_sort S (fun a=>∑'b,markedLocal T m f a b)

theorem marked_hasProd (T : Finset α) (m f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hs : Summable (fun v : α→₀β=>‖v.prod f‖))
    (hm : ∀a∈T,∀b,‖m a b‖≤1) :
    HasProd (fun a=>∑'b,markedLocal T m f a b) (∑'v : α→₀β,markedArray T m f v) := by
  have hf (a : α) : Summable (fun b=>‖f a b‖) := by
    have hh := hs.comp_injective (Finsupp.single_injective a)
    simpa only [Function.comp_def,Finsupp.prod_single_index (h0 a)] using hh
  have ht : Tendsto (fun S : Finset α=>∑'v : α→₀β,
      if v.support⊆S then markedArray T m f v else 0) atTop
      (𝓝 (∑'v : α→₀β,markedArray T m f v)) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · intro v
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop v.support] with S hS
      simp only [if_pos hS]
    · apply Filter.Eventually.of_forall
      intro S v
      split_ifs
      · exact markedArray_norm_le T m f hm v
      · simpa only [norm_zero] using norm_nonneg (v.prod f)
  change Tendsto (fun S : Finset α=>∏a∈S,∑'b,markedLocal T m f a b) atTop _
  apply ht.congr'
  filter_upwards [eventually_ge_atTop T] with S hTS
  rw [←marked_finiteEuler T S hTS m f h0 hf hm]
  trans ∑'v : α→₀β,{v : α→₀β | (v.support:Set α)⊆S}.indicator (markedArray T m f) v
  · apply tsum_congr
    intro v
    simp only [Set.indicator,Set.mem_setOf_eq,Finset.coe_subset]
  · exact (tsum_subtype {v : α→₀β | (v.support:Set α)⊆S} (markedArray T m f)).symm

end ProbeEulerFinsupp
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein UniqueFactorizationMonoid ProbeCompleted
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma prime_dvd_iff_valuation (P : PrimeIdeal) (I : Id) (hI : I≠0) :
    P.val∣I ↔ primeValuations I P≠0 := by
  rw [primeValuations_apply,Multiset.count_ne_zero,mem_normalizedFactors_iff hI]
  exact ⟨fun h=>⟨P.property,h⟩,fun h=> h.2⟩

lemma prime_dvd_high_completed (P : PrimeIdeal) (v : PrimeIdeal→₀HighValuation) :
    P.val∣(highIdeals v).1.1*(highIdeals v).1.2^3 ↔ (v P).1.1+3*(v P).1.2≠0 := by
  have hI : (highIdeals v).1.1≠0 := idealFromValuations_ne_zero _
  have hJ : (highIdeals v).1.2≠0 := idealFromValuations_ne_zero _
  rw [prime_dvd_iff_valuation P _ (mul_ne_zero hI (pow_ne_zero _ hJ)),
    primeValuations_mul _ _ hI (pow_ne_zero _ hJ),primeValuations_pow]
  simp only [highIdeals,primeValuations_idealFromValuations,Finsupp.add_apply,
    Finsupp.mapRange_apply,Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]

lemma primeProduct_dvd (T : Finset PrimeIdeal) (I : Id) :
    (∏P∈T,P.val)∣I ↔ ∀P∈T,P.val∣I := by
  constructor
  · intro h P hP
    exact (Finset.dvd_prod_of_mem _ hP).trans h
  · intro h
    exact Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ=> primeIdeal_coprime P Q hPQ) h

def completedValuationMark (_P : PrimeIdeal) (b : HighValuation) : ℂ :=
  if b.1.1+3*b.1.2≠0 then 1 else 0

lemma completedValuationMark_norm (_P : PrimeIdeal) (b : HighValuation) :
    ‖completedValuationMark _P b‖≤1 := by
  unfold completedValuationMark
  split_ifs <;> norm_num

lemma completedValuationMark_product (T : Finset PrimeIdeal) (v : PrimeIdeal→₀HighValuation) :
    (∏P∈T,completedValuationMark P (v P))=
      if (∏P∈T,P.val)∣(highIdeals v).1.1*(highIdeals v).1.2^3 then 1 else 0 := by
  rw [primeProduct_dvd]
  simp only [prime_dvd_high_completed]
  by_cases h : ∀P∈T,(v P).1.1+3*(v P).1.2≠0
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro P hP
    exact if_pos (h P hP)
  · rw [if_neg h]
    push Not at h
    obtain ⟨P,hP,hv⟩ := h
    apply Finset.prod_eq_zero hP
    simp only [completedValuationMark,hv,ne_eq,not_true_eq_false,ite_false]

lemma highIdealMask_mark (S : Finset Id) (D I J K L : Id) :
    highIdealMask S D I J K L=(if D∣I*J^3 then 1 else 0)*highIdealMask S 1 I J K L := by
  unfold highIdealMask completedMask
  simp only [one_dvd,true_and]
  split_ifs <;> simp_all

lemma markedIdealHighSummand_mark (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) :
    markedIdealHighSummand S D η u x w z I J K L=
      (if D∣I*J^3 then 1 else 0)*markedIdealHighSummand S 1 η u x w z I J K L := by
  rw [markedIdealHighSummand,highIdealMask_mark,markedIdealHighSummand,mul_assoc]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein ProbeEulerFinsupp
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def excludedHighArray (S : Finset Id) (η : HeckeFamily.Character) (x w z : ℂ) (a : HighIdeal) : ℂ :=
  markedIdealHighSummand S 1 η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2

lemma excludedHighArray_one (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ) : excludedHighArray S η x w z 1=1 := by
  simp only [excludedHighArray,Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
    highIdealMask_unmarked_one S hS,bareIdealHighSummand_one,one_mul]

lemma excludedHighArray_mul (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ) (a b : HighIdeal)
    (hc : IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2)) :
    excludedHighArray S η x w z (a*b)=excludedHighArray S η x w z a*excludedHighArray S η x w z b := by
  simp only [excludedHighArray,Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
    highIdealMask_unmarked_mul S hS a b,
    bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hc]
  ring

def excludedHighPrimeTerm (S : Finset Id) (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  excludedHighArray S η x w z ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))

lemma excludedHighArray_prod (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    excludedHighArray S η x w z (highIdeals v)=v.prod (excludedHighPrimeTerm S η x w z) :=
  highArray_val_prod _ (excludedHighArray_one S hS η x w z) (excludedHighArray_mul S hS η x w z) v

lemma markedHighArray_val (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    markedIdealHighSummand S (∏P∈T,P.val) η 1 x w z
      (highIdeals v).1.1 (highIdeals v).1.2 (highIdeals v).2.1 (highIdeals v).2.2=
        markedArray T completedValuationMark (excludedHighPrimeTerm S η x w z) v := by
  rw [markedIdealHighSummand_mark,markedArray,completedValuationMark_product]
  change _*excludedHighArray S η x w z (highIdeals v)=_
  rw [excludedHighArray_prod S hS]

theorem markedIdealHighSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b)
      (markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z) := by
  have h0 (P : PrimeIdeal) : excludedHighPrimeTerm S η x w z P 0=1 := by
    simp only [excludedHighPrimeTerm,Prod.fst_zero,Prod.snd_zero,pow_zero]
    exact excludedHighArray_one S hS η x w z
  have hs := (markedIdealHighSummand_summable S 1 η 1 x w z hx hw hz).norm.comp_injective highIdeals_injective
  change Summable (fun v=>‖excludedHighArray S η x w z (highIdeals v)‖) at hs
  simp only [excludedHighArray_prod S hS] at hs
  have he := marked_hasProd T completedValuationMark (excludedHighPrimeTerm S η x w z) h0 hs
    (fun P _ b=> completedValuationMark_norm P b)
  have hsum : (∑'v : PrimeIdeal→₀HighValuation,
      markedArray T completedValuationMark (excludedHighPrimeTerm S η x w z) v)=
      markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z := by
    simp only [←markedHighArray_val S hS T η x w z]
    unfold markedIdealHighSeries
    apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
      markedIdealHighSummand S (∏P∈T,P.val) η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
    intro a ha
    have hh : bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hc := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
      ((⟨a.1.1,hc.2.1.1⟩,⟨a.1.2,hc.2.2.1.1⟩),(⟨a.2.1,hc.2.2.2.1.1⟩,⟨a.2.2,hc.2.2.2.2.1⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [hsum] using he

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma highExclusion_prime (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    highExclusion S hS P.val=if P.val∈S then 0 else 1 := by
  change (if ∀Q∈S,¬Q∣P.val then (1:ℂ) else 0)=_
  by_cases hP : P.val∈S
  · rw [if_neg (fun h=> h P.val hP (dvd_refl _)),if_pos hP]
  · have houtside : ∀Q∈S,¬Q∣P.val := by
      intro Q hQ hd
      have hn : (⟨Q,hS Q hQ⟩ : PrimeIdeal)≠P := by
        intro hh
        exact hP ((congrArg Subtype.val hh) ▸ hQ)
      exact (hS Q hQ).not_unit ((primeIdeal_coprime ⟨Q,hS Q hQ⟩ P hn).isUnit_of_dvd hd)
    rw [if_pos houtside,if_neg hP]

lemma highIdealMask_prime_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (P : PrimeIdeal) (hP : P.val∉S) (b : HighValuation) :
    highIdealMask S 1 (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=1 := by
  simp only [highIdealMask_unmarked S hS,map_pow,highExclusion_prime S hS P,
    if_neg hP,one_pow,one_mul]

lemma highIdealMask_prime_inside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (P : PrimeIdeal) (hP : P.val∈S) (b : HighValuation) :
    highIdealMask S 1 (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=
      if b=0 then 1 else 0 := by
  rcases b with ⟨⟨e,l⟩,k,m⟩
  simp only [highIdealMask_unmarked S hS,map_pow,highExclusion_prime S hS P,if_pos hP]
  by_cases he : e=0 <;> by_cases hl : l=0 <;> by_cases hk : k=0 <;> by_cases hm : m=0 <;>
    simp [he,hl,hk,hm,Prod.mk_eq_zero]

theorem excludedHighLocalFactor (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,markedIdealHighSummand S 1 η 1 x w z
      (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)) =
      if P.val∈S then 1 else idealHighLocalFactor η P.val x w z := by
  by_cases hP : P.val∈S
  · rw [if_pos hP]
    have he (b : HighValuation) : markedIdealHighSummand S 1 η 1 x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=if b=0 then 1 else 0 := by
      rw [markedIdealHighSummand,highIdealMask_prime_inside S hS P hP b]
      by_cases hb : b=0
      · subst b
        simp only [Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_one,mul_one]
      · simp only [if_neg hb,zero_mul]
    simp only [he,tsum_ite_eq]
  · rw [if_neg hP]
    simp only [markedIdealHighSummand,highIdealMask_prime_outside S hS P hP,one_mul]
    exact highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz P

theorem excludedIdealHighSeries_hasProd_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=> idealHighLocalFactor η P.val.val x w z)
      (markedIdealHighSeries S 1 η 1 x w z) := by
  have h := excludedIdealHighSeries_hasProd S hS η x w z hx hw hz
  simp only [excludedHighLocalFactor S hS η x w z hx hw hz] at h
  apply (hasProd_subtype_iff_mulIndicator
    (s:={P : PrimeIdeal | P.val∉S})
    (f:=fun P : PrimeIdeal=> idealHighLocalFactor η P.val x w z)).mpr
  convert h using 1 <;> first | rfl | (funext P; simp only [Set.mulIndicator,Set.mem_setOf_eq]; split_ifs <;> simp_all)

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow 
local notation "O" => Eisenstein.O

theorem idealHighLocalFactor_rational (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    idealHighLocalFactor η P.val x w z =
      (1-HeckeFamily.idealCoeff η P.val*(Q:ℂ)^(-x)) /
        ((1-(Q:ℂ)^(-6*z))*(1-(Q:ℂ)^(-w))) * idealClosedCorrection η P x w z := by
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp ((supported_iff_native _).mp hsp)
  have hprimary := (primaryIdealGenerator_spec P.val (supported_primaryIdealGenerator_ne_zero P.val hs)).2
  have hQ2 : (2:ℝ)≤ Ideal.absNorm (Ideal.span {p}) := by
    rw [hspan]
    exact_mod_cast HeckeIdealSeries.prime_norm_two_le P
  have hQ0 : (0:ℝ)< Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)< Ideal.absNorm (Ideal.span {p}) := by linarith
  have hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1 := by
    rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1 := by
    apply (coordW_norm_le _ hQ0 1 w (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hDnorm : ‖coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x‖<1 := by
    apply (coordD_norm_le _ hQ0 _ 1 x (targetMonoid_norm_le_one η p) (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x≠0 := by
    intro he
    have hh : coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x=1 := (sub_eq_zero.mp he).symm
    rw [hh,norm_one] at hDnorm
    exact lt_irrefl _ hDnorm
  have he := idealHighLocalFactor_euler_identity η p hp hg.1 hg.2 hprimary hsp x w z hV hR hW hD
  dsimp only at he ⊢
  rw [hspan,actualACube_sq,targetMonoid_primaryIdealGenerator η P.val hs] at he
  simpa only [coordD,coordV,coordW,star_one,mul_one,one_mul,idealClosedCorrection,p] using he

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein HeckeFamily
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma prime_coprime_fixedProduct (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    IsCoprime P.val (∏Q∈S,Q) ↔ P.val∉S := by
  rw [IsCoprime.prod_right_iff]
  constructor
  · intro h hP
    exact P.property.not_unit (isCoprime_self.mp (h P.val hP))
  · intro h Q hQ
    exact primeIdeal_coprime P ⟨Q,hS Q hQ⟩ (fun he=> h ((congrArg Subtype.val he).symm ▸ hQ))

lemma fixedSourcePrincipal_prime (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    idealCoeff (fixedSourcePrincipal S hS) P.val=if P.val∈S then 0 else 1 := by
  unfold fixedSourcePrincipal
  rw [HeckeRayFamily.idealCoeff_character,RayOrthogonality.idealCharacter_one]
  change (if P.val=0 then (0:ℂ) else if IsCoprime P.val (∏Q∈S,Q) then 1 else 0)=_
  simp only [P.property.ne_zero,ite_false,prime_coprime_fixedProduct S hS P]
  split_ifs <;> simp_all

lemma excludedTarget_prime (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    idealCoeff (η.excludePrimes S hS) P.val=if P.val∈S then 0 else idealCoeff η P.val := by
  rw [idealCoeff_excludePrimes]
  have he : (∀Q∈S,IsCoprime P.val Q) ↔ P.val∉S := by
    rw [←IsCoprime.prod_right_iff]
    exact prime_coprime_fixedProduct S hS P
  simp only [he]
  split_ifs <;> simp_all

theorem LFunction_hasProd_outside (χ : Character) (S : Finset Id) (a : Id→ℂ)
    (ha : ∀P : PrimeIdeal,idealCoeff χ P.val=if P.val∈S then 0 else a P.val)
    (s : ℂ) (hs : 1< s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-a P.val.val*fullIdealWeight s P.val.val)⁻¹) (LFunction χ s) := by
  have h := IdealEuler.euler_hasProd (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs
  rw [←LFunction_eq_series χ hs] at h
  have he (P : PrimeIdeal) : (1-IdealEuler.weighted (idealCoeff χ) s P.val)⁻¹=
      if P.val∈S then 1 else (1-a P.val*fullIdealWeight s P.val)⁻¹ := by
    change (1-idealCoeff χ P.val*fullIdealWeight s P.val)⁻¹=_
    rw [ha]
    split_ifs <;> simp only [zero_mul,sub_zero,inv_one]
  simp only [he] at h
  apply (hasProd_subtype_iff_mulIndicator (s:={P : PrimeIdeal|P.val∉S})
    (f:=fun P : PrimeIdeal=>(1-a P.val*fullIdealWeight s P.val)⁻¹)).mpr
  convert h using 1 <;> first | rfl | (funext P; simp only [Set.mulIndicator,Set.mem_setOf_eq]; split_ifs <;> simp_all)

theorem fixedSourcePrincipal_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (s : ℂ) (hs : 1< s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-fullIdealWeight s P.val.val)⁻¹) (LFunction (fixedSourcePrincipal S hS) s) := by
  simpa only [one_mul] using
    LFunction_hasProd_outside (fixedSourcePrincipal S hS) S (fun _=>1) (fixedSourcePrincipal_prime S hS) s hs

theorem excludedTarget_hasProd (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (s : ℂ) (hs : 1< s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-idealCoeff η P.val.val*fullIdealWeight s P.val.val)⁻¹)
      (LFunction (η.excludePrimes S hS) s) :=
  LFunction_hasProd_outside _ S (idealCoeff η) (excludedTarget_prime η S hS) s hs

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein HeckeFamily CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

theorem principalHigh_L_factorization (S : Finset Id) (hS : ∀P∈S,Prime P)
    (hgood : ∀P : PrimeIdeal,P.val∉S → Supported P.val) (htail : CorrectionTail S)
    (η : Character) (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    markedIdealHighSeries S 1 η 1 x w z =
      LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (fixedSourcePrincipal S hS) w /
        LFunction (η.excludePrimes S hS) x * globalClosedCorrection η S x w z := by
  have hx1 : 1< x.re := by linarith
  have hw1 : 1< w.re := by linarith
  have hz1 : 1<(6*z).re := by
    norm_num [Complex.mul_re]
    linarith
  have hH := globalClosedCorrection_multipliable η S htail x w z (by linarith) (by linarith) (by linarith)
  have hinv : HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>
      ((1-idealCoeff η P.val.val*fullIdealWeight x P.val.val)⁻¹)⁻¹)
      (LFunction (η.excludePrimes S hS) x)⁻¹ := by
    have h := excludedTarget_hasProd η S hS x hx1
    rw [HasProd] at h ⊢
    simpa only [Finset.prod_inv_distrib] using
      h.inv₀ (LFunction_ne_zero_of_one_lt_re (η.excludePrimes S hS) hx1)
  have he := (((fixedSourcePrincipal_hasProd S hS (6*z) hz1).mul
    (fixedSourcePrincipal_hasProd S hS w hw1)).mul hinv).mul hH.hasProd
  have hlocal (P : {P : PrimeIdeal // P.val∉S}) :
      ((1-fullIdealWeight (6*z) P.val.val)⁻¹ *
       (1-fullIdealWeight w P.val.val)⁻¹ *
       ((1-idealCoeff η P.val.val*fullIdealWeight x P.val.val)⁻¹)⁻¹) *
       idealClosedCorrection η P.val x w z = idealHighLocalFactor η P.val.val x w z := by
    rw [idealHighLocalFactor_rational η P.val (hgood P.val P.property) x w z hx hw hz]
    simp only [fullIdealWeight,P.val.property.ne_zero,ite_false,
      Complex.ofReal_natCast,div_eq_mul_inv,mul_inv_rev,inv_inv]
    rw [show -(6*z)=(-6:ℂ)*z by ring]
    ring
  have he' : HasProd (fun P : {P : PrimeIdeal // P.val∉S}=> idealHighLocalFactor η P.val.val x w z)
      (LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (fixedSourcePrincipal S hS) w /
        LFunction (η.excludePrimes S hS) x * globalClosedCorrection η S x w z) := by
    simpa only [hlocal,div_eq_mul_inv,globalClosedCorrection] using he
  exact (excludedIdealHighSeries_hasProd_outside S hS η x w z hx hw hz).unique he'

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CanonicalQuadraticSieve UniqueFactorizationMonoid ProbeEuler
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

theorem source_principalHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (x w z : ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    markedIdealHighSeries S 1 η 1 x w z =
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
        HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z :=
  principalHigh_L_factorization S hS.prime (outside_prime_supported S hS.bad) hS.tail η x w z hx hw hz

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ProbeEuler ProbeRow 
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def idealMarkedLocalFactor (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∑e : Fin 2,∑'l,∑'k,∑'m,
    completedValuationMark P ((e.val,l),(k,m))*highPrimeTerm η x w z P ((e.val,l),(k,m))

lemma markedPrimeTerm_summable_norm (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    Summable (fun b : HighValuation=>‖completedValuationMark P b*highPrimeTerm η x w z P b‖) := by
  apply Summable.of_nonneg_of_le (fun _=> norm_nonneg _) _ (highPrimeTerm_summable_norm η x w z hx hw hz P)
  intro b
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (completedValuationMark_norm P b)

lemma markedPrimeTerm_tsum (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    (∑'b : HighValuation,completedValuationMark P b*highPrimeTerm η x w z P b)=
      idealMarkedLocalFactor η P x w z := by
  have hs := (markedPrimeTerm_summable_norm η P x w z hx hw hz).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) : (∑'b : ℕ×ℕ,completedValuationMark P ((e,l),b)*highPrimeTerm η x w z P ((e,l),b))=
      ∑'k,∑'m,completedValuationMark P ((e,l),(k,m))*highPrimeTerm η x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=> by
    have hh : 2≤ e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [highPrimeTerm_zero_of_two_le η x w z P e _ _ _ hh,mul_zero,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

lemma selectedLocal_outside (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    (∑'b : HighValuation,ProbeEulerFinsupp.markedLocal T completedValuationMark
      (excludedHighPrimeTerm S η x w z) P b)=
      if P∈T then idealMarkedLocalFactor η P x w z else idealHighLocalFactor η P.val x w z := by
  have he (b : HighValuation) : excludedHighPrimeTerm S η x w z P b=highPrimeTerm η x w z P b := by
    simp only [excludedHighPrimeTerm,excludedHighArray,markedIdealHighSummand,
      highIdealMask_prime_outside S hS P hP,one_mul,highPrimeTerm]
  simp only [ProbeEulerFinsupp.markedLocal,he]
  by_cases hPT : P∈T
  · simp only [if_pos hPT]
    exact markedPrimeTerm_tsum η P x w z hx hw hz
  · simp only [if_neg hPT,one_mul]
    exact highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz P

lemma idealMarkedLocalFactor_eq_source (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    let p := primaryIdealGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    letI : (Ideal.span {p}:Id).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hg := (supported_prime_data p hp ((supported_iff_native _).mp ((CenteredMomentSourceRow.primary_span_supported P.val hs).symm ▸ hs))).1
    idealMarkedLocalFactor η P x w z=
      principalMarkedSeries p hp hg (targetMonoid η p) (actualACube η p)
        ((Ideal.absNorm P.val:ℂ)^(-x)) ((Ideal.absNorm P.val:ℂ)^(-w))
        (coordV (Ideal.absNorm P.val) z) := by
  dsimp only
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Id).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp ((supported_iff_native _).mp hsp)
  have hprimary := (primaryIdealGenerator_spec P.val (supported_primaryIdealGenerator_ne_zero P.val hs)).2
  unfold idealMarkedLocalFactor principalMarkedSeries principalInner
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  change completedValuationMark P ((e.val,l),(k,m))*bareIdealHighSummand η 1 x w z
    (P.val^e.val) (P.val^l) (P.val^k) (P.val^m)=_
  have hterm := bareIdealHighSummand_at_prime η p hp hg.1 hg.2 hprimary hsp e.val l k m (by omega) x w z
  conv_lhs at hterm => rw [hspan]
  rw [hterm]
  by_cases ht : e.val+3*l=0
  · have he0 : e.val=0 := by omega
    have hl0 : l=0 := by omega
    simp only [completedValuationMark,ht,ne_eq,not_true_eq_false,ite_false,zero_mul]
    rw [he0,hl0]
    simpa only [hspan] using (markedTerm_zero_index p hp hg.1 (targetMonoid η p)
      (actualACube η p) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) k m).symm
  · simp only [completedValuationMark,ht,ne_eq,not_false_eq_true,ite_true,one_mul]
    simpa only [hspan] using sourcePrincipalTerm_pos p hp hg.1 (targetMonoid η p) (actualACube η p) x w z e.val l k m ht

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow 
local notation "O" => Eisenstein.O

theorem idealMarkedLocalFactor_rational (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hx : 3/2< x.re) (hz : 1/6< z.re) :
    idealMarkedLocalFactor η P x w z=idealMarkedClosed η P x w z := by
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp ((supported_iff_native _).mp hsp)
  have hQ2 : (2:ℝ)≤ Ideal.absNorm (Ideal.span {p}) := by
    rw [hspan]
    exact_mod_cast HeckeIdealSeries.prime_norm_two_le P
  have hQ0 : (0:ℝ)< Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)< Ideal.absNorm (Ideal.span {p}) := by linarith
  have hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1 := by
    rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hr := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (actualACube η p) x z
  simp only [Complex.ofReal_natCast] at hr
  have he := principalMarkedSeries_eq p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p)
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) hV (by simpa only [hr] using hR)
  have hsource := idealMarkedLocalFactor_eq_source η P hs x w z
  dsimp only at hsource
  rw [hsource]
  have hk := coordK_eq_geometric (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (targetMonoid η p) x w
  simp only [Complex.ofReal_natCast] at hr hk
  rw [hr,←hk] at he
  simp only [actualACube_sq] at he
  convert he using 1
  · congr 2 <;> simp only [hspan,p]
  · simp only [idealMarkedClosed,coordD,coordW,star_one,mul_one,one_mul]
    simp only [hspan,p,targetMonoid_primaryIdealGenerator η P.val hs,Complex.ofReal_natCast,neg_mul]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein ProbeEuler ProbeEulerFinsupp
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma source_idealHighLocalFactor_ne_zero (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    idealHighLocalFactor η P.val x w z≠0 := by
  rw [idealHighLocalFactor_rational η P (outside_prime_supported S hS.bad P hP) x w z hx hw hz]
  have hQ : (1:ℝ)< Ideal.absNorm P.val := by
    have hh := hS.tail.norm_four P hP
    exact_mod_cast (by omega : 1< Ideal.absNorm P.val)
  have hQ0 : (0:ℝ)< Ideal.absNorm P.val := by linarith
  have hD : ‖HeckeFamily.idealCoeff η P.val*(Ideal.absNorm P.val:ℂ)^(-x)‖<1 := by
    rw [norm_mul,Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0),Complex.neg_re]
    apply (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (HeckeFamily.idealCoeff_norm_le_one η P.val)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  have hV : ‖(Ideal.absNorm P.val:ℂ)^(-6*z)‖<1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0)]
    apply Real.rpow_lt_one_of_one_lt_of_neg hQ
    norm_num [Complex.mul_re]
    linarith
  have hW : ‖(Ideal.absNorm P.val:ℂ)^(-w)‖<1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0),Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  apply mul_ne_zero
  · exact div_ne_zero (one_sub_ne_zero_of_norm_lt_one _ hD)
      (mul_ne_zero (one_sub_ne_zero_of_norm_lt_one _ hV) (one_sub_ne_zero_of_norm_lt_one _ hW))
  · exact factor_ne_zero_of_defect _ ((idealClosedCorrection_bound η P (hS.tail.norm_four P hP)
      x w z (by linarith) (by linarith) (by linarith)).trans (hS.tail.half ⟨P,hP⟩))

theorem markedIdealHighSeries_eq_product (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z=
      markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z := by
  let R := fun P : PrimeIdeal=> if P∈T then
    idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z else 1
  have hR : HasProd R (∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R) (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=> if_neg hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := (excludedIdealHighSeries_hasProd S hS.prime η x w z hx hw hz).mul hR
  have heq (P : PrimeIdeal) :
      (∑'b : HighValuation,excludedHighPrimeTerm S η x w z P b)*R P=
      ∑'b : HighValuation,markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b := by
    by_cases hp : P∈T
    · rw [selectedLocal_outside S hS.prime T η P (hT P hp) x w z hx hw hz,if_pos hp]
      have hu : (∑'b : HighValuation,excludedHighPrimeTerm S η x w z P b)=idealHighLocalFactor η P.val x w z := by
        simpa only [excludedHighPrimeTerm,excludedHighArray,if_neg (hT P hp)] using
          excludedHighLocalFactor S hS.prime η x w z hx hw hz P
      rw [hu,show R P=idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z from if_pos hp]
      exact mul_div_cancel₀ _ (source_idealHighLocalFactor_ne_zero S hS η P (hT P hp) x w z hx hw hz)
    · simp only [R,hp,ite_false,mul_one,markedLocal,one_mul]
  have he' : HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b)
      (markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z) := by
    convert he using 1 <;> first | rfl | (funext P; exact (heq P).symm)
  exact (markedIdealHighSeries_hasProd S hS.prime T η x w z hx hw hz).unique he'

theorem source_markedHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z := by
  rw [markedIdealHighSeries_eq_product S hS T hT η x w z hx hw hz,
    source_principalHigh_L_factorization S hS η x w z hx hw hz]

end ProbePhysical
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
