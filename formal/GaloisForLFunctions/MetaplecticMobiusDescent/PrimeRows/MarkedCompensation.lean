/-
Marked compensation adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SelectedPrimeSums
import GaloisForLFunctions.MetaplecticMobiusDescent.PrimeRows.HighRowCharacters

/-!
# Marked compensation

Continued compensated local factors and rows, marked source exclusions and calibrated tuple
values; first-subpower bounds of unselected corrections; dyadic weighted rows.
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
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

def globalNormalization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  (LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
    (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x

theorem globalNormalization_finite_split (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 1< x.re) (hw : 1< w.re) (hz : 1<(6*z).re) :
    globalNormalization S hS η u x w z=
      globalNormalization (markExclusions S T) (markExclusions_prime S hS T) η u x w z*
        ∏P∈T,localNormalization η u P x w z := by
  have hleft := localNormalization_hasProd S hS hbad η u x w z hx hw hz
  have hbase := localNormalization_hasProd (markExclusions S T) (markExclusions_prime S hS T)
    (hbad.trans Finset.subset_union_left) η u x w z hx hw hz
  let R := fun P : HeckeIdealSeries.PrimeIdeal=> if P∈T then localNormalization η u P x w z else 1
  have hR : HasProd R (∏P∈T,localNormalization η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional HeckeIdealSeries.PrimeIdeal) (fun P hP=> if_neg hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  apply hleft.unique
  convert hbase.mul hR using 1
  · funext P
    by_cases hP : P∈T
    · simp only [if_neg (hT P hP),mem_markExclusions,hP,or_true,ite_true,R,if_pos hP,one_mul]
    · simp only [mem_markExclusions,hP,or_false,R,if_neg hP,mul_one]
  · rfl

theorem finite_replacement_normalized (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (g : HeckeIdealSeries.PrimeIdeal→ℂ) (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    (markedIdealHighSeries (markExclusions S T) 1 η u.val x w z*∏P∈T,g P)*
      globalNormalization S hS η u x w z=
      globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,g P*localNormalization η u P x w z := by
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  rw [globalNormalization_finite_split S hS hbad T hT η u x w z (by linarith) (by linarith) hz1,
    globalCorrection,(localCorrection_hasProd (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz).tprod_eq,
    Finset.prod_mul_distrib,globalNormalization]
  ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

/-- The marked local factor after subtracting its unmarked contribution. -/
def compensatedLocalCorrection (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (x w z B q : ℂ) : ℂ :=
  B*markedLocalCorrection η u P x w z-q*localCorrection η u P x w z

theorem compensatedLocalCorrection_eq_raw (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (x w z B q : ℂ) :
    compensatedLocalCorrection η u P x w z B q=
      (B*idealRowMarkedLocalFactor η u.val P x w z-q*idealRowHighLocalFactor η u.val P.val x w z)*
        localNormalization η u P x w z := by
  rw [compensatedLocalCorrection,markedLocalCorrection,localCorrection_eq_normalization]
  ring

theorem spectralCompensatedRow_original_L_factorization
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (B q : HeckeIdealSeries.PrimeIdeal→ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    spectralCompensatedRow S T η u.val x w z B q=
      (LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (rowCharacter S hS u) w/
        LFunction ((targetRow η u).excludePrimes S hS) x)*
      (globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,compensatedLocalCorrection η u P x w z (B P) (q P)) := by
  have hx1 : 1< x.re := by linarith
  have hw1 : 1< w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hZ := LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := LFunction_ne_zero_of_one_lt_re ((targetRow η u).excludePrimes S hS) hx1
  have hn := finite_replacement_normalized S hS hbad T hT η u x w z
    (fun P=> B P*idealRowMarkedLocalFactor η u.val P x w z-q P*idealRowHighLocalFactor η u.val P.val x w z)
    hx hw hz
  simp_rw [←compensatedLocalCorrection_eq_raw] at hn
  rw [←spectralCompensatedRow_eq_product S hS T hT η u.val x w z B q hx hw hz] at hn
  rw [←hn,globalNormalization]
  field_simp

theorem indexedCompensatedHigh_original_L_factorization {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    indexedCompensatedHigh η S (fun i=> primaryIdealGenerator (P i).val) u.val x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (rowCharacter S hS.prime u) w/
        LFunction ((targetRow η u).excludePrimes S hS.prime) x)*
      (globalCorrection (markExclusions S (Finset.univ.image P)) η u x w z*
        ∏i,compensatedLocalCorrection η u (P i) x w z
          (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
          (((P i).val.absNorm:ℂ)^(-w))) := by
  have hs (i : Fin K) := outside_prime_supported S hS.bad (P i) (hPS i)
  rw [indexedCompensatedHigh_eq_spectral η S P hP hs u.val x w z]
  have ht : ∀Q∈Finset.univ.image P,Q.val∉S := by
    intro Q hQ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
    exact hPS i
  rw [spectralCompensatedRow_original_L_factorization S hS.prime hS.bad
    (Finset.univ.image P) ht η u x w z _ _ hx hw hz,Finset.prod_image hP.injOn]

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
local notation "O" => Eisenstein.O

/-- Closed local series expressed through the primary generator and valuation of the row. -/
def continuedMarkedLocal (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  let p := primaryIdealGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (CenteredMomentSourceRow.primary_span_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)).1
  rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
    ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
    (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    (multiplicity p u.val)

theorem idealRowMarkedLocalFactor_eq_source (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    let p := primaryIdealGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hsp : Supported (Ideal.span {p}) := (CenteredMomentSourceRow.primary_span_supported P.val hs).symm ▸ hs
    let hg := (supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)).1
    idealRowMarkedLocalFactor η u.val P x w z=
      rowMarkedSeries p hp hg (targetMonoid η p) (actualACube η p)
        ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
        (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
        (multiplicity p u.val) := by
  dsimp only
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)
  have hprimary := (primaryIdealGenerator_spec P.val (supported_primaryIdealGenerator_ne_zero P.val hs)).2
  unfold idealRowMarkedLocalFactor rowMarkedSeries rowInner
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  change completedValuationMark P ((e.val,l),(k,m))*bareIdealHighSummand η u.val x w z
    (P.val^e.val) (P.val^l) (P.val^k) (P.val^m)=_
  have ht := bareIdealHighSummand_row_at_prime η p hp hg.1 hg.2 hprimary hsp
    (unitPart u p hp) (unitPart_coprime u p hp) (multiplicity p u.val) e.val l k m (by omega) x w z
  rw [←(canonical_decomposition u p hp).1] at ht
  conv_lhs at ht => rw [hspan]
  rw [ht]
  by_cases hzero : e.val+3*l=0
  · simp only [completedValuationMark,hzero,ne_eq,not_true_eq_false,ite_false,zero_mul,
      rowMarkedTerm,ite_true]
  · simp only [completedValuationMark,hzero,ne_eq,not_false_eq_true,ite_true,one_mul]
    simpa only [hspan] using sourceRowTerm_pos p hp hg.1 (targetMonoid η p) (actualACube η p)
      (complexSexticChar (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x w z
      (multiplicity p u.val) e.val l k m hzero

theorem continuedMarkedLocal_eq_initial (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    continuedMarkedLocal η u P hs x w z=idealRowMarkedLocalFactor η u.val P x w z := by
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)
  have hρ := complexSexticChar_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)
  have hgeom := row_initial_geometric η p hp hg.1 hg.2 (unitPart u p hp)
    (unitPart_coprime u p hp) x w z hx hw hz
  have hQ0 : (0:ℝ)< Ideal.absNorm (Ideal.span {p}) :=
    HeckeDyadic.norm_pos ⟨Ideal.span {p},Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero⟩
  have he := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (actualACube η p) x z
  simp only [Complex.ofReal_natCast] at he
  have hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [he]
    exact hgeom.2.1
  rw [idealRowMarkedLocalFactor_eq_source η u P hs x w z]
  unfold continuedMarkedLocal
  symm
  simpa only [hspan] using rowMarkedSeries_eq_closed p hp hg.1 hg.2 (targetMonoid η p)
    (actualACube η p) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
    _ hρ hgeom.1 hR (multiplicity p u.val) (multiplicity_lt_six u p hp)

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ComplexConjugate
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
local notation "O" => Eisenstein.O

def continuedCompensatedLocal (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (hs : Supported P.val)
    (x w z B q : ℂ) : ℂ :=
  ProbeLocal.compensatedReplacement (coordV P.val.absNorm z)
    (coordW P.val.absNorm (idealRowHom u.val P.val) w)
    (coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x)
    (continuedMarkedLocal η u P hs x w z) B q

theorem localNormalization_coordinates (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (x w z : ℂ) :
    localNormalization η u P x w z=
      (1-coordV P.val.absNorm z)*(1-coordW P.val.absNorm (idealRowHom u.val P.val) w)/
        (1-coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x) := by
  unfold localNormalization coordV coordW coordD fullIdealWeight
  simp only [P.property.ne_zero,ite_false,Complex.ofReal_natCast]
  rw [show -(6*z)=(-6:ℂ)*z by ring]
  rfl

theorem row_phase_ramified (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (hP : P.val∣Ideal.span {u.val}) :
    idealRowHom u.val P.val=0 := by
  have hu : u.val∈P.val := (Ideal.dvd_iff_le.mp hP) (Ideal.subset_span (by simp))
  exact idealRowHom_zero_of_dvd u.val P.property (dvd_refl _) hu

theorem continuedCompensatedLocal_ramified (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    let p := primaryIdealGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    letI : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hg := (supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp
      ((CenteredMomentSourceRow.primary_span_supported P.val hs).symm ▸ hs))).1
    continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))=
      ramifiedSelected p hp hg (targetMonoid η p) (actualACube η p)
        (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
        x w z (multiplicity p u.val) := by
  dsimp only
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)
  have he := ramifiedSelected_eq_replacement p hp hg.1 (targetMonoid η p) (actualACube η p)
    (complexSexticChar (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val)
  rw [he]
  unfold continuedCompensatedLocal
  rw [row_phase_ramified u P hP]
  simp only [coordW,coordD,zero_mul,mul_zero,star_zero]
  rw [←targetMonoid_primaryIdealGenerator η P.val hs]
  unfold continuedMarkedLocal
  simp only [hspan]
  rfl

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ComplexConjugate
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
local notation "O" => Eisenstein.O

theorem continuedMarkedLocal_unramified (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryIdealGenerator P.val)) x z‖<1) :
    continuedMarkedLocal η u P hs x w z=
      unramifiedMarked P.val.absNorm (actualAPhase η (primaryIdealGenerator P.val))
        (idealCoeff η P.val) (idealRowHom u.val P.val) x w z := by
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)
  have hnot : ¬p∣u.val := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hj := multiplicity_eq_zero.mpr hnot
  have hb : unitPart u p hp=u.val := by
    have he := (unitPart_spec u p hp).1
    rw [hj,pow_zero,one_mul] at he
    exact he.symm
  have hu : IsCoprime u.val p := by rw [←hb]; exact unitPart_coprime u p hp
  have hρ := complexSexticChar_unit_six p u.val hg.1 hg.2 hu
  have hQ0 : (0:ℝ)< Ideal.absNorm (Ideal.span {p}) :=
    HeckeDyadic.norm_pos ⟨Ideal.span {p},Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero⟩
  have hr := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (actualACube η p) x z
  simp only [Complex.ofReal_natCast] at hr
  have hR' : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hr,actualACube_sq,hspan]
    exact hR
  have hv' : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by rw [hspan];exact hV
  have hh := rowClosedMarked_unramified p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p)
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) _ hρ hv' hR'
  have hk := coordK_eq_geometric (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (targetMonoid η p) x w
  simp only [Complex.ofReal_natCast] at hk
  have hi : (complexSexticChar (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val))⁻¹=
      star (complexSexticChar (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val)) :=
    Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hρ (by decide))
  have heta : idealCoeff η P.val=targetMonoid η p :=
    (targetMonoid_primaryIdealGenerator η P.val hs).symm
  have hphase : idealRowHom u.val P.val=
      complexSexticChar (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    conv_lhs => rw [←hspan]
    exact idealRowHom_prime u.val (Ideal.span {p}) hg.1
  simp only [hspan] at hh hr hk
  unfold continuedMarkedLocal
  change rowClosedMarked p hp hg.1 (targetMonoid η p) (actualACube η p)
    ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
    (complexSexticChar (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) (multiplicity p u.val)=_
  rw [hj,hb,hh,hr,←hk,actualACube_sq,heta,hphase]
  simp only [unramifiedMarked,coordD,coordW,div_eq_mul_inv,hi,Complex.ofReal_natCast]
  congr 1; ring

theorem continuedCompensatedLocal_unramified (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryIdealGenerator P.val)) x z‖<1) :
    continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))=
      unramifiedSelected P.val.absNorm (actualAPhase η (primaryIdealGenerator P.val))
        (idealCoeff η P.val) (idealRowHom u.val P.val) x w z := by
  rw [continuedCompensatedLocal,continuedMarkedLocal_unramified η u P hs hn x w z hV hR]
  rfl

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ComplexConjugate
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
local notation "O" => Eisenstein.O

def finiteLocalCorrection (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  ProbeLocal.continuedCorrection (coordV P.val.absNorm z)
    (coordW P.val.absNorm (idealRowHom u.val P.val) w)
    (coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x)
    (continuedMarkedLocal η u P hs x w z)

theorem continuedCompensatedLocal_eq_difference (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (x w z B q : ℂ) :
    continuedCompensatedLocal η u P hs x w z B q=
      B*continuedMarkedLocal η u P hs x w z*localNormalization η u P x w z-
        q*finiteLocalCorrection η u P hs x w z := by
  rw [localNormalization_coordinates]
  unfold continuedCompensatedLocal finiteLocalCorrection ProbeLocal.compensatedReplacement ProbeLocal.continuedCorrection
  ring

theorem ramifiedCorrection_eq_marked (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    ramifiedCorrection η u P hs x w z=
      1+(1-coordV P.val.absNorm z)*continuedMarkedLocal η u P hs x w z := by
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := (supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)).1
  have hnorm : Ideal.absNorm (Ideal.span {p})=P.val.absNorm := congrArg Ideal.absNorm hspan
  change ramifiedClosed p hp hg (targetMonoid η p) (actualACube η p)
    (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val)=
    1+(1-coordV P.val.absNorm z)*rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
      ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
      (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) (multiplicity p u.val)
  unfold ramifiedClosed
  rw [hnorm]

theorem finiteLocalCorrection_ramified (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    finiteLocalCorrection η u P hs x w z=ramifiedCorrection η u P hs x w z := by
  rw [ramifiedCorrection_eq_marked]
  unfold finiteLocalCorrection
  rw [row_phase_ramified u P hP]
  simp only [coordW,coordD,star_zero,mul_zero,zero_mul,ProbeLocal.continuedCorrection,
    sub_zero,mul_one,div_one]

theorem finiteLocalCorrection_unramified (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryIdealGenerator P.val)) x z‖<1) :
    finiteLocalCorrection η u P hs x w z=idealUnramifiedCorrection η u P x w z := by
  rw [finiteLocalCorrection,continuedMarkedLocal_unramified η u P hs hn x w z hV hR]
  rfl

theorem initial_marked_geometry (η : Character) (P : HeckeIdealSeries.PrimeIdeal) (x z : ℂ)
    (hx : 3/2< x.re) (hz : 1/6< z.re) :
    ‖coordV P.val.absNorm z‖<1 ∧
      ‖coordR P.val.absNorm (actualAPhase η (primaryIdealGenerator P.val)) x z‖<1 := by
  have hQ : (1:ℝ)< P.val.absNorm := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1:ℕ)<2) (HeckeIdealSeries.prime_norm_two_le P))
  have hQ0 : (0:ℝ)< P.val.absNorm := by linarith
  constructor
  · rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  · apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η _)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)

theorem finiteLocalCorrection_eq_initial (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    finiteLocalCorrection η u P hs x w z=localCorrection η u P x w z := by
  by_cases hP : P.val∣Ideal.span {u.val}
  · rw [finiteLocalCorrection_ramified η u P hs hP]
    exact (localCorrection_eq_ramified η u P hs hP x w z hx hw hz).symm
  · have hg := initial_marked_geometry η P x z hx hz
    rw [finiteLocalCorrection_unramified η u P hs hP x w z hg.1 hg.2]
    exact (localCorrection_unramified_ideal η u P hs (supported_prime_coprime P hs u.val hP)
      x w z hx hw hz).symm

theorem continuedCompensatedLocal_eq_initial (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (x w z B q : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    continuedCompensatedLocal η u P hs x w z B q=compensatedLocalCorrection η u P x w z B q := by
  rw [continuedCompensatedLocal_eq_difference,
    continuedMarkedLocal_eq_initial η u P hs x w z hx hw hz,
    finiteLocalCorrection_eq_initial η u P hs x w z hx hw hz]
  unfold compensatedLocalCorrection markedLocalCorrection
  ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Filter
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CompletedGauss
local notation "O" => Eisenstein.O

theorem continuedMarkedLocal_eq_quotient (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hV : 1-coordV P.val.absNorm z≠0) :
    continuedMarkedLocal η u P hs x w z=(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z) := by
  rw [ramifiedCorrection_eq_marked]
  field_simp
  ring

theorem selected_V_ne_zero (P : HeckeIdealSeries.PrimeIdeal) (hQ : (4:ℝ)≤ P.val.absNorm) (z : ℂ)
    (hz : (4/25:ℝ)≤ z.re) : 1-coordV P.val.absNorm z≠0 := by
  apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
  rw [coordV_norm _ (by linarith : (0:ℝ)< P.val.absNorm)]
  apply rpow_le_half _ _ hQ
  linarith

theorem continuedMarkedLocal_analyticAt_x (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)< x.re) (hz : (4/25:ℝ)≤ z.re) :
    AnalyticAt ℂ (fun x=> continuedMarkedLocal η u P hs x w z) x := by
  have he : (fun x=> continuedMarkedLocal η u P hs x w z)=
      (fun x=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun x=> continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z hz))
  rw [he]
  exact (((ramifiedCorrection_analytic_x η u P hs hQ w z hz) x hx).sub analyticAt_const).div_const

theorem continuedMarkedLocal_differentiable_w (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm) (x z : ℂ)
    (hx : (7/8:ℝ)≤ x.re) (hz : (4/25:ℝ)≤ z.re) :
    Differentiable ℂ (fun w=> continuedMarkedLocal η u P hs x w z) := by
  have he : (fun w=> continuedMarkedLocal η u P hs x w z)=
      (fun w=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun w=> continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z hz))
  rw [he]
  exact ((ramifiedCorrection_analytic_w η u P hs hQ x z hx hz).sub_const 1).div_const _

theorem continuedMarkedLocal_analyticAt_z (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)≤ x.re) (hz : (4/25:ℝ)< z.re) :
    AnalyticAt ℂ (fun z=> continuedMarkedLocal η u P hs x w z) z := by
  have hcv := (coordV_differentiable (P.val.absNorm:ℝ) (by linarith)).analyticAt z
  have ha : AnalyticAt ℂ (fun t=>(ramifiedCorrection η u P hs x w t-1)/(1-coordV P.val.absNorm t)) z :=
    (((ramifiedCorrection_analytic_z η u P hs hQ x w hx) z hz).sub analyticAt_const).div
    (analyticAt_const.sub hcv) (selected_V_ne_zero P hQ z hz.le)
  apply ha.congr
  filter_upwards [(show IsOpen {z : ℂ | (4/25:ℝ) < z.re} from isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with t ht
  exact (continuedMarkedLocal_eq_quotient η u P hs x w t (selected_V_ne_zero P hQ t ht.le)).symm

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => Eisenstein.O

theorem continuedCompensatedLocal_differentiableAt_x (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)< x.re) (hz : (4/25:ℝ)≤ z.re) :
    DifferentiableAt ℂ (fun x=> continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) x := by
  have hQ0 : (0:ℝ)< P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := (continuedMarkedLocal_analyticAt_x η u P hs hQ x w z hx hz).differentiableAt
  have hD := coordD_differentiable (P.val.absNorm:ℝ) hQ0 (idealCoeff η P.val) (idealRowHom u.val P.val)
  have hB : Differentiable ℂ (fun x:ℂ=> star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) :=
    (differentiable_id.const_cpow (Or.inl hQc)).const_mul _
  have hd := (open_region_denominators (P.val.absNorm:ℝ) 0 (idealCoeff η P.val)
    (idealRowHom u.val P.val) x z hQ (by simp) (idealCoeff_norm_le_one η _)
    (idealRowHom_norm u.val _) hx.le hz).2.2
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop (disch := first | assumption | exact Or.inl hQc)

theorem continuedCompensatedLocal_differentiable_w (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm) (x z : ℂ)
    (hx : (7/8:ℝ)≤ x.re) (hz : (4/25:ℝ)≤ z.re) :
    Differentiable ℂ (fun w=> continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) := by
  have hQ0 : (0:ℝ)< P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := continuedMarkedLocal_differentiable_w η u P hs hQ x z hx hz
  have hW := coordW_differentiable (P.val.absNorm:ℝ) hQ0 (idealRowHom u.val P.val)
  have hq : Differentiable ℂ (fun w:ℂ=>(P.val.absNorm:ℂ)^(-w)) :=
    differentiable_id.neg.const_cpow (Or.inl hQc)
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop

theorem continuedCompensatedLocal_differentiableAt_z (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm) (x w z : ℂ)
    (hx : (7/8:ℝ)≤ x.re) (hz : (4/25:ℝ)< z.re) :
    DifferentiableAt ℂ (fun z=> continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) z := by
  have hQ0 : (0:ℝ)< P.val.absNorm := by linarith
  have hM := (continuedMarkedLocal_analyticAt_z η u P hs hQ x w z hx hz).differentiableAt
  have hV := coordV_differentiable (P.val.absNorm:ℝ) hQ0
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Filter
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => Eisenstein.O

theorem continuedMarkedLocal_first_analyticAt_x (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm) (x w z : ℂ)
    (hx : (1/2:ℝ)< x.re) (hz : (1/3:ℝ)≤ z.re) :
    AnalyticAt ℂ (fun x=> continuedMarkedLocal η u P hs x w z) x := by
  have he : (fun x=> continuedMarkedLocal η u P hs x w z)=
      (fun x=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun x=> continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z (by linarith)))
  rw [he]
  exact (((ramifiedCorrection_first_analytic_x η u P hs hQ w z hz) x hx).sub analyticAt_const).div_const

theorem continuedMarkedLocal_first_differentiable_w (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm) (x z : ℂ)
    (hx : (1/2:ℝ)≤ x.re) (hz : (1/3:ℝ)≤ z.re) :
    Differentiable ℂ (fun w=> continuedMarkedLocal η u P hs x w z) := by
  have he : (fun w=> continuedMarkedLocal η u P hs x w z)=
      (fun w=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun w=> continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z (by linarith)))
  rw [he]
  exact ((ramifiedCorrection_first_analytic_w η u P hs hQ x z hx hz).sub_const 1).div_const _

theorem continuedMarkedLocal_first_analyticAt_z (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm) (x w z : ℂ)
    (hx : (1/2:ℝ)≤ x.re) (hz : (1/3:ℝ)< z.re) :
    AnalyticAt ℂ (fun z=> continuedMarkedLocal η u P hs x w z) z := by
  have hcv := (coordV_differentiable (P.val.absNorm:ℝ) (by linarith)).analyticAt z
  have ha : AnalyticAt ℂ (fun t=>(ramifiedCorrection η u P hs x w t-1)/(1-coordV P.val.absNorm t)) z :=
    (((ramifiedCorrection_first_analytic_z η u P hs hQ x w hx) z hz).sub analyticAt_const).div
    (analyticAt_const.sub hcv) (selected_V_ne_zero P hQ z (by linarith))
  apply ha.congr
  filter_upwards [(show IsOpen {z : ℂ | (1/3:ℝ) < z.re} from isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with t ht
  exact (continuedMarkedLocal_eq_quotient η u P hs x w t (selected_V_ne_zero P hQ t (by linarith))).symm

theorem continuedCompensatedLocal_first_differentiableAt_x (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm) (x w z : ℂ)
    (hx : (1/2:ℝ)< x.re) (hz : (1/3:ℝ)≤ z.re) :
    DifferentiableAt ℂ (fun x=> continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) x := by
  have hQ0 : (0:ℝ)< P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := (continuedMarkedLocal_first_analyticAt_x η u P hs hQ x w z hx hz).differentiableAt
  have hD := coordD_differentiable (P.val.absNorm:ℝ) hQ0 (idealCoeff η P.val) (idealRowHom u.val P.val)
  have hB : Differentiable ℂ (fun x:ℂ=> star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) :=
    (differentiable_id.const_cpow (Or.inl hQc)).const_mul _
  have hd := (first_open_region_denominators (P.val.absNorm:ℝ) 0 (idealCoeff η P.val)
    (idealRowHom u.val P.val) x z hQ (by simp) (idealCoeff_norm_le_one η _)
    (idealRowHom_norm u.val _) hx.le hz).2.2
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop (disch := first | assumption | exact Or.inl hQc)

theorem continuedCompensatedLocal_first_differentiable_w (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm) (x z : ℂ)
    (hx : (1/2:ℝ)≤ x.re) (hz : (1/3:ℝ)≤ z.re) :
    Differentiable ℂ (fun w=> continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) := by
  have hQ0 : (0:ℝ)< P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := continuedMarkedLocal_first_differentiable_w η u P hs hQ x z hx hz
  have hW := coordW_differentiable (P.val.absNorm:ℝ) hQ0 (idealRowHom u.val P.val)
  have hq : Differentiable ℂ (fun w:ℂ=>(P.val.absNorm:ℂ)^(-w)) :=
    differentiable_id.neg.const_cpow (Or.inl hQc)
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop

theorem continuedCompensatedLocal_first_differentiableAt_z (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm) (x w z : ℂ)
    (hx : (1/2:ℝ)≤ x.re) (hz : (1/3:ℝ)< z.re) :
    DifferentiableAt ℂ (fun z=> continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) z := by
  have hQ0 : (0:ℝ)< P.val.absNorm := by linarith
  have hM := (continuedMarkedLocal_first_analyticAt_z η u P hs hQ x w z hx hz).differentiableAt
  have hV := coordV_differentiable (P.val.absNorm:ℝ) hQ0
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily ProbePhysical
local notation "O" => Eisenstein.O

theorem correctionTail_mono {S T : Finset (Ideal O)} (hS : CorrectionTail S) (hst : S⊆T) :
    CorrectionTail T := by
  let inc : {P : HeckeIdealSeries.PrimeIdeal // P.val∉T}→{P : HeckeIdealSeries.PrimeIdeal // P.val∉S} :=
    fun P=>⟨P.val,fun h=> P.property (hst h)⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun R : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S}=> R.val) h)
  constructor
  · intro P hP
    exact hS.norm_four P (fun h=> hP (hst h))
  · apply le_trans _ hS.small
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=> globalPrimeDefectBound_nonneg P.val)
      (fun _=> le_rfl) (globalPrimeDefectBound_summable.subtype _) hS.summable

theorem firstTail_mono {eps : ℝ} {S T : Finset (Ideal O)} (hS : FirstTail eps S) (hst : S⊆T) :
    FirstTail eps T := by
  let inc : {P : HeckeIdealSeries.PrimeIdeal // P.val∉T}→{P : HeckeIdealSeries.PrimeIdeal // P.val∉S} :=
    fun P=>⟨P.val,fun h=> P.property (hst h)⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun R : {P : HeckeIdealSeries.PrimeIdeal // P.val∉S}=> R.val) h)
  refine ⟨hS.positive,?_,?_⟩
  · intro P hP
    exact hS.norm_four P (fun h=> hP (hst h))
  · apply le_trans _ hS.small
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=> firstPrimeDefectBound_nonneg eps P.val)
      (fun _=> le_rfl) ((firstPrimeDefectBound_summable eps hS.positive).subtype _) hS.summable

theorem markedSourceExclusions (S : Finset (Ideal O)) (hS : SourceExclusions S) (T : Finset HeckeIdealSeries.PrimeIdeal) :
    SourceExclusions (markExclusions S T) := {
  prime := markExclusions_prime S hS.prime T
  bad := hS.bad.trans Finset.subset_union_left
  tail := correctionTail_mono hS.tail Finset.subset_union_left }

theorem marked_firstTail (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S) (T : Finset HeckeIdealSeries.PrimeIdeal) :
    FirstTail eps (markExclusions S T) := firstTail_mono hS Finset.subset_union_left

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

/-- Continued row as global L-factors times unselected and selected local corrections. -/
def continuedCompensatedRow (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (B q : HeckeIdealSeries.PrimeIdeal→ℂ) : ℂ :=
  (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeOrigin.continued (rowCharacter S hS.prime u) w*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
  (continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
    ∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z (B P.val) (q P.val))

theorem continuedCompensatedRow_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (B q : HeckeIdealSeries.PrimeIdeal→ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    continuedCompensatedRow S hS T hT η u x w z B q=spectralCompensatedRow S T η u.val x w z B q := by
  have hx0 : x≠0 := by intro h; simp only [h,Complex.zero_re] at hx;linarith
  have hx1 : x≠1 := by intro h; simp only [h,Complex.one_re] at hx;linarith
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw;linarith
  have hw1 : w≠1 := by intro h; simp only [h,Complex.one_re] at hw;linarith
  unfold continuedCompensatedRow
  rw [HeckeOrigin.continued_eq _ hw0 hw1,HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,
    continuedCorrection_eq_initial (markExclusions S T) (markedSourceExclusions S hS T) η u x w z hx hw hz]
  simp_rw [continuedCompensatedLocal_eq_initial η u _ _ x w z _ _ hx hw hz]
  rw [Finset.prod_attach T (fun P=> compensatedLocalCorrection η u P x w z (B P) (q P)),spectralCompensatedRow_original_L_factorization S hS.prime hS.bad T hT η u x w z B q hx hw hz,
    div_eq_mul_inv]

theorem continuedCompensatedRow_eq_indexed {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    let hT : ∀Q∈Finset.univ.image P,Q.val∉S := by
      intro Q hQ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
      exact hPS i
    continuedCompensatedRow S hS (Finset.univ.image P) hT η u x w z
      (fun Q=> star (idealCoeff η Q.val)*(Q.val.absNorm:ℂ)^x)
      (fun Q=>(Q.val.absNorm:ℂ)^(-w))=
      indexedCompensatedHigh η S (fun i=> primaryIdealGenerator (P i).val) u.val x w z := by
  dsimp only
  rw [continuedCompensatedRow_eq_initial _ _ _ _ _ _ _ _ _ _ _ hx hw hz,
    indexedCompensatedHigh_eq_spectral η S P hP
      (fun i=> outside_prime_supported S hS.bad (P i) (hPS i)) u.val x w z]

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

def physicalCompensatedRow (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) : ℂ :=
  continuedCompensatedRow S hS T hT η u x w z
    (fun P=> star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x)
    (fun P=>(P.val.absNorm:ℂ)^(-w))

theorem physicalCompensatedRow_first_differentiableAt_x (eps : ℝ) (heps : 0< eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (7/8:ℝ)< x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re) (hbeta : HeckeZeroSupremum.beta< x.re) :
    DifferentiableAt ℂ (fun x=> physicalCompensatedRow S hS T hT η u x w z) x := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (HeckeReciprocal.reciprocal_differentiableAt _ hbeta).const_mul _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_x eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        (by linarith) hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_differentiableAt_x η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z hx (by linarith)

theorem physicalCompensatedRow_first_differentiableAt_w (eps : ℝ) (heps : 0< eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (7/8:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re) (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=> physicalCompensatedRow S hS T hT η u x w z) w := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact ((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_w eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        (by linarith) hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact (continuedCompensatedLocal_differentiable_w η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x z hx (by linarith)) w

theorem physicalCompensatedRow_first_differentiableAt_z (eps : ℝ) (heps : 0< eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (7/8:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re) :
    DifferentiableAt ℂ (fun z=> physicalCompensatedRow S hS T hT η u x w z) z := by
  have hz0 : 6*z≠0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.mul_re] at hh
    linarith
  have hz1 : 6*z≠1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.mul_re] at hh
    linarith
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) hz0 (Or.inl hz1)).comp z
      (differentiableAt_id.const_mul 6)).mul_const _).mul_const _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_z eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        (by linarith) hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_differentiableAt_z η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z hx (by linarith)

theorem unselectedCorrection_subpower (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0< C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (T : Finset HeckeIdealSeries.PrimeIdeal) (η : Character) (u : FreeRow) (x w z : ℂ),
      (7/8:ℝ)≤ x.re → (19/20:ℝ)≤ w.re → (33/200:ℝ)≤ z.re →
      ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ := by
  obtain ⟨C,hC,hbound⟩ := continuedCorrection_subpower δ hδ
  exact ⟨C,hC,fun S hS T η u x w z hx hw hz=>
    hbound (markExclusions S T) (markedSourceExclusions S hS T) η u x w z hx hw hz⟩

theorem unselectedCorrection_first_subpower (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0< C ∧ ∀ (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (T : Finset HeckeIdealSeries.PrimeIdeal) (η : Character) (u : FreeRow) (x w z : ℂ),
      (51/100:ℝ)≤ x.re → -(1/100:ℝ)≤ w.re → (17/50:ℝ)≤ z.re → 1+eps≤ x.re+w.re →
      ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ := by
  obtain ⟨C,hC,hbound⟩ := continuedCorrection_first_subpower δ hδ
  exact ⟨C,hC,fun eps S hS hfirst T η u x w z hx hw hz hxw=>
    hbound eps (markExclusions S T) (markedSourceExclusions S hS T) (marked_firstTail eps S hfirst T)
      η u x w z hx hw hz hxw⟩

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem physicalCompensatedRow_indexed {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    let hT : ∀Q∈Finset.univ.image P,Q.val∉S := by
      intro Q hQ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
      exact hPS i
    physicalCompensatedRow S hS (Finset.univ.image P) hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,continuedCompensatedLocal η u (P i)
          (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
          (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
          (((P i).val.absNorm:ℂ)^(-w))) := by
  dsimp only
  unfold physicalCompensatedRow continuedCompensatedRow
  congr 2
  symm
  apply Finset.prod_bij (fun i _=>⟨P i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  · intro i _; exact Finset.mem_attach _ _
  · intro i _ j _ h; exact hP (congrArg Subtype.val h)
  · intro Q _
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp Q.property
    exact ⟨i,hi,Subtype.ext he⟩
  · intro i _; rfl

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem tupleOutside {K : ℕ} (S : Finset (Ideal O)) (P : Fin K→HeckeIdealSeries.PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) : ∀Q∈Finset.univ.image P,Q.val∉S := by
  intro Q hQ
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
  exact hPS i

def calibratedTupleValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℂ :=
  star ((calibrationForSet S hmax).residueMonoid u.val)*
  (∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1))*
  physicalCompensatedRow S hS (Finset.univ.image P) (tupleOutside S P hPS) η u x w z

theorem calibratedTupleValue_factor {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    calibratedTupleValue S hS hmax η u P hPS W Y x w z=
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
          HeckeOrigin.continued (rowCharacter S hS.prime u) w*
          HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x))*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1)*
          continuedCompensatedLocal η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
            (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
            (((P i).val.absNorm:ℂ)^(-w))) := by
  unfold calibratedTupleValue
  rw [physicalCompensatedRow_indexed S hS P hP hPS]
  simp only [Finset.prod_mul_distrib]
  ring

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalRowCompletion
open CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "O" => Eisenstein.O

lemma rawRow_elementCoeff (u : FreeRow) (n : O) :
    elementCoeff (rawRow u) n = rowTwist (HeckeRowClosure.elementHom
      (fixedSourcePrincipal ∅ (by simp))) rowMaskElement 1 u.val n :=
  (Classical.choose_spec (HeckeRowClosure.exists_row_character_with_conductor
    (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
    rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2 n

lemma rowCharacter_principal_iff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) :
    (rowCharacter S hS u).residue=1 ↔ (rawRow u).residue=1 :=
  HeckeFiniteDeletion.principal_iff_of_mask _ _ (excludePrimes_mask (rawRow u) S hS)

lemma supported_coprime_row_fixed (r : O) (hr : Supported (Ideal.span {r})) :
    IsCoprime (Ideal.span {r})
      ((fixedSourcePrincipal ∅ (by simp)).modulus*Ideal.span {rowMaskElement}*
        Ideal.span {(72:O)}) := by
  have hl : IsCoprime lambda r :=
    residue_lambda_prime.irreducible.coprime_iff_not_dvd.mpr
      ((CanonicalQuadraticSieve.supported_span_iff r).mp hr).1
  have hn : IsCoprime (-2:O) r := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((CanonicalQuadraticSieve.supported_span_iff r).mp hr).2)
  have h2 : IsCoprime (2:O) r := hn.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  have h9 : IsCoprime (9:O) r := CanonicalRowCompletion.nine_coprime_of_not_lambda_dvd r
    ((CanonicalQuadraticSieve.supported_span_iff r).mp hr).1
  have h72 : IsCoprime (72:O) r := by
    convert (h2.pow_left (m:=3)).mul_left h9 using 1; norm_num
  have hm := (h2.mul_left hl).symm
  have hmod : (fixedSourcePrincipal ∅ (by simp)).modulus=(1:Ideal O) := by
    simp [fixedSourcePrincipal,HeckeRayFamily.character,Character.ofResidue]
  rw [hmod,one_mul]
  exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr hm).mul_right
    ((Ideal.isCoprime_span_singleton_iff _ _).mpr h72.symm)

theorem rawRow_principal_supported_isUnit (u : FreeRow)
    (hu : Supported (Ideal.span {u.val})) (hp : (rawRow u).residue=1) : IsUnit u.val := by
  obtain ⟨v,hv⟩ := exists_supported_primary_unit u.val ((CanonicalQuadraticSieve.supported_iff_native _).mp hu)
  let r : O := (v:O)*u.val
  have hspan : (Ideal.span {r}:Ideal O)=Ideal.span {u.val} :=
    Ideal.span_singleton_mul_left_unit v.isUnit u.val
  have hr : Supported (Ideal.span {r}) := hspan.symm ▸ hu
  have hx : (1:O)^4*u.val=(v⁻¹:Oˣ).val*lambda^0*(2:O)^0*r := by
    simp [r]
  have hempty : normalizedFactors (Ideal.span {r})=0 := by
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro P hP
    have hcop : IsCoprime
        ((fixedSourcePrincipal ∅ (by simp)).modulus*Ideal.span {rowMaskElement}*Ideal.span {(72:O)}) P :=
      (supported_coprime_row_fixed r hr).symm.of_isCoprime_of_dvd_right (dvd_of_mem_normalizedFactors hP)
    have hd := HeckeRowNonprincipal.principal_row_multiplicity
      (fixedSourcePrincipal ∅ (by simp)) (rawRow u) rowMaskElement 1 u.val
      (dvd_mul_left _ _) (dvd_mul_right _ _) v⁻¹ 0 0 r hr hv hx (rawRow_elementCoeff u) hp P hP hcop
    have hlt : (normalizedFactors (Ideal.span {r})).count P<6 := by
      rw [hspan]
      exact u.property.2 P
    exact Nat.not_dvd_of_pos_of_lt (Multiset.count_pos.mpr hP) hlt hd
  have hone : (Ideal.span {u.val}:Ideal O)=1 := by
    rw [←hspan,←Ideal.prod_normalizedFactors_eq_self hr.1,hempty,Multiset.prod_zero]
  exact Ideal.span_singleton_eq_top.mp (by simpa only [Ideal.one_eq_top] using hone)

lemma idealCoeff_principal_eq_one (χ : Character) (hχ : χ.residue=1)
    (I : Ideal O) (hI : idealCoeff χ I≠0) : idealCoeff χ I=1 := by
  change IdealCharacter.value χ.modulus χ.residue I=1
  change IdealCharacter.value χ.modulus χ.residue I≠0 at hI
  unfold IdealCharacter.value at *
  split_ifs at * with hzero
  · exact False.elim (hI rfl)
  · have hu := MulChar.apply_ne_zero_iff.mp hI
    rw [hχ,MulChar.one_apply hu]

theorem rowCharacter_unit_nonprincipal (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (u : FreeRow)
    (v : Oˣ) (hu : u.val=(v:O)) (hv : v≠1) :
    (rowCharacter S hS u).residue≠1 := by
  -- Finite deletion preserves nonprincipality; the raw unit row is detected at norm seven.
  let Q : HeckeIdealSeries.PrimeIdeal := ⟨sevenIdeal, Ideal.prime_of_isPrime
    (Ideal.span_singleton_eq_bot.not.mpr sevenPrime_ne_zero) inferInstance⟩
  have hc : IsCoprime sevenIdeal (Ideal.span {rowMaskElement}) :=
    (supported_coprime_row_fixed sevenPrime
      ((CanonicalQuadraticSieve.supported_iff_native _).mpr HeckeUnitRows.seven_supported)).of_isCoprime_of_dvd_right
        ⟨(fixedSourcePrincipal ∅ (by simp)).modulus * Ideal.span {(72 : O)}, by ring⟩
  have he : idealCoeff (rawRow u) sevenIdeal = ringComplex (v : O) := by
    rw [rawRow_coeff, fixedSourcePrincipal_prime ∅ (by simp) Q,
      if_neg (by simp), one_mul, hu, idealRowHom_argument_mul,
      idealRowHom_sixth_mask rowMaskElement sevenIdeal HeckeUnitRows.seven_supported,
      if_pos hc, one_mul, idealRowHom_unit_norm v sevenIdeal HeckeUnitRows.seven_supported,
      sevenIdeal_norm]
    norm_num
  intro hp
  have hrp := (rowCharacter_principal_iff S hS u).mp hp
  have hn : idealCoeff (rawRow u) sevenIdeal ≠ 0 :=
    he ▸ (v.isUnit.map ringComplex).ne_zero
  have hval := he.symm.trans (idealCoeff_principal_eq_one _ hrp _ hn)
  apply hv
  apply Units.ext
  apply ringComplex_injective
  simpa only [Units.val_one, map_one] using hval


theorem rowCharacter_principal_supported_eq_one (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (u : FreeRow)
    (hu : Supported (Ideal.span {u.val})) (hp : (rowCharacter S hS u).residue=1) : u.val=1 := by
  obtain ⟨v,hv⟩ := rawRow_principal_supported_isUnit u hu ((rowCharacter_principal_iff S hS u).mp hp)
  by_contra hn
  have hv1 : v≠1 := by
    intro he
    subst v
    exact hn hv.symm
  exact rowCharacter_unit_nonprincipal S hS hbad u v hv.symm hv1 hp

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

lemma calibration_nonzero_supported (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (a : O)
    (ha : (calibrationForSet S hS).residueMonoid a≠0) : Supported (Ideal.span {a}) := by
  have hu := (calibrationForSet S hS).residue.apply_ne_zero_iff.mp ha
  have hc := (CubicEisenstein.isUnit_quotient_span_iff _ _).mp hu
  have havoid := (calibrationForSet_coprime_iff S hS a).mp hc
  rw [CanonicalQuadraticSieve.supported_span_iff]
  constructor
  · intro hd
    exact havoid (Ideal.span {lambda}) (hbad (Finset.mem_insert_self _ _))
      (Ideal.mem_span_singleton.mpr hd)
  · intro hd
    exact havoid (Ideal.span {(2:O)}) (hbad (by simp [CanonicalRowCompletion.fixedBadPrimes, ramifiedIdeal, cubicTwoIdeal, Ideal.span_singleton_neg]))
      (Ideal.mem_span_singleton.mpr hd)

theorem calibrated_row_nonprincipal (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hmax : ∀P∈S,P.IsMaximal) (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S)
    (u : FreeRow) (hu : u.val≠1)
    (hcal : (calibrationForSet S hmax).residueMonoid u.val≠0) :
    (rowCharacter S hS u).residue≠1 := fun hp=> hu
      (rowCharacter_principal_supported_eq_one S hS hbad u
        (calibration_nonzero_supported S hmax hbad u.val hcal) hp)

theorem principal_calibration_vanish (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hmax : ∀P∈S,P.IsMaximal) (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S)
    (u : FreeRow) (hu : u.val≠1) (hp : (rowCharacter S hS u).residue=1) :
    (calibrationForSet S hmax).residueMonoid u.val=0 := by
  by_contra hn
  exact calibrated_row_nonprincipal S hS hmax hbad u hu hn hp

theorem calibrated_numerator_differentiable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hmax : ∀P∈S,P.IsMaximal) (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S)
    (u : FreeRow) (hu : u.val≠1) :
    Differentiable ℂ (fun w=> star ((calibrationForSet S hmax).residueMonoid u.val)*
      HeckeOrigin.continued (rowCharacter S hS u) w) := by
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul]
    exact differentiable_const _
  · intro w
    exact (HeckeOrigin.continued_differentiableAt _
      (Or.inr (calibrated_row_nonprincipal S hS hmax hbad u hu hc))).const_mul _

theorem calibrated_physicalRow_first_differentiableAt_w (eps : ℝ) (heps : 0< eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x w z : ℂ)
    (hx : (7/8:ℝ)≤ x.re) (hw : -(1/100:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+w.re) :
    DifferentiableAt ℂ (fun w=> star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z) w := by
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul]
    exact differentiableAt_const _
  · exact (physicalCompensatedRow_first_differentiableAt_w eps heps S hS hfirst T hT η u
      x w z hx hw hz hxw (Or.inr
        (calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc))).const_mul _

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
local notation "O" => Eisenstein.O

lemma continuedCompensatedLocal_ramified_bound (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤ P.val.absNorm)
    (x w z : ℂ) (hx : (7/8:ℝ)≤ x.re) (hw : (1/2:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤
        385*(P.val.absNorm:ℝ)^(max (1-w.re) 0) := by
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  rw [continuedCompensatedLocal_ramified η u P hs hP x w z]
  have hb := ramifiedSelected_bound p hp hg.1 hg.2 _ _ _ x w z
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) ha
    (complexSexticChar_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)) hx hw hz
    (multiplicity p u.val) (multiplicity_lt_six u p hp)
  simpa only [hspan] using hb

lemma continuedCompensatedLocal_unramified_bound (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hP : ¬P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤ P.val.absNorm)
    (x w z : ℂ) (hx : (7/8:ℝ)≤ x.re) (hw : (1/2:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤961 := by
  let p := primaryIdealGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := CenteredMomentSourceRow.primary_span_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp ((CanonicalQuadraticSieve.supported_iff_native _).mp hsp)
  have hnot : ¬p∣u.val := by
    intro hd
    apply hP
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hu : IsCoprime u.val p := (hp.irreducible.coprime_iff_not_dvd.mpr hnot).symm
  have hQ0 : (0:ℝ)< P.val.absNorm := by linarith
  have hV : ‖coordV P.val.absNorm z‖<1 := by
    exact (first_region_V_half _ hQ z hz).trans_lt (by norm_num)
  have hR : ‖coordR P.val.absNorm (actualAPhase η p) x z‖<1 := by
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact (rpow_le_half _ _ hQ (by linarith)).trans_lt (by norm_num)
  rw [continuedCompensatedLocal_unramified η u P hs hP x w z hV hR]
  have hb := actualUnramifiedSelected_bound η p u.val hg.1 hg.2 hu (hspan.symm ▸ hQ) x w z hx hw hz
  have he : idealCoeff η P.val=elementCoeff η p := by rw [←hspan,idealCoeff_span η hp.ne_zero]
  have hv : idealRowHom u.val P.val=complexSexticChar (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    rw [←hspan,idealRowHom_prime u.val (Ideal.span {p}) hg.1]
  simpa only [actualUnramifiedSelected,hspan,he,hv] using hb

lemma continuedCompensatedLocal_bound (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm)
    (x w z : ℂ) (hx : (7/8:ℝ)≤ x.re) (hw : (1/2:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤
        961*(if P.val∣Ideal.span {u.val} then (P.val.absNorm:ℝ)^(max (1-w.re) 0) else 1) := by
  by_cases hp : P.val∣Ideal.span {u.val}
  · rw [if_pos hp]
    apply (continuedCompensatedLocal_ramified_bound η u P hs hp hQ x w z hx hw hz).trans
    gcongr
    norm_num
  · simpa only [if_neg hp,mul_one] using continuedCompensatedLocal_unramified_bound η u P hs hp hQ x w z hx hw hz

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion

lemma compensatedReplacement_crude (V W D M B q : ℂ) (A E : ℝ)
    (hA : 0≤ A) (hE : 0≤ E) (hV : ‖V‖≤1) (hW : ‖W‖≤ A)
    (hD : ‖D‖≤1/2) (hM : ‖M‖≤388) (hB : ‖B‖≤ E) (hq : ‖q‖≤ A) :
    ‖ProbeLocal.compensatedReplacement V W D M B q‖≤
      2*((E+A)*2*(1+A)*388+A*(1+A)) := by
  have h1V : ‖1-V‖≤2 := by have h := norm_sub_le (1:ℂ) V;rw [norm_one] at h;linarith
  have h1W : ‖1-W‖≤1+A := by have h := norm_sub_le (1:ℂ) W;rw [norm_one] at h;linarith
  have h1VW : ‖1-V*W‖≤1+A := by
    apply (norm_sub_le (1:ℂ) (V*W)).trans
    rw [norm_one,norm_mul]
    have hm := (mul_le_mul hV hW (norm_nonneg _) (by norm_num)).trans_eq (one_mul A)
    linarith
  have hi := ProbeLocal.inv_one_sub_norm_le_two D hD
  unfold ProbeLocal.compensatedReplacement
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ ((‖B-q‖*‖1-V‖*‖1-W‖*‖M‖)+‖q‖*‖1-V*W‖)*2 := by
      apply mul_le_mul _ hi (norm_nonneg _) (by positivity)
      simpa only [norm_mul] using norm_sub_le ((B-q)*(1-V)*(1-W)*M) (q*(1-V*W))
    _ ≤ ((E+A)*2*(1+A)*388+A*(1+A))*2 := by
      have hbq : ‖B-q‖≤ E+A := (norm_sub_le B q).trans (add_le_add hB hq)
      gcongr
    _ = _ := by ring

def selectedFirstBound (Q R : ℝ) : ℝ :=
  2*((Q^R+Q^(1/100:ℝ))*2*(1+Q^(1/100:ℝ))*388+Q^(1/100:ℝ)*(1+Q^(1/100:ℝ)))

lemma selectedFirstBound_nonneg (Q R : ℝ) (hQ : 0≤ Q) : 0≤ selectedFirstBound Q R := by
  unfold selectedFirstBound
  positivity

theorem continuedCompensatedLocal_first_bound (η : Character) (u : FreeRow) (P : HeckeIdealSeries.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤ P.val.absNorm) (R : ℝ) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hxR : x.re≤ R) (hw : -(1/100:ℝ)≤ w.re)
    (hz : (17/50:ℝ)≤ z.re) (hxw : 1≤ x.re+w.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤
        selectedFirstBound P.val.absNorm R := by
  have hQ0 : (0:ℝ)< P.val.absNorm := by linarith
  have hQ1 : (1:ℝ)≤ P.val.absNorm := by linarith
  have hV := first_region_V_half _ hQ z hz
  have hD : ‖coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x‖≤1/2 :=
    (coordD_norm_le _ hQ0 _ _ x (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _)).trans
      (rpow_le_half _ _ hQ (by linarith))
  have hM : ‖continuedMarkedLocal η u P hs x w z‖≤388 := by
    rw [continuedMarkedLocal_eq_quotient η u P hs x w z
      (ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV),div_eq_mul_inv,norm_mul]
    have hH := ramifiedCorrection_first_bound η u P hs hQ x w z hx hw hz hxw
    have hn : ‖ramifiedCorrection η u P hs x w z-1‖≤194 := by
      have h := norm_sub_le (ramifiedCorrection η u P hs x w z) (1:ℂ)
      rw [norm_one] at h
      linarith
    exact (mul_le_mul hn (ProbeLocal.inv_one_sub_norm_le_two _ hV) (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have hW : ‖coordW P.val.absNorm (idealRowHom u.val P.val) w‖≤(P.val.absNorm:ℝ)^(1/100:ℝ) :=
    (coordW_norm_le _ hQ0 _ w (idealRowHom_norm u.val _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hq : ‖(P.val.absNorm:ℂ)^(-w)‖≤(P.val.absNorm:ℝ)^(1/100:ℝ) := by
    rw [show (P.val.absNorm:ℂ)=((P.val.absNorm:ℝ):ℂ) from by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hB : ‖star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x‖≤(P.val.absNorm:ℝ)^R := by
    rw [norm_mul,norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)).trans
    rw [show (P.val.absNorm:ℂ)=((P.val.absNorm:ℝ):ℂ) from by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 hxR
  exact compensatedReplacement_crude _ _ _ _ _ _ _ _ (by positivity) (by positivity)
    (hV.trans (by norm_num)) hW hD hM hB hq

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
local notation "O" => Eisenstein.O

theorem continued_selected_slot_bound (eps a b r B : ℝ) (heps : 0< eps)
    (ha : 0< a) (hb : 0< b) (hr : (17/50:ℝ)≤ r) (hB : 0≤ B) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (u : FreeRow) (T : Finset HeckeIdealSeries.PrimeIdeal)
      (hT : ∀P∈T,Supported P.val ∧ (4:ℝ)≤ P.val.absNorm)
      (Y : ℝ),1≤ Y → ∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b →
      (∀y,‖W y‖≤ B) → ∀(x w z : ℂ),(7/8:ℝ)≤ x.re → (1/2:ℝ)≤ w.re → z.re=r →
      (∑P : T,‖W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*
        continuedCompensatedLocal η u P.val (hT P.val P.property).1 x w z
          (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))‖)
      ≤ C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*Y^r := by
  obtain ⟨C,hC,hmain⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed eps a b r (1/2) B 961
    heps ha hb (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro η u T hT Y hY W hWS hWB x w z hx hw hz
  let f : T→Ideal O := fun P=> P.val.val
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    exact Subtype.ext h
  let G : T→ℂ := fun P=> continuedCompensatedLocal η u P.val (hT P.val P.property).1 x w z
    (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))
  have hg (P : T) (_ : P∈Finset.univ) : ‖G P‖≤
      961*(if f P∣Ideal.span {u.val} then (Ideal.absNorm (f P):ℝ)^(1/2:ℝ) else 1) := by
    have hh := continuedCompensatedLocal_bound η u P.val (hT P.val P.property).1
      (hT P.val P.property).2 x w z hx hw (by rw [hz];exact hr)
    apply hh.trans
    by_cases hp : f P∣Ideal.span {u.val}
    · simp only [show P.val.val=f P from rfl,if_pos hp]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by have := (hT P.val P.property).2;change 1≤(P.val.val.absNorm:ℝ);linarith)
        (max_le (by linarith) (by norm_num))
    · simp only [show P.val.val=f P from rfl,if_neg hp,le_refl]
  exact hmain f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _=> P.val.property.ne_zero) W hWS hWB G hg z hz

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
local notation "O" => Eisenstein.O

theorem continued_selected_tuple_bound (K : ℕ) (eps a b r B : ℝ) (heps : 0< eps)
    (ha : 0< a) (hb : 0< b) (hr : (17/50:ℝ)≤ r) (hB : 0≤ B) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (u : FreeRow) (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal)
      (hT : ∀i P,P∈T i→Supported P.val ∧ (4:ℝ)≤ P.val.absNorm)
      (Y : Fin K→ℝ), (∀i,1≤ Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤ B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤ x.re → (1/2:ℝ)≤ w.re → z.re=r →
      (∑P : (∀i, T i),‖∏i,
        W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
        continuedCompensatedLocal η u (P i).val (hT i (P i).val (P i).property).1 x w z
          (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
          (((P i).val.val.absNorm:ℂ)^(-w))‖)
      ≤ C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏i,(Y i)^r := by
  let d : ℝ := eps/((K:ℝ)+1)
  have hd : 0< d := div_pos heps (by positivity)
  obtain ⟨C,hC,hmain⟩ := continued_selected_slot_bound d a b r B hd ha hb hr hB
  refine ⟨C ^ K,pow_pos hC K,?_⟩
  intro η u T hT Y hY W hWS hWB x w z hx hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 1≤ N := by
    dsimp [N]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hdK : d*(K:ℝ)≤ eps := by
    dsimp [d]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : (0:ℝ)<(K:ℝ)+1)]
    nlinarith
  have hpow : (N^d)^K≤ N^eps := by
    rw [←Real.rpow_mul_natCast (by linarith : 0≤ N)]
    exact Real.rpow_le_rpow_of_exponent_le hN hdK
  let F : ∀i:Fin K,T i→ℂ := fun i P=>
    W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
      continuedCompensatedLocal η u P.val (hT i P.val P.property).1 x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))
  change (∑P:(∀i,T i),‖∏i,F i (P i)‖)≤ C ^ K*N^eps*∏i,(Y i)^r
  simp_rw [norm_prod]
  rw [←Fintype.prod_sum (fun i P=>‖F i P‖)]
  calc
    _ ≤ ∏i:Fin K, (C*N^d*(Y i)^r) := by
      apply Finset.prod_le_prod
      · intro i _; exact Finset.sum_nonneg fun _ _=> norm_nonneg _
      · intro i _; exact hmain η u (T i) (hT i) (Y i) (hY i) (W i) (hWS i) (hWB i) x w z hx hw hz
    _ = C ^ K*(N^d)^K*∏i:Fin K,(Y i)^r := by
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    _ ≤ C ^ K*N^eps*∏i:Fin K,(Y i)^r := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
        (Finset.prod_nonneg fun i _=> Real.rpow_nonneg (by linarith [hY i]) _)

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

theorem continued_selected_tuple_with_correction (K : ℕ) (δ a b r B : ℝ)
    (hδ : 0<δ) (ha : 0< a) (hb : 0< b) (hr : (17/50:ℝ)≤ r) (hB : 0≤ B) :
    ∃C : ℝ,0< C ∧ ∀(eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (η : Character) (u : FreeRow)
      (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal)
      (hT : ∀i P,P∈T i→Supported P.val ∧ (4:ℝ)≤ P.val.absNorm)
      (Y : Fin K→ℝ), (∀i,1≤ Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤ B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤ x.re → (1/2:ℝ)≤ w.re → z.re=r →
      1+eps≤ x.re+w.re →
      (∑P : (∀i,T i),‖continuedCorrection
        (markExclusions S (Finset.univ.image (fun i=>(P i).val)))
        (markedSourceExclusions S hS (Finset.univ.image (fun i=>(P i).val))) η u x w z*
        ∏i,W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
          continuedCompensatedLocal η u (P i).val (hT i (P i).val (P i).property).1 x w z
            (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
            (((P i).val.val.absNorm:ℂ)^(-w))‖)
      ≤ C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ*∏i,(Y i)^r := by
  obtain ⟨C₁,hC₁,hmain⟩ := continued_selected_tuple_bound K (δ/2) a b r B (by linarith) ha hb hr hB
  obtain ⟨C₂,hC₂,hcorr⟩ := unselectedCorrection_first_subpower (δ/2) (by linarith)
  refine ⟨C₂*C₁,mul_pos hC₂ hC₁,?_⟩
  intro eps S hS hfirst η u T hT Y hY W hWS hWB x w z hx hw hz hxw
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 0< N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  let F : (∀i,T i)→ℂ := fun P=>∏i,
    W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
      continuedCompensatedLocal η u (P i).val (hT i (P i).val (P i).property).1 x w z
        (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
        (((P i).val.val.absNorm:ℂ)^(-w))
  calc
    _ ≤ ∑P:(∀i,T i),(C₂*N^(δ/2))*‖F P‖ := by
      apply Finset.sum_le_sum
      intro P _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hcorr eps S hS hfirst (Finset.univ.image (fun i=>(P i).val)) η u x w z
          (by linarith) (by linarith) (by rw [hz];exact hr) hxw) (norm_nonneg _)
    _ = (C₂*N^(δ/2))*∑P:(∀i,T i),‖F P‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ (C₂*N^(δ/2))*(C₁*N^(δ/2)*∏i,(Y i)^r) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hmain η u T hT Y hY W hWS hWB x w z hx hw hz
    _ = (C₂*C₁)*N^δ*∏i,(Y i)^r := by
      have hp : N^(δ/2)*N^(δ/2)=N^δ := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = (C₂*C₁)*(N^(δ/2)*N^(δ/2))*∏i,(Y i)^r := by ring
        _ = _ := by rw [hp]

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem nonprincipal_positive_growth (σ δ : ℝ) (hσ : 0<σ) (hδ : 0<δ) :
    ∃C : ℝ,0< C ∧ ∀χ : Character,χ.residue≠1 → ∀s : ℂ,σ≤ s.re →
      ‖HeckeOrigin.continued χ s‖≤ C*(χ.modulus.absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hdel⟩ := HeckeDeletionBounds.factors_subpower_bound σ δ hσ hδ
  refine ⟨(1+HeckeLogarithmicInput.uniformConstant)*Cd,
    mul_pos (by linarith [HeckeLogarithmicInput.uniformConstant_nonneg]) hCd,?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h=> hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10:ℝ)≤ s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hg
  have hd : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤ Cd*(χ.modulus.absNorm:ℝ)^δ :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hdel χ.modulus χ.modulus_ne_bot ψ s hs)
  have hQ' : (ψ.modulus.absNorm:ℝ)^(3/5:ℝ)≤(χ.modulus.absNorm:ℝ)^(3/5:ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by norm_num)
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  have hN : (0:ℝ)<χ.modulus.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  rw [HeckeOrigin.continued,if_neg hχ,
    HeckeFiniteDeletion.LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ (by linarith),norm_mul]
  calc
    _ ≤ (HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*(χ.modulus.absNorm:ℝ)^δ) := mul_le_mul hg hd (norm_nonneg _) (by positivity)
    _ ≤ ((1+HeckeLogarithmicInput.uniformConstant)*(χ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*(χ.modulus.absNorm:ℝ)^δ) := by gcongr;linarith
    _ = _ := by rw [Real.rpow_add hN];ring

theorem calibrated_numerator_positive_growth (σ δ : ℝ) (hσ : 0<σ) (hδ : 0<δ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0< C ∧ ∀(u : FreeRow),u.val≠1 → ∀s : ℂ,σ≤ s.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) s‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by
  obtain ⟨C,hC,hmain⟩ := nonprincipal_positive_growth σ δ hσ hδ
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤ A := by dsimp [A];positivity
  refine ⟨C*(1+A^(3/5+δ)),mul_pos hC (by positivity),?_⟩
  intro u hu s hs
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul,norm_zero]
    positivity
  · have hnp := calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc
    have hg := hmain (rowCharacter S hS.prime u) hnp s hs
    have hcal : ‖star ((calibrationForSet S hmax).residueMonoid u.val)‖≤1 := by
      rw [norm_star]
      exact (calibrationForSet S hmax).residueMonoid_norm_le_one _
    have hQ : ((rowCharacter S hS.prime u).modulus.absNorm:ℝ)≤
        A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
      have h := rowCharacter_conductor S hS.prime u
      dsimp [A]
      exact_mod_cast (by simpa only [mul_right_comm] using h)
    rw [norm_mul]
    calc
      _ ≤ ‖HeckeOrigin.continued (rowCharacter S hS.prime u) s‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hcal
      _ ≤ C*((rowCharacter S hS.prime u).modulus.absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := hg
      _ ≤ C*(A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))^(3/5+δ)*(3+|s.im|)^2 := by
        gcongr
      _ ≤ C*(1+A^(3/5+δ))*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by
        rw [Real.mul_rpow hA (by positivity)]
        calc
          _ = C*A^(3/5+δ)*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by ring
          _ ≤ _ := by gcongr;linarith

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem targetRow_reciprocal_growth (e δ : ℝ) (he : 0< e) (he' : e<1/1000)
    (hδ : 0<δ) (hδ' : δ≤2) (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (u : FreeRow) (x : ℂ),
      HeckeZeroSupremum.beta+8*e≤ x.re →
      ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS) x‖≤
        C*(η.modulus.absNorm:ℝ)^δ*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ*(3+|x.im|)^2 := by
  obtain ⟨D,hD,hmain⟩ := HeckeReciprocalGrowth.reciprocal_subpower e (δ/2) he he' (by linarith)
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤ A := by dsimp [A];positivity
  refine ⟨D*(2:ℝ)^(δ/2)*(1+A^δ),by positivity,?_⟩
  intro η u x hx
  let q : ℝ := η.modulus.absNorm
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hq : 0≤ q := by dsimp [q];positivity
  have hN : 0≤ N := by dsimp [N];positivity
  have hQ : (((targetRow η u).excludePrimes S hS).modulus.absNorm:ℝ)≤ A*q*N := by
    have hh := targetRow_excluded_conductor S hS η u
    dsimp [A,q,N]
    exact_mod_cast (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hh)
  have hc := HeckeDyadic.presentationComplexity_le_of_modulus_le
    ((targetRow η u).excludePrimes S hS) (A*q*N) x.im hQ
  have ht : 0≤3+|x.im| := by positivity
  have hpow : (2*(A*q*N)^2*(3+|x.im|)^2)^(δ/2)=
      (2:ℝ)^(δ/2)*A^δ*q^δ*N^δ*(3+|x.im|)^δ := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity),
      ←Real.rpow_natCast_mul (mul_nonneg (mul_nonneg hA hq) hN),
      ←Real.rpow_natCast_mul ht]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(δ/2)=δ by ring,
      Real.mul_rpow (mul_nonneg hA hq) hN,Real.mul_rpow hA hq]
    ring
  have hbase := hmain ((targetRow η u).excludePrimes S hS) x hx
  calc
    _ ≤ D*(2*(A*q*N)^2*(3+|x.im|)^2)^(δ/2) := by
      apply hbase.trans
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact Real.rpow_le_rpow (by unfold HeckeReciprocalGrowth.presentationComplexity HeckeLogarithmic.complexity;positivity) hc (by linarith)
    _ = D*(2:ℝ)^(δ/2)*A^δ*q^δ*N^δ*(3+|x.im|)^δ := by rw [hpow];ring
    _ ≤ D*(2:ℝ)^(δ/2)*(1+A^δ)*q^δ*N^δ*(3+|x.im|)^2 := by
      have hh : (3+|x.im|)^δ≤(3+|x.im|)^2 := by
        simpa only [Real.rpow_ofNat] using
          (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg x.im] : (1:ℝ)≤3+|x.im|) hδ')
      apply mul_le_mul _ hh (Real.rpow_nonneg ht δ) (by positivity)
      gcongr
      linarith

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem calibrated_scalar_growth (e δ : ℝ) (he : 0< e) (he' : e<1/1000)
    (hδ : 0<δ) (hδ' : δ≤1) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 → ∀(x w z : ℂ),
      HeckeZeroSupremum.beta+8*e≤ x.re → (1/2:ℝ)≤ w.re → (17/50:ℝ)≤ z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
          HeckeOrigin.continued (rowCharacter S hS.prime u) w*
          HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)‖≤
        C*(η.modulus.absNorm:ℝ)^δ*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*
          (3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_positive_growth (1/2) (δ/2) (by norm_num) (by linarith) S hS hmax
  obtain ⟨Cr,hCr,hr⟩ := targetRow_reciprocal_growth e (δ/2) he he' (by linarith) (by linarith) S hS.prime
  let B : ℝ := HeckeReciprocalBound.bound 2
  have hB : 0≤ B := tsum_nonneg (fun _=> norm_nonneg _)
  refine ⟨(1+B)*Cn*Cr,by positivity,?_⟩
  intro η u hu x w z hx hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 0< N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hn' := hn u hu w hw
  have hr' := hr η u x hx
  have hz' : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤1+B := by
    apply (HeckeStripActual.LFunction_norm_le _ (by norm_num : (1:ℝ)<2) (s:=6*z) ?_).trans
    · dsimp [B];linarith
    · norm_num [Complex.mul_re];linarith
  have hη : (η.modulus.absNorm:ℝ)^(δ/2)≤(η.modulus.absNorm:ℝ)^δ :=
    Real.rpow_le_rpow_of_exponent_le (HeckeLogarithmicInput.modulus_norm_ge_one η) (by linarith)
  have he : star ((calibrationForSet S hmax).residueMonoid u.val)*
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)=
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x := by ring
  rw [he,norm_mul,norm_mul]
  calc
    _ ≤ (1+B)*(Cn*N^(3/5+δ/2)*(3+|w.im|)^2)*
        (Cr*(η.modulus.absNorm:ℝ)^(δ/2)*N^(δ/2)*(3+|x.im|)^2) := by
      apply mul_le_mul _ hr' (norm_nonneg _) (by positivity)
      exact mul_le_mul hz' hn' (norm_nonneg _) (by positivity)
    _ ≤ (1+B)*(Cn*N^(3/5+δ/2)*(3+|w.im|)^2)*
        (Cr*(η.modulus.absNorm:ℝ)^δ*N^(δ/2)*(3+|x.im|)^2) := by gcongr
    _ = ((1+B)*Cn*Cr)*(η.modulus.absNorm:ℝ)^δ*N^(3/5+δ)*(3+|x.im|)^2*(3+|w.im|)^2 := by
      have hp : N^(3/5+δ/2)*N^(δ/2)=N^(3/5+δ) := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = ((1+B)*Cn*Cr)*(η.modulus.absNorm:ℝ)^δ*(N^(3/5+δ/2)*N^(δ/2))*(3+|x.im|)^2*(3+|w.im|)^2 := by ring
        _ = _ := by rw [hp]

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

theorem calibrated_physical_tuple_sum (K : ℕ) (e δ a b r B : ℝ)
    (he : 0< e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1)
    (ha : 0< a) (hb : 0< b) (hr : (17/50:ℝ)≤ r) (hB : 0≤ B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀(Y : Fin K→ℝ), (∀i,1≤ Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤ B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤ x.re → HeckeZeroSupremum.beta+8*e≤ x.re →
      (1/2:ℝ)≤ w.re → z.re=r →
      (∑P:(∀i,T i),‖calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
        (fun i=> hT i (P i).val (P i).property) W Y x w z‖)≤
      C*(η.modulus.absNorm:ℝ)^δ*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*
        (∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨CL,hCL,hL⟩ := calibrated_scalar_growth e (δ/2) he he' (by linarith) (by linarith) S hS hmax
  obtain ⟨CG,hCG,hG⟩ := continued_selected_tuple_with_correction K (δ/2) a b r B (by linarith) ha hb hr hB
  refine ⟨CL*CG,mul_pos hCL hCG,?_⟩
  intro η u hu T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 0< N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have ht : ∀i P,P∈T i→CanonicalQuadraticSieve.Supported P.val ∧ (4:ℝ)≤ P.val.absNorm := by
    intro i P hP
    exact ⟨outside_prime_supported S hS.bad P (hT i P hP),by exact_mod_cast hS.tail.norm_four P (hT i P hP)⟩
  let L : ℂ := star ((calibrationForSet S hmax).residueMonoid u.val)*
    (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*HeckeOrigin.continued (rowCharacter S hS.prime u) w*
      HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)
  let G : (∀i,T i)→ℂ := fun P=> continuedCorrection
    (markExclusions S (Finset.univ.image (fun i=>(P i).val)))
    (markedSourceExclusions S hS (Finset.univ.image (fun i=>(P i).val))) η u x w z*
    ∏i,W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
      continuedCompensatedLocal η u (P i).val (ht i (P i).val (P i).property).1 x w z
        (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
        (((P i).val.val.absNorm:ℂ)^(-w))
  have heq (P:∀i,T i) : calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=> hT i (P i).val (P i).property) W Y x w z=L*G P :=
    calibratedTupleValue_factor S hS hmax η u _ (hdis P) _ W Y x w z
  have hLb : ‖L‖≤ CL*(η.modulus.absNorm:ℝ)^(δ/2)*N^(3/5+δ/2)*(3+|x.im|)^2*(3+|w.im|)^2 :=
    hL η u hu x w z hxβ hw (by rw [hz];exact hr)
  have hGb : (∑P:(∀i,T i),‖G P‖)≤ CG*N^(δ/2)*∏i,(Y i)^r :=
    hG (1/4) S hS hfirst η u T ht Y hY W hWS hWB x w z hx hw hz (by linarith)
  have hη : (η.modulus.absNorm:ℝ)^(δ/2)≤(η.modulus.absNorm:ℝ)^δ :=
    Real.rpow_le_rpow_of_exponent_le (HeckeLogarithmicInput.modulus_norm_ge_one η) (by linarith)
  have hYP : 0≤∏i,(Y i)^r := Finset.prod_nonneg fun i _=> Real.rpow_nonneg (by linarith [hY i]) _
  simp_rw [heq,norm_mul]
  rw [←Finset.mul_sum]
  calc
    _ ≤ (CL*(η.modulus.absNorm:ℝ)^(δ/2)*N^(3/5+δ/2)*(3+|x.im|)^2*(3+|w.im|)^2)*
        (CG*N^(δ/2)*∏i,(Y i)^r) :=
      mul_le_mul hLb hGb (Finset.sum_nonneg fun _ _=> norm_nonneg _) (by positivity)
    _ ≤ (CL*(η.modulus.absNorm:ℝ)^δ*N^(3/5+δ/2)*(3+|x.im|)^2*(3+|w.im|)^2)*
        (CG*N^(δ/2)*∏i,(Y i)^r) := by gcongr
    _ = (CL*CG)*(η.modulus.absNorm:ℝ)^δ*N^(3/5+δ)*(∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
      have hp : N^(3/5+δ/2)*N^(δ/2)=N^(3/5+δ) := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = (CL*CG)*(η.modulus.absNorm:ℝ)^δ*(N^(3/5+δ/2)*N^(δ/2))*(∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by ring
        _ = _ := by rw [hp]

end ProbeHighRowFamily
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical  Eisenstein
local notation "O" => Eisenstein.O

lemma freeRow_count (R : Finset FreeRow) (H : ℝ) (hH : 1≤ H)
    (hR : ∀u∈R,((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ H) :
    (R.card:ℝ)≤128*H := by
  have hc := EisensteinLatticeCount.finite_norm_ball_card (R.image Subtype.val) ⌊H⌋₊ (by
    intro a ha
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
    rw [ringComplex_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.le_floor (hR u hu))
  rw [Finset.card_image_of_injective R Subtype.val_injective] at hc
  have hr : (R.card : ℝ) ≤ 64*((⌊H⌋₊ : ℝ)+1) := by exact_mod_cast hc
  have hf : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le (by linarith only [hH])
  linarith only [hr, hf, hH]

lemma frequencyWeight_ideal_norm (z : ℂ) (u : FreeRow) :
    ‖frequencyWeight z ⟨u.val,u.property.1⟩‖=
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(-z.re) := by
  have hN : (0:ℝ)<((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  unfold frequencyWeight elementNorm
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN,Complex.neg_re]

lemma dyadic_weighted_rows (a r C U : ℝ) (hC : 0≤ C) (hU : 1≤ U)
    (R : Finset FreeRow)
    (hR : ∀u∈R,U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U)
    (F : FreeRow→ℝ) (hF : ∀u∈R,F u≤ C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^a)
    (z : ℂ) (hz : z.re=r) :
    (∑u∈R,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u)≤
      256*C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(1+a-r) := by
  have hU0 : 0< U := by linarith
  have hcard : (R.card:ℝ)≤256*U := by
    have hc := freeRow_count R (2*U) (by linarith) (fun u hu=>(hR u hu).2)
    linarith
  have hA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 (a-r) (by norm_num)
  calc
    _ ≤ ∑u∈R,C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r) := by
      apply Finset.sum_le_sum
      intro u hu
      have hN : 0<((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := hU0.trans_le (hR u hu).1
      rw [frequencyWeight_ideal_norm,hz]
      calc
        _ ≤ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(-r)*
            (C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^a) :=
          mul_le_mul_of_nonneg_left (hF u hu) (Real.rpow_nonneg hN.le _)
        _ = C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(a-r) := by
          rw [show a-r=(-r)+a by ring,Real.rpow_add hN]
          ring
        _ ≤ _ := by
          have hb := ProbeSelectedPrimeSums.annular_rpow 1 2 U
            ((Ideal.span {u.val}:Ideal O).absNorm:ℝ) (a-r) (by norm_num) (by norm_num) hU0
            (by simpa only [one_mul] using (hR u hu).1) (hR u hu).2
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC
    _ = (R.card:ℝ)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r)) := by simp
    _ ≤ (256*U)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      have hp : U*U^(a-r)=U^(1+a-r) := by
        rw [show 1+a-r=1+(a-r) by ring,Real.rpow_add hU0,Real.rpow_one]
      calc
        _ = (256*C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r))*(U*U^(a-r)) := by ring
        _ = _ := by rw [hp]

end ProbeHighRowFamily
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
