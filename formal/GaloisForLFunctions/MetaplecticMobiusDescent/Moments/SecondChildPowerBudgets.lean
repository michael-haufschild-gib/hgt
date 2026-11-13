/-
Second child power budgets adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.FirstChildProfileControl
import GaloisForLFunctions.MetaplecticMobiusDescent.Energy.AllocatedClippedProfiles

/-!
# Second child power budgets

Powers, coefficients and source costs of the second child power budget; branches and removed
widths of exceptional paid scales; seven dyadic bands transfer the amplified estimate to the
annular majorant.
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
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentFirstAnnularEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentFirstAnnularMajorant CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentSmoothedWindowEnergy
local notation "O"=> Eisenstein.O

variable {α:Type*}

lemma dyadic_summable (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(j:ℤ):Summable (fun z:O=> dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2):=by
  have hs:=gaussEnergy_hasSum_re S a ha c CenteredMomentEnergyProfiles.annulusTemplate.profile
    (dyadicScale j) (dyadicScale_pos j)
  simpa only [CenteredMomentEnergyProfiles.annulusTemplate_apply,Complex.ofReal_re,
    dyadicWeight,normValue_eq_embedding,mul_comm] using hs.summable

lemma weighted_summable (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0< H):
    Summable (fun z:O=>‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
  simpa only [normValue_eq_embedding] using (gaussEnergy_hasSum_re S a ha c profile H hH).summable

theorem energy_partition (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0< H):
    (gaussEnergy S a ha c profile H).re=
      ∑j∈bands H,∑'z:O,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
  have hs:=weighted_summable S a ha c H hH
  have hj (j:ℤ):Summable (fun z:O=> dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)):=by
    apply hs.of_nonneg_of_le
    · intro z
      exact mul_nonneg (dyadicWeight_bounds j _).1 (mul_nonneg (sq_nonneg _) (profile_nonneg _))
    · intro z
      exact mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) (profile_nonneg _)) (dyadicWeight_bounds j _).2
  have he (z:O):‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re=
      ∑j∈bands H,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
    rw [←Finset.sum_mul]
    calc
      _=‖gaussPolynomial S a ha c z‖^2*
          ((∑j∈bands H,dyadicWeight j (normValue z))*(profile (normValue z/H)).re):=by
        rw [←weighted_partition H (normValue z) hH]
      _=_:=by ring
  have hsum:=gaussEnergy_hasSum_re S a ha c profile H hH
  rw [←hsum.tsum_eq]
  simp_rw [←normValue_eq_embedding]
  calc
    _ = ∑'z:O, ∑j∈bands H,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re) :=
      tsum_congr he
    _ = _ := Summable.tsum_finsetSum (fun j _=> hj j)

theorem energy_le_dyadic (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0< H):
    (gaussEnergy S a ha c profile H).re≤
      ∑j∈bands H,∑'z:O,dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2:=by
  rw [energy_partition S a ha c H hH]
  apply Finset.sum_le_sum
  intro j hj
  have hs:=dyadic_summable S a ha c j
  have hdom (z:O):dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)≤
      dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2:=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (sq_nonneg _) (profile_le_one _))
      (dyadicWeight_bounds j _).1
  have hl:Summable (fun z:O=> dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)):=
    hs.of_nonneg_of_le (fun z=> mul_nonneg (dyadicWeight_bounds j _).1
      (mul_nonneg (sq_nonneg _) (profile_nonneg _))) hdom
  exact hl.tsum_le_tsum hdom hs

end CenteredMomentFirstAnnularEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentFirstAnnularGeometry
open CenteredMomentSectorLocalization CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstAnnularEnergy CenteredMomentGaussEnergy CanonicalQuadraticSieve

local notation "O"=> Eisenstein.O

lemma retained_of_scale_le (j:ℤ)(R:ℝ)(h:dyadicScale j≤ R):Retained R j:=by
  refine ⟨dyadicScale j/2, by exact div_pos (dyadicScale_pos j) (by norm_num), by linarith [dyadicScale_pos j], ?_⟩
  apply subset_closure
  change dyadicWeight j (dyadicScale j/2)≠0
  have he:(dyadicScale j/2)/dyadicScale j=(1/2:ℝ):=by
    field_simp [ne_of_gt (dyadicScale_pos j)]
  rw [dyadicWeight,he,annulus,cutoff_one _ (by norm_num)]
  norm_num [cutoff_zero]

lemma bands_retained (H R:ℝ)(hH:0< H)(hR:8*H≤ R)(j:ℤ)(hj:j∈bands H):
    Retained R j:=retained_of_scale_le j R ((bands_scale H hH j hj).2.trans hR)

lemma bands_log_cap (H Z A:ℝ)(hH:0< H)(hZ:1< Z)(hcap:8*H≤ Z^A)
    (j:ℤ)(hj:j∈bands H):Real.logb Z (dyadicScale j)≤ A:=by
  have he:Real.logb Z (Z^A)=A:=Real.logb_rpow (by positivity) (ne_of_gt hZ)
  rw [←he]
  exact Real.logb_le_logb_of_le hZ (dyadicScale_pos j) ((bands_scale H hH j hj).2.trans hcap)

lemma bands_nonempty (H:ℝ)(hH:0< H):(bands H).Nonempty:=by
  by_contra hn
  have he:bands H=∅:=Finset.not_nonempty_iff_eq_empty.mp hn
  have hp:=weighted_partition H (H/2) hH
  have hr:(H/2)/H=(1/2:ℝ):=by field_simp
  rw [hr,profile_one _ (by norm_num) (by norm_num),he] at hp
  norm_num at hp

theorem common_bound {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(H B:ℝ)(hH:0< H)(hB:0≤ B)
    (hb:∀j∈bands H,(∑' z : O, dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2)≤ B):
    (gaussEnergy S a ha c profile H).re≤7*B:=by
  apply (energy_le_dyadic S a ha c H hH).trans
  calc
    _≤∑j∈bands H,B:=Finset.sum_le_sum hb
    _=((bands H).card:ℝ)*B:=by simp
    _≤7*B:=mul_le_mul_of_nonneg_right (bands_card H hH) hB

theorem common_bound_auto {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(H B:ℝ)(hH:0< H)
    (hb:∀j∈bands H,(∑' z : O, dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2)≤ B):
    (gaussEnergy S a ha c profile H).re≤7*B:=by
  obtain ⟨j,hj⟩:=bands_nonempty H hH
  have hB:0≤ B:=(tsum_nonneg (fun z=> mul_nonneg (dyadicWeight_bounds j _).1 (sq_nonneg _))).trans (hb j hj)
  exact common_bound S a ha c H B hH hB hb

end CenteredMomentFirstAnnularGeometry

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace CenteredMomentFirstAnnularAmplification
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve 
open  CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=> Eisenstein.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

/-- Seven dyadic bands transfer the amplified estimate to the annular majorant. -/
theorem eventually_annular_amplification_common {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hb : 0≤ b) (hgap : eta< sigma/6)
    (hC : 1≤ Csec) (hxi : 0≤ xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → lambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayFourExpansion.RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤ eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤ Z^BR → (Ideal.absNorm D.s:ℝ)≤ Z^Bs →
          ∀ (t T d cLog : ℝ),0< T →
          ∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0< K → 0< X →
          Tsec≤ Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0< H0 → H0≤4*frequencyRadius Tsec Z xi →
          8*H0≤ Z^Mmax →
          (gaussEnergy Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            CenteredMomentFirstAnnularMajorant.profile H0).re≤
            (56/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))) := by
  filter_upwards [CenteredMomentAmplificationRadicalChoice.eventually_original_amplification_common
    (ι:=ι) M H hH Sbad hbad sigma loss BR Bs Mmax b eta (32*Csec) xi reserve
    hsigma hloss hM hb hgap (by linarith) hxi hreserve] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩:=hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  have hsec' :32*Tsec≤(32*Csec)*firstNominalScale I J E K X:=by nlinarith
  have hfreq:8*H0≤ frequencyRadius (32*Tsec) Z xi:=by
    unfold frequencyRadius at houter ⊢
    nlinarith
  have hbnd:=CenteredMomentFirstAnnularGeometry.common_bound_auto Finset.univ
    (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (D.coefficient η m t T) H0 _ hH0 (fun j hj=>
      henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
        I J E hE K X (32*Tsec) hK hX hsec' j
        (CenteredMomentFirstAnnularGeometry.bands_retained H0 _ hH0 hfreq j hj)
        (CenteredMomentFirstAnnularGeometry.bands_log_cap H0 Z Mmax hH0 hZ hcap j hj))
  convert hbnd using 1 <;> first | rfl | ring

end CenteredMomentFirstAnnularAmplification

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstExceptionalPaidScales
open CanonicalQuadraticSieve CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentFirstPhysicalLedger
local notation "O"=> Eisenstein.O

structure Branch (Z:ℝ) where
  I:Ideal O
  J:Ideal O
  E:Ideal O
  hI:Supported I
  hJ:Supported J
  hE:E≠0
  H:ℝ
  X:ℝ
  Tsec:ℝ
  Csec:ℝ
  ξ:ℝ
  q:ℝ
  w:ℝ
  wo:ℝ
  ell:ℝ
  σ:ℝ
  kind:ℝ
  hH:0< H
  hX:0< X
  hCsec:1≤ Csec
  hξ:0≤ξ
  hsec:Tsec≤ Csec*firstNominalScale I J E H X
  n:ℤ
  hn:Retained (frequencyRadius Tsec Z ξ) n
  hq:0≤ q
  hw:0≤ w
  hwo:0≤ wo
  hell:0≤ ell
  hσ:0≤σ
  hkind:kind≤2
  hwσ:w≤7*σ/3

def removedWidth {Z:ℝ}(s:Branch Z):ℝ:=
  Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)+s.w

def saving {Z:ℝ}(s:Branch Z):ℝ:=
  let c:=Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)
  let d:=Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)
  let p:=Real.logb Z ((commonRadical s.I s.J).absNorm:ℝ)
  let R:=Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ)
  let e:=Real.logb Z (s.E.absNorm:ℝ)
  let D₀:=d+Real.logb Z (firstNominalScale s.I s.J s.E s.H s.X)-
    Real.logb Z (dyadicScale s.n)
  firstSaving c D₀ s.w (s.q+R+e) s.wo (c+d-2*p-R)
    (max (D₀-c-2*s.w+s.wo) 0+s.kind*s.σ) s.ell

def loss {Z:ℝ}(s:Branch Z):ℝ:=3*s.σ+5*frequencyLoss Z s.Csec s.ξ/6

def rawCap (Z:ℝ)(X red:Fin 2→ℝ):ℝ:=
  min (Real.logb Z (X 0/red 0)) (Real.logb Z (X 1/red 1))

lemma actual_saving {Z:ℝ}(hZ:1< Z)(s:Branch Z):
    2*removedWidth s/3-loss s≤ saving s:=by
  have hh:=actual_first_saving s.I s.J s.E s.hI s.hJ s.hE Z s.H s.X s.Tsec s.Csec
    s.ξ s.q s.w s.wo s.ell s.σ s.kind hZ s.hH s.hX s.hCsec s.hξ s.hsec
    s.n s.hn s.hq s.hw s.hwo s.hell s.hσ s.hkind s.hwσ
  simpa only [removedWidth,loss,saving,sub_add_eq_sub_sub] using hh

lemma raw_cap_lower (Z L d:ℝ)(hZ:1< Z)(X red:Fin 2→ℝ)
    (hX:∀i,Z^L≤ X i)(hred:∀i,0< red i)(hupper:∀i,red i≤ Z^d):
    L-d≤ rawCap Z X red:=by
  have h (i:Fin 2):L-d≤ Real.logb Z (X i/red i):=by
    have hz:0< Z:=zero_lt_one.trans hZ
    have hx:0< X i:=(Real.rpow_pos_of_pos hz L).trans_le (hX i)
    have hl:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos hz L) (hX i)
    have hr:=Real.logb_le_logb_of_le hZ (hred i) (hupper i)
    rw [Real.logb_rpow hz hZ.ne'] at hl hr
    rw [Real.logb_div hx.ne' (hred i).ne']
    linarith
  exact le_min (h 0) (h 1)

theorem actual_branch_stage (Z A M:ℝ)(hZ:1< Z)(s:Branch Z)(X red:Fin 2→ℝ)
    (hX:∀i,Z^(M/4)≤ X i)(hred:∀i,0< red i)
    (hupper:∀i,red i≤ Z^(removedWidth s)):
    A-5*M/6-saving s-2*max (rawCap Z X red) 0/3≤ A-M+loss s:=by
  have hs:=actual_saving hZ s
  have hr:=raw_cap_lower Z (M/4) (removedWidth s) hZ X red hX hred hupper
  have hm:=le_max_left (rawCap Z X red) (0:ℝ)
  linarith

theorem actual_paired_stage (Z A M:ℝ)(hZ:1< Z)(s:Fin 2→Branch Z)
    (X red:Fin 2→Fin 2→ℝ)
    (hX:∀j i,Z^(M/4)≤ X j i)(hred:∀j i,0< red j i)
    (hupper:∀j i,red j i≤ Z^(removedWidth (s j))):
    A-5*M/6-(saving (s 0)+saving (s 1))/2-
      (max (rawCap Z (X 0) (red 0)) 0+max (rawCap Z (X 1) (red 1)) 0)/3≤
      max (A-M) 0+(loss (s 0)+loss (s 1))/2:=by
  have h₀:=actual_branch_stage Z A M hZ (s 0) (X 0) (red 0) (hX 0) (hred 0) (hupper 0)
  have h₁:=actual_branch_stage Z A M hZ (s 1) (X 1) (red 1) (hX 1) (hred 1) (hupper 1)
  have hm:=le_max_left (A-M) (0:ℝ)
  linarith

end CenteredMomentFirstExceptionalPaidScales

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstMixedAllowance
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical CenteredMomentFirstCanonicalAllowance
open CenteredMomentFirstPhysicalLedger CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentFirstExceptionalPaidScales
local notation "O"=> Eisenstein.O

theorem first_saving_with_allowance {Z:ℝ}(hZ:1< Z)(s:Branch Z):
    let c:=Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)
    let d:=Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ)
    let e:=Real.logb Z (s.E.absNorm:ℝ)
    let D₀:=d+Real.logb Z (firstNominalScale s.I s.J s.E s.H s.X)-
      Real.logb Z (dyadicScale s.n)
    2*(c+s.w)/3-loss s≤
      firstSaving c D₀ s.w (s.q+R+e) s.wo (extractedAllowance s.I s.J Z)
        (max (D₀-c-2*s.w+s.wo) 0+s.kind*s.σ) s.ell:=by
  have hC:(1:ℝ)≤((commonPart s.I s.J).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero s.I s.J))
  have hR:(1:ℝ)≤((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr
        (SchwartzPlanePoisson.finitePrimeModulus_ne_zero _)))
  have hE:(1:ℝ)≤(s.E.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr s.hE)
  have hc:=Real.logb_nonneg hZ hC
  have hr:=Real.logb_nonneg hZ hR
  have he:=Real.logb_nonneg hZ hE
  have hd:=retained_deficit s.I s.J s.E s.hE Z s.H s.X s.Tsec s.Csec s.ξ
    hZ s.hH s.hX (zero_lt_one.trans_le s.hCsec) s.hsec s.n s.hn
  have hh:=firstSaving_lower _ _ _ s.w
    (s.q+Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ)+Real.logb Z (s.E.absNorm:ℝ))
    _ s.wo (extractedAllowance s.I s.J Z)
    (max (Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)+
      Real.logb Z (firstNominalScale s.I s.J s.E s.H s.X)-Real.logb Z (dyadicScale s.n)-
      Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)-2*s.w+s.wo) 0+s.kind*s.σ)
    s.ell s.σ (frequencyLoss Z s.Csec s.ξ)
    hc s.hw (by linarith [s.hq]) s.hwo (by unfold extractedAllowance;positivity)
    s.hσ (frequencyLoss_nonneg Z s.Csec s.ξ hZ s.hCsec s.hξ)
    (by linarith [s.hq]) (le_refl _) hd (by nlinarith [s.hkind,s.hσ]) s.hell s.hwσ
  dsimp only at hh ⊢
  simpa only [loss,sub_add_eq_sub_sub] using hh

def columnSaving {Z:ℝ}(s:Branch Z):ℝ:=
  saving s-(Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)+
    Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)-
    2*Real.logb Z ((commonRadical s.I s.J).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ))+
    extractedAllowance s.I s.J Z

lemma column_saving {Z:ℝ}(hZ:1< Z)(s:Branch Z):
    2*removedWidth s/3-loss s≤ columnSaving s:=by
  have hh:=first_saving_with_allowance hZ s
  dsimp only [columnSaving,saving,removedWidth] at hh ⊢
  unfold firstSaving at hh ⊢
  linarith

end CenteredMomentFirstMixedAllowance

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentSecondChildPowerBudget
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEligibleEnergy
open CenteredMomentFirstChildProfileControl CenteredMomentCommonRadialPointwise
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
local notation "O"=> Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma endpoint_product (s : Input ι) (N : ℕ) (b : ℝ) (hb : 1≤ b)
    (hu : s.upper≤ b) (hc : Fintype.card ι≤ N) (hhi : ∀i,0≤ s.hi i) :
    0≤∏i,s.hi i ∧ (∏i,s.hi i)≤ b^N := by
  refine ⟨Finset.prod_nonneg (fun i _=> hhi i),?_⟩
  calc
    _≤∏i:ι,b:=Finset.prod_le_prod (fun i _=> hhi i) (fun i _=>(s.upper_ge i).trans hu)
    _=b^Fintype.card ι:=by simp
    _≤ b^N:=pow_le_pow_right₀ hb hc

omit [DecidableEq ι] in
lemma main_cost (s : Input ι) (N : ℕ) (b b₁ b₂ A : ℝ)
    (hb : 1≤ b) (h₁ : 1≤ b₁) (h₂ : 1≤ b₂) (hu : s.upper≤ b)
    (hc : Fintype.card ι≤ N) (hhi : ∀i,0≤ s.hi i)
    (hs₁ : 0≤ s.b₁) (hs₂ : 0≤ s.b₂) (hb₁ : s.b₁≤ b₁) (hb₂ : s.b₂≤ b₂)
    (hm : mass s≤ A) :
    profileCost s*sourceRadius s≤
      (2*(b₁*b₂)*b^N*A^2)*(b^N*b₁*b₂)*
        CenteredMomentAmplificationChildInput.volume s*mass s^2 := by
  have hg:=CenteredMomentAmplificationChildSourceCaps.radius_le N b b₁ b₂ hb
    (zero_le_one.trans h₁) (zero_le_one.trans h₂) s hc hhi
    (fun i=>(s.upper_ge i).trans hu) hs₁ hs₂ hb₁ hb₂
  have hp:=profile_cost_bound s N b A hb hu hc hm
  have he : max 1 s.b₁*max 1 s.b₂≤ b₁*b₂ :=
    mul_le_mul (max_le h₁ hb₁) (max_le h₂ hb₂) (by positivity) (by linarith)
  have hp' : profileCost s≤(2*(b₁*b₂)*b^N*A^2)*mass s^2 := by
    apply hp.trans
    gcongr
  have hh:=mul_le_mul hp' hg.2 hg.1 (by positivity)
  convert hh using 1 <;> first | rfl | ring

omit [DecidableEq ι] in
lemma diagonal_cost (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)) (N : ℕ) (b whi ε : ℝ)
    (hb : 1≤ b) (hu : s.upper≤ b) (hc : Fintype.card ι≤ N)
    (hhi : ∀i,0≤ s.hi i) (hε : 0≤ε) :
    (2*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*mass s)^2*
      (1+(∏i,s.hi i)*whi*whi)^(1+ε)≤
    (4*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
      (1+b^N*whi^2)^(1+ε))*mass s^2 := by
  have hp:=endpoint_product s N b hb hu hc hhi
  have hx : 1+(∏i,s.hi i)*whi*whi≤1+b^N*whi^2 := by nlinarith [mul_le_mul_of_nonneg_right hp.2 (sq_nonneg whi)]
  have hx0 : 0≤1+(∏i,s.hi i)*whi*whi := by nlinarith [mul_nonneg hp.1 (sq_nonneg whi)]
  have h:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0 hx (by linarith : 0≤1+ε))
    (sq_nonneg (2*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*mass s))
  convert h using 1 <;> first | rfl | ring

omit [DecidableEq ι] in
lemma tail_cost (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)) :
    plainControl s W₁ W₂^2=
      (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*mass s^2 := by
  unfold plainControl mass
  ring

def powers (ε : ℝ) : Fin 4→ℝ := ![1,1/3,ε,0]

lemma powers_nonneg (ε : ℝ) (hε : 0≤ε) : ∀j,0≤ powers ε j := by
  intro j
  fin_cases j <;> simp [powers,hε]

def coefficients {wlo whi : ℝ} (N : ℕ) (b b₁ b₂ A : ℝ)
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O)
    (K t ε seedNorm : ℝ) (a : Fin 4→ℝ) : Fin 4→ℝ :=
  ![a 0*(2*(b₁*b₂)*b^N*A^2)*(b^N*b₁*b₂)/seedNorm,
    a 1*exceptionalConstant N b J Q K*p.control S^2*(1+‖t‖)^(2*J)*A^4/seedNorm,
    a 2*4*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2*(1+b^N*whi^2)^(1+ε)/seedNorm,
    a 3*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2]

lemma coefficients_nonneg {wlo whi : ℝ} (N : ℕ) (b b₁ b₂ A : ℝ)
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O)
    (K t ε seedNorm : ℝ) (a : Fin 4→ℝ)
    (hb : 0≤ b) (h₁ : 0≤ b₁) (h₂ : 0≤ b₂) (hK : 0≤ K)
    (hs : 0≤ seedNorm) (ha : ∀j,0≤ a j) :
    ∀j,0≤ coefficients N b b₁ b₂ A S p J Q K t ε seedNorm a j := by
  have h0:=ha 0
  have h1:=ha 1
  have h2:=ha 2
  have h3:=ha 3
  intro j
  fin_cases j <;> dsimp [coefficients,exceptionalConstant] <;> positivity

def sourceCost {wlo whi : ℝ} (s : Input ι) (S : Finset (ℕ×ℕ))
    (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O) (K ε seedNorm : ℝ)
    (a : Fin 4→ℝ) : ℝ :=
    a 0*profileCost s*sourceRadius s/seedNorm+
    a 1*profileFactor S s p J Q K*(CenteredMomentAmplificationChildInput.volume s)^(1/3:ℝ)/seedNorm+
    a 2*(2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*mass s)^2*
      (1+(∏i,s.hi i)*whi*whi)^(1+ε)*(CenteredMomentAmplificationChildInput.volume s)^ε/seedNorm+
    a 3*plainControl s (p.profile 0) (p.profile 1)^2

omit [DecidableEq ι] in
theorem source_rhs {wlo whi : ℝ} (s : Input ι) (N : ℕ) (b b₁ b₂ A : ℝ)
    (hb : 1≤ b) (h₁ : 1≤ b₁) (h₂ : 1≤ b₂) (hu : s.upper≤ b)
    (hc : Fintype.card ι≤ N) (hhi : ∀i,0≤ s.hi i)
    (hs₁ : 0≤ s.b₁) (hs₂ : 0≤ s.b₂) (hb₁ : s.b₁≤ b₁) (hb₂ : s.b₂≤ b₂)
    (hm : mass s≤ A) (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi)
    (J : ℕ) (Q : Ideal O) (K ε seedNorm : ℝ) (hK : 0≤ K) (hε : 0≤ε)
    (hs : 0≤ seedNorm) (a : Fin 4→ℝ) (ha : ∀j,0≤ a j) :
    sourceCost s S p J Q K ε seedNorm a ≤
      (∑j,coefficients N b b₁ b₂ A S p J Q K s.t ε seedNorm a j*
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  unfold sourceCost
  have hv := (CenteredMomentAmplificationChildInput.volume_pos s).le
  have hmain:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (main_cost s N b b₁ b₂ A hb h₁ h₂ hu hc hhi hs₁ hs₂ hb₁ hb₂ hm) (ha 0)) hs
  have hexc:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exceptional_factor_bound S p J Q K hK s N b A hb hu hc hm) (ha 1))
      (Real.rpow_nonneg hv (1/3:ℝ))) hs
  have hdiag:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (diagonal_cost s (p.profile 0) (p.profile 1) N b whi ε hb hu hc hhi hε) (ha 2))
      (Real.rpow_nonneg hv ε)) hs
  have htail:=congrArg (fun x:ℝ=> a 3*x) (tail_cost s (p.profile 0) (p.profile 1))
  have hh:=add_le_add (add_le_add (add_le_add hmain hexc) hdiag) (le_of_eq htail)
  convert hh using 1 <;> first | rfl |
    ((try simp only [coefficients,powers,Fin.sum_univ_succ,Fin.sum_univ_zero,
      Matrix.cons_val_zero,Matrix.cons_val_succ,
      Real.rpow_one,Real.rpow_zero]); ring)

omit [DecidableEq ι] in
theorem twice_source_rhs {wlo whi : ℝ} (s : Input ι) (N : ℕ) (b b₁ b₂ : ℝ)
    (hb : 1≤ b) (h₁ : 1≤ b₁) (h₂ : 1≤ b₂) (hu : s.upper≤ b)
    (hc : Fintype.card ι≤ N) (hhi : ∀i,0≤ s.hi i)
    (hs₁ : 0≤ s.b₁) (hs₂ : 0≤ s.b₂) (hb₁ : s.b₁≤ b₁) (hb₂ : s.b₂≤ b₂)
    (C R : Ideal O) (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (P : Ideal O) (k : ℕ)
    (Bp : CenteredMomentCommonAllocationSum.actualAllocations
      (CenteredMomentAmplificationChildInput.child s C R B τ t).pools (P^k))
    (υ : Character) (v : ℝ)
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O)
    (K ε seedNorm : ℝ) (hK : 0≤ K) (hε : 0≤ε) (hs : 0≤ seedNorm)
    (a : Fin 4→ℝ) (ha : ∀j,0≤ a j) :
    let d:=CenteredMomentAmplificationChildSourceCaps.twiceChild s C R B τ t P k Bp υ v;
    sourceCost d S p J Q K ε seedNorm a≤
      (∑j,coefficients N b b₁ b₂ (mass s) S p J Q K v ε seedNorm a j*
        (CenteredMomentAmplificationChildInput.volume d)^(powers ε j))*mass d^2 := by
  let d:=CenteredMomentAmplificationChildSourceCaps.twiceChild s C R B τ t P k Bp υ v
  have hm : mass d≤ mass s :=
    (child_mass (CenteredMomentAmplificationChildInput.child s C R B τ t) (P^k) (R*C) Bp υ v).trans
      (child_mass s C R B τ t)
  have hn : Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤ N :=
    (child_card Bp.val).trans ((child_card B.val).trans hc)
  exact source_rhs d N b b₁ b₂ (mass s) hb h₁ h₂ hu hn
    (fun i=> hhi i.val.val) hs₁ hs₂ hb₁ hb₂ hm S p J Q K ε seedNorm hK hε hs a ha

end CenteredMomentSecondChildPowerBudget

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace CenteredMomentFirstAnnularInput
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve 
open  CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=> Eisenstein.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily

theorem eventually_input_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hb : 0≤ b) (hgap : eta< sigma/6)
    (hC : 1≤ Csec) (hxi : 0≤ xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ s : Input ι,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤ eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤ Z^BR → (seed.absNorm:ℝ)≤ Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0< K → 0< X →
          Tsec≤ Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0< H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤ Z^Mmax →
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                normalizedGaussSource s R seed ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve)+
                ∑p : elementPool P,∑i : Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
                    ∑χ:RayCharacter,∑B:actualAllocations (activeInput s).pools
                        ((Ideal.span {p.val})^(errorIndex i+1)),
                      childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                        R seed B (τ p i χ) s.t ballProfile
                        (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                          (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))) := by
  filter_upwards [CenteredMomentFirstAnnularAmplification.eventually_annular_amplification_common
    (ι:=ι) M H hH Sbad hbad sigma loss BR Bs Mmax b eta Csec xi reserve
    hsigma hloss hM hb hgap hC hxi hreserve,
    eventually_dyadic_amplification.{0} M H hH Sbad hbad sigma loss BR Bs Mmax b eta
      hsigma hloss hM hgap] with Z hz hpz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hpz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η
  obtain ⟨τ,hN,henergy⟩:=hfam η fixedBadMask fixedBadMask_ne_zero
    (dvd_mul_right _ _) (dvd_mul_left _ _)
  refine ⟨τ,hN,?_⟩
  intro s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  have he:=henergy (original s R seed) s.pools_ne s.prime hsupp z hz hlen hR0 hs0 hR hs
    s.t (volume s) d cLog (volume_pos s) I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  rw [←hsη,normalized_input_coefficient,normalized_input_coefficient] at he
  convert he using 1
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
    (fun Q hQ=>(hdata Q hQ).2.1) p.val p.property
  have hcop:∀i,∀Q∈(activeInput s).slots i,IsCoprime (Ideal.span {p.val}) Q:=by
    exact original_slot_coprime (original s R seed).active Z sigma b eta hZ.le hb hsep z hz hlen
      hsupp (original s R seed).active_slot
      (fun i Q hQ=> s.prime i Q ((original s R seed).active_subset _ hQ))
      (Ideal.span {p.val}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  apply Finset.sum_congr rfl
  intro i _
  rw [←original_active]
  exact (original_childEnergy_eq_inputs (activeInput s) R seed (τ p i) p.val hd.1.ne_zero hcop
    (errorIndex i) s.t _).symm

end CenteredMomentFirstAnnularInput

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace CenteredMomentFirstAmplifiedPowerBudget
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve 
open  CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=> Eisenstein.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily

open CenteredMomentFirstAnnularInput CenteredMomentFirstErrorAllocationPower
theorem eventually_input_power_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hb : 0≤ b) (hgap : eta< sigma/6)
    (hC : 1≤ Csec) (hxi : 0≤ xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ s : Input ι,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤ eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤ Z^BR → (seed.absNorm:ℝ)≤ Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0< K → 0< X →
          Tsec≤ Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0< H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤ Z^Mmax →
          ∀ (amain:Fin 4→ℝ) (aerror:elementPool P→Fin 3→RayCharacter→Fin 4→ℝ)
            (α:Fin 4→ℝ), (∀p i χ j,0≤ aerror p i χ j)→
          (normalizedGaussSource s R seed ballProfile
            (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
              (frequencyLoss Z (32*Csec) xi) reserve)≤
                (∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)→
          (∀p:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
            ∀B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                R seed B (τ p i χ) s.t ballProfile
                (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                  (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))≤
                (∑j,aerror p i χ j*(volume (child (activeInput s)
                  ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ p i χ) s.t))^(α j))*
                  CenteredMomentFirstChildProfileControl.mass (child (activeInput s)
                    ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ p i χ) s.t)^2)→
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*CenteredMomentFirstChildProfileControl.mass s^2*
              (((Mmax+2*sigma)/(sigma/6))*(∑j,amain j*(volume s)^(α j))+
                ∑p:elementPool P,∑i:Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*(errorIndex i+2:ℝ)*
                    ∑χ:RayCharacter,∑j,aerror p i χ j*
                      (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j)) := by
  filter_upwards [eventually_input_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta Csec xi reserve hsigma hloss hM hb hgap hC hxi hreserve,
    eventually_dyadic_amplification.{0} M H hH Sbad hbad sigma loss BR Bs Mmax b eta
      hsigma hloss hM hgap] with Z hz hpz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hpz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η
  obtain ⟨τ,hN,henergy⟩:=hfam η
  refine ⟨τ,hN,?_⟩
  intro s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec hK hX hsec
    H0 hH0 houter hcap amain aerror α haerr hmain herr
  have he:=henergy s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec
    hK hX hsec H0 hH0 houter hcap
  apply he.trans
  have hpweight:0≤56/((primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card:ℝ):=by positivity
  have hmweight:0≤(Mmax+2*sigma)/(sigma/6):=by positivity
  have herror: ∀p:elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))),∀i:Fin 3,
      (∑χ:RayCharacter,∑B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
          R seed B (τ p i χ) s.t ballProfile
          (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
            (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1)))≤
      (errorIndex i+2:ℝ)*(∑χ:RayCharacter,∑j,aerror p i χ j*
        (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
          CenteredMomentFirstChildProfileControl.mass s^2:=by
    intro p i
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) p.val p.property
    have hcop:∀j,∀Q∈(activeInput s).slots j,IsCoprime (Ideal.span {p.val}) Q:=by
      exact original_slot_coprime (original s R seed).active Z sigma b eta hZ.le hb hsep z hz hlen
        hsupp (original s R seed).active_slot
        (fun j Q hQ=> s.prime j Q ((original s R seed).active_subset _ hQ))
        (Ideal.span {p.val}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hq:Prime (Ideal.span {p.val}):=(hdata _ hd.2.1).1
    calc
      _≤∑χ:RayCharacter,((errorIndex i+1+1:ℕ):ℝ)*
          (∑j,aerror p i χ j*(volume (activeInput s)/
            ((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
              CenteredMomentFirstChildProfileControl.mass (activeInput s)^2:=by
        apply Finset.sum_le_sum
        intro χ hχ
        apply le_trans (Finset.sum_le_sum (fun B _=> herr p i χ B))
        exact budget_sum_le (activeInput s) (Ideal.span {p.val}) hq (errorIndex i+1) hcop R
          (fun _=>τ p i χ) (fun _=> s.t) 4 (aerror p i χ) α (haerr p i χ)
      _=_:=by
        simp only [CenteredMomentFirstChildProfileControl.mass,activeInput]
        push_cast
        rw [←Finset.sum_mul,←Finset.mul_sum]
        congr 2
        ring
  calc
    _≤(56/((primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*
          ((∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)+
          ∑p:elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))),∑i:Fin 3,(16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
            ((errorIndex i+2:ℝ)*(∑χ:RayCharacter,∑j,aerror p i χ j*
              (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
                CenteredMomentFirstChildProfileControl.mass s^2)):=by
      apply mul_le_mul_of_nonneg_left _ hpweight
      apply add_le_add (mul_le_mul_of_nonneg_left hmain hmweight)
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (herror p i)
        (mul_nonneg (by positivity) (localErrorCost_nonneg p (errorIndex i)))
    _=_:=by
      simp only [←mul_assoc,←Finset.sum_mul]
      ring

theorem eventually_original_subsets_power_amplification {Ω : Type*} [Fintype Ω]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hb : 0≤ b) (hgap : eta< sigma/6)
    (hC : 1≤ Csec) (hxi : 0≤ xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (A:Finset Ω) → (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (A:Finset Ω) (p : elementPool P) i χ,(τ A p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ A:Finset Ω,∀ s : Input A,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : A→ℝ),(∀i,z i≤ eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤ Z^BR → (seed.absNorm:ℝ)≤ Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0< K → 0< X →
          Tsec≤ Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0< H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤ Z^Mmax →
          ∀ (amain:Fin 4→ℝ) (aerror:elementPool P→Fin 3→RayCharacter→Fin 4→ℝ)
            (α:Fin 4→ℝ), (∀p i χ j,0≤ aerror p i χ j)→
          (normalizedGaussSource s R seed ballProfile
            (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
              (frequencyLoss Z (32*Csec) xi) reserve)≤
                (∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)→
          (∀p:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
            ∀B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                R seed B (τ A p i χ) s.t ballProfile
                (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                  (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))≤
                (∑j,aerror p i χ j*(volume (child (activeInput s)
                  ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t))^(α j))*
                  CenteredMomentFirstChildProfileControl.mass (child (activeInput s)
                    ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t)^2)→
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*CenteredMomentFirstChildProfileControl.mass s^2*
              (((Mmax+2*sigma)/(sigma/6))*(∑j,amain j*(volume s)^(α j))+
                ∑p:elementPool P,∑i:Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*(errorIndex i+2:ℝ)*
                    ∑χ:RayCharacter,∑j,aerror p i χ j*
                      (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j)) := by
  have hall:=Filter.eventually_all.mpr (fun A:Finset Ω=>
    eventually_input_power_amplification (ι:=A) M H hH Sbad hbad sigma loss BR Bs Mmax b eta Csec xi reserve
      hsigma hloss hM hb hgap hC hxi hreserve)
  filter_upwards [hall] with Z hz
  have hbase:=hz (∅:Finset Ω)
  refine ⟨hbase.1,hbase.2.1,hbase.2.2.1,?_⟩
  intro η
  have hf (A:Finset Ω):=(hz A).2.2.2 η
  choose τ hN he using hf
  exact ⟨τ,hN,he⟩

end CenteredMomentFirstAmplifiedPowerBudget

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstExceptionalChildPaid
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentFirstChildLower
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstExceptionalPaidScales CenteredMomentCompleteCommon
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def inputCap (Z:ℝ)(s:Input ι):ℝ:=
  min (min (Real.logb Z s.X₁) (Real.logb Z s.X₂))
    (min (Real.logb Z s.Y₁) (Real.logb Z s.Y₂))

lemma input_cap_lower (Z r:ℝ)(hZ:1< Z)(s:Input ι)
    (hX₁:Z^r≤ s.X₁)(hX₂:Z^r≤ s.X₂)(hY₁:Z^r≤ s.Y₁)(hY₂:Z^r≤ s.Y₂):
    r ≤ inputCap Z s:=by
  have h (x:ℝ)(hx:Z^r≤ x):r≤ Real.logb Z x:=by
    have hh:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) r) hx
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  exact le_min (le_min (h _ hX₁) (h _ hX₂)) (le_min (h _ hY₁) (h _ hY₂))

lemma input_cap_scales (Z:ℝ)(hZ:1< Z)(s:Input ι):
    Z^(inputCap Z s)≤ s.X₁ ∧ Z^(inputCap Z s)≤ s.X₂ ∧
      Z^(inputCap Z s)≤ s.Y₁ ∧ Z^(inputCap Z s)≤ s.Y₂:=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have h (x:ℝ)(hx:0< x)(hl:inputCap Z s≤ Real.logb Z x):Z^(inputCap Z s)≤ x:=by
    calc
      _≤ Z^(Real.logb Z x):=Real.rpow_le_rpow_of_exponent_le hZ.le hl
      _=x:=Real.rpow_logb hz hZ.ne' hx
  refine ⟨h _ s.X₁_pos ?_,h _ s.X₂_pos ?_,h _ s.Y₁_pos ?_,h _ s.Y₂_pos ?_⟩
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem main_child_stage (Z A M:ℝ)(hZ:1< Z)(b:Branch Z)(hb:b.w=0)
    (s:Input ι)(R:Ideal O)
    (B:actualAllocations s.pools (commonPart b.I b.J))(τ:Character)(t:ℝ)
    (hX₁:Z^(M/4)≤ s.X₁)(hX₂:Z^(M/4)≤ s.X₂)
    (hY₁:Z^(M/4)≤ s.Y₁)(hY₂:Z^(M/4)≤ s.Y₂):
    let d:=child s (commonPart b.I b.J) R B τ t
    A-5*M/6-saving b-2*max (inputCap Z d) 0/3≤ A-M+loss b:=by
  have hh:=child_lower s (commonPart b.I b.J) R (commonPart_ne_zero b.I b.J)
    B τ t Z (M/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hs:=actual_saving hZ b
  have hm:=le_max_left (inputCap Z (child s (commonPart b.I b.J) R B τ t)) (0:ℝ)
  dsimp only [removedWidth] at hs
  rw [hb] at hs
  dsimp only
  linarith

theorem error_child_stage (Z A M:ℝ)(hZ:1< Z)(b:Branch Z)
    (s:Input ι)(R:Ideal O)
    (B:actualAllocations s.pools (commonPart b.I b.J))(τ:Character)(t:ℝ)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (Bp:actualAllocations (child s (commonPart b.I b.J) R B τ t).pools (Q^k))
    (υ:Character)(v:ℝ)(hw:b.w=(k:ℝ)*Real.logb Z (Q.absNorm:ℝ))
    (hX₁:Z^(M/4)≤ s.X₁)(hX₂:Z^(M/4)≤ s.X₂)
    (hY₁:Z^(M/4)≤ s.Y₁)(hY₂:Z^(M/4)≤ s.Y₂):
    let d:=twiceChild s (commonPart b.I b.J) R B τ t Q k Bp υ v
    A-5*M/6-saving b-2*max (inputCap Z d) 0/3≤ A-M+loss b:=by
  have hh:=twice_lower s (commonPart b.I b.J) R (commonPart_ne_zero b.I b.J)
    B τ t Q hQ k Bp υ v Z (M/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hs:=actual_saving hZ b
  have hm:=le_max_left (inputCap Z (twiceChild s (commonPart b.I b.J) R B τ t Q k Bp υ v)) (0:ℝ)
  dsimp only [removedWidth] at hs
  rw [hw] at hs
  dsimp only at hr ⊢
  linarith

theorem actual_error_pair (Z A M:ℝ)(hZ:1< Z)(b:Fin 2→Branch Z)
    (s:Input ι)(R:Ideal O)
    (B:∀j,actualAllocations s.pools (commonPart (b j).I (b j).J))
    (τ:Fin 2→Character)(t:Fin 2→ℝ)(Q:Fin 2→Ideal O)(hQ:∀j,Q j≠0)(k:Fin 2→ℕ)
    (Bp:∀j,actualAllocations
      (child s (commonPart (b j).I (b j).J) R (B j) (τ j) (t j)).pools ((Q j)^(k j)))
    (υ:Fin 2→Character)(v:Fin 2→ℝ)
    (hw:∀j,(b j).w=(k j:ℝ)*Real.logb Z ((Q j).absNorm:ℝ))
    (hX₁:Z^(M/4)≤ s.X₁)(hX₂:Z^(M/4)≤ s.X₂)
    (hY₁:Z^(M/4)≤ s.Y₁)(hY₂:Z^(M/4)≤ s.Y₂):
    let d:=fun j=> twiceChild s (commonPart (b j).I (b j).J) R
      (B j) (τ j) (t j) (Q j) (k j) (Bp j) (υ j) (v j)
    A-5*M/6-(saving (b 0)+saving (b 1))/2-
      (max (inputCap Z (d 0)) 0+max (inputCap Z (d 1)) 0)/3≤
      max (A-M) 0+(loss (b 0)+loss (b 1))/2:=by
  have h₀:=error_child_stage Z A M hZ (b 0) s R (B 0) (τ 0) (t 0) (Q 0) (hQ 0)
    (k 0) (Bp 0) (υ 0) (v 0) (hw 0) hX₁ hX₂ hY₁ hY₂
  have h₁:=error_child_stage Z A M hZ (b 1) s R (B 1) (τ 1) (t 1) (Q 1) (hQ 1)
    (k 1) (Bp 1) (υ 1) (v 1) (hw 1) hX₁ hX₂ hY₁ hY₂
  have hm:=le_max_left (A-M) (0:ℝ)
  dsimp only at h₀ h₁ ⊢
  linarith

end CenteredMomentFirstExceptionalChildPaid

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstMixedChild
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstChildLower CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedCommonRadius
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool 
open CenteredMomentRankinRadical Eisenstein
local notation "O" => Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem actual_main_child_stage (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t parentA parentM:ℝ)
    (hX₁:Z^(parentM/4)≤ s.X₁)(hX₂:Z^(parentM/4)≤ s.X₂)
    (hY₁:Z^(parentM/4)≤ s.Y₁)(hY₂:Z^(parentM/4)≤ s.Y₂) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    parentA-5*parentM/6-(
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (extractedAllowance I J Z)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3))-2*max (inputCap Z (child s (commonPart I J) Rmask B τ t)) 0/3≤
      parentA-parentM+4*sigma/3+5*(delta+reserve)/6 := by
  have hs:=actual_main_column_saving η τ m I J E hI hJ A K X Z j sigma delta reserve hZ hmod
  have hh:=child_lower s (commonPart I J) Rmask (commonPart_ne_zero I J)
    B τ t Z (parentM/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hm:=le_max_left (inputCap Z (child s (commonPart I J) Rmask B τ t)) (0:ℝ)
  dsimp only at hs hr ⊢
  linarith

theorem actual_error_child_stage (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t parentA parentM:ℝ)
    (Bp:actualAllocations (child s (commonPart I J) Rmask B τ t).pools ((Ideal.span {p0})^k))
    (υ:Character)(v:ℝ)
    (hX₁:Z^(parentM/4)≤ s.X₁)(hX₂:Z^(parentM/4)≤ s.X₂)
    (hY₁:Z^(parentM/4)≤ s.Y₁)(hY₂:Z^(parentM/4)≤ s.Y₂) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    parentA-5*parentM/6-(
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (extractedAllowance I J Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0)-2*max (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) 0/3≤
      parentA-parentM+3*sigma/2+5*(delta+reserve)/6 := by
  have hs:=actual_error_column_saving η τ m I J E hI hJ A K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have hQ:Ideal.span {p0}≠0:=Ideal.span_singleton_eq_bot.not.mpr hd.1.ne_zero
  have hh:=twice_lower s (commonPart I J) Rmask (commonPart_ne_zero I J)
    B τ t (Ideal.span {p0}) hQ k Bp υ v Z (parentM/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hm:=le_max_left (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) (0:ℝ)
  dsimp only at hs hr ⊢
  unfold errorRemoval normValue at hs ⊢
  linarith

end CenteredMomentFirstMixedChild

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstMixedExceptionalCap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein 
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

lemma fixed_presentation_log_nonneg (Z:ℝ)(hZ:1< Z):0≤ Real.logb Z fixedPresentationCost:=by
  have h₁:(1:ℝ)≤((Ideal.span {fixedBadMask}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  have h₂:(1:ℝ)≤((Ideal.span {(72:O)}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
  apply Real.logb_nonneg hZ
  unfold fixedPresentationCost
  nlinarith

lemma extracted_allowance_eq (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D)(Z:ℝ):extractedAllowance C D Z=allowance C D Z:=by
  simp only [extractedAllowance,allowance,commonPart_of_equal_support C D hC hCD,
    commonPart_of_equal_support D C hD hCD.symm]

theorem actual_main_exceptional_cap (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex I J=> P.val) A})
    (K X Z j sigma delta reserve : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t:ℝ)(hK:0< K)(hX:0< X)(_hvolume:X=volume s)
    (hX₁:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤ s.X₁)(hX₂:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤ s.X₂)
    (hY₁:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤ s.Y₁)(hY₂:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤ s.Y₂) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max (inputCap Z (child s (commonPart I J) Rmask B τ t)) 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+4*sigma/3+5*(delta+reserve)/6):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_main_child_stage η τ fixedBadMask I J E hI hJ A K X Z j sigma delta reserve hZ hmod s Rmask B t (Real.logb Z X) (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)) hX₁ hX₂ hY₁ hY₂
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have he:=(actual_exceptional_reference η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j) 0 0 (sigma/3) hK hX hZ hmod).le
  rw [←hE] at he
  have hrad:0< mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  rw [show j+(Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j)=Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  simp only [neg_zero,Real.rpow_zero,mul_one,div_one] at he
  have hexp:-sigma/3=-(sigma/3):=by ring
  rw [hexp]
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max (inputCap Z (child s (commonPart I J) Rmask B τ t)) 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

theorem actual_error_exceptional_cap (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex I J=> P.val) A})
    (K X Z j sigma delta reserve : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t:ℝ)(hK:0< K)(hX:0< X)(_hvolume:X=volume s)
    (Bp:actualAllocations (child s (commonPart I J) Rmask B τ t).pools ((Ideal.span {p0})^k))
    (υ:Character)(v:ℝ)
    (hX₁:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤ s.X₁)(hX₂:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤ s.X₂)
    (hY₁:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤ s.Y₁)(hY₂:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤ s.Y₂) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+3*sigma/2+5*(delta+reserve)/6):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_error_child_stage η τ fixedBadMask I J E hI hJ A K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk s Rmask B t (Real.logb Z X) (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)) Bp υ v hX₁ hX₂ hY₁ hY₂
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have hp:=elementPool_data _
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have he:=actual_error_reference_le η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j) hK hX hZ hmod p0 hp.1.ne_zero k hk
  rw [←hE] at he
  have hrad:0< errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k:=by unfold errorCommonRadius;positivity
  rw [show j+(Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j)=Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

end CenteredMomentFirstMixedExceptionalCap

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstMixedExceptionalLow
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein 
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=> Eisenstein.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstMixedExceptionalCap CenteredMomentFirstMixedCommonRadius

theorem actual_main_exceptional_reference (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex I J=> P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0< K)(hX:0< X) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(Real.logb Z X-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+4*sigma/3+5*(delta+reserve)/6):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max r 0 := le_max_right _ _
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_main_column_saving η τ fixedBadMask I J E hI hJ A
    K X Z j sigma delta reserve hZ hmod
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have he:=(actual_exceptional_reference η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j) 0 0 (sigma/3) hK hX hZ hmod).le
  rw [←hE] at he
  have hrad:0< mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  rw [show j+(Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j)=Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  simp only [neg_zero,Real.rpow_zero,mul_one,div_one] at he
  have hexp:-sigma/3=-(sigma/3):=by ring
  rw [hexp]
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max r 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

theorem actual_error_exceptional_reference (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex I J=> P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0< K)(hX:0< X) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(Real.logb Z X-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+3*sigma/2+5*(delta+reserve)/6):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max r 0 := le_max_right _ _
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_error_column_saving η τ fixedBadMask I J E hI hJ A
    K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have hp:=elementPool_data _
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have hl : 0 ≤ Real.logb Z (normValue p0) :=
    Real.logb_nonneg hZ (normValue_ge_one p0 hp.1.ne_zero)
  have hw : 0 ≤ errorRemoval p0 Z k := by unfold errorRemoval; positivity
  have he:=actual_error_reference_le η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j) hK hX hZ hmod p0 hp.1.ne_zero k hk
  rw [←hE] at he
  have hrad:0< errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k:=by unfold errorCommonRadius;positivity
  rw [show j+(Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j)=Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max r 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

theorem actual_main_exceptional_low (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex I J=> P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0< K)(hX:0< X)
    (hLow : Real.logb Z X ≤ 5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(4*sigma/3+5*(delta+reserve)/6) := by
  apply (actual_main_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod hK hX).trans
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem actual_error_exceptional_low (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex I J=> P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0< K)(hX:0< X)
    (hLow : Real.logb Z X ≤ 5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(3*sigma/2+5*(delta+reserve)/6) := by
  apply (actual_error_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod M H Sbad hbad p0 hp0 k hk hK hX).trans
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

end CenteredMomentFirstMixedExceptionalLow

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstMixedExceptionalDeclared
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein 
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=> Eisenstein.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstMixedExceptionalCap CenteredMomentFirstMixedCommonRadius

open CenteredMomentFirstMixedExceptionalLow

theorem actual_main_exceptional_declared (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex I J=> P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0< K)(hX:0< X)
    (Mdecl : ℝ) (hactual : Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ) ≤ Mdecl)
    (hLow : Real.logb Z X ≤ 5*Mdecl/6) :
    (K*(η.modulus.absNorm:ℝ))*(((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3))≤
      Z^(Mdecl+4*sigma/3+5*(delta+reserve)/6) := by
  have hh:=actual_main_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod hK hX
  have hz:0< Z:=zero_lt_one.trans hZ
  have hn:0<(η.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hpow:K*(η.modulus.absNorm:ℝ)=Z^(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)):=by
    rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hn]
  apply (mul_le_mul_of_nonneg_left hh (mul_pos hK hn).le).trans
  rw [hpow,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

theorem actual_error_exceptional_declared (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex I J=> P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1< Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0< K)(hX:0< X)
    (Mdecl : ℝ) (hactual : Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ) ≤ Mdecl)
    (hLow : Real.logb Z X ≤ 5*Mdecl/6) :
    (K*(η.modulus.absNorm:ℝ))*(((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3))≤
      Z^(Mdecl+3*sigma/2+5*(delta+reserve)/6) := by
  have hh:=actual_error_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod M H Sbad hbad p0 hp0 k hk hK hX
  have hz:0< Z:=zero_lt_one.trans hZ
  have hn:0<(η.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hpow:K*(η.modulus.absNorm:ℝ)=Z^(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)):=by
    rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hn]
  apply (mul_le_mul_of_nonneg_left hh (mul_pos hK hn).le).trans
  rw [hpow,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

end CenteredMomentFirstMixedExceptionalDeclared

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstMixedDiagonal
open HeckeFamily CanonicalQuadraticSieve CompletedGauss Eisenstein 
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedExceptionalCap
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstExceptionalPrefactor CenteredMomentDescentLedger
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCanonicalFirst CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationErrorEnergy
local notation "O"=> Eisenstein.O

theorem actual_common_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z w wo branch sigma delta reserve eps:ℝ)(hK:0< K)(hV:0< V)(hZ:1< Z)
    (hw:0≤ w)(hwo:0≤ wo)(heps:0≤ eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=nominalLog C D
      (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z;
    (V/(C.absNorm:ℝ))*Z^(-wo)*
      Z^(K0+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve)*
      (V/(C.absNorm:ℝ)/Z^w)^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        branch*sigma+delta+reserve+eps*Real.logb Z V):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hnc:=norm_pos C hC.1
  have hnd:=norm_pos D hD.1
  have hne:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hnr:=active_norm_pos C D
  have hnq:=norm_pos _ τ.modulus_ne_bot
  have hη:=norm_pos _ η.modulus_ne_bot
  have hf:=fixedPresentationCost_pos
  have hc:0≤ Real.logb Z (C.absNorm:ℝ):=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1))
  have hd:0≤ Real.logb Z (D.absNorm:ℝ):=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1))
  have hallow:=allowance_nonneg C D Z
  have hfix:=fixed_presentation_log_nonneg Z hZ
  have hm:max (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)-2*w+wo) 0≤
      Real.logb Z (D.absNorm:ℝ)+wo:=max_le (by linarith) (by linarith)
  have he:eps*(Real.logb Z (C.absNorm:ℝ)+w)≥0:=mul_nonneg heps (add_nonneg hc hw)
  have hq:=actual_reference_width η τ C D hC E K Z hK hZ hmod
  have hnom:nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z=
      Real.logb Z ((Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)+2*Real.logb Z V-
      Real.logb Z K-Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ):=by
    rw [nominalLog,nominal_equal_support C D _ hC.1 hD.1 hCD K V]
    simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow]
    ring
  dsimp only
  apply (Real.logb_le_iff_le_rpow hZ (by positivity)).mp
  simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_rpow hz hZ.ne',Real.logb_rpow_eq_mul_logb_of_pos,Real.logb_pow]
  rw [hnom]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hq,hm,he,hfix,hallow]

theorem actual_main_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve eps:ℝ)(hK:0< K)(hV:0< V)(hZ:1< Z)(heps:0≤ eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D}):
    (V/(C.absNorm:ℝ))*mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve*(V/(C.absNorm:ℝ))^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        2*sigma+delta+reserve+eps*Real.logb Z V):=by
  simpa only [mainCommonRadius,zero_mul,mul_zero,sub_zero,add_zero,neg_zero,
    Real.rpow_zero,mul_one,div_one] using
    actual_common_diagonal η τ C D hC hD hCD E K V Z 0 0 2 sigma delta reserve eps
      hK hV hZ (le_refl _) (le_refl _) heps hmod

theorem actual_error_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve eps:ℝ)(hK:0< K)(hV:0< V)(hZ:1< Z)(heps:0≤ eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    (V/(C.absNorm:ℝ))*localErrorCost p (k-1)*errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k*(V/(C.absNorm:ℝ)/(normValue p)^k)^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        sigma+delta+reserve+eps*Real.logb Z V):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hpv:=normValue_pos p hp
  have hcpos:=norm_pos C hC.1
  have hqpos:=norm_pos _ τ.modulus_ne_bot
  have hl:0≤ Real.logb Z (normValue p):=Real.logb_nonneg hZ (normValue_ge_one p hp)
  have hw:0≤ errorRemoval p Z k:=by unfold errorRemoval;positivity
  have hwo:0≤ errorMoving p Z k:=by unfold errorMoving;split_ifs <;> positivity
  have hh:=actual_common_diagonal η τ C D hC hD hCD E K V Z
    (errorRemoval p Z k) (errorMoving p Z k) 1 sigma delta reserve eps hK hV hZ hw hwo heps hmod
  dsimp only at hh
  rw [one_mul,errorRemoval_power p hp Z hZ k] at hh
  apply le_trans ?_ hh
  unfold errorCommonRadius
  gcongr
  exact actual_error_weight p hp Z hZ k hk

end CenteredMomentFirstMixedDiagonal

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
