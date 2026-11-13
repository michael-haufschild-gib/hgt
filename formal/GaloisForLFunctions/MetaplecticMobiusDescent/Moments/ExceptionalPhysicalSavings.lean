/-
Exceptional physical savings adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.SecondPhysicalBlocks

/-!
# Exceptional physical savings

Profile factors and source budgets of physical exceptional profiles; live rows and the second
physical ledger; the saved and uniform exceptional blocks.
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

namespace CenteredMomentSecondExceptionalKernel
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentMobiusRegroup CenteredMomentFixedRay CenteredMomentRowNorm
open CenteredMomentSmooth CenteredMomentCauchy CenteredMomentPlainChildEnergy
open CenteredMomentSecondScaled CenteredMomentExceptionalKernel RayFourExpansion
local notation "O" => Eisenstein.O

theorem whole_kernel_divisor_pair (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ)
    (M : Fin 4→ℝ) (hM : ∀i,0≤ M i)
    (hV : ∀i y,V i y≠0→|y|≤ M i) (A J : ℕ) :
    ∃C:ℝ,0≤ C ∧ ∀R:ℝ,0< R →
      ∀{α β:Type*}(Ls:Finset (Ideal O))(rows:Finset O)(S:Finset α)(T:Finset β)
        (a:α→O)(b:β→O)(c:Ideal O→α→ℂ)(d:Ideal O→β→ℂ)
        (u:α→ℝ)(v:β→ℝ)(ρ x:O→ℝ)(η:O→ℂ),
      (∀z∈rows,‖η z‖≤1) → (∀z∈rows,‖V 0 (ρ z)‖≤1) →
      (∀z∈rows,‖V 1 (x z)‖≤1) → ∀E:ℝ,0≤ E →
      (∀t:ℝ,(∑L∈Ls,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
        ∑z∈rows,‖rowPolynomial S a (fun i=> c L i*columnPhase (V 2) (u i) t) z‖*
          ‖rowPolynomial T b (fun j=> d L j*star (columnPhase (V 3) (v j) t)) (-z)‖)
        ≤ E*(1+‖t‖)^J) →
      (1+R)^A*‖∑L∈Ls,(UniqueFactorizationMonoid.moebius L:ℂ)*
        ∑z∈rows,η z*∑i∈S,∑j∈T,
          ((c L i*idealRowHom z (Ideal.span {a i}))*
            star (d L j*idealRowHom (-z) (Ideal.span {b j})))*
              wholeKernel W V R (ρ z) (x z) (u i) (v j)‖≤ C*E := by
  obtain ⟨C,hC,hbound⟩:=whole_kernel_paired_row_estimate W V M hM hV A J
  refine ⟨C,hC,?_⟩
  intro R hR α β Ls rows S T a b c d u v ρ x η hη hV₀ hV₁ E hE he
  have hh:=hbound R hR (Ls×ˢrows) S T
    (fun k i=>(UniqueFactorizationMonoid.moebius k.1:ℂ)*(c k.1 i*idealRowHom k.2 (Ideal.span {a i})))
    (fun k j=> d k.1 j*idealRowHom (-k.2) (Ideal.span {b j})) u v
    (fun k=>ρ k.2) (fun k=> x k.2) (fun k=>η k.2)
    (fun k hk=> hη k.2 (Finset.mem_product.mp hk).2)
    (fun k hk=> hV₀ k.2 (Finset.mem_product.mp hk).2)
    (fun k hk=> hV₁ k.2 (Finset.mem_product.mp hk).2) E hE
  have hl (L:Ideal O)(z:O)(t:ℝ):
      leftColumn S (fun i=>(UniqueFactorizationMonoid.moebius L:ℂ)*(c L i*idealRowHom z (Ideal.span {a i})))
        (V 2) u t=(UniqueFactorizationMonoid.moebius L:ℂ)*
          rowPolynomial S a (fun i=> c L i*columnPhase (V 2) (u i) t) z := by
    rw [←leftColumn_eq_rowPolynomial]
    unfold leftColumn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hp:∀t:ℝ,(∑k∈Ls×ˢrows,
      ‖leftColumn S (fun i=>(UniqueFactorizationMonoid.moebius k.1:ℂ)*(c k.1 i*idealRowHom k.2 (Ideal.span {a i}))) (V 2) u t‖*
      ‖rightColumn T (fun j=> d k.1 j*idealRowHom (-k.2) (Ideal.span {b j})) (V 3) v t‖)
      ≤ E*(1+‖t‖)^J:=by
    intro t
    simp only [Finset.sum_product,hl,rightColumn_eq_star_rowPolynomial,norm_star,norm_mul,mul_assoc,←Finset.mul_sum]
    exact he t
  have hout:=hh hp
  apply hout.trans_eq'
  congr 2
  simp only [Finset.sum_product,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L hL
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem weighted_norm_sum {α:Type*} (S:Finset α)(a f:α→ℂ)
    (r:ℝ)(hr:0≤ r)(B:α→ℝ)(hB:∀i∈S,r*‖f i‖≤ B i):
    r*‖∑i∈S,a i*f i‖≤∑i∈S,‖a i‖*B i:=by
  calc
    _≤ r*∑i∈S,‖a i*f i‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
    _=∑i∈S,‖a i‖*(r*‖f i‖):=by simp only [Finset.mul_sum,norm_mul];congr 1;funext i;ring
    _≤ _:=Finset.sum_le_sum (fun i hi=> mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _))

theorem whole_kernel_actual_second_pair (W : 𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (M:Fin 4→ℝ)(hM:∀i,0≤ M i)(hV:∀i y,V i y≠0→|y|≤ M i)(A J:ℕ):
    ∃C:ℝ,0≤ C ∧ ∀R:ℝ,0< R →
      ∀{α β:Type*}(rows:Finset O)(S:Finset α)(T:Finset β)
        (D E A₀:O)(a:α→O)(b:β→O)
        (hD:Supported (Ideal.span {D}))(hE:Supported (Ideal.span {E}))
        (ha:∀i,Supported (Ideal.span {a i}))(hb:∀j,Supported (Ideal.span {b j})),
      (lambda^2∣D-1) →
      (lambda^2∣E-1) →
      (∀i,lambda^2∣a i-1) →
      (∀j,lambda^2∣b j-1) →
      (∀i,IsCoprime (D*E) (a i)) → (∀j,IsCoprime (D*E) (b j)) →
      ∀(q:O→ℂ)(c:α→ℂ)(d:β→ℂ)(u:α→ℝ)(v:β→ℝ)(ρ x:O→ℝ),
      (∀z∈rows,‖q z*actualCorrelation D E hD hE (A₀*z)‖≤1) →
      (∀z∈rows,‖V 0 (ρ z)‖≤1) → (∀z∈rows,‖V 1 (x z)‖≤1) →
      ∀E0:ℝ,0≤ E0 →
      (∀χ ξ:RayCharacter,∀t:ℝ,
        (∑L∈divisorPool T (fun j=> Ideal.span {b j}),‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
          ∑z∈rows,
            ‖rowPolynomial S a (fun i=> divisorCoefficient L a (movingCoefficient A₀ a c) χ i*
              columnPhase (V 2) (u i) t) z‖*
            ‖rowPolynomial T b (fun j=> divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) j*
              star (columnPhase (V 3) (v j) t)) (-z)‖)≤ E0*(1+‖t‖)^J) →
      (1+R)^A*‖∑z∈rows,q z*∑i∈S,∑j∈T,
        (if IsCoprime (a i) (b j) then actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0)*(c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖≤ C*E0:=by
  obtain ⟨C,hC,hbound⟩:=whole_kernel_divisor_pair W V M hM hV A J
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x hq hV₀ hV₁ E0 hE0 hpair
  rw [actual_scaled_row_children rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  let f:RayCharacter→RayCharacter→ℂ:=fun χ ξ=>
    ∑L∈divisorPool T (fun j=> Ideal.span {b j}),(UniqueFactorizationMonoid.moebius L:ℂ)*
      ∑z∈rows,(q z*actualCorrelation D E hD hE (A₀*z))*∑i∈S,∑j∈T,
        ((divisorCoefficient L a (movingCoefficient A₀ a c) χ i*idealRowHom z (Ideal.span {a i}))*
          star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j})))*
            wholeKernel W V R (ρ z) (x z) (u i) (v j)
  have hf:∀χ ξ,(1+R)^A*‖f χ ξ‖≤ C*E0:=by
    intro χ ξ
    exact hbound R hR _ rows S T a b
      (fun L=> divisorCoefficient L a (movingCoefficient A₀ a c) χ)
      (fun L=> divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹))
      u v ρ x (fun z=> q z*actualCorrelation D E hD hE (A₀*z)) hq hV₀ hV₁ E0 hE0 (hpair χ ξ)
  have heq:(∑L∈divisorPool T (fun j=> Ideal.span {b j}),
      (UniqueFactorizationMonoid.moebius L:ℂ)*∑χ:RayCharacter,∑ξ:RayCharacter,
        pairCoeff (phaseTable D E) χ ξ *
          ∑z∈rows,(q z*actualCorrelation D E hD hE (A₀*z))*∑i∈S,∑j∈T,
            ((divisorCoefficient L a (movingCoefficient A₀ a c) χ i*idealRowHom z (Ideal.span {a i}))*
              star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j})))*
                wholeKernel W V R (ρ z) (x z) (u i) (v j))=
        ∑χ:RayCharacter,∑ξ:RayCharacter,pairCoeff (phaseTable D E) χ ξ*f χ ξ:=by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ξ hξ
    unfold f
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro L hL
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq]
  calc
    _≤∑χ:RayCharacter,∑ξ:RayCharacter,‖pairCoeff (phaseTable D E) χ ξ‖*(C*E0):=by
      have hh:=weighted_norm_sum Finset.univ (fun _:RayCharacter=>(1:ℂ))
        (fun χ=>∑ξ:RayCharacter,pairCoeff (phaseTable D E) χ ξ*f χ ξ) ((1+R)^A) (by positivity)
        (fun χ=>∑ξ:RayCharacter,‖pairCoeff (phaseTable D E) χ ξ‖*(C*E0))
        (fun χ _=> weighted_norm_sum Finset.univ _ _ ((1+R)^A) (by positivity) _ (fun ξ _=> hf χ ξ))
      simpa only [one_mul,norm_one] using hh
    _=(∑χ:RayCharacter,∑ξ:RayCharacter,‖pairCoeff (phaseTable D E) χ ξ‖)*(C*E0):=by
      simp only [Finset.sum_mul]
    _≤256*(C*E0):=mul_le_mul_of_nonneg_right (phaseTable_mass D E) (mul_nonneg hC hE0)
    _=(256*C)*E0:=by ring

open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSupport CenteredMomentRestrictedEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentChildRows CenteredExceptionalProfile

theorem exceptional_rows_pair (η:Character)(χ₀ χ ξ:RayCharacter)(Q:Ideal O)
    (hQ:Q≤ Ideal.span {(72:O)})(m A:O)(hmLam:lambda∣m)
    (hm2:(2:O)∣m)(rows:Finset O)
    (hrows:∀z∈rows,FixedInducingRow (childCharacter η χ₀) Q m A z):
    (∀z∈rows,FixedInducingRow (childCharacter η χ) Q m A z) ∧
    (∀z∈rows,FixedInducingRow (childCharacter η (ξ⁻¹)) Q m A (-z)):=by
  constructor
  · intro z hz
    have hh:=CenteredMomentExceptionalReflection.fixedInducingRow_reflected
      η χ₀ χ₀ Q hQ m A z hmLam hm2 (hrows z hz)
    simpa only [neg_neg] using
      CenteredMomentExceptionalReflection.fixedInducingRow_reflected
        η χ₀ χ Q hQ m A (-z) hmLam hm2 hh
  · intro z hz
    exact CenteredMomentExceptionalReflection.fixedInducingRow_reflected
      η χ₀ (ξ⁻¹) Q hQ m A z hmLam hm2 (hrows z hz)

theorem actual_exceptional_block_bound (W:𝓢(ℝ,ℂ))(decay J:ℕ):
    ∃B:ℝ,0≤ B ∧ ∀r:ℝ,0< r →
      ∀(η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
        (C D:Ideal O)(hC:Supported C)(hD:Supported D),
      primeSupport C=primeSupport D →
      ∀(U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)
        (ρ x:O→ℝ)(u:sectorPool C hC.1 S→ℝ)(v:sectorPool D hD.1 S→ℝ)
        (Q:Ideal O)(m:O)(χ₀:RayCharacter),
      Q≤ Ideal.span {(72:O)} → lambda∣m → (2:O)∣m →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let c:=fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I
      let d:=fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I
      (∀z∈rows,FixedInducingRow (childCharacter η χ₀) Q m A z) →
      ∀E:ℝ,0≤ E →
      (∀χ ξ:RayCharacter,
        (∀z∈rows,FixedInducingRow (childCharacter η χ) Q m A z) →
        (∀z∈rows,FixedInducingRow (childCharacter η (ξ⁻¹)) Q m A (-z)) →
        ∀w:ℝ,
        (∑L∈divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*∑z∈rows,
          ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
            (fun I=> divisorCoefficient L (sectorElement C hC.1 S)
              (movingCoefficient A (sectorElement C hC.1 S) c) χ I*columnPhase logAnnulus (u I) w) z‖*
          ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
            (fun I=> divisorCoefficient L (sectorElement D hD.1 S)
              (movingCoefficient A (sectorElement D hD.1 S) d) (ξ⁻¹) I*star (columnPhase logAnnulus (v I) w)) (-z)‖)
          ≤ E*(1+‖w‖)^J) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            (c I*star (d J))*wholeKernel W (fun _=> logAnnulus) r (ρ z) (x z) (u I) (v J)‖≤ B*E:=by
  obtain ⟨B,hB,hbound⟩:=whole_kernel_actual_second_pair W (fun _=> logAnnulus)
    (fun _=> Real.log 4) (fun _=> Real.log_nonneg (by norm_num))
    (fun _ x hx=> CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure x hx) decay J
  refine ⟨B,hB,?_⟩
  intro r hr η t S β C D hC hD hCD U R rows ρ x u v Q m χ₀ hQ hmLam hm2
  dsimp only
  intro hrows E hE hpair
  have hcopD (I:sectorPool D hD.1 S):
      IsCoprime (primaryIdealGenerator C*primaryIdealGenerator D) (sectorElement D hD.1 S I):=by
    simpa only [mul_comm] using sectorElement_coprime D C hD hC hCD.symm S I
  have he:=hbound r hr rows Finset.univ Finset.univ (primaryIdealGenerator C) (primaryIdealGenerator D)
    (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
    (sectorElement C hC.1 S) (sectorElement D hD.1 S)
    ((supported_span_primaryIdealGenerator_iff C).mpr hC) ((supported_span_primaryIdealGenerator_iff D).mpr hD)
    (sectorElement_supported C hC.1 S) (sectorElement_supported D hD.1 S)
    (primaryIdealGenerator_spec C (supported_primaryIdealGenerator_ne_zero C hC)).2
    (primaryIdealGenerator_spec D (supported_primaryIdealGenerator_ne_zero D hD)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary D hD.1 S)
    (sectorElement_coprime C D hC hD hCD S) hcopD
    (retainedScalar C D U R) (fun I=>β (C*I)*heightCoeff η t I)
    (fun I=>β (D*I)*heightCoeff η t I) u v ρ x
    (fun z _=> actual_retained_scalar_norm C D hC hD hCD U R z)
    (fun z _=> logAnnulus_norm _) (fun z _=> logAnnulus_norm _) E hE
  have hh:∀χ ξ:RayCharacter,∀w:ℝ,
      (∑L∈divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O)),
        ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*∑z∈rows,
        ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
          (fun I=> divisorCoefficient L (sectorElement C hC.1 S)
            (movingCoefficient (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
              (sectorElement C hC.1 S) (fun I=>β (C*I)*heightCoeff η t I)) χ I*columnPhase logAnnulus (u I) w) z‖*
        ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
          (fun I=> divisorCoefficient L (sectorElement D hD.1 S)
            (movingCoefficient (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
              (sectorElement D hD.1 S) (fun I=>β (D*I)*heightCoeff η t I)) (ξ⁻¹) I*
              star (columnPhase logAnnulus (v I) w)) (-z)‖)≤ E*(1+‖w‖)^J:=by
    intro χ ξ w
    have hg:=exceptional_rows_pair η χ₀ χ ξ Q hQ m _ hmLam hm2 rows hrows
    exact hpair χ ξ hg.1 hg.2 w
  have he':=he (by simpa only [sectorElement_span] using hh)
  have hcop (I:sectorPool C hC.1 S)(J:sectorPool D hD.1 S):
      IsCoprime (sectorElement C hC.1 S I) (sectorElement D hD.1 S J) ↔
        IsCoprime (I:Ideal O) (J:Ideal O):=by
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  have hcop' (I:sectorPool C hC.1 S)(J:sectorPool D hD.1 S):
      IsCoprime (primaryIdealGenerator (I:Ideal O)) (primaryIdealGenerator (J:Ideal O)) ↔
        IsCoprime (I:Ideal O) (J:Ideal O):=hcop I J
  simpa only [sectorElement_span,idealCorrelation,primaryIdealGenerator_mul,sectorElement,hcop'] using he'

end CenteredMomentSecondExceptionalKernel

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace CenteredMomentSecondDivisorSupport
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondExceptionalPairBound RayFourExpansion
local notation "O"=> Eisenstein.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem live_right_divisor_norm (D I L:Ideal O)(hD:D≠0)(hI:I≠0)
    (β:Ideal O→ℂ)(H:ℝ)(hβ:∀J,β J≠0→(J.absNorm:ℝ)≤ H)
    (hne:β (D*I)≠0)(hLI:L∣I):
    (L.absNorm:ℝ)≤ H/(D.absNorm:ℝ):=by
  have hDpos:(0:ℝ)< D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hnorm:(L.absNorm:ℝ)≤ I.absNorm:=by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)) (map_dvd Ideal.absNorm hLI)
  have hb:=hβ (D*I) hne
  rw [map_mul,Nat.cast_mul] at hb
  apply hnorm.trans
  apply (le_div_iff₀ hDpos).mpr
  simpa only [mul_comm] using hb

theorem right_divisor_coefficient_zero
    (D:Ideal O)(hD:Supported D)(S:Finset (Ideal O))(β:Ideal O→ℂ)(H:ℝ)
    (hβ:∀J,β J≠0→(J.absNorm:ℝ)≤ H)(L:Ideal O)(hL:H/(D.absNorm:ℝ)< L.absNorm)
    (η:Character)(t:ℝ)(A:O)(ξ:RayCharacter)(I:sectorPool D hD.1 S):
    divisorCoefficient L (sectorElement D hD.1 S)
      (movingCoefficient A (sectorElement D hD.1 S)
        (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I=0:=by
  unfold divisorCoefficient
  rw [sectorElement_span]
  split_ifs with hd
  · have hz:β (D*I)=0:=by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (sectorPool_supported D hD.1 S I).1 β H hβ hn hd)
    simp only [movingCoefficient,hz,zero_mul]
  · rfl

theorem right_divisor_row_zero
    (D:Ideal O)(hD:Supported D)(S:Finset (Ideal O))(β:Ideal O→ℂ)(H:ℝ)
    (hβ:∀J,β J≠0→(J.absNorm:ℝ)≤ H)(L:Ideal O)(hL:H/(D.absNorm:ℝ)< L.absNorm)
    (η:Character)(t:ℝ)(A:O)(ξ:RayCharacter)(v:sectorPool D hD.1 S→ℂ)(z:O):
    rowPolynomial Finset.univ (sectorElement D hD.1 S)
      (fun I=> divisorCoefficient L (sectorElement D hD.1 S)
        (movingCoefficient A (sectorElement D hD.1 S)
          (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*v I) z=0:=by
  unfold rowPolynomial
  apply Finset.sum_eq_zero
  intro I hI
  exact mul_eq_zero_of_left
    (mul_eq_zero_of_left (right_divisor_coefficient_zero D hD S β H hβ L hL η t A ξ I) _) _

theorem originalPair_filter_right {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(η:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y H:ℝ)(Ds:Finset (Ideal O))(rows:Finset O)
    (hβ:∀I:Ideal O,finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I≠0→
      (I.absNorm:ℝ)≤ H):
    originalPair s η χ ξ A C D hC hD R seed t w X Y Ds rows=
      originalPair s η χ ξ A C D hC hD R seed t w X Y
        (Ds.filter (fun L=>(L.absNorm:ℝ)≤ H/(D.absNorm:ℝ))) rows:=by
  unfold originalPair
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hLD
  by_cases hL:(L.absNorm:ℝ)≤ H/(D.absNorm:ℝ)
  · rw [if_pos hL]
  · rw [if_neg hL]
    have hz:=right_divisor_row_zero D hD (finiteColumns (Fintype.piFinset s.pools))
      (finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed))
      H hβ L (lt_of_not_ge hL) η t A ξ
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro z hzr
    apply mul_eq_zero_of_right
    exact norm_eq_zero.mpr (hz _ _)

end CenteredMomentSecondDivisorSupport

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open   CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open  CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => Eisenstein.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def sourceBudget {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
    Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=> P.val)
      (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
      2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*
    ((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*
      frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

lemma sourceBudget_nonneg {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ)(hK:0≤ K)(hZ:0≤ Z)(hCr:0≤ Cr):
    0≤ sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M:=by
  have hp:=profileMass_nonneg Sprofile s.toData s.toData p p J
  have hf:=frozenProfile_nonneg s
  have hv:0≤ volume s.toData:=(volume_pos s.toData).le
  unfold sourceBudget
  positivity

theorem actual_original_exceptional_block (wlo whi:ℝ)(hwlo:0< wlo)(hwhi:0≤ whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤ B)(hL:0≤ Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤ Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
      ∃K:ℝ,0< K ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤ Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤ Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → lambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤ Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤ Cr*Z^M) →
      ∀X Y:ℝ,0< X → 0< Y →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤ H) → H/(D.absNorm:ℝ)≤ Z^Lbound →
      ∀(R:ℝ)(ρ x:O→ℝ)(rK:ℝ),0< rK →
      (1+rK)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff s.η s.t I)*star (β (D*J)*heightCoeff s.η s.t J))*
              wholeKernel W (fun _=> logAnnulus) rK (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M:=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_canonical_original_pair wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  obtain ⟨Ck,hCk,hkernel⟩:=actual_exceptional_block_bound W decay (2*J)
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN X Y hX hY H hβ hHD R ρ x rK hrK
  apply hkernel rK hrK s.η s.t S β C D hC hD hCD U R rows ρ x
    (fun I=> Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
    (fun I=> Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) Q m χ₀ hQ72 hml hm2 hex
    (sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M)
    (sourceBudget_nonneg Sprofile s p J Q C D U K Z ε δ θ r Cr M hK.le (zero_lt_one.trans hZ.1).le hCr)
  intro χ ξ _ _ w
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD r
    hX₁ hX₂ hY₁ hY₂ (τ χ) (τ (ξ⁻¹)) χ (ξ⁻¹) A
    (fun I hI hc v=> hτ χ I hI (Or.inl hc) v)
    (fun I hI hc v=> hτ (ξ⁻¹) I hI (Or.inr hc) v)
    rows hn (hex₁ χ) (hex₂ (ξ⁻¹)) (hcond₁ χ) (hcond₂ (ξ⁻¹))
    s.η χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN X Y hX hY
    ((divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))).filter
      (fun L=>(L.absNorm:ℝ)≤ H/(D.absNorm:ℝ)))
    (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hHD) w
  change originalPair s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y
    (divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))) rows≤ _
  rw [originalPair_filter_right s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y H _ rows hβ]
  exact hp

end CenteredMomentFiniteProfileExceptionalPhysical

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open   CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open  CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => Eisenstein.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_physical_exceptional_block (wlo whi:ℝ)(hwlo:0< wlo)(hwhi:0≤ whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤ B)(hL:0≤ Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤ Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
      ∃K:ℝ,0< K ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤ Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤ Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → lambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤ Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤ Cr*Z^M) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤ H) → H/(D.absNorm:ℝ)≤ Z^Lbound →
      ∀(R Kphys:ℝ),0< Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_original_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN H hβ hHD R Kphys hKphys n rK
  have hrK:0< rK:=div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hh:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN (dyadicScale (n 2)) (dyadicScale (n 3))
    (dyadicScale_pos _) (dyadicScale_pos _) H hβ hHD R
    (fun _=> Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
    (fun z=> Real.log (normValue z/dyadicScale (n 1))) rK hrK
  change (1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤ _ at hh
  have ho:0≤ outerScalar C D Kphys n:=by unfold outerScalar; positivity
  have hno:0≤ normalizer C D U:=(normalizer_pos C D hC U).le
  rw [physicalBlock_eq s.η s.t S β C D hC hD U R rows hn W Kphys hKphys n,
    norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno]
  calc
    _=(outerScalar C D Kphys n*normalizer C D U)*
        ((1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖):=by ring
    _≤ _:=mul_le_mul_of_nonneg_left hh (mul_nonneg ho hno)

end CenteredMomentFiniteProfileExceptionalPhysical

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentSourceDyadicShell
open CenteredMomentSectorLocalization 
local notation "O" => Eisenstein.O

lemma residual_window_bounds (C I:Ideal O) (hC:C≠0) (L U:ℝ) (n:ℤ)
    (hL:L≤(Ideal.absNorm (C*I):ℝ)) (hU:(Ideal.absNorm (C*I):ℝ)≤ U)
    (hw:dyadicWeight n (Ideal.absNorm I:ℝ)≠0) :
    L/(Ideal.absNorm C:ℝ)≤ dyadicScale n ∧
      dyadicScale n≤4*U/(Ideal.absNorm C:ℝ) := by
  have hc:(0:ℝ)< Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hs:=dyadicWeight_support n hw
  simp only [map_mul,Nat.cast_mul] at hL hU
  constructor
  · apply (div_le_iff₀ hc).mpr
    exact hL.trans (by nlinarith [hs.2])
  · apply (le_div_iff₀ hc).mpr
    nlinarith [hs.1]

lemma raw_window_lower (C I:Ideal O) (hC:C≠0) (a H:ℝ) (ha:0< a) (n:ℤ)
    (hL:a*H≤(Ideal.absNorm (C*I):ℝ))
    (hw:dyadicWeight n (Ideal.absNorm I:ℝ)≠0) :
    H/(Ideal.absNorm C:ℝ)≤ dyadicScale n/a := by
  have hc:(0:ℝ)< Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hs:=(dyadicWeight_support n hw).2.le
  simp only [map_mul,Nat.cast_mul] at hL
  apply (div_le_div_iff₀ hc ha).mpr
  nlinarith

end CenteredMomentSourceDyadicShell

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentSourceBlockWindows
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSourceDyadicShell CenteredMomentHeckeColumnWindow
local notation "O" => Eisenstein.O

 theorem physicalBlock_column_witnesses (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃I:sectorPool C hC.1 S,∃J:sectorPool D hD.1 S,
      β (C*I)≠0 ∧ β (D*J)≠0 ∧
      dyadicWeight (n 2) (Ideal.absNorm (I:Ideal O):ℝ)≠0 ∧
      dyadicWeight (n 3) (Ideal.absNorm (J:Ideal O):ℝ)≠0 := by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hcoeff: (β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J)≠0:=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hterm).1).2
    have hl:β (C*I)≠0:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hcoeff).1).1
    have hr:β (D*J)≠0:=by
      intro hh
      exact hcoeff (by rw [hh,zero_mul,star_zero,mul_zero])
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    exact ⟨I,J,hl,hr,(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).2,(mul_ne_zero_iff.mp hw).2⟩
  · exact False.elim (hz rfl)

 theorem physicalBlock_scale_lower (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (a H:ℝ) (ha:0< a) (hlower:∀I:Ideal O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    H/(Ideal.absNorm C:ℝ)≤ dyadicScale (n 2)/a ∧
      H/(Ideal.absNorm D:ℝ)≤ dyadicScale (n 3)/a := by
  obtain ⟨I,J,hI,hJ,hwi,hwj⟩:=physicalBlock_column_witnesses η t S β C D hC hD U R rows W K n hne
  exact ⟨raw_window_lower C I hC.1 a H ha (n 2) (hlower _ hI) hwi,
    raw_window_lower D J hD.1 a H ha (n 3) (hlower _ hJ) hwj⟩

end CenteredMomentSourceBlockWindows

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentSecondPhysicalCost
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondCanonicalFrequency
open CenteredMomentCanonicalFirst CenteredMomentLogDyadic CenteredMomentSupport
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
local notation "O" => Eisenstein.O

theorem actual_normalized_prefactor (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (K:ℝ) (n:Fin 4→ℤ) :
    outerScalar C D K n*normalizer C D U*
      Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/
        (Real.sqrt (C.absNorm:ℝ)*Real.sqrt (D.absNorm:ℝ)*(∏P∈U,P.val).absNorm) := by
  have hcp:0<(C.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hdp:0<(D.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hx:=Real.sqrt_pos.mpr (dyadicScale_pos (n 2))
  have hy:=Real.sqrt_pos.mpr (dyadicScale_pos (n 3))
  rw [normalizer,actual_partitionNormalizer C D hC,outerScalar,
    Real.sqrt_mul (dyadicScale_pos (n 2)).le]
  field_simp

lemma logb_sqrt (Z x:ℝ) (hx:0< x) : Real.logb Z (Real.sqrt x)=Real.logb Z x/2 := by
  rw [Real.sqrt_eq_rpow,Real.logb_rpow_eq_mul_logb_of_pos hx]
  ring

theorem actual_prefactor_log (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (K Z:ℝ) (hK:0< K) (n:Fin 4→ℤ) :
    Real.logb Z (outerScalar C D K n*normalizer C D U*
      Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))=
      Real.logb Z K+
      Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)-
      (Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/2-
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ) := by
  have hc:0<(C.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hg:0<(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by simpa only [Ideal.span_singleton_eq_bot] using commonFrequencyGenerator_ne_zero C D hC))
  have hu:0<((∏P∈U,P.val).absNorm:ℝ) := by
    rw [map_prod,Nat.cast_prod]
    apply Finset.prod_pos
    intro P hP
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by rw [←commonPrime_span C D hC P]; exact (commonPrime_supported C D hC P).1))
  rw [actual_normalized_prefactor C D hC hD,
    Real.logb_div (mul_pos hK hg).ne' (mul_pos (mul_pos (Real.sqrt_pos.mpr hc) (Real.sqrt_pos.mpr hd)) hu).ne',
    Real.logb_mul hK.ne' hg.ne',
    Real.logb_mul (mul_pos (Real.sqrt_pos.mpr hc) (Real.sqrt_pos.mpr hd)).ne' hu.ne',
    Real.logb_mul (Real.sqrt_pos.mpr hc).ne' (Real.sqrt_pos.mpr hd).ne',
    logb_sqrt Z _ hc,logb_sqrt Z _ hd]
  ring

end CenteredMomentSecondPhysicalCost

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentSecondPhysicalLedger
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSourceBlockWindows CenteredMomentSecondPhysicalCost
open CenteredMomentSupport CenteredMomentHeckeColumnWindow
open CenteredMomentSecondCanonicalLedger CenteredMomentForcing
open CenteredMomentSecondSectorFrequency CenteredMomentFirstWholeKernel
open CenteredMomentSmooth
local notation "O" => Eisenstein.O

theorem physicalBlock_effective_window (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K
      < dyadicScale (n 0) := by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    exact (dyadicWeight_support (n 0)
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).1).1).2
  · exact False.elim (hz rfl)

lemma logb_one_add_sixth (Z x:ℝ) (hZ:1< Z) (hx:0< x) :
    Real.logb Z x/6≤ Real.logb Z (1+x) := by
  have hp:0≤ Real.logb Z (1+x):=Real.logb_nonneg hZ (by linarith)
  have hm:=Real.logb_le_logb_of_le hZ hx (show x≤1+x by linarith)
  linarith

theorem scalar_log_ledger (Z c d g u v f p K H a k₀ h₀ A B:ℝ)
    (hZ:1< Z) (hc:0< c) (hd:0< d) (hg:0< g) (hu:0< u) (hv:0< v)
    (hf:0< f) (hp:0< p) (hK:0< K) (hH:0< H) (ha:0< a)
    (hk₀:0< k₀) (hh₀:0< h₀) (hA:0< A) (hB:0< B)
    (hk:K*g*v/(c*d)≤ k₀) (hleft:a*H/c≤ A) (hright:a*H/d≤ B) :
    Real.logb Z (K*g/(Real.sqrt c*Real.sqrt d*u*Real.sqrt A*Real.sqrt B)*
      h₀^(1/6:ℝ)/(1+k₀*h₀/(A*B))*H/(c*d)*p/f^(1/3:ℝ))≤
      Real.logb Z H/3+5*Real.logb Z K/6-2*Real.logb Z a/3-
      (Real.logb Z c+Real.logb Z d-5*Real.logb Z g/6-Real.logb Z p+
        Real.logb Z u+Real.logb Z v/6+Real.logb Z f/3) := by
  have hklog:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos (mul_pos hK hg) hv) (mul_pos hc hd)) hk
  have hl:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hc) hleft
  have hr:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hd) hright
  have hdec:=logb_one_add_sixth Z (k₀*h₀/(A*B)) hZ (by positivity)
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul (by positivity) hv.ne',Real.logb_mul hK.ne' hg.ne',
    Real.logb_mul hc.ne' hd.ne'] at hklog
  rw [Real.logb_div (by positivity) hc.ne',Real.logb_mul ha.ne' hH.ne'] at hl
  rw [Real.logb_div (by positivity) hd.ne',Real.logb_mul ha.ne' hH.ne'] at hr
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul hk₀.ne' hh₀.ne',Real.logb_mul hA.ne' hB.ne'] at hdec
  simp (disch := positivity) only [Real.logb_div,
    Real.logb_mul,
    Real.logb_rpow_eq_mul_logb_of_pos hh₀,
    Real.logb_rpow_eq_mul_logb_of_pos hf,
    logb_sqrt Z c hc,logb_sqrt Z d hd,logb_sqrt Z A hA,logb_sqrt Z B hB]
  linarith

def forcingNorm (C D:Ideal O) (U:Finset (CommonIndex C D)) : ℝ :=
  Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=> P.val)
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U))

def saving (C D:Ideal O) (U:Finset (CommonIndex C D)) (Z:ℝ) : ℝ :=
  Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
    5*Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/6-
    Real.logb Z (Ideal.absNorm (∏ P:CommonIndex C D,P.val):ℝ)+
    Real.logb Z (Ideal.absNorm (∏ P∈U,P.val):ℝ)+
    Real.logb Z (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ)/6+
    Real.logb Z (forcingNorm C D U)/3

def centralPhysicalCost (C D:Ideal O) (U:Finset (CommonIndex C D))
    (K H:ℝ) (n:Fin 4→ℤ) : ℝ :=
  (1/H)*outerScalar C D K n*normalizer C D U*
    (dyadicScale (n 1))^(1/6:ℝ)/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))*
    (H^2/((C.absNorm:ℝ)*D.absNorm))*(Ideal.absNorm (∏ P:CommonIndex C D,P.val):ℝ)/
    (forcingNorm C D U)^(1/3:ℝ)

lemma common_product_pos (C D:Ideal O) (hC:Supported C) (V:Finset (CommonIndex C D)) :
    (0:ℝ)< Ideal.absNorm (∏P∈V,P.val) := by
  rw [map_prod,Nat.cast_prod]
  apply Finset.prod_pos
  intro P hP
  rw [←commonPrime_span C D hC P]
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (commonPrime_supported C D hC P).1)

theorem actual_physical_log_ledger (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hK:0< K) (H a Z:ℝ) (hH:0< H) (ha:0< a) (hZ:1< Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    Real.logb Z (centralPhysicalCost C D U K H n)≤
      Real.logb Z H/3+5*Real.logb Z K/6-2*Real.logb Z a/3-saving C D U Z := by
  have hc:(0:ℝ)< C.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:(0:ℝ)< D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hg:(0:ℝ)< Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by simpa only [Ideal.span_singleton_eq_bot] using commonFrequencyGenerator_ne_zero C D hC))
  have hv:(0:ℝ)< Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by simpa only [Ideal.span_singleton_eq_bot] using nonunitFrequencyGenerator_ne_zero C D hC U))
  have hu:=common_product_pos C D hC U
  have hp:=common_product_pos C D hC Finset.univ
  have hf:0< forcingNorm C D U:=common_product_pos C D hC _
  have hw:=physicalBlock_scale_lower η t S β C D hC hD U R rows W K n a H ha hlower hne
  have hl:a*H/(C.absNorm:ℝ)≤ dyadicScale (n 2):=by
    have hh: H/(C.absNorm:ℝ)*a≤ dyadicScale (n 2):=(le_div_iff₀ ha).mp hw.1
    convert hh using 1 <;> first | rfl | ring
  have hr:a*H/(D.absNorm:ℝ)≤ dyadicScale (n 3):=by
    have hh: H/(D.absNorm:ℝ)*a≤ dyadicScale (n 3):=(le_div_iff₀ ha).mp hw.2
    convert hh using 1 <;> first | rfl | ring
  have hk:=physicalBlock_effective_window η t S β C D hC hD U R rows W K n hne
  have he:secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)*
        Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U})/((C.absNorm:ℝ)*D.absNorm):=by
    simp only [secondEffectiveScale,map_mul,norm_mul,mul_pow,
      ringComplex_norm_sq_eq_absNorm_span]
    ring
  rw [he] at hk
  have hb:=scalar_log_ledger Z (C.absNorm:ℝ) (D.absNorm:ℝ)
    (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)
    (Ideal.absNorm (∏P∈U,P.val):ℝ)
    (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ)
    (forcingNorm C D U) (Ideal.absNorm (∏P:CommonIndex C D,P.val):ℝ)
    K H a (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))
    hZ hc hd hg hu hv hf hp hK hH ha (dyadicScale_pos _) (dyadicScale_pos _)
    (dyadicScale_pos _) (dyadicScale_pos _) hk.le hl hr
  change _≤ Real.logb Z H/3+5*Real.logb Z K/6-2*Real.logb Z a/3-saving C D U Z at hb
  convert hb using 1
  congr 1
  rw [centralPhysicalCost,normalizer,actual_partitionNormalizer C D hC,outerScalar]
  field_simp

lemma centralPhysicalCost_pos (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (K H:ℝ) (hK:0< K) (hH:0< H) (n:Fin 4→ℤ) :
    0< centralPhysicalCost C D U K H n := by
  have hc:(0:ℝ)< C.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:(0:ℝ)< D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hf:0< forcingNorm C D U:=common_product_pos C D hC _
  have hp:=common_product_pos C D hC Finset.univ
  have hu:=normalizer_pos C D hC U
  have hn0:=dyadicScale_pos (n 0)
  have hn1:=dyadicScale_pos (n 1)
  have hn2:=dyadicScale_pos (n 2)
  have hn3:=dyadicScale_pos (n 3)
  unfold centralPhysicalCost outerScalar
  positivity

theorem actual_physical_cost_bound (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hK:0< K) (H a Z:ℝ) (hH:0< H) (ha:0< a) (hZ:1< Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    centralPhysicalCost C D U K H n≤
      H^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*Z^(-saving C D U Z) := by
  have hh:=actual_physical_log_ledger η t S β C D hC hD U R rows W K n hK H a Z hH ha hZ hlower hne
  apply (Real.logb_le_logb hZ (centralPhysicalCost_pos C D hC hD U K H hK hH n)
    (show 0< H^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*Z^(-saving C D U Z) by positivity)).mp
  simp (disch := positivity) only [Real.logb_mul,
    Real.logb_rpow_eq_mul_logb_of_pos hH,Real.logb_rpow_eq_mul_logb_of_pos hK,
    Real.logb_rpow_eq_mul_logb_of_pos ha,Real.logb_rpow (by linarith : 0< Z) hZ.ne']
  linarith

theorem actual_canonical_physical_cost (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (w:O) (hpart:canonicalPartition C D U w)
    (hcorr:idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0)
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hK:0< K) (H a Z:ℝ) (hH:0< H) (ha:0< a) (hZ:1< Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    centralPhysicalCost C D U K H n≤
      H^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*
        Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3) := by
  have hs:=actual_second_ledger_lower C D hC hD hCD U w hpart Z hZ hcorr
  change (Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3≤ saving C D U Z at hs
  exact (actual_physical_cost_bound η t S β C D hC hD U R rows W K n hK H a Z hH ha hZ hlower hne).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) (by positivity))

theorem physicalBlock_canonical_witness (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (hrows:∀z∈rows,z≠0) (W:𝓢(ℝ,ℂ))
    (K:ℝ) (hK:0< K) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,canonicalPartition C D U (nonunitFrequencyGenerator C D U*z) ∧
      idealCorrelation C D hC hD
        (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  rw [physicalBlock_eq η t S β C D hC hD U R rows hrows W K hK n] at hne
  have hn:=right_ne_zero_of_mul hne
  unfold normalizedBlock at hn
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hn
  have hr:=left_ne_zero_of_mul hz
  have hpart:canonicalPartition C D U (nonunitFrequencyGenerator C D U*z):=by
    by_contra hp
    simp only [retainedScalar,canonicalPartitionScalar,hp,ite_false,zero_mul] at hr
    exact hr rfl
  refine ⟨z,hzr,hpart,?_⟩
  intro hc
  let F:O→Ideal O→Ideal O→ℂ:=fun _ I J=>
    wholeKernel W (fun _=> CenteredMomentLogDyadic.logAnnulus)
      (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
      (Real.log (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/
        dyadicScale (n 0))) (Real.log (normValue z/dyadicScale (n 1)))
      (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
      (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))
  have he:=sectorFrequency_zero_of_common η t S β C D hC hD hCD F
    ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z)
    (by simpa only [mul_assoc] using hc)
  exact (right_ne_zero_of_mul hz) (by simpa only [sectorFrequency,F] using he)

theorem original_block_physical_cost (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (hrows:∀z∈rows,z≠0) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hK:0< K) (H a Z:ℝ) (hH:0< H) (ha:0< a) (hZ:1< Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    centralPhysicalCost C D U K H n≤
      H^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*
        Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3) := by
  obtain ⟨z,hz,hpart,hcorr⟩:=physicalBlock_canonical_witness η t S β C D hC hD hCD U R rows hrows W K hK n hne
  exact actual_canonical_physical_cost η t S β C D hC hD hCD U _ hpart hcorr R rows W K n
    hK H a Z hH ha hZ hlower hne

end CenteredMomentSecondPhysicalLedger

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CenteredMomentSecondRetainedWidth
open CenteredMomentSectorLocalization
local notation "O" => Eisenstein.O
theorem retained_geometry (R : ℝ) (G V z : O)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    0< R ∧ G≠0 ∧ V≠0 ∧ z≠0 ∧ 1≤ normValue z ∧
      normValue z≤4*R/(normValue G*normValue V) ∧
      1≤4*R/(normValue G*normValue V) := by
  obtain ⟨hGV,hz⟩:=retained_product_ne_zero R (G*V) z hne
  have hg:=left_ne_zero_of_mul hGV
  have hv:=right_ne_zero_of_mul hGV
  have hrow:=retained_norm_enclosure R (G*V) z hGV hne
  rw [normValue_mul] at hrow
  have hn:=normValue_ge_one z hz
  have hr:=retainedWeight_enclosure R _ hne
  refine ⟨by linarith,hg,hv,hz,hn,hrow,hn.trans hrow⟩


end CenteredMomentSecondRetainedWidth

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CenteredMomentSecondLiveBlock
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open scoped BigOperators Classical SchwartzMap
local notation "O" => Eisenstein.O
def liveRows (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O):Finset O:=
  rows.filter (fun z=> retainedWeight R
    (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0)

lemma liveRows_weight (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O)
    (z:O) (hz:z∈liveRows C D U R rows):
    retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0:=
  (Finset.mem_filter.mp hz).2

lemma liveRows_geometry (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O)
    (z:O) (hz:z∈liveRows C D U R rows):
    0< R ∧ z≠0 ∧ 1≤ normValue z ∧ normValue z≤
      4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)):=by
  obtain ⟨hr,hg,hv,hz0,h1,hbound,hmax⟩:=CenteredMomentSecondRetainedWidth.retained_geometry R
    (commonFrequencyGenerator C D) (nonunitFrequencyGenerator C D U) z
    (liveRows_weight C D U R rows z hz)
  exact ⟨hr,hz0,h1,hbound⟩

lemma physicalBlock_live_rows (η:Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n:=by
  unfold physicalBlock liveRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hr:retainedWeight R
      (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))=0
  · simp only [hr,ne_eq,not_true_eq_false,physicalKernel,Complex.ofReal_zero,
      mul_zero,zero_mul,Finset.sum_const_zero,ite_self]
  · simp only [hr,ne_eq,not_false_eq_true,ite_true]

lemma physicalBlock_row_split (η:Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ) (p:O→Prop):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter p) W K n+
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter (fun z=>¬p z)) W K n:=by
  rw [physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
  unfold physicalBlock
  exact (Finset.sum_filter_add_sum_filter_not _ p _).symm


end CenteredMomentSecondLiveBlock

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentSecondDyadicRowSupport
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
local notation "O"=> Eisenstein.O

 def dyadicRows (rows:Finset O) (n:Fin 4→ℤ):Finset O:=
  rows.filter (fun z=> dyadicWeight (n 1) (normValue z)≠0)

 theorem mem_dyadicRows (rows:Finset O)(n:Fin 4→ℤ)(z:O):
    z∈dyadicRows rows n ↔ z∈rows ∧ dyadicWeight (n 1) (normValue z)≠0:=
  Finset.mem_filter

 theorem dyadicRows_subset (rows:Finset O)(n:Fin 4→ℤ):dyadicRows rows n⊆rows:=
  Finset.filter_subset _ _

 theorem dyadicRows_norm (rows:Finset O)(n:Fin 4→ℤ)(z:O)(hz:z∈dyadicRows rows n):
    dyadicScale (n 1)/4< normValue z ∧ normValue z< dyadicScale (n 1):=
  dyadicWeight_support (n 1) ((mem_dyadicRows rows n z).mp hz).2

 theorem dyadicRows_nonzero (rows:Finset O)(n:Fin 4→ℤ)(z:O)(hz:z∈dyadicRows rows n):z≠0:=by
  have hn:0< normValue z:=(div_pos (dyadicScale_pos (n 1)) (by norm_num)).trans
    (dyadicRows_norm rows n z hz).1
  intro he
  simp only [he,normValue_eq_embedding,map_zero,norm_zero,zero_pow (by decide : 2≠0)] at hn
  exact (lt_irrefl 0) hn

 theorem dyadicRows_power_cap (rows:Finset O)(n:Fin 4→ℤ)(Z:ℝ)(hZ:1< Z)
    (z:O)(hz:z∈dyadicRows rows n):
    (Ideal.absNorm (Ideal.span {z}):ℝ)≤ Z^(Real.logb Z (dyadicScale (n 1))):=by
  rw [Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (dyadicScale_pos (n 1))]
  exact (dyadicRows_norm rows n z hz).2.le

 theorem physicalBlock_dyadic_rows (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (dyadicRows rows n) W K n:=by
  unfold physicalBlock dyadicRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hd:dyadicWeight (n 1) (normValue z)=0
  · simp only [hd,ne_eq,not_true_eq_false,mul_zero,zero_mul,
      Complex.ofReal_zero,Finset.sum_const_zero,ite_self]
  · simp only [hd,ne_eq,not_false_eq_true,ite_true]

 theorem dyadicRows_liveRows (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)
    (rows:Finset O)(n:Fin 4→ℤ):
    dyadicRows (liveRows C D U R rows) n=liveRows C D U R (dyadicRows rows n):=by
  ext z
  simp only [dyadicRows,liveRows,Finset.mem_filter]
  tauto

 theorem physicalBlock_live_dyadic_rows (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (dyadicRows (liveRows C D U R rows) n) W K n:=
  (physicalBlock_live_rows η t S β C D hC hD U R rows W K n).trans
    (physicalBlock_dyadic_rows η t S β C D hC hD U R _ W K n)

end CenteredMomentSecondDyadicRowSupport

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open   CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport
open  CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => Eisenstein.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_dyadic_exceptional_block (wlo whi:ℝ)(hwlo:0< wlo)(hwhi:0≤ whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤ B)(hL:0≤ Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤ Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
      ∃K:ℝ,0< K ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤ Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤ Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → lambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤ H) → H/(D.absNorm:ℝ)≤ Z^Lbound →
      ∀(R Kphys:ℝ),0< Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_physical_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n rK
  rw [physicalBlock_dyadic_rows s.η s.t S β C D hC hD U R rows W Kphys n]
  exact hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ (dyadicRows rows n)
    (fun z hz=> dyadicRows_nonzero rows n z hz)
    (fun χ z hz=> hex₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=> hex₂ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=> hcond₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=> hcond₂ χ z (dyadicRows_subset rows n hz))
    χ₀ hcop hη m hm hml hm2 (fun z hz=> hex z (dyadicRows_subset rows n hz))
    1 (Real.logb Z (dyadicScale (n 1))) (by norm_num)
    (fun z hz=> by simpa only [one_mul] using dyadicRows_power_cap rows n Z hZ.1 z hz)
    H hβ hHD R Kphys hKphys n

end CenteredMomentFiniteProfileExceptionalPhysical

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory

namespace CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss UniqueFactorizationMonoid
open CenteredMomentSecondPhysicalLedger
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open  CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentForcing CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
local notation "O"=> Eisenstein.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma profileMass_self {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ):
    profileMass Sprofile s.toData s.toData p p J=
      p.control Sprofile^2*(1+‖s.t‖)^(2*J)*slotControl s.toData^2*volume s.toData:=by
  have hs:volume s.toData=Real.sqrt (volume s.toData)*Real.sqrt (volume s.toData):=by
    nlinarith [Real.sq_sqrt (volume_pos s.toData).le]
  unfold CenteredMomentFiniteProfileExceptionalCommon.profileMass
  rw [show 2*J=J+J by omega,pow_add]
  conv_rhs => rw [hs]
  ring

lemma count_power (Z h f e:ℝ)(hZ:1< Z)(hh:0< h)(hf:0< f):
    Z^((Real.logb Z h-4*Real.logb Z f)/6+e)=
      h^(1/6:ℝ)/f^(2/3:ℝ)*Z^e:=by
  have hz:0< Z:=zero_lt_one.trans hZ
  rw [show (Real.logb Z h-4*Real.logb Z f)/6+e=
    Real.logb Z h*(1/6)-Real.logb Z f*(2/3)+e by ring,
    Real.rpow_add hz,Real.rpow_sub hz,Real.rpow_mul hz.le,Real.rpow_mul hz.le,
    Real.rpow_logb hz (ne_of_gt hZ) hh,Real.rpow_logb hz (ne_of_gt hZ) hf]

def profileFactor {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q:Ideal O)(K:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*
    p.control Sprofile^2*(1+‖s.t‖)^(2*J)*slotControl s.toData^2*frozenProfile s^2*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

omit [DecidableEq ι] in
lemma profileFactor_nonneg {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q:Ideal O)(K:ℝ)(hK:0≤ K):
    0≤ profileFactor Sprofile s p J Q K:=by
  unfold profileFactor
  have hp:=Profiles.control_nonneg p Sprofile
  positivity

lemma sourceBudget_exact {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(U:Finset (CommonIndex C D))(K Z ε δ θ r h:ℝ)
    (hZ:1< Z)(hh:0< h):
    sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z h)=
      profileFactor Sprofile s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      (h^(1/6:ℝ)/(forcingNorm C D U)^(2/3:ℝ)*volume s.toData^2/
        ((C.absNorm:ℝ)*D.absNorm)):=by
  have hf:0< forcingNorm C D U:=common_product_pos C D hC _
  unfold sourceBudget
  simp only [forcingNorm] at hf ⊢
  rw [Real.one_rpow, mul_one]
  rw [show (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=> P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+2*ε+δ-
      max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0=
      (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=> P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
        (2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0) by ring,
    count_power Z h (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=> P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ) _ hZ hh hf,profileMass_self]
  unfold profileFactor
  ring

/-- Cancel the common-prime norm without expanding the physical factors. -/
private lemma central_budget_scalar (a b c d e h p f : ℝ) (hp : p ≠ 0) :
    a * (b * (c / (f * f) * h / d)) / e =
      b * (a * c / e * (h / d) * p / f) / (p * f) := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    a * (b * (c * (f⁻¹ * f⁻¹) * h * d⁻¹)) * e⁻¹ =
        (a * (b * (c * (f⁻¹ * f⁻¹) * h * d⁻¹)) * e⁻¹) * (p * p⁻¹) := by
      rw [mul_inv_cancel₀ hp, mul_one]
    _ = _ := by ring

theorem central_sourceBudget_exact {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(_hD:Supported D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys:ℝ)(n:Fin 4→ℤ)(hZ:1< Z):
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))=
    profileFactor Sprofile s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      centralPhysicalCost C D U Kphys (volume s.toData) n/
      ((Ideal.absNorm (∏P:CommonIndex C D,P.val):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=by
  have hf:0< forcingNorm C D U:=common_product_pos C D hC _
  have hp:=common_product_pos C D hC Finset.univ
  have hpow:(forcingNorm C D U)^(2/3:ℝ)=
      (forcingNorm C D U)^(1/3:ℝ)*(forcingNorm C D U)^(1/3:ℝ):=by
    rw [←Real.rpow_add hf];congr 1;ring
  rw [sourceBudget_exact Sprofile s p J Q C D hC U K Z ε δ θ r _ hZ (dyadicScale_pos _),hpow]
  unfold centralPhysicalCost
  exact central_budget_scalar _ _ _ _ _ _ _ _ (ne_of_gt hp)

end CenteredMomentFiniteProfileExceptionalPhysical

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentCommonAllowance
open CenteredMomentActive CenteredMomentSecondLedger CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

def activeIndicator (c d : ℕ) : ℝ := if netExponent c d ≠ 0 then 1 else 0

theorem netExponent_self (c : ℕ) : netExponent c c = 0 := by
  unfold netExponent
  have h : c+5*c=6*c := by omega
  rw [h, Nat.mul_mod_right]

theorem local_allowance (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    max (3*(c:ℝ)-5*(d:ℝ)-activeIndicator c d) 0 / 6 +
      max (3*(d:ℝ)-5*(c:ℝ)-activeIndicator c d) 0 / 6 ≤
      (c:ℝ)+(d:ℝ)-2-activeIndicator c d := by
  have hc' : (1:ℝ) ≤ c := by exact_mod_cast hc
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  unfold activeIndicator
  split_ifs with he
  · have hne : c ≠ d := by rintro rfl; exact he (netExponent_self c)
    have hgap : (c:ℝ)+1 ≤ d ∨ (d:ℝ)+1 ≤ c := by
      rcases lt_or_gt_of_ne hne with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    rcases hgap with hgap | hgap <;>
      rw [max_def,max_def] <;> split_ifs <;> linarith
  · rw [max_def,max_def]; split_ifs <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem weighted_positive_part (a w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    max (∑ i, a i*w i) 0 ≤ ∑ i, max (a i) 0*w i := by
  apply max_le
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (hw i)
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (hw i)

omit [DecidableEq ι] in
theorem weighted_allowance (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hd : ∀ i, 1 ≤ d i) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    max (3*(∑ i, (c i:ℝ)*w i)-5*(∑ i, (d i:ℝ)*w i)-
      ∑ i, activeIndicator (c i) (d i)*w i) 0/6 +
    max (3*(∑ i, (d i:ℝ)*w i)-5*(∑ i, (c i:ℝ)*w i)-
      ∑ i, activeIndicator (c i) (d i)*w i) 0/6 ≤
      (∑ i, (c i:ℝ)*w i)+(∑ i, (d i:ℝ)*w i)-
        2*(∑ i, w i)-(∑ i, activeIndicator (c i) (d i)*w i) := by
  have h₁ := weighted_positive_part (fun i => 3*(c i:ℝ)-5*(d i:ℝ)-activeIndicator (c i) (d i)) w hw
  have h₂ := weighted_positive_part (fun i => 3*(d i:ℝ)-5*(c i:ℝ)-activeIndicator (c i) (d i)) w hw
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_right (local_allowance (c i) (d i) (hc i) (hd i)) (hw i))
  simp only [sub_mul, add_mul, div_mul_eq_mul_div, mul_assoc,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
    ] at h₁ h₂ hsum ⊢
  simp only [← Finset.sum_div] at hsum
  linarith

omit [DecidableEq ι] in
theorem actual_common_support_allowance (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (Z : ℝ) (hZ : 1 < Z) :
    let C := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ)
    let D := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ)
    let P := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ)
    let R := Real.logb Z (Ideal.absNorm
      (∏ i ∈ activeSupport Finset.univ c d, Ideal.span {p i}) : ℝ)
    max (3*C-5*D-R) 0/6 + max (3*D-5*C-R) 0/6 ≤ C+D-2*P-R := by
  dsimp only
  rw [log_norm_power_product p hp c,log_norm_power_product p hp d,
    log_norm_radical p hp,log_norm_radical p hp]
  simpa only [activeSupport,Finset.sum_filter,activeIndicator,ite_mul,one_mul,zero_mul]
    using weighted_allowance c d hc hd
      (fun i => Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ))
      (fun i => Real.logb_nonneg hZ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))))

end CenteredMomentCommonAllowance

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentFirstCanonicalAllowance
open Eisenstein CanonicalQuadraticSieve 
open CenteredMomentActive CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentSecondCanonical CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical CenteredMomentCommonAllowance
local notation "O" => Eisenstein.O

theorem activeConductor_span_product (I J : Ideal O) :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ activeSupport (Finset.univ : Finset (CommonIndex I J))
        (leftExponent I J) (rightExponent I J), P.val := by
  rw [activeConductor, span_finitePrimeModulus]
  exact Finset.prod_coe_sort (s := ActiveIndex I J)
    (f := fun P : CommonIndex I J => P.val)

theorem active_generator_ideal_product (I J : Ideal O) (hI : Supported I) :
    (∏ P ∈ activeSupport (Finset.univ : Finset (CommonIndex I J))
      (leftExponent I J) (rightExponent I J), Ideal.span {commonPrime I J P}) =
      Ideal.span {activeConductor I J} := by
  simp_rw [commonPrime_span I J hI]
  exact (activeConductor_span_product I J).symm

theorem common_ideal_product (I J : Ideal O) :
    (∏ P : CommonIndex I J, P.val) = commonRadical I J := by
  exact Finset.prod_coe_sort (s := commonSupport I J) (f := fun P : Ideal O => P)

theorem common_generator_ideal_product (I J : Ideal O) (hI : Supported I) :
    (∏ P : CommonIndex I J, Ideal.span {commonPrime I J P}) = commonRadical I J := by
  simp_rw [commonPrime_span I J hI]
  exact common_ideal_product I J

theorem commonRadical_active_principal (I J : Ideal O) :
    commonRadical I J = Ideal.span {activeConductor I J} *
      ∏ P ∈ principalSupport (Finset.univ : Finset (CommonIndex I J))
        (leftExponent I J) (rightExponent I J), P.val := by
  rw [← common_ideal_product, activeConductor_span_product]
  simpa only [CenteredMomentActive.activeSupport, CenteredMomentActive.principalSupport, not_not] using
    (Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun P : CommonIndex I J => netExponent (leftExponent I J P) (rightExponent I J P) ≠ 0)
    (fun P => P.val)).symm

theorem actual_canonical_common_support_allowance
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D)
    (Z : ℝ) (hZ : 1 < Z) :
    let c := Real.logb Z (C.absNorm : ℝ)
    let d := Real.logb Z (D.absNorm : ℝ)
    let p := Real.logb Z ((commonRadical C D).absNorm : ℝ)
    let r := Real.logb Z ((Ideal.span {activeConductor C D}).absNorm : ℝ)
    max (3*c-5*d-r) 0/6 + max (3*d-5*c-r) 0/6 ≤ c+d-2*p-r := by
  have h := actual_common_support_allowance (commonPrime C D)
    (commonPrime_supported C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) Z hZ
  dsimp only at h ⊢
  rw [left_ideal_product C D hC hCD, right_ideal_product C D hC hD hCD,
    common_generator_ideal_product C D hC, active_generator_ideal_product C D hC] at h
  exact h

theorem activeConductor_span_filter (I J : Ideal O) :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ (commonSupport I J).filter (fun P =>
        netExponent (CenteredExceptionalCount.valuation I P)
          (CenteredExceptionalCount.valuation J P) ≠ 0), P := by
  rw [activeConductor_span_product]
  simp only [CenteredMomentActive.activeSupport, Finset.prod_filter]
  exact Finset.prod_coe_sort (s := commonSupport I J)
    (f := fun P : Ideal O => if netExponent (CenteredExceptionalCount.valuation I P)
      (CenteredExceptionalCount.valuation J P) ≠ 0 then P else 1)

theorem extracted_activeConductor_span (I J : Ideal O) :
    Ideal.span {activeConductor (commonPart I J) (commonPart J I)} =
      Ideal.span {activeConductor I J} := by
  have hs : commonSupport (commonPart I J) (commonPart J I) = commonSupport I J := by
    unfold commonSupport
    rw [commonPart_support, commonPart_support, commonSupport_comm J I, Finset.inter_self]
    rfl
  rw [activeConductor_span_filter, activeConductor_span_filter, hs]
  apply Finset.prod_congr
  · apply Finset.filter_congr
    intro P hP
    rw [commonPart_valuation, commonPart_valuation, commonSupport_comm J I,
      if_pos hP, if_pos hP]
  · intro P _
    rfl

theorem actual_extracted_common_support_allowance
    (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (Z : ℝ) (hZ : 1 < Z) :
    let c := Real.logb Z ((commonPart I J).absNorm : ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm : ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm : ℝ)
    let r := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm : ℝ)
    max (3*c-5*d-r) 0/6 + max (3*d-5*c-r) 0/6 ≤ c+d-2*p-r := by
  have h := actual_canonical_common_support_allowance
    (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
    (commonPart_supported J I hJ) (commonParts_equal_support I J) Z hZ
  dsimp only at h ⊢
  rw [extracted_commonRadical, extracted_activeConductor_span] at h
  exact h

end CenteredMomentFirstCanonicalAllowance

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CenteredMomentSecondExceptionalPhysicalSaving
open CanonicalQuadraticSieve CenteredMomentSecondPhysicalLedger CenteredMomentCanonicalFirst
local notation "O" => Eisenstein.O
lemma column_power_saving (Z c d θ:ℝ) (hZ:1< Z) (hc:1≤ c) (hd:1≤ d) (hθ:θ≤1/3) :
    (c*d)^θ*Z^(-(Real.logb Z c+Real.logb Z d)/3)≤1 := by
  have hc0:0< c:=zero_lt_one.trans_le hc
  have hd0:0< d:=zero_lt_one.trans_le hd
  have hz:0< Z:=zero_lt_one.trans hZ
  have he:-(Real.logb Z c+Real.logb Z d)/3=Real.logb Z (c*d)*(-1/3):=by
    rw [Real.logb_mul hc0.ne' hd0.ne'];ring
  rw [he,Real.rpow_mul hz.le,Real.rpow_logb hz (ne_of_gt hZ) (mul_pos hc0 hd0),
    ←Real.rpow_add (mul_pos hc0 hd0)]
  have hcd:1≤ c*d:=by nlinarith
  exact (Real.rpow_le_rpow_of_exponent_le hcd (by linarith : θ+ -1/3≤0)).trans_eq
    (Real.rpow_zero _)

lemma forcingNorm_ge_one (C D:Ideal O)(hC:Supported C)(U:Finset (CommonIndex C D)) :
    1≤ forcingNorm C D U := by
  have hf:0< forcingNorm C D U:=common_product_pos C D hC _
  unfold forcingNorm at hf ⊢
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hf)

lemma column_cap_ledger (c d r:ℝ)(hc:0≤ c)(hd:0≤ d) :
    2*max r 0/3≤(c+d)/3+max (r-min c d) 0 := by
  have hmin:0≤ min c d:=le_min hc hd
  have hc':min c d≤ c:=min_le_left _ _
  have hd':min c d≤ d:=min_le_right _ _
  by_cases hr:0≤ r
  · rw [max_eq_left hr]
    by_cases hm:r≤ min c d
    · rw [max_eq_right (by linarith : r-min c d≤0)]
      linarith
    · rw [max_eq_left (by linarith : 0≤ r-min c d)]
      linarith
  · rw [max_eq_right (le_of_not_ge hr)]
    have hm:0≤ max (r-min c d) 0:=le_max_right _ _
    linarith


end CenteredMomentSecondExceptionalPhysicalSaving

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

namespace CenteredMomentSecondExceptionalCommonSaving
open CenteredMomentSecondExceptionalPhysicalSaving
lemma common_weight_bound (Z c d θ B ε δ r:ℝ)(hZ:1< Z)(hc:1≤ c)(hd:1≤ d)
    (hθ:0≤θ)(hC:c≤ Z^B)(hD:d≤ Z^B):
    Z^(2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*(c*d)^θ*
      Z^(-(Real.logb Z c+Real.logb Z d)/3)≤
        Z^(2*ε+δ+2*B*θ-2*max r 0/3):=by
  have hz:0< Z:=zero_lt_one.trans hZ
  have hcd:0≤ c*d:=mul_nonneg (zero_le_one.trans hc) (zero_le_one.trans hd)
  have hpow:(c*d)^θ≤ Z^(2*B*θ):=by
    calc
      _≤(Z^B*Z^B)^θ:=Real.rpow_le_rpow hcd
        (mul_le_mul hC hD (zero_le_one.trans hd) (Real.rpow_nonneg hz.le _)) hθ
      _=Z^(2*B*θ):=by
        rw [←Real.rpow_add hz,←Real.rpow_mul hz.le]
        congr 1;ring
  have hl:=column_cap_ledger (Real.logb Z c) (Real.logb Z d) r
    (Real.logb_nonneg hZ hc) (Real.logb_nonneg hZ hd)
  calc
    _≤ Z^(2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*Z^(2*B*θ)*
      Z^(-(Real.logb Z c+Real.logb Z d)/3):=by gcongr
    _=Z^((2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)+2*B*θ-
      (Real.logb Z c+Real.logb Z d)/3):=by
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1;ring
    _≤ _:=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
end CenteredMomentSecondExceptionalCommonSaving

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid 
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondExceptionalPhysicalSaving
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalAllowance
open CenteredMomentRankinRadical
local notation "O"=> Eisenstein.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem original_budget_physical_saving_full
    {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys a:ℝ)(n:Fin 4→ℤ)(hK:0≤ K)(hZ:1< Z)
    (hKphys:0< Kphys)(ha:0< a)
    (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(hrows:∀z∈rows,z≠0)(W:𝓢(ℝ,ℂ))
    (hlower:∀I:Ideal O,β I≠0→a*volume s.toData≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W Kphys n≠0) :
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    profileFactor Sprofile s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      ((volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ))*
      Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
      (Ideal.absNorm (commonRadical C D):ℝ) := by
  have hp:0<(Ideal.absNorm (commonRadical C D):ℝ):=by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf:=forcingNorm_ge_one C D hC U
  have hfp:1≤(forcingNorm C D U)^(1/3:ℝ):=Real.one_le_rpow hf (by norm_num)
  have hcost:=original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W Kphys n
    hKphys (volume s.toData) a Z (volume_pos s.toData) ha hZ hlower hne
  let A:ℝ:=profileFactor Sprofile s p J Q K*
    Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ
  let E:ℝ:=(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
    Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)
  have hA:0≤ A:=mul_nonneg
    (mul_nonneg (profileFactor_nonneg Sprofile s p J Q K hK) (Real.rpow_nonneg (by linarith) _))
    (Real.rpow_nonneg (by positivity) _)
  have hv:=volume_pos s.toData
  have hz:0< Z:=zero_lt_one.trans hZ
  have hE:0≤ E:=by dsimp [E];positivity
  rw [central_sourceBudget_exact Sprofile s p J Q C D hC hD U K Z ε δ θ r Kphys n hZ,
    common_ideal_product]
  change A*centralPhysicalCost C D U Kphys (volume s.toData) n/
    ((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ))≤ _
  calc
    _≤ A*E/((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hA)
        (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _))
    _≤ A*E/(Ideal.absNorm (commonRadical C D):ℝ):=by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hE) hp
      nlinarith
    _= _:=by dsimp [A,E];ring

end CenteredMomentFiniteProfileExceptionalPhysical

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open   CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open  CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => Eisenstein.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_saved_exceptional_block (wlo whi:ℝ)(hwlo:0< wlo)(hwhi:0≤ whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤ B)(hL:0≤ Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤ Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
      ∃K:ℝ,0< K ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤ Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤ Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → lambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤ H) → H/(D.absNorm:ℝ)≤ Z^Lbound →
      ∀a:ℝ,0< a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0< Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
          Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_dyadic_exceptional_block wlo whi hwlo hwhi lo hi W 1 ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  let F:=physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n
  by_cases hne:F=0
  · change ‖F‖/_≤ _
    rw [hne,norm_zero,zero_div]
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hz:0≤ Z:=(zero_lt_one.trans hZ.1).le
    have hv:0≤ volume s.toData:=(volume_pos s.toData).le
    positivity
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n
  let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hd:0<1+rK:=by
    have h0:=dyadicScale_pos (n 0)
    have h1:=dyadicScale_pos (n 1)
    have h2:=dyadicScale_pos (n 2)
    have h3:=dyadicScale_pos (n 3)
    dsimp [rK]; positivity
  have hp':‖F‖≤ outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK):=by
    apply (le_div_iff₀ hd).mpr
    simpa only [pow_one,mul_comm] using hp
  have hs:=original_budget_physical_saving_full Sprofile s p J Q C D hC hD hCD U K Z ε δ θ r Kphys a n
    hK.le hZ.1 hKphys ha s.η s.t S β R rows hn W hlower hne
  calc
    _≤(outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK))/
      volume s.toData:=div_le_div_of_nonneg_right hp' (volume_pos s.toData).le
    _=Ck*((1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/(1+rK)):=by ring
    _≤ _:=by
      convert mul_le_mul_of_nonneg_left hs hCk using 1 <;> first | rfl | ring

end CenteredMomentFiniteProfileExceptionalPhysical

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open   CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open  CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => Eisenstein.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_uniform_exceptional_block (wlo whi:ℝ)(hwlo:0< wlo)(hwhi:0≤ whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤ B)(hL:0≤ Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤ Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
      ∃K:ℝ,0< K ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      (C.absNorm:ℝ)≤ Z^B → (D.absNorm:ℝ)≤ Z^B → primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayMonoid χ (primaryIdealGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤ Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤ Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → lambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤ H) → H/(D.absNorm:ℝ)≤ Z^Lbound →
      ∀a:ℝ,0< a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0< Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_saved_exceptional_block wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hNC hND hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hs:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hc:1≤(C.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hb:=common_weight_bound Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ B ε δ r hZ.1 hc hd hθ.le hNC hND
  let F:=Ck*profileFactor Sprofile s p J Q K*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
    (Ideal.absNorm (commonRadical C D):ℝ)
  have hF:0≤ F:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:0≤ volume s.toData:=(volume_pos s.toData).le
    dsimp only [F]
    positivity
  apply hs.trans
  calc
    _=F*(Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
      dsimp only [F];ring
    _≤ F*Z^(2*ε+δ+2*B*θ-2*max r 0/3):=mul_le_mul_of_nonneg_left hb hF
    _=_:=by dsimp only [F];ring

end CenteredMomentFiniteProfileExceptionalPhysical

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
