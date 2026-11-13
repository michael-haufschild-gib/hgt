/-
Second exceptional families adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.AmplificationShortening
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.FirstAnnularMajorants

/-!
# Second exceptional families

Existence and expanded factors of second exceptional families; canonical radial parts of
nonexceptional chosen blocks; ratio penalties and width costs of the capacity ledger.
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
open Filter

namespace CenteredMomentFirstReferenceBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss  
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentFirstDivisorSupport CenteredMomentChildAssembly
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSecondWindowBudget
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentMobiusRegroup
open CenteredMomentSecondHeightFamily CenteredMomentFirstPhysicalAnnularCommonBound
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstMixedAllowance
open CenteredMomentFirstMixedWindow CenteredMomentFirstWindowBudgets
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
local notation "O"=> Eisenstein.O

theorem actual_reference_block (W:𝓢(ℝ,ℂ)) (decay J₁ J₂:ℕ)
    (B δ:ℝ)(hB:0≤ B)(hδ:0<δ):
    ∃Cb:ℝ,0< Cb ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀{ι:Type*}[Fintype ι][DecidableEq ι],∀s:Input ι,∀R seed:Ideal O,
    ∀a₁ a₂:ℝ,0< a₁→0< a₂→
    (∀x,s.W₁ x≠0→a₁≤ x)→(∀x,s.W₂ x≠0→a₂≤ x)→
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀E:Finset (CommonIndex C D),∀ξ₁ ξ₂:RayCharacter,
    ∀F:FixedPair s.η C D hC E ξ₁ ξ₂,∀rows:Finset O,∀K:ℝ,0< K→∀n:Fin 4→ℤ,
    sourceRadius s/(D.absNorm:ℝ)≤ Z^B→∀EL ER:Fin 4→ℝ,(∀i,0≤ EL i)→(∀i,0≤ ER i)→
    let V:=volume s;
    let refL:=(F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z);
    let refR:=(F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z);
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 (original s R seed).columns))
      (fun b=> Ideal.span {element C D hD.1 (original s R seed).columns b}),
      (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) C hC (fixedPair s.η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        ((∑i,refL*EL i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁))→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 (original s R seed).columns))
      (fun b=> Ideal.span {element C D hD.1 (original s R seed).columns b}),
      (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) D hD (fixedPair s.η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        ((∑i,refR*ER i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂))→
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay*
      ‖block s.η (fixedBadMask*cubicIdealGenerator R) 1 s.t (original s R seed).columns
        (original s R seed).beta C D hC hD E rows W (fun _=> logAnnulus)
        K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))‖/V≤
      Cb*Z^δ*(‖inactiveWeight C D E‖*(Real.exp (Real.log 4)/((∏i,s.lo i)*a₁*a₂))*
        fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm)*
      (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (EL i)*windowBudget J₂ s.t (ER j)):=by
  obtain ⟨Cb,hCb,hev⟩:=CenteredMomentFirstDivisorCommonBound.actual_supported_annular_harmonic
    W decay J₁ J₂ B δ hB hδ
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ _ s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ C D hC hD hCD E ξ₁ ξ₂ F rows K hK n hcap EL ER hEL hER
    V refL refR hleft hright
  have hz:0≤ Z:=zero_le_one.trans hZ.1.le
  have hcb:0≤ Cb:=hCb.le
  have hf:0≤ fixedPresentationCost:=fixedPresentationCost_pos.le
  have hprodlo:0≤∏i,s.lo i:=Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)
  have hV:0< V:=volume_pos s
  have hRL:0≤ refL:=by dsimp [refL]; positivity
  have hRR:0≤ refR:=by dsimp [refR]; positivity
  have hLE:∀i:Fin 4,0≤ refL*EL i:=fun i=> mul_nonneg hRL (hEL i)
  have hRE:∀i:Fin 4,0≤ refR*ER i:=fun i=> mul_nonneg hRR (hER i)
  have hz₁:s.W₁ 0=0:=by by_contra hn;have hh:=hs₁ 0 hn;linarith
  have hz₂:s.W₂ 0=0:=by by_contra hn;have hh:=hs₂ 0 hn;linarith
  have hb:=hZ.2 s.η (original s R seed) s.t C D hC hD hCD E rows K hK n
    (sourceRadius s) (fun I hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2)
    hcap (∑i,refL*EL i) (∑i,refR*ER i)
    (Finset.sum_nonneg (fun i _=> hLE i)) (Finset.sum_nonneg (fun i _=> hRE i)) hleft hright
  have hw:=windowBudget_pair_sum Finset.univ Finset.univ (fun i=> refL*EL i) (fun i=> refR*ER i)
    (fun i _=> hLE i) (fun i _=> hRE i) J₁ J₂ s.t
  have hb':=hb.trans (mul_le_mul_of_nonneg_left hw (by positivity))
  by_cases hn:block s.η (fixedBadMask*cubicIdealGenerator R) 1 s.t (original s R seed).columns
      (original s R seed).beta C D hC hD E rows W (fun _=> logAnnulus)
      K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))=0
  · simp only [hn,norm_zero,mul_zero,zero_div]
    have he:0≤∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (EL i)*windowBudget J₂ s.t (ER j):=
      Finset.sum_nonneg (fun i _=> Finset.sum_nonneg (fun j _=> mul_nonneg
        (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))
    positivity
  · have href:=original_four_budget_reference s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂
      (fixedBadMask*cubicIdealGenerator R) 1 s.t (original s R seed).columns C D hC hD hCD E
      ξ₁ ξ₂ F rows W (fun _=> logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) (Real.log 4) Z EL ER J₁ J₂ s.t hK
      (dyadicScale_pos _) (dyadicScale_pos _) hZ.1 hEL hER
      (fun _ x hx=> by
        have hh:=logAnnulus_support hx
        exact abs_le.mpr ⟨hh.1,hh.2.trans (Real.log_nonneg (by norm_num))⟩) hn
    have hh:=div_le_div_of_nonneg_right hb' hV.le
    have hscale:0≤ Cb*Z^δ:=by positivity
    have hmul:=mul_le_mul_of_nonneg_left href hscale
    calc
      _ ≤ _ := hh
      _ = Cb*Z^δ*(‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖/V*
          (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (refL*EL i)*windowBudget J₂ s.t (refR*ER j))) := by ring
      _ ≤ _ := by
        convert hmul using 1 <;>
          (try dsimp [refL,refR,V,CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume]) <;>
          (first | rfl | ring)

end CenteredMomentFirstReferenceBlock

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentFirstReferenceEnergy
open HeckeFamily CanonicalQuadraticSieve  CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstReferenceBlock
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstSourceReduction CenteredMomentFirstInactiveRadicalMass
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentExceptionalAmplitudePair CenteredMomentRankinRadical
open CenteredMomentAmplificationChildInput CenteredMomentGaussEnergy CenteredMomentChildAssembly
open CenteredMomentCommonSupport CenteredMomentMobiusRegroup CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstMixedAllowance CenteredMomentSecondWindowBudget CenteredMomentSecondHeightFamily
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev supported (s:Input ι)(R seed:Ideal O)(p:Labels s R seed):=
  commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property

def ColumnBounds (s:Input ι)(R seed:Ideal O)(Z:ℝ)(J₁ J₂:ℕ)(EL ER:Fin 4→ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(n:Fin 4→ℤ):Prop:=
  let C:=p.val.1; let D:=p.val.2; let h:=supported s R seed p
  let F:=fixedPair s.η C D h.1 E 1 1
  let V:=volume s.toData
  let refL:=(F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)
  let refR:=(F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)
  (∀L∈divisorPool (Finset.univ:Finset (columns C D h.2.1 (original s R seed).columns))
    (fun b=> Ideal.span {element C D h.2.1 (original s R seed).columns b}),
    (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
    (commonEnergy (original s R seed) C h.1 (fixedPair s.η C D h.1 E χ χ).left v L
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      ((∑i,refL*EL i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) ∧
  (∀L∈divisorPool (Finset.univ:Finset (columns C D h.2.1 (original s R seed).columns))
    (fun b=> Ideal.span {element C D h.2.1 (original s R seed).columns b}),
    (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
    (commonEnergy (original s R seed) D h.2 (fixedPair s.η C D h.1 E χ χ).right v L
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      ((∑i,refR*ER i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂))

def pairedBudget (J₁ J₂:ℕ)(t:ℝ)(EL ER:Fin 4→ℝ):ℝ:=
  ∑i:Fin 4,∑j:Fin 4,windowBudget J₁ t (EL i)*windowBudget J₂ t (ER j)
lemma pairedBudget_nonneg (J₁ J₂:ℕ)(t:ℝ)(EL ER:Fin 4→ℝ):0≤ pairedBudget J₁ J₂ t EL ER:=
  Finset.sum_nonneg (fun _i _=> Finset.sum_nonneg (fun _j _=> mul_nonneg
    (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))

theorem actual_physical_mass (W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)(hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤ B)(hξ:0≤ξ)(hε:0<ε):
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,∀s:Input ι,∀R seed:Ideal O,
      Squarefree seed→seed≠0→(∀i,|s.hi i|≤ hi i)→|s.b₁|≤ b₁→|s.b₂|≤ b₂→
      ∀a₁ a₂ K:ℝ,0< a₁→0< a₂→0< K→
      (∀x,s.W₁ x≠0→a₁≤ x)→(∀x,s.W₂ x≠0→a₂≤ x)→
      volume s.toData≤ Z^B→K⁻¹≤ Z^B→∀EL ER:Fin 4→ℝ,(∀i,0≤ EL i)→(∀i,0≤ ER i)→
      (∀p:Labels s R seed,∀E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        ∀n:SourceBlocks s R seed K Z ξ p E,
        CenteredMomentFirstReferenceSource.originalBlock s R seed W K Z ξ p E n ≠ 0 →
          ColumnBounds s R seed Z J₁ J₂ EL ER p E (fun i => (n i).val)) →
      physicalMass s R seed fixedBadMask 1 W K Z ξ/volume s.toData≤
        C*Z^ε/(seed.absNorm:ℝ)*sourceFactor s a₁ a₂ K*pairedBudget J₁ J₂ s.t EL ER:=by
  obtain ⟨Cs,hCs,hsum⟩:=original_block_sum hi b₁ b₂ B ξ (ε/2) hB hξ (by linarith)
  obtain ⟨Cb,hCb,hblock⟩:=actual_reference_block W 0 J₁ J₂ (B+1) (ε/2) (by linarith) (by linarith)
  refine ⟨Cs*Cb,mul_pos hCs hCb,?_⟩
  filter_upwards [hsum,hblock,eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hsum hblock hfixed
  intro s R seed hseed hseed0 hhi hb₁ hb₂ a₁ a₂ K ha₁ ha₂ hK hs₁ hs₂ hV hKi EL ER hEL hER hcol
  have hz₁:s.W₁ 0=0:=by by_contra hn;have hh:=hs₁ 0 hn;linarith
  have hz₂:s.W₂ 0=0:=by by_contra hn;have hh:=hs₂ 0 hn;linarith
  by_cases hH:0< sourceRadius s
  case neg =>
    rw [CenteredMomentFirstPhysicalZeroRadius.physicalMass_zero s R seed hz₁ hz₂ (le_of_not_gt hH)]
    simp only [zero_div]
    have hsF:=sourceFactor_nonneg s a₁ a₂ K ha₁ ha₂ hK
    have hsP:=pairedBudget_nonneg J₁ J₂ s.t EL ER
    have hZpos:0< Z:=zero_lt_one.trans hblock.1
    positivity
  let A:=Cb*Z^(ε/2)*sourceFactor s a₁ a₂ K*pairedBudget J₁ J₂ s.t EL ER
  have hA:0≤ A:=mul_nonneg (mul_nonneg (mul_nonneg hCb.le (Real.rpow_nonneg (by linarith [hblock.1]) _))
    (sourceFactor_nonneg s a₁ a₂ K ha₁ ha₂ hK)) (pairedBudget_nonneg _ _ _ _ _)
  have hcap:=CenteredMomentFirstPhysicalDyadicCount.input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hblock.1.le hfixed hV
  have hpblock (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
      (hE:E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2)
      (n:SourceBlocks s R seed K Z ξ p E):
      ‖CenteredMomentFirstReferenceSource.originalBlock s R seed W K Z ξ p E n‖/volume s.toData≤ A*radicalWeight s R seed p E:=by
    by_cases hne:CenteredMomentFirstReferenceSource.originalBlock s R seed W K Z ξ p E n=0
    · rw [hne,norm_zero,zero_div]
      exact mul_nonneg hA (radicalWeight_nonneg s R seed p E)
    have hp:=supported s R seed p
    have hg:=actual_common_gates s R seed hseed hz₁ hz₂ p.val.1 p.val.2 p.property
    have hND:1≤(p.val.2.absNorm:ℝ):=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1)
    have hcapD:sourceRadius s/(p.val.2.absNorm:ℝ)≤ Z^(B+1):=
      (div_le_self hH.le hND).trans hcap
    have hh:=hblock.2 s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ p.val.1 p.val.2 hp.1 hp.2 hg.2.2.1 E 1 1
      (fixedPair s.η p.val.1 p.val.2 hp.1 E 1 1) (retainedRows (localRadius s R seed K Z ξ p E) 1)
      K hK (fun i => (n i).val) hcapD EL ER hEL hER (hcol p E hE n hne).1 (hcol p E hE n hne).2
    simp only [pow_zero,one_mul] at hh
    convert hh using 1 <;>
      simp only [CenteredMomentFirstReferenceSource.originalBlock,A,sourceFactor,pairedBudget,radicalWeight,
        CenteredMomentFirstInactiveRadicalMass.inactiveWeight,Real.rpow_zero,div_one,
        CenteredMomentFirstPhysicalSource.inactiveWeight, CenteredMomentAmplificationChildInput.original,
        CenteredMomentFirstAmplificationChoice.OriginalData.columns,
        CenteredMomentFirstAmplificationChoice.OriginalData.beta,
        CenteredMomentFirstAmplificationChoice.OriginalData.profile,
        CenteredMomentOriginalCommonHarmonic.coefficient,
        CenteredMomentAmplificationChildInput.volume,
        CenteredMomentExceptionalAmplitudePair.volume] ; ring
  have hh:=hsum s R seed hseed hseed0 hz₁ hz₂ hhi hb₁ hb₂ hH W K A hK hA hV hKi hpblock
  rw [CenteredMomentFirstPhysicalOriginalMask.original_physicalMass] at hh
  calc
    _≤ _:=hh
    _=_:=by
      rw [show Z^ε=Z^(ε/2)*Z^(ε/2) by rw [←Real.rpow_add (by linarith [hblock.1]:0< Z)];congr 1;ring]
      dsimp [A]
      ring

end CenteredMomentFirstReferenceEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSecondBlockSupport
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorFrequency CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentHeckeColumnWindow
local notation "O" => Eisenstein.O

theorem normalizedBlock_zero_of_common (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hz:∀z∈rows,idealCorrelation C D hC hD
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z)=0) :
    normalizedBlock η t S β C D hC hD U R rows W K n=0 := by
  unfold normalizedBlock
  apply Finset.sum_eq_zero
  intro z hzr
  let F:O→Ideal O→Ideal O→ℂ:=fun _ I J=>
    wholeKernel W (fun _=> logAnnulus)
      (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
      (Real.log (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/
        dyadicScale (n 0))) (Real.log (normValue z/dyadicScale (n 1)))
      (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
      (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))
  have he:=sectorFrequency_zero_of_common η t S β C D hC hD hCD F
    ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z) (hz z hzr)
  simpa only [sectorFrequency,F,mul_zero] using congrArg (fun x:ℂ=> retainedScalar C D U R z*x) he

/-- A nonzero block contains a row with nonzero common correlation. -/
theorem normalizedBlock_nonzero_common (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hne:normalizedBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  by_contra hn
  push Not at hn
  apply hne
  exact normalizedBlock_zero_of_common η t S β C D hC hD hCD U R rows W K n
    (fun z hz=> by simpa only [mul_assoc] using hn z hz)

theorem physicalBlock_nonzero_common (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (hrows:∀z∈rows,z≠0)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0< K) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  rw [physicalBlock_eq η t S β C D hC hD U R rows hrows W K hK n] at hne
  exact normalizedBlock_nonzero_common η t S β C D hC hD hCD U R rows W K n
    (right_ne_zero_of_mul hne)

end CenteredMomentSecondBlockSupport

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace CenteredMomentSecondExceptionalFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentPartitionNorm
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedWidth
open CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource CenteredMomentSecondRadicalColumns
open CenteredMomentSecondReducedPredicate CenteredMomentSecondLiveBlock CenteredMomentSecondBlockSupport
open CenteredMomentSecondPhysicalBlock CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentRestrictedEnergy CenteredMomentSectorLocalization RayFourExpansion
open CenteredExceptionalProfile CenteredMomentReflectedSource
local notation "O" => Eisenstein.O

theorem span_thirty_six_norm : (Ideal.span {(36:O)}).absNorm=1296 := by
  have h := Eisenstein.Coordinates.rational_modulus_card 36
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply]
  exact h

theorem reflected_modulus_bound (τ:Character) :
    (reflected τ).modulus.absNorm≤1296*τ.modulus.absNorm := by
  have h := HeckePrimeScale.product_modulus_bound τ (HeckeUnitRows.character (-1:Oˣ))
  change (reflected τ).modulus.absNorm≤τ.modulus.absNorm*(Ideal.span {(36:O)}).absNorm at h
  simpa only [span_thirty_six_norm,mul_comm] using h

theorem common_subproduct_dvd_left (C D:Ideal O) (hC:Supported C)
    (hCD:primeSupport C=primeSupport D) (S:Finset (CommonIndex C D)) :
    (∏P∈S,P.val)∣C := by
  have h₁ := Finset.prod_dvd_prod_of_subset S Finset.univ
    (fun P:CommonIndex C D=> P.val) (Finset.subset_univ S)
  have h₂ : (∏P:CommonIndex C D,P.val)∣
      ∏P:CommonIndex C D,Ideal.span {commonPrime C D P}^leftExponent C D P := by
    apply Finset.prod_dvd_prod_of_dvd
    intro P _
    rw [commonPrime_span C D hC]
    exact dvd_pow_self _ (Nat.ne_zero_of_lt (leftExponent_pos C D P))
  rw [left_ideal_product C D hC hCD] at h₂
  exact h₁.trans h₂

theorem common_subproduct_dvd_right (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (S:Finset (CommonIndex C D)) :
    (∏P∈S,P.val)∣D := by
  have h₁ := Finset.prod_dvd_prod_of_subset S Finset.univ
    (fun P:CommonIndex C D=> P.val) (Finset.subset_univ S)
  have h₂ : (∏P:CommonIndex C D,P.val)∣
      ∏P:CommonIndex C D,Ideal.span {commonPrime C D P}^rightExponent C D P := by
    apply Finset.prod_dvd_prod_of_dvd
    intro P _
    rw [commonPrime_span C D hC]
    exact dvd_pow_self _ (Nat.ne_zero_of_lt (rightExponent_pos C D P))
  rw [right_ideal_product C D hC hD hCD] at h₂
  exact h₁.trans h₂

theorem selected_nonunit_product (C D:Ideal O) (hC:Supported C)
    (U:Finset (CommonIndex C D)) :
    (∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}=
      ∏P∈U∪nonunitPartitionSet C D U,P.val := by
  have hd : Disjoint U (nonunitPartitionSet C D U) := by
    apply Finset.disjoint_left.mpr
    intro P hP hV
    exact (Finset.mem_sdiff.mp hV).2 hP
  rw [Finset.prod_union hd,nonunitFrequencyGenerator_span]
  simp only [unitIdeal,commonPrime_span C D hC]

theorem selected_nonunit_dvd (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D)) :
    ((∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}∣C) ∧
    ((∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}∣D) := by
  rw [selected_nonunit_product C D hC]
  exact ⟨common_subproduct_dvd_left C D hC hCD _,
    common_subproduct_dvd_right C D hC hD hCD _⟩

theorem selected_nonunit_norm (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D)) :
    (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm≤ C.absNorm ∧
    (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm≤ D.absNorm := by
  obtain ⟨h₁,h₂⟩ := selected_nonunit_dvd C D hC hD hCD U
  constructor
  · simpa only [map_mul] using Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)) (map_dvd Ideal.absNorm h₁)
  · simpa only [map_mul] using Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)) (map_dvd Ideal.absNorm h₂)

structure Family (η:Character) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (τ:RayCharacter→Character) : Prop where
  element_eq : ∀χ n,elementCoeff (τ χ) n=
    rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n
  height_eq : ∀χ I,Supported I→(IsCoprime C I ∨ IsCoprime D I)→∀t,
    heightCoeff (τ χ) t I=heightCoeff η t I*
      idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
      rayMonoid χ (primaryIdealGenerator I)
  physical_budget : ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0< K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U R rows W K n≠0→∀χ,
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
    ∀Z:ℝ,1< Z→∀z∈liveRows C D U R rows,
      Real.logb Z (normValue z)+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
        Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ))

theorem exists_exceptional_family (η:Character) (C D:Ideal O)
    (hC:Supported C) (hD:Supported D) (hCD:primeSupport C=primeSupport D)
    (U:Finset (CommonIndex C D)) : ∃τ,Family η C D hC hD U τ := by
  choose τ he ht hrest using fun χ:RayCharacter=> exists_retained_width_family η χ C D hC U
  refine ⟨τ,he,?_,?_⟩
  · intro χ I hI hi t
    rw [ht χ I hI t]
    rcases hi with hi|hi
    · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
    · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]
  · intro t S β R rows W K hK n hne χ
    have hne':physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n≠0:=by
      rwa [←physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
    obtain ⟨w,_,hwc⟩:=physicalBlock_nonzero_common η t S β C D hC hD hCD U R
      (liveRows C D U R rows) (fun z hz=>(liveRows_geometry C D U R rows z hz).2.1)
      W K hK n hne'
    obtain ⟨hN,hwidth⟩:=hrest χ hD hCD (nonunitFrequencyGenerator C D U*w) hwc
    refine ⟨hN,?_⟩
    intro Z hZ z hz
    exact (hwidth Z R hZ z (liveRows_weight C D U R rows z hz)).2.2.2.2.2

namespace Family
variable {η:Character} {C D:Ideal O} {hC:Supported C} {hD:Supported D}
  {U:Finset (CommonIndex C D)} {τ:RayCharacter→Character}

theorem nonexceptional_iff (h:Family η C D hC hD U τ) (χ:RayCharacter)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hml:lambda∣m) (hm2:(2:O)∣m) :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      z≠0 ∧ ¬FixedInducingRow (τ χ) Q fixedBadMask 1 z :=
  actual_nonexceptional_iff η (τ χ) χ C D hC U (h.element_eq χ) Q m z hm hml hm2

theorem inducing_iff (h:Family η C D hC hD U τ) (χ:RayCharacter)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:lambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      FixedInducingRow (τ χ) Q fixedBadMask 1 z :=
  actual_reduced_inducing_iff η (τ χ) χ C D hC U (h.element_eq χ) Q m z hm hz hml hm2

theorem paired_inducing_iff (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O) (hQ:Q≤ Ideal.span {(72:O)}) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:lambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (τ χ) Q fixedBadMask 1 z ↔
      FixedInducingRow (τ ξ) Q fixedBadMask 1 (-z) :=
  (h.inducing_iff χ Q m z hm hz hml hm2).symm.trans
    ((CenteredMomentExceptionalReflection.fixedInducingRow_reflection_iff η χ ξ Q hQ m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z hml hm2).trans
      (h.inducing_iff ξ Q m (-z) hm (neg_ne_zero.mpr hz) hml hm2))

theorem both_inducing (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O) (hQ:Q≤ Ideal.span {(72:O)}) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:lambda∣m) (hm2:(2:O)∣m)
    (hex:FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) :
    FixedInducingRow (τ χ) Q fixedBadMask 1 z ∧
      FixedInducingRow (reflected (τ ξ)) Q fixedBadMask 1 z := by
  have hleft := (h.inducing_iff χ Q m z hm hz hml hm2).mp hex
  refine ⟨hleft,?_⟩
  exact (reflected_inducing (τ ξ) Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp
    ((h.paired_inducing_iff χ ξ Q hQ m z hm hz hml hm2).mp hleft)

theorem reflected_height_eq (h:Family η C D hC hD U τ) (ξ:RayCharacter)
    (I:Ideal O)(hI:Supported I)(hi:IsCoprime C I ∨ IsCoprime D I)(t:ℝ) :
    heightCoeff (reflected (τ ξ)) t I=heightCoeff η t I*
      idealRowHom (-(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)) I*
      rayMonoid ξ (primaryIdealGenerator I) := by
  have hneg : idealRowHom (-(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)) I=
      idealRowHom (-1) I*idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I := by
    rw [show -(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)=
      (-1)*(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) by ring]
    exact idealRowHom_argument_mul _ _ _
  rw [reflected_height _ _ _ hI,h.height_eq ξ I hI hi t,hneg]
  ring

theorem live_both_inducing (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O)(hQ:Q≤ Ideal.span {(72:O)})(m z:O)(hm:m≠0)
    (hml:lambda∣m)(hm2:(2:O)∣m)
    (radius:ℝ)(rows:Finset O)(hz:z∈liveRows C D U radius rows)
    (hex:FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) :
    z≠0 ∧ FixedInducingRow (τ χ) Q fixedBadMask 1 z ∧
      FixedInducingRow (reflected (τ ξ)) Q fixedBadMask 1 z := by
  have hz0 := (liveRows_geometry C D U radius rows z hz).2.1
  exact ⟨hz0,h.both_inducing χ ξ Q hQ m z hm hz0 hml hm2 hex⟩

theorem physical_conductor_bounds (h:Family η C D hC hD U τ)
    (hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)(χ:RayCharacter) :
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*C.absNorm ∧
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*D.absNorm := by
  have hN := (h.physical_budget t S β R rows W K hK n hne χ).1
  obtain ⟨h₁,h₂⟩ := selected_nonunit_norm C D hC hD hCD U
  constructor
  · exact hN.trans <| by
      simpa only [mul_assoc] using (Nat.mul_le_mul_left (η.modulus.absNorm*fixedFactor) h₁)
  · exact hN.trans <| by
      simpa only [mul_assoc] using (Nat.mul_le_mul_left (η.modulus.absNorm*fixedFactor) h₂)

end Family

def expandedConductor (τ:Character)(R C:Ideal O)(z:O):ℕ :=
  τ.modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
    (R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm

def expandedFactor (η:Character):ℕ :=
  1296*η.modulus.absNorm*fixedFactor*(Ideal.span {fixedBadMask}).absNorm*
    (Ideal.span {(72:O)}).absNorm

theorem expanded_conductor_bounds {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0< K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (χ ξ:RayCharacter)(R:Ideal O)(z:O) :
    expandedConductor (τ χ) R C z≤
      expandedFactor η*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm ∧
    expandedConductor (reflected (τ ξ)) R D z≤
      expandedFactor η*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm := by
  have hl := (h.physical_conductor_bounds hCD t S β radius rows W K hK n hne χ).2
  have hr := (h.physical_conductor_bounds hCD t S β radius rows W K hK n hne ξ).1
  have hl' : (τ χ).modulus.absNorm≤1296*(η.modulus.absNorm*fixedFactor*D.absNorm) := by
    exact hl.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  have hr' := (reflected_modulus_bound (τ ξ)).trans (Nat.mul_le_mul_left 1296 hr)
  constructor
  · calc
      expandedConductor (τ χ) R C z≤
        (1296*(η.modulus.absNorm*fixedFactor*D.absNorm))*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm := by
            unfold expandedConductor
            gcongr
      _=_ := by unfold expandedFactor;ring
  · calc
      expandedConductor (reflected (τ ξ)) R D z≤
        (1296*(η.modulus.absNorm*fixedFactor*C.absNorm))*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm := by
            unfold expandedConductor
            gcongr
      _=_ := by unfold expandedFactor;ring

theorem eventually_expanded_conductor_caps (η:Character)(ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1< Z₀ ∧ ∀Z:ℝ,Z₀≤ Z→
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0< K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(z:O)(c d r m:ℝ),
    (C.absNorm:ℝ)≤ Z^c→(D.absNorm:ℝ)≤ Z^d→(R.absNorm:ℝ)≤ Z^r→normValue z≤ Z^m→
    (expandedConductor (τ χ) R C z:ℝ)≤ Z^(c+d+r+m+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤ Z^(c+d+r+m+ε) := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (expandedFactor η:ℝ)
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.1 he
  refine ⟨max 2 Z₀,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ C D hC hD hCD U τ h t S β radius rows W K hK n hne χ ξ R z c d r m hCN hDN hRN hzn
  have hZpos : 0< Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have hconstant := hZ₀ Z ((le_max_right _ _).trans hZ)
  have hproduct : (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm≤
      Z^(c+d+r+m+ε) := by
    calc
      _≤ Z^ε*Z^r*Z^c*Z^d*Z^m := by
        change (Ideal.absNorm (Ideal.span {z}):ℝ)≤ _ at hzn
        gcongr
      _=Z^(c+d+r+m+ε) := by
        rw [←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos]
        congr 1
        ring
  obtain ⟨hl,hr⟩ := expanded_conductor_bounds h hCD t S β radius rows W K hK n hne χ ξ R z
  constructor
  · exact (show (expandedConductor (τ χ) R C z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hl).trans hproduct
  · exact (show (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hr).trans hproduct

theorem live_norm_le_four_radius (C D:Ideal O)(U:Finset (CommonIndex C D))
    (radius:ℝ)(rows:Finset O)(z:O)(hz:z∈liveRows C D U radius rows) :
    normValue z≤4*radius := by
  obtain ⟨hr,hg,hv,_,_,hn,_⟩ := retained_geometry radius
    (commonFrequencyGenerator C D) (nonunitFrequencyGenerator C D U) z
    (liveRows_weight C D U radius rows z hz)
  have hG := normValue_ge_one _ hg
  have hV := normValue_ge_one _ hv
  have hprod : 1≤ normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hG) (sub_nonneg.mpr hV)]
  exact hn.trans (div_le_self (by positivity) hprod)

theorem eventually_live_expanded_conductor_caps (η:Character)(ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1< Z₀ ∧ ∀Z:ℝ,Z₀≤ Z→
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0< K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(c d r m:ℝ),
    (C.absNorm:ℝ)≤ Z^c→(D.absNorm:ℝ)≤ Z^d→(R.absNorm:ℝ)≤ Z^r→ radius≤ Z^m→
    ∀z∈liveRows C D U radius rows,z≠0 ∧
    (expandedConductor (τ χ) R C z:ℝ)≤ Z^(c+d+r+m+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤ Z^(c+d+r+m+ε) := by
  obtain ⟨Z₁,hZ₁,h₁⟩ := eventually_expanded_conductor_caps η (ε/2) (by positivity)
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<ε/2 by positivity))) (4:ℝ)
  obtain ⟨Z₂,h₂⟩ := Filter.eventually_atTop.1 he
  refine ⟨max Z₁ Z₂,hZ₁.trans_le (le_max_left _ _),?_⟩
  intro Z hZ C D hC hD hCD U τ h t S β radius rows W K hK n hne χ ξ R c d r m hCN hDN hRN hrad z hz
  have hZpos : 0< Z := zero_lt_one.trans (hZ₁.trans_le ((le_max_left _ _).trans hZ))
  have hfour := h₂ Z ((le_max_right _ _).trans hZ)
  have hfreq : normValue z≤ Z^(m+ε/2) := by
    calc
      _≤4*radius := live_norm_le_four_radius C D U radius rows z hz
      _≤ Z^(ε/2)*Z^m := mul_le_mul hfour hrad
        (liveRows_geometry C D U radius rows z hz).1.le (Real.rpow_nonneg hZpos.le _)
      _=Z^(m+ε/2) := by rw [←Real.rpow_add hZpos,add_comm]
  have hc := h₁ Z ((le_max_left _ _).trans hZ) C D hC hD hCD U τ h t S β radius rows W K hK
    n hne χ ξ R z c d r (m+ε/2) hCN hDN hRN hfreq
  have hexp : c+d+r+(m+ε/2)+ε/2=c+d+r+m+ε := by ring
  rw [hexp] at hc
  exact ⟨(liveRows_geometry C D U radius rows z hz).2.1,hc⟩

end CenteredMomentSecondExceptionalFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentHeckeHeight CenteredMomentPrimeSlot
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
local notation "O" => Eisenstein.O

lemma excluded_one_ideal (χ : Character) (I : Ideal O) :
    idealCoeff (excluded χ 1) I=idealCoeff χ I := by
  simp only [excluded_ideal χ 1 one_ne_zero,isCoprime_one_right,ite_true]

lemma natural_unit_mask_coefficient {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff η I*CanonicalRowCompletion.idealRowHom ((fixedBadMask*cubicIdealGenerator 1)^6*z) I=
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (fixedBadMask^6*z) I := by
  rw [←F.masked_ideal 1 one_ne_zero,excluded_one_ideal,F.ideal]

lemma natural_unit_mask_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*cubicIdealGenerator 1) 1 z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η fixedBadMask 1 z W₁ W₂ S β P t X₁ X₂ := by
  simp only [positiveSlotRow,rowTwistedSum,rowSlot,one_mul,natural_unit_mask_coefficient F]


end CenteredMomentNaturalFixedRaySource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators ContDiff Topology
namespace CenteredMomentRelativeCapacityRemoval
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily Filter
local notation "O"=> Eisenstein.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
include hH

theorem relative_slots_uniform {ι:Type*}[Fintype ι]
    (W:ι→ℝ→ℂ)(a b:ι→ℝ)(ha:∀i,0< a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i))(hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot loss lo hi κ:ℝ)(hLm:0≤ Lmod)(hLs:0≤ Lslot)(hloss:0< loss)
    (hbeta:(51/100:ℝ)≤ beta)(hκ:2*beta-1≤κ):
    ∃degree:ℕ,∃C:ℝ,1≤ C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1< Z₀ ∧
    ∀i:ι,∀Z P:ℝ,Z₀≤ Z → 1≤ P → P≤ Z^Lslot →
    ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤ Z^Lmod →
    ∀Q:Ideal O,Q≤ M → Q≤(ν i).modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀σ t v V:ℝ,lo≤σ → σ≤ hi → 0≤ V → |v|≤ V →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H (b i) P)
        (fun I=> idealCoeff (ν i) I*annularWeight (W i) P σ v I) t P‖^2≤
        C*(1+|t|+V)^degree*Z^loss*P^κ := by
  choose degree C hC hb using fun i=> natural_character_slot_bound M H hH (W i) (a i) (b i)
    (ha i) (hWs i) (hW i) Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  let Ctotal:ℝ:=1+∑i,C i
  have hCtotal:1≤ Ctotal:=by
    have hsum:=Finset.sum_nonneg (fun i (_:i∈Finset.univ)=>(hC i).le)
    dsimp [Ctotal];linarith
  have hCi (i:ι):C i≤ Ctotal:=by
    have hsum:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hC j).le) (Finset.mem_univ i)
    dsimp [Ctotal];linarith
  refine ⟨∑i,degree i,Ctotal,hCtotal,?_⟩
  intro ν
  have hev:∀ᶠZ:ℝ in atTop,∀i:ι,_ := Filter.eventually_all.mpr (fun i=> hb i (ν i))
  obtain ⟨Zbase,hbase⟩:=eventually_atTop.mp hev
  refine ⟨max 2 Zbase,lt_max_of_lt_left (by norm_num),?_⟩
  intro i Z P hZ hP hPcap η z hz F hcond Q hQM hQν hex σ t v V hσ hσhi hV hv
  have hZ0:Zbase≤ Z:=(le_max_right _ _).trans hZ
  have hZp:0< Z:=lt_of_lt_of_le (by norm_num:0<(2:ℝ)) ((le_max_left _ _).trans hZ)
  refine (hbase Z hZ0 i P hP hPcap η z hz F hcond Q hQM hQν hex σ t v hσ hσhi).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
  apply mul_le_mul (hCi i) _ (by positivity) (zero_le_one.trans hCtotal)
  calc
    _≤(1+|t|+V)^(degree i):=pow_le_pow_left₀ (by positivity) (by linarith) _
    _≤ _:=pow_le_pow_right₀ (by linarith [abs_nonneg t])
      (Finset.single_le_sum (fun j _=> Nat.zero_le _) (Finset.mem_univ i))

theorem actual_relative_capacity_removal {ι:Type*}[Fintype ι][DecidableEq ι]
    (W:ι→ℝ→ℂ)(a b:ι→ℝ)(ha:∀i,0< a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i))(hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot ε lo hi κ:ℝ)(hLm:0≤ Lmod)(hLs:0≤ Lslot)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤ beta)(hκ:2*beta-1≤κ):
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1< Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤ mesh →
      (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤ width) ∧
      κ*(∑i∈R,w i)≤ CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤ Z → ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤ Z^Lmod →
    ∀Q:Ideal O,Q≤ M → (∀i,Q≤(ν i).modulus) → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ V → (∀i,|freq i|≤ V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),
      let P:=fun i=> Z^(w i)
      let S:=fun i=> primePool M H (b i) (P i)
      let coeff:=fun i I=> idealCoeff (ν i) I*annularWeight (W i) (P i) (σ i) (freq i) I
      ‖selectedProduct J η fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂‖^2≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          ‖selectedProduct (J\R) η fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂‖^2 := by
  let N:=Fintype.card ι
  let loss:=ε/((N:ℝ)+1)
  have hloss:0< loss:=div_pos hε (by positivity)
  obtain ⟨degree,C,hC,hbound⟩:=relative_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  have hκpos:0<κ:=by linarith
  refine ⟨degree*N,C ^ N,pow_pos (zero_lt_one.trans_le hC) _,?_⟩
  intro ν
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound ν
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  let excess:=CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ
  obtain ⟨R,hR,hRsum,hpay,hcost⟩:=whole_removal J w excess κ mesh (le_max_right _ _) hκpos hmesh
    (fun i _=> hw i) (fun i _=> hwm i)
  refine ⟨R,hR,CenteredMomentLiveCapacity.remaining_capacity J R hR w n₁ n₂ width κ hpay,hcost,?_⟩
  intro Z hZ η z hz F hcond Q hQM hQν hex σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂
  dsimp only
  have hZ1:1≤ Z:=hZ₀.le.trans hZ
  have hZp:0< Z:=zero_lt_one.trans_le hZ1
  let B:=C*(1+|t|+V)^degree*Z^loss
  have hB:1≤ B:=by
    have ht:1≤(1+|t|+V)^degree:=one_le_pow₀ (by linarith [abs_nonneg t])
    have hz:1≤ Z^loss:=Real.one_le_rpow hZ1 hloss.le
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC ht) hz
  have hs:∀i∈R,‖normalizedSlot η fixedBadMask 1 z (primePool M H (b i) (Z^(w i)))
      (fun I=> idealCoeff (ν i) I*annularWeight (W i) (Z^(w i)) (σ i) (freq i) I) t (Z^(w i))‖^2≤
      B*Z^(κ*w i) := by
    intro i hi
    have hb:=hbound i Z (Z^(w i)) hZ (Real.one_le_rpow hZ1 (hw i))
      (Real.rpow_le_rpow_of_exponent_le hZ1 (hwcap i)) η z hz F hcond Q hQM (hQν i) hex
      (σ i) t (freq i) V (hσ i) (hσhi i) hV (hfreq i)
    rw [←Real.rpow_mul hZp.le] at hb
    simpa only [B,mul_comm (w i) κ] using hb
  have he:=selectedProduct_energy_remove J R hR η fixedBadMask 1 z W₁ W₂
    (fun i=> primePool M H (b i) (Z^(w i)))
    (fun i I=> idealCoeff (ν i) I*annularWeight (W i) (Z^(w i)) (σ i) (freq i) I)
    (fun i=> Z^(w i)) t X₁ X₂ Z κ hZp w (fun _=> B) (fun i hi=> zero_le_one.trans hB) hs
  apply he.trans
  gcongr 1
  have hcard:R.card≤ N:=Finset.card_le_univ R
  have hpow:(∏i∈R,B)≤ B^N:=by
    rw [Finset.prod_const]
    exact pow_le_pow_right₀ hB hcard
  have hcostZ:Z^(κ*∑i∈R,w i)≤ Z^(excess/6+κ*mesh):=
    Real.rpow_le_rpow_of_exponent_le hZ1 hcost
  have hsplit:B^N=C ^ N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)):=by
    dsimp [B]
    rw [mul_pow,mul_pow,←pow_mul,←Real.rpow_natCast (Z^loss) N,←Real.rpow_mul hZp.le]
  have hlossN:loss*(N:ℝ)≤ε:=by
    dsimp [loss]
    have hden:0<(N:ℝ)+1:=by positivity
    have hh:ε/((N:ℝ)+1)*((N:ℝ)+1)=ε:=div_mul_cancel₀ _ hden.ne'
    nlinarith [hloss.le]
  calc
    _≤ B^N*Z^(excess/6+κ*mesh):=mul_le_mul hpow hcostZ (Real.rpow_nonneg hZp.le _) (by positivity)
    _=C ^ N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)+(excess/6+κ*mesh)):=by
      rw [hsplit,mul_assoc,←Real.rpow_add hZp]
    _≤ _:=mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)) (by positivity)
  apply le_of_eq
  congr 3
  ext i
  simp

end CenteredMomentRelativeCapacityRemoval

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentSlotClassTransport
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentAllocatedNaturalSource CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentRetainedEnergy
local notation "O"=> Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem common_fixed_slot_coefficient (s : Input ι) (ν : ι→Character)
    (hν : ∀i I,s.ν i I=idealCoeff (ν i) I)
    (τ : Character) (v : ℝ) (C R : Ideal O) (B : actualAllocations s.pools C)
    (i : CenteredMomentCommonProfile.liveIndices B.val) (I : Ideal O) :
    (commonData (withHeight s τ v) C R B).coefficient i I=
      idealCoeff (ν i.val) I*s.W i.val ((I.absNorm:ℝ)/s.P i.val) := by
  change s.ν i.val I*s.W i.val ((I.absNorm:ℝ)/s.P i.val)=_
  rw [hν]

omit [DecidableEq ι] in
theorem commonSlots_fixed_coefficient (s : Input ι) (ν : ι→Character)
    (hν : ∀i I,s.ν i I=idealCoeff (ν i) I)
    (τ : Character) (v : ℝ) (C : Ideal O) (B : actualAllocations s.pools C)
    (i : CenteredMomentCommonProfile.liveIndices B.val) (I : Ideal O) :
    (commonSlots (withHeight s τ v) C B).coefficient i I=
      idealCoeff (ν i.val) I*s.W i.val ((I.absNorm:ℝ)/s.P i.val) := by
  change s.ν i.val I*s.W i.val ((I.absNorm:ℝ)/s.P i.val)=_
  rw [hν]

theorem allocated_fixed_character_gate (s : Input ι) (ν : ι→Character)
    (Q : Ideal O) (hQ : ∀i,Q≤(ν i).modulus)
    (τ : Character) (v : ℝ) (C R L : Ideal O) (B : actualAllocations s.pools C)
    (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2)))
    (i : CenteredMomentDivisorRaw.liveIndices L a) :
    Q≤(ν i.val.val).modulus ∧
    (commonData (withHeight s τ v) C R B).slots i.val=s.slots i.val.val ∧
    (commonData (withHeight s τ v) C R B).P i.val=s.P i.val.val ∧
    (commonData (withHeight s τ v) C R B).W i.val=s.W i.val.val :=
  ⟨hQ _,rfl,rfl,rfl⟩

theorem allocated_positive_fixed_characters (s : Input ι) (ν : ι→Character)
    (hν : ∀i I,s.ν i I=idealCoeff (ν i) I)
    (τ : Character) (v : ℝ) (C R L : Ideal O) (B : actualAllocations s.pools C)
    (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2)))
    (z : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ) :
    let d:=commonData (withHeight s τ v) C R B
    allocatedPositiveRow d.η d.m d.A z d.t d.slots d.coefficient d.P L a W₁ W₂ X₁ X₂=
      retainedPositiveRow τ
        (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator (R*C))
        1 z W₁ W₂
        (fun i : CenteredMomentDivisorRaw.liveIndices L a=> s.slots i.val.val)
        (fun i : CenteredMomentDivisorRaw.liveIndices L a=> fun I=>
          idealCoeff (ν i.val.val) I*s.W i.val.val ((I.absNorm:ℝ)/s.P i.val.val))
        (fun i : CenteredMomentDivisorRaw.liveIndices L a=> s.P i.val.val) v
        (X₁/Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain L a 0))
        (X₂/Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain L a 1)) := by
  dsimp only
  unfold allocatedPositiveRow
  have he : (fun i : CenteredMomentDivisorRaw.liveIndices L a=>
      (commonData (withHeight s τ v) C R B).coefficient i.val)=
    (fun i : CenteredMomentDivisorRaw.liveIndices L a=> fun I=>
      idealCoeff (ν i.val.val) I*s.W i.val.val ((I.absNorm:ℝ)/s.P i.val.val)) := by
    funext i I
    exact common_fixed_slot_coefficient s ν hν τ v C R B i.val I
  rw [he]
  rfl

end CenteredMomentSlotClassTransport

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
noncomputable section
open scoped SchwartzMap
namespace CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentRadialEligibleEnergy CenteredMomentSecondOriginalChildren
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
local notation "O" => Eisenstein.O
def canonicalRadial (τ:Character)(Q:Ideal O)(n:Fin 4→ℤ):Radial:=
  sourceRadial (fun z=> z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow τ Q fixedBadMask 1 z)
    ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=> ballProfile_nonneg _)


end CenteredMomentSecondNonexceptionalChosenBlock

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
noncomputable section
open scoped SchwartzMap
namespace CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAmplificationChoice
theorem ballProfile_support_upper (x : ℝ) (hx : 0≤ x) (h : ballProfile x≠0) : x<2 := by
  have hb : x∈Function.support SchwartzPlanePoisson.sieveBump := by
    intro hz
    exact h (by simp only [ballProfile,SchwartzPlanePoisson.sieveCutoff_apply,hz,Complex.ofReal_zero])
  rw [SchwartzPlanePoisson.sieveBump.support_eq] at hb
  simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hx,
    SchwartzPlanePoisson.sieveBump] using hb


end CenteredMomentAmplifiedRetainedRadius

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Filter
namespace CenteredMomentCommonMaskChildCapacity
open HeckeFamily HeckeDyadic CenteredMomentComparisonReflection
local notation "O" => Eisenstein.O

lemma polynomial_nonzero_support (χ : Character) (W : ℝ→ℂ) (X sigma t b : ℝ)
    (hX : 0< X) (hs : Function.support W⊆Set.Iic b)
    (hn : polynomial χ false W X sigma t≠0) : 1≤ b*X := by
  by_contra hh
  have hb : b*X<1:=lt_of_not_ge hh
  apply hn
  unfold polynomial
  have hzero : ∀I : NonzeroIdeal,HeckeDyadic.summand χ false W X sigma t I=0 := by
    intro I
    have hW : W (norm I/X)=0 := by
      by_contra hW
      have hu:=hs hW
      have hle : norm I≤ b*X:=(div_le_iff₀ hX).mp hu
      have hi : 1≤ norm I := by
        change 1≤(I.val.absNorm:ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
      linarith
    simp only [HeckeDyadic.summand,hW,mul_zero,zero_mul]
  simp only [hzero,tsum_zero,mul_zero]

lemma actual_clipped_log (χ : Character) (W : ℝ→ℂ) (Z X sigma t b : ℝ)
    (hZ : 1< Z) (hX : 0< X) (hs : Function.support W⊆Set.Iic b)
    (hn : polynomial χ false W X sigma t≠0) :
    0≤ Real.logb Z (max 1 X) ∧
      Real.logb Z (max 1 X)≤ Real.logb Z X+Real.logb Z (max 1 b) := by
  have hB : 0< max 1 b:=zero_lt_one.trans_le (le_max_left _ _)
  have hclip : max 1 X≤ max 1 b*X := by
    apply max_le
    · exact (polynomial_nonzero_support χ W X sigma t b hX hs hn).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hX.le)
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 b) hX.le
  refine ⟨Real.logb_nonneg hZ (le_max_left _ _),?_⟩
  have hh:=Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (le_max_left 1 X)) hclip
  rw [Real.logb_mul hB.ne' hX.ne'] at hh
  linarith

lemma deleted_same_product (X₁ X₂ Y₁ Y₂ T d₁ d₂ : ℝ)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/d₁)*(X₂/d₂)=T/(d₁*d₂) ∧
      (Y₁/d₁)*(Y₂/d₂)=T/(d₁*d₂) := by
  constructor <;> rw [div_mul_div_comm]
  · rw [hX]
  · rw [hY]

theorem actual_deleted_capacity {α : Type*} [DecidableEq α]
    (F J : Finset α) (hJ : J⊆F) (P : α→ℝ) (hP : ∀i∈F,1≤ P i)
    (χ : Character) (W₁ W₂ : ℝ→ℂ) (Z X₁ X₂ t₁ t₂ b₁ b₂ kappa M : ℝ)
    (D₁ D₂ : Ideal O) (hD₁ : D₁≠0) (hD₂ : D₂≠0)
    (hZ : 1< Z) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hk : 0≤ kappa)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (hn : polynomial χ false W₁ (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
      polynomial χ false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂≠0)
    (hcap : Real.logb Z (X₁*X₂)+6*kappa*(∑i∈F,Real.logb Z (P i))≤ M) :
    let n₁:=Real.logb Z (max 1 (X₁/(D₁.absNorm:ℝ)))
    let n₂:=Real.logb Z (max 1 (X₂/(D₂.absNorm:ℝ)))
    0≤ n₁ ∧ 0≤ n₂ ∧ n₁+n₂+6*kappa*(∑i∈J,Real.logb Z (P i))≤
      M+Real.logb Z (max 1 b₁*max 1 b₂) := by
  have hd₁ : 1≤(D₁.absNorm:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD₁)
  have hd₂ : 1≤(D₂.absNorm:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD₂)
  have hd₁p : 0<(D₁.absNorm:ℝ):=zero_lt_one.trans_le hd₁
  have hd₂p : 0<(D₂.absNorm:ℝ):=zero_lt_one.trans_le hd₂
  have hc₁:=actual_clipped_log χ W₁ Z _ 0 t₁ b₁ hZ (div_pos hX₁ hd₁p) hs₁ (mul_ne_zero_iff.mp hn).1
  have hc₂:=actual_clipped_log χ W₂ Z _ 0 t₂ b₂ hZ (div_pos hX₂ hd₂p) hs₂ (mul_ne_zero_iff.mp hn).2
  have hslots : (∑i∈J,Real.logb Z (P i))≤∑i∈F,Real.logb Z (P i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hJ (fun i hi _=> Real.logb_nonneg hZ (hP i hi))
  have hslots' := mul_le_mul_of_nonneg_left hslots (by positivity : 0≤6*kappa)
  have hlog₁:=Real.logb_nonneg hZ hd₁
  have hlog₂:=Real.logb_nonneg hZ hd₂
  rw [Real.logb_div hX₁.ne' hd₁p.ne'] at hc₁
  rw [Real.logb_div hX₂.ne' hd₂p.ne'] at hc₂
  rw [Real.logb_mul hX₁.ne' hX₂.ne'] at hcap
  have hb₁ : 0< max 1 b₁:=zero_lt_one.trans_le (le_max_left _ _)
  have hb₂ : 0< max 1 b₂:=zero_lt_one.trans_le (le_max_left _ _)
  dsimp only
  refine ⟨hc₁.1,hc₂.1,?_⟩
  rw [Real.logb_mul hb₁.ne' hb₂.ne']
  linarith [hc₁.2,hc₂.2]

lemma eventually_fixed_clipping_cost (b₁ b₂ delta : ℝ) (hdelta : 0< delta) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ Real.logb Z (max 1 b₁*max 1 b₂)≤ delta := by
  have hc:=(tendsto_rpow_atTop hdelta).eventually (eventually_ge_atTop (max 1 b₁*max 1 b₂))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc] with Z hZ hC
  refine ⟨hZ,?_⟩
  exact (Real.logb_le_iff_le_rpow hZ (mul_pos
    (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _)))).mpr hC
end CenteredMomentCommonMaskChildCapacity

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentAllocatedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained CenteredMomentEligibleEnergy
open CenteredMomentCommonRadialData
local notation "O" => Eisenstein.O

def clippingLoss (Z U₁ U₂ : ℝ) : ℝ :=
  max (-Real.logb Z U₁) 0+max (-Real.logb Z U₂) 0

lemma clipped_log (Z U : ℝ) (hZ : 1< Z) (hU : 0< U) :
    Real.logb Z (clippedScale U)=Real.logb Z U+max (-Real.logb Z U) 0 := by
  by_cases h : 1≤ U
  · rw [clippedScale,max_eq_right h,max_eq_right (neg_nonpos.mpr (Real.logb_nonneg hZ h))]
    ring
  · have hu : U≤1 := (lt_of_not_ge h).le
    have hl : Real.logb Z U≤0 := Real.logb_nonpos hZ hU.le hu
    rw [clippedScale,max_eq_left hu,max_eq_left (neg_nonneg.mpr hl),Real.logb_one]
    ring

lemma clipped_pair_log (Z U₁ U₂ : ℝ) (hZ : 1< Z) (h₁ : 0< U₁) (h₂ : 0< U₂) :
    Real.logb Z (clippedScale U₁)+Real.logb Z (clippedScale U₂)=
      Real.logb Z U₁+Real.logb Z U₂+clippingLoss Z U₁ U₂ := by
  rw [clipped_log Z U₁ hZ h₁,clipped_log Z U₂ hZ h₂]
  unfold clippingLoss
  ring

lemma clipping_loss_bound (Z U₁ U₂ b₁ b₂ : ℝ) (hZ : 1< Z)
    (h₁ : 0< U₁) (h₂ : 0< U₂) (hs₁ : 1≤ U₁*b₁) (hs₂ : 1≤ U₂*b₂) :
    0≤ clippingLoss Z U₁ U₂ ∧
      clippingLoss Z U₁ U₂≤ Real.logb Z (max 1 b₁*max 1 b₂) := by
  have one (U b : ℝ) (hU : 0< U) (hs : 1≤ U*b) :
      max (-Real.logb Z U) 0≤ Real.logb Z (max 1 b) := by
    have hb : 0< max 1 b := zero_lt_one.trans_le (le_max_left _ _)
    have hc : clippedScale U≤ max 1 b*U := by
      apply max_le
      · exact hs.trans (by nlinarith [le_max_right (1:ℝ) b])
      · nlinarith [le_max_left (1:ℝ) b]
    have hl := Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (clippedScale_ge_one U)) hc
    rw [clipped_log Z U hZ hU,Real.logb_mul hb.ne' hU.ne'] at hl
    linarith
  refine ⟨add_nonneg (le_max_right _ _) (le_max_right _ _),?_⟩
  rw [Real.logb_mul (ne_of_gt (zero_lt_one.trans_le (le_max_left (1:ℝ) b₁)))
    (ne_of_gt (zero_lt_one.trans_le (le_max_left (1:ℝ) b₂)))]
  exact add_le_add (one U₁ b₁ h₁ hs₁) (one U₂ b₂ h₂ hs₂)

lemma profile_polynomial_survives (χ : Character) (V : Plain) (U : ℝ) (hU : 0< U)
    (t X σ v : ℝ) (hn : HeckeDyadic.polynomial χ false (V.profile U hU t) X σ v≠0) :
    1≤ U*V.b := by
  by_contra hs
  rw [V.profile_zero U hU t (lt_of_not_ge hs)] at hn
  exact hn (by simp [HeckeDyadic.polynomial,HeckeDyadic.summand])

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def plainLogs (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ : ℝ) : ℝ :=
  Real.logb Z (clippedScale (rawScale D a X₁ 0))+
    Real.logb Z (clippedScale (rawScale D a X₂ 1))

def remainingLogs (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z : ℝ) (P : ι→ℝ) : ℝ := ∑i∈liveIndices D a,Real.logb Z (P i)

def preVolume (s : Data ι) : ℝ := s.X₁*s.X₂*∏i,s.P i

omit [DecidableEq ι] in
lemma preVolume_pos (s : Data ι) : 0< preVolume s :=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=> s.P_pos i))

lemma selectedNorm_ge_one (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) :
    1≤ selectedNorm D a := by
  have hn (j : Fin 2) : (1:ℝ)≤ Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  exact one_le_mul_of_one_le_of_one_le (hn 0) (hn 1)

lemma formalReduction_ge_one (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (P : ι→ℝ) (hP : ∀i,1≤ P i) : 1≤ formalReductionFactor D a P :=
  one_le_mul_of_one_le_of_one_le (selectedNorm_ge_one D a)
    (Finset.one_le_prod (fun i _=> hP i))

lemma remainingLogs_le (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z : ℝ) (hZ : 1< Z) (P : ι→ℝ) (hP : ∀i,1≤ P i) :
    remainingLogs D a Z P≤∑i,Real.logb Z (P i) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=> Real.logb_nonneg hZ (hP i))

lemma raw_volume (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (X₁ X₂ : ℝ) (P : ι→ℝ) (hP : ∀i,0< P i) :
    rawScale D a X₁ 0*rawScale D a X₂ 1*(∏i∈liveIndices D a,P i)=
      (X₁*X₂*∏i,P i)/formalReductionFactor D a P := by
  have hr : 0< formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=> hP i))
  apply (eq_div_iff hr.ne').mpr
  simpa only [rawScale,div_mul_div_comm,rawRemaining,selectedNorm] using
    CenteredMomentDivisorRaw.raw_scale_identity D a (X₁*X₂) P

lemma raw_log_volume (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ : ℝ) (h₁ : 0< X₁) (h₂ : 0< X₂) (P : ι→ℝ) (hP : ∀i,0< P i) :
    Real.logb Z (rawScale D a X₁ 0)+Real.logb Z (rawScale D a X₂ 1)+remainingLogs D a Z P=
      Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P) := by
  have hr : 0< formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=> hP i))
  have hh := congrArg (Real.logb Z) (raw_volume D a X₁ X₂ P hP)
  rw [Real.logb_div (mul_pos (mul_pos h₁ h₂) (Finset.prod_pos (fun i _=> hP i))).ne' hr.ne',
    Real.logb_mul (mul_pos (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1)).ne'
      (Finset.prod_pos (fun i _=> hP i)).ne',
    Real.logb_mul (rawScale_pos D a X₁ h₁ 0).ne' (rawScale_pos D a X₂ h₂ 1).ne',
    Real.logb_prod _ _ (fun i _=>(hP i).ne')] at hh
  exact hh

theorem affine_exact (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (hZ : 1< Z) (h₁ : 0< X₁) (h₂ : 0< X₂)
    (P : ι→ℝ) (hP : ∀i,0< P i) :
    plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M=
      Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*remainingLogs D a Z P+
        clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) := by
  have hv := raw_log_volume D a Z X₁ X₂ h₁ h₂ P hP
  rw [plainLogs,clipped_pair_log Z _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1)]
  nlinarith

theorem excess_le (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ M : ℝ) (hZ : 1< Z) (h₁ : 0< X₁) (h₂ : 0< X₂)
    (P : ι→ℝ) (hP : ∀i,1≤ P i) (hκ : (1/6:ℝ)≤κ)
    (hs₁ : 1≤ rawScale D a X₁ 0*b₁) (hs₂ : 1≤ rawScale D a X₂ 1*b₂) :
    max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0≤
      max (Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*(∑i,Real.logb Z (P i))+Real.logb Z (max 1 b₁*max 1 b₂)) 0 := by
  rw [affine_exact D a Z X₁ X₂ κ M hZ h₁ h₂ P (fun i=> zero_lt_one.trans_le (hP i))]
  have hc := (clipping_loss_bound Z _ _ b₁ b₂ hZ
    (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂).2
  have hp := mul_le_mul_of_nonneg_left (remainingLogs_le D a Z hZ P hP)
    (by linarith : 0≤6*κ-1)
  exact max_le_max (by linarith) le_rfl

theorem allocated_survives (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O)
    (X₁ X₂ : ℝ) (h₁ : 0< X₁) (h₂ : 0< X₂)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0) :
    1≤ rawScale D a X₁ 0*s.b₁ ∧ 1≤ rawScale D a X₂ 1*s.b₂ := by
  have hz (hs : rawScale D a X₁ 0*s.b₁<1 ∨ rawScale D a X₂ 1*s.b₂<1) : False := by
    apply hne
    exact CenteredMomentCommonMaskEnergy.original_retained_zero s.η s.m s.A z _ _ _ _
      s.support₁ s.support₂ (fun i : liveIndices D a=> s.slots i)
      (fun i : liveIndices D a=> s.coefficient i) (fun i : liveIndices D a=> s.P i)
      s.t _ _ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs
  constructor
  · exact le_of_not_gt (fun hh=> hz (Or.inl hh))
  · exact le_of_not_gt (fun hh=> hz (Or.inr hh))

theorem paired_capacity (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z κ M : ℝ) (hZ : 1< Z) (hκ : (1/6:ℝ)≤κ) (hP : ∀i,1≤ s.P i) :
    let bound := max (Real.logb Z (preVolume s)-Real.logb Z (formalReductionFactor D a s.P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0
    (∀z,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.X₁ s.X₂≠0 →
      max (plainLogs D a Z s.X₁ s.X₂+6*κ*remainingLogs D a Z s.P-M) 0≤ bound) ∧
    (∀z,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.Y₁ s.Y₂≠0 →
      max (plainLogs D a Z s.Y₁ s.Y₂+6*κ*remainingLogs D a Z s.P-M) 0≤ bound) := by
  constructor
  · intro z hn
    obtain ⟨h₁,h₂⟩ := allocated_survives s D a z s.X₁ s.X₂ s.X₁_pos s.X₂_pos hn
    exact excess_le D a Z _ _ _ _ κ M hZ s.X₁_pos s.X₂_pos s.P hP hκ h₁ h₂
  · intro z hn
    obtain ⟨h₁,h₂⟩ := allocated_survives s D a z s.Y₁ s.Y₂ s.Y₁_pos s.Y₂_pos hn
    have hb := excess_le D a Z _ _ _ _ κ M hZ s.Y₁_pos s.Y₂_pos s.P hP hκ h₁ h₂
    simpa only [s.same_product,preVolume] using hb

omit [DecidableEq ι] in
theorem common_preVolume (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    preVolume (commonData s C R B)=preVolume s.toData/
      CenteredMomentCommonRawScale.rawReduction B.val s.P := by
  have hr := CenteredMomentCommonRawScale.rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  apply (eq_div_iff hr.ne').mpr
  simpa only [preVolume,commonData,div_mul_div_comm,
    CenteredMomentCommonRawScale.remainingRaw,CenteredMomentCommonRawScale.plainNorm] using
      CenteredMomentCommonRawScale.raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P

omit [DecidableEq ι] in
lemma common_reduction_ge_one (s : Input ι) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) (hP : ∀i,1≤ s.P i) :
    1≤ CenteredMomentCommonRawScale.rawReduction B.val s.P := by
  have hn (j : ι⊕Fin 2) : (1:ℝ)≤ Ideal.absNorm (B.val j) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B j))
  apply one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (hn (Sum.inr 0)) (hn (Sum.inr 1)))
  apply Finset.one_le_prod
  intro i _
  unfold CenteredMomentCommonRawScale.frozenScale
  split_ifs
  · exact le_rfl
  · exact hP i

omit [DecidableEq ι] in
lemma common_slot_logs_le (s : Input ι) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (Z : ℝ) (hZ : 1< Z) (hP : ∀i,1≤ s.P i) :
    (∑i : CenteredMomentCommonProfile.liveIndices B.val,Real.logb Z (s.P i))≤
      ∑i,Real.logb Z (s.P i) := by
  rw [Finset.sum_coe_sort (CenteredMomentCommonProfile.liveIndices B.val) (fun i : ι=> Real.logb Z (s.P i))]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=> Real.logb_nonneg hZ (hP i))

theorem common_allocated_raw_volume (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (D : Ideal O) (a : Allocation D
      (Finset.univ : Finset ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2))) :
    let v := commonData s C R B
    let result := preVolume s.toData/(CenteredMomentCommonRawScale.rawReduction B.val s.P*
      formalReductionFactor D a v.P)
    rawScale D a v.X₁ 0*rawScale D a v.X₂ 1*(∏i∈liveIndices D a,v.P i)=result ∧
      rawScale D a v.Y₁ 0*rawScale D a v.Y₂ 1*(∏i∈liveIndices D a,v.P i)=result := by
  dsimp only
  have hx := raw_volume D a (commonData s C R B).X₁ (commonData s C R B).X₂
    (commonData s C R B).P (commonData s C R B).P_pos
  have hy := raw_volume D a (commonData s C R B).Y₁ (commonData s C R B).Y₂
    (commonData s C R B).P (commonData s C R B).P_pos
  change _=preVolume (commonData s C R B)/_ at hx
  rw [common_preVolume s C R B,div_div] at hx
  rw [(commonData s C R B).same_product] at hy
  change _=preVolume (commonData s C R B)/_ at hy
  rw [common_preVolume s C R B,div_div] at hy
  exact ⟨hx,hy⟩

theorem common_paired_capacity (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (D : Ideal O) (a : Allocation D
      (Finset.univ : Finset ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2)))
    (Z κ M : ℝ) (hZ : 1< Z) (hκ : (1/6:ℝ)≤κ) (hP : ∀i,1≤ s.P i) :
    let v := commonData s C R B
    let bound := max (Real.logb Z (preVolume s.toData)-
      Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
      Real.logb Z (formalReductionFactor D a v.P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0
    (∀z,allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P D a
      v.W₁ v.W₂ v.X₁ v.X₂≠0 →
      max (plainLogs D a Z v.X₁ v.X₂+6*κ*remainingLogs D a Z v.P-M) 0≤ bound) ∧
    (∀z,allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P D a
      v.W₁ v.W₂ v.Y₁ v.Y₂≠0 →
      max (plainLogs D a Z v.Y₁ v.Y₂+6*κ*remainingLogs D a Z v.P-M) 0≤ bound) := by
  dsimp only
  obtain ⟨hx,hy⟩ := paired_capacity (commonData s C R B) D a Z κ M hZ hκ (fun i=> hP i)
  have hv : Real.logb Z (preVolume (commonData s C R B))=
      Real.logb Z (preVolume s.toData)-Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P) := by
    rw [common_preVolume s C R B,Real.logb_div (preVolume_pos s.toData).ne'
      (CenteredMomentCommonRawScale.rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos).ne']
  have hl := mul_le_mul_of_nonneg_left (common_slot_logs_le s C B Z hZ hP)
    (by linarith : 0≤6*κ-1)
  have hb : max (Real.logb Z (preVolume (commonData s C R B))-
      Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
      (6*κ-1)*(∑i,Real.logb Z ((commonData s C R B).P i))+
      Real.logb Z (max 1 (commonData s C R B).b₁*max 1 (commonData s C R B).b₂)) 0≤
      max (Real.logb Z (preVolume s.toData)-
        Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
        Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
        (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0 := by
    rw [hv]
    apply max_le_max _ le_rfl
    change _≤ Real.logb Z (preVolume s.toData)-
      Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
      Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)
    dsimp only [commonData]
    linarith
  exact ⟨fun z hz=>(hx z hz).trans hb,fun z hz=>(hy z hz).trans hb⟩

theorem excess_le_remaining (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ M : ℝ) (hZ : 1< Z) (h₁ : 0< X₁) (h₂ : 0< X₂)
    (P : ι→ℝ) (hP : ∀i,0< P i)
    (hs₁ : 1≤ rawScale D a X₁ 0*b₁) (hs₂ : 1≤ rawScale D a X₂ 1*b₂) :
    max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0≤
      max (Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*remainingLogs D a Z P+Real.logb Z (max 1 b₁*max 1 b₂)) 0 := by
  rw [affine_exact D a Z X₁ X₂ κ M hZ h₁ h₂ P hP]
  have hc := (clipping_loss_bound Z _ _ b₁ b₂ hZ
    (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂).2
  exact max_le_max (by linarith) le_rfl

theorem allocated_clipping (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O)
    (Z X₁ X₂ : ℝ) (hZ : 1< Z) (h₁ : 0< X₁) (h₂ : 0< X₂)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0) :
    plainLogs D a Z X₁ X₂=Real.logb Z (rawScale D a X₁ 0)+Real.logb Z (rawScale D a X₂ 1)+
      clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) ∧
    0≤ clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) ∧
    clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1)≤ Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  obtain ⟨hs₁,hs₂⟩ := allocated_survives s D a z X₁ X₂ h₁ h₂ hne
  exact ⟨clipped_pair_log Z _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1),
    clipping_loss_bound Z _ _ _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂⟩

lemma native_excess (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) :
    CenteredMomentLiveCapacity.excess (liveIndices D a) (fun i=> Real.logb Z (P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) M κ=
      max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0 := rfl

end CenteredMomentAllocatedChildCapacity

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstSecondCapacityLedger
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentLiveCapacity
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem formal_reduction_pays_slots (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z:ℝ)(hZ:1< Z)(P:ι→ℝ)(hP:∀i,1≤ P i):
    (∑i,Real.logb Z (P i))-remainingLogs D a Z P≤
      Real.logb Z (formalReductionFactor D a P) := by
  have hp:∀i,0< P i:=fun i=> zero_lt_one.trans_le (hP i)
  have hs:=congrArg (Real.logb Z) (split_slot_product D a P)
  rw [Real.logb_mul (Finset.prod_pos (fun i _=> hp i)).ne'
    (Finset.prod_pos (fun i _=> hp i)).ne',
    Real.logb_prod _ _ (fun i _=>(hp i).ne'),
    Real.logb_prod _ _ (fun i _=>(hp i).ne'),
    Real.logb_prod _ _ (fun i _=>(hp i).ne')] at hs
  rw [formalReductionFactor,Real.logb_mul (selectedNorm_pos D a).ne'
    (Finset.prod_pos (fun i _=> hp i)).ne',
    Real.logb_prod _ _ (fun i _=>(hp i).ne')]
  have hn:=Real.logb_nonneg hZ (selectedNorm_ge_one D a)
  dsimp only [remainingLogs]
  linarith

theorem affine_reduction_le_parent (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z κ:ℝ)(hZ:1< Z)(hκ:0≤κ)(P:ι→ℝ)(hP:∀i,1≤ P i):
    -Real.logb Z (formalReductionFactor D a P)+(6*κ-1)*remainingLogs D a Z P≤
      (6*κ-1)*(∑i,Real.logb Z (P i)) := by
  have hred:=formal_reduction_pays_slots D a Z hZ P hP
  have hrem:=remainingLogs_le D a Z hZ P hP
  nlinarith

theorem allocated_excess_from_parent (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ A M Mnom Mact w ell δ θ:ℝ)
    (hZ:1< Z)(h₁:0< X₁)(h₂:0< X₂)(hκ:0≤κ)
    (P:ι→ℝ)(hP:∀i,1≤ P i)
    (hs₁:1≤ rawScale D a X₁ 0*b₁)(hs₂:1≤ rawScale D a X₂ 1*b₂)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (P i))≤ M)
    (hshift:Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤ A-M+6*(w+ell)+δ)
    (hactual:Mnom≤ Mact)(hw:0≤ w)(hell:0≤ ell)(hδ:0≤δ)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 b₁*max 1 b₂)≤2*θ):
    excess (liveIndices D a) (fun i=> Real.logb Z (P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ≤
        6*(w+ell)+δ+2*θ := by
  rw [native_excess]
  apply (excess_le_remaining D a Z X₁ X₂ b₁ b₂ κ Mact hZ h₁ h₂ P
    (fun i=> zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le
  · have hr:=affine_reduction_le_parent D a Z κ hZ hκ P hP
    linarith
  · positivity

theorem live_allocated_excess (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ θ:ℝ)
    (hZ:1< Z)(h₁:0< X₁)(h₂:0< X₂)(hκ:0≤κ)(hP:∀i,1≤ s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤ M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤ A-M+6*(w+ell)+δ)
    (hactual:Mnom≤ Mact)(hw:0≤ w)(hell:0≤ ell)(hδ:0≤δ)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ):
    excess (liveIndices D a) (fun i=> Real.logb Z (s.P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ≤
        6*(w+ell)+δ+2*θ := by
  obtain ⟨hs₁,hs₂⟩:=allocated_survives s D a z X₁ X₂ h₁ h₂ hne
  exact allocated_excess_from_parent D a Z X₁ X₂ s.b₁ s.b₂ κ A M Mnom Mact
    w ell δ θ hZ h₁ h₂ hκ s.P hP hs₁ hs₂ hparent hshift hactual hw hell hδ hθ hclip

theorem live_whole_removal (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ θ mesh:ℝ)
    (hZ:1< Z)(h₁:0< X₁)(h₂:0< X₂)(hκ:0<κ)(hP:∀i,1≤ s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤ M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤ A-M+6*(w+ell)+δ)
    (hactual:Mnom≤ Mact)(hw:0≤ w)(hell:0≤ ell)(hδ:0≤δ)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ)
    (hm:0≤ mesh)(hmesh:∀i∈liveIndices D a,Real.logb Z (s.P i)≤ mesh):
    ∃removed:Finset ι,removed⊆liveIndices D a ∧
      (removed=liveIndices D a ∨
        plainLogs D a Z X₁ X₂+6*κ*(∑i∈liveIndices D a\removed,Real.logb Z (s.P i))≤ Mact) ∧
      κ*(∑i∈removed,Real.logb Z (s.P i))≤ w+ell+δ/6+θ/3+κ*mesh := by
  have he:=live_allocated_excess s D a z Z X₁ X₂ κ A M Mnom Mact w ell δ θ
    hZ h₁ h₂ hκ.le hP hne hparent hshift hactual hw hell hδ hθ hclip
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a)
    (fun i=> Real.logb Z (s.P i))
    (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
    (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ mesh hκ hm
    (fun i _=> Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  linarith

theorem paired_edge_cost (shell width₁ width₂ cost₁ cost₂ w ell δ₁ δ₂ θ κ mesh:ℝ)
    (hs:shell≤2*θ)(hwidth₁:width₁≤δ₂)(hwidth₂:width₂≤δ₂)
    (hc₁:cost₁≤ w+ell+δ₁/6+θ/3+κ*mesh)
    (hc₂:cost₂≤ w+ell+δ₁/6+θ/3+κ*mesh):
    shell+(width₁+width₂)/2+(cost₁+cost₂)/2-(w+ell)≤
      δ₂+δ₁/6+κ*mesh+7*θ/3 := by linarith

theorem edge_loss_budget (δ₁ δ₂ θ κ mesh ξ η:ℝ)
    (hδ₁:δ₁≤ξ)(hδ₂:δ₂≤ξ)(hθ:θ≤ξ)(hκ:κ≤1)
    (hm:0≤ mesh)(hmesh:mesh≤η):
    δ₂+δ₁/6+κ*mesh+7*θ/3≤7*ξ/2+η := by
  nlinarith

end CenteredMomentFirstSecondCapacityLedger

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstSecondCapacityLedger
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentLiveCapacity
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
local notation "O"=> Eisenstein.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

lemma width_defect_cost (x B δ:ℝ)(hB:0≤ B)(hδ:0≤δ)(hx:x≤δ):
    x+max (B-x) 0/6≤δ+B/6 := by
  by_cases h:0≤ B-x
  · rw [max_eq_left h];linarith
  · rw [max_eq_right (le_of_not_ge h)];linarith

theorem live_allocated_excess_defect (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ θ:ℝ)
    (hZ:1< Z)(h₁:0< X₁)(h₂:0< X₂)(hκ:0≤κ)(hP:∀i,1≤ s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤ M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤ A-M+6*(w+ell)+δ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ):
    excess (liveIndices D a) (fun i=> Real.logb Z (s.P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ≤
        max (6*(w+ell)+δ+2*θ+Mnom-Mact) 0 := by
  obtain ⟨hs₁,hs₂⟩:=allocated_survives s D a z X₁ X₂ h₁ h₂ hne
  rw [native_excess]
  apply (excess_le_remaining D a Z X₁ X₂ s.b₁ s.b₂ κ Mact hZ h₁ h₂ s.P
    (fun i=> zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le_max _ le_rfl
  have hr:=affine_reduction_le_parent D a Z κ hZ hκ s.P hP
  linarith

theorem live_removal_width_cost (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ₁ δ₂ θ mesh:ℝ)
    (hZ:1< Z)(h₁:0< X₁)(h₂:0< X₂)(hκ:0<κ)(hP:∀i,1≤ s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤ M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤ A-M+6*(w+ell)+δ₁)
    (hwidth:Mact-Mnom≤δ₂)(hw:0≤ w)(hell:0≤ ell)(hδ₁:0≤δ₁)(hδ₂:0≤δ₂)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ)
    (hm:0≤ mesh)(hmesh:∀i∈liveIndices D a,Real.logb Z (s.P i)≤ mesh):
    ∃removed:Finset ι,removed⊆liveIndices D a ∧
      (removed=liveIndices D a ∨
        plainLogs D a Z X₁ X₂+6*κ*(∑i∈liveIndices D a\removed,Real.logb Z (s.P i))≤ Mact) ∧
      Mact-Mnom+κ*(∑i∈removed,Real.logb Z (s.P i))≤
        δ₂+w+ell+δ₁/6+θ/3+κ*mesh := by
  have he:=live_allocated_excess_defect s D a z Z X₁ X₂ κ A M Mnom Mact w ell δ₁ θ
    hZ h₁ h₂ hκ.le hP hne hparent hshift hclip
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a)
    (fun i=> Real.logb Z (s.P i))
    (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
    (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ mesh hκ hm
    (fun i _=> Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  have hh:=width_defect_cost (Mact-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mact-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mact by ring] at hh
  linarith

theorem source_removal_width_cost (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ A M Mnom Mact w ell δ₁ δ₂ θ mesh:ℝ)
    (hZ:1< Z)(h₁:0< X₁)(h₂:0< X₂)(hκ:0<κ)(hP:∀i,1≤ s.P i)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤ M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤ A-M+6*(w+ell)+δ₁)
    (hwidth:Mact-Mnom≤δ₂)(hw:0≤ w)(hell:0≤ ell)(hδ₁:0≤δ₁)(hδ₂:0≤δ₂)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ)
    (hm:0≤ mesh)(hmesh:∀i∈liveIndices D a,Real.logb Z (s.P i)≤ mesh):
    ∃removed:Finset ι,removed⊆liveIndices D a ∧
      (removed=liveIndices D a ∨
        plainLogs D a Z X₁ X₂+6*κ*(∑i∈liveIndices D a\removed,Real.logb Z (s.P i))≤ Mact) ∧
      ((∃z:O,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
          s.W₁ s.W₂ X₁ X₂≠0) →
        Mact-Mnom+κ*(∑i∈removed,Real.logb Z (s.P i))≤
          δ₂+w+ell+δ₁/6+θ/3+κ*mesh) := by
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a)
    (fun i=> Real.logb Z (s.P i))
    (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
    (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ mesh hκ hm
    (fun i _=> Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  rintro ⟨z,hne⟩
  have he:=live_allocated_excess_defect s D a z Z X₁ X₂ κ A M Mnom Mact w ell δ₁ θ
    hZ h₁ h₂ hκ.le hP hne hparent hshift hclip
  have hh:=width_defect_cost (Mact-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mact-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mact by ring] at hh
  linarith

theorem paired_width_defect_cost (shell edge₁ edge₂ w ell δ₁ δ₂ θ κ mesh:ℝ)
    (hs:shell≤2*θ)
    (h₁:edge₁≤δ₂+w+ell+δ₁/6+θ/3+κ*mesh)
    (h₂:edge₂≤δ₂+w+ell+δ₁/6+θ/3+κ*mesh):
    shell+(edge₁+edge₂)/2-(w+ell)≤δ₂+δ₁/6+κ*mesh+7*θ/3 := by linarith

end CenteredMomentFirstSecondCapacityLedger

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
noncomputable section
namespace CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentSectorLocalization
def ratioPenalty (n:Fin 4→ℤ):ℝ:=
  max 1 (1/(dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))


end CenteredMomentFirstAmplifiedCapacityCommon

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
