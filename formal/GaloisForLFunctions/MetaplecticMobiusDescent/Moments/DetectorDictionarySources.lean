/-
Detector dictionary sources adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.FinalAssemblyData

/-!
# Detector dictionary sources

Source moment bases of the detector dictionary, fixed ideals of natural fixed-ray sources,
initial states and profiles; plain unmarked allowances, radial majorants, relative classes and
profile control.
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
open scoped Classical BigOperators ComplexConjugate

namespace CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer CenteredMomentRetainedEnergy
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugation preserves the norm of each physical row and its two smooth factors. -/
theorem source_plain_pair_norm
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ ψ : Character) (m u : O) (reverse : Bool)
    (hrow : ∀n,elementCoeff ψ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (1*u) n)
    (hc : ∀I : Ideal O,idealCoeff χ I=if reverse then conj (idealCoeff ψ I) else idealCoeff ψ I)
    (hmLam : lambda∣m) (hMm : M≤ Ideal.span {m})
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hP : ∀i,0< P i)
    (hη : ∀i,∀J∈primePool M H (b i) (P i),V i ((J.absNorm:ℝ)/(P i))≠0→ IsCoprime J η.modulus) :
    ‖polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u (V i) (b i) (P i) (external i)‖ =
    ‖positiveSlotRow η m 1 u
      (twistProfile (orientedProfile reverse W₁) σ (orientedFrequency reverse t))
      (twistProfile (orientedProfile reverse W₂) σ (orientedFrequency reverse t))
      (fun i=> primePool M H (b i) (P i))
      (fun i=> physicalSlotCoefficient η (V i) (P i) (external i)) P 0 X₁ X₂‖ := by
  rw [positiveSlotRow_eq_product η ψ m 1 u hrow _ _ _ _ P _ _ _ _ hX₁ hX₂ hP]
  simp only [norm_mul,norm_prod]
  rw [norm_of_oriented_coefficients χ ψ reverse hc false W₁ X₁ σ t hX₁,
    norm_of_oriented_coefficients χ ψ reverse hc false W₂ X₂ σ t hX₂]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [physical_slot_conj M H η m u hmLam hMm (V i) (b i) (P i) (external i) (hP i) (hη i),RCLike.norm_conj]

theorem momentData_plain_pair_norm
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ : Character) (u : FreeRow) (reverse : Bool)
    (hc : ∀I : Ideal O,idealCoeff χ I=if reverse then
      conj (idealCoeff ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u)) I)
      else idealCoeff ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u)) I)
    (hMm : M≤ Ideal.span {ProbeHighRowFamily.rowMaskElement})
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hP : ∀i,0< P i)
    (hη : ∀i,∀J∈primePool M H (b i) (P i),V i ((J.absNorm:ℝ)/(P i))≠0→ IsCoprime J η.modulus) :
    ‖polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (P i) (external i)‖ =
    ‖positiveSlotRow η ProbeHighRowFamily.rowMaskElement 1 u.val
      (twistProfile (orientedProfile reverse W₁) σ (orientedFrequency reverse t))
      (twistProfile (orientedProfile reverse W₂) σ (orientedFrequency reverse t))
      (fun i=> primePool M H (b i) (P i))
      (fun i=> physicalSlotCoefficient η (V i) (P i) (external i)) P 0 X₁ X₂‖ := by
  apply source_plain_pair_norm M H η χ
    ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u))
    ProbeHighRowFamily.rowMaskElement u.val reverse _ hc (dvd_mul_left _ _) hMm
    W₁ W₂ V b P external X₁ X₂ σ t hX₁ hX₂ hP hη
  intro n
  simpa only [ProbeHighRowFamily.momentData,ProbeHighRowFamily.momentElement,one_mul] using
    (ProbeHighRowFamily.momentData η).character_spec (ProbeHighRowFamily.momentElement u) n

end CenteredMomentDetectorDictionary

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorRawFiber HeckeDetectorRowwisePolynomial
open HeckeDetectorDyadicProfiles CenteredMomentRetainedEnergy
open CenteredMomentPrimeSlot ProbeHighRowFamily
local notation "O" => Eisenstein.O
variable {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def detectorPositiveRow (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (selected : Finset Slot) (j k : ℕ) (σ t : ℝ) (u : FreeRow) : ℂ :=
  positiveSlotRow η rowMaskElement 1 u.val
    (twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (fun s : selected=> primePool M H (F.upper s.val) (U^(F.widths s.val)))
    (fun s : selected=> physicalSlotCoefficient η (F.profile s.val) (U^(F.widths s.val)) (F.external s.val))
    (fun s : selected=> U^(F.widths s.val)) 0 (U^F.m) (U^F.m)

/-- The finite fiber energy equals the energy of the corresponding positive rows. -/
theorem fiber_plain_energy_eq (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤ Ideal.span {rowMaskElement}) (hU : 0< U)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (hη : ∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→ IsCoprime J η.modulus) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t*
        F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2 := by
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  have hc := F.row_coeff u hu
  rw [hdata] at hc
  have he := momentData_plain_pair_norm M H η (F.family u F.label) u F.reverse hc hMm
    ((logProfile^[j]) positiveAnnular) ((logProfile^[k]) positiveAnnular)
    (fun s : selected=> F.profile s.val) (fun s : selected=> F.upper s.val)
    (fun s : selected=> U^(F.widths s.val)) (fun s : selected=> F.external s.val)
    (U^F.m) (U^F.m) σ t (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _)
    (fun s=> Real.rpow_pos_of_pos hU _) (fun s=> hη s.val s.property)
  have hprod := Finset.prod_coe_sort selected (fun s=> HeckePrimeRow.canonicalPrimeAmplitude M H u.val
    (F.profile s) (F.upper s) (U^(F.widths s)) (F.external s))
  rw [hprod] at he
  simpa only [detectorPositiveRow,Fiber.physicalProduct,HeckeDetectorPhysicalSelection.physical,
    Finset.prod_coe_sort] using he

theorem fiber_plain_unmarked_energy_eq (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤ Ideal.span {rowMaskElement}) (hU : 0< U)
    (j k : ℕ) (σ t : ℝ) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t‖^2)=
      ∑u∈F.rows,‖detectorPositiveRow F η ∅ j k σ t u‖^2 := by
  simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one] using
    fiber_plain_energy_eq F η hdata hMm hU ∅ j k σ t (by simp)

end CenteredMomentDetectorDictionary

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Filter
namespace CenteredMomentDetectorDictionary
open HeckeFamily CenteredMomentPrimeSlot
local notation "O" => Eisenstein.O

lemma annular_prime_coprime (η : Character) (a D : ℝ) (ha : 0< a) (hD : 0< D)
    (hlarge : (η.modulus.absNorm:ℝ)/a< D)
    (W : ℝ→ℂ) (hs : Function.support W⊆Set.Ici a)
    (P : Ideal O) (hp : Prime P) (hW : W ((P.absNorm:ℝ)/D)≠0) :
    IsCoprime P η.modulus := by
  apply ProbeRaySlots.prime_coprime_of_norm_gt η ⟨P,hp⟩
  have hlo : a*D≤(P.absNorm:ℝ) := (le_div_iff₀ hD).mp (hs hW)
  have hh : (η.modulus.absNorm:ℝ)< a*D := by
    have hh := (div_lt_iff₀ ha).mp hlarge
    nlinarith
  exact hh.trans_le hlo

theorem eventually_primePool_coprime (η : Character) (a : ℝ) (ha : 0< a) :
    ∀ᶠD : ℝ in atTop,∀(M : Ideal O)(H : Subgroup (O⧸M)ˣ)(W : ℝ→ℂ)(b : ℝ),
      Function.support W⊆Set.Ici a →
      ∀P∈primePool M H b D,W ((P.absNorm:ℝ)/D)≠0→ IsCoprime P η.modulus := by
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_gt_atTop ((η.modulus.absNorm:ℝ)/a)] with D hD hlarge
  intro M H W b hs P hP hW
  exact annular_prime_coprime η a D ha hD hlarge W hs P (Finset.mem_filter.mp hP).2.1 hW

theorem eventually_primePool_power_coprime (η : Character) (a ell : ℝ) (ha : 0< a) (hell : 0< ell) :
    ∀ᶠZ : ℝ in atTop,∀(M : Ideal O)(H : Subgroup (O⧸M)ˣ)(W : ℝ→ℂ)(b : ℝ),
      Function.support W⊆Set.Ici a →
      ∀P∈primePool M H b (Z^ell),W ((P.absNorm:ℝ)/(Z^ell))≠0→ IsCoprime P η.modulus :=
  (tendsto_rpow_atTop hell).eventually (eventually_primePool_coprime η a ha)

end CenteredMomentDetectorDictionary

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace CenteredMomentDetectorDictionary
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbePhysical CenteredMomentPrimeSlot
local notation "O" => Eisenstein.O

lemma source_product_le_rowMask (S : Finset (Ideal O))
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) :
    (∏P∈S,P)≤ Ideal.span {rowMaskElement} := by
  apply Ideal.dvd_iff_le.mp
  have hne : ramifiedIdeal ≠ cubicTwoIdeal := by
    intro he
    have hn := congrArg Ideal.absNorm he
    rw [ramifiedIdeal_absNorm, cubicTwoIdeal_absNorm] at hn
    norm_num at hn
  have hd := Finset.prod_dvd_prod_of_subset CanonicalRowCompletion.fixedBadPrimes S
    (fun P : Ideal O => P) hbad
  have he : (∏ P ∈ CanonicalRowCompletion.fixedBadPrimes, P) =
      Ideal.span {rowMaskElement} := by
    rw [CanonicalRowCompletion.fixedBadPrimes, Finset.prod_pair hne]
    simp only [ramifiedIdeal, cubicTwoIdeal, Ideal.span_singleton_neg]
    rw [Ideal.span_singleton_mul_span_singleton]
    unfold rowMaskElement
    rw [mul_comm]
  rwa [he] at hd

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

def sourceMomentBase (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) :
    Sum Bool (RayQuotient.Characters M H)→ Character :=
  Sum.elim (fun b=> if b then fixedSourcePrincipal S hS else η.inverse.excludePrimes S hS)
    (fun θ=>(HeckeRayQuotient.character M H hH θ).inverse)

lemma sourceMomentData_base (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (j : Sum Bool (RayQuotient.Characters M H)) :
    sourceMomentData M H hH S hS η j=momentData (sourceMomentBase M H hH S hS η j) := by
  rcases j with b|θ
  · cases b <;> rfl
  · rfl

/-- Growing prime windows eventually avoid every fixed source conductor. -/
theorem eventually_source_slots_coprime {N : ℕ}
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (ell : Fin N→ℝ) (hell : ∀i,0< ell i) (a : ℝ) (ha : 0< a) :
    ∀ᶠZ : ℝ in atTop,∀j : Sum Bool (RayQuotient.Characters M H),∀i : Fin N,
      ∀d : ℝ,d≠0→∀(W : ℝ→ℂ)(b : ℝ),Function.support W⊆Set.Ici a→
      ∀P∈primePool M H b ((Z^d)^(ell i/d)),
        W ((P.absNorm:ℝ)/((Z^d)^(ell i/d)))≠0→
          IsCoprime P (sourceMomentBase M H hH S hS η j).modulus := by
  have he : ∀ᶠZ : ℝ in atTop,∀j : Sum Bool (RayQuotient.Characters M H),∀i : Fin N,
      ∀(W : ℝ→ℂ)(b : ℝ),Function.support W⊆Set.Ici a→
      ∀P∈primePool M H b (Z^(ell i)),W ((P.absNorm:ℝ)/(Z^(ell i)))≠0→
        IsCoprime P (sourceMomentBase M H hH S hS η j).modulus := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [eventually_primePool_power_coprime (sourceMomentBase M H hH S hS η j)
      a (ell i) ha (hell i)] with Z hz
    exact hz M H
  filter_upwards [he,eventually_ge_atTop (0:ℝ)] with Z hz hZ
  intro j i d hd W b hs
  have heq : (Z^d)^(ell i/d)=Z^(ell i) := by
    rw [←Real.rpow_mul hZ,mul_div_cancel₀ _ hd]
  rw [heq]
  exact hz j i W b hs

end CenteredMomentDetectorDictionary

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily 
local notation "O" => Eisenstein.O

variable {Δ : ℝ} {D : Parameters.HighData Δ}

def sourceFixedIdeal (F : ProbeFinalAssembly.SourceData D) : Ideal O :=
  F.modulus⊓Ideal.span {(72:O)}

lemma sourceFixedIdeal_ne_zero (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma sourceFixedIdeal_ne_top (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {lambda} ∈ F.S :=
    F.exclusions.bad (Finset.mem_insert_self _ _)
  have hle : F.modulus≤ Ideal.span {lambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=> P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : sourceFixedIdeal F≤ Ideal.span {lambda})))

lemma sourceFixedIdeal_le_modulus (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤ F.modulus := inf_le_left
lemma sourceFixedIdeal_le_72 (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤ Ideal.span {(72:O)} := inf_le_right

def sourceExceptional (F : ProbeFinalAssembly.SourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (sourceFixedIdeal F) η)
    (fixedBadMask*cubicIdealGenerator 1) 1 u.val

theorem source_retained_sector_nonprincipal (F : ProbeFinalAssembly.SourceData D)
    (η : Character) (u : FreeRow) (hu : ¬sourceExceptional F η u)
    (θ : RayQuotient.Characters F.modulus ⊤) :
    ((naturalRow η u.val u.property.1).character.product
      (relativeCharacter F.modulus ⊤ le_top η θ)).residue≠1 :=
  internal_sector_nonprincipal F.modulus ⊤ le_top (naturalRow η u.val u.property.1)
    η θ (sourceFixedIdeal F) 1 (sourceFixedIdeal_le_modulus F) one_ne_zero u.property.1 hu

theorem source_energy_split (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (rows : Finset FreeRow) (f : FreeRow→ℂ) :
    (∑u∈rows,‖f u‖^2)=
      (∑u∈rows.filter (fun u=>¬sourceExceptional F η u),‖f u‖^2)+
      ∑u∈rows.filter (sourceExceptional F η),‖f u‖^2 := by
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not rows (fun u=>¬sourceExceptional F η u)
      (fun u=>‖f u‖^2)).symm

end CenteredMomentNaturalFixedRaySource

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily UniqueFactorizationMonoid
open CenteredMomentDetectorDictionary CenteredExceptionalProfile CenteredExceptionalCount
open  CenteredMomentSecondHeightFamily
local notation "O" => Eisenstein.O

theorem fixed_inducing_free_support (η : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQ : Q≠⊤) (hQ72 : Q≤ Ideal.span {(72:O)}) (hQη : Q≤η.modulus)
    (m : O) (hm : m≠0) (hml : lambda∣m) (hm2 : (2:O)∣m)
    (u : FreeRow) (hu : FixedInducingRow η Q m 1 u.val) :
    u.val∈HeckeExceptionalRows.rows (normalizedFactors Q).toFinset := by
  obtain ⟨χ,ψ,hprim,hind,hψ,hχ⟩:=hu
  refine ⟨u.property.1,?_⟩
  intro P hP
  refine ⟨?_,u.property.2 P⟩
  by_contra hout
  have hp : Prime P:=prime_of_normalized_factor P hP
  let : P.IsMaximal:=(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  obtain ⟨hl,h2,hQP⟩:=outside_fixed_support Q hQ0 hQ72 P hp hout
  have hηP : IsCoprime η.modulus P:=hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hQη)
  have hz:=actual_row_numerator_valuation_zero η χ ψ hind Q hQ hQ72 hψ
    m 1 u.val hm one_ne_zero u.property.1 hml hm2
    (by simpa only [one_mul] using hχ) P hl h2 hQP hηP
  simp only [one_pow,one_mul,valuation] at hz
  have hpos:=Multiset.count_pos.mpr hP
  have hlt:=u.property.2 P
  omega

variable {Δ : ℝ} {D : Parameters.HighData Δ}

def sourceExceptionalBound (F : ProbeFinalAssembly.SourceData D) (η : Character) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors (internalQ (sourceFixedIdeal F) η)).toFinset

lemma source_exceptional_norm (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (u : FreeRow) (hu : sourceExceptional F η u) :
    (Ideal.span {u.val}).absNorm≤ sourceExceptionalBound F η := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=> prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  apply fixed_inducing_free_support η (internalQ (sourceFixedIdeal F) η)
    (internalQ_ne_zero _ (sourceFixedIdeal_ne_zero F) η)
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η)
    (inf_le_left.trans (sourceFixedIdeal_le_72 F)) inf_le_right
    (fixedBadMask*cubicIdealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (cubicIdealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

/-- Exceptional sixth-power-free rows have bounded norm and leave every growing window. -/
theorem eventually_source_no_exceptional (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀u : FreeRow,
      Z^(1/100:ℝ)≤ rowNorm u →
      ¬sourceExceptional F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u := by
  have hh : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (sourceExceptionalBound F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)< Z^(1/100:ℝ) := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).eventually (eventually_gt_atTop _)
  filter_upwards [hh] with Z hz
  intro label u hu hex
  have hb : rowNorm u≤(sourceExceptionalBound F
      (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ) := by
    change ((Ideal.span {u.val}).absNorm:ℝ)≤ _
    exact_mod_cast source_exceptional_norm F _ u hex
  exact (not_lt_of_ge (hu.trans hb)) (hz label)


end CenteredMomentNaturalFixedRaySource
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace CenteredMomentDetectorPlainSlotProfile
open HeckeFamily HeckeInverseAmplification HeckeDyadic CenteredMomentDetectorDictionary
open CenteredMomentRetainedEnergy
local notation "O"=> Eisenstein.O
variable {Δ:ℝ}{D:Parameters.HighData Δ}

lemma conjugate_source_support (F:ProbeFinalAssembly.SourceData D):
    Function.support (fun x=> conj (F.W x))⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  exact F.complex_support (by simpa using hx)

private lemma conjugate_source_smooth (F : ProbeFinalAssembly.SourceData D) :
    ContDiff ℝ ∞ (fun x => conj (F.W x)) := by
  exact Complex.conjCLE.contDiff.comp (F.W.smooth (⊤ : ℕ∞))

def slotSchwartz (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ):𝓢(ℝ,ℂ):=
  interpolatedProfile (fun x=> conj (F.W x)) 1 2 (by norm_num)
    (conjugate_source_support F) (conjugate_source_smooth F)
    (1-ζ.re) (-ζ.im)

theorem slotSchwartz_apply (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ)(x:ℝ):
    slotSchwartz F ζ x=conj (F.W x*(x:ℂ)^(ζ-1)) := by
  rw [slotSchwartz,interpolatedProfile_apply]
  unfold twistProfile
  by_cases hw:F.W x=0
  · simp [hw]
  have hx:0< x:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (F.complex_support hw).1
  rw [map_mul,conj_positive_cpow _ hx]
  congr 1
  congr 1
  apply Complex.ext <;> simp [HeckeDyadic.shift]

theorem slotSchwartz_support (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ):
    Function.support (slotSchwartz F ζ:ℝ→ℂ)⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  apply F.complex_support
  intro hw
  exact hx (by rw [slotSchwartz_apply,hw,zero_mul,map_zero])

theorem slotSchwartz_smooth (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ):
    ContDiff ℝ ∞ (slotSchwartz F ζ:ℝ→ℂ):=(slotSchwartz F ζ).smooth (⊤ : ℕ∞)

theorem slotSchwartz_norm (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ)(hζ:ζ.re≤1)(x:ℝ):
    ‖slotSchwartz F ζ x‖≤1 := by
  rw [slotSchwartz_apply,RCLike.norm_conj]
  by_cases hw:F.W x=0
  · simp [hw]
  have hx:=F.complex_support hw
  have hxpos:0< x:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hx.1
  have hW:‖F.W x‖≤1 := by
    rw [F.complex_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.bounded x).1]
    exact (F.bounded x).2
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  have hp:x^((ζ-1).re)≤1:=
    (Real.rpow_le_rpow_of_exponent_le hx.1 (by simp only [Complex.sub_re,Complex.one_re];linarith)).trans_eq
      (Real.rpow_zero _)
  simpa only [one_mul] using mul_le_mul hW hp (Real.rpow_nonneg hxpos.le _) zero_le_one

theorem physical_coefficient (F:ProbeFinalAssembly.SourceData D)(η:Character)
    (P:ℝ)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η F.W P ζ I=
      idealCoeff η.inverse I*slotSchwartz F ζ ((I.absNorm:ℝ)/P) := by
  rw [slotSchwartz_apply]
  rfl

theorem physical_coefficient_norm (F:ProbeFinalAssembly.SourceData D)(η:Character)
    (P:ℝ)(ζ:ℂ)(hζ:ζ.re≤1)(I:Ideal O):
    ‖physicalSlotCoefficient η F.W P ζ I‖≤1 := by
  rw [physical_coefficient,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (idealCoeff_norm_le_one η.inverse I)).trans (slotSchwartz_norm F ζ hζ _)

theorem slotSchwartz_uniform (F:ProbeFinalAssembly.SourceData D)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀ζ:ℂ,ζ.re∈Set.Icc (0:ℝ) 1 →
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz F ζ)≤ C*(1+‖ζ.im‖)^J := by
  obtain ⟨J,C,hC,hbound⟩:=interpolatedProfile_uniform (fun x=> conj (F.W x)) 1 2 (by norm_num)
    (conjugate_source_support F) (conjugate_source_smooth F) S
  refine ⟨J,C,hC,?_⟩
  intro ζ hζ
  have hh:=hbound (1-ζ.re) ⟨by linarith [hζ.2],by linarith [hζ.1]⟩ (-ζ.im)
  simpa only [slotSchwartz,norm_neg] using hh

theorem slotSchwartz_height_uniform (F:ProbeFinalAssembly.SourceData D)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀{ι:Type*}(ζ:ι→ℂ)(height:ℝ),0≤ height →
      (∀i,(ζ i).re=17/50) → (∀i,|(ζ i).im|≤ height) → ∀i,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz F (ζ i))≤ C*(1+height)^J := by
  obtain ⟨J,C,hC,hbound⟩:=slotSchwartz_uniform F S
  refine ⟨J,C,hC,?_⟩
  intro ι ζ height hheight hreal him i
  refine (hbound (ζ i) (by rw [hreal i];norm_num)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by simp only [Real.norm_eq_abs];linarith [him i]) J

theorem physical_positive_row {ι:Type*}[Fintype ι][DecidableEq ι]
    (F:ProbeFinalAssembly.SourceData D)(η η₀:Character)(m A z:O)
    (W₁ W₂:ℝ→ℂ)(S:ι→ Finset (Ideal O))(P:ι→ℝ)(ζ:ι→ℂ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ S (fun i=> physicalSlotCoefficient η₀ F.W (P i) (ζ i)) P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ S
        (fun i I=> idealCoeff η₀.inverse I*slotSchwartz F (ζ i) ((I.absNorm:ℝ)/P i)) P t X₁ X₂ := by
  congr 1
  funext i I
  exact physical_coefficient F η₀ (P i) (ζ i) I

end CenteredMomentDetectorPlainSlotProfile

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentHeckeHeight CenteredMomentPrimeSlot HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open ProbeHighRowFamily 
local notation "O" => Eisenstein.O

lemma rowMaskElement_eq_fixed : rowMaskElement=fixedBadMask := by
  unfold rowMaskElement fixedBadMask
  exact mul_comm _ _


end CenteredMomentNaturalFixedRaySource
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate

namespace CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily  Eisenstein
local notation "O"=> Eisenstein.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

def plainProfile (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (j:ℕ)(σ t:ℝ):ℝ→ℂ:=
  twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ
    (orientedFrequency F.reverse t)

def slotWindow (F:Fiber M H Label Slot U a ε tstar T allowance i)(s:Slot)(x:ℝ):ℂ:=
  conj (F.profile s x*(x:ℂ)^(F.external s-1))

def fiberPool (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot):
    Finset (CenteredMomentAddedZeroUniform.Tuple selected):=
  completePool (fun s:selected=> primePool M H (F.upper s.val) (U^(F.widths s.val)))
    (9/4) (9/4) (U^F.m) (U^F.m)

def fiberCoefficient (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ):Ideal O→ℂ:=
  finiteColumnCoefficient (fiberPool F selected)
    (uncenteredProfileCoefficient 1 (fun _:selected=> idealCoeff η.inverse)
      (fun s:selected=> slotWindow F s.val) (fun s:selected=> U^(F.widths s.val))
      (plainProfile F j σ t) (plainProfile F k σ t) (U^F.m) (U^F.m) 1 1 1)

def fiberSourceEnergy (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ)):ℝ:=
  sourceRestrictedEnergy (fun _=> True) (finiteColumns (fiberPool F selected))
    (fiberCoefficient F η selected j k σ t) (heightCoeff η 0) Φ U /
    ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val))

/-- Each detector row is the normalized finite polynomial of its complete tuple pool. -/
theorem detector_row_eq_source (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(u:FreeRow)(hU:0< U):
    detectorPositiveRow F η selected j k σ t u=
      (Real.sqrt ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):ℂ)⁻¹*
      ∑I∈finiteColumns (fiberPool F selected),fiberCoefficient F η selected j k σ t I*
        CenteredMomentHeckeExpansion.rowWeight η fixedBadMask 1 u.val 0 I:=by
  have he:=positiveSlotRow_eq_complete_source η fixedBadMask 1 u.val 0
    (dvd_mul_right _ _) (dvd_mul_left _ _)
    (fun s:selected=> primePool M H (F.upper s.val) (U^(F.widths s.val))) 1
    (fun _:selected=> idealCoeff η.inverse) (fun s:selected=> slotWindow F s.val)
    (fun s:selected=> U^(F.widths s.val)) (plainProfile F j σ t) (plainProfile F k σ t)
    (1/4) (9/4) (1/4) (9/4) (U^F.m) (U^F.m) (by norm_num) (by norm_num)
    (detector_profile_support F.reverse j σ _) (detector_profile_support F.reverse k σ _)
    (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _)
  rw [natural_unit_mask_positive (CenteredMomentNaturalRowSource.naturalRow η u.val u.property.1)] at he
  unfold detectorPositiveRow
  rw [rowMaskElement_eq_fixed]
  exact he

theorem detector_positive_energy_le_source
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(hU:0< U):
    (∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2)≤
      fiberSourceEnergy F η selected j k σ t Φ:=by
  let Q:=finiteColumns (fiberPool F selected)
  let c:=fun I:supportedColumns Q=> fiberCoefficient F η selected j k σ t I*heightCoeff η 0 I
  let rows:Finset O:=F.rows.image Subtype.val
  have ht:0<(U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val):=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _))
      (Finset.prod_pos (fun _ _=> Real.rpow_pos_of_pos hU _))
  have he (u:FreeRow):
      ‖detectorPositiveRow F η selected j k σ t u‖^2=
      ‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
    rw [detector_row_eq_source F η selected j k σ t u hU,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
    congr 1
    exact congrArg (fun w : ℂ=>‖w‖^2)
      (height_source_row η 0 Q (fiberCoefficient F η selected j k σ t) u.val).symm
  have hb:=finite_energy_le_restricted (fun _ : O=> True) Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) c Φ U hU rows
    (by simp) (fun z=> hΦ _) (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      have hn:‖ringComplex u.val‖^2/U∈Set.Icc (0:ℝ) 1:=by
        refine ⟨div_nonneg (sq_nonneg _) hU.le,(div_le_one hU).mpr ?_⟩
        rw [ringComplex_norm_sq_eq_absNorm_span]
        exact F.row_norm u hu
      rw [hone _ hn,Complex.one_re])
  calc
    _=(∑u∈F.rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      simp_rw [he]
      rw [Finset.sum_div]
    _=(∑z∈rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c z‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      rw [Finset.sum_image (fun x _ y _ hxy=> Subtype.val_injective hxy)]
    _≤ _:=div_le_div_of_nonneg_right hb ht.le

theorem fiber_plain_energy_le_source
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (hdata:F.rowData=momentData η)(hMm:M≤ Ideal.span {rowMaskElement})(hU:0< U)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)
    (hη:∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→ IsCoprime J η.modulus):
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
      (U^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
      (U^F.m) σ t*F.physicalProduct selected u‖^2)≤
      fiberSourceEnergy F η selected j k σ t Φ:=by
  rw [fiber_plain_energy_eq F η hdata hMm hU selected j k σ t hη]
  exact detector_positive_energy_le_source Φ hΦ hone F η selected j k σ t hU

def radialMajorant : 𝓢(ℝ,ℂ):=
  Classical.choose DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant

lemma radialMajorant_compact : HasCompactSupport (radialMajorant:ℝ→ℂ):=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).1

lemma radialMajorant_nonneg (x:ℝ):0≤(radialMajorant x).re:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.1 x

lemma radialMajorant_one (x:ℝ)(hx:x∈Set.Icc (0:ℝ) 1):radialMajorant x=1:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.2.2 x hx

theorem actual_fiber_plain_energy_le_source
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (hdata:F.rowData=momentData η)(hMm:M≤ Ideal.span {rowMaskElement})(hU:0< U)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)
    (hη:∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→ IsCoprime J η.modulus):
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
      (U^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
      (U^F.m) σ t*F.physicalProduct selected u‖^2)≤
      fiberSourceEnergy F η selected j k σ t radialMajorant:=
  fiber_plain_energy_le_source radialMajorant radialMajorant_nonneg radialMajorant_one
    F η hdata hMm hU selected j k σ t hη

theorem actual_fiber_unmarked_energy_le_source
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (hdata:F.rowData=momentData η)(hMm:M≤ Ideal.span {rowMaskElement})(hU:0< U)
    (j k:ℕ)(σ t:ℝ):
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
      (U^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
      (U^F.m) σ t‖^2)≤ fiberSourceEnergy F η ∅ j k σ t radialMajorant:=by
  simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one] using
    actual_fiber_plain_energy_le_source F η hdata hMm hU ∅ j k σ t (by simp)

end CenteredMomentDetectorPlainFiberSource

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace CenteredMomentDetectorEnergyInitialState
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentNaturalFixedRaySource 
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional
local notation "O"=> Eisenstein.O

def initialKeep (η:Character)(Q:Ideal O)(z:O):Prop:=
  z≠0 ∧ ¬FixedInducingRow η Q (fixedBadMask*cubicIdealGenerator 1) 1 z

def initialState (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ U δ:ℝ)
    (hU:1≤ U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤ U^δ):NaturalState U 0 bΦ where
  character:=η
  fixedModulus:=Q
  puncture:=1
  radial := {
    keep := initialKeep η Q
    profile := Φ
    scale := U
    scale_pos := zero_lt_one.trans_le hU
    nonneg := fun z => hp _ }
  rowWidth:=1
  characterWidth:=δ
  base_ge_one:=hU
  row_nonneg:=by norm_num
  character_nonneg:=hδ
  scale_eq:=by simp
  modulus_bound:=hη
  puncture_ne_zero:=one_ne_zero
  puncture_bound:=by simp
  radial_support:=hs
  row_ne_zero:=fun _ h=> h.1
  nonexceptional:=fun _ h=> h.2

lemma initialState_width (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ U δ:ℝ)
    (hU:1≤ U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤ U^δ):
    (initialState η Q Φ bΦ U δ hU hδ hs hp hη).width=1+δ:=rfl

def detectorProfiles (reverse:Bool)(j k:ℕ)(σ t:ℝ):Profiles (1/4) (9/4) where
  profile:=fun n=> detectorSchwartz reverse (if n=0 then j else k) σ t
  support:=by
    intro n x hx
    have he:(detectorSchwartz reverse (if n=0 then j else k) σ t:ℝ→ℂ)=
      HeckeInverseAmplification.twistProfile
        (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          ((HeckeDetectorRowwisePolynomial.logProfile^[if n=0 then j else k])
            HeckeDetectorDyadicProfiles.positiveAnnular)) σ
          (HeckeDetectorCoefficientTransfer.orientedFrequency reverse t):=by
      funext y;exact detectorSchwartz_apply _ _ _ _ _
    rw [he] at hx
    exact detector_profile_support _ _ _ _ hx

theorem radialMajorant_support_bound:
    ∃bΦ:ℝ,0< bΦ ∧ Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ:=by
  obtain ⟨b,hb⟩:=radialMajorant_compact.isCompact.bddAbove
  refine ⟨max 1 b,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x hx
  exact (hb (subset_tsupport _ hx)).trans (le_max_right _ _)

variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem source_label_modulus_eventually (F:ProbeFinalAssembly.SourceData D)
    (η:Character)(δ:ℝ)(hδ:0<δ):
    ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),∀d:ℝ,(1/200:ℝ)≤ d→
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤(Z^d)^δ:=by
  have hc:∀ᶠZ:ℝ in atTop,∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤ Z^((1/200)*δ):=by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (mul_pos (by norm_num) hδ)).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro label d hd
  apply (hz label).trans
  rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (mul_le_mul_of_nonneg_right hd hδ.le)

lemma source_keep_iff (F:ProbeFinalAssembly.SourceData D)(η:Character)(u:FreeRow):
    initialKeep η (internalQ (sourceFixedIdeal F) η) u.val↔¬sourceExceptional F η u:=by
  exact and_iff_right u.property.1

lemma source_fixed_gates (F:ProbeFinalAssembly.SourceData D)(η:Character):
    internalQ (sourceFixedIdeal F) η≠0 ∧
    internalQ (sourceFixedIdeal F) η≤ F.modulus ∧
    internalQ (sourceFixedIdeal F) η≤η.modulus ∧
    internalQ (sourceFixedIdeal F) η≤ Ideal.span {(72:O)}:=
  ⟨internalQ_ne_zero _ (sourceFixedIdeal_ne_zero F) η,
    inf_le_left.trans (sourceFixedIdeal_le_modulus F),inf_le_right,
    inf_le_left.trans (sourceFixedIdeal_le_72 F)⟩

theorem source_energy_split_state (F:ProbeFinalAssembly.SourceData D)(η:Character)
    (rows:Finset FreeRow)(f:FreeRow→ℂ):
    (∑u∈rows,‖f u‖^2)=
      (∑u∈rows.filter (fun u=> initialKeep η (internalQ (sourceFixedIdeal F) η) u.val),‖f u‖^2)+
      ∑u∈rows.filter (sourceExceptional F η),‖f u‖^2:=by
  simpa only [source_keep_iff] using source_energy_split F η rows f

/-- Each source character determines a retained natural state with width one plus its conductor allowance. -/
theorem source_initial_states (F:ProbeFinalAssembly.SourceData D):
    ∃bΦ:ℝ,0< bΦ ∧ ∀η:Character,∀δ:ℝ,0<δ→
      ∀ᶠZ:ℝ in atTop,∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d:ℝ,(1/200:ℝ)≤ d→
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label;
      ∃s:NaturalState (Z^d) 0 bΦ,
        s.character=η₀ ∧ s.fixedModulus=internalQ (sourceFixedIdeal F) η₀ ∧
        s.puncture=1 ∧ s.radial.profile=radialMajorant ∧ s.radial.scale=Z^d ∧
        s.radial.keep=initialKeep η₀ (internalQ (sourceFixedIdeal F) η₀) ∧
        s.rowWidth=1 ∧ s.characterWidth=δ ∧ s.width=1+δ:=by
  obtain ⟨bΦ,hbΦ,hs⟩:=radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [source_label_modulus_eventually F η δ hδ] with Z hz
  intro label d hd
  have hd0:0< d:=by linarith
  have hU:1≤ Z^d:=(Real.one_lt_rpow hz.1 hd0).le
  dsimp only
  refine ⟨initialState (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label)
    (internalQ (sourceFixedIdeal F) (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label))
    radialMajorant bΦ (Z^d) δ hU hδ.le hs
    radialMajorant_nonneg (hz.2 label d hd),?_⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end CenteredMomentDetectorEnergyInitialState

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace CenteredMomentDetectorPlainExceptional
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily  Eisenstein
local notation "O"=> Eisenstein.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

def retainedSourceEnergy (keep:O→ Prop)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ)):ℝ:=
  sourceRestrictedEnergy keep (finiteColumns (fiberPool F selected))
    (fiberCoefficient F η selected j k σ t) (heightCoeff η 0) Φ U /
    ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val))

theorem retained_positive_energy_le_source
    (keep:O→ Prop)(Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(hU:0< U)
    (hkeep:∀u∈F.rows,keep u.val):
    (∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2)≤
      retainedSourceEnergy keep F η selected j k σ t Φ:=by
  let Q:=finiteColumns (fiberPool F selected)
  let c:=fun I:supportedColumns Q=> fiberCoefficient F η selected j k σ t I*heightCoeff η 0 I
  let rows:Finset O:=F.rows.image Subtype.val
  have ht:0<(U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val):=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _))
      (Finset.prod_pos (fun _ _=> Real.rpow_pos_of_pos hU _))
  have he (u:FreeRow):
      ‖detectorPositiveRow F η selected j k σ t u‖^2=
      ‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
    rw [detector_row_eq_source F η selected j k σ t u hU,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
    congr 1
    exact congrArg (fun w : ℂ=>‖w‖^2)
      (height_source_row η 0 Q (fiberCoefficient F η selected j k σ t) u.val).symm
  have hb:=finite_energy_le_restricted keep Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) c Φ U hU rows
    (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      exact hkeep u hu) (fun z=> hΦ _) (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      have hn:‖ringComplex u.val‖^2/U∈Set.Icc (0:ℝ) 1:=by
        refine ⟨div_nonneg (sq_nonneg _) hU.le,(div_le_one hU).mpr ?_⟩
        rw [ringComplex_norm_sq_eq_absNorm_span]
        exact F.row_norm u hu
      rw [hone _ hn,Complex.one_re])
  calc
    _=(∑u∈F.rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      simp_rw [he]
      rw [Finset.sum_div]
    _=(∑z∈rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c z‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      rw [Finset.sum_image (fun x _ y _ hxy=> Subtype.val_injective hxy)]
    _≤ _:=div_le_div_of_nonneg_right hb ht.le

variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem source_fibers_eventually_retained (S:ProbeFinalAssembly.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀(d a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∀u∈(B.fiber bin label J K hne).rows,
        initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) u.val) ∧
      ((B.fiber bin label J K hne).rows.filter (sourceExceptional S η₀))=∅:=by
  filter_upwards [eventually_source_no_exceptional S η] with Z hz
  intro rows hrows d a ε tstar T allowance i B hB bin label J K hne η₀
  have hk:∀u∈(B.fiber bin label J K hne).rows,
      initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) u.val:=by
    intro u hu
    apply (source_keep_iff S η₀ u).mpr
    apply hz label u
    apply hrows u
    apply hB
    simp only [Batch.fiber,HeckeDetectorFiberPartition.toFiber,
      HeckeDetectorFiberPartition.fiber,Finset.mem_filter] at hu
    exact hu.1
  refine ⟨hk,?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hu,hex⟩:=Finset.mem_filter.mp hu
  exact ((source_keep_iff S η₀ u).mp (hk u hu)) hex

theorem source_exceptional_energy_eventually_zero (S:ProbeFinalAssembly.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀f:FreeRow→ℂ,
      (∑u∈rows.filter (sourceExceptional S
        (sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label)),‖f u‖^2)=0:=by
  filter_upwards [eventually_source_no_exceptional S η] with Z hz
  intro rows hrows label f
  apply Finset.sum_eq_zero
  intro u hu
  obtain ⟨hu,hex⟩:=Finset.mem_filter.mp hu
  exact False.elim ((hz label u (hrows u hu)) hex)

/-- Eventually every source fiber lies in the retained, nonexceptional row set. -/
theorem source_batch_plain_retained (S:ProbeFinalAssembly.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,d≠0→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→ B.widths=(fun s=> D.ell s/d)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),∀j k:ℕ,∀σ t:ℝ,
      let F:=B.fiber bin label J K hne;
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        retainedSourceEnergy (initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀))
          F η₀ selected j k σ t radialMajorant:=by
  filter_upwards [source_fibers_eventually_retained S η,
    eventually_source_slots_coprime S.modulus ⊤ le_top S.S S.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1) 1 (by norm_num),eventually_gt_atTop (1:ℝ)] with Z hret hcop hZ
  refine ⟨hZ,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth
    bin label J K hne selected j k σ t F η₀
  have hU:0< Z^d:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hdataF:F.rowData=momentData η₀:=by
    change B.data label=momentData η₀
    rw [hdata,sourceMomentData_base]
  have hMm:S.modulus≤ Ideal.span {rowMaskElement}:=source_product_le_rowMask S.S S.exclusions.bad
  have hη:∀s∈selected,∀I∈primePool S.modulus ⊤ (F.upper s) ((Z^d)^(F.widths s)),
      F.profile s ((I.absNorm:ℝ)/((Z^d)^(F.widths s)))≠0→ IsCoprime I η₀.modulus:=by
    intro s hs I hI hn
    change I∈primePool S.modulus ⊤ (B.upper s) ((Z^d)^(B.widths s)) at hI
    change B.profile s ((I.absNorm:ℝ)/((Z^d)^(B.widths s)))≠0 at hn
    rw [hwidth] at hI
    rw [hwidth,hprofile] at hn
    exact hcop label s d hd (fun x=>(S.w x:ℂ)) (B.upper s)
      (by
        intro x hx
        have hn:S.w x≠0:=by simpa using hx
        exact (S.support hn).1.le) I hI hn
  rw [fiber_plain_energy_eq F η₀ hdataF hMm hU selected j k σ t hη]
  exact retained_positive_energy_le_source _ radialMajorant radialMajorant_nonneg radialMajorant_one
    F η₀ selected j k σ t hU (hret rows hrows d a ε tstar T allowance i B hB bin label J K hne).1

end CenteredMomentDetectorPlainExceptional

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentDetectorPlainStateDictionary
open HeckeFamily HeckeDetectorRawFiber HeckePrimeAnnular
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentSecondHeightFamily 
local notation "O" => Eisenstein.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

lemma plainProfile_eq_detectorSchwartz
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(j:ℕ)(σ t:ℝ):
    plainProfile F j σ t=(detectorSchwartz F.reverse j σ t:ℝ→ℂ):=by
  funext x
  exact (detectorSchwartz_apply F.reverse j σ t x).symm

/-- The finite source expansion equals the retained positive-row energy. -/
theorem retainedSourceEnergy_eq_energy
    (keep:O→ Prop)(F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ))(hU:0< U):
    retainedSourceEnergy keep F η selected j k σ t Φ=
      energy η (fixedBadMask*cubicIdealGenerator 1) 1 0
        (plainProfile F j σ t) (plainProfile F k σ t)
        (fun s:selected=> CenteredMomentPrimeSlot.primePool M H (F.upper s.val) (U^(F.widths s.val)))
        (fun (s:selected) I=> idealCoeff η.inverse I*slotWindow F s.val ((I.absNorm:ℝ)/(U^(F.widths s.val))))
        (fun s:selected=> U^(F.widths s.val)) (U^F.m) (U^F.m) keep Φ U:=by
  exact (positive_energy_eq_complete_source η 0 keep
    (fun s:selected=> CenteredMomentPrimeSlot.primePool M H (F.upper s.val) (U^(F.widths s.val))) 1
    (fun _:selected=> idealCoeff η.inverse) (fun s:selected=> slotWindow F s.val)
    (fun s:selected=> U^(F.widths s.val)) (fun _=> Real.rpow_pos_of_pos hU _)
    (plainProfile F j σ t) (plainProfile F k σ t)
    (1/4) (9/4) (1/4) (9/4) (U^F.m) (U^F.m) (by norm_num) (by norm_num)
    (detector_profile_support F.reverse j σ _) (detector_profile_support F.reverse k σ _)
    (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _) Φ U).symm

theorem retainedSourceEnergy_empty_eq_plainEnergy
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)
    (hU:1≤ U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤ U^δ)
    (j k:ℕ)(σ t:ℝ):
    retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t Φ=
      (initialState η Q Φ bΦ U δ hU hδ hs hp hη).plainEnergy
        (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m):=by
  rw [retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  simp only [plainProfile_eq_detectorSchwartz]
  unfold NaturalState.plainEnergy energy
  apply tsum_congr
  intro z
  simp [initialState,NaturalState.mask,detectorProfiles,positiveSlotRow]

end CenteredMomentDetectorPlainStateDictionary

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators ContDiff ComplexConjugate
namespace CenteredMomentDetectorPlainCapacity
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSlotProfile
local notation "O"=> Eisenstein.O
variable {Δ:ℝ}{D:Parameters.HighData Δ}

/-- Physical slot coefficients equal annular weights, including the zero ideal. -/
theorem physical_annular_all (S:ProbeFinalAssembly.SourceData D)(η₀:Character)
    (P:ℝ)(hP:0< P)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η₀ S.W P ζ I=
      idealCoeff η₀.inverse I*annularWeight (fun x=> conj (S.W x)) P (1-ζ.re) (-ζ.im) I := by
  by_cases hI:I=0
  · subst I
    have hw:S.W 0=0:=by
      by_contra hh
      have hs:=S.complex_support hh
      norm_num at hs
    simp [physicalSlotCoefficient,annularWeight,hw]
  · exact physicalSlotCoefficient_annular η₀ S.W P ζ I hI hP


end CenteredMomentDetectorPlainCapacity
end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate Topology ContDiff
open Filter

namespace CenteredMomentDetectorPlainMarkedState
open HeckeFamily HeckeDyadic HeckeDetectorRawFiber HeckeDetectorBatch HeckePrimeAnnular
open HeckeInverseAmplification HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorPlainStateDictionary CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorPlainCapacity
open CenteredMomentDetectorPlainSlotProfile CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open  ProbeHighRowFamily
local notation "O" => Eisenstein.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}
variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem source_slot_coefficient (S:ProbeFinalAssembly.SourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(η:Character)(s:Slot)
    (hreal:(F.external s).re=17/50)(hU:0< U)(I:Ideal O):
    idealCoeff η.inverse I*slotWindow F s ((I.absNorm:ℝ)/(U^(F.widths s)))=
      idealCoeff η.inverse I*annularWeight (fun x=> conj (S.W x))
        (U^(F.widths s)) (33/50) (-(F.external s).im) I := by
  have he:=physical_annular_all S η (U^(F.widths s)) (Real.rpow_pos_of_pos hU _)
    (F.external s) I
  rw [hreal] at he
  norm_num at he
  simpa only [physicalSlotCoefficient,slotWindow,hprofile] using he

theorem retained_eq_initial_energy (S:ProbeFinalAssembly.SourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(hupper:∀s,F.upper s=2)
    (η:Character)(Q:Ideal O)(selected:Finset Slot)
    (hreal:∀s∈selected,(F.external s).re=17/50)
    (Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)(hU:1≤ U)(hδ:0≤δ)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤ U^δ)(j k:ℕ)(σ t:ℝ):
    let state:=initialState η Q Φ bΦ U δ hU hδ hs hp hη
    retainedSourceEnergy state.radial.keep F η selected j k σ t Φ=
      energy state.character state.mask 1 0
        ((detectorProfiles F.reverse j k σ t).profile 0)
        ((detectorProfiles F.reverse j k σ t).profile 1)
        (fun s:selected=> CenteredMomentPrimeSlot.primePool M H 2 (U^(F.widths s.val)))
        (fun (s:selected) I=> idealCoeff η.inverse I*
          annularWeight (fun x=> conj (S.W x)) (U^(F.widths s.val)) (33/50)
            (-(F.external s.val).im) I)
        (fun s:selected=> U^(F.widths s.val)) (U^F.m) (U^F.m)
        state.radial.keep state.radial.profile state.radial.scale := by
  dsimp only
  rw [retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  have hc:(fun (s:selected) I=> idealCoeff η.inverse I*
      slotWindow F s.val ((I.absNorm:ℝ)/(U^(F.widths s.val))))=
      (fun (s:selected) I=> idealCoeff η.inverse I*
        annularWeight (fun x=> conj (S.W x)) (U^(F.widths s.val)) (33/50)
          (-(F.external s.val).im) I):=by
    funext s I
    exact source_slot_coefficient S F hprofile η s.val (hreal s.val s.property)
      (zero_lt_one.trans_le hU) I
  rw [hc]
  simp only [hupper,plainProfile_eq_detectorSchwartz,initialState,NaturalState.mask,
    detectorProfiles,reduceIte,Fin.one_eq_zero_iff]
  norm_num

theorem plain_length_eq [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1< U):
    length U (U^F.m)=F.m := by
  have hm:0≤ F.m:=(F.lengths hU).2.2.2.2
  rw [length,max_eq_right (Real.one_le_rpow hU.le hm),
    Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem marked_capacity [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1< U)
    (selected:Finset Slot)(κ δ:ℝ)(hδ:0≤δ)
    (hcap:2*F.m+6*κ*(∑s∈selected,F.widths s)≤1):
    length U (U^F.m)+length U (U^F.m)+6*κ*(∑s:selected,F.widths s.val)≤1+δ := by
  rw [plain_length_eq F hU,Finset.sum_coe_sort]
  linarith

theorem selected_widths (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(hselected:selected⊆F.slots):
    (∀s:selected,0< F.widths s.val) ∧ (∀s:selected,F.widths s.val≤ F.mesh) :=
  ⟨fun s=> F.widths_pos s.val (hselected s.property),
    fun s=> F.widths_mesh s.val (hselected s.property)⟩

theorem source_profile_uniform (S:ProbeFinalAssembly.SourceData D)(Hsemin:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀{ι:Type*}(ζ:ι→ℂ)(height:ℝ),0≤ height→
      (∀s,(ζ s).re=17/50)→(∀s,|(ζ s).im|≤ height)→∀s,
      Hsemin.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz S (ζ s))≤
        C*(1+height)^J :=
  slotSchwartz_height_uniform S Hsemin

theorem source_relative_fixed_gates (S:ProbeFinalAssembly.SourceData D)(η:Character):
    internalQ (sourceFixedIdeal S) η≠0 ∧
    internalQ (sourceFixedIdeal S) η≤ S.modulus ∧
    internalQ (sourceFixedIdeal S) η≤η.inverse.modulus ∧
    internalQ (sourceFixedIdeal S) η≤ Ideal.span {(72:O)} :=
  source_fixed_gates S η

theorem fixed_window_data (S:ProbeFinalAssembly.SourceData D):
    Function.support (fun x=> conj (S.W x))⊆Set.Icc (1:ℝ) 2 ∧
    ContDiff ℝ ∞ (fun x=> conj (S.W x)) ∧ ∀x,‖conj (S.W x)‖≤1 := by
  refine ⟨conjugate_source_support S,
    Complex.conjCLE.contDiff.comp (S.W.smooth (⊤ : ℕ∞)),?_⟩
  intro x
  rw [RCLike.norm_conj,S.complex_eq,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (S.bounded x).1]
  exact (S.bounded x).2

/-- Selected source fibers satisfy the natural-state width and capacity bounds. -/
theorem source_batch_marked_initial (S:ProbeFinalAssembly.SourceData D):
    ∃bΦ:ℝ,0< bΦ ∧ ∀η:Character,∀δ:ℝ,0<δ→
      ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤ d→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→ B.widths=(fun s=> D.ell s/d)→
      (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),selected⊆B.slots→
      let F:=B.fiber bin label J K hne;
      2*F.m+6*(3/4+2*Δ)*(∑s∈selected,F.widths s)≤1→
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      ∃state:NaturalState (Z^d) 0 bΦ,
        state.character=η₀ ∧ state.fixedModulus=internalQ (sourceFixedIdeal S) η₀ ∧
        state.puncture=1 ∧ state.radial.profile=radialMajorant ∧ state.radial.scale=Z^d ∧
        state.radial.keep=initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) ∧
        state.width=1+δ ∧
        length (Z^d) ((Z^d)^F.m)+length (Z^d) ((Z^d)^F.m)+
          6*(3/4+2*Δ)*(∑s:selected,F.widths s.val)≤ state.width ∧
        (∀s:selected,0< F.widths s.val ∧ F.widths s.val≤ F.mesh) ∧
        ∀j k:ℕ,∀σ t:ℝ,
        (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
          energy state.character state.mask 1 0
            ((detectorProfiles F.reverse j k σ t).profile 0)
            ((detectorProfiles F.reverse j k σ t).profile 1)
            (fun s:selected=> CenteredMomentPrimeSlot.primePool S.modulus ⊤ 2 ((Z^d)^(F.widths s.val)))
            (fun (s:selected) I=> idealCoeff η₀.inverse I*
              annularWeight (fun x=> conj (S.W x)) ((Z^d)^(F.widths s.val)) (33/50)
                (-(F.external s.val).im) I)
            (fun s:selected=>(Z^d)^(F.widths s.val)) ((Z^d)^F.m) ((Z^d)^F.m)
            state.radial.keep state.radial.profile state.radial.scale := by
  obtain ⟨bΦ,hbΦ,hs⟩:=radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [source_label_modulus_eventually S η δ hδ,source_batch_plain_retained S η] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label J K hne selected hselected F hcap η₀
  have hdpos:0< d:=by linarith
  have hU:1< Z^d:=Real.one_lt_rpow hz.1 hdpos
  have hη:(η₀.modulus.absNorm:ℝ)≤(Z^d)^δ:=hz.2 label d hd
  let state:=initialState η₀ (internalQ (sourceFixedIdeal S) η₀) radialMajorant bΦ
    (Z^d) δ hU.le hδ.le hs radialMajorant_nonneg hη
  refine ⟨state,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · exact marked_capacity F hU selected _ δ hδ.le hcap
  · intro s
    exact ⟨F.widths_pos s.val (hselected s.property),F.widths_mesh s.val (hselected s.property)⟩
  · intro j k σ t
    have hb:=hr.2 rows hrows d hdpos.ne' a ε tstar T allowance i B hB hdata hprofile hwidth
      bin label J K hne selected j k σ t
    have hprof:∀s x,F.profile s x=S.W x:=by
      intro s x
      change B.profile s x=S.W x
      rw [hprofile,S.complex_eq]
    have he:=retained_eq_initial_energy S F hprof hupper η₀ (internalQ (sourceFixedIdeal S) η₀) selected
      (fun s _=> hreal s) radialMajorant bΦ δ hU.le hδ.le hs radialMajorant_nonneg hη j k σ t
    exact hb.trans_eq he

end CenteredMomentDetectorPlainMarkedState

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentDetectorPlainUnmarkedState
open HeckeFamily HeckeDetectorRawFiber CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainStateDictionary
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainFiberSource
local notation "O"=> Eisenstein.O

def allowance (δ m:ℝ):ℝ:=δ+max 0 (2*m-1)

lemma allowance_nonneg (δ m:ℝ)(hδ:0≤δ):0≤ allowance δ m:=
  add_nonneg hδ (le_max_left _ _)

lemma padded_width (δ m:ℝ):1+allowance δ m=max 1 (2*m)+δ:=by
  unfold allowance
  by_cases hm:1≤2*m
  · rw [max_eq_right hm,max_eq_right (by linarith:0≤2*m-1)]
    ring
  · rw [max_eq_left (le_of_not_ge hm),max_eq_left (by linarith:2*m-1≤0)]
    ring

lemma padded_modulus (η:Character)(U δ m:ℝ)(hU:1≤ U)
    (hη:(η.modulus.absNorm:ℝ)≤ U^δ):
    (η.modulus.absNorm:ℝ)≤ U^(allowance δ m):=
  hη.trans (Real.rpow_le_rpow_of_exponent_le hU (le_add_of_nonneg_right (le_max_left _ _)))

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T heightAllowance:ℝ}{i:ℕ}

def state (F:Fiber M H Label Slot U a ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)
    (hU:1≤ U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤ U^δ):NaturalState U 0 bΦ:=
  initialState η Q Φ bΦ U (allowance δ F.m) hU (allowance_nonneg _ _ hδ) hs hp
    (padded_modulus η U δ F.m hU hη)

omit [NeZero M] in
/-- Padding the conductor allowance admits both smooth lengths within the state width. -/
theorem actual_scale_gates (F:Fiber M H Label Slot U a ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ εcap:ℝ)
    (hU:1< U)(hδ:0≤δ)(hε:ε≤εcap)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤ U^δ):
    let s:=state F η Q Φ bΦ δ hU.le hδ hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=max 1 (2*F.m)+δ ∧
    s.width≤ max 1 (1+150*εcap)+δ ∧
    1≤ U^F.m ∧ length U (U^F.m)=F.m ∧
    2*length U (U^F.m)≤ s.width ∧ U^F.m≤ U^(1/2+75*εcap):=by
  dsimp only
  have hm:=F.lengths hU
  have hmcap:F.m≤1/2+75*εcap:=by linarith [hm.2.2.1]
  have hscale:1≤ U^F.m:=Real.one_le_rpow hU.le hm.2.2.2.2
  have hlen:length U (U^F.m)=F.m:=by
    rw [length,max_eq_right hscale]
    exact Real.logb_rpow (zero_lt_one.trans hU) hU.ne'
  have hw:(state F η Q Φ bΦ δ hU.le hδ hs hp hη).width=max 1 (2*F.m)+δ:=padded_width δ F.m
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,hw,?_,hscale,hlen,?_,?_⟩
  · rw [hw]
    exact add_le_add (max_le_max le_rfl (by linarith)) le_rfl
  · rw [hw,hlen]
    exact (le_max_right 1 (2*F.m)).trans (le_add_of_nonneg_right hδ)
  · exact Real.rpow_le_rpow_of_exponent_le hU.le hmcap

omit [NeZero M] in
theorem actual_source_eq (F:Fiber M H Label Slot U a ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)
    (hU:1≤ U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤ U^δ)
    (j k:ℕ)(σ t:ℝ):
    retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t Φ=
      (state F η Q Φ bΦ δ hU hδ hs hp hη).plainEnergy
        (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m):=
  retainedSourceEnergy_empty_eq_plainEnergy F η Q Φ bΦ (allowance δ F.m)
    hU (allowance_nonneg _ _ hδ) hs hp (padded_modulus η U δ F.m hU hη) j k σ t

end CenteredMomentDetectorPlainUnmarkedState

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace CenteredMomentDetectorPlainMomentParameters
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open CenteredMomentDetectorDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainUnmarkedState CenteredMomentNaturalFixedRaySource
local notation "O" => Eisenstein.O

variable {Δ:ℝ}

def delta (D:Parameters.HighData Δ):ℝ := D.t/4
def stageError (D:Parameters.HighData Δ):ℝ := D.t/4
def kappaPlain (_D:Parameters.HighData Δ):ℝ := 3/4+2*Δ

/-- Quarter-size error and conductor allowances fit the detector margin. -/
theorem fixed_parameters (D:Parameters.HighData Δ):
    0< delta D ∧ delta D≤1/4 ∧ 0< stageError D ∧
    delta D+stageError D≤ D.t ∧ 3/4< kappaPlain D ∧ 0< kappaPlain D := by
  have hΔ:0<Δ:=by linarith [D.t_pos,D.t_delta]
  dsimp [delta,stageError,kappaPlain]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_small]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_pos]
  constructor <;> linarith

lemma source_base_gt_one (_D:Parameters.HighData Δ)(Z d:ℝ)
    (hZ:1< Z)(hd:(1/200:ℝ)≤ d):1< Z^d :=
  Real.one_lt_rpow hZ (by linarith)

lemma witness_length_cap (D:Parameters.HighData Δ):
    1/2+75*D.ε≤(23/40:ℝ) := by linarith [D.epsilon_small]

lemma original_width_bounds (D:Parameters.HighData Δ)(d:ℝ)
    (hd:(1/200:ℝ)≤ d)(s:Fin D.N):0< D.ell s/d ∧ D.ell s/d≤ D.t := by
  have hdpos:0< d:=by linarith
  refine ⟨div_pos (D.slots_bounds s).1 hdpos,(div_le_iff₀ hdpos).mpr ?_⟩
  have hs: D.ell s≤(1/200:ℝ)*D.t:=(D.slots_bounds s).2.2
  nlinarith [D.t_pos]

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
variable {U a tstar T heightAllowance:ℝ}{i:ℕ}

theorem actual_fiber_lengths (D:Parameters.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)(hU:1< U):
    0≤ F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤ U^F.m ∧ U^F.m≤ U ∧ length U (U^F.m)=F.m := by
  have hm:=F.lengths hU
  have hcap:=hm.2.2.1.trans (witness_length_cap D)
  refine ⟨hm.2.2.2.2,hm.2.2.1,hcap,Real.one_le_rpow hU.le hm.2.2.2.2,?_,?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m≤1 by linarith)
  · exact plain_length_eq F hU

theorem batch_fiber_parameters (D:Parameters.HighData Δ)(Z d:ℝ)
    (hZ:1< Z)(hd:(1/200:ℝ)≤ d)
    (B:Batch M H Label (Fin D.N) (Z^d) a D.ε tstar T heightAllowance i)
    (hwidth:B.widths=(fun s=> D.ell s/d))
    (bin label J K)(hne:(B.fiberRows bin label J K).Nonempty):
    let F:=B.fiber bin label J K hne;
    1< Z^d ∧ 0≤ F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤(Z^d)^F.m ∧ (Z^d)^F.m≤ Z^d ∧ length (Z^d) ((Z^d)^F.m)=F.m ∧
    (∀s,0< F.widths s ∧ F.widths s≤ D.t) ∧
    (∀selected:Finset (Fin D.N),∀s:selected,0< F.widths s.val ∧ F.widths s.val≤ D.t) := by
  dsimp only
  have hU:=source_base_gt_one D Z d hZ hd
  have hf:=actual_fiber_lengths D (B.fiber bin label J K hne) hU
  have hw:∀s,0<(B.fiber bin label J K hne).widths s ∧
      (B.fiber bin label J K hne).widths s≤ D.t:=by
    intro s
    change 0< B.widths s ∧ B.widths s≤ D.t
    rw [hwidth]
    exact original_width_bounds D d hd s
  exact ⟨hU,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,hf.2.2.2.2.2,
    hw,fun _ s=> hw s.val⟩

lemma width_bands (D:Parameters.HighData Δ)(m:ℝ)(hm:m≤23/40):
    1≤1+delta D ∧ 1+delta D≤2 ∧
    1≤ max 1 (2*m)+delta D ∧ max 1 (2*m)+delta D≤2 := by
  have hδ:0< delta D:=(fixed_parameters D).1
  have hd:delta D≤1/4:=(fixed_parameters D).2.1
  have hmax:max 1 (2*m)≤23/20:=max_le (by norm_num) (by linarith)
  have hlo:=le_max_left (1:ℝ) (2*m)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem marked_state_admission (D:Parameters.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1< U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤ U^(delta D))
    (selected:Finset (Fin D.N))
    (hcap:2*F.m+6*(kappaPlain D)*(∑s∈selected,F.widths s)≤1):
    let s:=initialState η Q Φ bΦ U (delta D) hU.le (fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=1+delta D ∧ 1≤ s.width ∧ s.width≤2 ∧
    1≤ U^F.m ∧ U^F.m≤ U ∧
    length U (U^F.m)+length U (U^F.m)+
      6*(kappaPlain D)*(∑s:selected,F.widths s.val)≤ s.width := by
  dsimp only
  have hf:=actual_fiber_lengths D F hU
  have hw:=width_bands D F.m hf.2.2.1
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,hw.1,hw.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  exact marked_capacity F hU selected (kappaPlain D) (delta D) (fixed_parameters D).1.le hcap

theorem unmarked_state_admission (D:Parameters.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1< U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤ U^(delta D)):
    let s:=state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=max 1 (2*F.m)+delta D ∧ 1≤ s.width ∧ s.width≤2 ∧
    1≤ U^F.m ∧ U^F.m≤ U ∧ 2*length U (U^F.m)≤ s.width := by
  dsimp only
  have hf:=actual_fiber_lengths D F hU
  have hw:=width_bands D F.m hf.2.2.1
  have he:(state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη).width=
      max 1 (2*F.m)+delta D:=padded_width _ _
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,he,?_,?_,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  · rw [he];exact hw.2.2.1
  · rw [he];exact hw.2.2.2
  · rw [he,hf.2.2.2.2.2]
    exact (le_max_right 1 (2*F.m)).trans (le_add_of_nonneg_right (fixed_parameters D).1.le)

theorem source_label_fixed_allowance (D:Parameters.HighData Δ)
    (S:ProbeFinalAssembly.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀d:ℝ,(1/200:ℝ)≤ d→
      ((sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤(Z^d)^(delta D) :=
  source_label_modulus_eventually S η (delta D) (fixed_parameters D).1

lemma final_exponent_budget (D:Parameters.HighData Δ)(base:ℝ):
    base+delta D+stageError D≤ base+D.t := by
  linarith [(fixed_parameters D).2.2.2.1]

end CenteredMomentDetectorPlainMomentParameters

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentDetectorPlainRelativeClass
open HeckeFamily CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
local notation "O"=> Eisenstein.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

lemma ray_identity (θ:RayQuotient.Characters M H)(I:Ideal O)
    (hI:I∈RayQuotient.identityClass M H):
    idealCoeff (HeckeRayQuotient.character M H hH θ) I=1:=by
  rcases hI with ⟨hI,a,ha,u,hu,huH⟩
  rw [HeckeRayQuotient.idealCoeff_character]
  change IdealCharacter.ofResidue M θ (RayQuotient.character_unitInvariant M H hH θ) I=1
  rw [IdealCharacter.ofResidue_of_generator M θ _ hI ha,←hu]
  exact (RayOrthogonality.mem_characters_iff H θ).mp θ.property u huH

lemma relative_pool (η₀:Character)(θ:RayQuotient.Characters M H)(b P:ℝ)
    (I:Ideal O)(hI:I∈primePool M H b P):
    idealCoeff (relativeCharacter M H hH η₀ θ) I=idealCoeff η₀.inverse I:=by
  rw [relativeCharacter_ideal,ray_identity M H hH θ I (Finset.mem_filter.mp hI).2.2,one_mul]

variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem positive_row (η η₀:Character)(θ:ι→ RayQuotient.Characters M H)(m A z:O)
    (W₁ W₂:ℝ→ℂ)(b P:ι→ℝ)(β:ι→ Ideal O→ℂ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ (fun i=> primePool M H (b i) (P i))
      (fun i I=> idealCoeff η₀.inverse I*β i I) P t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ (fun i=> primePool M H (b i) (P i))
      (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*β i I) P t X₁ X₂:=by
  unfold positiveSlotRow
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only
  rw [relative_pool M H hH η₀ (θ i) (b i) (P i) I hI]

omit [DecidableEq ι] in
/-- Ray characters are trivial on the identity-class pool, preserving its positive energy. -/
theorem energy_eq (η η₀:Character)(θ:ι→ RayQuotient.Characters M H)(m A:O)
    (W₁ W₂:ℝ→ℂ)(b P:ι→ℝ)(β:ι→ Ideal O→ℂ)(t X₁ X₂:ℝ)
    (keep:O→ Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (fun i=> primePool M H (b i) (P i))
      (fun i I=> idealCoeff η₀.inverse I*β i I) P X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i=> primePool M H (b i) (P i))
      (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*β i I) P X₁ X₂ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_row M H hH η η₀ θ m A z W₁ W₂ b P β t X₁ X₂]

end CenteredMomentDetectorPlainRelativeClass

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentDetectorPlainProfileControl
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional

/-- Two detector profiles have polynomial seminorm growth in the Fourier height. -/
theorem paired_control (S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀reverse:Bool,∀j k:ℕ,j+k≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t:ℝ,
      (detectorProfiles reverse j k σ t).control S ^2≤ C*(1+‖t‖)^J:=by
  obtain ⟨J,C,hC,h⟩:=detectorSchwartz_uniform S
  refine ⟨4*J,C ^ 4,by positivity,?_⟩
  intro reverse j k hjk σ hσ t
  have hj:=h reverse j (by omega) σ hσ t
  have hk:=h reverse k (by omega) σ hσ t
  have hp:(detectorProfiles reverse j k σ t).control S≤(C*(1+‖t‖)^J)^2:=by
    simpa only [detectorProfiles,Profiles.control,sourceControl,Fin.zero_eta,ite_true,
      show ¬((1:Fin 2)=0) by decide,ite_false,pow_two] using
      mul_le_mul hj hk (sourceControl_nonneg S (detectorSchwartz reverse k σ t)) (by positivity)
  have hs:=pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2
  calc
    _≤((C*(1+‖t‖)^J)^2)^2:=hs
    _=C ^ 4*(1+‖t‖)^(4*J):=by
      rw [←pow_mul,mul_pow,←pow_mul]
      congr 2 ; omega

theorem source_height_factor (S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀degree:ℕ,∀reverse:Bool,∀j k:ℕ,j+k≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀height t:ℝ,0≤ height → |t|≤ height →
      (detectorProfiles reverse j k σ t).control S ^2*(1+|(0:ℝ)|+height)^degree
        ≤ C*(1+height)^(J+degree):=by
  obtain ⟨J,C,hC,h⟩:=paired_control S
  refine ⟨J,C,hC,?_⟩
  intro degree reverse j k hjk σ hσ height t hh ht
  have hb:(detectorProfiles reverse j k σ t).control S ^2≤ C*(1+height)^J:=by
    apply (h reverse j k hjk σ hσ t).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply pow_le_pow_left₀ (by positivity)
    simpa only [Real.norm_eq_abs] using add_le_add le_rfl ht
  simpa only [abs_zero,add_zero,pow_add,mul_assoc] using
    mul_le_mul_of_nonneg_right hb (pow_nonneg (by linarith:0≤1+height) degree)

end CenteredMomentDetectorPlainProfileControl

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
