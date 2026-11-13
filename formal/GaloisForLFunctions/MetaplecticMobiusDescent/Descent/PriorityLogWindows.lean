/-
Priority logarithmic windows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.SecondPrincipalCaller

/-!
# Priority logarithmic windows

Priority heights and logarithmic windows; truncated fresh radial parts of the first family and
the full second source; fixed three-window child data.
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

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem first_fresh_radial_truncated
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (c d : Eis) (r : FirstCoreIndex)
    (K : Finset ι → Finset ι → Finset Eis) :
    let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X
    let Ψ₀ := firstCoreTwist negative χ Ψ r
    let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
    let c₀ := c*jLabel p B v ε₁ ε₂
    firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
      (primeMark slots lists coeff) om X c d r t Y =
      truncatedSecondSource p hp hg F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K +
        secondSourceTail p hp hg F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K := by
  intro H₀ Ψ₀ m₀ c₀
  rw [firstFreshSecondPoisson_markedRadial p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    slots lists coeff hD om a b ha hs X t Y hX hY c d r]
  rw [←inputConjugateRow_smoothed_second_poisson p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp hinj (fun i => complexSexticChar_ne_one _ (hg i)) F Ψ₀ m₀ c₀ d H₀ rowMajorant Y hY]
  exact inputConjugateRow_eq_truncated_add_tail p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y hY K

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion
open InverseInitialArithmetic (sourceIdeal)
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem first_fresh_parent_radial_truncated
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (F D : Finset ι)
    (hq : parent.quotient = sourceIdeal p D)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (core : FirstCoreIndex)
    (K : Finset ι → Finset ι → Finset Eis) :
    let Ψ₀ := firstCoreTwist negative χ Ψ core
    let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X
    firstFreshSecondPoisson p hp hg hinj F D parent.cube.support
      (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit negative χ Ψ m (primeMark slots lists coeff) om X
      (∏ i∈parent.firstCommon,p i) (secondParentDivisor p parent) core t Y =
    truncatedSecondSource p hp hg F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
    secondSourceTail p hp hg F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K := by
  intro Ψ₀ H₀
  let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
    (columnLog p (primeProductNorm p D*X)) negative (-t) D
  let m₀ := (m*b0Label p parent.cube.support
    (fun i=>parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit)*∏ i∈D,p i
  have he (k : Eis) : inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ₀ m₀
      (secondParentLabel p parent) (secondParentDivisor p parent) H k =
    inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ k := by
    calc
      _ = inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ₀ m₀ (secondParentLabel p parent)
          (secondParentDivisor p parent) H₀ k := by
        unfold inputConjugateRow supportConjugateSum
        apply Finset.sum_congr rfl
        intro U hU
        rw [firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX]
      _ = _ := fresh_input_parent_mask p hg parent F D hq Ψ₀ m H₀ k
  rw [firstFreshSecondPoisson_fixed_pool p hp hg hinj hc (hY:=hY)]
  rw [←inputConjugateRow_smoothed_second_poisson p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp hinj (fun i => complexSexticChar_ne_one _ (hg i)) _ _ _ _ _ _ _ _ hY]
  change (∑' k : Eis,rowMajorant (‖ringComplex k‖^2/Y)*
    (‖inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ₀ m₀ (secondParentLabel p parent)
      (secondParentDivisor p parent) H k‖^2 : ℝ)) = _
  simp_rw [he]
  exact inputConjugateRow_eq_truncated_add_tail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
    (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y hY K

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion
open InverseInitialArithmetic (sourceIdeal)
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ] [Fintype κ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

include hcop in
theorem first_parent_full_second_source
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (F D : Finset ι)
    (hq : parent.quotient = sourceIdeal p D)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X height Y : ℝ) (hX : 0<X) (hY : 0<Y) (core : FirstCoreIndex)
    (R : Finset ι → Finset ι → ℝ) (label : Finset ι → SecondExpansionData ι → κ) :
    let Ψ₀ := firstCoreTwist negative χ Ψ core
    let V := principalWindow om a b ha hs negative height
    let H₀ := markedRadial p slots lists coeff ∅ V X
    let K := secondVariableCutoff p parent R
    firstFreshSecondPoisson p hp hg hinj F D parent.cube.support
      (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit negative χ Ψ m (primeMark slots lists coeff) om X
      (∏ i∈parent.firstCommon,p i) (secondParentDivisor p parent) core height Y =
    truncatedSecondZero p hg F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
    (∑ ray : SecondRayIndex,∑ residual∈F.powerset,∑ j : κ,
      (Y : ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector F K residual label j).image (attachSecondExpansion parent),
          actualSecondSignedWeight p hg Ψ₀ (m*cubicIdealGenerator x.quotient) ray x *
            actualSecondProfileRow p hg F (secondInheritedProfile p x Ψ₀ m ray)
              slots slots lists lists coeff coeff V V rowMajorant Y X) +
    secondSourceTail p hp hg F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K := by
  intro Ψ₀ V H₀ K
  have htest : H₀=(fun U=>primeMark slots lists coeff U*V (primeProductNorm p U/X)) := by
    funext U
    simp only [H₀,markedRadial,Finset.empty_union]
  have hret := truncated_second_attached_variable p hp hcop hg hinj hc hpr parent F Ψ₀ m
    slots lists coeff V rowMajorant X Y R label
  rw [←htest] at hret
  calc
    _ = truncatedSecondSource p hp hg F Ψ₀ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
        secondSourceTail p hp hg F Ψ₀ (secondParentPuncture p m parent)
          (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K :=
      first_fresh_parent_radial_truncated p hp hg hinj hc parent F D hq negative χ Ψ m
        slots lists coeff hD om a b ha hs X height Y hX hY core K
    _ = _ := congrArg (fun v=>v + secondSourceTail p hp hg F Ψ₀ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K) hret

end
end InverseMoment

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseSecondPrincipalCaller InverseSecondProfileUniform
open CompletedHeight SecondPassIntegration
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

def priorityLogWindow (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool):𝓢(ℝ,ℂ) :=
  if negative then conjugateProfile (CanonicalCubeSeparation.sourceLogProfile om a b ha hs (om.smooth ⊤))
  else CanonicalCubeSeparation.sourceLogProfile om a b ha hs (om.smooth ⊤)

def priorityHeight (negative:Bool) (t:ℝ):ℝ := if negative then -t else t

theorem priorityLogWindow_support (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool) :
    Function.support (priorityLogWindow om a b ha hs negative)⊆
      Set.Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro y hy
  have hn:om (Real.exp y)≠0:=by
    cases negative <;> simpa only [priorityLogWindow,Bool.false_eq_true,ite_true,ite_false,
      conjugateProfile_apply,CanonicalCubeSeparation.sourceLogProfile_apply,Function.mem_support,star_ne_zero] using hy
  have hh:=hs hn
  have hlo:=Real.log_le_log ha hh.1
  have hhi:=Real.log_le_log (Real.exp_pos y) hh.2
  rw [Real.log_exp] at hlo hhi
  constructor
  · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]

theorem principalWindow_positiveSource (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool) (t x:ℝ) (hx:0<x) :
    principalWindow om a b ha hs negative t x =
      positiveSource (priorityLogWindow om a b ha hs negative) 1 (priorityHeight negative t) x := by
  rw [principalWindow_apply]
  cases negative <;> simp only [priorityLogWindow,priorityHeight,Bool.false_eq_true,ite_true,ite_false,
    positiveSource,Real.log_one,add_zero,conjugateProfile_apply,CanonicalCubeSeparation.sourceLogProfile_apply,
    Real.exp_log hx,normTwistedSource]

theorem positiveSource_conjugate_one (g:𝓢(ℝ,ℂ)) (t x:ℝ) :
    star (positiveSource (conjugateProfile g) 1 (-t) x)=positiveSource g 1 t x := by
  simp only [positiveSource,Real.log_one,add_zero,conjugateProfile_apply,star_mul,star_star,
    JointLogSeparation.kernelLogPhase_conjugate,neg_neg,mul_comm]

theorem actualSecondProfileRow_congr_positive {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (pool:Finset ι) (x:SecondProfileData ι) (slots₁ slots₂:Finset σ)
    (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (W₁ W₂ V₁ V₂:ℝ→ℂ) (Φ:𝓢(ℝ,ℂ)) (Y X:ℝ) (hX:0<X)
    (h₁:∀t,0<t→W₁ t=V₁ t) (h₂:∀t,0<t→W₂ t=V₂ t) :
    actualSecondProfileRow p hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X =
      actualSecondProfileRow p hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂ V₁ V₂ Φ Y X := by
  simp only [actualSecondProfileRow_eq_whole p hp hg]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  congr 1
  unfold secondNormProfile
  have h0 : secondActualNorms p x N M 0 = primeProductNorm p x.common := rfl
  have h2 : secondActualNorms p x N M 2 = primeProductNorm p x.overlap := rfl
  have h4 : secondActualNorms p x N M 4 = primeProductNorm p N := rfl
  have h5 : secondActualNorms p x N M 5 = primeProductNorm p M := rfl
  rw [h0,h2,h4,h5]
  dsimp only
  rw [h₁ _ (div_pos (mul_pos (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
      (primeProductNorm_pos p hp _)) hX),
    h₂ _ (div_pos (mul_pos (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
      (primeProductNorm_pos p hp _)) hX)]

theorem actual_priority_profile_common {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (pool:Finset ι) (x:SecondProfileData ι) (slots₁ slots₂:Finset σ)
    (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (negative:Bool) (t:ℝ) (Φ:𝓢(ℝ,ℂ)) (Y X:ℝ) (hX:0<X) :
    let g:=priorityLogWindow om lo hi hlo hs negative
    let θ:=priorityHeight negative t
    actualSecondProfileRow p hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
      (principalWindow om lo hi hlo hs negative t) (principalWindow om lo hi hlo hs negative t) Φ Y X =
      actualSecondProfileRow p hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
        (fun y=>star (positiveSource (conjugateProfile g) 1 (-θ) y)) (positiveSource g 1 θ) Φ Y X := by
  intro g θ
  apply actualSecondProfileRow_congr_positive p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
    _ _ _ _ Φ Y X hX
  · intro y hy
    rw [positiveSource_conjugate_one]
    exact principalWindow_positiveSource om lo hi hlo hs negative t y hy
  · intro y hy
    exact principalWindow_positiveSource om lo hi hlo hs negative t y hy

end InverseMoment

end

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open JointLogSeparation MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem first_family_integral_of_two_energies (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (omega₁ omega₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (density : Frequency × (Fin 9 → ℝ) → ℂ)
    (J : ℕ) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hDensity : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true omega₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false omega₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w omega₁ omega₂ A₁ A₂ C R d h s z‖ ≤
    (Real.sqrt B₁*Real.sqrt B₂)*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖ := by
  have hb (z : Frequency × (Fin 9 → ℝ)) :
      ‖firstFamilySeparatedRow p hg source F selector C₁ C₂ w omega₁ omega₂ A₁ A₂ C R d h s z‖ ≤
      (Real.sqrt B₁*Real.sqrt B₂)*(tripleHeight J z.1*coordinateHeight J z.2) := by
    apply (first_family_cauchy p hg source F selector C₁ C₂ w omega₁ omega₂ A₁ A₂ C R d h s z).trans
    have hh := mul_le_mul (Real.sqrt_le_sqrt (hleft z)) (Real.sqrt_le_sqrt (hright z))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    apply hh.trans_eq
    rw [Real.sqrt_mul hB₁,Real.sqrt_mul hB₂]
    calc
      _=(Real.sqrt B₁*Real.sqrt B₂)*(Real.sqrt (tripleHeight J z.1*coordinateHeight J z.2))^2:=by ring
      _= _:=by rw [Real.sq_sqrt];unfold tripleHeight coordinateHeight;positivity
  calc
    _ ≤ ∫ z : Frequency × (Fin 9 → ℝ),(Real.sqrt B₁*Real.sqrt B₂)*(tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul _)
      filter_upwards with z
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _
end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open JointLogSeparation MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem actual_first_family_two_energies (hp : ∀ i,p i ≠ 0)
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (W₁ W₂ omega₁ omega₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (hs : ∀ i,0 < s i) (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 9 → ℝ,
      (Real.exp (-(9/2:ℝ)*L):ℂ)*firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z*
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (homega₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₁ (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (homega₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₂ (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      omega₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → omega₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,V i (firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i) = 1)
    (J : ℕ) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hWeighted : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true omega₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false omega₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖firstFamilyPhysicalRows p hg source F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Real.sqrt B₁*Real.sqrt B₂)*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
  have he := actual_first_balanced_family p hg hp source F selector C₁ C₂ w
    W₁ W₂ omega₁ omega₂ Φ V A₁ A₂ C R K L d h s hpos hs density hDensity hsep homega₁ homega₂ hcut
  have hb := first_family_integral_of_two_energies p hg source F selector C₁ C₂ w omega₁ omega₂ A₁ A₂ C R d h s
    density J B₁ B₂ hB₁ hB₂ hWeighted hleft hright
  have hn := congrArg norm he
  conv_lhs at hn => rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  conv_rhs at hn => rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (firstRootScale_pos s hs)]
  have hexp : Real.exp ((9/2:ℝ)*L)*Real.exp (-(9/2:ℝ)*L) = 1 := by
    rw [←Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hn' := congrArg (fun a : ℝ => Real.exp ((9/2:ℝ)*L)*a) hn
  rw [←mul_assoc,hexp,one_mul] at hn'
  rw [←mul_assoc,←div_eq_mul_inv] at hn'
  rw [hn']
  exact mul_le_mul_of_nonneg_left hb (by have := firstRootScale_pos s hs; positivity)

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open JointLogSeparation MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
variable {ι κ : Type*} [DecidableEq ι]
theorem actual_first_moving_family_two_energies
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile : ℝ,0 ≤ Cprofile ∧ ∀ (p : ι → Eis) (_hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (omega₁ omega₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (_hK : 0 < K) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (_hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (_hs : ∀ i,0 < s i)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_homega₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_homega₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      omega₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → omega₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true omega₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false omega₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F selector C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K d h s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Real.sqrt B₁*Real.sqrt B₂)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hmeasure⟩ := InverseMomentFirstProfileUniform.first_profile_common_measure
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨Cprofile,hCprofile,?_⟩
  intro p hp _ hg source F selector C₁ C₂ w omega₁ omega₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK d h s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    homega₁ homega₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hRad : 0 < K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8) := by
    exact div_pos (mul_pos hK (hs 6))
      (mul_pos (mul_pos (mul_pos (mul_pos (hs 3) (hs 4)) (sq_pos_of_pos (hs 5))) (hs 7)) (hs 8))
  obtain ⟨b₃,hb₃⟩ := hmeasure (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) hRad
  obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  let g := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.firstBalancedSlope i) (hU i)
  let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) hg₁
  let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) hg₂
  let den := density g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have hden : Integrable den := first_balanced_density_integrable g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have he := actual_first_family_two_energies p hg hp source F selector C₁ C₂ w
    (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) omega₁ omega₂ Φ (fun i y => U₀ i (y+ρ i))
    A₁ A₂ C R K L d h s hpos hs den hden hsep homega₁ homega₂ hcut
    J B₁ B₂ hB₁ hB₂ hWeighted hleft hright
  have hd : (∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖den z‖) ≤
      Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
        (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker := by
    apply (le_div_iff₀ (pow_pos (by linarith : 0 < 1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) Aker)).mpr
    exact (mul_comm _ _).le.trans hMoment
  exact he.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    (by have := firstRootScale_pos s hs; positivity))

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open JointLogSeparation MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
variable {ι : Type*} [DecidableEq ι]
theorem actual_first_retained_two_energies (ε : ℝ) (hε : 0<ε)
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile Kpush : ℝ,0 ≤ Cprofile ∧ 0<Kpush ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (_hc : ∀ i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr : ∀ i,lambda^2∣p i-1)
    (F : Finset ι) (b : SecondPassArithmetic.CubeCoordinates ι) (common : Finset ι)
    (Ψ₁ Ψ₂ : Eis→*ℂ) (mleft mright dd : Eis) (H₁ H₂ selector : Finset ι→ℂ)
    (labels : Finset (Ideal Eis)) (a : Ideal Eis×Eis→ℂ) (Γ Y : ℝ)
    (_hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (_hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (_hΓ : 0≤Γ) (_hY : 0<Y)
    (_hlabels : ∀ f∈labels,Squarefree f) (_hn : ∀ f∈labels,f≠0)
    (_ha : ∀ x∈firstRetainedSource p labels b Y,‖a x‖≤Γ)
    (omega₁ omega₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : Ideal Eis×Eis → ℝ) (K L : ℝ) (_hK : 0<K) (s : Fin 9→ℝ)
    (_hs : ∀ i,0<s i),
    let source := firstRetainedSource p labels b Y
    let C₁ := firstCanonicalCoefficient p hg b common true Ψ₁ mleft dd H₁
    let C₂ := firstCanonicalCoefficient p hg b common false Ψ₂ mright dd H₂
    let w := retainedCubeWeight p hp hg b common Ψ₁ Ψ₂ mleft mright dd a
    ∀ (_hpos : ∀ x∈source,0<A₁ x ∧ 0<A₂ x ∧ 0<C x ∧ 0<R x ∧ dd≠0 ∧ x.2≠0)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_homega₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2 j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_homega₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2 j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      omega₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2 j ≠ 0 →
      omega₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → omega₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) dd x.2 j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstCanonicalSecondEnergy p hp hg hinj F b common true Ψ₁ mleft dd H₁ selector omega₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstCanonicalSecondEnergy p hp hg hinj F b common false Ψ₂ mright dd H₂ selector omega₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F (fun _=>selector) C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K (fun _=>dd) Prod.snd s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂))*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hprofile⟩ := actual_first_moving_family_two_energies (ι := ι) (κ := Ideal Eis×Eis)
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  obtain ⟨Kpush,hKpush,hpush⟩ := first_retained_actual_second_energy ε hε
  refine ⟨Cprofile,Kpush,hCprofile,hKpush,?_⟩
  intro p hp _ hg hinj hcop hc hpr F b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha omega₁ omega₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs
    source C₁ C₂ w hpos hρ hc₁ hc₂ hc₁b hc₂b hL homega₁ homega₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hweight : 0≤Γ*Kpush*Y^ε := by positivity
  have hroot:Real.sqrt (Γ*Kpush*Y^ε*B₁)*Real.sqrt (Γ*Kpush*Y^ε*B₂)=Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂):=by
    rw [Real.sqrt_mul hweight,Real.sqrt_mul hweight]
    calc
      _=(Real.sqrt (Γ*Kpush*Y^ε))^2*(Real.sqrt B₁*Real.sqrt B₂):=by ring
      _= _:=by rw [Real.sq_sqrt hweight]
  rw [←hroot]
  apply hprofile p hp hg source F (fun _=>selector) C₁ C₂ w omega₁ omega₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK (fun _=>dd) Prod.snd s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    homega₁ homega₂ hcut (Γ*Kpush*Y^ε*B₁) (Γ*Kpush*Y^ε*B₂) (mul_nonneg hweight hB₁) (mul_nonneg hweight hB₂)
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F b common Ψ₁ Ψ₂ hΨ₁ hΨ₂ mleft mright dd
      labels a Γ Y hΓ hY hlabels hn ha true H₁ selector omega₁ (s 7)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (hs 7)
    apply he.trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hleft z) hweight
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F b common Ψ₁ Ψ₂ hΨ₁ hΨ₂ mleft mright dd
      labels a Γ Y hΓ hY hlabels hn ha false H₂ selector omega₂ (s 8)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (hs 8)
    apply he.trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hright z) hweight

end
end InverseMoment

noncomputable section
namespace InverseMomentFirstChildWindows
open InverseMoment InverseMomentFirstProfileUniform
open InverseSecondChildWindows

theorem fresh_three_window (g : 𝓢(ℝ,ℂ)) (m bcap : ℝ)
    (lo hi : Fin 3→ℝ) (hm : 0≤ m)
    (hg : Function.support g⊆Set.Icc (-m) m)
    (hlo : ∀i,0<lo i) (hhi : ∀i,lo i≤ hi i) :
    ∃(w : 𝓢(ℝ,ℂ))(a b : ℝ),0<a ∧ a≤ b ∧ HasCompactSupport (w : ℝ→ℂ) ∧
      tsupport (w : ℝ→ℂ)⊆Set.Icc a b ∧
      ∀(c θ u v r n : ℝ),1≤ c → c≤ bcap →
        u∈Set.Icc (lo 0) (hi 0) → v∈Set.Icc (lo 1) (hi 1) → r∈Set.Icc (lo 2) (hi 2) →
        0<n → positiveSource g c θ (u*v*r*n)≠0 → w n=1 := by
  let R := m+Real.log bcap
  let a := Real.exp (-R)/(hi 0*hi 1*hi 2)
  let b := Real.exp R/(lo 0*lo 1*lo 2)
  have hhip (i : Fin 3) : 0<hi i := (hlo i).trans_le (hhi i)
  have hh0 := hhip 0
  have hh1 := hhip 1
  have hh2 := hhip 2
  have hl0 := hlo 0
  have hl1 := hlo 1
  have hl2 := hlo 2
  have ha : 0<a := by dsimp [a];positivity
  have hb : 0<b := by dsimp [b];positivity
  obtain ⟨w,hwc,hwone,hws⟩ := InverseSecondChildWindows.positive_cutoff a (a+b+1) ha (by linarith)
  refine ⟨w,a/2,a+b+2,half_pos ha,by linarith,hwc,by convert hws using 1; ring_nf,?_⟩
  intro c θ u v r n hc hcb hu hv hr hn hnz
  have hu0 := (hlo 0).trans_le hu.1
  have hv0 := (hlo 1).trans_le hv.1
  have hr0 := (hlo 2).trans_le hr.1
  have hs := positiveSource_ratio_support g m bcap c θ (u*v*r*n) hm hg hc hcb (by positivity) hnz
  have hnlo : a≤ n := by
    apply (div_le_iff₀ (by positivity : 0<hi 0*hi 1*hi 2)).mpr
    calc
      _ ≤ u*v*r*n := hs.1
      _ ≤ (hi 0*hi 1*hi 2)*n := mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul hu.2 hv.2 hv0.le (hhip 0).le) hr.2 hr0.le (by positivity)) hn.le
      _ = _ := by ring
  have hnhi : n≤ b := by
    apply (le_div_iff₀ (by positivity : 0<lo 0*lo 1*lo 2)).mpr
    calc
      _ = (lo 0*lo 1*lo 2)*n := by ring
      _ ≤ u*v*r*n := mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul hu.1 hv.1 (hlo 1).le hu0.le) hr.1 (hlo 2).le (by positivity)) hn.le
      _ ≤ _ := hs.2
  exact hwone n ⟨hnlo,by linarith⟩

def outerIndex (i : Fin 7) : Fin 9 := i.castLE (by decide)

theorem fixed_windows (g₁ g₂ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 7→ℝ) (Bρ : Fin 9→ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂)
    (hlo : ∀i,0<lo i) (hhi : ∀i,lo i≤ hi i) (hBρ : ∀i,0≤ Bρ i) :
    ∃(w₁ w₂ : 𝓢(ℝ,ℂ))(U : Fin 9→𝓢(ℝ,ℂ))(M : Fin 9→ℝ)(a b : ℝ),
      0<a ∧ a≤ b ∧ HasCompactSupport (w₁ : ℝ→ℂ) ∧ HasCompactSupport (w₂ : ℝ→ℂ) ∧
      tsupport (w₁ : ℝ→ℂ)⊆Set.Icc a b ∧ tsupport (w₂ : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀i,0≤ M i) ∧ (∀i,HasCompactSupport (U i : ℝ→ℂ)) ∧
      (∀i,Function.support (U i)⊆Set.Icc (-M i) (M i)) ∧
      (∀(c θ u v r n : ℝ),1≤ c → c≤ bcap →
        u∈Set.Icc (lo 0) (hi 0) → v∈Set.Icc (lo 2) (hi 2) → r∈Set.Icc (lo 5) (hi 5) →
        0<n → positiveSource g₁ c θ (u*v*r*n)≠0 → w₁ n=1) ∧
      (∀(c θ u v r n : ℝ),1≤ c → c≤ bcap →
        u∈Set.Icc (lo 1) (hi 1) → v∈Set.Icc (lo 2) (hi 2) → r∈Set.Icc (lo 5) (hi 5) →
        0<n → positiveSource g₂ c θ (u*v*r*n)≠0 → w₂ n=1) ∧
      (∀(q ρ : Fin 9→ℝ),(∀i,|ρ i|≤ Bρ i) →
        (∀i : Fin 7,q (outerIndex i)∈Set.Icc (lo i) (hi i)) →
        w₁ (q 7)≠0 → w₂ (q 8)≠0 → ∀i,U i (Real.log (q i)+ρ i)=1) := by
  let left : Fin 3→Fin 7 := ![0,2,5]
  let right : Fin 3→Fin 7 := ![1,2,5]
  obtain ⟨w₁,a₁,b₁,ha₁,hab₁,hwc₁,hws₁,hfresh₁⟩ := fresh_three_window g₁ m₁ bcap
    (lo ∘ left) (hi ∘ left) hm₁ hg₁ (fun i=>hlo (left i)) (fun i=>hhi (left i))
  obtain ⟨w₂,a₂,b₂,ha₂,hab₂,hwc₂,hws₂,hfresh₂⟩ := fresh_three_window g₂ m₂ bcap
    (lo ∘ right) (hi ∘ right) hm₂ hg₂ (fun i=>hlo (right i)) (fun i=>hhi (right i))
  let l : Fin 9→ℝ := ![lo 0,lo 1,lo 2,lo 3,lo 4,lo 5,lo 6,a₁,a₂]
  let u : Fin 9→ℝ := ![hi 0,hi 1,hi 2,hi 3,hi 4,hi 5,hi 6,b₁,b₂]
  have hl (i : Fin 9) : 0<l i := by
    fin_cases i
    · exact hlo 0
    · exact hlo 1
    · exact hlo 2
    · exact hlo 3
    · exact hlo 4
    · exact hlo 5
    · exact hlo 6
    · exact ha₁
    · exact ha₂
  let H (i : Fin 9) := |Real.log (l i)|+|Real.log (u i)|+Bρ i
  have hH (i : Fin 9) : 0≤ H i := by dsimp [H];exact add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hBρ i)
  choose V hVc hVs hVone hVsupport hVzero using
    fun i : Fin 9=>JointLogSeparation.exists_complex_smooth_cutoff (H i) (hH i)
  let U (i : Fin 9) : 𝓢(ℝ,ℂ) := (hVc i).toSchwartzMap (hVs i)
  refine ⟨w₁,w₂,U,(fun i=>H i+1),min a₁ a₂,max b₁ b₂,lt_min ha₁ ha₂,
    (min_le_left _ _).trans (hab₁.trans (le_max_left _ _)),hwc₁,hwc₂,?_,?_,
    (fun i=>by linarith [hH i]),hVc,(fun i=>(subset_tsupport _).trans (hVsupport i)),hfresh₁,hfresh₂,?_⟩
  · intro x hx
    exact ⟨(min_le_left _ _).trans (hws₁ hx).1,(hws₁ hx).2.trans (le_max_left _ _)⟩
  · intro x hx
    exact ⟨(min_le_right _ _).trans (hws₂ hx).1,(hws₂ hx).2.trans (le_max_right _ _)⟩
  · intro q ρ hρ hblock hw₁ hw₂ i
    have hq (k : Fin 9) : q k∈Set.Icc (l k) (u k) := by
      fin_cases k
      · exact hblock 0
      · exact hblock 1
      · exact hblock 2
      · exact hblock 3
      · exact hblock 4
      · exact hblock 5
      · exact hblock 6
      · exact hws₁ (subset_tsupport _ hw₁)
      · exact hws₂ (subset_tsupport _ hw₂)
    exact hVone i _ (translated_log_bound _ _ _ _ _ (hl i) (hq i) (hρ i))

end InverseMomentFirstChildWindows
end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
