/-
Assigned callers and second fibers adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.InitialPhysicalMeasure

/-!
# Assigned callers and second fibers

Assigned sources of the initial energy caller (`InverseInitialEnergyCallerAssigned`) and the
second fibers `InverseSecondFibers` with their outer triples, cardinality and weight bounds.
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

namespace InverseInitialEnergyCallerAllocation
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerSector InverseInitialRayAttachment
open scoped BigOperators Classical
local notation "Eis" => O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def modeCoefficient (Ψ:Eis→*ℂ)(j:Eis)(Z D B v θ H:ℝ)
    (x:Source (ι:=ι) 0)(ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) : ℂ :=
  outerCoefficient p hg Ψ j (sourcePoint x ∅ ∅) ρ *
    secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2)
      (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H)

def allocatedMode (u:Eisˣ)(pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)
    (slots J₁ J₂:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (x:Source (ι:=ι) 0)(ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) : ℂ :=
  let height := profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
  modeCoefficient p hg Ψ j Z D B v θ H x ρ z *
    (star (primeMark J₁ lists a (x.common∪x.overlap))*primeMark J₂ lists a (x.common∪x.overlap))*
    (star (child p hg pool (secondRayMinus Ψ ρ) j (slots\J₁) lists a
      (childLogTest ω₁ (-height 4)) (Z^(columnCenter D B v))
      (initialChild (toTuple p (sectorSource u x))))*
      child p hg pool (secondRayPlus Ψ ρ) j (slots\J₂) lists a
      (childLogTest ω₂ (height 5)) (Z^(columnCenter D B v))
      (negativeChild (initialChild (toTuple p (sectorSource u x)))))

theorem rowMode_eq_allocations
    (hpr:∀i,lambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) :
    rowMode p hp hg hpr pool Ψ j slots lists a ω₁ ω₂ Z D B v θ H x ρ z=
      ∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        allocatedMode p hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
  unfold rowMode
  dsimp only
  rw [markedModeColumn_sector p hp hg hpr x hdiv u hu,
    markedModeColumn_negative_sector p hp hg hpr x hdiv u hu]
  simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  simp only [star_mul,allocatedMode,modeCoefficient]
  ring

include hp hcop in
theorem modeCoefficient_norm_le
    (hpr:∀i,lambda^2∣p i-1)
    (Ψ:Eis→*ℂ)(hΨ:∀n,‖Ψ n‖≤1)(j:Eis)(Z D B v θ H:ℝ)
    (x:Source (ι:=ι) 0)(ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) :
    ‖modeCoefficient p hg Ψ j Z D B v θ H x ρ z‖≤‖secondRayCoefficient ρ‖ := by
  simp only [modeCoefficient,norm_mul,secondOuterPhase_norm,mul_one]
  exact InverseInitialEnergyCallerWeights.outerCoefficient_norm_le p hp hcop hg hpr Ψ hΨ j _ ρ


end InverseInitialEnergyCallerAllocation

namespace InverseInitialEnergyCallerAssigned
open Eisenstein SchwartzPlanePoisson CompletedGauss
open InverseMoment InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialClippedColumns
open scoped BigOperators Classical
local notation "Eis" => O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def attach {J : ℕ} (x : Source (ι:=ι) 0) (q : Fin J→ι) : Source (ι:=ι) J where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency
  assigned := q

def erase {J : ℕ} (x : Source (ι:=ι) J) : Source (ι:=ι) 0 where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency
  assigned := Fin.elim0

omit [DecidableEq ι] in
@[simp] theorem erase_attach {J : ℕ} (x : Source (ι:=ι) 0) (q : Fin J→ι) :
    erase (attach x q) = x := by
  apply Source.ext <;> try rfl
  funext i
  exact Fin.elim0 i

omit [DecidableEq ι] in
theorem attach_injective {J : ℕ} :
    Function.Injective (fun z : Source (ι:=ι) 0 × (Fin J→ι) => attach z.1 z.2) := by
  intro x y h
  apply Prod.ext
  · simpa only [erase_attach] using congrArg erase h
  · exact congrArg Source.assigned h

def attachPair (J₁ J₂ : Finset σ)
    (z : Source (ι:=ι) 0 × ((∀ i∈J₁,ι) × (∀ i∈J₂,ι))) :
    Source (ι:=ι) (J₁.card+J₂.card) :=
  attach z.1 (pairedSlotAssignment J₁ J₂ z.2)

omit [DecidableEq ι] [DecidableEq σ] in
theorem attachPair_injective (J₁ J₂ : Finset σ) :
    Function.Injective (attachPair (ι:=ι) J₁ J₂) := by
  intro x y h
  have he := @attach_injective ι (J₁.card + J₂.card)
    (x.1,pairedSlotAssignment J₁ J₂ x.2) (y.1,pairedSlotAssignment J₁ J₂ y.2) h
  exact Prod.ext (congrArg (fun z : Source (ι:=ι) 0 × (Fin (J₁.card+J₂.card)→ι)=>z.1) he)
    (pairedSlotAssignment_injective J₁ J₂
      (congrArg (fun z : Source (ι:=ι) 0 × (Fin (J₁.card+J₂.card)→ι)=>z.2) he))

def assignedSource (S : Finset (Source (ι:=ι) 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ→Finset ι) : Finset (Source (ι:=ι) (J₁.card+J₂.card)) :=
  ((S ×ˢ ((J₁.pi L₁) ×ˢ (J₂.pi L₂))).filter
    (fun z=>∀ i,pairedSlotAssignment J₁ J₂ z.2 i∈z.1.common∪z.1.overlap)).image
      (attachPair J₁ J₂)

def coefficient (J₁ J₂ : Finset σ) (a₁ a₂ : σ→ι→ℂ)
    (x : Source (ι:=ι) (J₁.card+J₂.card)) : ℂ :=
  star (slotAssignmentWeight J₁ a₁
    (fun i hi=>x.assigned (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩)))) *
    slotAssignmentWeight J₂ a₂
    (fun i hi=>x.assigned (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩)))

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem coefficient_attach (J₁ J₂ : Finset σ) (a₁ a₂ : σ→ι→ℂ)
    (x : Source (ι:=ι) 0) (q : (∀ i∈J₁,ι) × (∀ i∈J₂,ι)) :
    coefficient J₁ J₂ a₁ a₂ (attachPair J₁ J₂ (x,q)) = pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  simp only [coefficient,attachPair,attach,pairedSlotAssignment,
    Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,pairedSlotWeight]

theorem assignedSource_sum (S : Finset (Source (ι:=ι) 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ→Finset ι) (F : Source (ι:=ι) (J₁.card+J₂.card)→ℂ) :
    ∑ x∈assignedSource S J₁ J₂ L₁ L₂,F x =
      ∑ y∈S,∑ q∈(J₁.pi (fun i=>L₁ i∩(y.common∪y.overlap))) ×ˢ
        (J₂.pi (fun i=>L₂ i∩(y.common∪y.overlap))),F (attachPair J₁ J₂ (y,q)) := by
  rw [assignedSource,Finset.sum_image (fun x _ y _ he=>attachPair_injective J₁ J₂ he),
    Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem original_marks_eq_assigned (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (w P : Source (ι:=ι) 0→ℂ) :
    (∑ y∈S,w y*(star (primeMark J₁ L₁ a₁ (y.common∪y.overlap))*
      primeMark J₂ L₂ a₂ (y.common∪y.overlap))*P y) =
    ∑ x∈assignedSource S J₁ J₂ L₁ L₂,
      (w (erase x)*coefficient J₁ J₂ a₁ a₂ x)*P (erase x) := by
  rw [assignedSource_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [coefficient_attach]
  simp only [attachPair,erase_attach]

theorem assignedSource_support (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι)
    (hdiv : ∀ x∈S,x.divisor⊆x.common)
    {x : Source (ι:=ι) (J₁.card+J₂.card)} (hx : x∈assignedSource S J₁ J₂ L₁ L₂) :
    erase x∈S ∧ x.divisor⊆x.common ∧ ∀ i,x.assigned i∈x.common∪x.overlap := by
  obtain ⟨⟨y,q⟩,hy,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hmem,hq⟩ := Finset.mem_filter.mp hy
  have hyS := (Finset.mem_product.mp hmem).1
  exact ⟨by simpa only [attachPair,erase_attach] using hyS,hdiv y hyS,hq⟩

theorem coefficient_norm_le_one (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (ha₁ : ∀ i∈J₁,∀ q∈L₁ i,‖a₁ i q‖≤1)
    (ha₂ : ∀ i∈J₂,∀ q∈L₂ i,‖a₂ i q‖≤1)
    {x : Source (ι:=ι) (J₁.card+J₂.card)} (hx : x∈assignedSource S J₁ J₂ L₁ L₂) :
    ‖coefficient J₁ J₂ a₁ a₂ x‖≤1 := by
  obtain ⟨⟨y,q⟩,hy,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hmem,hq⟩ := Finset.mem_filter.mp hy
  have hq' : q∈(J₁.pi L₁ ×ˢ J₂.pi L₂).filter
      (fun q=>∀ i,pairedSlotAssignment J₁ J₂ q i∈y.common∪y.overlap) :=
    Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hmem).2,hq⟩
  rw [paired_assignment_filter] at hq'
  rw [coefficient_attach]
  exact pairedSlotWeight_norm_le_one J₁ J₂ L₁ L₂ a₁ a₂ _ q hq' ha₁ ha₂

theorem assigned_tuple_valid
    (p : ι→O) (hp : ∀ i,p i≠0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hpr : ∀ i,lambda^2∣p i-1)
    (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι)
    (hdiv : ∀ x∈S,x.divisor⊆x.common) (u : Oˣ)
    {x : Source (ι:=ι) (J₁.card+J₂.card)} (hx : x∈assignedSource S J₁ J₂ L₁ L₂) :
    InitialSourceValid (toTuple p (sectorSource u x)) := by
  obtain ⟨_,hdivx,hassigned⟩ := assignedSource_support S J₁ J₂ L₁ L₂ hdiv hx
  exact sourceTuple_valid p hp hpr x.common x.divisor x.overlap
    ((u:O)^5*x.frequency) x.assigned hdivx hassigned


end InverseInitialEnergyCallerAssigned

namespace InverseInitialEnergyCallerSupport
open Eisenstein SchwartzPlanePoisson CompletedGauss
open InverseMoment InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialClippedColumns
open scoped BigOperators Classical
local notation "Eis" => O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_sector_energy {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hsupport : ∀ x ∈ S, ∀i,x.assigned i∈x.common∪x.overlap)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (F : InitialChild → ℂ) :
    (∑ x ∈ S, ‖F (initialChild (toTuple p (sectorSource u x)))‖^2) ≤
      ∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) *
          ∑ k ∈ rows, ‖F (t,f,k)‖^2 := by
  let T := S.image (fun x => toTuple p (sectorSource u x))
  have hvalid : ∀ y ∈ T, InitialSourceValid y := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact sourceTuple_valid p hp hpr x.common x.divisor x.overlap
      ((u:Eis)^5*x.frequency) x.assigned (hdiv x hx) (hsupport x hx)
  have hc : ∀ y ∈ T, (initialChild y).2.1 ∈ labels ∧ (initialChild y).2.2 ∈ rows := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hchild x hx
  have he := initial_energy_projection T hvalid labels rows hlabels hc
    (fun _ => 1) (fun _ _ => le_rfl) F
  simp only [one_mul] at he
  rw [show initialQuotientSet T = quotientSet p S from
    quotientSet_eq_initial p hp S u hdiv] at he
  have hs : (∑ y ∈ T, ‖F (initialChild y)‖^2) =
      ∑ x ∈ S, ‖F (initialChild (toTuple p (sectorSource u x)))‖^2 := by
    exact Finset.sum_image (fun x _ y _ he => sectorSource_injective u (toTuple_injective p hinj he))
  rw [hs] at he
  exact he

include hp in

theorem actual_sector_signed_pair {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hsupport : ∀ x ∈ S, ∀i,x.assigned i∈x.common∪x.overlap)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (c : Source (ι:=ι) J → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hc : ∀ x ∈ S, ‖c x‖ ≤ A) (F G : InitialChild → ℂ) :
    ‖∑ x ∈ S, c x * star (F (initialChild (toTuple p (sectorSource u x)))) *
        G (initialChild (toTuple p (sectorSource u x)))‖ ≤
      A * (Real.sqrt (∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) * ∑ k ∈ rows, ‖F (t,f,k)‖^2) *
        Real.sqrt (∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) * ∑ k ∈ rows, ‖G (t,f,k)‖^2)) := by
  let child := fun x : Source (ι:=ι) J => initialChild (toTuple p (sectorSource u x))
  have hF := actual_sector_energy p hp hinj hpr S u hdiv hsupport labels rows hlabels hchild F
  have hG := actual_sector_energy p hp hinj hpr S u hdiv hsupport labels rows hlabels hchild G
  calc
    _ ≤ ∑ x ∈ S, ‖c x * star (F (child x)) * G (child x)‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ S, A * (‖F (child x)‖ * ‖G (child x)‖) := by
      apply Finset.sum_le_sum
      intro x hx
      simp only [norm_mul, norm_star]
      nlinarith [mul_le_mul_of_nonneg_right (hc x hx)
        (mul_nonneg (norm_nonneg (F (child x))) (norm_nonneg (G (child x))))]
    _ = A * ∑ x ∈ S, ‖F (child x)‖ * ‖G (child x)‖ := by rw [Finset.mul_sum]
    _ ≤ A * (Real.sqrt (∑ x ∈ S, ‖F (child x)‖^2) *
        Real.sqrt (∑ x ∈ S, ‖G (child x)‖^2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt S _ _) hA
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA


end InverseInitialEnergyCallerSupport

namespace InverseInitialEnergyCallerAssignedPair
open Eisenstein SchwartzPlanePoisson CompletedGauss
open InverseMoment InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialClippedColumns
open scoped BigOperators Classical
local notation "Eis" => O
open InverseInitialEnergyCallerAssigned InverseInitialEnergyCallerOpposite
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] in
theorem child_erase {J:ℕ}(u:Eisˣ)(x:Source (ι:=ι) J) :
    initialChild (toTuple p (sectorSource u (erase x)))=
      initialChild (toTuple p (sectorSource u x)) := rfl

include hp in

theorem original_assigned_pair
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,lambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)
    (J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι)(a₁ a₂:σ→ι→ℂ)
    (ha₁:∀i∈J₁,∀q∈L₁ i,‖a₁ i q‖≤1)
    (ha₂:∀i∈J₂,∀q∈L₂ i,‖a₂ i q‖≤1)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (labels:Finset (Ideal Eis))(rows:Finset Eis)
    (hlabels:∀f∈labels,f≠0)
    (hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
    (c:Source (ι:=ι) 0→ℂ)(A:ℝ)(hA:0≤A)(hc:∀x∈S,‖c x‖≤A)
    (F G:InitialChild→ℂ) :
    ‖∑x∈S,c x*(star (primeMark J₁ L₁ a₁ (x.common∪x.overlap))*
      primeMark J₂ L₂ a₂ (x.common∪x.overlap))*
      (star (F (initialChild (toTuple p (sectorSource u x))))*
        G (initialChild (toTuple p (sectorSource u x))))‖≤
      A*(Real.sqrt (∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card)*
        ∑f∈labels,((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1)*
          ∑k∈rows,‖F (t,f,k)‖^2)*
        Real.sqrt (∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card)*
        ∑f∈labels,((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1)*
          ∑k∈rows,‖G (t,f,k)‖^2)) := by
  let T := assignedSource S J₁ J₂ L₁ L₂
  have hs (x:Source (ι:=ι) (J₁.card+J₂.card))(hx:x∈T) :=
    assignedSource_support S J₁ J₂ L₁ L₂ hdiv hx
  have hcoeff (x:Source (ι:=ι) (J₁.card+J₂.card))(hx:x∈T) :
      ‖c (erase x)*coefficient J₁ J₂ a₁ a₂ x‖≤A := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (coefficient_norm_le_one S J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ hx)
      (norm_nonneg _)).trans (by simpa only [mul_one] using hc (erase x) (hs x hx).1)
  rw [original_marks_eq_assigned S J₁ J₂ L₁ L₂ a₁ a₂ c
    (fun x=>star (F (initialChild (toTuple p (sectorSource u x))))*
      G (initialChild (toTuple p (sectorSource u x))))]
  simp only [child_erase,←mul_assoc]
  simpa only [←mul_assoc] using InverseInitialEnergyCallerSupport.actual_sector_signed_pair p hp hinj hpr T u
    (fun x hx=>(hs x hx).2.1) (fun x hx=>(hs x hx).2.2) labels rows hlabels
    (fun x hx=>by simpa only [child_erase] using hchild (erase x) (hs x hx).1)
    (fun x=>c (erase x)*coefficient J₁ J₂ a₁ a₂ x) A hA hcoeff F G


end InverseInitialEnergyCallerAssignedPair

namespace InverseInitialEnergyCallerAssignedCanonical
open Eisenstein SchwartzPlanePoisson CompletedGauss
open InverseMoment InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialClippedColumns
open scoped BigOperators Classical
local notation "Eis" => O
open InverseInitialEnergyCallerAssigned InverseInitialEnergyCallerOpposite
open InverseInitialEnergyCallerCanonical
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

include hp in
theorem original_assigned_canonical_pair
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,lambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)
    (J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι)(a₁ a₂:σ→ι→ℂ)
    (ha₁:∀i∈J₁,∀q∈L₁ i,‖a₁ i q‖≤1)
    (ha₂:∀i∈J₂,∀q∈L₂ i,‖a₂ i q‖≤1)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (labels:Finset (Ideal Eis))(rows:Finset Eis)
    (hlabels:∀f∈labels,f≠0)(hneg:∀k∈rows,-k∈rows)
    (hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
    (c:Source (ι:=ι) 0→ℂ)(A:ℝ)(hA:0≤A)(hc:∀x∈S,‖c x‖≤A)
    (pool:Finset ι)(Ψ₁ Ψ₂:Eis→*ℂ)(j:Eis)(slots₁ slots₂:Finset σ)
    (W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ){Z:ℝ}(hZ:0<Z)(F B₁ B₂:ℝ)
    (hmoment₁:∀t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
      normalizedColumnEnergy p hg pool Ψ₁ (j*primaryIdealGenerator t)
        slots₁ L₁ a₁ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        W₁ X₁ Z F≤B₁)
    (hmoment₂:∀t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
      normalizedColumnEnergy p hg pool Ψ₂ (j*primaryIdealGenerator t)
        slots₂ L₂ a₂ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        W₂ X₂ Z F≤B₂) :
    ‖∑x∈S,c x*(star (primeMark J₁ L₁ a₁ (x.common∪x.overlap))*
      primeMark J₂ L₂ a₂ (x.common∪x.overlap))*
      (star (child p hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
          (initialChild (toTuple p (sectorSource u x))))*
        child p hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
          (negativeChild (initialChild (toTuple p (sectorSource u x)))))‖≤
      A*(Z^F*∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*(Real.sqrt B₁*Real.sqrt B₂) := by
  let T := quotientSet p (assignedSource S J₁ J₂ L₁ L₂)
  let f := child p hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
  let g := child p hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
  have h₁ := energy_le_moment p hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
    (J₁.card+J₂.card) T labels rows hZ F B₁ hmoment₁
  have h₂ := energy_le_moment p hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
    (J₁.card+J₂.card) T labels rows hZ F B₂ hmoment₂
  rw [←energy_neg_rows T labels rows hneg (J₁.card+J₂.card) g] at h₂
  have hh := InverseInitialEnergyCallerAssignedPair.original_assigned_pair p hp hinj hpr
    S u J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ hdiv labels rows hlabels hchild c A hA hc f
    (fun k=>g (negativeChild k))
  apply hh.trans
  calc
    _≤A*(Real.sqrt ((Z^F*∑t∈T,((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*B₁)*
      Real.sqrt ((Z^F*∑t∈T,((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*B₂)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt h₁)
        (Real.sqrt_le_sqrt h₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA
    _=_ := by
      rw [sqrt_pair_mass _ B₁ B₂ (mul_nonneg (Real.rpow_nonneg hZ.le _)
        (Finset.sum_nonneg fun t ht=>by positivity))]
      ring


end InverseInitialEnergyCallerAssignedCanonical

namespace InverseInitialEnergyCallerBranch
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialRayAttachment
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "Eis" => O
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

include hp hcop in
theorem actual_allocated_mode_bound
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,lambda^2∣p i-1)
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)(hdiv:∀x∈S,x.divisor⊆x.common)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
    (slots J₁ J₂:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (ha₁:∀i∈J₁,∀q∈lists i,‖a i q‖≤1)(ha₂:∀i∈J₂,∀q∈lists i,‖a i q‖≤1)
    (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)(hZ:0<Z)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
    (w:Source (ι:=ι) 0→ℂ)(hw:∀x∈S,‖w x‖≤1)
    (labels:Finset (Ideal Eis))(rows:Finset Eis)
    (hlabels:∀f∈labels,f≠0)(hneg:∀k∈rows,-k∈rows)
    (hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
    (F B₁ B₂:ℝ)
    (hmoment₁:∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
      normalizedColumnEnergy p hg pool (secondRayMinus Ψ ρ) (j*primaryIdealGenerator t)
        (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
        (Z^(columnCenter D B v)) Z F≤B₁)
    (hmoment₂:∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
      normalizedColumnEnergy p hg pool (secondRayPlus Ψ ρ) (j*primaryIdealGenerator t)
        (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
        (Z^(columnCenter D B v)) Z F≤B₂) :
    ‖∑x∈S,w x*allocatedMode p hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
      Z D B v θ H x ρ z‖≤
      ‖secondRayCoefficient ρ‖*(Z^F*∑t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*(Real.sqrt B₁*Real.sqrt B₂) := by
  let c := fun x=>w x*modeCoefficient p hg Ψ j Z D B v θ H x ρ z
  have hcoeff (x:Source (ι:=ι) 0)(hx:x∈S) : ‖c x‖≤‖secondRayCoefficient ρ‖ := by
    dsimp only [c]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw x hx)).trans
      (modeCoefficient_norm_le p hp hcop hg hpr Ψ hΨ j Z D B v θ H x ρ z)
  have he := InverseInitialEnergyCallerAssignedCanonical.original_assigned_canonical_pair
    p hp hg hinj hpr S u J₁ J₂ lists lists a a ha₁ ha₂ hdiv labels rows hlabels hneg hchild
    c ‖secondRayCoefficient ρ‖ (norm_nonneg _) hcoeff pool (secondRayMinus Ψ ρ) (secondRayPlus Ψ ρ) j
    (slots\J₁) (slots\J₂)
    (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
    (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
    (Z^(columnCenter D B v)) (Z^(columnCenter D B v)) hZ F B₁ B₂ hmoment₁ hmoment₂
  apply le_trans (le_of_eq ?_) he
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only [allocatedMode,c]
  ring


end InverseInitialEnergyCallerBranch

namespace InverseInitialEnergyCallerMass
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialRayAttachment
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "Eis" => O
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _
theorem assigned_quotient_subset {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→Eis)(S:Finset (Source (ι:=ι) 0))(J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι) :
    quotientSet p (assignedSource S J₁ J₂ L₁ L₂)⊆quotientSet p S := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨⟨y,q⟩,hy,rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨y,(Finset.mem_product.mp (Finset.mem_filter.mp hy).1).1,rfl⟩

theorem divisor_weight_mono {t:Ideal Eis}(ht:t≠0){J K:ℕ}(hJK:J≤K) :
    ((idealDivisors t).card:ℝ)^J≤((idealDivisors t).card:ℝ)^K := by
  have hc : (1:ℝ)≤(idealDivisors t).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1,(mem_idealDivisors ht).mpr (one_dvd t)⟩
  exact pow_le_pow_right₀ hc hJK

theorem assigned_quotient_mass (K:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (S:Finset (Source (ι:=ι) 0))(J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι)
      (_hJ:J₁.card+J₂.card≤K)(Z R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R),
      (∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))≤C*Z^(R+π) := by
  have hε : 0<π/(U+1) := div_pos hπ (by linarith)
  obtain ⟨C,hC,hb⟩ := normalized_mass_bound K (π/(U+1)) hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ S J₁ J₂ L₁ L₂ hJ Z R hZ hR hn
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  let T := quotientSet p (assignedSource S J₁ J₂ L₁ L₂)
  have ht : ∀t∈T,t≠0 := quotientSet_nonzero p hp _
  have hnorm : ∀t∈T,(t.absNorm:ℝ)≤Z^R :=
    fun t hh=>hn t (assigned_quotient_subset p S J₁ J₂ L₁ L₂ hh)
  have hm := hb T (Z^R) (Real.rpow_pos_of_pos hZp _) ht hnorm
  have hpow : (Z^R)^(π/(U+1))≤Z^π := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    apply (mul_le_mul_of_nonneg_right hR hε.le).trans
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<U+1)).mpr
    nlinarith
  have hm' := hm.trans (mul_le_mul_of_nonneg_left hpow hC.le)
  have hs := mul_le_mul_of_nonneg_left hm' (Real.rpow_nonneg hZp.le R)
  simp only [normalizedMass,←mul_assoc,mul_inv_cancel₀ (Real.rpow_pos_of_pos hZp R).ne',one_mul] at hs
  calc
    _≤∑t∈T,((idealDivisors t).card:ℝ)^K :=
      Finset.sum_le_sum fun t hmem=>divisor_weight_mono (ht t hmem) hJ
    _≤Z^R*(C*Z^π) := by simpa only [mul_assoc] using hs
    _=C*Z^(R+π) := by rw [Real.rpow_add hZp];ring


end InverseInitialEnergyCallerMass

namespace InverseInitialEnergyCallerAllSlots
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialRayAttachment
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "Eis" => O
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _
open InverseInitialEnergyCallerBranch
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem rowMode_sum_allocations
    (hpr:∀i,lambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)(u:Eisˣ)
    (hu:∀x∈S,unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))(w:Source (ι:=ι) 0→ℂ) :
    (∑x∈S,w x*rowMode p hp hg hpr pool Ψ j slots lists a ω₁ ω₂ Z D B v θ H x ρ z)=
      ∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        ∑x∈S,w x*allocatedMode p hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
  calc
    _=∑x∈S,∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        w x*allocatedMode p hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [rowMode_eq_allocations p hp hg hpr x (hdiv x hx) u (hu x hx)]
      simp only [Finset.mul_sum]
    _=_ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J hJ
      exact Finset.sum_comm

theorem all_slots_bound (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,lambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)(_hdiv:∀x∈S,x.divisor⊆x.common)
      (_hu:∀x∈S,unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
      (F E:ℝ)(_hE:0≤E)
      (_hmoment:∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ ρ) (j*primaryIdealGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤E ∧
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ ρ) (j*primaryIdealGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤E),
      ‖∑x∈S,w x*rowMode p hp hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := by
  obtain ⟨C,hC,hmass⟩ := InverseInitialEnergyCallerMass.assigned_quotient_mass (2*N) U π hU hπ
  refine ⟨C*4^N,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S u hdiv hu pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn ρ z w hw labels rows hlabels hneg hchild F E hE hmoment
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  let bound := C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E
  have hb (J₁:Finset σ)(hJ₁:J₁∈slots.powerset)(J₂:Finset σ)(hJ₂:J₂∈slots.powerset) :
      ‖∑x∈S,w x*allocatedMode p hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤bound := by
    have h₁ := Finset.mem_powerset.mp hJ₁
    have h₂ := Finset.mem_powerset.mp hJ₂
    have he := actual_allocated_mode_bound p hp hcop hg hinj hpr hc S u hdiv pool Ψ hΨ j
      slots J₁ J₂ lists a (fun i hi=>ha i (h₁ hi)) (fun i hi=>ha i (h₂ hi)) ω₁ ω₂
      Z D B v θ H hZp ρ z w hw labels rows hlabels hneg hchild F E E
      (fun t ht=>(hmoment J₁ hJ₁ J₂ hJ₂ t ht).1)
      (fun t ht=>(hmoment J₁ hJ₁ J₂ hJ₂ t ht).2)
    rw [Real.mul_self_sqrt hE] at he
    have hJ : J₁.card+J₂.card≤2*N := by
      have := (Finset.card_le_card h₁).trans hslots
      have := (Finset.card_le_card h₂).trans hslots
      omega
    have hm := hmass p hp S J₁ J₂ lists lists hJ Z R hZ hR hn
    apply he.trans
    calc
      _≤‖secondRayCoefficient ρ‖*(Z^F*(C*Z^(R+π)))*E := by gcongr
      _=bound := by dsimp only [bound];rw [add_assoc F R π,Real.rpow_add hZp F (R+π)];ring
  rw [rowMode_sum_allocations p hp hg hpr S hdiv u hu]
  calc
    _≤∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        ‖∑x∈S,w x*allocatedMode p hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z‖ := (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun J hJ=>norm_sum_le _ _)
    _≤∑_J₁∈slots.powerset,∑_J₂∈slots.powerset,bound :=
      Finset.sum_le_sum fun J₁ hJ₁=>Finset.sum_le_sum fun J₂ hJ₂=>hb J₁ hJ₁ J₂ hJ₂
    _=(4:ℝ)^slots.card*bound := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)=2*2 by norm_num,mul_pow]
      ring
    _≤(4:ℝ)^N*bound := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hslots) (by dsimp [bound];positivity)
    _=_ := by dsimp [bound];ring


end InverseInitialEnergyCallerAllSlots

namespace InverseInitialEnergyCallerUnits
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialRayAttachment
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "Eis" => O
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _
open InverseInitialEnergyCallerBranch
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def sourceSector (hpr:∀i,lambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>unitSector p hp hpr (sourcePoint x ∅ ∅)=u)

omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem sourceSector_partition (hpr:∀i,lambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(f:Source (ι:=ι) 0→ℂ) :
    (∑x∈S,f x)=∑u:Eisˣ,∑x∈sourceSector p hp hpr S u,f x :=
  (Finset.sum_fiberwise S (fun x=>unitSector p hp hpr (sourcePoint x ∅ ∅)) f).symm

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem quotientSet_mono {J:ℕ}{S T:Finset (Source (ι:=ι) J)}(hst:S⊆T) :
    quotientSet p S⊆quotientSet p T := Finset.image_subset_image hst

theorem all_units_bound (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,lambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F E:ℝ)(_hE:0≤E)
      (_hmoment:∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ ρ) (j*primaryIdealGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤E ∧
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ ρ) (j*primaryIdealGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤E),
      ‖∑x∈S,w x*rowMode p hp hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := by
  obtain ⟨C,hC,hbound⟩ := InverseInitialEnergyCallerAllSlots.all_slots_bound N U π hU hπ
  have hn : 0 < (Fintype.card Eisˣ : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨(Fintype.card Eisˣ : ℝ)*C,mul_pos hn hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn ρ z w hw labels rows hlabels hneg hchild F E hE hmoment
  have hb (u:Eisˣ) :
      ‖∑x∈sourceSector p hp hpr S u,w x*rowMode p hp hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := by
    have hs : sourceSector p hp hpr S u⊆S := Finset.filter_subset _ _
    apply hbound p hp hcop hg hinj hpr hc (sourceSector p hp hpr S u) u
      (fun x hx=>hdiv x (hs hx)) (fun x hx=>(Finset.mem_filter.mp hx).2)
      pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂ Z D B v θ H R hZ hR
      (fun t ht=>hn t (quotientSet_mono p hs ht)) ρ z w
      (fun x hx=>hw x (hs hx)) labels rows hlabels hneg
      (fun x hx=>by
        have hh := hchild x (hs hx)
        rw [(Finset.mem_filter.mp hx).2] at hh
        exact hh) F E hE
    intro J₁ hJ₁ J₂ hJ₂ t ht
    exact hmoment J₁ hJ₁ J₂ hJ₂ t
      (quotientSet_mono p hs (InverseInitialEnergyCallerMass.assigned_quotient_subset
        p (sourceSector p hp hpr S u) J₁ J₂ lists lists ht))
  rw [sourceSector_partition p hp hpr S]
  calc
    _≤∑u:Eisˣ,‖∑x∈sourceSector p hp hpr S u,w x*rowMode p hp hg hpr pool Ψ j
      slots lists a ω₁ ω₂ Z D B v θ H x ρ z‖ := norm_sum_le _ _
    _≤∑_u:Eisˣ,C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := Finset.sum_le_sum fun u _=>hb u
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];norm_num;ring


end InverseInitialEnergyCallerUnits

namespace InverseInitialEnergyCallerRays
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialRayAttachment
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "Eis" => O
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _
open InverseInitialEnergyCallerBranch
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem all_rays_bound (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,lambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (z:JointLogSeparation.Frequency×(Fin 6→ℝ))
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F E:ℝ)(_hE:0≤E)
      (_hmoment:∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ ρ) (j*primaryIdealGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤E ∧
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ ρ) (j*primaryIdealGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤E),
      ‖∑x∈S,∑ρ:SecondRayIndex,w x*rowMode p hp hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*Z^(F+R+π)*E := by
  obtain ⟨C,hC,hbound⟩ := InverseInitialEnergyCallerUnits.all_units_bound N U π hU hπ
  let A : ℝ := ∑ρ:SecondRayIndex,‖secondRayCoefficient ρ‖
  have hA : 0≤A := Finset.sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨C*(1+A),mul_pos hC (by linarith),?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn z w hw labels rows hlabels hneg hchild F E hE hmoment
  have hb (ρ:SecondRayIndex) := hbound p hp hcop hg hinj hpr hc S hdiv pool Ψ hΨ j
    slots hslots lists a ha ω₁ ω₂ Z D B v θ H R hZ hR hn ρ z w hw labels rows
    hlabels hneg hchild F E hE (hmoment ρ)
  rw [Finset.sum_comm]
  calc
    _≤∑ρ:SecondRayIndex,‖∑x∈S,w x*rowMode p hp hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖ := norm_sum_le _ _
    _≤∑ρ:SecondRayIndex,C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := Finset.sum_le_sum fun ρ _=>hb ρ
    _=C*A*Z^(F+R+π)*E := by simp only [←Finset.sum_mul,←Finset.mul_sum,A]
    _≤C*(1+A)*Z^(F+R+π)*E := by gcongr;linarith


end InverseInitialEnergyCallerRays

namespace InverseInitialEnergyCallerIntegral
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialRayAttachment
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "Eis" => O
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _
open InverseInitialEnergyCallerBranch
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem actual_common_integral_bound (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,lambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F A:ℝ)(_hA:0≤A)(J:ℕ)
      (g:Fin 6→𝓢(ℝ,ℂ))(g₁ g₂ b₃:𝓢(ℝ,ℂ))(c₁ c₂ θ₁ θ₂ L:ℝ)
      (_hmoment:∀z:JointLogSeparation.Frequency×(Fin 6→ℝ),∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ ρ) (j*primaryIdealGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2) ∧
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ ρ) (j*primaryIdealGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2)),
      ‖∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
        familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z*
        (∑x∈S,∑ρ:SecondRayIndex,w x*rowMode p hp hg hpr pool Ψ j slots lists a ω₁ ω₂
          Z D B v θ H x ρ z)‖≤
        C*Z^(F+R+π)*A*(∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
          tripleHeight J z.1*coordinateHeight J z.2*‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z‖) := by
  obtain ⟨C,hC,hbound⟩ := InverseInitialEnergyCallerRays.all_rays_bound N U π hU hπ
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn w hw labels rows hlabels hneg hchild F A hA J g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L hmoment
  have hb (z:JointLogSeparation.Frequency×(Fin 6→ℝ)) :=
    hbound p hp hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
      Z D B v θ H R hZ hR hn z w hw labels rows hlabels hneg hchild F
      (A*(tripleHeight J z.1*coordinateHeight J z.2))
      (by unfold tripleHeight coordinateHeight;positivity) (hmoment z)
  calc
    _≤∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
      (C*Z^(F+R+π)*A)*(tripleHeight J z.1*coordinateHeight J z.2*
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z‖) := by
      apply norm_integral_le_of_norm_le
        ((familyDensity_weighted_integrable g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L J).const_mul _)
      filter_upwards with z
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (by ring)
    _=_ := integral_const_mul _ _


end InverseInitialEnergyCallerIntegral

namespace InverseInitialEnergyCallerPhysical
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialRayAttachment
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "Eis" => O
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _
open InverseInitialEnergyCallerBranch
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem actual_physical_block_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (Φ:𝓢(ℝ,ℂ))(V:Fin 6→ℝ→ℂ)(M:Fin 6→ℝ)
    (hV:∀i,ContDiff ℝ ∞ (V i))(hS:∀i,HasCompactSupport (V i))
    (hM:∀i,0≤M i)(hbox:∀i y,V i y≠0→|y|≤M i)
    (J N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,lambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)(_hf:∀x∈S,x.frequency≠0)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R m η:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hη:0≤η*Real.log Z)(c₁ c₂ θ₁ θ₂:ℝ)(_hc₁:0<c₁)(_hc₂:0<c₂)
      (_hsupport:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F A:ℝ)(_hA:0≤A)
      (_hmoment:∀z:JointLogSeparation.Frequency×(Fin 6→ℝ),∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ ρ) (j*primaryIdealGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2) ∧
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ ρ) (j*primaryIdealGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2)),
      ‖physicalBlock p hg (pointSource pool S) (w ∘ erasePoint) Ψ j
        (primeMark slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(prefactorCenter m D B θ+3*η+F+R+π)*A*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) := by
  obtain ⟨Ce,hCe,he⟩ := InverseInitialEnergyCallerIntegral.actual_common_integral_bound N U π hU hπ
  obtain ⟨Cp,hCp,hprofile⟩ := initial_physical_family_common_measure
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox 0 J
  refine ⟨Ce*(Cp+1),mul_pos hCe (by linarith),?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R m η hZ hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F A hA hmoment
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  obtain ⟨b₃,hb₃⟩ := hprofile Z D B v m θ H η hZp hη
  obtain ⟨hid,hint,hprofileBound⟩ := hb₃ c₁ c₂ θ₁ θ₂ hc₁ hc₂
  let g := secondRootSchwartz V hV hS
  let g₁ := CanonicalCubeSeparation.sourceLogProfile W₁ a₀ b₀ ha₀ hs₁ hW₁
  let g₂ := CanonicalCubeSeparation.sourceLogProfile W₂ a₀ b₀ ha₀ hs₂ hW₂
  have hb := he p hp hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn w hw labels rows hlabels hneg hchild F A hA J
    g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) hmoment
  have hprof : (∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
      tripleHeight J z.1*coordinateHeight J z.2*
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z‖)≤
      (Cp+1)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) := by
    simp only [pow_zero,one_mul] at hprofileBound
    exact hprofileBound.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  rw [physicalBlock_rectangular_common_measure p hp hcop hg hpr W₁ W₂ Φ V g g₁ g₂ b₃
    Z D B v m θ H η c₁ c₂ θ₁ θ₂ hid pool S hdiv hf w Ψ j slots lists a ω₁ ω₂ hsupport]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZp _)]
  apply (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hZp.le _)).trans
  calc
    _≤Z^(prefactorCenter m D B θ+3*η)*
      (Ce*Z^(F+R+π)*A*((Cp+1)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J))) := by gcongr
    _=_ := by
      have hexp : Z^(prefactorCenter m D B θ+3*η+F+R+π)=
          Z^(prefactorCenter m D B θ+3*η)*Z^(F+R+π) := by
        rw [show prefactorCenter m D B θ+3*η+F+R+π=
          (prefactorCenter m D B θ+3*η)+(F+R+π) by ring,Real.rpow_add hZp]
      rw [hexp]
      ring


end InverseInitialEnergyCallerPhysical

namespace InverseInitialEnergyCallerClipping
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialClippedColumns InverseInitialProfile InverseInitialOverlapFourier
open InverseInitialRayAttachment MeasureTheory JointLogSeparation
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
local notation "Eis"=>Eisenstein.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

omit [DecidableEq σ] in
include hp in
theorem normalized_energy_clipping
    (pool:Finset ι)(Ψ:Eis→*ℂ)(m:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(labels:Finset (Ideal Eis))(rows:Finset Eis)
    (d:Ideal Eis→ℝ)(w:ℝ→ℂ){Z:ℝ}(hZ:0<Z)(N h F:ℝ) :
    normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows d
      (childLogTest w h) (Z^N) Z F =
    normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows d
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) Z F := by
  unfold normalizedColumnEnergy
  simp_rw [norm_mul, canonical_row_clipping_norm p hg hp pool Ψ m _ _
    slots lists a w hZ N h]

theorem initial_scalar_identity (m D B _v θ η δ π ε:ℝ) :
    prefactorCenter m D B θ+3*η+(D-B+θ+δ)+(B-θ+2*η)+π+
      ((D-B+θ+δ)+ε)=m+5*η+2*δ+π+ε := by
  unfold prefactorCenter
  ring

theorem initial_scalar_le (m D B v θ η δ π ε:ℝ)(hδ:δ≤3*η) :
    prefactorCenter m D B θ+3*η+(D-B+θ+δ)+(B-θ+2*η)+π+
      ((D-B+θ+δ)+ε)≤ m+11*η+π+ε := by
  rw [initial_scalar_identity m D B v θ η δ π ε]
  linarith


end InverseInitialEnergyCallerClipping

namespace InverseSecondFibers

open Eisenstein
open Eisenstein

open InverseInitialFibers (divisor_card_mul_le divisor_card_pos)
open scoped BigOperators Classical
noncomputable section

@[ext] structure OuterTriple where
  q0 : Ideal O
  quotient : Ideal O
  residual : Ideal O

@[ext] structure SecondTuple (Jo Jn : ℕ) where
  outer : OuterTriple
  core : Fin 8 → Ideal O
  commonResidual : Ideal O
  cubeResidual : Ideal O
  secondCube : Ideal O
  extractedCommon : Ideal O
  frequency : O
  oldAssigned : Fin Jo → InverseInitialFibers.PrimeIdeal
  newAssigned : Fin Jn → InverseInitialFibers.PrimeIdeal

structure Valid {Jo Jn : ℕ} (x : SecondTuple Jo Jn)
    (γ : OuterTriple) (f : Ideal O) (k : O) : Prop where
  outer_eq : x.outer = γ
  label : x.core 0 * x.core 1 * x.core 2 * x.commonResidual = f
  j_split : x.core 3 * x.cubeResidual = x.core 0
  b_split : x.core 4 * x.secondCube = γ.q0^2 * x.cubeResidual^2 * x.core 3
  a1 : x.core 5 ∣ (x.core 4 * x.secondCube).radical
  a2 : x.core 6 ∣ (x.core 4 * x.secondCube).radical
  d : x.core 7 ∣ x.core 1 * (x.core 4 * x.secondCube).radical
  extracted_eq : x.core 2 * γ.residual = x.extractedCommon
  generator_d : primaryIdealGenerator (x.core 7) ≠ 0
  generator_d2 : primaryIdealGenerator (x.core 2) ≠ 0
  row_eq : primaryIdealGenerator (x.core 7) * primaryIdealGenerator (x.core 2) * x.frequency = k
  old_dvd : ∀ i, (x.oldAssigned i).val ∣ γ.q0 * f * γ.quotient
  new_dvd : ∀ i, (x.newAssigned i).val ∣ f * γ.residual

lemma poisson_divisor_source (d C R rest B : Ideal O)
    (hR : R * rest = B.radical) (hd : d ∣ C * rest) : d ∣ C * B.radical := by
  apply hd.trans
  rw [← hR]
  exact mul_dvd_mul_left C (dvd_mul_left rest R)

lemma core_dvd_label {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) (i : Fin 4) :
    x.core ⟨i.val, by omega⟩ ∣ f := by
  have hJ : x.core 0 ∣ f := by
    rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  fin_cases i
  · exact hJ
  · rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  · rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  · exact (show x.core 3 ∣ x.core 0 from ⟨x.cubeResidual, hx.j_split.symm⟩).trans hJ

lemma common_label_dvd {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    x.core 1 * x.core 0 ∣ f := by
  refine ⟨x.core 2 * x.commonResidual, ?_⟩
  rw [← hx.label]
  ring

lemma cube_product_dvd_square {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    x.core 4 * x.secondCube ∣ (γ.q0 * x.core 0)^2 := by
  refine ⟨x.core 3, ?_⟩
  rw [hx.b_split, ← hx.j_split]
  ring

lemma cube_radical_dvd {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    (x.core 4 * x.secondCube).radical ∣ γ.q0 * x.core 0 := by
  apply Ideal.dvd_iff_le.mpr
  have hle := Ideal.radical_mono (Ideal.dvd_iff_le.mp (cube_product_dvd_square hx))
  rw [Ideal.radical_pow (γ.q0 * x.core 0) (by decide : (2 : ℕ) ≠ 0)] at hle
  exact Ideal.le_radical.trans hle

lemma cube_factor_dvd_target {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    x.core 4 ∣ (γ.q0 * f)^2 :=
  (dvd_mul_right _ _).trans ((cube_product_dvd_square hx).trans
    (pow_dvd_pow_of_dvd (mul_dvd_mul_left _ (core_dvd_label hx 0)) 2))

lemma core_dvd_outer_label {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) (i : Fin 3) :
    x.core ⟨i.val+5, by omega⟩ ∣ γ.q0 * f := by
  have hrad : (x.core 4 * x.secondCube).radical ∣ γ.q0 * f :=
    (cube_radical_dvd hx).trans (mul_dvd_mul_left _ (core_dvd_label hx 0))
  fin_cases i
  · exact hx.a1.trans hrad
  · exact hx.a2.trans hrad
  · apply hx.d.trans
    apply (mul_dvd_mul_left (x.core 1) (cube_radical_dvd hx)).trans
    convert mul_dvd_mul_left γ.q0 (common_label_dvd hx) using 1
    ring

lemma core_ne_zero {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (i : Fin 8) : x.core i ≠ 0 := by
  have hd : x.core i ∣ (γ.q0*f)^2 := by
    by_cases hi : i.val < 4
    · exact (core_dvd_label hx ⟨i.val, hi⟩).trans
        ((dvd_mul_left _ _).trans (dvd_pow_self _ (by decide : 2 ≠ 0)))
    · by_cases hi4 : i.val = 4
      · have he : i = 4 := Fin.ext hi4
        simpa only [he] using cube_factor_dvd_target hx
      · have he : (⟨(i.val-5)+5, by omega⟩ : Fin 8) = i := by
          apply Fin.ext
          dsimp
          omega
        exact (he ▸ core_dvd_outer_label hx ⟨i.val-5, by omega⟩).trans
          (dvd_pow_self _ (by decide : 2 ≠ 0))
  intro hz
  rw [hz, zero_dvd_iff] at hd
  exact (pow_ne_zero 2 (mul_ne_zero hq hf)) hd

theorem valid_key_injective {Jo Jn : ℕ} (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) {x y : SecondTuple Jo Jn}
    (hx : Valid x γ f k) (hy : Valid y γ f k)
    (hc : x.core = y.core) (ho : x.oldAssigned = y.oldAssigned)
    (hn : x.newAssigned = y.newAssigned) : x = y := by
  have hcore (i : Fin 8) : x.core i = y.core i := congrFun hc i
  have hv : x.commonResidual = y.commonResidual := by
    apply mul_left_cancel₀ (mul_ne_zero
      (mul_ne_zero (core_ne_zero hx hf hq 0) (core_ne_zero hx hf hq 1))
      (core_ne_zero hx hf hq 2))
    exact hx.label.trans (by simpa only [hcore] using hy.label.symm)
  have hj : x.cubeResidual = y.cubeResidual := by
    apply mul_left_cancel₀ (core_ne_zero hx hf hq 3)
    exact hx.j_split.trans (by simpa only [hcore] using hy.j_split.symm)
  have hb : x.secondCube = y.secondCube := by
    apply mul_left_cancel₀ (core_ne_zero hx hf hq 4)
    exact hx.b_split.trans (by simpa only [hcore, hj] using hy.b_split.symm)
  have hg : x.extractedCommon = y.extractedCommon := by
    rw [← hx.extracted_eq, ← hy.extracted_eq, hcore]
  have hr : x.frequency = y.frequency := by
    apply mul_left_cancel₀ (mul_ne_zero hx.generator_d hx.generator_d2)
    exact hx.row_eq.trans (by simpa only [hcore] using hy.row_eq.symm)
  exact SecondTuple.ext (hx.outer_eq.trans hy.outer_eq.symm) hc hv hj hb hg hr ho hn

theorem valid_tuple_card_le {Jo Jn : ℕ} (T : Finset (SecondTuple Jo Jn))
    (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid x γ f k) :
    T.card ≤ (idealDivisors f).card^4 * (idealDivisors ((γ.q0*f)^2)).card *
      (idealDivisors (γ.q0*f)).card^3 *
      (idealDivisors (γ.q0*f*γ.quotient)).card^Jo *
      (idealDivisors (f*γ.residual)).card^Jn := by
  let D := idealDivisors f
  let E := idealDivisors ((γ.q0*f)^2)
  let F := idealDivisors (γ.q0*f)
  let A := idealDivisors (γ.q0*f*γ.quotient)
  let B := idealDivisors (f*γ.residual)
  let Target := (Fin 4 → D) × E × (Fin 3 → F) × (Fin Jo → A) × (Fin Jn → B)
  let encode (x : T) : Target :=
    (fun i => ⟨x.val.core ⟨i.val, by omega⟩,
      (mem_idealDivisors hf).mpr (core_dvd_label (hT x.val x.property) i)⟩,
    ⟨x.val.core 4, (mem_idealDivisors (pow_ne_zero 2 (mul_ne_zero hq hf))).mpr
      (cube_factor_dvd_target (hT x.val x.property))⟩,
    (fun i => ⟨x.val.core ⟨i.val+5, by omega⟩,
      (mem_idealDivisors (mul_ne_zero hq hf)).mpr (core_dvd_outer_label (hT x.val x.property) i)⟩),
    (fun i => ⟨(x.val.oldAssigned i).val,
      (mem_idealDivisors (mul_ne_zero (mul_ne_zero hq hf) ht)).mpr
        ((hT x.val x.property).old_dvd i)⟩),
    (fun i => ⟨(x.val.newAssigned i).val,
      (mem_idealDivisors (mul_ne_zero hf hr)).mpr ((hT x.val x.property).new_dvd i)⟩))
  have hi : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    apply valid_key_injective γ f k hf hq (hT x.val x.property) (hT y.val y.property)
    · funext i
      fin_cases i
      · exact congrArg (fun z : Target => (z.1 0).val) he
      · exact congrArg (fun z : Target => (z.1 1).val) he
      · exact congrArg (fun z : Target => (z.1 2).val) he
      · exact congrArg (fun z : Target => (z.1 3).val) he
      · exact congrArg (fun z : Target => z.2.1.val) he
      · exact congrArg (fun z : Target => (z.2.2.1 0).val) he
      · exact congrArg (fun z : Target => (z.2.2.1 1).val) he
      · exact congrArg (fun z : Target => (z.2.2.1 2).val) he
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : Target => (z.2.2.2.1 i).val) he
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : Target => (z.2.2.2.2 i).val) he
  simpa only [Target, D, E, F, A, B, Fintype.card_coe, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Nat.mul_assoc] using Fintype.card_le_of_injective encode hi

lemma divisor_card_sq_le (I : Ideal O) (hI : I ≠ 0) :
    (idealDivisors (I ^ 2)).card ≤ (idealDivisors I).card^2 := by
  simpa only [pow_two] using divisor_card_mul_le I I hI hI

theorem valid_tuple_card_le_separated {Jo Jn : ℕ} (T : Finset (SecondTuple Jo Jn))
    (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid x γ f k) :
    T.card ≤ (idealDivisors f).card^(9+Jo+Jn) * (idealDivisors γ.q0).card^(5+Jo) *
      (idealDivisors γ.quotient).card^Jo * (idealDivisors γ.residual).card^Jn := by
  let df := (idealDivisors f).card
  let dq := (idealDivisors γ.q0).card
  let dt := (idealDivisors γ.quotient).card
  let dr := (idealDivisors γ.residual).card
  have hqf : (idealDivisors (γ.q0*f)).card ≤ dq*df := divisor_card_mul_le _ _ hq hf
  have hsq : (idealDivisors ((γ.q0*f)^2)).card ≤ (dq*df)^2 :=
    (divisor_card_sq_le _ (mul_ne_zero hq hf)).trans (Nat.pow_le_pow_left hqf 2)
  have hold : (idealDivisors (γ.q0*f*γ.quotient)).card ≤ dq*df*dt :=
    (divisor_card_mul_le _ _ (mul_ne_zero hq hf) ht).trans (Nat.mul_le_mul_right _ hqf)
  have hnew : (idealDivisors (f*γ.residual)).card ≤ df*dr := divisor_card_mul_le _ _ hf hr
  apply (valid_tuple_card_le T γ f k hf hq ht hr hT).trans
  calc
    _ ≤ df^4 * (dq*df)^2 * (dq*df)^3 * (dq*df*dt)^Jo * (df*dr)^Jn := by
      gcongr
    _ = _ := by
      dsimp [df, dq, dt, dr]
      simp only [mul_pow, pow_add]
      ring

theorem valid_tuple_card_le_slot_cap {Jo Jn : ℕ} (T : Finset (SecondTuple Jo Jn))
    (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid x γ f k) (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    T.card ≤ (idealDivisors f).card^(9+4*K) * (idealDivisors γ.q0).card^(5+2*K) *
      (idealDivisors γ.quotient).card^(2*K) * (idealDivisors γ.residual).card^(2*K) := by
  apply (valid_tuple_card_le_separated T γ f k hf hq ht hr hT).trans
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
    (pow_le_pow_right₀ (divisor_card_pos f hf) (by omega))
    (pow_le_pow_right₀ (divisor_card_pos γ.q0 hq) (by omega)))
    (pow_le_pow_right₀ (divisor_card_pos γ.quotient ht) ho))
    (pow_le_pow_right₀ (divisor_card_pos γ.residual hr) hn)

theorem valid_label_squarefree {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k)
    (hJ : Squarefree (x.core 0)) (hC : Squarefree (x.core 1))
    (hg : Squarefree x.extractedCommon) (hv : Squarefree x.commonResidual)
    (hJC : IsCoprime (x.core 0) (x.core 1))
    (hgmask : IsCoprime x.extractedCommon (x.core 1 * x.core 0))
    (hvmask : IsCoprime x.commonResidual (x.extractedCommon * x.core 1 * x.core 0)) :
    Squarefree f := by
  have hdg : x.core 2 ∣ x.extractedCommon := ⟨γ.residual, hx.extracted_eq.symm⟩
  have hdJC : IsCoprime (x.core 2) (x.core 0 * x.core 1) := by
    simpa only [mul_comm] using hgmask.of_isCoprime_of_dvd_left hdg
  have hdiv : (x.core 0 * x.core 1) * x.core 2 ∣
      x.extractedCommon * x.core 1 * x.core 0 := by
    convert mul_dvd_mul_left (x.core 0 * x.core 1) hdg using 1
    ring
  have hvJCd := hvmask.of_isCoprime_of_dvd_right hdiv
  rw [← hx.label]
  exact squarefree_mul_iff.mpr ⟨hvJCd.symm.isRelPrime,
    squarefree_mul_iff.mpr ⟨hdJC.symm.isRelPrime,
      squarefree_mul_iff.mpr ⟨hJC.isRelPrime, hJ, hC⟩,
      hg.squarefree_of_dvd hdg⟩, hv⟩

theorem cube_quotient_norm_sq_le {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) :
    Ideal.absNorm γ.q0 ^ 2 ≤ Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube := by
  have hj0 : x.cubeResidual ≠ 0 := by
    intro hz
    have he := hx.j_split
    rw [hz, mul_zero] at he
    exact core_ne_zero hx hf hq 0 he.symm
  have hp0 : x.core 4 * x.secondCube ≠ 0 := by
    rw [hx.b_split]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hq) (pow_ne_zero 2 hj0))
      (core_ne_zero hx hf hq 3)
  have hdiv : γ.q0^2 ∣ x.core 4 * x.secondCube := by
    rw [hx.b_split]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hn := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun hz => hp0 (Ideal.absNorm_eq_zero_iff.mp hz)))
    (map_dvd Ideal.absNorm hdiv)
  simpa only [map_pow, map_mul] using hn

theorem cube_quotient_norm_le {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (N : ℕ)
    (hpair : Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube ≤ N^2) :
    Ideal.absNorm γ.q0 ≤ N := by
  have hh := (cube_quotient_norm_sq_le hx hf hq).trans hpair
  nlinarith

def originalSource {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) : Finset (SecondTuple Jo Jn) :=
  source.filter fun x => (∀ i, x.oldAssigned i ∈ oldLists i) ∧
    (∀ i, x.newAssigned i ∈ newLists i) ∧ keep x

def sourceTriples {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) : Finset OuterTriple :=
  (originalSource source oldLists newLists keep).image SecondTuple.outer

theorem mem_sourceTriples {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) :
    γ ∈ sourceTriples source oldLists newLists keep ↔
      ∃ x ∈ source, (∀ i, x.oldAssigned i ∈ oldLists i) ∧
        (∀ i, x.newAssigned i ∈ newLists i) ∧ keep x ∧ x.outer = γ := by
  simp only [sourceTriples, originalSource, Finset.mem_image, Finset.mem_filter]
  aesop

theorem sourceTriples_property {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (P : OuterTriple → Prop)
    (hP : ∀ x ∈ originalSource source oldLists newLists keep, P x.outer)
    (γ : OuterTriple) (hγ : γ ∈ sourceTriples source oldLists newLists keep) : P γ := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hγ
  exact hP x hx

theorem sourceTriples_cube_norm_le {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (N : ℕ)
    (hsrc : ∀ x ∈ originalSource source oldLists newLists keep,
      ∃ f k, Valid x x.outer f k ∧ f ≠ 0 ∧ x.outer.q0 ≠ 0 ∧
        Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube ≤ N^2)
    (γ : OuterTriple) (hγ : γ ∈ sourceTriples source oldLists newLists keep) :
    Ideal.absNorm γ.q0 ≤ N := by
  apply sourceTriples_property source oldLists newLists keep
    (fun γ => Ideal.absNorm γ.q0 ≤ N) ?_ γ hγ
  intro x hx
  obtain ⟨f, k, hv, hf, hq, hpair⟩ := hsrc x hx
  exact cube_quotient_norm_le hv hf hq N hpair

def secondFiber {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O) :
    Finset (SecondTuple Jo Jn) :=
  (originalSource source oldLists newLists keep).filter (fun x => Valid x γ f k)

theorem secondFiber_outer_mem {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O)
    (x : SecondTuple Jo Jn) (hx : x ∈ secondFiber source oldLists newLists keep γ f k) :
    γ ∈ sourceTriples source oldLists newLists keep := by
  obtain ⟨hsrc, hv⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_image.mpr ⟨x, hsrc, hv.outer_eq⟩

theorem secondFiber_empty_of_not_sourceTriple {Jo Jn : ℕ}
    (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O)
    (hγ : γ ∉ sourceTriples source oldLists newLists keep) :
    secondFiber source oldLists newLists keep γ f k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hγ (secondFiber_outer_mem source oldLists newLists keep γ f k x hx)

theorem secondFiber_card_le {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    (secondFiber source oldLists newLists keep γ f k).card ≤
      (idealDivisors f).card^(9+4*K) * (idealDivisors γ.q0).card^(5+2*K) *
      (idealDivisors γ.quotient).card^(2*K) * (idealDivisors γ.residual).card^(2*K) :=
  valid_tuple_card_le_slot_cap _ γ f k hf hq ht hr
    (fun _x hx => (Finset.mem_filter.mp hx).2) K ho hn

theorem secondFiber_weight_bound {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset InverseInitialFibers.PrimeIdeal)
    (newLists : Fin Jn → Finset InverseInitialFibers.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x ∈ secondFiber source oldLists newLists keep γ f k, ‖w x‖ ≤ C) :
    (∑ x ∈ secondFiber source oldLists newLists keep γ f k, ‖w x‖) ≤
      C * ((idealDivisors f).card : ℝ)^(9+4*K) *
        ((idealDivisors γ.q0).card : ℝ)^(5+2*K) *
        ((idealDivisors γ.quotient).card : ℝ)^(2*K) *
        ((idealDivisors γ.residual).card : ℝ)^(2*K) := by
  calc
    _ ≤ ∑ _x ∈ secondFiber source oldLists newLists keep γ f k, C := Finset.sum_le_sum hw
    _ = ((secondFiber source oldLists newLists keep γ f k).card : ℝ) * C := by simp
    _ ≤ ((idealDivisors f).card^(9+4*K) * (idealDivisors γ.q0).card^(5+2*K) *
        (idealDivisors γ.quotient).card^(2*K) * (idealDivisors γ.residual).card^(2*K) : ℕ) * C :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast (secondFiber_card_le source oldLists newLists keep γ f k hf hq ht hr K ho hn)) hC
    _ = _ := by push_cast; ring

end
end InverseSecondFibers

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
