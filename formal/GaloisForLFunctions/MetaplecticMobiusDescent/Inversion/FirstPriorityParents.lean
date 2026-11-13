/-
First priority parents adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.FirstGlobalRetainedSource

/-!
# First priority parents

Priority parent attachment `InverseFirstPriorityParents` with valid sources and extracted
support; marked radial principal energies `InversePrincipalEnergy` and uniform row control.
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
open scoped BigOperators Classical SchwartzMap ContDiff

namespace InverseSecondChildWindows
open InverseMoment InverseSecondProfileUniform
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open Eisenstein SchwartzPlanePoisson
open InverseInitialRayAttachment
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem positive_cutoff (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ w : 𝓢(ℝ,ℂ), HasCompactSupport (w : ℝ → ℂ) ∧
      (∀ x ∈ Set.Icc a b,w x = 1) ∧ tsupport (w : ℝ → ℂ) ⊆ Set.Icc (a/2) (b+1) := by
  let c := (a+b)/2
  let r := (b-a)/2
  let δ := min (a/2) 1
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hδ : 0 < δ := lt_min (half_pos ha) zero_lt_one
  have hδa : δ ≤ a/2 := min_le_left _ _
  have hδb : δ ≤ 1 := min_le_right _ _
  let bump : ContDiffBump c := ⟨r+δ/2,r+δ,by linarith,by linarith⟩
  let v : ℝ → ℂ := fun x => (bump x : ℂ)
  have hv : ContDiff ℝ ∞ v := Complex.ofRealCLM.contDiff.comp bump.contDiff
  have hvs : Function.support v ⊆ Set.Icc (a/2) (b+1) := by
    intro x hx
    have hb : x ∈ Function.support bump := by
      intro hz
      exact hx (by simp only [v,hz,Complex.ofReal_zero])
    rw [bump.support_eq] at hb
    have hd : |x-c| < r+δ := by simpa only [Metric.mem_ball,Real.dist_eq] using hb
    obtain ⟨hl,hu⟩ := abs_lt.mp hd
    dsimp [c,r] at hl hu
    constructor <;> linarith
  have hvc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hvs
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,closure_minimal hvs isClosed_Icc⟩
  intro x hx
  have hb : x ∈ Metric.closedBall c bump.rIn := by
    change dist x c ≤ r+δ/2
    rw [Real.dist_eq,abs_le]
    dsimp [c,r]
    constructor <;> linarith [hx.1,hx.2]
  change (bump x : ℂ) = 1
  simp only [bump.one_of_mem_closedBall hb,Complex.ofReal_one]

theorem positiveSource_log_bound (g : 𝓢(ℝ,ℂ)) (m bcap c θ x : ℝ)
    (_hm : 0≤ m) (hs : Function.support g⊆Set.Icc (-m) m)
    (hc : 1≤ c) (hcb : c≤ bcap) (_hx : 0<x)
    (hn : positiveSource g c θ x≠0) : |Real.log x|≤ m+Real.log bcap := by
  have hc0 : 0<c := zero_lt_one.trans_le hc
  have hgn : g (Real.log x+Real.log c)≠0 := (mul_ne_zero_iff.mp hn).2
  have hh := hs hgn
  have hcl : 0≤ Real.log c := Real.log_nonneg hc
  have hclb : Real.log c≤ Real.log bcap := Real.log_le_log hc0 hcb
  rw [abs_le]
  constructor <;> linarith [hh.1,hh.2]

theorem positiveSource_ratio_support (g : 𝓢(ℝ,ℂ)) (m bcap c θ x : ℝ)
    (hm : 0≤ m) (hs : Function.support g⊆Set.Icc (-m) m)
    (hc : 1≤ c) (hcb : c≤ bcap) (hx : 0<x)
    (hn : positiveSource g c θ x≠0) :
    x∈Set.Icc (Real.exp (-(m+Real.log bcap))) (Real.exp (m+Real.log bcap)) := by
  have hh := (abs_le.mp (positiveSource_log_bound g m bcap c θ x hm hs hc hcb hx hn))
  exact ⟨(Real.le_log_iff_exp_le hx).mp hh.1,(Real.log_le_iff_le_exp hx).mp hh.2⟩

theorem translated_log_bound (a b x ρ B : ℝ) (ha : 0<a)
    (hx : x∈Set.Icc a b) (hρ : |ρ|≤ B) :
    |Real.log x+ρ|≤|Real.log a|+|Real.log b|+B := by
  have hx0 := ha.trans_le hx.1
  have hlo := Real.log_le_log ha hx.1
  have hhi := Real.log_le_log hx0 hx.2
  have hl : |Real.log x|≤|Real.log a|+|Real.log b| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
    · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]
  exact (abs_add_le _ _).trans (add_le_add hl hρ)

def outerIndex (i : Fin 4) : Fin 6 := i.castLE (by decide)

theorem fixed_windows (m bcap : ℝ) (lo hi : Fin 4→ℝ) (Bρ : Fin 6→ℝ)
    (hm : 0≤ m) (_hcap : 1≤ bcap) (hlo : ∀ i,0<lo i)
    (hhi : ∀ i,lo i≤ hi i) (hBρ : ∀ i,0≤ Bρ i) :
    ∃ (w : 𝓢(ℝ,ℂ)) (U : Fin 6→𝓢(ℝ,ℂ)) (M : Fin 6→ℝ) (a b : ℝ),
      0<a ∧ a≤ b ∧ HasCompactSupport (w : ℝ→ℂ) ∧
      tsupport (w : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀ i,0≤ M i) ∧ (∀ i,HasCompactSupport (U i : ℝ→ℂ)) ∧
      (∀ i,Function.support (U i)⊆Set.Icc (-M i) (M i)) ∧
      (∀ (g : 𝓢(ℝ,ℂ)),Function.support g⊆Set.Icc (-m) m →
        ∀ (c θ u v n : ℝ),1≤ c → c≤ bcap →
        u∈Set.Icc (lo 0) (hi 0) → v∈Set.Icc (lo 2) (hi 2) → 0<n →
        positiveSource g c θ (u*v*n)≠0 → w n=1) ∧
      (∀ (q : Fin 6→ℝ) (ρ : Fin 6→ℝ),
        (∀ i,|ρ i|≤ Bρ i) →
        (∀ i : Fin 4,q (outerIndex i)∈Set.Icc (lo i) (hi i)) →
        w (q 4)≠0 → w (q 5)≠0 → ∀ i,U i (Real.log (q i)+ρ i)=1) := by
  let R := m+Real.log bcap
  let a := Real.exp (-R)/(hi 0*hi 2)
  let b := Real.exp R/(lo 0*lo 2)
  have hhi0 (i : Fin 4) : 0<hi i := (hlo i).trans_le (hhi i)
  have ha : 0<a := div_pos (Real.exp_pos _) (mul_pos (hhi0 0) (hhi0 2))
  have hb : 0<b := div_pos (Real.exp_pos _) (mul_pos (hlo 0) (hlo 2))
  obtain ⟨w,hwc,hwone,hws⟩ := positive_cutoff a (a+b+1) ha (by linarith)
  let l : Fin 6→ℝ := ![lo 0,lo 1,lo 2,lo 3,a/2,a/2]
  let u : Fin 6→ℝ := ![hi 0,hi 1,hi 2,hi 3,(a+b+1)+1,(a+b+1)+1]
  have hl (i : Fin 6) : 0<l i := by
    fin_cases i
    · exact hlo 0
    · exact hlo 1
    · exact hlo 2
    · exact hlo 3
    · exact half_pos ha
    · exact half_pos ha
  let H (i : Fin 6) := |Real.log (l i)|+|Real.log (u i)|+Bρ i
  have hH (i : Fin 6) : 0≤ H i := add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hBρ i)
  choose V hVc hVs hVone hVsupport hVzero using
    fun i : Fin 6 => JointLogSeparation.exists_complex_smooth_cutoff (H i) (hH i)
  let U (i : Fin 6) : 𝓢(ℝ,ℂ) := (hVc i).toSchwartzMap (hVs i)
  refine ⟨w,U,(fun i=>H i+1),a/2,(a+b+1)+1,half_pos ha,by linarith,hwc,hws,
    (fun i=>by linarith [hH i]),hVc,(fun i=>(subset_tsupport _).trans (hVsupport i)),?_,?_⟩
  · intro g hg c θ u v n hc hcb hu hv hn hnz
    have hu0 := (hlo 0).trans_le hu.1
    have hv0 := (hlo 2).trans_le hv.1
    have hs := positiveSource_ratio_support g m bcap c θ (u*v*n) hm hg hc hcb
      (mul_pos (mul_pos hu0 hv0) hn) hnz
    have hnlo : a≤ n := by
      apply (div_le_iff₀ (mul_pos (hhi0 0) (hhi0 2))).mpr
      calc
        _ ≤ u*v*n := hs.1
        _ ≤ (hi 0*hi 2)*n := mul_le_mul_of_nonneg_right
          (mul_le_mul hu.2 hv.2 hv0.le (hhi0 0).le) hn.le
        _ = _ := by ring
    have hnhi : n≤ b := by
      apply (le_div_iff₀ (mul_pos (hlo 0) (hlo 2))).mpr
      calc
        _ = (lo 0*lo 2)*n := by ring
        _ ≤ u*v*n := mul_le_mul_of_nonneg_right
          (mul_le_mul hu.1 hv.1 (hlo 2).le hu0.le) hn.le
        _ ≤ _ := hs.2
    exact hwone n ⟨hnlo,by linarith⟩
  · intro q ρ hρ hblock hleft hright i
    have hq (k : Fin 6) : q k∈Set.Icc (l k) (u k) := by
      fin_cases k
      · exact hblock 0
      · exact hblock 1
      · exact hblock 2
      · exact hblock 3
      · exact hws (subset_tsupport _ hleft)
      · exact hws (subset_tsupport _ hright)
    exact hVone i _ (translated_log_bound (l i) (u i) (q i) (ρ i) (Bρ i) (hl i) (hq i) (hρ i))

def actualOuterRatios {ι : Type*} [DecidableEq ι] (p : ι→O)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (G E V B : ℝ) : Fin 4→ℝ :=
  ![primeProductNorm p x.second.sourceCommon/G,
    ‖ringComplex ((∏ i ∈ x.second.divisor,p i))‖^2/E,
    primeProductNorm p x.second.overlap/V,‖ringComplex x.second.frequency‖^2/B]

lemma actualRelativeNorm_outer {ι : Type*} [DecidableEq ι] (p : ι→O)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex)
    (Q₁ Q₂ : Finset ι) (G E V B X : ℝ) (i : Fin 4) :
    secondRelativeNorm (secondActualNorms p (secondInheritedProfile p x Ψ m z) Q₁ Q₂)
      G E V B X (outerIndex i)=actualOuterRatios p x G E V B i := by
  fin_cases i <;> rfl

theorem actual_second_child_windows (g₁ g₂ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 4→ℝ) (Bρ : Fin 6→ℝ)
    (hm₁ : 0≤ m₁) (_hm₂ : 0≤ m₂) (hcap : 1≤ bcap)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂)
    (hlo : ∀ i,0<lo i) (hhi : ∀ i,lo i≤ hi i) (hBρ : ∀ i,0≤ Bρ i) :
    ∃ (w₁ w₂ : 𝓢(ℝ,ℂ)) (U₀ : Fin 6→𝓢(ℝ,ℂ)) (M₀ : Fin 6→ℝ) (a b : ℝ),
      0<a ∧ a≤ b ∧ HasCompactSupport (w₁ : ℝ→ℂ) ∧ HasCompactSupport (w₂ : ℝ→ℂ) ∧
      tsupport (w₁ : ℝ→ℂ)⊆Set.Icc a b ∧ tsupport (w₂ : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀ i,0≤ M₀ i) ∧ (∀ i,HasCompactSupport (U₀ i : ℝ→ℂ)) ∧
      (∀ i,Function.support (U₀ i)⊆Set.Icc (-M₀ i) (M₀ i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (_hp : ∀ i,p i≠0)
      [∀ i,(Ideal.span {p i}).IsMaximal]
      {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (pool : Finset ι)
      (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex) (G E V B X : ℝ)
      (ρ : Fin 6→ℝ) (c₁ c₂ θ₁ θ₂ : ℝ),
      0<G → 0<E → 0<V → 0<B → 0<X →
      (∀ i,|ρ i|≤ Bρ i) → 1≤ c₁ → c₁≤ bcap → 1≤ c₂ → c₂≤ bcap →
      (∀ x∈source,∀ i,actualOuterRatios p x G E V B i∈Set.Icc (lo i) (hi i)) →
      (∀ x∈source,∀ Q∈(pool\x.second.overlap).powerset,
        star (positiveSource g₁ c₁ θ₁
          (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*primeProductNorm p Q/(G*V*X)))≠0 →
        w₁ (primeProductNorm p Q/X)=1) ∧
      (∀ x∈source,∀ Q∈(pool\x.second.overlap).powerset,
        positiveSource g₂ c₂ θ₂
          (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*primeProductNorm p Q/(G*V*X))≠0 →
        w₂ (primeProductNorm p Q/X)=1) ∧
      (∀ j∈secondProfileIndices source pool (fun x=>secondInheritedProfile p x Ψ m z),
        w₁ (primeProductNorm p j.2.1/X)≠0 → w₂ (primeProductNorm p j.2.2/X)≠0 → ∀ i,
        U₀ i (secondRelativeLog
          (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2) G E V B X i+ρ i)=1) := by
  let mmax := max m₁ m₂
  have hmmax : 0≤ mmax := hm₁.trans (le_max_left _ _)
  have hg₁' : Function.support g₁⊆Set.Icc (-mmax) mmax := by
    intro x hx
    have h := hg₁ hx
    exact ⟨(neg_le_neg (le_max_left _ _)).trans h.1,h.2.trans (le_max_left _ _)⟩
  have hg₂' : Function.support g₂⊆Set.Icc (-mmax) mmax := by
    intro x hx
    have h := hg₂ hx
    exact ⟨(neg_le_neg (le_max_right _ _)).trans h.1,h.2.trans (le_max_right _ _)⟩
  obtain ⟨w,U,M,a,b,ha,hab,hwc,hws,hM,hUc,hUs,hfresh,hcut⟩ :=
    fixed_windows mmax bcap lo hi Bρ hmmax hcap hlo hhi hBρ
  refine ⟨w,w,U,M,a,b,ha,hab,hwc,hwc,hws,hws,hM,hUc,hUs,?_⟩
  intro ι _ p hp _ Jo Jn source pool Ψ m z G E V B X ρ c₁ c₂ θ₁ θ₂ hG hE hV hB hX hρ hc₁ hcb₁ hc₂ hcb₂ hblock
  have he (x : MarkedSecondSource ι Jo Jn) (Q : Finset ι) :
      (primeProductNorm p x.second.sourceCommon/G)*(primeProductNorm p x.second.overlap/V)*(primeProductNorm p Q/X)=
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*primeProductNorm p Q/(G*V*X) := by
    field_simp
  refine ⟨?_,?_,?_⟩
  · intro x hx Q _ hn
    apply hfresh g₁ hg₁' c₁ θ₁ _ _ _ hc₁ hcb₁ (hblock x hx 0) (hblock x hx 2)
      (div_pos (primeProductNorm_pos p hp Q) hX)
    change positiveSource g₁ c₁ θ₁ ((primeProductNorm p x.second.sourceCommon/G)*
      (primeProductNorm p x.second.overlap/V)*(primeProductNorm p Q/X))≠0
    rw [he]
    exact star_ne_zero.mp hn
  · intro x hx Q _ hn
    apply hfresh g₂ hg₂' c₂ θ₂ _ _ _ hc₂ hcb₂ (hblock x hx 0) (hblock x hx 2)
      (div_pos (primeProductNorm_pos p hp Q) hX)
    change positiveSource g₂ c₂ θ₂ ((primeProductNorm p x.second.sourceCommon/G)*
      (primeProductNorm p x.second.overlap/V)*(primeProductNorm p Q/X))≠0
    rw [he]
    exact hn
  · intro j hj hleft hright i
    apply hcut (secondRelativeNorm
      (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2) G E V B X) ρ hρ
      (fun k=>?_) hleft hright i
    rw [actualRelativeNorm_outer]
    exact hblock j.1 ((mem_secondProfileIndices source pool _ j).mp hj).1 k

end InverseSecondChildWindows

end

noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap

namespace InverseFirstPriorityParents
open Eisenstein SecondPassArithmetic FirstPassCubeLabels
open InverseMoment InverseInitialArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O

@[ext] structure Source (ι : Type*) (Jo : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  quotientSupport : Finset ι
  oldAssigned : Fin Jo → InverseInitialFibers.PrimeIdeal

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

def extractedSupport (negative : Bool) (x : Source ι Jo) : Finset ι :=
  ((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪x.quotientSupport

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def parent (x : Source ι Jo) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := sourceIdeal p x.quotientSupport
  oldAssigned := x.oldAssigned

theorem parent_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (parent p (Jo:=Jo)) := by
  intro x y h
  apply Source.ext
  · exact congrArg SecondParentSource.cube h
  · exact congrArg SecondParentSource.firstCommon h
  · exact congrArg SecondParentSource.firstDivisor h
  · exact sourceIdeal_injective p hinj (congrArg SecondParentSource.quotient h)
  · exact congrArg SecondParentSource.oldAssigned h

def appendParent {Jn : ℕ} (x : SecondParentSource ι Jo)
    (q : Fin Jn→InverseInitialFibers.PrimeIdeal) : SecondParentSource ι (Jo+Jn) where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := Fin.addCases x.oldAssigned q

def forgetAppended {Jn : ℕ} (x : SecondParentSource ι (Jo+Jn)) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := fun i=>x.oldAssigned (Fin.castAdd Jn i)

omit [DecidableEq ι] in
@[simp] theorem forget_append {Jn : ℕ} (x : SecondParentSource ι Jo)
    (q : Fin Jn→InverseInitialFibers.PrimeIdeal) : forgetAppended (appendParent x q)=x := by
  apply SecondParentSource.ext <;> try rfl
  funext i
  simp only [forgetAppended,appendParent,Fin.addCases_left]

omit [DecidableEq ι] in
theorem appendParent_injective {Jn : ℕ} :
    Function.Injective (fun q : SecondParentSource ι Jo × (Fin Jn→InverseInitialFibers.PrimeIdeal)=>
      appendParent q.1 q.2) := by
  intro q r h
  apply Prod.ext
  · simpa only [forget_append] using congrArg forgetAppended h
  · funext i
    simpa only [appendParent,Fin.addCases_right] using
      congrArg (fun x : SecondParentSource ι (Jo+Jn)=>x.oldAssigned (Fin.natAdd Jo i)) h

def attach (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) : SecondParentSource ι (Jo+(J.card+J.card)) :=
  appendParent (parent p q.1) (fun i=>sourcePrime p (pairedSlotAssignment J J q.2 i))

omit [DecidableEq σ] in
theorem attach_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) (J : Finset σ) :
    Function.Injective (attach p (Jo:=Jo) J) := by
  intro q r h
  have he := @appendParent_injective ι Jo (J.card+J.card)
    (parent p q.1,fun i=>sourcePrime p (pairedSlotAssignment J J q.2 i))
    (parent p r.1,fun i=>sourcePrime p (pairedSlotAssignment J J r.2 i)) h
  apply Prod.ext
  · exact parent_injective p hinj (congrArg Prod.fst he)
  · apply pairedSlotAssignment_injective J J
    funext i
    exact hinj (congrArg (fun q : SecondParentSource ι Jo ×
      (Fin (J.card+J.card)→InverseInitialFibers.PrimeIdeal)=>(q.2 i).val) he)

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem forget_attach (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    forgetAppended (attach p J q)=parent p q.1 := forget_append _ _

def assignmentSource (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) :
    Finset (Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :=
  (source ×ˢ ((J.pi lists)×ˢ(J.pi lists))).filter
    (fun q=>∀ i,pairedSlotAssignment J J q.2 i∈extractedSupport negative q.1)

def assignedParents (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) : Finset (SecondParentSource ι (Jo+(J.card+J.card))) :=
  (assignmentSource source negative J lists).image (attach p J)

theorem sum_assignmentSource {A : Type*} [AddCommMonoid A]
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (H : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))→A) :
    ∑ q∈assignmentSource source negative J lists,H q =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),H (x,q) := by
  rw [assignmentSource,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem sum_assignedParents (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {A : Type*} [AddCommMonoid A] (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (H : SecondParentSource ι (Jo+(J.card+J.card))→A) :
    ∑ y∈assignedParents p source negative J lists,H y =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),H (attach p J (x,q)) := by
  rw [assignedParents,Finset.sum_image (fun _ _ _ _ h=>attach_injective p hinj J h)]
  exact sum_assignmentSource source negative J lists _

def coefficient (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) :
    SecondParentSource ι (Jo+(J.card+J.card))→ℂ :=
  Function.extend (attach p J) (fun q=>w q.1*pairedSlotWeight J J a a q.2) (fun _=>0)

omit [DecidableEq σ] in
theorem coefficient_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    coefficient p J a w (attach p J q)=w q.1*pairedSlotWeight J J a a q.2 :=
  (attach_injective p hinj J).extend_apply _ _ _

theorem paired_parent_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(star (primeMark J lists a (extractedSupport negative x))*
      primeMark J lists a (extractedSupport negative x))*H (parent p x)) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  rw [sum_assignedParents p hinj]
  apply Finset.sum_congr rfl
  intro x hx
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul,coefficient_attach p hinj,forget_attach]

theorem paired_parent_sq_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (extractedSupport negative x)‖^2 : ℝ)*H (parent p x)) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  simpa only [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,starRingEnd_apply] using
    paired_parent_sum p hinj source negative J lists a w H

lemma mem_assignmentSource (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (q : (∀ i∈J,ι)×(∀ i∈J,ι)) :
    (x,q)∈assignmentSource source negative J lists ↔ x∈source ∧
      q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)) := by
  rw [←paired_assignment_filter]
  simp only [assignmentSource,Finset.mem_filter,Finset.mem_product]
  tauto

theorem mem_assignedParents (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    y∈assignedParents p source negative J lists ↔
      ∃ x∈source,∃ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),attach p J (x,q)=y := by
  simp only [assignedParents,Finset.mem_image]
  constructor
  · rintro ⟨⟨x,q⟩,hq,he⟩
    exact ⟨x,(mem_assignmentSource source negative J lists x q).mp hq |>.1,
      q,(mem_assignmentSource source negative J lists x q).mp hq |>.2,he⟩
  · rintro ⟨x,hx,q,hq,he⟩
    exact ⟨(x,q),(mem_assignmentSource source negative J lists x q).mpr ⟨hx,hq⟩,he⟩

structure SourceValid (x : Source ι Jo) : Prop where
  admissible : x.cube.Admissible
  common_disjoint : Disjoint x.firstCommon x.cube.support
  first_divisor : x.firstDivisor⊆x.firstCommon∪x.cube.support
  old_support : ∀ i,(x.oldAssigned i).val∣
    sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*sourceIdeal p x.quotientSupport

theorem extracted_prime_dvd (x : Source ι Jo) (hx : x.cube.Admissible)
    (negative : Bool) (i : ι) (hi : i∈extractedSupport negative x) :
    (sourcePrime p i).val∣sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*
      sourceIdeal p x.quotientSupport := by
  obtain hi|hi := Finset.mem_union.mp hi
  · obtain hi|hi := Finset.mem_union.mp hi
    · have hb : i∈x.cube.support := by
        cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hi
        · exact hx.1 hi
        · exact hx.2 hi
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (source_prime_dvd p _ i hb) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _) _
  · exact dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _

theorem attach_old_support (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (hx : SourceValid p x)
    (q : (∀ i∈J,ι)×(∀ i∈J,ι))
    (hq : q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
      (J.pi (fun i=>lists i∩extractedSupport negative x))) :
    ∀ i,((attach p J (x,q)).oldAssigned i).val∣
      sourceIdeal p (attach p J (x,q)).cube.support*
        sourceIdeal p (attach p J (x,q)).firstCommon*(attach p J (x,q)).quotient := by
  have hh : ∀ i,pairedSlotAssignment J J q i∈extractedSupport negative x := by
    have hf : q∈((J.pi lists)×ˢ(J.pi lists)).filter
        (fun q=>∀ i,pairedSlotAssignment J J q i∈extractedSupport negative x) := by
      rwa [paired_assignment_filter]
    exact (Finset.mem_filter.mp hf).2
  intro i
  refine Fin.addCases (fun k=>?_) (fun k=>?_) i
  · simpa only [attach,appendParent,parent,Fin.addCases_left] using hx.old_support k
  · simpa only [attach,appendParent,parent,Fin.addCases_right] using
      extracted_prime_dvd p x hx.admissible negative _ (hh k)

omit [DecidableEq σ] in

theorem attach_physical_data (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) (m : O) :
    secondParentLabel p (attach p J q)=secondParentLabel p (parent p q.1) ∧
    secondParentDivisor p (attach p J q)=secondParentDivisor p (parent p q.1) ∧
    secondParentPuncture p m (attach p J q)=secondParentPuncture p m (parent p q.1) :=
  ⟨rfl,rfl,rfl⟩

theorem coefficient_norm (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (B : ℝ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1) (hw : ∀ x∈source,‖w x‖≤ B)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈assignedParents p source negative J lists) : ‖coefficient p J a w y‖≤ B := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
  rw [coefficient_attach p hinj,norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pairedSlotWeight_norm_le_one J J lists lists a a
    _ q hq ha ha)).trans (hw x hx)

theorem assigned_family_conditions (hp : ∀ i,p i≠0)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (Jo+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀ y∈assignedParents p source negative J lists,∀ x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p (attachedSecondFamily (assignedParents p source negative J lists) expansion) := by
  apply attached_family_conditions p _ _
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).admissible
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).common_disjoint
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).first_divisor
  · exact hE
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact attach_old_support p negative J lists x (hs x hx) q hq
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact sourceIdeal_ne_zero p hp x.quotientSupport

def fixedPoint (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→InverseInitialFibers.PrimeIdeal) (D : Finset ι) : Source ι Jo :=
  ⟨b,C,E,D,old⟩

def fixedSource (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→InverseInitialFibers.PrimeIdeal) : Finset (Source ι Jo) :=
  F.powerset.image (fixedPoint b C E old)

omit [DecidableEq ι] in
theorem fixedPoint_injective (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→InverseInitialFibers.PrimeIdeal) : Function.Injective (fixedPoint b C E old) := by
  intro D D' h
  exact congrArg Source.quotientSupport h

def parentFunction (H : Source ι Jo→ℂ) : SecondParentSource ι Jo→ℂ :=
  Function.extend (parent p) H (fun _=>0)

theorem parentFunction_parent (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (H : Source ι Jo→ℂ) (x : Source ι Jo) : parentFunction p H (parent p x)=H x :=
  (parent_injective p hinj).extend_apply _ _ _

theorem paired_source_sq_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w H : Source ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (extractedSupport negative x)‖^2 : ℝ)*H x) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*parentFunction p H (forgetAppended y) := by
  simpa only [parentFunction_parent p hinj] using
    paired_parent_sq_sum p hinj source negative J lists a w (parentFunction p H)

theorem fixed_priority_complex (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→InverseInitialFibers.PrimeIdeal) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w H : Finset ι→ℂ) :
    (∑ D∈F.powerset,w D*(‖primeMark J lists a
      (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2 : ℝ)*H D) =
    ∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>w x.quotientSupport) y *
        parentFunction p (fun x=>H x.quotientSupport) (forgetAppended y) := by
  have he := paired_source_sq_sum p hinj (fixedSource F b C E old) negative J lists a
    (fun x=>w x.quotientSupport) (fun x=>H x.quotientSupport)
  rw [fixedSource,Finset.sum_image (fun _ _ _ _ h=>fixedPoint_injective b C E old h)] at he
  simpa only [fixedPoint,extractedSupport,fixedSource] using he

theorem fixed_priority_slice (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→InverseInitialFibers.PrimeIdeal) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : Finset ι→ℝ) :
    (∑ D∈F.powerset,w D*‖primeMark J lists a
      (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2) =
    (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>(w x.quotientSupport:ℂ)) y).re := by
  have he := paired_parent_sq_sum p hinj (fixedSource F b C E old) negative J lists a
    (fun x=>(w x.quotientSupport:ℂ)) (fun _=>1)
  simp only [mul_one] at he
  rw [fixedSource,Finset.sum_image (fun _ _ _ _ h=>fixedPoint_injective b C E old h)] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    fixedPoint,extractedSupport,fixedSource] using hr

variable (hp : ∀ i,p i≠0) (hg : ∀ i,lambda∉Ideal.span {p i})

def priorityOuter (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter)
    (core : FirstCoreIndex) (D : Finset ι) : ℝ :=
  (‖InverseFirstRayAttachment.crossCoeff r.1 r.2‖*‖selector D‖) *
    ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit negative Ψ m D core‖

def priorityPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (omega : ℝ→ℂ) (X t Y : ℝ)
    (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter)
    (core : FirstCoreIndex) (D : Finset ι) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj F D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (fun U=>primeMark (slots\J)
      (fun i=>lists i\(((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)) a U)
    omega X (∏i∈C,p i) d core t Y

theorem first_priority_physical_slice (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→InverseInitialFibers.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (omega : ℝ→ℂ) (X t Y : ℝ)
    (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter) (core : FirstCoreIndex) :
    (∑ D∈F.powerset,
      priorityOuter p hg b negative Ψ m selector r core D *
      ‖primeMark J lists a (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2 *
      (priorityPoisson p hp hg hinj F b C negative Ψ m
        ((∏ i ∈ E,p i))
        slots J lists a omega X t Y r core D).re) =
    (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
      parentFunction p (fun x=>priorityPoisson p hp hg hinj F b C negative Ψ m
        ((∏ i ∈ E,p i))
        slots J lists a omega X t Y r core x.quotientSupport) (forgetAppended y)).re := by
  have he := fixed_priority_complex p hinj F b C E old negative J lists a
    (fun D=>(priorityOuter p hg b negative Ψ m selector r core D:ℂ))
    (priorityPoisson p hp hg hinj F b C negative Ψ m
      ((∏ i ∈ E,p i)) slots J lists a omega X t Y r core)
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero] using hr

theorem first_priority_energy_reindex (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→InverseInitialFibers.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (omega : ℝ→ℂ) (X t Y : ℝ) :
    firstPrioritySecondEnergy p hp hg hinj F b C negative Ψ m
      ((∏ i ∈ E,p i)) slots lists a selector omega X t Y =
    firstCoreMassBound*(2:ℝ)^slots.card *
      ∑ r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter,
      ∑ core : FirstCoreIndex,∑ J∈slots.powerset,
      (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
        coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        parentFunction p (fun x=>priorityPoisson p hp hg hinj F b C negative Ψ m
          ((∏ i ∈ E,p i))
          slots J lists a omega X t Y r core x.quotientSupport) (forgetAppended y)).re := by
  simp_rw [←first_priority_physical_slice p hp hg hinj]
  unfold firstPrioritySecondEnergy
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro core hcore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro D hD
  unfold priorityOuter priorityPoisson
  ring

end InverseFirstPriorityParents

end

noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped Classical BigOperators SchwartzMap
namespace InversePrincipalEnergy
open Eisenstein SchwartzPlanePoisson
open SecondPassArithmetic FirstPassCubeLabels IdealDivisorBound
open InverseMoment
open Eisenstein SchwartzPlanePoisson
local notation "Eis" => Eisenstein.O

def pvSeminorms : Finset (ℕ × ℕ) :=
  Classical.choose paperRadialFourier_nonzero_lattice_uniform

def pvConstant : ℝ :=
  Classical.choose (Classical.choose_spec paperRadialFourier_nonzero_lattice_uniform)

theorem pvConstant_pos : 0 < pvConstant :=
  (Classical.choose_spec
    (Classical.choose_spec paperRadialFourier_nonzero_lattice_uniform)).1

def pvControl (W : 𝓢(ℝ, ℂ)) : ℝ :=
  pvConstant * pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) W

theorem pvControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ pvControl W :=
  mul_nonneg pvConstant_pos.le (apply_nonneg _ _)

theorem pv_lattice_bound (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    t * (∑' h : {h : O // h ≠ 0},
      ‖paperRadialFourier W (t * ‖ringComplex h.val‖ ^ 2)‖) ≤ pvControl W :=
  (Classical.choose_spec
    (Classical.choose_spec paperRadialFourier_nonzero_lattice_uniform)).2 W t ht

section
variable {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem zero_norm_le (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1)
    (m c d : Eis) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 ≤ Y)
    (K : Finset ι → Finset ι → Finset Eis)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : Eis) ∈ K G E) :
    ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ ≤
      Y * ‖paperRadialFourier W 0‖ * ∑ G ∈ F.powerset, ‖H G‖ ^ 2 := by
  apply (truncatedSecondZero_norm_le p hg hinj F Ψ m c d H W Y K hzero).trans
  rw [abs_of_nonneg hY]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hY (norm_nonneg _))
  exact Finset.sum_le_sum (fun G _ => pow_le_pow_left₀ (norm_nonneg _)
    (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d H G) 2)

def supportIdeal (G : Finset ι) : Ideal Eis := ∏ i ∈ G, Ideal.span {p i}

omit [DecidableEq ι] in
lemma supportIdeal_ne_zero (G : Finset ι) : supportIdeal p G ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i}))

omit [DecidableEq ι] in
lemma supportIdeal_norm_pos (G : Finset ι) : 0 < (Ideal.absNorm (supportIdeal p G) : ℝ) := by
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (supportIdeal_ne_zero p G))

include hinj in

theorem mask_card_le_divisors (G : Finset ι) :
    G.powerset.card ≤ (idealDivisors (supportIdeal p G)).card := by
  apply Finset.card_le_card_of_injOn (supportIdeal p)
  · intro E hE
    apply (mem_idealDivisors (supportIdeal_ne_zero p G)).mpr
    exact Finset.prod_dvd_prod_of_subset E G (fun i => Ideal.span {p i}) (Finset.mem_powerset.mp hE)
  · intro E _ D _ h
    exact primeIdealFamily_product_injective (fun i => Ideal.span {p i}) hinj h

def principalFrequency (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ((Y : ℂ) / (‖ringComplex (∏ i ∈ (∅ : Finset ι) ∪ ∅, p i)‖ : ℂ)) *
    paperRadialFourier W (Y * ‖ringComplex k‖ ^ 2 /
      (‖ringComplex e‖ ^ 2 * primeProductNorm p ((∅ : Finset ι) ∪ ∅))) *
    secondGaussTerm p hp hg Ψ Ψ m r c d e k H₁ H₂ ∅ ∅

theorem principalFrequency_eq (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    principalFrequency p hg hp Ψ m r c d e k H₁ H₂ W Y =
      (Y : ℂ) * paperRadialFourier W (Y * ‖ringComplex k‖ ^ 2 / ‖ringComplex e‖ ^ 2) *
        (star (H₁ ∅) * H₂ ∅) := by
  simp only [principalFrequency, Finset.union_empty, Finset.prod_empty, map_one, norm_one,
    Complex.ofReal_one, div_one, primeProductNorm, one_pow, mul_one,
    secondGaussTerm_empty (p := p) (hp := hp) (hg := hg)]

theorem principalFrequency_eq_secondFrequencyKernel_empty
    (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    principalFrequency p hg hp Ψ m r c d e k H₁ H₂ W Y =
      secondFrequencyKernel p hp hg ∅ Ψ Ψ m r c d e k H₁ H₂ W Y := by
  simp only [secondFrequencyKernel, secondKernelPair, Finset.powerset_empty, Finset.sum_singleton,
    Finset.disjoint_empty_left, ite_true, principalFrequency]
  ring

def restorationTerm (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (G : Finset ι) (E : G.powerset) (k : Eis) : ℂ :=
  secondSourceCommonCoefficient p hg Ψ m c d G E.val *
    principalFrequency p hg hp Ψ m
      (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
      (∏ i ∈ E.val,p i) k
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

theorem restorationTerm_eq_principal_kernel (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ)
    (m c d : Eis) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (G : Finset ι) (E : G.powerset) (k : Eis) :
    restorationTerm p hg hp Ψ m c d H W Y G E k =
      secondSourceCommonCoefficient p hg Ψ m c d G E.val *
        secondFrequencyKernel p hp hg ∅ Ψ Ψ m
          (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
          (∏ i ∈ E.val,p i) k
          (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y := by
  rw [restorationTerm, principalFrequency_eq_secondFrequencyKernel_empty]

theorem restorationTerm_eq (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (G : Finset ι) (E : G.powerset) (k : Eis) :
    restorationTerm p hg hp Ψ m c d H W Y G E k =
      (‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ) *
      (‖H G‖ ^ 2 : ℝ) * supportMobius E.val *
      ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ) : ℝ) : ℂ) *
      paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖ringComplex k‖ ^ 2) := by
  rw [restorationTerm, principalFrequency_eq]
  simp only [Finset.union_empty, secondSourceCommonCoefficient, ringComplex_norm_sq_eq_absNorm_span, span_finset_prime_product]
  have hh : star (H G) * H G = (‖H G‖ ^ 2 : ℝ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hh]
  simp only [supportIdeal, Complex.ofReal_div]
  have harg : Y * ‖ringComplex k‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E.val, Ideal.span {p i}) : ℝ) =
      (Y / (Ideal.absNorm (∏ i ∈ E.val, Ideal.span {p i}) : ℝ)) * ‖ringComplex k‖ ^ 2 := by ring
  simp only [ringComplex_norm_sq_eq_absNorm_span] at harg
  rw [harg]
  ring

theorem restorationTerm_mask_norm_le (hp : ∀ i, p i ≠ 0)
    (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (G : Finset ι) (E : G.powerset) (k : Eis) (θ : ℂ) (hθ : ‖θ‖ ≤ 1) :
    ‖θ * restorationTerm p hg hp Ψ m c d H W Y G E k‖ ≤
      ‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        ‖paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖ringComplex k‖ ^ 2)‖ := by
  have ht := div_pos hY (supportIdeal_norm_pos p E.val)
  have ha : ‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d (fun _ => 1) G‖ ^ 2 ≤ 1 := by
    simpa only [norm_one, one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d (fun _ => 1) G) 2
  have hμ := (supportMobius_norm E.val).le
  rw [restorationTerm_eq]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_norm, abs_of_pos ht]
  calc
    _ ≤ 1 * (1 * ‖H G‖ ^ 2 * 1 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        ‖paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖ringComplex k‖ ^ 2)‖) := by gcongr
    _ = _ := by ring

theorem restorationTerm_mask_summable_norm (hp : ∀ i, p i ≠ 0)
    (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (G : Finset ι) (E : G.powerset) (θ : Eis → ℂ)
    (hθ : ∀ k : {k : Eis // k ≠ 0}, ‖θ k.val‖ ≤ 1) :
    Summable (fun k : {k : Eis // k ≠ 0} =>
      ‖θ k.val * restorationTerm p hg hp Ψ m c d H W Y G E k.val‖) := by
  have ht := div_pos hY (supportIdeal_norm_pos p E.val)
  have hs := (paperRadialFourier_lattice_summable_norm W _ ht).subtype (fun k : Eis => k ≠ 0)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => restorationTerm_mask_norm_le p hg hp Ψ hΨ m c d H W Y hY G E k.val (θ k.val) (hθ k))
    (hs.mul_left (‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ))))

theorem restoration_divisor_abs_le (hp : ∀ i, p i ≠ 0)
    (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (G : Finset ι) (E : G.powerset) (θ : Eis → ℂ)
    (hθ : ∀ k : {k : Eis // k ≠ 0}, ‖θ k.val‖ ≤ 1) :
    (∑' k : {k : Eis // k ≠ 0},
      ‖θ k.val * restorationTerm p hg hp Ψ m c d H W Y G E k.val‖) ≤
        pvControl W * ‖H G‖ ^ 2 := by
  have ht := div_pos hY (supportIdeal_norm_pos p E.val)
  have hs := (paperRadialFourier_lattice_summable_norm W _ ht).subtype (fun k : Eis => k ≠ 0)
  have hb : (∑' k : {k : Eis // k ≠ 0},
      ‖θ k.val * restorationTerm p hg hp Ψ m c d H W Y G E k.val‖) ≤
      ∑' k : {k : Eis // k ≠ 0}, ‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        ‖paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖ringComplex k.val‖ ^ 2)‖ :=
    Summable.tsum_le_tsum
      (fun k : {k : Eis // k ≠ 0} => restorationTerm_mask_norm_le p hg hp Ψ hΨ m c d H W Y hY G E k.val (θ k.val) (hθ k))
      (restorationTerm_mask_summable_norm p hg hp Ψ hΨ m c d H W Y hY G E θ hθ)
      (hs.mul_left (‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ))))
  apply hb.trans
  calc
    _ = (‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ))) *
        (∑' k : {k : Eis // k ≠ 0}, ‖paperRadialFourier W
          ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖ringComplex k.val‖ ^ 2)‖) :=
      tsum_mul_left
    _ = ‖H G‖ ^ 2 * ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        (∑' k : {k : Eis // k ≠ 0}, ‖paperRadialFourier W
          ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖ringComplex k.val‖ ^ 2)‖)) := mul_assoc _ _ _
    _ ≤ ‖H G‖ ^ 2 * pvControl W :=
      mul_le_mul_of_nonneg_left (pv_lattice_bound W _ ht) (sq_nonneg ‖H G‖)
    _ = _ := mul_comm _ _

def principalRestoration (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (θ : Finset ι → Finset ι → Eis → ℂ) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset, ∑' k : {k : Eis // k ≠ 0},
    θ G E.val k.val * restorationTerm p hg hp Ψ m c d H W Y G E k.val

include hinj in
theorem principalRestoration_abs_le (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (θ : Finset ι → Finset ι → Eis → ℂ)
    (hθ : ∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) :
    (∑ G ∈ F.powerset, ∑ E : G.powerset, ∑' k : {k : Eis // k ≠ 0},
      ‖θ G E.val k.val * restorationTerm p hg hp Ψ m c d H W Y G E k.val‖) ≤
      pvControl W *
        ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro G hG
  calc
    _ ≤ ∑ E : G.powerset, pvControl W * ‖H G‖ ^ 2 :=
      Finset.sum_le_sum (fun E _ => restoration_divisor_abs_le p hg hp Ψ hΨ m c d H W Y hY G E
        (θ G E.val) (hθ G hG E))
    _ = (G.powerset.card : ℝ) * (pvControl W * ‖H G‖ ^ 2) := by simp
    _ ≤ ((idealDivisors (supportIdeal p G)).card : ℝ) *
        (pvControl W * ‖H G‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast mask_card_le_divisors p hinj G)
        (mul_nonneg (pvControl_nonneg W) (sq_nonneg _))
    _ = _ := by ring

include hinj in
theorem principalRestoration_norm_le (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (θ : Finset ι → Finset ι → Eis → ℂ)
    (hθ : ∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) :
    ‖principalRestoration p hg hp F Ψ m c d H W Y θ‖ ≤
      pvControl W *
        ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  apply (norm_sum_le _ _).trans
  apply le_trans _ (principalRestoration_abs_le p hg hinj hp F Ψ hΨ m c d H W Y hY θ hθ)
  apply Finset.sum_le_sum
  intro G hG
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro E _
  exact norm_tsum_le_tsum_norm (restorationTerm_mask_summable_norm p hg hp Ψ hΨ m c d H W Y hY G E
    (θ G E.val) (hθ G hG E))

def markedRadial {σ : Type*} [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (V : 𝓢(ℝ, ℂ)) (X : ℝ) (G : Finset ι) : ℂ :=
  primeMark slots lists a (A ∪ G) * V (primeProductNorm p G / X)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma markedRadial_support {σ : Type*} [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (V : 𝓢(ℝ, ℂ)) (X M : ℝ) (hX : 0 < X)
    (hV : ∀ t, V t ≠ 0 → t ≤ Real.exp M) (G : Finset ι)
    (hG : markedRadial p slots lists a A V X G ≠ 0) :
    primeProductNorm p G ≤ X * Real.exp M := by
  have hv : V (primeProductNorm p G / X) ≠ 0 := by
    intro hz
    exact hG (by simp [markedRadial, hz])
  simpa only [mul_comm] using (div_le_iff₀ hX).mp (hV _ hv)

include hinj in

theorem radial_mass_from_pointwise (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (H : Finset ι → ℂ) (U ε D : ℝ)
    (hU : 0 < U) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hs : ∀ G, H G ≠ 0 → primeProductNorm p G ≤ U)
    (hb : ∀ G, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 ≤
      D * (primeProductNorm p G) ^ ε) :
    (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) ≤
      (1+diagonalControl sieveCutoff) * D * U ^ (1 + ε) := by
  let T := boundedPrimeSupports p F U
  have he : (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) =
      ∑ G ∈ T, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro G hG hn
    have hz : H G = 0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hG, hs G hh⟩)
    simp [hz]
  rw [he]
  calc
    _ ≤ ∑ G ∈ T, D * U ^ ε := by
      apply Finset.sum_le_sum
      intro G hG
      exact (hb G).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (primeProductNorm_pos p hp G).le (Finset.mem_filter.mp hG).2 hε) hD)
    _ = (T.card : ℝ) * (D * U ^ ε) := by simp
    _ ≤ ((1+diagonalControl sieveCutoff) * U) * (D * U ^ ε) := mul_le_mul_of_nonneg_right
      (boundedPrimeSupports_card_positive p hp hinj F U hU) (by positivity)
    _ = (1+diagonalControl sieveCutoff) * D * U ^ (1 + ε) := by rw [Real.rpow_add hU, Real.rpow_one]; ring

omit [DecidableEq ι] in
lemma mass_le_divisor_mass (F : Finset ι) (H : Finset ι → ℂ) :
    (∑ G ∈ F.powerset, ‖H G‖ ^ 2) ≤
      ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro G _
  have ho : (1 : Ideal Eis) ∈ idealDivisors (supportIdeal p G) :=
    (mem_idealDivisors (supportIdeal_ne_zero p G)).mpr (one_dvd _)
  have hc : (1 : ℝ) ≤ ((idealDivisors (supportIdeal p G)).card : ℝ) := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1, ho⟩
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (sq_nonneg ‖H G‖)

end

theorem marked_radial_divisor_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (V : 𝓢(ℝ, ℂ)) (X M : ℝ), 0 < X →
      (∀ t, V t ≠ 0 → t ≤ Real.exp M) →
      (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) *
        ‖markedRadial p slots lists a A V X G‖ ^ 2) ≤
        C * (4 : ℝ)^A.card * (SchwartzMap.seminorm ℝ 0 0 V)^2 *
          (X * Real.exp M)^(1 + ε) := by
  obtain ⟨Cm, hCm, hm⟩ := finite_primeMark_extracted_bound (ε / 4) (by positivity)
  obtain ⟨Cd, hCd, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  have hdc := diagonalControl_nonneg sieveCutoff
  refine ⟨(1+diagonalControl sieveCutoff) * Cd * Cm ^ 2, by positivity, ?_⟩
  intro ι σ _ _ p hp _ hinj hcop slots lists a hslots ha A F V X M hX hV
  have hpoint (G : Finset ι) :
      ((idealDivisors (supportIdeal p G)).card : ℝ) *
        ‖markedRadial p slots lists a A V X G‖ ^ 2 ≤
      (Cd * ((2 : ℝ)^A.card * Cm * SchwartzMap.seminorm ℝ 0 0 V)^2) *
        (primeProductNorm p G)^ε := by
    have hn := primeProductNorm_pos p hp G
    have hmark := hm p hp hcop slots lists a hslots ha A G
    have hv := V.norm_le_seminorm ℝ (primeProductNorm p G / X)
    have hdiv := hd (supportIdeal p G) (supportIdeal_ne_zero p G)
    rw [show (Ideal.absNorm (supportIdeal p G) : ℝ) = primeProductNorm p G from
      (primeProductNorm_eq_ideal_norm p G).symm] at hdiv
    have hpow : (primeProductNorm p G) ^ (ε / 2) * ((primeProductNorm p G) ^ (ε / 4))^2 =
        (primeProductNorm p G)^ε := by
      rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_add hn]
      congr 1
      ring
    calc
      _ ≤ (Cd * (primeProductNorm p G)^(ε/2)) *
          (((2 : ℝ)^A.card * Cm * (primeProductNorm p G)^(ε/4)) *
            SchwartzMap.seminorm ℝ 0 0 V)^2 := by
        apply mul_le_mul hdiv _ (sq_nonneg _) (by positivity)
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [markedRadial, norm_mul]
        exact mul_le_mul hmark hv (norm_nonneg _) (by positivity)
      _ = (Cd * ((2 : ℝ)^A.card * Cm * SchwartzMap.seminorm ℝ 0 0 V)^2) *
          ((primeProductNorm p G)^(ε/2) * ((primeProductNorm p G)^(ε/4))^2) := by ring
      _ = _ := by rw [hpow]
  have hb := radial_mass_from_pointwise p hinj hp F (markedRadial p slots lists a A V X)
    (X * Real.exp M) ε (Cd * ((2 : ℝ)^A.card * Cm * SchwartzMap.seminorm ℝ 0 0 V)^2)
    (by positivity) hε.le (by positivity)
    (markedRadial_support p slots lists a A V X M hX hV) hpoint
  have h4 : ((2 : ℝ)^A.card)^2 = (4 : ℝ)^A.card := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  convert hb using 1 ; (rw [mul_pow, mul_pow, h4]; ring)

lemma radial_support_of_annular (V : 𝓢(ℝ, ℂ)) (a M : ℝ)
    (hV : tsupport V ⊆ Set.Icc a (Real.exp M)) :
    ∀ t, V t ≠ 0 → t ≤ Real.exp M := by
  intro t ht
  exact (hV (subset_closure ht)).2

def outsideCutoff {ι : Type*} [DecidableEq ι]
    (K : Finset ι → Finset ι → Finset Eis) (G E : Finset ι) (k : Eis) : ℂ :=
  if k ∈ K G E then 0 else 1

lemma outsideCutoff_norm_le_one {ι : Type*} [DecidableEq ι]
    (K : Finset ι → Finset ι → Finset Eis) (G E : Finset ι) (k : Eis) :
    ‖outsideCutoff K G E k‖ ≤ 1 := by
  unfold outsideCutoff
  split_ifs <;> norm_num

lemma outsideCutoff_mul_norm_le_one {ι : Type*} [DecidableEq ι]
    (K : Finset ι → Finset ι → Finset Eis) (G E : Finset ι) (k : Eis)
    (θ : ℂ) (hθ : ‖θ‖ ≤ 1) : ‖outsideCutoff K G E k * θ‖ ≤ 1 := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul (outsideCutoff_norm_le_one K G E k) hθ
    (norm_nonneg _) zero_le_one

theorem uniform_row_control :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(ℝ, ℂ),
      ‖paperRadialFourier W 0‖ + pvControl W ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 0
  refine ⟨s ∪ pvSeminorms,
    C + pvConstant, add_pos hC pvConstant_pos, ?_⟩
  intro W
  have h₁ := Seminorm.le_def.mp (Finset.sup_mono (f := schwartzSeminormFamily ℝ ℝ ℂ)
    (Finset.subset_union_left (s₁ := s) (s₂ := pvSeminorms))) W
  have h₂ := Seminorm.le_def.mp (Finset.sup_mono (f := schwartzSeminormFamily ℝ ℝ ℂ)
    (Finset.subset_union_right (s₁ := s) (s₂ := pvSeminorms))) W
  have hz : ‖paperRadialFourier W 0‖ ≤ C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    simpa only [pow_zero, one_mul] using hb W 0 le_rfl
  calc
    _ ≤ C * (s ∪ pvSeminorms).sup (schwartzSeminormFamily ℝ ℝ ℂ) W +
        pvConstant *
          (s ∪ pvSeminorms).sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
      add_le_add (hz.trans (mul_le_mul_of_nonneg_left h₁ hC.le))
        (mul_le_mul_of_nonneg_left h₂ pvConstant_pos.le)
    _ = _ := by ring

section
variable {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in
theorem principal_energy_le (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 1 ≤ Y)
    (K : Finset ι → Finset ι → Finset Eis)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : Eis) ∈ K G E)
    (θ : Finset ι → Finset ι → Eis → ℂ)
    (hθ : ∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) :
    ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ +
        ‖principalRestoration p hg hp F Ψ m c d H W Y θ‖ ≤
      Y * (‖paperRadialFourier W 0‖ + pvControl W) *
        ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hd : 0 ≤ ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 :=
    Finset.sum_nonneg (fun G _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  calc
    _ ≤ Y * ‖paperRadialFourier W 0‖ * ∑ G ∈ F.powerset, ‖H G‖ ^ 2 +
        pvControl W *
          ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 :=
      add_le_add (zero_norm_le p hg hinj F Ψ hΨ m c d H W Y hY0.le K hzero)
        (principalRestoration_norm_le p hg hinj hp F Ψ hΨ m c d H W Y hY0 θ hθ)
    _ ≤ Y * ‖paperRadialFourier W 0‖ *
          (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) +
        Y * pvControl W *
          (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (mass_le_divisor_mass p F H) (mul_nonneg hY0.le (norm_nonneg _))
      · exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_left (pvControl_nonneg W) hY) hd
    _ = _ := by ring

end

theorem marked_principal_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (Ψ : Eis →* ℂ), (∀ z, ‖Ψ z‖ ≤ 1) →
      ∀ (m c d : Eis) (V W : 𝓢(ℝ, ℂ)) (X M Y : ℝ), 0 < X → 1 ≤ Y →
      (∀ t, V t ≠ 0 → t ≤ Real.exp M) →
      ∀ K : Finset ι → Finset ι → Finset Eis,
      (∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : Eis) ∈ K G E) →
      ∀ θ : Finset ι → Finset ι → Eis → ℂ,
      (∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) →
      ‖truncatedSecondZero p hg F Ψ m c d (markedRadial p slots lists a A V X) W Y K‖ +
        ‖principalRestoration p hg hp F Ψ m c d (markedRadial p slots lists a A V X) W Y θ‖ ≤
      C * (4 : ℝ)^A.card *
        (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 V)^2) *
        Y * (X * Real.exp M)^(1 + ε) := by
  obtain ⟨s, Cr, hCr, hr⟩ := uniform_row_control
  obtain ⟨Cm, hCm, hm⟩ := marked_radial_divisor_mass ε hε
  refine ⟨s, Cr * Cm, mul_pos hCr hCm, ?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists a hslots ha A F Ψ hΨ m c d V W X M Y hX hY hV K hzero θ hθ
  apply (principal_energy_le p hg hinj hp F Ψ hΨ m c d
    (markedRadial p slots lists a A V X) W Y hY K hzero θ hθ).trans
  have hb := hm p hp hinj hcop slots lists a hslots ha A F V X M hX hV
  calc
    _ ≤ Y * (Cr * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
        (Cm * (4 : ℝ)^A.card * (SchwartzMap.seminorm ℝ 0 0 V)^2 *
          (X * Real.exp M)^(1 + ε)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hr W) (le_trans zero_le_one hY)) hb
        (Finset.sum_nonneg (fun G _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
        (mul_nonneg (le_trans zero_le_one hY) (mul_nonneg hCr.le (apply_nonneg _ _)))
    _ = _ := by ring

end InversePrincipalEnergy

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
