/-
Two-pass height cost adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.ActualLabelSteps

/-!
# Two-pass height cost

First degrees and heights of the first–second height cost; live first heights and the original
two-pass energy; redundant punctures in canonical marked rows.
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
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMomentFirstSecondHeightCost
open InverseMoment InverseAmbientProfileTower JointLogSeparation JointLogSeparation
open InverseMomentFirstOriginalProfile

def firstDegree (degree : ℕ) : ℕ := 2*InverseClippingProfiles.momentOrder (2*degree)

def firstHeight (negative : Bool) (z : Frequency×(Fin 9→ℝ)) : ℝ :=
  profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 (if negative then 7 else 8)

lemma first_height_cost (degree : ℕ) (negative : Bool) (z : Frequency×(Fin 9→ℝ)) :
    (1+‖firstHeight negative z‖)^(firstDegree degree)≤
      tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2 := by
  cases negative
  · exact first_right_height_budget _ z
  · exact first_left_height_budget _ z

lemma first_weight_one_le (J : ℕ) (z : Frequency×(Fin 9→ℝ)) :
    1≤ tripleHeight J z.1*coordinateHeight J z.2 := by
  simpa only [ambientWeight,tripleHeight,coordinateHeight] using ambientWeight_one_le J z

def stepBudget (C Cbin Czero Ctail A Z F eta tau pi epschild saving : ℝ) : ℝ :=
  Czero*Z^(F+17*eta+tau+pi)+
    C*A*(1+Cbin*Real.log Z)^4*Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)

lemma stepBudget_nonneg (C Cbin Czero Ctail A Z F eta tau pi epschild saving : ℝ)
    (hC : 0≤ C) (hz : 0≤ Czero) (ht : 0≤ Ctail) (hA : 0≤ A) (hZ : 0≤ Z) :
    0≤ stepBudget C Cbin Czero Ctail A Z F eta tau pi epschild saving := by
  unfold stepBudget
  positivity

theorem second_step_first_height (degree : ℕ) (negative : Bool)
    (C Cbin Czero Ctail A Z F eta tau pi epschild saving : ℝ)
    (hC : 0≤ C) (hz : 0≤ Czero) (ht : 0≤ Ctail) (hA : 0≤ A) (hZ : 0≤ Z)
    (z : Frequency×(Fin 9→ℝ)) :
    Czero*Z^(F+17*eta+tau+pi)+
      C*A*(1+‖firstHeight negative z‖)^(firstDegree degree)*(1+Cbin*Real.log Z)^4*
        Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)≤
      stepBudget C Cbin Czero Ctail A Z F eta tau pi epschild saving*
        (tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
  have hw := first_weight_one_le (firstDegree degree) z
  have hh := first_height_cost degree negative z
  have hzero : Czero*Z^(F+17*eta+tau+pi)≤
      (Czero*Z^(F+17*eta+tau+pi))*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) :=
    le_mul_of_one_le_right (by positivity) hw
  have htail : Ctail*Z^(-saving)≤
      (Ctail*Z^(-saving))*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) :=
    le_mul_of_one_le_right (by positivity) hw
  have hmiddle := mul_le_mul_of_nonneg_left hh
    (show 0≤ C*A*(1+Cbin*Real.log Z)^4*Z^(F+48*eta+tau+pi+epschild) by positivity)
  have hs := add_le_add (add_le_add hzero hmiddle) htail
  simpa only [stepBudget, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, one_mul, mul_one] using hs

lemma log_fourth_small_power (Cbin ε : ℝ) (hε : 0<ε) :
    ∃ Clog : ℝ,0< Clog ∧ ∀ Z : ℝ,2≤ Z→
      (1+Cbin*Real.log Z)^4≤ Clog*Z^ε := by
  obtain ⟨C,hC,he⟩ := log_eighth_small_power ε hε
  let b := 1+|Cbin|
  have hb : 0< b := by dsimp [b];positivity
  refine ⟨b^4*C,mul_pos (pow_pos hb _) hC,?_⟩
  intro Z hZ
  have hZ1 : 1≤ Z := by linarith
  have hl : 0≤ Real.log Z := Real.log_nonneg hZ1
  have hn : |1+Cbin*Real.log Z|≤ b*(1+Real.log Z) := by
    calc
      _≤1+|Cbin| *Real.log Z := by simpa [abs_mul,abs_of_nonneg hl] using abs_add_le (1:ℝ) (Cbin*Real.log Z)
      _≤ _ := by dsimp [b];nlinarith [abs_nonneg Cbin]
  calc
    _ = |1+Cbin*Real.log Z|^4 := by rw [←abs_pow,abs_of_nonneg (by positivity)]
    _ ≤ (b*(1+Real.log Z))^4 := pow_le_pow_left₀ (abs_nonneg _) hn 4
    _≤ b^4*(1+Real.log Z)^8 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith : 1≤1+Real.log Z) (by norm_num : 4≤8)) (by positivity)
    _≤ b^4*(C*Z^ε) := mul_le_mul_of_nonneg_left (he Z hZ1) (by positivity)
    _=_ := by ring

theorem stepBudget_small_power (C Cbin Czero Ctail ε : ℝ)
    (hC : 0≤ C) (hz : 0≤ Czero) (ht : 0≤ Ctail) (hε : 0<ε) :
    ∃ Ctotal : ℝ,0< Ctotal ∧ ∀ A Z F eta tau pi epschild saving : ℝ,
      0≤ A→2≤ Z→0≤ eta→0≤ epschild→
      -saving≤ F+48*eta+tau+pi+epschild+ε→
      stepBudget C Cbin Czero Ctail A Z F eta tau pi epschild saving≤
        Ctotal*(1+A)*Z^(F+48*eta+tau+pi+epschild+ε) := by
  obtain ⟨Clog,hlog,hlogs⟩ := log_fourth_small_power Cbin ε hε
  refine ⟨1+Czero+C*Clog+Ctail,by positivity,?_⟩
  intro A Z F eta tau pi epschild saving hA hZ heta hepschild hsaving
  have hZ1 : 1≤ Z := by linarith
  have hZ0 : 0< Z := by linarith
  have h0 : Z^(F+17*eta+tau+pi)≤ Z^(F+48*eta+tau+pi+epschild+ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have h1 : C*A*(1+Cbin*Real.log Z)^4*Z^(F+48*eta+tau+pi+epschild)≤
      C*A*Clog*Z^(F+48*eta+tau+pi+epschild+ε) := by
    calc
      _≤ C*A*(Clog*Z^ε)*Z^(F+48*eta+tau+pi+epschild) := by gcongr;exact hlogs Z hZ
      _=_ := by rw [show C*A*(Clog*Z^ε)*Z^(F+48*eta+tau+pi+epschild)=
          C*A*Clog*(Z^ε*Z^(F+48*eta+tau+pi+epschild)) by ring,←Real.rpow_add hZ0];congr 1;congr 1;ring
  have h2 : Z^(-saving)≤ Z^(F+48*eta+tau+pi+epschild+ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 hsaving
  have hsum := add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 hz) h1)
    (mul_le_mul_of_nonneg_left h2 ht)
  unfold stepBudget
  apply hsum.trans
  have hpow : 0≤ Z^(F+48*eta+tau+pi+epschild+ε) := Real.rpow_nonneg hZ0.le _
  have hcoef : Czero+C*A*Clog+Ctail≤(1+Czero+C*Clog+Ctail)*(1+A) := by
    have hza : 0≤ Czero*A := mul_nonneg hz hA
    have hta : 0≤ Ctail*A := mul_nonneg ht hA
    have hc : 0≤ C*Clog := mul_nonneg hC hlog.le
    nlinarith
  convert mul_le_mul_of_nonneg_right hcoef hpow using 1 ; ring

theorem first_source_budget (degree : ℕ) (C Cbin Czero Ctail ε : ℝ)
    (hC : 0≤ C) (hz : 0≤ Czero) (ht : 0≤ Ctail) (hε : 0<ε) :
    ∃ Ctotal : ℝ,0< Ctotal ∧ ∀ A Z F eta tau pi epschild saving : ℝ,
      0≤ A→2≤ Z→0≤ eta→0≤ epschild→
      -saving≤ F+48*eta+tau+pi+epschild+ε→
      ∀(negative : Bool)(z : Frequency×(Fin 9→ℝ)),
      Czero*Z^(F+17*eta+tau+pi)+
        C*A*(1+‖firstHeight negative z‖)^(firstDegree degree)*(1+Cbin*Real.log Z)^4*
          Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)≤
      (Ctotal*(1+A)*Z^(F+48*eta+tau+pi+epschild+ε))*
        (tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
  obtain ⟨Ct,hCt,hbudget⟩ := stepBudget_small_power C Cbin Czero Ctail ε hC hz ht hε
  refine ⟨Ct,hCt,?_⟩
  intro A Z F eta tau pi epschild saving hA hZ heta heps hsaving negative z
  exact (second_step_first_height degree negative C Cbin Czero Ctail A Z F eta tau pi epschild saving
    hC hz ht hA (by linarith) z).trans
    (mul_le_mul_of_nonneg_right (hbudget A Z F eta tau pi epschild saving hA hZ heta heps hsaving)
      (le_trans zero_le_one (first_weight_one_le _ z)))

theorem first_source_requested_loss (degree : ℕ) (C Cbin Czero Ctail ε : ℝ)
    (hC : 0≤ C) (hz : 0≤ Czero) (ht : 0≤ Ctail) (hε : 0<ε) :
    ∃ Ctotal : ℝ,0< Ctotal ∧ ∀ A Z F eta tau pi epschild saving loss : ℝ,
      0≤ A→2≤ Z→0≤ eta→0≤ epschild→
      -saving≤ F+48*eta+tau+pi+epschild+ε→
      48*eta+tau+pi+epschild+ε≤ loss→
      ∀(negative : Bool)(z : Frequency×(Fin 9→ℝ)),
      Czero*Z^(F+17*eta+tau+pi)+
        C*A*(1+‖firstHeight negative z‖)^(firstDegree degree)*(1+Cbin*Real.log Z)^4*
          Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)≤
      (Ctotal*(1+A)*Z^(F+loss))*
        (tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
  obtain ⟨Ct,hCt,hbudget⟩ := first_source_budget degree C Cbin Czero Ctail ε hC hz ht hε
  refine ⟨Ct,hCt,?_⟩
  intro A Z F eta tau pi epschild saving loss hA hZ heta heps hsaving hloss negative z
  apply (hbudget A Z F eta tau pi epschild saving hA hZ heta heps hsaving negative z).trans
  apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one (first_weight_one_le _ z))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end InverseMomentFirstSecondHeightCost
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseAmbientProfileTower JointLogSeparation JointLogSeparation
open InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell CompletedHeight
open Eisenstein (ringComplex)
local notation "O"=> Eisenstein.O

theorem actual_live_first_height
    (old:ℝ → ℂ)(oldb:ℝ)(hsold:∀y,old y≠0 → y≤ oldb)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0< lo)(hs:Function.support om⊆Set.Icc lo hi)(negative:Bool)
    (F tau saving window b em ed:ℝ)(hF:0≤ F)(htau:0< tau)(hb:1≤ b)
    (hhib:hi≤ b)(hwindow: b≤ Real.exp window)(hold:oldb≤ Real.exp window)(hem:0< em)(hed:0< ed)(K:ℕ):
    ∃(ω₁ ω₂:𝓢(ℝ,ℂ))(af bf:ℝ),0< af ∧ af≤ bf ∧ HasCompactSupport (ω₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂:ℝ → ℂ) ∧
      tsupport (ω₁:ℝ → ℂ)⊆Set.Icc af bf ∧ tsupport (ω₂:ℝ → ℂ)⊆Set.Icc af bf ∧
    ∀degree:ℕ,∀eps:ℝ,0< eps → ∃C:ℝ,0< C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι → O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hpr:∀i,lambda^2∣p i-1)(hinj:Function.Injective (fun i=> Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι →₀ ℕ))(labels:Finset (Ideal O))(β:Ideal O → (ι →₀ ℕ) → ℂ)
      (Ψ:O →* ℂ)(m:O)(slots:Finset σ)(lists:σ → Finset ι)(weights:σ → ι → ℂ)
      (Φ:𝓢(ℝ,ℂ))(Z M r ell V eta pi epschild A theta Kphysical loss:ℝ),
      2≤ Z → 2≤ Z^eta → 0≤ M → M≤ F →  (-eta≤ r)  → r≤ F → 0≤ ell → ell≤ F → 0≤ V → V≤ F →
      0≤ eta → eta≤1 → tau≤1 → Real.exp window≤ Z^eta → 0≤ pi → 6*eta≤ pi →
      em*(20*(3*F+16)+30)≤ pi/4 → ed*(20*(3*F+16)+30)≤ pi/4 →
      (∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀u,‖Ψ u‖≤1) → (slots:Set σ).PairwiseDisjoint lists → slots.card≤ K →
      (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) → 0≤ A → 0≤ epschild → -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+eps →
      48*eta+tau+pi+epschild+eps≤ loss →
      let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=> firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=> normTwistedSource old theta (y/Z^r);
      let mark:=fun v U=> primeMark slots lists weights (v.support∪U);
      let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=> labels) (fun x=> x.1) (Z^(2*F+15*eta+tau));
      ∀k∈liveJointKeys p S pool (sourceSummand p hp hg β cutoff Ψ m mark W Φ Kphysical),
      ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 negative Ψ m slots lists weights ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree → ∀z:Frequency×(Fin 9 → ℝ),
      (Z^(firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2) (parentWeight p k.2.1)
        negative Ψ m slots lists weights om (columnScale Z r k.1 k.2.1 negative) (InverseMomentFirstSecondHeightCost.firstHeight negative z) (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤
      (C*(1+A)*Z^(r+3*ell+V+loss))*
        (tripleHeight (InverseMomentFirstSecondHeightCost.firstDegree degree) z.1*
          coordinateHeight (InverseMomentFirstSecondHeightCost.firstDegree degree) z.2) :=by
  obtain ⟨w₁,w₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,he⟩:=actual_live_label_step
    old oldb hsold om lo hi hlo hs negative F tau saving window b em ed hF htau hb hhib hwindow hold hem hed K
  refine ⟨w₁,w₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro degree eps heps
  obtain ⟨C,Cbin,Cz,Ct,hC,hCb,hCz,hCt,hstep⟩:=he degree
  obtain ⟨Ctotal,hCtotal,hbudget⟩:=InverseMomentFirstSecondHeightCost.first_source_requested_loss degree C Cbin Cz Ct eps hC hCz hCt heps
  refine ⟨Ctotal,hCtotal,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights Φ
    Z M r ell V eta pi epschild A theta Kphysical loss hZ hbin hM hMF hr hrF hell hellF hV hVF heta heta1 htau1
    hwin hpi hetapi hsmall hsmall' hQ hn hΨ hslots hcard hw hA hechild hsave hloss cutoff W mark S k hk hchild z
  have he':=hstep p hp hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights Φ
    Z M r ell V eta pi epschild A theta (InverseMomentFirstSecondHeightCost.firstHeight negative z) Kphysical
    hZ hbin hM hMF hr hrF hell hellF hV hVF heta heta1 htau1 hwin hpi hetapi hsmall hsmall'
    hQ hn hΨ hslots hcard hw hA k hk hchild
  exact he'.trans (hbudget A Z (r+3*ell+V) eta tau pi epschild saving loss hA hZ heta hechild hsave hloss negative z)

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform InverseMomentFirstLabelCell
open InverseMomentFirstSecondHeightCost
open InverseAmbientProfileTower JointLogSeparation JointLogSeparation CompletedHeight
open Eisenstein (ringComplex)
local notation "O"=> Eisenstein.O

theorem original_two_pass_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0< a)(hs:Function.support om⊆Set.Icc a b)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤ Lcap)(hb:0≤ b)
    (heta:0≤ eta)(heta1:eta≤1)(htau:0< tau)(htau1:tau≤1)
    (hem:0< em)(hed:0< ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0< af₁ ∧ af₁≤ bf₁ ∧ 0< af₂ ∧ af₂≤ bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤ bw ∧ b≤ bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0< epsFirst→0< epsSecond→∀degree:ℕ,
      ∃C Czero Ctail:ℝ,0≤ C ∧ 0≤ Czero ∧ 0≤ Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=> Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta pi epschild A loss:ℝ)
      (_hZ:2≤ Z)(_hbin:2≤ Z^eta)(_hM:0≤ M)(_hF:r+3*ell+V≤ Lcap)(_hMcap:M≤ Lcap)(_hell:0≤ ell)(_hV:0≤ V)(_hr: -eta≤ r)
      (_hbZ:b≤ Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
      (_hrcap:r≤ Lcap)(_hellcap:ell≤ Lcap)

      (_hVcap:V≤ Lcap)(_hwin:Real.exp window≤ Z^eta)(_hpi:0≤ pi)(_hpieta:6*eta≤ pi)
      (_hemcost:em*(20*(3*Lcap+16)+30)≤ pi/4)(_hedcost:ed*(20*(3*Lcap+16)+30)≤ pi/4)
      (_hechild:0≤ epschild)(_hsave: -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+epsSecond)
      (_hloss:48*eta+tau+pi+epschild+epsSecond≤ loss)(_hcard:slots.card≤ K)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hA:0≤ A)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤ Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=> primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=> firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=> normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=> labels) (fun x=> x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hg β cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
        Z M r ell V eta tau window bw epschild A K degree)→
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
        Z M r ell V eta tau window bw epschild A K degree)→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hg pool Q (β I) Ψ m (cubicIdealGenerator I)
          (fun v U=> mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        Czero*Γ^2*Z^(M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta))+
        C*Γ^2*(1+A)*Z^(r+3*ell+V+loss)*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*
          Z^((2*Lcap+15*eta+tau)*epsFirst+epsFirst)+Ctail*Γ^2*Z^(-saving) :=by
  obtain ⟨om₁,om₂,lo,hi,hlo,hlh,hom₁,hom₂,hs₁,hs₂,hfull⟩:=original_dyadic_full_energy om a b ha hs Lcap Lcap eta tau saving hcap hcap hb heta heta1 htau htau1
  let bw:=max 1 (max hi b)
  have hbw:1≤ bw:=le_max_left _ _
  have hbwb: b≤ bw:=(le_max_right hi b).trans (le_max_right 1 _)
  have hbwh:hi≤ bw:=(le_max_left hi b).trans (le_max_right 1 _)
  have hbwp:0< bw:=by linarith
  let window:=Real.log bw
  have hew:Real.exp window=bw:=Real.exp_log hbwp
  have hsold:∀y,om y≠0→y≤ b:=fun y hy=>(hs hy).2
  obtain ⟨w₁₁,w₁₂,af₁,bf₁,haf₁,hab₁,hw₁₁,hw₁₂,hs₁₁,hs₁₂,hleft⟩:=actual_live_first_height
    om b hsold om₁ lo hi hlo (subset_closure.trans hs₁) true
    Lcap tau saving window bw em ed hcap htau hbw hbwh hew.ge (hbwb.trans hew.ge) hem hed K
  obtain ⟨w₂₁,w₂₂,af₂,bf₂,haf₂,hab₂,hw₂₁,hw₂₂,hs₂₁,hs₂₂,hright⟩:=actual_live_first_height
    om b hsold om₂ lo hi hlo (subset_closure.trans hs₂) false
    Lcap tau saving window bw em ed hcap htau hbw hbwh hew.ge (hbwb.trans hew.ge) hem hed K
  refine ⟨w₁₁,w₁₂,w₂₁,w₂₂,af₁,bf₁,af₂,bf₂,window,bw,haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hew.symm,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Cf,Cz,Ct,hCf,hCz,hCt,hfull⟩:=hfull epsFirst hepsF (firstDegree degree)
  obtain ⟨Cl,hCl,hleft⟩:=hleft degree epsSecond hepsS
  obtain ⟨Cr,hCr,hright⟩:=hright degree epsSecond hepsS
  refine ⟨Cf*(Cl+Cr),Cz,Ct,mul_nonneg hCf (by positivity),hCz,hCt,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights
    Z M r ell V Γ theta pi epschild A loss hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap
    hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hΨ hΓ hA hsf hn hβ hlabels hslots hweights
    mark Y cutoff W source keys hl hr'
  let Be:ℝ:=(Cl+Cr)*(1+A)*Z^(r+3*ell+V+loss)
  have hz:0< Z:=by linarith
  have hBe:0≤ Be:=by dsimp[Be];positivity
  have left : ∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=> q.rightExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          true Ψ m slots lists weights om₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤ Be*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
    intro k hk z
    have he:=hleft p hp hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights rowMajorant
      Z M r ell V eta pi epschild A theta (Z^M) loss hZ hbin hM hMcap hr hrcap hell hellcap hV hVcap
      heta heta1 htau1 hwin hpi hpieta hemcost hedcost hQ hn hΨ hslots hcard hweights hA hechild hsave hloss k hk (hl k hk) z
    rw [columnScale_physical Z r (by linarith)] at he
    apply he.trans
    change (Cl*(1+A)*Z^(r+3*ell+V+loss))*_ ≤ Be*_
    have hwgt:0≤ tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2 := le_trans zero_le_one (first_weight_one_le _ z)
    dsimp[Be]
    gcongr
    linarith
  have right : ∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=> q.leftExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          false Ψ m slots lists weights om₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤ Be*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
    intro k hk z
    have he:=hright p hp hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights rowMajorant
      Z M r ell V eta pi epschild A theta (Z^M) loss hZ hbin hM hMcap hr hrcap hell hellcap hV hVcap
      heta heta1 htau1 hwin hpi hpieta hemcost hedcost hQ hn hΨ hslots hcard hweights hA hechild hsave hloss k hk (hr' k hk) z
    rw [columnScale_physical Z r (by linarith)] at he
    apply he.trans
    change (Cr*(1+A)*Z^(r+3*ell+V+loss))*_ ≤ Be*_
    have hwgt:0≤ tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2 := le_trans zero_le_one (first_weight_one_le _ z)
    dsimp[Be]
    gcongr
    linarith
  have hall:=hfull p hp hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta Be
    hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap hΨ hΓ hBe hsf hn hβ hlabels hslots hweights left right
  convert hall using 1 ; dsimp[Be] ; ring

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment

theorem two_pass_scalar (C Cz Ct Γ A Z F M r ell eta tau _pi epsFirst loss Lcap saving lossFinal H:ℝ)
    (hC:0≤ C)(hCz:0≤ Cz)(hCt:0≤ Ct)(hA:0≤ A)(hZ:1≤ Z)(hH:1≤ H)
    (hM:M-ell≤ F)
    (hprincipal:3*eta+epsFirst*(5*ell+2*r+7*eta)≤ lossFinal)
    (hretained:loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤ lossFinal)
    (htail: -saving≤ F+lossFinal):
    Cz*Γ^2*Z^(M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta))+
      C*Γ^2*(1+A)*Z^(F+loss)*H*Z^((2*Lcap+15*eta+tau)*epsFirst+epsFirst)+Ct*Γ^2*Z^(-saving)≤
    (C+Cz+Ct)*Γ^2*(1+A)*H*Z^(F+lossFinal) :=by
  have hz:0< Z:=lt_of_lt_of_le zero_lt_one hZ
  have hP:=Real.rpow_le_rpow_of_exponent_le hZ (show M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta)≤ F+lossFinal by linarith)
  have hT:=Real.rpow_le_rpow_of_exponent_le hZ htail
  have hR:=Real.rpow_le_rpow_of_exponent_le hZ (show F+loss+((2*Lcap+15*eta+tau)*epsFirst+epsFirst)≤ F+lossFinal by linarith)
  have hlarge:1≤(1+A)*H:=one_le_mul_of_one_le_of_one_le (by linarith) hH
  have hp:Cz*Γ^2*Z^(M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta))≤ Cz*Γ^2*((1+A)*H)*Z^(F+lossFinal):=by
    apply (mul_le_mul_of_nonneg_left hP (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa using mul_le_mul_of_nonneg_left hlarge (show 0≤ Cz*Γ^2 by positivity)
  have ht:Ct*Γ^2*Z^(-saving)≤ Ct*Γ^2*((1+A)*H)*Z^(F+lossFinal):=by
    apply (mul_le_mul_of_nonneg_left hT (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa using mul_le_mul_of_nonneg_left hlarge (show 0≤ Ct*Γ^2 by positivity)
  have hr:C*Γ^2*(1+A)*Z^(F+loss)*H*Z^((2*Lcap+15*eta+tau)*epsFirst+epsFirst)≤
      C*Γ^2*((1+A)*H)*Z^(F+lossFinal):=by
    calc
      _=C*Γ^2*((1+A)*H)*Z^(F+loss+((2*Lcap+15*eta+tau)*epsFirst+epsFirst)):=by simp only [Real.rpow_add hz];ring
      _≤ _:=mul_le_mul_of_nonneg_left hR (by positivity)
  nlinarith [add_le_add (add_le_add hp hr) ht]

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform InverseMomentFirstLabelCell
open InverseMomentFirstSecondHeightCost
open InverseAmbientProfileTower JointLogSeparation JointLogSeparation CompletedHeight
open Eisenstein (ringComplex)
local notation "O"=> Eisenstein.O

theorem original_two_pass_parent_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0< a)(hs:Function.support om⊆Set.Icc a b)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤ Lcap)(hb:0≤ b)
    (heta:0≤ eta)(heta1:eta≤1)(htau:0< tau)(htau1:tau≤1)
    (hem:0< em)(hed:0< ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0< af₁ ∧ af₁≤ bf₁ ∧ 0< af₂ ∧ af₂≤ bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤ bw ∧ b≤ bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0< epsFirst→0< epsSecond→∀degree:ℕ,
      ∃C:ℝ,0≤ C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=> Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta pi epschild A loss lossFinal:ℝ)
      (_hZ:2≤ Z)(_hbin:2≤ Z^eta)(_hM:0≤ M)(_hF:r+3*ell+V≤ Lcap)(_hMcap:M≤ Lcap)(_hell:0≤ ell)(_hV:0≤ V)(_hr: -eta≤ r)
      (_hbZ:b≤ Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta))
      (_hrcap:r≤ Lcap)(_hellcap:ell≤ Lcap)

      (_hVcap:V≤ Lcap)(_hwin:Real.exp window≤ Z^eta)(_hpi:0≤ pi)(_hpieta:6*eta≤ pi)
      (_hemcost:em*(20*(3*Lcap+16)+30)≤ pi/4)(_hedcost:ed*(20*(3*Lcap+16)+30)≤ pi/4)
      (_hechild:0≤ epschild)(_hsave: -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+epsSecond)
      (_hloss:48*eta+tau+pi+epschild+epsSecond≤ loss)(_hcard:slots.card≤ K)
      (_hparent:M-ell≤ r+3*ell+V)
      (_hprincipal:3*eta+epsFirst*(5*ell+2*r+7*eta)≤ lossFinal)
      (_hretained:loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤ lossFinal)
      (_htail: -saving≤ r+3*ell+V+lossFinal)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hA:0≤ A)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤ Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=> primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=> firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=> normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=> labels) (fun x=> x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hg β cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
        Z M r ell V eta tau window bw epschild A K degree)→
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
        Z M r ell V eta tau window bw epschild A K degree)→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hg pool Q (β I) Ψ m (cubicIdealGenerator I)
          (fun v U=> mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        C*Γ^2*(1+A)*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*
          Z^(r+3*ell+V+lossFinal) :=by
  obtain ⟨w₁₁,w₁₂,w₂₁,w₂₂,af₁,bf₁,af₂,bf₂,window,bw,haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hew,he⟩:=
    original_two_pass_energy om a b ha hs Lcap eta tau saving em ed hcap hb heta heta1 htau htau1 hem hed K
  refine ⟨w₁₁,w₁₂,w₂₁,w₂₂,af₁,bf₁,af₂,bf₂,window,bw,haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hew,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨C,Cz,Ct,hC,hCz,hCt,he⟩:=he epsFirst epsSecond hepsF hepsS degree
  refine ⟨C+Cz+Ct,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights
    Z M r ell V Γ theta pi epschild A loss lossFinal hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap
    hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hparent hprincipal hretained htail
    hΨ hΓ hA hsf hn hβ hlabels hslots hweights mark Y cutoff W source keys hl hr'
  have hall:=he p hp hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights
    Z M r ell V Γ theta pi epschild A loss hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap
    hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hΨ hΓ hA hsf hn hβ hlabels hslots hweights hl hr'
  exact hall.trans (two_pass_scalar C Cz Ct Γ A Z (r+3*ell+V) M r ell eta tau pi epsFirst loss Lcap saving lossFinal
    ((1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))) hC hCz hCt hA (by linarith)
    (one_le_pow₀ (by linarith [norm_nonneg theta])) hparent hprincipal hretained htail)

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform InverseMomentFirstLabelCell
open InverseMomentFirstSecondHeightCost
open InverseAmbientProfileTower JointLogSeparation JointLogSeparation CompletedHeight
open Eisenstein (ringComplex)
local notation "O"=> Eisenstein.O

theorem actual_long_parent_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0< a)(hs:Function.support om⊆Set.Icc a b)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤ Lcap)(hb:0≤ b)
    (heta:0≤ eta)(heta1:eta≤1)(htau:0< tau)(htau1:tau≤1)
    (hem:0< em)(hed:0< ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0< af₁ ∧ af₁≤ bf₁ ∧ 0< af₂ ∧ af₂≤ bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤ bw ∧ b≤ bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0< epsFirst→0< epsSecond→∀degree:ℕ,
      ∃Ccoef C:ℝ,0< Ccoef ∧ 0≤ C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=> Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (Ψ:O→*ℂ)(m mCoef:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V H₀ ξ pi epschild A loss lossFinal:ℝ)
      (_hZ:2≤ Z)(_hbin:2≤ Z^eta)(_hbinExp:Real.exp 1≤ Z^eta)(_hM:0≤ M)(_hF:r+3*ell+V≤ Lcap)(_hMcap:M≤ Lcap)(_hell:0≤ ell)(_hV:0≤ V)(_hr: -eta≤ r)
      (_hbZ:b≤ Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQlo:∀v∈Q,Z^ell≤‖ringComplex (primeProduct p v.support v)‖^2)
      (_hQhi:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Real.exp 1*Z^ell)
      (_hrcap:r≤ Lcap)(_hellcap:ell≤ Lcap)

      (_hVcap:V≤ Lcap)(_hwin:Real.exp window≤ Z^eta)(_hpi:0≤ pi)(_hpieta:6*eta≤ pi)
      (_hemcost:em*(20*(3*Lcap+16)+30)≤ pi/4)(_hedcost:ed*(20*(3*Lcap+16)+30)≤ pi/4)
      (_hechild:0≤ epschild)(_hsave: -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+epsSecond)
      (_hloss:48*eta+tau+pi+epschild+epsSecond≤ loss)(_hcard:slots.card≤ K)
      (_hparent:M-ell≤ r+3*ell+V)
      (_hprincipal:3*eta+epsFirst*(5*ell+2*r+7*eta)≤ lossFinal)
      (_hretained:loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤ lossFinal)
      (_htail: -saving≤ r+3*ell+V+lossFinal)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hA:0≤ A)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤ Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=> primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=> firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=> normTwistedSource om ξ (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=> labels) (fun x=> x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hg (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
        Z M r ell V eta tau window bw epschild A K degree)→
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
        Z M r ell V eta tau window bw epschild A K degree)→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hg pool Q ((actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) I) Ψ m (cubicIdealGenerator I)
          (fun v U=> mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*(1+‖ξ‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*
          Z^(r+3*ell+V+lossFinal) := by
  obtain ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,he⟩:=
    original_two_pass_parent_energy om a b ha hs Lcap eta tau saving em ed hcap hb heta heta1 htau htau1 hem hed K
  refine ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Ccoef,hCcoef,hcoef⟩:=actualLongCoefficient_uniform epsFirst hepsF
  obtain ⟨C,hC,hfull⟩:=he epsFirst epsSecond hepsF hepsS degree
  refine ⟨Ccoef,C,hCcoef,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels Ψ m mCoef slots lists weights
    Z M r ell V H₀ ξ pi epschild A loss lossFinal hZ hbin hbinExp hM hF hMcap hell hV hr hbZ hQpool hQlo hQhi
    hrcap hellcap hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hparent hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights mark Y cutoff W source keys hleft hright
  have hz:0< Z:=by linarith
  have hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ Z^(ell+eta) := by
    intro v hv
    apply (hQhi v hv).trans
    calc
      Real.exp 1*Z^ell≤ Z^eta*Z^ell:=mul_le_mul_of_nonneg_right hbinExp (Real.rpow_nonneg hz.le _)
      _=Z^(ell+eta):=by rw [Real.rpow_add hz];ring
  have hβ:∀I∈labels,∀v∈Q,
      ‖actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ I v‖≤ Ccoef*(Real.exp 1*Z^ell)^epsFirst := by
    intro I hI v hv
    exact hcoef p hp Ψ hΨ mCoef H₀ (Z^ell) ξ I v (Real.rpow_pos_of_pos hz _) (hQlo v hv) (hQhi v hv)
  exact hfull p hp hg hinj hcop hc hpr pool Q labels
    (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) Ψ m slots lists weights
    Z M r ell V (Ccoef*(Real.exp 1*Z^ell)^epsFirst) ξ pi epschild A loss lossFinal hZ hbin hM hF hMcap hell hV hr hbZ
    hQpool hQ hrcap hellcap hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hparent hprincipal hretained htail
    hΨ (by positivity) hA hsf hn hβ hlabels hslots hweights hleft hright

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks
open InverseMomentFirstOriginalProfile CompletedHeight
local notation "O"=> Eisenstein.O

def actualLongSourceKeys {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Ψ:O→*ℂ)(m mCoef:O)
    (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)(om:ℝ→ℂ)
    (Z M r ell V H₀ ξ Lcap eta tau:ℝ) :=
  let mark:=fun v U=> primeMark slots lists weights (v.support∪U)
  let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>
    firstDyadicRadius p q C D Z M r ell V eta tau
  let W:=fun y=> normTwistedSource om ξ (y/Z^r)
  let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=> labels)
    (fun x=> x.1) (Z^(2*Lcap+15*eta+tau))
  liveJointKeys p source pool (sourceSummand p hp hg
    (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) cutoff Ψ m mark W rowMajorant (Z^M))

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open MeasureTheory Eisenstein CompletedGauss CanonicalRowCompletion 
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open JointLogSeparation JointLogSeparation
local notation "O"=> Eisenstein.O

theorem actual_marked_bin_uniform_test
    (a₀ b₀:ℝ)(ha₀:0< a₀)(hb₀:0≤ b₀)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤ Alog)
    (hone:∀x,|x|≤ CanonicalCubeSeparation.columnWindowRadius a₀ b₀ → Vlog x=1)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤ Lcap)
    (heta:0≤ eta)(heta1:eta≤1)(htau:0< tau)(htau1:tau≤1)
    (hem:0< em)(hed:0< ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0< af₁ ∧ af₁≤ bf₁ ∧ 0< af₂ ∧ af₂≤ bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ → ℂ) ∧ HasCompactSupport (ω₁₂:ℝ → ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂₂:ℝ → ℂ) ∧
      tsupport (ω₁₁:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤ bw ∧ Real.exp Alog≤ bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0< epsFirst → 0< epsSecond → ∀degree:ℕ,
      ∃Ccoef C:ℝ,0< Ccoef ∧ 0≤ C ∧
    ∀(test:ℝ → ℂ)(hs₀:Function.support test⊆Set.Icc a₀ b₀)(hTest:ContDiff ℝ ∞ test),
    ∀{σ:Type}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(hSp:∀P∈S,Prime P),
      let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D;
      let hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D hbad;
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
        fun i=> by rw [poolPrimary_span F hF i];infer_instance;
      let p:=poolPrimary F;
      let hp:=poolPrimary_ne_zero F hF;
      let hcop:=poolPrimary_coprime F hF;
      let hg:=poolPrimary_good F hF;
      let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      ∀(Q:Finset (primePool F →₀ ℕ))(labels:Finset (Ideal O))(Ψ:O →* ℂ)(m:O)
        (slots:Finset σ)(lists:σ → Finset (primePool F))(weights:σ → primePool F → ℂ)
        (Z M r ell V H₀ pi epschild A loss lossFinal:ℝ),
        2≤ Z → 2≤ Z^eta → Real.exp 1≤ Z^eta → 0≤ M → r+3*ell+V≤ Lcap → M≤ Lcap →
        0≤ ell → 0≤ V → -eta≤ r → Real.exp Alog≤ Z^eta →
        (∀v∈Q,Z^ell≤(Ideal.absNorm (cubeIdeal F v):ℝ)) →
        (∀v∈Q,(Ideal.absNorm (cubeIdeal F v):ℝ)≤ Real.exp 1*Z^ell) →
        r≤ Lcap → ell≤ Lcap → V≤ Lcap → Real.exp window≤ Z^eta → 0≤ pi → 6*eta≤ pi →
        em*(20*(3*Lcap+16)+30)≤ pi/4 → ed*(20*(3*Lcap+16)+30)≤ pi/4 →
        0≤ epschild → -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+epsSecond →
        48*eta+tau+pi+epschild+epsSecond≤ loss → slots.card≤ K →
        M-ell≤ r+3*ell+V → 3*eta+epsFirst*(5*ell+2*r+7*eta)≤ lossFinal →
        loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤ lossFinal → -saving≤ r+3*ell+V+lossFinal →
        (∀u,‖Ψ u‖≤1) → 0≤ A → (∀I∈labels,Squarefree I) → (∀I∈labels,I≠0) →
        (∀I∈labels,(Ideal.absNorm I:ℝ)≤ Z^(V+eta)) →
        (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) →
        b₀*Z^(r+3*ell)≤ D →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
            Z M r ell V eta tau window bw epschild A K degree) →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
            Z M r ell V eta tau window bw epschild A K degree) →
        Z^(-V)*rowFamilyEnergy labels (fun I z=> markedReopenedCubeBin S D Q Ψ m (cubicIdealGenerator I) z
          test (Z^(r+3*ell)) H₀ slots lists weights) (Z^M)≤
          C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*Z^(r+3*ell+V+lossFinal)*
            (∫ξ:ℝ,‖reopeningCoefficient test a₀ b₀ ha₀ hs₀ hTest ξ‖*(1+|ξ|)^(InverseClippingProfiles.momentOrder (firstDegree degree)))^2 := by
  let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox
  have hs:Function.support om⊆Set.Icc (Real.exp (-Alog)) (Real.exp Alog):=
    fun x hx=> radialFromLog_support Vlog (Vlog.smooth ⊤) Alog hbox x hx
  obtain ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,he⟩:=
    actual_long_parent_energy om (Real.exp (-Alog)) (Real.exp Alog) (Real.exp_pos _) hs
      Lcap eta tau saving em ed hcap (Real.exp_pos _).le heta heta1 htau htau1 hem hed K
  refine ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Ccoef,C,hCcoef,hC,hparent⟩:=he epsFirst epsSecond hepsF hepsS degree
  let d:=InverseClippingProfiles.momentOrder (firstDegree degree)
  refine ⟨Ccoef,C,hCcoef,hC,?_⟩
  intro test hs₀ hTest
  let moment:ℝ:=∫ξ:ℝ,‖reopeningCoefficient test a₀ b₀ ha₀ hs₀ hTest ξ‖*(1+|ξ|)^d
  intro σ _ S D hbad hSp
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=> by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  intro Q labels Ψ m slots lists weights Z M r ell V H₀ pi epschild A loss lossFinal
    hZ hbin hbinExp hM hFcap hMcap hell hV hr hbZ hQlo hQhi hrcap hellcap hVcap hwin
    hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights hD hleft hright
  have hz:0< Z:=by linarith
  have hg' : ∀i:primePool F,lambda∉Ideal.span {poolPrimary F i}:=poolPrimary_good F hF
  have hinj:Function.Injective (fun i:primePool F=> Ideal.span {poolPrimary F i}) := by
    intro i j hij
    exact Subtype.ext (by simpa only [poolPrimary_span F hF] using hij)
  have hpr (i:primePool F):lambda^2∣poolPrimary F i-1:=
    (primaryIdealPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2
  let Gamma:=Ccoef*(Real.exp 1*Z^ell)^epsFirst
  let E:=C*Gamma^2*(1+A)*Z^(r+3*ell+V+lossFinal)
  have hE:0≤ E:=by dsimp [E];positivity
  refine (actual_long_bin_normalized_energy S D hbad hSp Q labels Ψ m test a₀ b₀ ha₀ hb₀ hs₀ hTest
    Vlog hone Z r ell V H₀ (Z^M) E d hz hD (Real.rpow_pos_of_pos hz _) hE hQlo hQhi slots lists weights ?_).trans_eq ?_
  · intro ξ
    have hbnd:=hparent (poolPrimary F) (poolPrimary_ne_zero F hF) hg' hinj
      (poolPrimary_coprime F hF) (poolPrimary_odd F hF) hpr Finset.univ Q labels Ψ m (m*excludedGenerator S)
      slots lists weights Z M r ell V H₀ ξ pi epschild A loss lossFinal
      hZ hbin hbinExp hM hFcap hMcap hell hV hr hbZ (fun _ _=> Finset.subset_univ _)
      (by intro v hv;rw [cubeIdeal_primeProduct_norm F hF];exact hQlo v hv)
      (by intro v hv;rw [cubeIdeal_primeProduct_norm F hF];exact hQhi v hv)
      hrcap hellcap hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
      hΨ hA hsf hn hlabels hslots hweights (hleft ξ) (hright ξ)
    have hc (I:Ideal O) := funext (actualLongCoefficient_complete S D hbad Ψ m H₀ (Z^ell) ξ I)
    have hrow: (fun I z=> varyingReopenedRow (poolPrimary F) hg' Finset.univ Q
        (separatedCubeCoefficient (fun v=> reopenedCubeCoefficient H₀
          (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) 1) (cubeIdeal F v))
          (fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)) (Z^ell) ξ) Ψ m (cubicIdealGenerator I)
        (fun v T=> primeMark slots lists weights (T∪v.support)*frequencyTwist Vlog ξ (columnLog (poolPrimary F) (Z^r) T)) z)=
      (fun I z=> varyingReopenedRow (poolPrimary F) hg' Finset.univ Q
        (separatedCubeCoefficient (fun v=> reopenedCubeCoefficient H₀
          (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) 1) (cubeIdeal F v))
          (fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)) (Z^ell) ξ) Ψ m (cubicIdealGenerator I)
        (fun v T=> primeMark slots lists weights (v.support∪T)*normTwistedSource om ξ (primeProductNorm (poolPrimary F) T/Z^r)) z) := by
      funext I z
      exact long_marked_source_eq (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        hg' Finset.univ Q _ Ψ m (cubicIdealGenerator I) z slots lists weights Vlog Alog hbox Z r ξ hz
    rw [hrow]
    convert hbnd using 1
    · apply congrArg (fun f => Z^(-r-2*ell-V)*rowFamilyEnergy labels f (Z^M))
      funext I z
      exact congrArg (fun coeff => varyingReopenedRow (poolPrimary F) hg' Finset.univ Q coeff Ψ m (cubicIdealGenerator I)
        (fun v T => primeMark slots lists weights (v.support∪T)*normTwistedSource om ξ
          (primeProductNorm (poolPrimary F) T/Z^r)) z) (hc I).symm
    · dsimp [E,Gamma,d]
      try simp only [Real.norm_eq_abs]
      ring
  · dsimp [E,Gamma,moment]

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
namespace InverseMoment
open MeasureTheory CanonicalCubeSeparation JointLogSeparation JointLogSeparation CompletedHeight

theorem reopening_coefficient_twist (W:ℝ→ℂ)(a b:ℝ)(ha:0< a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(theta:ℝ)
    (hT:ContDiff ℝ ∞ (normTwistedSource W theta)):
    reopeningCoefficient (normTwistedSource W theta) a b ha
      ((normTwistedSource_support W theta).trans hs) hT=
      𝓕 (frequencyTwist (sourceLogProfile W a b ha hs hW) theta) :=by
  unfold reopeningCoefficient
  congr 1
  ext x
  simp only [sourceLogProfile_apply,frequencyTwist_apply,normTwistedSource,Real.log_exp]

theorem reopening_twisted_moment (W:ℝ→ℂ)(a b:ℝ)(ha:0< a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(J:ℕ):
    ∃C:ℝ,0≤ C ∧ ∀theta:ℝ,∀hT:ContDiff ℝ ∞ (normTwistedSource W theta),
      (∫ξ:ℝ,‖reopeningCoefficient (normTwistedSource W theta) a b ha
        ((normTwistedSource_support W theta).trans hs) hT ξ‖*(1+|ξ|)^J)≤
      C*(1+‖theta‖)^(J+(volume:Measure ℝ).integrablePower) :=by
  obtain ⟨C,hC,he⟩:=frequencyTwist_fourier_moment J (sourceLogProfile W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro theta hT
  rw [reopening_coefficient_twist W a b ha hs hW theta hT]
  simpa only [Real.norm_eq_abs,mul_comm] using he theta

theorem reopening_twisted_moment_squared (W:ℝ→ℂ)(a b:ℝ)(ha:0< a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(J:ℕ):
    ∃C:ℝ,0≤ C ∧ ∀theta:ℝ,∀hT:ContDiff ℝ ∞ (normTwistedSource W theta),
      (∫ξ:ℝ,‖reopeningCoefficient (normTwistedSource W theta) a b ha
        ((normTwistedSource_support W theta).trans hs) hT ξ‖*(1+|ξ|)^J)^2≤
      C*(1+‖theta‖)^(2*(J+(volume:Measure ℝ).integrablePower)) :=by
  obtain ⟨C,hC,he⟩:=reopening_twisted_moment W a b ha hs hW J
  refine ⟨C ^ 2,sq_nonneg _,?_⟩
  intro theta hT
  have hh:=pow_le_pow_left₀ (integral_nonneg (fun ξ=> by positivity)) (he theta hT) 2
  simpa only [mul_pow,←pow_mul,Nat.mul_comm] using hh

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open MeasureTheory Eisenstein CompletedGauss CanonicalRowCompletion 
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open JointLogSeparation JointLogSeparation
local notation "O"=> Eisenstein.O

theorem actual_marked_bin_height
    (a₀ b₀:ℝ)(ha₀:0< a₀)(hb₀:0≤ b₀)
    (W:ℝ→ℂ)(hsW:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤ Alog)
    (hone:∀x,|x|≤ CanonicalCubeSeparation.columnWindowRadius a₀ b₀ → Vlog x=1)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤ Lcap)
    (heta:0≤ eta)(heta1:eta≤1)(htau:0< tau)(htau1:tau≤1)
    (hem:0< em)(hed:0< ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0< af₁ ∧ af₁≤ bf₁ ∧ 0< af₂ ∧ af₂≤ bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ → ℂ) ∧ HasCompactSupport (ω₁₂:ℝ → ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂₂:ℝ → ℂ) ∧
      tsupport (ω₁₁:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤ bw ∧ Real.exp Alog≤ bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0< epsFirst → 0< epsSecond → ∀degree:ℕ,
      ∃Ccoef C:ℝ,0< Ccoef ∧ 0≤ C ∧
    ∀theta:ℝ,
    ∀{σ:Type}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(hSp:∀P∈S,Prime P),
      let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D;
      let hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D hbad;
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
        fun i=> by rw [poolPrimary_span F hF i];infer_instance;
      let p:=poolPrimary F;
      let hp:=poolPrimary_ne_zero F hF;
      let hcop:=poolPrimary_coprime F hF;
      let hg:=poolPrimary_good F hF;
      let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      ∀(Q:Finset (primePool F →₀ ℕ))(labels:Finset (Ideal O))(Ψ:O →* ℂ)(m:O)
        (slots:Finset σ)(lists:σ → Finset (primePool F))(weights:σ → primePool F → ℂ)
        (Z M r ell V H₀ pi epschild A loss lossFinal:ℝ),
        2≤ Z → 2≤ Z^eta → Real.exp 1≤ Z^eta → 0≤ M → r+3*ell+V≤ Lcap → M≤ Lcap →
        0≤ ell → 0≤ V → -eta≤ r → Real.exp Alog≤ Z^eta →
        (∀v∈Q,Z^ell≤(Ideal.absNorm (cubeIdeal F v):ℝ)) →
        (∀v∈Q,(Ideal.absNorm (cubeIdeal F v):ℝ)≤ Real.exp 1*Z^ell) →
        r≤ Lcap → ell≤ Lcap → V≤ Lcap → Real.exp window≤ Z^eta → 0≤ pi → 6*eta≤ pi →
        em*(20*(3*Lcap+16)+30)≤ pi/4 → ed*(20*(3*Lcap+16)+30)≤ pi/4 →
        0≤ epschild → -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+epsSecond →
        48*eta+tau+pi+epschild+epsSecond≤ loss → slots.card≤ K →
        M-ell≤ r+3*ell+V → 3*eta+epsFirst*(5*ell+2*r+7*eta)≤ lossFinal →
        loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤ lossFinal → -saving≤ r+3*ell+V+lossFinal →
        (∀u,‖Ψ u‖≤1) → 0≤ A → (∀I∈labels,Squarefree I) → (∀I∈labels,I≠0) →
        (∀I∈labels,(Ideal.absNorm I:ℝ)≤ Z^(V+eta)) →
        (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) →
        b₀*Z^(r+3*ell)≤ D →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
            Z M r ell V eta tau window bw epschild A K degree) →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
            Z M r ell V eta tau window bw epschild A K degree) →
        Z^(-V)*rowFamilyEnergy labels (fun I z=> markedReopenedCubeBin S D Q Ψ m (cubicIdealGenerator I) z
          (normTwistedSource W theta) (Z^(r+3*ell)) H₀ slots lists weights) (Z^M)≤
          C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*Z^(r+3*ell+V+lossFinal)*
            (1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower)) := by
  obtain ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,he⟩:=
    actual_marked_bin_uniform_test a₀ b₀ ha₀ hb₀ Vlog Alog hbox hone
      Lcap eta tau saving em ed hcap heta heta1 htau htau1 hem hed K
  refine ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Ccoef,C,hCcoef,hC,hbin⟩:=he epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Cm,hCm,hmoment⟩:=reopening_twisted_moment_squared W a₀ b₀ ha₀ hsW hW
    (InverseClippingProfiles.momentOrder (firstDegree degree))
  refine ⟨Ccoef,C*Cm,hCcoef,mul_nonneg hC hCm,?_⟩
  intro theta σ _ S D hbad hSp
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=> by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  intro Q labels Ψ m slots lists weights Z M r ell V H₀ pi epschild A loss lossFinal
    hZ hbins hbinExp hM hFcap hMcap hell hV hr hbZ hQlo hQhi hrcap hellcap hVcap hwin
    hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights hD hleft hright
  have hT:=CanonicalRowCompletion.normTwistedSource_contDiff W a₀ b₀ ha₀ hsW hW theta
  have hsT:Function.support (normTwistedSource W theta)⊆Set.Icc a₀ b₀:=
    (normTwistedSource_support W theta).trans hsW
  have hbnd:=hbin (normTwistedSource W theta) hsT hT S D hbad hSp
    Q labels Ψ m slots lists weights Z M r ell V H₀ pi epschild A loss lossFinal
    hZ hbins hbinExp hM hFcap hMcap hell hV hr hbZ hQlo hQhi hrcap hellcap hVcap hwin
    hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights hD hleft hright
  have hz:0< Z:=by linarith
  apply hbnd.trans
  calc
    _ ≤ C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*Z^(r+3*ell+V+lossFinal)*
        (Cm*(1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+
          (volume:Measure ℝ).integrablePower))) :=
      mul_le_mul_of_nonneg_left (hmoment theta hT) (by positivity)
    _ = _ := by ring

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein CompletedGauss  CanonicalQuadraticSieve
open CanonicalRowCompletion FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstChildWindows
local notation "O"=> Eisenstein.O

theorem actual_live_bin_rank_children
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Z N V M cutoff eta L b window bW Qwidth z c eps A Mnext Fnext cnext tau:ℝ)
    (j:ℕ)(hZ:1< Z)(hL:1≤ L)(heta:0≤ eta)(heta1:eta≤1)
    (hcut:0< cutoff)(hsmall:eta≤ cutoff/32)(hV:0≤ V)(hparentcap:N+V≤ L)
    (hbW:bW≤ Z^eta)(hlog:1≤ eta*Real.log Z)(hexp:Real.exp 1≤ Z^eta)
    (hbin:2≤ Z^eta)(hb:1≤ b)(hbt:b≤ Z^(6*eta))(hwindow:Real.exp window≤ Z^(4*eta))
    (hne:(progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D bW (Z^N) j)).Nonempty)
    (base Ψ:O→*ℂ)(hΨ:CanonicalCoefficientClass.IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (hparent:CanonicalMargins (N+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤ Z^Qwidth)
    (hMc:M-3*(cutoff/2)/2≤ Mnext)(hFc:N+V+15*eta≤ Fnext)(hcc:cnext≤ c-7*eta)
    {σ:Type}[DecidableEq σ](slots:Finset σ)
    (lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)→ℂ)
    (ω₁ ω₂:𝓢(ℝ,ℂ))(K degree:ℕ):
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D;
    let hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hF i];infer_instance;
    CanonicalRankMoments (poolPrimary F)
      (poolPrimary_good F hF) Finset.univ base slots lists a ω₁ Z Mnext Fnext z cnext eps A K degree →
    CanonicalRankMoments (poolPrimary F)
      (poolPrimary_good F hF) Finset.univ base slots lists a ω₂ Z Mnext Fnext z cnext eps A K degree →
    ∀k:SourceIndex,∀l jj:ℕ,∀negative:Bool,
      ChildBounds (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ
        (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D bW (Z^N) j))
        k l jj negative Ψ m slots lists a ω₁ ω₂
        Z M (N-3*actualCubeLength Z j) (actualCubeLength Z j) V eta tau window b eps A K degree :=by
  dsimp only
  intro h₁ h₂ k l jj negative
  let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
  have hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D hbad
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hF i];infer_instance
  obtain ⟨hel,hr,hrL,helL,hFL,hgap,hqn⟩:=actual_long_bin_geometry S D hbad bW Z N V cutoff eta L j
    hZ hL heta1 hV hparentcap hbW hlog hne
  have hs:(N-3*actualCubeLength Z j)+3*actualCubeLength Z j+V=N+V:=by ring
  apply canonical_rank_cap_children (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_odd F hF)
    (fun i=>(primaryIdealPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2)
    Finset.univ _ k l jj negative base Ψ hΨ m hm slots lists a ω₁ ω₂
    Z M _ _ V eta tau window b (cutoff/2) Qwidth z c eps A Mnext Fnext cnext K degree
    hZ heta hbin hel hV hb hbt hwindow (by linarith) (by linarith) (by linarith)
    (by simpa only [hs] using hparent) hpuncture ?_ hMc (by simpa only [hs] using hFc) hcc h₁ h₂
  intro v hv
  apply (hqn v hv).2.trans
  calc
    _≤ Z^eta*Z^(actualCubeLength Z j):=mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg (by linarith) _)
    _=Z^(actualCubeLength Z j+eta):=by rw [Real.rpow_add (by linarith : 0< Z)];ring

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein CompletedGauss CanonicalRowCompletion 
open CanonicalQuadraticSieve InverseReflectedPhase InverseTerminalWidths CompletedHeight
open InverseCanonicalShortAttachment InverseSecondFibers FirstPassCubeLabels SecondPassArithmetic
local notation "O"=> Eisenstein.O
universe v

theorem actual_complete_state_from_live_bins
    (lo hi:ℝ)(hlo:0< lo)(hhi:0≤ hi)(W:ℝ→ℂ)
    (hWs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (L cstar eta eps:ℝ)(hL:0≤ L)(hcstar:0< cstar)(heta:0< eta)
    (heta1:eta≤1)(hetac:eta≤ cstar/100000)(heps:0< eps)(rmax K:ℕ) :
    ∃degree:ℕ,∀(q:ℕ)(_hq:q≠0),∃C Z₀:ℝ,0< C ∧ 1< Z₀ ∧
    ∀{σ:Type v}[DecidableEq σ](m:O),m≠0 → ∀Z N V M z₀ margin cutoff:ℝ,
      Z₀≤ Z → 0≤ N → N≤ L → 0≤ V → V≤ L → 0≤ M → M≤ L → z₀≤ L →
      0≤ cutoff → cutoff≤ L → cutoff≤ cstar/200 →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤ Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
    ∀labels:Finset (Ideal O),(∀I∈labels,Supported I ∧ Squarefree I ∧ (I.absNorm:ℝ)≤ Z^V) →
    ∀D:ℕ,hi*Z^N≤ D → ∀slots:Finset σ,slots.card≤ rmax →
    ∀(lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))(H:σ→ℝ),
      (slots:Set σ).Pairwise (fun i j=> Disjoint (lists i) (lists j)) →
      (∀i∈slots,1≤ H i) → (∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤ H i) → (∏i∈slots,H i)≤ Z^z₀ →
    ∀(Ψ:O→*ℂ),(∀u,‖Ψ u‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀(theta:ℝ)(a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1) → ∀E:ℝ,0≤ E →
      let S:=reflectionExcludedPrimes q;
      let test:=normTwistedSource W theta;
      (∀j∈cubeLogRange hi (Z^N),
        (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j)).Nonempty →
        Z^(-V)*rowFamilyEnergy labels (fun I z=> markedReopenedCubeBin S D
          (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j))
          Ψ m (cubicIdealGenerator I) z test (Z^N) (Z^(cutoff-V)) slots lists a) (Z^M)≤ E) →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
        ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (cubicIdealGenerator I) z
          slots lists a test (Z^N)‖^2)≤
      C*((1+‖theta‖)^degree*Z^(N+V-cstar/256)+Z^eps*E) := by
  obtain ⟨degree,hs⟩:=actual_complete_short_finite_uniform_degree lo hi hlo W hWs hW L cstar eta
    hL hcstar heta heta1 hetac rmax K
  obtain ⟨Cl,hCl,hl⟩:=actual_complete_energy_from_live_bins K hi L eps hhi hL heps
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨Cs,Z₀,hCs,hZ₀,hshort⟩:=hs q hq
  refine ⟨2*Cs+Cl,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin cutoff hZ hN hNL hV hVL hM hML hzL hcut hcutL hcutc
    hmN hmargin hreserve labels hlabels D hD slots hcard lists H hdis hH1 hH hprod Ψ hΨ hperiod theta a ha E hE
  dsimp only
  intro hbins
  have hz:0< Z:=zero_lt_one.trans (lt_of_lt_of_le hZ₀ hZ)
  have hZ1:1≤ Z:=(hZ₀.trans_le hZ).le
  let S:=reflectionExcludedPrimes q
  let test:=normTwistedSource W theta
  let mark:=indexedIdealMark (fun i:primePool (CanonicalRowCompletion.outsideSquarefreeIdeals S D)=> i.val) slots lists a
  have htest:HasCompactSupport test:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((normTwistedSource_support W theta).trans hWs)
  have hupper:∀x,test x≠0 → x≤ hi:=fun x hx=>(hWs (normTwistedSource_support W theta hx)).2
  have hT:∀z∈nonzeroChildFrequencyBall 1 (Z^M),z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤ Z^M := by
    intro z hz
    have hh:=(mem_nonzeroChildFrequencyBall 1 one_ne_zero (Z^M) z).mp hz
    constructor
    · intro he
      simp only [he,mul_zero,map_zero,norm_zero,pow_succ,lt_self_iff_false] at hh
      exact hh.1
    · rw [←ringComplex_norm_sq_eq_absNorm_span]
      simpa only [one_mul] using hh.2
  have hshortbound:Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
      ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) z)
        test (Z^N) (Z^(cutoff-V)) mark‖^2)≤ Cs*(1+‖theta‖)^degree*Z^(N+V-cstar/256) := by
    by_cases hbig:cutoff≤ V
    · have he (I:Ideal O)(z:O):markedShortCompletedSum
          (rowTwist Ψ (m*excludedGenerator S) (cubicIdealGenerator I) z) test (Z^N) (Z^(cutoff-V)) mark=0:=
        short_sum_zero_of_label_large _ _ _ _ _ _ _ hZ1 hbig
      simp only [he,norm_zero,zero_pow (by decide:2≠0),Finset.sum_const_zero,mul_zero]
      positivity
    · exact hshort m hm Z N V M z₀ margin (cutoff-V) cutoff hZ hN hV hM hML hVL hzL
        (by linarith) (by linarith) hmN hmargin hreserve (by linarith) (by linarith) hcutc
        labels (fun I hI => by
          have hn := (admissible_iff_native I).mp
            ⟨(hlabels I hI).1.1, (hlabels I hI).2.1, (hlabels I hI).1.2⟩
          exact ⟨⟨hn.1, hn.2.2⟩, (hlabels I hI).2⟩) (nonzeroChildFrequencyBall 1 (Z^M)) hT D hD slots hcard lists H
        hdis hH1 hH hprod Ψ hΨ hperiod theta a ha
  have hb:=hl S D (reflectionExcludedPrimes_bad q) (reflectionExcludedPrimes_prime q) labels
    (fun I hI=>(hlabels I hI).1.1) Ψ m slots lists a test htest Z N V (Z^M)
    (Z^(cutoff-V)) (Cs*(1+‖theta‖)^degree*Z^(N+V-cstar/256)) E
    hZ1 (Real.rpow_pos_of_pos hz _) hNL hVL (fun I hI=>(hlabels I hI).2.2)
    hupper hD hE hshortbound hbins
  apply hb.trans
  have hA:0≤(1+‖theta‖)^degree*Z^(N+V-cstar/256):=by positivity
  have hB:0≤ Z^eps*E:=by positivity
  nlinarith

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment

theorem actual_long_coefficient_cost (Z ell L epsilon Ccoef:ℝ)
    (hZ:1≤ Z)(hell:ell≤ L)(heps:0≤ epsilon):
    (Ccoef*(Real.exp 1*Z^ell)^epsilon)^2≤
      Ccoef^2*Real.exp (2*epsilon)*Z^(2*L*epsilon) := by
  have hz:0< Z:=zero_lt_one.trans_le hZ
  have hex:(Real.exp 1)^epsilon=Real.exp epsilon:=by rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,one_mul]
  have hex2:(Real.exp epsilon)^2=Real.exp (2*epsilon):=by rw [←Real.exp_nat_mul];norm_num
  have hid:(Ccoef*(Real.exp 1*Z^ell)^epsilon)^2=
      Ccoef^2*Real.exp (2*epsilon)*Z^(2*ell*epsilon) := by
    rw [Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg hz.le _),hex,
      ←Real.rpow_mul hz.le,mul_pow,mul_pow,hex2,
      ←Real.rpow_mul_natCast hz.le]
    ring_nf
  rw [hid]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  nlinarith

theorem actual_long_uniform_parent_cost (Z ell N V L epsilon Ccoef C A loss:ℝ)
    (hZ:1≤ Z)(hell:ell≤ L)(heps:0≤ epsilon)(hC:0≤ C)(hA:0≤ A):
    C*(Ccoef*(Real.exp 1*Z^ell)^epsilon)^2*(1+A)*Z^((N-3*ell)+3*ell+V+loss)≤
      (C*Ccoef^2*Real.exp (2*epsilon))*(1+A)*Z^(N+V+loss+2*L*epsilon) := by
  have hz:0< Z:=zero_lt_one.trans_le hZ
  have h:=actual_long_coefficient_cost Z ell L epsilon Ccoef hZ hell heps
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h hC) (by linarith:0≤1+A))
    (Real.rpow_nonneg hz.le ((N-3*ell)+3*ell+V+loss))
  apply hh.trans_eq
  have hpow:Z^(2*L*epsilon)*Z^((N-3*ell)+3*ell+V+loss)=Z^(N+V+loss+2*L*epsilon):=by
    rw [←Real.rpow_add hz];congr 1;ring
  calc
    _=(C*Ccoef^2*Real.exp (2*epsilon))*(1+A)*
        (Z^(2*L*epsilon)*Z^((N-3*ell)+3*ell+V+loss)):=by ring
    _=_:=by rw [hpow]

theorem complete_state_power_absorption (Z F cstar eps loss C A height E:ℝ)
    (hZ:1≤ Z)(hc:0≤ cstar)(heps:0≤ eps)(hloss:0≤ loss)
    (hC:0≤ C)(_hA:0≤ A)(hheight:0≤ height)
    (hE:E≤ A*height*Z^(F+loss)):
    C*(height*Z^(F-cstar/256)+Z^eps*E)≤
      C*(1+A)*height*Z^(F+loss+eps) := by
  have hz:0< Z:=zero_lt_one.trans_le hZ
  have hs:height*Z^(F-cstar/256)≤ height*Z^(F+loss+eps):=by
    apply mul_le_mul_of_nonneg_left _ hheight
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have ht:Z^eps*E≤ A*height*Z^(F+loss+eps):=by
    have hh:=mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hz.le eps)
    apply hh.trans_eq
    rw [Real.rpow_add hz (F+loss) eps]
    ring
  have hh:=mul_le_mul_of_nonneg_left (add_le_add hs ht) hC
  simpa only [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, one_mul, mul_one, add_assoc, add_left_comm, add_comm] using hh

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open MeasureTheory Eisenstein CompletedGauss CanonicalRowCompletion 
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open JointLogSeparation JointLogSeparation InverseReflectedPhase InverseTerminalWidths InverseSecondFibers
local notation "O"=> Eisenstein.O

theorem actual_complete_state_from_children
    (lo hi:ℝ)(hlo:0< lo)(hhi:0≤ hi)(W:ℝ→ℂ)
    (hsW:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤ Alog)
    (hone:∀x,|x|≤ columnWindowRadius lo hi → Vlog x=1)
    (L cstar eta tau saving em ed eps:ℝ)(hL:1≤ L)(hcstar:0< cstar)(heta:0< eta)
    (heta1:eta≤1)(hetac:eta≤ cstar/100000)(htau:0< tau)(htau1:tau≤1)
    (hem:0< em)(hed:0< ed)(heps:0< eps)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ)(shortDegree:ℕ),
      0< af₁ ∧ af₁≤ bf₁ ∧ 0< af₂ ∧ af₂≤ bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤ bw ∧ Real.exp Alog≤ bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0< epsFirst → 0< epsSecond → ∀degree:ℕ,
    ∀(q:ℕ)(hq:q≠0),∃Cs Cb Z₀:ℝ,0< Cs ∧ 0≤ Cb ∧ 1< Z₀ ∧
    ∀{σ:Type}[DecidableEq σ](m:O),m≠0 →
    ∀Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta:ℝ,
      Z₀≤ Z → 2≤ Z → 2≤ Z^eta → Real.exp 1≤ Z^eta → 1≤ eta*Real.log Z →
      0≤ N → 0≤ V → 0≤ M → N+V≤ L → M≤ N+V → z₀≤ L →
      hi≤ Z^eta → Real.exp Alog≤ Z^eta → Real.exp window≤ Z^eta →
      0≤ cutoff → cutoff≤ L → cutoff≤ cstar/200 →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤ Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      0≤ pi → 6*eta≤ pi → em*(20*(3*L+16)+30)≤ pi/4 → ed*(20*(3*L+16)+30)≤ pi/4 →
      0≤ epschild → -saving≤48*eta+tau+pi+epschild+epsSecond →
      48*eta+tau+pi+epschild+epsSecond≤ loss →
      3*eta+epsFirst*(2*L+7*eta)≤ lossFinal →
      loss+(2*L+15*eta+tau)*epsFirst+epsFirst≤ lossFinal → -saving≤ lossFinal →
      0≤ A →
    ∀labels:Finset (Ideal O),(∀I∈labels,Supported I ∧ Squarefree I ∧ (I.absNorm:ℝ)≤ Z^V) →
    ∀D:ℕ,hi*Z^N≤ D → ∀slots:Finset σ,slots.card≤ K →
    ∀(lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))(H:σ→ℝ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,1≤ H i) → (∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤ H i) → (∏i∈slots,H i)≤ Z^z₀ →
    ∀(Ψ:O→*ℂ),(∀u,‖Ψ u‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ,
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1) →
      let S:=reflectionExcludedPrimes q;
      let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D;
      let hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q);
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hF i];infer_instance;
      let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      (∀j∈cubeLogRange hi (Z^N),
        let ell:=actualCubeLength Z j;
        let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j);
        Q.Nonempty → ∀ξ:ℝ,∀k∈actualLongSourceKeys (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists a om Z M (N-3*ell) ell V (Z^(cutoff-V)) ξ L eta tau,
          ChildBounds (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) Finset.univ Q k.1 k.2.1 k.2.2 true Ψ m slots lists a ω₁₁ ω₁₂
            Z M (N-3*ell) ell V eta tau window bw epschild A K degree) →
      (∀j∈cubeLogRange hi (Z^N),
        let ell:=actualCubeLength Z j;
        let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j);
        Q.Nonempty → ∀ξ:ℝ,∀k∈actualLongSourceKeys (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists a om Z M (N-3*ell) ell V (Z^(cutoff-V)) ξ L eta tau,
          ChildBounds (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) Finset.univ Q k.1 k.2.1 k.2.2 false Ψ m slots lists a ω₂₁ ω₂₂
            Z M (N-3*ell) ell V eta tau window bw epschild A K degree) →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
        ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (cubicIdealGenerator I) z
          slots lists a (normTwistedSource W theta) (Z^N)‖^2)≤
      Cs*(1+‖theta‖)^shortDegree*Z^(N+V-cstar/256)+
      Cb*(1+A)*(1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower))*
        Z^(N+V+lossFinal+2*L*epsFirst+eps) := by
  have hL0:0≤ L:=by linarith only [hL]
  obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hbin⟩:=
    actual_marked_bin_height lo hi hlo hhi W hsW hW Vlog Alog hbox hone L eta tau saving em ed
      hL0 heta.le heta1 htau htau1 hem hed K
  obtain ⟨ds,hstate⟩:=actual_complete_state_from_live_bins lo hi hlo hhi W hsW hW L cstar eta eps
    hL0 hcstar heta heta1 hetac heps K K
  refine ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,?_⟩
  intro epsFirst epsSecond heF heS degree q hq
  obtain ⟨Ccoef,C,hcoef,hC,hbin⟩:=hbin epsFirst epsSecond heF heS degree
  obtain ⟨Cs,Z₀,hCs,hZ₀,hstate⟩:=hstate q hq
  let Cb:=C*Ccoef^2*Real.exp (2*epsFirst)
  refine ⟨Cs,Cs*Cb,Z₀,hCs,by dsimp [Cb];positivity,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta hZ hZ2 h2 hExp hlog
    hN hV hM hFcap hMF hzcap hbZ hAZ hwin hcut hcutL hcutc hmN hmargin hreserve
    hpi hpieta hemc hedc hechild hsave hloss hprincipal hretained htail hA
    labels hlabels D hD slots hcard lists H hdis hH1 hH hprod Ψ hΨ hperiod a ha
  dsimp only
  intro hleft hright
  have hz:0< Z:=by linarith only [hZ2]
  have hZ1:1≤ Z:=by linarith only [hZ2]
  let d:=2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower)
  let E:=Cb*(1+A)*Z^(N+V+lossFinal+2*L*epsFirst)*(1+‖theta‖)^d
  have hE:0≤ E:=by dsimp [E,Cb];positivity
  have hbins:∀j∈cubeLogRange hi (Z^N),
      (progressingCubes (reflectionExcludedPrimes q) D (Z^(cutoff-V))
        (activeCubeLogBin (reflectionExcludedPrimes q) D hi (Z^N) j)).Nonempty →
      Z^(-V)*rowFamilyEnergy labels (fun I z=> markedReopenedCubeBin (reflectionExcludedPrimes q) D
        (progressingCubes (reflectionExcludedPrimes q) D (Z^(cutoff-V))
          (activeCubeLogBin (reflectionExcludedPrimes q) D hi (Z^N) j))
        Ψ m (cubicIdealGenerator I) z (normTwistedSource W theta) (Z^N) (Z^(cutoff-V)) slots lists a) (Z^M)≤ E := by
    intro j hj hne
    let ell:=actualCubeLength Z j
    let S:=reflectionExcludedPrimes q
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D
    have hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
    let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hF i];infer_instance
    let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j)
    obtain ⟨hel,hr,hrL,helL,hFL,hgap,hqn⟩:=actual_long_bin_geometry S D (reflectionExcludedPrimes_bad q)
      hi Z N V cutoff eta L j (by linarith only [hZ2]) hL heta1 hV hFcap hbZ hlog hne
    have hsN:(N-3*ell)+3*ell=N:=by ring
    have hpr:3*eta+epsFirst*(5*ell+2*(N-3*ell)+7*eta)≤ lossFinal:=by
      have hNL:N≤ L:=by linarith only [hZ2, hL, hFcap, hMF, hN, hV, heta.le, hel, hr, hrL, helL, hFL, hgap, hsave, htail, hprincipal]
      nlinarith only [hprincipal, mul_nonneg heF.le hel, mul_le_mul_of_nonneg_left hNL heF.le]
    have hh:=hbin theta S D (reflectionExcludedPrimes_bad q) (reflectionExcludedPrimes_prime q)
      Q labels Ψ m slots lists a Z M (N-3*ell) ell V (Z^(cutoff-V)) pi epschild A loss lossFinal
      hZ2 h2 hExp hM hFL (by linarith only [hZ2, hL, hFcap, hMF, hN, hV, heta.le, hel, hr, hrL, helL, hFL, hgap, hsave, htail, hprincipal]) hel hV hr hAZ
      (by intro v hv;rw [←cubeIdeal_primeProduct_norm F hF];exact (hqn v hv).1)
      (by intro v hv;rw [←cubeIdeal_primeProduct_norm F hF];exact (hqn v hv).2)
      hrL helL (by linarith only [hZ2, hL, hFcap, hMF, hN, hV, heta.le, hel, hr, hrL, helL, hFL, hgap, hsave, htail, hprincipal]) hwin hpi hpieta hemc hedc hechild (by linarith only [hZ2, hL, hFcap, hMF, hN, hV, heta.le, hel, hr, hrL, helL, hFL, hgap, hsave, htail, hprincipal]) hloss hcard
      (by linarith only [hZ2, hL, hFcap, hMF, hN, hV, heta.le, hel, hr, hrL, helL, hFL, hgap, hsave, htail, hprincipal]) hpr hretained (by linarith only [hZ2, hL, hFcap, hMF, hN, hV, heta.le, hel, hr, hrL, helL, hFL, hgap, hsave, htail, hprincipal]) hΨ hA
      (fun I hI=>(hlabels I hI).2.1) (fun I hI=>(hlabels I hI).1.1)
      (fun I hI=>((hlabels I hI).2.2).trans (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith only [hZ2, hL, hFcap, hMF, hN, hV, heta.le, hel, hr, hrL, helL, hFL, hgap, hsave, htail, hprincipal])))
      hdis ha (by simpa only [hsN] using hD) (hleft j hj hne) (hright j hj hne)
    rw [hsN] at hh
    apply hh.trans
    have hc:=mul_le_mul_of_nonneg_right
      (actual_long_uniform_parent_cost Z ell N V L epsFirst Ccoef C A lossFinal hZ1 helL heF.le hC hA)
      (show 0≤(1+‖theta‖)^d by positivity)
    simpa only [hsN] using hc
  have hs:=hstate m hm Z N V M z₀ margin cutoff hZ hN (by linarith only [hFcap, hV]) hV (by linarith only [hFcap, hN]) hM (by linarith only [hMF,hFcap])
    hzcap hcut hcutL hcutc hmN hmargin hreserve labels hlabels D hD slots hcard lists H
    hdis hH1 hH hprod Ψ hΨ hperiod theta a ha E hE hbins
  apply hs.trans_eq
  dsimp only [E,d]
  rw [Real.rpow_add hz (N+V+lossFinal+2*L*epsFirst) eps]
  ring

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open MeasureTheory Eisenstein CompletedGauss CanonicalRowCompletion 
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open JointLogSeparation JointLogSeparation InverseReflectedPhase InverseTerminalWidths InverseSecondFibers
local notation "O"=> Eisenstein.O

theorem actual_complete_state_from_rank_moments
    (lo hi:ℝ)(hlo:0< lo)(hhi:0≤ hi)(W:ℝ→ℂ)
    (hsW:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤ Alog)
    (hone:∀x,|x|≤ columnWindowRadius lo hi → Vlog x=1)
    (L cstar eta tau saving em ed eps:ℝ)(hL:1≤ L)(hcstar:0< cstar)(heta:0< eta)
    (heta1:eta≤1)(hetac:eta≤ cstar/100000)(htau:0< tau)(htau1:tau≤1)
    (hem:0< em)(hed:0< ed)(heps:0< eps)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ)(shortDegree:ℕ),
      0< af₁ ∧ af₁≤ bf₁ ∧ 0< af₂ ∧ af₂≤ bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤ bw ∧ Real.exp Alog≤ bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0< epsFirst → 0< epsSecond → ∀degree:ℕ,
    ∀(q:ℕ)(hq:q≠0),∃Cs Cb Z₀:ℝ,0< Cs ∧ 0≤ Cb ∧ 1< Z₀ ∧
    ∀{σ:Type}[DecidableEq σ](m:O),m≠0 →
    ∀Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta:ℝ,
      Z₀≤ Z → 2≤ Z → 2≤ Z^eta → Real.exp 1≤ Z^eta → 1≤ eta*Real.log Z →
      0≤ N → 0≤ V → 0≤ M → N+V≤ L → M≤ N+V → z₀≤ L →
      hi≤ Z^eta → Real.exp Alog≤ Z^eta → Real.exp window≤ Z^eta →
      0< cutoff → cutoff≤ L → cutoff≤ cstar/200 → eta≤ cutoff/32 →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤ Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤ Z^(normWidth Z (Ideal.span {m})) →
      0≤ pi → 6*eta≤ pi → em*(20*(3*L+16)+30)≤ pi/4 → ed*(20*(3*L+16)+30)≤ pi/4 →
      0≤ epschild → -saving≤48*eta+tau+pi+epschild+epsSecond →
      48*eta+tau+pi+epschild+epsSecond≤ loss →
      3*eta+epsFirst*(2*L+7*eta)≤ lossFinal →
      loss+(2*L+15*eta+tau)*epsFirst+epsFirst≤ lossFinal → -saving≤ lossFinal →
      0≤ A →
    ∀labels:Finset (Ideal O),(∀I∈labels,Supported I ∧ Squarefree I ∧ (I.absNorm:ℝ)≤ Z^V) →
    ∀D:ℕ,hi*Z^N≤ D → ∀slots:Finset σ,slots.card≤ K →
    ∀(lists:σ→Finset (primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))(H:σ→ℝ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,1≤ H i) → (∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤ H i) → (∏i∈slots,H i)≤ Z^z₀ →
    ∀(base Ψ:O→*ℂ),CanonicalCoefficientClass.IsBaseRayTwist base Ψ → (∀u,‖Ψ u‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀a:σ→primePool (CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ,
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1) →
      let S:=reflectionExcludedPrimes q;
      let F:=CanonicalRowCompletion.outsideSquarefreeIdeals S D;
      let hF:=CanonicalRowCompletion.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q);
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hF i];infer_instance;
      let _om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      CanonicalRankMoments (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₁₁
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₁₂
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₂₁
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₂₂
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
        ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (cubicIdealGenerator I) z
          slots lists a (normTwistedSource W theta) (Z^N)‖^2)≤
      Cs*(1+‖theta‖)^shortDegree*Z^(N+V-cstar/256)+
      Cb*(1+A)*(1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower))*
        Z^(N+V+lossFinal+2*L*epsFirst+eps) := by
  obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hstep⟩:=
    actual_complete_state_from_children lo hi hlo hhi W hsW hW Vlog Alog hbox hone
      L cstar eta tau saving em ed eps hL hcstar heta heta1 hetac htau htau1 hem hed heps K
  refine ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,?_⟩
  intro epsFirst epsSecond heF heS degree q hq
  obtain ⟨Cs,Cb,Z₀,hCs,hCb,hZ₀,hstep⟩:=hstep epsFirst epsSecond heF heS degree q hq
  refine ⟨Cs,Cb,Z₀,hCs,hCb,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta hZ hZ2 h2 hExp hlog
    hN hV hM hFcap hMF hzcap hbZ hAZ hwin hcut hcutL hcutc hsmall hmN hmargin hreserve hpuncture
    hpi hpieta hemc hedc hechild hsave hloss hprincipal hretained htail hA
    labels hlabels D hD slots hcard lists H hdis hH1 hH hprod base Ψ hbase hΨ hperiod a ha
  dsimp only
  intro h11 h12 h21 h22
  apply hstep m hm Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta hZ hZ2 h2 hExp hlog
    hN hV hM hFcap hMF hzcap hbZ hAZ hwin hcut.le hcutL hcutc hmN hmargin hreserve
    hpi hpieta hemc hedc hechild hsave hloss hprincipal hretained htail hA
    labels hlabels D hD slots hcard lists H hdis hH1 hH hprod Ψ hΨ hperiod a ha
  · intro j hj
    dsimp only
    intro hne ξ k hk
    exact actual_live_bin_rank_children (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
      Z N V M cutoff eta L bw window hi (normWidth Z (Ideal.span {m})) z₀ margin epschild A
      (M-3*(cutoff/2)/2) (N+V+15*eta) (margin-7*eta) tau
      j (by linarith) hL heta.le heta1 hcut hsmall hV hFcap hbZ hlog hExp h2 hbw
      (by rw [hbexp]; exact hwin.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)))
      (hwin.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))) hne
      base Ψ hbase m hm hmargin hpuncture le_rfl le_rfl le_rfl slots lists a w11 w12 K degree h11 h12 k.1 k.2.1 k.2.2 true

  · intro j hj
    dsimp only
    intro hne ξ k hk
    exact actual_live_bin_rank_children (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
      Z N V M cutoff eta L bw window hi (normWidth Z (Ideal.span {m})) z₀ margin epschild A
      (M-3*(cutoff/2)/2) (N+V+15*eta) (margin-7*eta) tau
      j (by linarith) hL heta.le heta1 hcut hsmall hV hFcap hbZ hlog hExp h2 hbw
      (by rw [hbexp]; exact hwin.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)))
      (hwin.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))) hne
      base Ψ hbase m hm hmargin hpuncture le_rfl le_rfl le_rfl slots lists a w21 w22 K degree h21 h22 k.1 k.2.1 k.2.2 false

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseMoment
open Eisenstein FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open CanonicalRowCompletion  CanonicalQuadraticSieve
open InverseInitialClippedColumns
local notation "Eis" => Eisenstein.O

section General
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
theorem primeCoprimeMask_redundant_mul (S : Finset ι) (m c : Eis)
    (hc : ∀ i∈S,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    primeCoprimeMask p S (m*c)=
      primeCoprimeMask p S m := by
  have he : (∃i∈S,m*c∈Ideal.span {p i}) ↔ ∃i∈S,m∈Ideal.span {p i} := by
    constructor
    · rintro ⟨i,hi,hm⟩
      exact ⟨i,hi,((inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hm).elim id (hc i hi)⟩
    · rintro ⟨i,hi,hm⟩
      exact ⟨i,hi,Ideal.mul_mem_right _ _ hm⟩
  have he' : (∀ i ∈ S, ¬ p i ∣ m*c) ↔ ∀ i ∈ S, ¬ p i ∣ m := by
    simpa only [not_exists, not_and, Ideal.mem_span_singleton] using not_congr he
  simp only [primeCoprimeMask_indicator, he']

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_redundant_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m c f k : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ)
    (hc : ∀ i∈pool,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hg pool Ψ (m*c) f k slots lists a W X=
      finiteCanonicalMarkedRow p hg pool Ψ m f k slots lists a W X := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro S hS
  have hm := primeCoprimeMask_redundant_mul p S m c
    (fun i hi=>hc i (Finset.mem_powerset.mp hS hi))
  simp only [secondChildColumn,hm]

omit [DecidableEq σ] in
theorem normalizedColumnEnergy_redundant_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m c : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z F : ℝ)
    (hc : ∀ i∈pool,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    normalizedColumnEnergy p hg pool Ψ (m*c) slots lists a labels rows D W X Z F=
      normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows D W X Z F := by
  simp only [normalizedColumnEnergy,finiteCanonicalMarkedRow_redundant_puncture
    p hg pool Ψ m c _ _ slots lists a W X hc]


end General
end InverseMoment
end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
