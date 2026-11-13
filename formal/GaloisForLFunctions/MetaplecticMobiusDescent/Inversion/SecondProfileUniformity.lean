/-
Uniform second profiles adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.SecondSourceProfiles

/-!
# Uniform second profiles

Uniform second profiles `InverseSecondProfileUniform` and their positive sources; balanced
clipping slopes of the first-pass windows; the ambient profile tower and its weighted
integrability.
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

namespace InverseInitialEnergyCallerUniform
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialClippedColumns InverseInitialProfile InverseInitialOverlapFourier
open InverseInitialRayAttachment MeasureTheory JointLogSeparation
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
local notation "Eis"=>Eisenstein.O

theorem initial_height_bound (J:ℕ)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
    (h:ℝ)(hh:h = -leftHeight z ∨ h=rightHeight z) :
    (1+‖h‖)^(2*J)≤tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2 := by
  have hb := child_height_moment_bound (2*J) z
  have hl : 1≤(1+‖leftHeight z‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg (leftHeight z)])
  have hr : 1≤(1+‖rightHeight z‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg (rightHeight z)])
  rw [show 2*(2*J)=4*J by omega] at hb
  rcases hh with rfl|rfl
  · rw [norm_neg]
    exact (le_mul_of_one_le_right (by positivity) hr).trans hb
  · exact (le_mul_of_one_le_left (by positivity) hl).trans hb

theorem initial_raw_uniform
    (W:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hs:Function.support W⊆Set.Icc lo b)(hW:ContDiff ℝ ∞ W):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀J:ℕ,∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(m:Eis)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)(D:Ideal Eis→ℝ)(_hD:∀f∈labels,0≤D f)
      (Z N F E:ℝ)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))(h:ℝ),1<Z→0≤E→
      (h = -leftHeight z ∨ h=rightHeight z)→
      (∀s,normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) (Z^(max 0 N)) Z F≤E*(1+‖s‖)^(2*J))→
      normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows D
        (childLogTest W h) (Z^N) Z F≤C*E*(tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) := by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,huniform⟩ := canonical_clipped_uniform W lo b b hlo hb hs hW
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  obtain ⟨C,hC,hbound⟩ := huniform J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD Z N F E z h hZ hE hh hm
  by_cases hne:(freshColumns p pool W (Z^N)).Nonempty
  · obtain ⟨hc1,hcb⟩ := freshColumns_clipping_range p hp pool W lo b Z N hZ hb hs hne
    rw [InverseInitialEnergyCallerClipping.normalized_energy_clipping p hp hg
      pool Ψ m slots lists a labels rows D W (by linarith) N h F]
    apply (hbound p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
      (Z^(max 0 N-N)) h (Z^(max 0 N)) Z F E hc1 hcb (by positivity) hE hm).trans
    exact mul_le_mul_of_nonneg_left (initial_height_bound J z h hh) (mul_nonneg hC.le hE)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    unfold normalizedColumnEnergy
    simp_rw [canonical_row_zero_of_freshColumns_empty p hg pool Ψ m _ _
      slots lists a W (Z^N) h he,mul_zero,norm_zero,zero_pow (by omega : (2:ℕ)≠0),
      Finset.sum_const_zero,mul_zero,Finset.sum_const_zero]
    dsimp [tripleHeight,coordinateHeight]
    positivity


end InverseInitialEnergyCallerUniform

namespace InverseInitialEnergyCallerReference
open Eisenstein SchwartzPlanePoisson CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialClippedColumns InverseInitialProfile InverseInitialOverlapFourier
open InverseInitialRayAttachment MeasureTheory JointLogSeparation
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialEnergyCallerBranch
local notation "Eis"=>Eisenstein.O
local instance initialEnergyUnits : Fintype Eisˣ := @Fintype.ofFinite _ cubic_units_finite
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem actual_physical_reference_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (Φ:𝓢(ℝ,ℂ))(V:Fin 6→ℝ→ℂ)(M:Fin 6→ℝ)
    (hV:∀i,ContDiff ℝ ∞ (V i))(hS:∀i,HasCompactSupport (V i))
    (hM:∀i,0≤M i)(hbox:∀i y,V i y≠0→|y|≤M i)
    (ω₁ ω₂:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hω₁:Function.support ω₁⊆Set.Icc lo b)(hω₂:Function.support ω₂⊆Set.Icc lo b)
    (hd₁:ContDiff ℝ ∞ ω₁)(hd₂:ContDiff ℝ ∞ ω₂) :
    ∃(fresh₁ fresh₂:𝓢(ℝ,ℂ)),
      (∃af bf:ℝ,0<af ∧ af≤bf ∧ HasCompactSupport (fresh₁:ℝ→ℂ) ∧
        tsupport (fresh₁:ℝ→ℂ)⊆Set.Icc af bf) ∧
      (∃af bf:ℝ,0<af ∧ af≤bf ∧ HasCompactSupport (fresh₂:ℝ→ℂ) ∧
        tsupport (fresh₂:ℝ→ℂ)⊆Set.Icc af bf) ∧
    ∀(J N:ℕ)(U π:ℝ),0≤U→0<π→∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
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
      (Z D B v θ H R m η:ℝ)(_hZ:1<Z)(_hR:R≤U)
      (_hη:0≤η*Real.log Z)(c₁ c₂ θ₁ θ₂:ℝ)(_hc₁:0<c₁)(_hc₂:0<c₂)
      (_hsupport:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F A ε:ℝ)(_hA:0≤A)
      (_hδ:max 0 (columnCenter D B v)-columnCenter D B v≤3*η)
      (_hF:F=D-B+θ+(max 0 (columnCenter D B v)-columnCenter D B v))
      (_hReq:R=B-θ+2*η)
      (_hmoment:∀s:ℝ,∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ ρ) (j*primaryIdealGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest fresh₁ s)
          (Z^(max 0 (columnCenter D B v))) Z F≤(A*Z^(F+ε))*(1+‖s‖)^(2*J) ∧
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ ρ) (j*primaryIdealGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest fresh₂ s)
          (Z^(max 0 (columnCenter D B v))) Z F≤(A*Z^(F+ε))*(1+‖s‖)^(2*J)),
      ‖physicalBlock p hg (pointSource pool S) (w ∘ erasePoint) Ψ j
        (primeMark slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+11*η+π+ε)*A*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)) := by
  obtain ⟨fresh₁,af₁,bf₁,haf₁,hab₁,hc₁,hsf₁,hu₁⟩ :=
    InverseInitialEnergyCallerUniform.initial_raw_uniform ω₁ lo b hlo hb hω₁ hd₁
  obtain ⟨fresh₂,af₂,bf₂,haf₂,hab₂,hc₂,hsf₂,hu₂⟩ :=
    InverseInitialEnergyCallerUniform.initial_raw_uniform ω₂ lo b hlo hb hω₂ hd₂
  refine ⟨fresh₁,fresh₂,⟨af₁,bf₁,haf₁,hab₁,hc₁,hsf₁⟩,⟨af₂,bf₂,haf₂,hab₂,hc₂,hsf₂⟩,?_⟩
  intro J N U π hU hπ
  obtain ⟨C₁,hC₁,hh₁⟩ := hu₁ J
  obtain ⟨C₂,hC₂,hh₂⟩ := hu₂ J
  obtain ⟨Cp,hCp,hphysical⟩ := InverseInitialEnergyCallerPhysical.actual_physical_block_bound
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox (4*J) N U π hU hπ
  refine ⟨Cp*(C₁+C₂),mul_pos hCp (add_pos hC₁ hC₂),?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha
    Z D B v θ H R m η hZ hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F A ε hA hδ hF hReq hmoment
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hm : ∀z:JointLogSeparation.Frequency×(Fin 6→ℝ),∀ρ:SecondRayIndex,
      ∀J₁∈slots.powerset,∀J₂∈slots.powerset,∀t∈quotientSet p S,
      normalizedColumnEnergy p hg pool (secondRayMinus Ψ ρ) (j*primaryIdealGenerator t)
        (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
        (Z^(columnCenter D B v)) Z F≤((C₁+C₂)*(A*Z^(F+ε)))*
          (tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) ∧
      normalizedColumnEnergy p hg pool (secondRayPlus Ψ ρ) (j*primaryIdealGenerator t)
        (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
        (Z^(columnCenter D B v)) Z F≤((C₁+C₂)*(A*Z^(F+ε)))*
          (tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) := by
    intro z ρ J₁ hJ₁ J₂ hJ₂ t ht
    have hb₁ := hh₁ p hp hcop hg hpr pool (secondRayMinus Ψ ρ) (j*primaryIdealGenerator t)
      (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
      (by intros;positivity) Z (columnCenter D B v) F (A*Z^(F+ε)) z (-leftHeight z)
      hZ (by positivity) (Or.inl rfl) (fun s=>(hmoment s ρ J₁ hJ₁ J₂ hJ₂ t ht).1)
    have hb₂ := hh₂ p hp hcop hg hpr pool (secondRayPlus Ψ ρ) (j*primaryIdealGenerator t)
      (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
      (by intros;positivity) Z (columnCenter D B v) F (A*Z^(F+ε)) z (rightHeight z)
      hZ (by positivity) (Or.inr rfl) (fun s=>(hmoment s ρ J₁ hJ₁ J₂ hJ₂ t ht).2)
    rw [leftHeight_eq] at hb₁
    rw [rightHeight_eq] at hb₂
    have hh : 0≤tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2 := by
      dsimp [tripleHeight,coordinateHeight];positivity
    constructor
    · apply hb₁.trans
      gcongr
      linarith
    · apply hb₂.trans
      gcongr
      linarith
  have hb := hphysical p hp hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha
    ω₁ ω₂ Z D B v θ H R m η hZ.le hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F ((C₁+C₂)*(A*Z^(F+ε))) (by positivity) hm
  apply hb.trans
  have he : prefactorCenter m D B θ+3*η+F+R+π+(F+ε)≤ m+11*η+π+ε := by
    rw [hF,hReq]
    exact InverseInitialEnergyCallerClipping.initial_scalar_le m D B v θ η _ π ε hδ
  have hexp := Real.rpow_add hZp (prefactorCenter m D B θ+3*η+F+R+π) (F+ε)
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le he
  calc
    _=(Cp*(C₁+C₂))*Z^(prefactorCenter m D B θ+3*η+F+R+π+(F+ε))*A*
        ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)) := by rw [hexp];ring
    _≤_ := by gcongr


end InverseInitialEnergyCallerReference

namespace InverseInitialCanonicalEnergy
open scoped BigOperators Classical SchwartzMap
open Eisenstein CompletedGauss CanonicalQuadraticSieve
open InverseMoment InverseInitialClippedColumns SecondPassArithmetic CanonicalCoefficientClass
local notation "O"=>Eisenstein.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

omit [DecidableEq σ] in
theorem normalization_change (pool:Finset ι)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(w:Ideal O→ℝ)(W:ℝ→ℂ)
    (X Z F G:ℝ)(hZ:0<Z):
    normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows w W X Z F=
      Z^(G-F)*normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows w W X Z G := by
  have he:Z^F*normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows w W X Z F=
      Z^G*normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows w W X Z G:=
    (columnEnergy_normalization p hg pool Ψ m slots lists a labels rows w W X hZ F).symm.trans
      (columnEnergy_normalization p hg pool Ψ m slots lists a labels rows w W X hZ G)
  apply mul_left_cancel₀ (Real.rpow_pos_of_pos hZ F).ne'
  rw [←mul_assoc,←Real.rpow_add hZ,show F+(G-F)=G by ring]
  exact he

omit [DecidableEq σ] in
theorem energy_range_weight_le (pool:Finset ι)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows largeRows:Finset O)(w v:Ideal O→ℝ)(W:ℝ→ℂ)
    (X Z F:ℝ)(hrows:rows⊆largeRows)(hw:∀f∈labels,0≤ w f)(hv:∀f∈labels,w f≤ v f):
    normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows w W X Z F≤
      normalizedColumnEnergy p hg pool Ψ m slots lists a labels largeRows v W X Z F := by
  unfold normalizedColumnEnergy
  apply Finset.sum_le_sum
  intro f hf
  apply mul_le_mul (hv f hf)
    (Finset.sum_le_sum_of_subset_of_nonneg hrows (fun _ _ _=>sq_nonneg _))
    (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
    ((hw f hf).trans (hv f hf))

omit [DecidableEq σ] in
theorem initial_child_from_rank (pool:Finset ι)(base Ψ:O→*ℂ)
    (slots subslots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:𝓢(ℝ,ℂ))
    (Z Mcap Fcap z c eps A N V M Q η:ℝ)(K degree:ℕ)(m:O)
    (hZ:1<Z)(hbase:IsBaseRayTwist base Ψ)(hm:m≠0)
    (hN:0≤ N)(hV:0≤ V+2*η)(hM:0≤ M)(hQ:0≤ Q)
    (hMcap:M≤ Mcap)(hFcap:N+(V+2*η)≤ Fcap)
    (hmargin:CanonicalMargins (N+(V+2*η)) M Q z c)
    (hmnorm:‖ringComplex m‖^2=Z^Q)(hsub:subslots⊆slots)
    (labels:Finset (Ideal O))(hlabels:∀f∈labels,Admissible f ∧ (f.absNorm:ℝ)≤ Z^(V+2*η))
    (rows:Finset O)(hrows:rows⊆nonzeroChildFrequencyBall 1 (Z^M))
    (weight:Ideal O→ℝ)(hw:∀f∈labels,0≤ weight f)
    (hweight:∀f∈labels,weight f≤ secondLabelWeight K f)(s:ℝ)
    (hmoment:CanonicalRankMoments p hg pool base slots lists a W Z Mcap Fcap z c eps A K degree):
    normalizedColumnEnergy p hg pool Ψ m subslots lists a labels rows weight
      (childLogTest W s) (Z^N) Z (N+V)≤ A*Z^(N+V+eps+4*η)*(1+‖s‖)^(2*degree) := by
  have hcanon:=hmoment Ψ hbase m hm N (V+2*η) M Q hN hV hM hQ hMcap hFcap hmargin hmnorm
    subslots hsub labels hlabels s
  rw [normalization_change p hg pool Ψ m subslots lists a labels rows weight
    (childLogTest W s) (Z^N) Z (N+V) (N+(V+2*η)) (zero_lt_one.trans hZ)]
  apply (mul_le_mul_of_nonneg_left
    ((energy_range_weight_le p hg pool Ψ m subslots lists a labels rows
      (nonzeroChildFrequencyBall 1 (Z^M)) weight (secondLabelWeight K) (childLogTest W s)
      (Z^N) Z (N+(V+2*η)) hrows hw hweight).trans hcanon)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans_eq
  rw [show N+(V+2*η)-(N+V)=2*η by ring]
  calc
    _=A*(Z^(2*η)*Z^(N+(V+2*η)+eps))*(1+‖s‖)^(2*degree):=by ring
    _=_:=by
      rw [←Real.rpow_add (zero_lt_one.trans hZ)]
      congr 3
      ring

end InverseInitialCanonicalEnergy

namespace InverseClippingProfiles
def secondBalancedSlope : Fin 6 → ℝ := ![1,-1,0,0,0,0]
end InverseClippingProfiles

namespace InverseAmbientProfileTower
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory JointLogSeparation
open InverseMoment
noncomputable section

theorem frequencyTwist_fourier_joint_stronglyMeasurable (g : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : ℝ × ℝ => (𝓕 (frequencyTwist g p.1)) p.2) := by
  have he (θ t : ℝ) : (𝓕 (frequencyTwist g θ)) t = (𝓕 g) (t-θ) := by
    rw [SchwartzMap.fourier_coe]
    have hf : (frequencyTwist g θ : ℝ → ℂ) = fun y => kernelLogPhase θ y*g y := by
      ext y
      exact frequencyTwist_apply g θ y
    rw [hf,InverseClippingProfiles.fourier_phase_shift,←SchwartzMap.fourier_coe]
  simp_rw [he]
  exact ((𝓕 g : 𝓢(ℝ,ℂ)).continuous.comp
    (continuous_snd.sub continuous_fst)).stronglyMeasurable

theorem logSource_fourier_joint_stronglyMeasurable
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    StronglyMeasurable (fun p : ℝ × ℝ =>
      (𝓕 (frequencyTwist (CanonicalCubeSeparation.sourceLogProfile W a b ha hs hW) p.1)) p.2) :=
  frequencyTwist_fourier_joint_stronglyMeasurable _

theorem twistedTriple_joint_stronglyMeasurable (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × Frequency =>
      tripleCoefficient (𝓕 (frequencyTwist g₁ p.1.1))
        (𝓕 (frequencyTwist g₂ p.1.2)) b₃ p.2) := by
  unfold tripleCoefficient
  exact ((frequencyTwist_fourier_joint_stronglyMeasurable g₁).comp_measurable
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).mul
      (((frequencyTwist_fourier_joint_stronglyMeasurable g₂).comp_measurable
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))).mul
      (b₃.continuous.stronglyMeasurable.comp_measurable
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))

theorem ambientWeight_continuous {ι : Type*} [Fintype ι] (J : ℕ) :
    Continuous (ambientWeight (ι := ι) J) := by
  unfold ambientWeight
  fun_prop

theorem inheritedLeft_continuous {ι : Type*} (i : ι) :
    Continuous (inheritedLeft i) := by unfold inheritedLeft; fun_prop

theorem inheritedRight_continuous {ι : Type*} (i : ι) :
    Continuous (inheritedRight i) := by unfold inheritedRight; fun_prop

private theorem inheritedParameter_measurable {ι κ : Type*} (i j : ι) :
    Measurable (fun z : Ambient ι × Ambient κ =>
      ((inheritedLeft i z.1,inheritedRight j z.1),z.2)) := by
  unfold inheritedLeft inheritedRight
  fun_prop

private theorem conditional_tower_integrable
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (J K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (B : Ambient ι → ℂ) (hB : StronglyMeasurable B)
    (D : Ambient ι → Ambient κ → ℂ)
    (hD : StronglyMeasurable (Function.uncurry D))
    (hi : ∀ p, Integrable (fun q => ambientWeight J q * ‖D p q‖))
    (hb : ∀ p, (∫ q, ambientWeight J q * ‖D p q‖) ≤
      C * ((1 + ‖inheritedLeft i p‖)^K * (1 + ‖inheritedRight j p‖)^K))
    (houter : Integrable (fun p => ambientWeight (J+2*K) p * ‖B p‖)) :
    Integrable (fun z : Ambient ι × Ambient κ =>
      ambientWeight J z.1 * ambientWeight J z.2 * ‖B z.1 * D z.1 z.2‖) := by
  let f : Ambient ι × Ambient κ → ℝ := fun z =>
    ambientWeight J z.1 * ambientWeight J z.2 * ‖B z.1 * D z.1 z.2‖
  have hf_nonneg (z) : 0 ≤ f z := by
    dsimp only [f]
    exact mul_nonneg (mul_nonneg
      (le_trans zero_le_one (ambientWeight_one_le J z.1))
      (le_trans zero_le_one (ambientWeight_one_le J z.2))) (norm_nonneg _)
  have hsm : StronglyMeasurable f :=
    (((ambientWeight_continuous J).comp continuous_fst).stronglyMeasurable.mul
      ((ambientWeight_continuous J).comp continuous_snd).stronglyMeasurable).mul
        ((hB.comp_measurable measurable_fst).mul hD).norm
  apply (integrable_prod_iff hsm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun p => by
      convert (hi p).const_mul (ambientWeight J p * ‖B p‖) using 1
      funext q; dsimp only [f]; rw [norm_mul]; ring)
  · apply (houter.const_mul C).mono' (hsm.norm.integral_prod_right').aestronglyMeasurable
    filter_upwards with p
    have he : (∫ q, ‖f (p,q)‖) =
        ambientWeight J p * ‖B p‖ * (∫ q, ambientWeight J q * ‖D p q‖) := by
      simp_rw [Real.norm_of_nonneg (hf_nonneg _)]
      have heq (q) : f (p,q) =
          (ambientWeight J p * ‖B p‖) * (ambientWeight J q * ‖D p q‖) := by
        dsimp only [f]; rw [norm_mul]; ring
      simp_rw [heq]
      exact integral_const_mul _ _
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), he]
    calc
      _ ≤ ambientWeight J p * ‖B p‖ *
          (C * ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) :=
        mul_le_mul_of_nonneg_left (hb p)
          (mul_nonneg (le_trans zero_le_one (ambientWeight_one_le J p)) (norm_nonneg _))
      _ = (C * ‖B p‖) * (ambientWeight J p *
          ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) := by ring
      _ ≤ (C * ‖B p‖) * ambientWeight (J+2*K) p :=
        mul_le_mul_of_nonneg_left (inherited_pair_weight_bound i j J K p)
          (mul_nonneg hC (norm_nonneg _))
      _ = C * (ambientWeight (J+2*K) p * ‖B p‖) := by ring

private theorem conditional_tower_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (J K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (B : Ambient ι → ℂ) (hB : StronglyMeasurable B)
    (D : Ambient ι → Ambient κ → ℂ)
    (hD : StronglyMeasurable (Function.uncurry D))
    (hi : ∀ p, Integrable (fun q => ambientWeight J q * ‖D p q‖))
    (hb : ∀ p, (∫ q, ambientWeight J q * ‖D p q‖) ≤
      C * ((1 + ‖inheritedLeft i p‖)^K * (1 + ‖inheritedRight j p‖)^K))
    (houter : Integrable (fun p => ambientWeight (J+2*K) p * ‖B p‖)) :
    (∫ z : Ambient ι × Ambient κ,
      ambientWeight J z.1 * ambientWeight J z.2 * ‖B z.1 * D z.1 z.2‖) ≤
      C * (∫ p, ambientWeight (J+2*K) p * ‖B p‖) := by
  have hprod := conditional_tower_integrable i j J K C hC B hB D hD hi hb houter
  rw [Measure.volume_eq_prod, integral_prod _ hprod, ← integral_const_mul]
  apply integral_mono hprod.integral_prod_left (houter.const_mul C)
  intro p
  have he (q) : ambientWeight J p * ambientWeight J q * ‖B p * D p q‖ =
      (ambientWeight J p * ‖B p‖) * (ambientWeight J q * ‖D p q‖) := by
    rw [norm_mul]; ring
  simp_rw [he]
  rw [integral_const_mul]
  calc
    _ ≤ ambientWeight J p * ‖B p‖ *
        (C * ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) :=
      mul_le_mul_of_nonneg_left (hb p)
        (mul_nonneg (le_trans zero_le_one (ambientWeight_one_le J p)) (norm_nonneg _))
    _ = (C * ‖B p‖) * (ambientWeight J p *
        ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) := by ring
    _ ≤ (C * ‖B p‖) * ambientWeight (J+2*K) p :=
      mul_le_mul_of_nonneg_left (inherited_pair_weight_bound i j J K p)
        (mul_nonneg hC (norm_nonneg _))
    _ = C * (ambientWeight (J+2*K) p * ‖B p‖) := by ring

theorem integrable_density_test {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D F : Ambient ι × Ambient κ → ℂ)
    (hD : StronglyMeasurable D) (hF : StronglyMeasurable F) (J : ℕ)
    (hi : Integrable (fun z => ambientWeight J z.1 * ambientWeight J z.2 * ‖D z‖))
    (hFbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    Integrable (fun z => D z * F z) := by
  apply hi.mono' (hD.mul hF).aestronglyMeasurable
  filter_upwards with z
  change ‖D z * F z‖ ≤ _
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hFbound z) (norm_nonneg _)

theorem density_test_fubini {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D F : Ambient ι × Ambient κ → ℂ)
    (hD : StronglyMeasurable D) (hF : StronglyMeasurable F) (J : ℕ)
    (hi : Integrable (fun z => ambientWeight J z.1 * ambientWeight J z.2 * ‖D z‖))
    (hFbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    (∫ z, D z * F z) = ∫ p, ∫ q, D (p,q) * F (p,q) := by
  have h := integrable_density_test D F hD hF J hi hFbound
  simpa only [Measure.volume_eq_prod] using integral_prod (fun z => D z * F z) h

def twistedFullDensity {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (θ : ℝ × ℝ) (p : Ambient ι) : ℂ :=
  fullProfileDensity g (𝓕 (frequencyTwist g₁ θ.1))
    (𝓕 (frequencyTwist g₂ θ.2)) b₃ p

theorem fullProfileDensity_continuous {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) :
    Continuous (fullProfileDensity g b₁ b₂ b₃) := by
  unfold fullProfileDensity tripleCoefficient coordinateDensity
  fun_prop

theorem twistedFullDensity_joint_stronglyMeasurable {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × Ambient ι =>
      twistedFullDensity g g₁ g₂ b₃ p.1 p.2) := by
  unfold twistedFullDensity fullProfileDensity
  apply StronglyMeasurable.mul
  · have hm : Measurable (fun p : (ℝ × ℝ) × Ambient ι => (p.1,p.2.1)) := by fun_prop
    simpa only [Function.comp_def] using
      (twistedTriple_joint_stronglyMeasurable g₁ g₂ b₃).comp_measurable hm
  · apply Continuous.stronglyMeasurable
    unfold coordinateDensity
    fun_prop

theorem fullProfileDensity_weighted_integrable {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun p : Ambient ι =>
      ambientWeight J p * ‖fullProfileDensity g b₁ b₂ b₃ p‖) := by
  convert (tripleCoefficient_weighted_integrable b₁ b₂ b₃ J).mul_prod
    (coordinate_density_weighted_integrable g J) using 1 <;> first
  | rfl
  | (funext p; simp only [ambientWeight, fullProfileDensity, norm_mul]; ring)

theorem fullProfileDensity_weighted_integral {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ p : Ambient ι, ambientWeight J p * ‖fullProfileDensity g b₁ b₂ b₃ p‖) =
      (∫ t : Frequency,
        ((1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) *
      (∫ u : ι → ℝ, (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖) := by
  have he (p : Ambient ι) :
      ambientWeight J p * ‖fullProfileDensity g b₁ b₂ b₃ p‖ =
      (((1+‖p.1.1‖)^J * (1+‖p.1.2.1‖)^J * (1+‖p.1.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ p.1‖) *
      ((∏ i, (1+‖p.2 i‖)^J) * ‖coordinateDensity g p.2‖) := by
    simp only [ambientWeight, fullProfileDensity, norm_mul]; ring
  simp_rw [he, Measure.volume_eq_prod]
  exact integral_prod_mul
    (fun t : Frequency => ((1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) *
      ‖tripleCoefficient b₁ b₂ b₃ t‖)
    (fun u : ι → ℝ => (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖)

def towerMomentOrder (J : ℕ) : ℕ := J + 2*(J + (volume : Measure ℝ).integrablePower)

theorem twistedFullDensity_moment {ι : Type*} [Fintype ι]
    (J : ℕ) (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ × ℝ,
      (∫ p : Ambient ι, ambientWeight J p * ‖twistedFullDensity g g₁ g₂ b₃ θ p‖) ≤
      C * ((1+‖θ.1‖)^(J + (volume : Measure ℝ).integrablePower) *
        (1+‖θ.2‖)^(J + (volume : Measure ℝ).integrablePower)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂, hC₂, h₂⟩ := frequencyTwist_fourier_moment J g₂
  let M := ∫ u : ι → ℝ, (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖
  let B := ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖
  have hM : 0 ≤ M := integral_nonneg (fun _ => by positivity)
  have hB : 0 ≤ B := integral_nonneg (fun _ => by positivity)
  refine ⟨C₁*C₂*B*M, by positivity, ?_⟩
  intro θ
  unfold twistedFullDensity
  rw [fullProfileDensity_weighted_integral,
    tripleCoefficient_weighted_integral]
  have hh := mul_le_mul (h₁ θ.1) (h₂ θ.2)
    (integral_nonneg (fun _ => by positivity)) (by positivity)
  have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hB) hM
  convert hh' using 1 <;> first | rfl | ring

def towerDensity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (z : Ambient ι × Ambient κ) : ℂ :=
  fullProfileDensity outer b₁ b₂ b₃ z.1 *
    twistedFullDensity inner g₁ g₂ c₃
      (inheritedLeft i z.1, inheritedRight j z.1) z.2

theorem towerDensity_joint_stronglyMeasurable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃) := by
  unfold towerDensity
  apply StronglyMeasurable.mul
  · exact ((fullProfileDensity_continuous outer b₁ b₂ b₃).comp continuous_fst).stronglyMeasurable
  · simpa only [Function.comp_def] using
      (twistedFullDensity_joint_stronglyMeasurable inner g₁ g₂ c₃).comp_measurable
        (inheritedParameter_measurable i j)

theorem towerDensity_weighted {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : ℕ) (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
      Integrable (fun z : Ambient ι × Ambient κ =>
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ∧
      (∫ z : Ambient ι × Ambient κ,
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ≤
        C * (∫ p : Ambient ι, ambientWeight (towerMomentOrder J) p *
          ‖fullProfileDensity outer b₁ b₂ b₃ p‖) := by
  obtain ⟨C,hC,hb⟩ := twistedFullDensity_moment J inner g₁ g₂ c₃
  refine ⟨C,hC,?_⟩
  intro i j outer b₁ b₂ b₃
  let D : Ambient ι → Ambient κ → ℂ := fun p q =>
    twistedFullDensity inner g₁ g₂ c₃ (inheritedLeft i p, inheritedRight j p) q
  have hD : StronglyMeasurable (Function.uncurry D) := by
    simpa only [Function.comp_def, Function.uncurry_def, D] using
      (twistedFullDensity_joint_stronglyMeasurable inner g₁ g₂ c₃).comp_measurable
        (inheritedParameter_measurable i j)
  have hi (p : Ambient ι) : Integrable (fun q => ambientWeight J q * ‖D p q‖) :=
    fullProfileDensity_weighted_integrable inner
      (𝓕 (frequencyTwist g₁ (inheritedLeft i p)))
      (𝓕 (frequencyTwist g₂ (inheritedRight j p))) c₃ J
  have hout := fullProfileDensity_weighted_integrable outer b₁ b₂ b₃ (towerMomentOrder J)
  have hB := (fullProfileDensity_continuous outer b₁ b₂ b₃).stronglyMeasurable
  exact ⟨conditional_tower_integrable i j J _ C hC _ hB D hD hi
      (fun p => hb (inheritedLeft i p,inheritedRight j p)) hout,
    conditional_tower_bound i j J _ C hC _ hB D hD hi
      (fun p => hb (inheritedLeft i p,inheritedRight j p)) hout⟩

theorem towerDensity_fubini {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (F : Ambient ι × Ambient κ → ℂ) (hF : StronglyMeasurable F) (J : ℕ)
    (hFbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    (∫ z, towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z * F z) =
      ∫ p, ∫ q, towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ (p,q) * F (p,q) := by
  obtain ⟨C,hC,h⟩ := towerDensity_weighted (ι := ι) J inner g₁ g₂ c₃
  exact density_test_fubini _ F
    (towerDensity_joint_stronglyMeasurable i j outer b₁ b₂ b₃ inner g₁ g₂ c₃)
    hF J (h i j outer b₁ b₂ b₃).1 hFbound

theorem first_inherited_left_eq (p : Ambient (Fin 9)) :
    inheritedLeft 7 p = profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 7 := by
  simp [inheritedLeft, profileHeight, firstLeftSlope, firstRightSlope, firstKernelSlope]
  ring

theorem first_inherited_right_eq (p : Ambient (Fin 9)) :
    inheritedRight 8 p = -profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 8 := by
  simp [inheritedRight, profileHeight, firstLeftSlope, firstRightSlope, firstKernelSlope]
  ring

theorem second_inherited_left_eq (p : Ambient (Fin 6)) :
    inheritedLeft 4 p = profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 4 := by
  simp [inheritedLeft, profileHeight, secondLeftSlope, secondRightSlope, secondKernelSlope]
  ring

theorem second_inherited_right_eq (p : Ambient (Fin 6)) :
    inheritedRight 5 p = -profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 5 := by
  simp [inheritedRight, profileHeight, secondLeftSlope, secondRightSlope, secondKernelSlope]
  ring

theorem twistedFullDensity_uniform_separation {κ : Type*} [Fintype κ]
    (g : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (a₁ a₂ ak M : κ → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hbox : ∀ i y, g i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ c₃ : 𝓢(ℝ, ℂ),
      (∀ (θ : ℝ × ℝ) (y : κ → ℝ),
        (∏ i, g i (y i)) * frequencyTwist g₁ θ.1 (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ.2 (∑ i, a₂ i * y i) *
          SchwartzPlanePoisson.paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : κ → ℝ,
          twistedFullDensity g g₁ g₂ c₃ θ ((t₁,t₂,t₃),u) *
            pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u) ∧
      (∀ θ : ℝ × ℝ,
        (1+R)^A * (∫ p : Ambient κ,
          ambientWeight J p * ‖twistedFullDensity g g₁ g₂ c₃ θ p‖) ≤
        C * ((1+‖θ.1‖)^(J + (volume : Measure ℝ).integrablePower) *
          (1+‖θ.2‖)^(J + (volume : Measure ℝ).integrablePower))) := by
  obtain ⟨C,hC,hs⟩ := twisted_descent_profile_separation
    g₁ g₂ Φ (fun i => g i) a₁ a₂ ak M hM hbox A J
  let G := ∫ u : κ → ℝ, (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖
  have hG : 0 ≤ G := integral_nonneg (fun _ => by positivity)
  refine ⟨C*G,mul_nonneg hC hG,?_⟩
  intro R hR
  obtain ⟨c₃,hc⟩ := hs R hR
  refine ⟨c₃,?_,?_⟩
  · intro θ y
    rw [(hc θ.1 θ.2).1 y]
    exact profile_integral_coordinate_absorption g
      (𝓕 (frequencyTwist g₁ θ.1)) (𝓕 (frequencyTwist g₂ θ.2)) c₃ a₁ a₂ ak y
  · intro θ
    unfold twistedFullDensity
    rw [fullProfileDensity_weighted_integral]
    have hh := mul_le_mul_of_nonneg_right (hc θ.1 θ.2).2.2 hG
    convert hh using 1 <;> first | rfl | ring

theorem fullProfile_tower_uniform {ι κ : Type*} [Fintype ι] [Fintype κ]
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (a₁ a₂ ak M : κ → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hbox : ∀ i y, inner i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ c₃ : 𝓢(ℝ, ℂ),
      (∀ (θ : ℝ × ℝ) (y : κ → ℝ),
        (∏ i, inner i (y i)) * frequencyTwist g₁ θ.1 (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ.2 (∑ i, a₂ i * y i) *
          SchwartzPlanePoisson.paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : κ → ℝ,
          twistedFullDensity inner g₁ g₂ c₃ θ ((t₁,t₂,t₃),u) *
            pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u) ∧
      (∀ (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
        Integrable (fun z : Ambient ι × Ambient κ =>
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ∧
        (1+R)^A * (∫ z : Ambient ι × Ambient κ,
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ≤
          C * (∫ p : Ambient ι, ambientWeight (towerMomentOrder J) p *
            ‖fullProfileDensity outer b₁ b₂ b₃ p‖)) := by
  obtain ⟨C,hC,hs⟩ := twistedFullDensity_uniform_separation inner g₁ g₂ Φ a₁ a₂ ak M hM hbox A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨c₃,he,hb⟩ := hs R hR
  refine ⟨c₃,he,?_⟩
  intro i j outer b₁ b₂ b₃
  have hRpow : 0 < (1+R)^A := pow_pos (by linarith) A
  let D : Ambient ι → Ambient κ → ℂ := fun p q =>
    twistedFullDensity inner g₁ g₂ c₃ (inheritedLeft i p,inheritedRight j p) q
  have hD : StronglyMeasurable (Function.uncurry D) := by
    simpa only [Function.comp_def, Function.uncurry_def, D] using
      (twistedFullDensity_joint_stronglyMeasurable inner g₁ g₂ c₃).comp_measurable
        (inheritedParameter_measurable i j)
  have hi (p : Ambient ι) : Integrable (fun q => ambientWeight J q * ‖D p q‖) :=
    fullProfileDensity_weighted_integrable inner
      (𝓕 (frequencyTwist g₁ (inheritedLeft i p)))
      (𝓕 (frequencyTwist g₂ (inheritedRight j p))) c₃ J
  have hb' (p : Ambient ι) : (∫ q, ambientWeight J q * ‖D p q‖) ≤
      (C/(1+R)^A) * ((1+‖inheritedLeft i p‖)^(J + (volume : Measure ℝ).integrablePower) *
        (1+‖inheritedRight j p‖)^(J + (volume : Measure ℝ).integrablePower)) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hRpow).mpr
    simpa only [mul_comm] using hb (inheritedLeft i p,inheritedRight j p)
  have hout := fullProfileDensity_weighted_integrable outer b₁ b₂ b₃ (towerMomentOrder J)
  have hB := (fullProfileDensity_continuous outer b₁ b₂ b₃).stronglyMeasurable
  have hi' := conditional_tower_integrable i j J _ (C/(1+R)^A)
    (div_nonneg hC hRpow.le) _ hB D hD hi hb' hout
  have hb'' := conditional_tower_bound i j J _ (C/(1+R)^A)
    (div_nonneg hC hRpow.le) _ hB D hD hi hb' hout
  refine ⟨hi',?_⟩
  have hh := mul_le_mul_of_nonneg_left hb'' hRpow.le
  have hcancel (x : ℝ) : (1+R)^A * (C/(1+R)^A*x) = C*x := by
    field_simp [ne_of_gt hRpow]
  rw [hcancel] at hh
  simpa only [towerDensity, D, towerMomentOrder] using hh

def twistedPositiveSource (W : ℝ → ℂ) (θ x : ℝ) : ℂ :=
  kernelLogPhase θ (Real.log x) * W x

theorem first_second_profile_tower
    (W₁ W₂ U₁ U₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsW₁ : Function.support W₁ ⊆ Set.Icc a b) (hsW₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hsU₁ : Function.support U₁ ⊆ Set.Icc a b) (hsU₂ : Function.support U₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (hU₁ : ContDiff ℝ ∞ U₁) (hU₂ : ContDiff ℝ ∞ U₂)
    (Φ Ψ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (T : Fin 6 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hVS : ∀ i, HasCompactSupport (V i))
    (hT : ∀ i, ContDiff ℝ ∞ (T i)) (hTS : ∀ i, HasCompactSupport (T i))
    (MV : Fin 9 → ℝ) (MT : Fin 6 → ℝ)
    (hMV : ∀ i, 0 ≤ MV i) (hMT : ∀ i, 0 ≤ MT i)
    (hVbox : ∀ i y, V i y ≠ 0 → |y| ≤ MV i)
    (hTbox : ∀ i y, T i y ≠ 0 → |y| ≤ MT i) (A₁ A₂ J : ℕ) :
    let G := firstRootSchwartz V hV hVS
    let H := secondRootSchwartz T hT hTS
    let g₁ := CanonicalCubeSeparation.sourceLogProfile U₁ a b ha hsU₁ hU₁
    let g₂ := CanonicalCubeSeparation.sourceLogProfile U₂ a b ha hsU₂ hU₂
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 < R₁ → 0 < R₂ → ∃ b₃ c₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ V R₁ y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 9 → ℝ,
          fullProfileDensity G b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, kernelLogPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope
              (t₁,t₂,t₃) u i) (y i))) ∧
      (∀ (θ : ℝ × ℝ) (y : Fin 6 → ℝ),
        secondPoissonProfile (twistedPositiveSource U₁ θ.1)
          (twistedPositiveSource U₂ θ.2) Ψ T R₂ y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
          twistedFullDensity H g₁ g₂ c₃ θ ((t₁,t₂,t₃),u) *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y (t₁,t₂,t₃) u) ∧
      Integrable (fun z : Ambient (Fin 9) × Ambient (Fin 6) =>
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖towerDensity 7 8 G b₁ b₂ b₃ H g₁ g₂ c₃ z‖) ∧
      (1+R₁)^A₁ * (1+R₂)^A₂ *
        (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖towerDensity 7 8 G b₁ b₂ b₃ H g₁ g₂ c₃ z‖) ≤ C := by
  dsimp only
  let G := firstRootSchwartz V hV hVS
  let H := secondRootSchwartz T hT hTS
  let g₁ := CanonicalCubeSeparation.sourceLogProfile U₁ a b ha hsU₁ hU₁
  let g₂ := CanonicalCubeSeparation.sourceLogProfile U₂ a b ha hsU₂ hU₂
  obtain ⟨b₁,b₂,C₁,hC₁,hfirst⟩ := first_full_profile_common_measure
    W₁ W₂ a b ha hsW₁ hsW₂ hW₁ hW₂ Φ V MV hV hVS hMV hVbox A₁ (towerMomentOrder J)
  have hbox : ∀ i y, H i y ≠ 0 → |y| ≤ MT i := by
    intro i y hy
    change secondRootWindows T i y ≠ 0 at hy
    fin_cases i <;> apply hTbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  obtain ⟨C₂,hC₂,hsecond⟩ := fullProfile_tower_uniform (ι := Fin 9)
    H g₁ g₂ Ψ secondLeftSlope secondRightSlope secondKernelSlope MT hMT hbox A₂ J
  refine ⟨b₁,b₂,C₂*C₁,mul_nonneg hC₂ hC₁,?_⟩
  intro R₁ R₂ hR₁ hR₂
  obtain ⟨b₃,he₁,hi₁,hb₁⟩ := hfirst R₁ hR₁
  obtain ⟨c₃,he₂,htower⟩ := hsecond R₂ hR₂
  have ht := htower 7 8 G b₁ b₂ b₃
  refine ⟨b₃,c₃,he₁,?_,ht.1,?_⟩
  · intro θ y
    simpa only [secondPoissonProfile, twistedPositiveSource, Real.log_exp,
      frequencyTwist_apply, g₁, g₂, CanonicalCubeSeparation.sourceLogProfile_apply,
      H, secondRootSchwartz, rootSchwartz_apply] using he₂ θ y
  · have hh := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ (1+R₁)^A₁ by positivity)
    have hh' := mul_le_mul_of_nonneg_left hb₁ hC₂
    calc
      _ = (1+R₁)^A₁ * ((1+R₂)^A₂ *
          (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
            ambientWeight J z.1 * ambientWeight J z.2 *
              ‖towerDensity 7 8 G b₁ b₂ b₃ H g₁ g₂ c₃ z‖)) := by ring
      _ ≤ (1+R₁)^A₁ * (C₂ * (∫ p : Ambient (Fin 9),
          ambientWeight (towerMomentOrder J) p * ‖fullProfileDensity G b₁ b₂ b₃ p‖)) := hh
      _ ≤ C₂*C₁ := by
        simpa only [ambientWeight, tripleHeight, coordinateHeight, G, mul_assoc,
          mul_left_comm, mul_comm] using hh'

end
end InverseAmbientProfileTower

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory JointLogSeparation SchwartzPlanePoisson
open InverseMoment
open InverseInitialProfile
open InverseAmbientProfileTower
namespace InverseSecondProfileUniform

def rooted (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  InverseClippingProfiles.rootSchwartz g M 0 1 0 a 0 zero_lt_one (by simp) hg

@[simp] theorem rooted_apply (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (y : ℝ) :
    rooted g M a hg y = (Real.exp (a*y) : ℂ)*g y := by
  simp [rooted, InverseClippingProfiles.rootedWindow, InverseClippingProfiles.logWindow]

theorem rooted_support (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) :
    Function.support (rooted g M a hg) ⊆ Set.Icc (-M) M := by
  intro y hy
  exact hg (by simpa using hy)

def translated (g : 𝓢(ℝ, ℂ)) (ρ : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compSubConstCLM ℂ (-ρ) g

@[simp] theorem translated_apply (g : 𝓢(ℝ, ℂ)) (ρ y : ℝ) :
    translated g ρ y = g (y+ρ) := by simp [translated]

theorem fourier_translated (g : 𝓢(ℝ, ℂ)) (ρ t : ℝ) :
    (𝓕 (translated g ρ)) t = kernelLogPhase t ρ * (𝓕 g) t := by
  rw [SchwartzMap.fourier_coe]
  have he : (translated g ρ : ℝ → ℂ) = fun y => g (y+ρ) := by ext y; simp
  rw [he, InverseClippingProfiles.fourier_translate, ← SchwartzMap.fourier_coe]

def normalization (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) : ℝ :=
  Real.exp (-6*L - ∑ i, InverseClippingProfiles.secondBalancedSlope i*ρ i +
    (Real.log c₁+Real.log c₂)/2)

def density (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 6)) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    fullProfileDensity (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

theorem density_formula (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 6)) :
    density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p =
      (normalization ρ c₁ c₂ L : ℂ) *
        (sourceDensity g₁ c₁ θ₁ p.1.1 * (sourceDensity g₂ c₂ θ₂ p.1.2.1 * b₃ p.1.2.2)) *
        (∏ i, kernelLogPhase (p.2 i) (ρ i) * (𝓕 (g i)) (p.2 i)) := by
  simp only [density, fullProfileDensity, tripleCoefficient, coordinateDensity,
    fourier_translated, fourier_clippedTwist]
  ring

private theorem fourier_twist (g : 𝓢(ℝ, ℂ)) (θ t : ℝ) :
    (𝓕 (frequencyTwist g θ)) t = (𝓕 g) (t-θ) := by
  rw [SchwartzMap.fourier_coe]
  have he : (frequencyTwist g θ : ℝ → ℂ) = fun y => kernelLogPhase θ y * g y := by
    ext y
    exact frequencyTwist_apply g θ y
  rw [he, InverseClippingProfiles.fourier_phase_shift, ← SchwartzMap.fourier_coe]

theorem density_norm (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 6)) :
    ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖ = normalization ρ c₁ c₂ L *
      ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖ := by
  rw [density_formula]
  simp only [norm_mul, norm_prod, sourceDensity_norm, kernelLogPhase_norm, one_mul,
    Complex.norm_real, Real.norm_eq_abs, normalization,
    abs_of_pos (Real.exp_pos _), twistedFullDensity, fullProfileDensity,
    tripleCoefficient, coordinateDensity, fourier_twist]
  ring

theorem density_joint_measurable (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun z : ((Fin 6 → ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × ℝ) × Ambient (Fin 6) =>
      density g g₁ g₂ b₃ z.1.1 z.1.2.1.1 z.1.2.1.2 z.1.2.2.1.1 z.1.2.2.1.2 z.1.2.2.2 z.2) := by
  simp_rw [density_formula]
  apply Measurable.stronglyMeasurable
  unfold normalization sourceDensity kernelLogPhase
  have h1 := (𝓕 g₁ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h2 := (𝓕 g₂ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h3 := b₃.continuous.measurable
  have hu (i : Fin 6) := (𝓕 (g i) : 𝓢(ℝ, ℂ)).continuous.measurable
  have he := Complex.continuous_exp.measurable
  fun_prop

theorem normalization_bound (B : Fin 6 → ℝ) (b : ℝ)
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (hρ : ∀ i, |ρ i| ≤ B i)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁b : c₁ ≤ b) (hc₂b : c₂ ≤ b) (hL : 0 ≤ L) :
    normalization ρ c₁ c₂ L ≤
      Real.exp ((∑ i, |InverseClippingProfiles.secondBalancedSlope i| *B i)+Real.log b) := by
  unfold normalization
  apply Real.exp_le_exp.mpr
  have hs : -(∑ i, InverseClippingProfiles.secondBalancedSlope i*ρ i) ≤
      ∑ i, |InverseClippingProfiles.secondBalancedSlope i| *B i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |InverseClippingProfiles.secondBalancedSlope i*ρ i| := neg_le_abs _
      _ = |InverseClippingProfiles.secondBalancedSlope i| *|ρ i| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hρ i) (abs_nonneg _)
  have h1 := Real.log_le_log hc₁ hc₁b
  have h2 := Real.log_le_log hc₂ hc₂b
  linarith

theorem density_weighted_integrable (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Ambient (Fin 6) => ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) := by
  simp_rw [density_norm]
  convert (InverseAmbientProfileTower.fullProfileDensity_weighted_integrable g
    (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ J).const_mul
      (normalization ρ c₁ c₂ L) using 1
  funext p
  unfold twistedFullDensity
  ring

private theorem radial_common_box (Φ : 𝓢(ℝ, ℂ)) (M : Fin 6 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ (V : Fin 6 → ℝ → ℂ), (∀ i y, V i y ≠ 0 → |y| ≤ M i) →
        ∀ y : Fin 6 → ℝ,
        (∏ i, V i (y i))*paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)) =
          ∫ t : ℝ, (∏ i, V i (y i)*kernelLogPhase t (secondKernelSlope i*y i))*b₃ t) ∧
      (1+R)^A * (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) ≤ C := by
  let box : Fin 6 → ℝ → ℂ := fun i y => if |y| ≤ M i then 1 else 0
  have hb : ∀ i y, box i y ≠ 0 → |y| ≤ M i := by
    intro i y h
    simpa [box] using h
  obtain ⟨C,hC,hs⟩ := radial_profile_envelope Φ box
    secondKernelSlope M hM hb A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,he,_,hm,_⟩ := hs R hR
  refine ⟨b₃,?_,hm⟩
  intro V hV y
  simp only [Finset.prod_mul_distrib]
  by_cases hz : (∏ i, V i (y i)) = 0
  · simp [hz]
  · have hall (i : Fin 6) : V i (y i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)
    have hbox (i : Fin 6) : box i (y i) = 1 := by simp [box, hV i _ (hall i)]
    have h := he y
    simp only [hbox, one_mul, Finset.prod_const_one] at h
    rw [h, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring

theorem translated_box (g : 𝓢(ℝ, ℂ)) (M B ρ : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (hρ : |ρ| ≤ B)
    {y : ℝ} (hy : translated g ρ y ≠ 0) : |y| ≤ M+B := by
  have h := hg (show g (y+ρ) ≠ 0 from by simpa only [translated_apply] using hy)
  have hr := abs_le.mp hρ
  apply abs_le.mpr
  constructor <;> linarith [h.1,h.2,hr.1,hr.2]

theorem density_weighted_integral (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Ambient (Fin 6), ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) = normalization ρ c₁ c₂ L *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₁ θ₁)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₂ θ₂)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
        (∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖) := by
  simp_rw [density_norm]
  have he (p : Ambient (Fin 6)) :
      ambientWeight J p * (normalization ρ c₁ c₂ L *
        ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖) =
      normalization ρ c₁ c₂ L * (tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖fullProfileDensity g (𝓕 (frequencyTwist g₁ θ₁))
          (𝓕 (frequencyTwist g₂ θ₂)) b₃ p‖) := by
    unfold ambientWeight tripleHeight coordinateHeight twistedFullDensity
    ring
  simp_rw [he]
  rw [integral_const_mul, InverseMoment.fullProfileDensity_weighted_integral]
  simp only [tripleHeight]
  rw [tripleCoefficient_weighted_integral]
  ring

def profile (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    ((∏ i, translated (g i) (ρ i) (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, secondLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, secondRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)))

def requiredOuterOrder (J : ℕ) : ℕ := J+2*InverseClippingProfiles.momentOrder J

theorem common_measure (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hg : ∀ i, Function.support (g i) ⊆ Set.Icc (-M i) (M i)) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 0 < c₁ → 0 < c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 6 → ℝ, profile g g₁ g₂ Φ ρ c₁ c₂ θ₁ θ₂ R L y =
        ∫ p : Ambient (Fin 6), density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 6) => ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 6), ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  obtain ⟨C₃,hC₃,hsep⟩ := radial_common_box Φ (fun i => M i+B i)
    (fun i => add_nonneg (hM i) (hB i)) A J
  obtain ⟨C₁,hC₁,h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂,hC₂,h₂⟩ := frequencyTwist_fourier_moment J g₂
  let D := ∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖
  let E := Real.exp ((∑ i, |InverseClippingProfiles.secondBalancedSlope i| * B i)+Real.log b)
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i _ => integral_nonneg (fun _ => by positivity))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨E*C₁*C₂*C₃*D, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃,he,hm⟩ := hsep R hR
  refine ⟨b₃,?_⟩
  intro ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  refine ⟨?_, density_weighted_integrable _ _ _ _ _ _ _ _ _ _ _, ?_⟩
  · intro y
    have hb : ∀ i z, translated (g i) (ρ i) z ≠ 0 → |z| ≤ M i+B i :=
      fun i z hz => translated_box (g i) (M i) (B i) (ρ i) (hg i) (hρ i) hz
    have hid := descent_profile_identity (clippedTwist g₁ c₁ θ₁) (clippedTwist g₂ c₂ θ₂)
      Φ (fun i => translated (g i) (ρ i)) secondLeftSlope secondRightSlope secondKernelSlope
      R b₃ (he _ hb) y
    have habs := profile_integral_coordinate_absorption (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃
      secondLeftSlope secondRightSlope secondKernelSlope y
    simp only [profileMode] at habs
    unfold profile
    rw [hid, habs, ← full_density_mode_fubini, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    unfold density
    ring
  · rw [density_weighted_integral]
    have h12 := mul_le_mul (h₁ θ₁) (h₂ θ₂)
      (integral_nonneg (fun _ => by positivity)) (by positivity)
    have h123 := mul_le_mul h12 hm (by positivity) (by positivity)
    have hd := mul_le_mul_of_nonneg_right h123 hD
    have hn := normalization_bound B b ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
    have hh := mul_le_mul hn hd (by positivity) hE
    convert hh using 1 <;> first
    | rfl
    | (dsimp only [InverseClippingProfiles.momentOrder, E, D]; ring)

theorem balanced_exponential_identity (ρ y : Fin 6 → ℝ) (c₁ c₂ L : ℝ) :
    normalization ρ c₁ c₂ L *
      (∏ i, Real.exp (InverseClippingProfiles.secondBalancedSlope i*(y i+ρ i))) *
      Real.exp (-(1/2:ℝ)*((∑ i, secondLeftSlope i*y i)+Real.log c₁)) *
      Real.exp (-(1/2:ℝ)*((∑ i, secondRightSlope i*y i)+Real.log c₂)) =
      Real.exp (-6*L)*Real.exp (InverseClippingProfiles.secondRootExponent y) := by
  rw [normalization, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [InverseClippingProfiles.secondBalancedSlope,
    InverseClippingProfiles.secondRootExponent, secondLeftSlope, secondRightSlope,
    Fin.sum_univ_succ, Fin.succ, Fin.val_mk]
  ring_nf
  rfl

def positiveSource (g : 𝓢(ℝ, ℂ)) (c θ x : ℝ) : ℂ :=
  kernelLogPhase θ (Real.log x)*g (Real.log x+Real.log c)

theorem positiveSource_logSchwartz (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (θ : ℝ) :
    positiveSource (CanonicalCubeSeparation.sourceLogProfile W a b ha hs hW) c θ x =
      clippedSource W c θ x := by
  simp only [positiveSource, CanonicalCubeSeparation.sourceLogProfile_apply,
    Real.exp_add, Real.exp_log hc, Real.exp_log hx, clippedSource]
  rw [mul_comm x c]

theorem balanced_profile_identity
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M : Fin 6 → ℝ) (m₁ m₂ : ℝ)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂)
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) :
    profile (fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i))
      (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂)
      Φ ρ c₁ c₂ θ₁ θ₂ R L y =
      (Real.exp (-6*L) : ℂ) * secondPoissonProfile
        (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
        Φ (fun i y => U i (y+ρ i)) R y := by
  have he := congrArg (fun x : ℝ => (x : ℂ)) (balanced_exponential_identity ρ y c₁ c₂ L)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod] at he
  unfold profile secondPoissonProfile
  rw [InverseClippingProfiles.secondRootWindows_prod]
  simp only [translated_apply, clippedTwist_apply, rooted_apply, positiveSource, Real.log_exp,
    Finset.prod_mul_distrib]
  linear_combination
    (∏ i, U i (y i+ρ i)) * kernelLogPhase θ₁ (∑ i, secondLeftSlope i*y i) *
    g₁ ((∑ i, secondLeftSlope i*y i)+Real.log c₁) *
    kernelLogPhase θ₂ (∑ i, secondRightSlope i*y i) *
    g₂ ((∑ i, secondRightSlope i*y i)+Real.log c₂) *
    paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)) * he

theorem second_profile_common_measure
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 6 → ℝ,
        (Real.exp (-6*L) : ℂ) * secondPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ (fun i y => U i (y+ρ i)) R y =
        ∫ p : Ambient (Fin 6), density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 6) => ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 6), ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C,hC,hs⟩ := common_measure
    (fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i))
    (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂) Φ M B b hM hB
    (fun i => rooted_support _ _ _ _) A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,hb₃⟩ := hs R hR
  refine ⟨b₃,?_⟩
  intro ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have h := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ (zero_lt_one.trans_le hc₁)
    (zero_lt_one.trans_le hc₂) hc₁b hc₂b hL
  refine ⟨?_,h.2⟩
  intro y
  rw [← balanced_profile_identity U g₁ g₂ Φ M m₁ m₂ hU h₁ h₂]
  exact h.1 y

def densityTower {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (z : Ambient ι × Ambient (Fin 6)) : ℂ :=
  fullProfileDensity outer b₁ b₂ b₃ z.1 *
    density g g₁ g₂ c₃ ρ c₁ c₂ (inheritedLeft i z.1) (inheritedRight j z.1) L z.2

theorem densityTower_joint_measurable {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) :
    StronglyMeasurable (densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L) := by
  unfold densityTower
  apply StronglyMeasurable.mul
  · exact ((InverseAmbientProfileTower.fullProfileDensity_continuous outer b₁ b₂ b₃).comp
      continuous_fst).stronglyMeasurable
  · have hm : Measurable (fun z : Ambient ι × Ambient (Fin 6) =>
        ((ρ,(c₁,c₂),(inheritedLeft i z.1,inheritedRight j z.1),L),z.2)) := by
      unfold inheritedLeft inheritedRight
      fun_prop
    exact (density_joint_measurable g g₁ g₂ c₃).comp_measurable hm

theorem densityTower_norm {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (z : Ambient ι × Ambient (Fin 6)) :
    ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖ =
      normalization ρ c₁ c₂ L *
        ‖InverseAmbientProfileTower.towerDensity i j outer b₁ b₂ b₃ g g₁ g₂ c₃ z‖ := by
  simp only [densityTower, InverseAmbientProfileTower.towerDensity, norm_mul, density_norm]
  ring

theorem densityTower_weighted_integrable {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (J : ℕ) :
    Integrable (fun z : Ambient ι × Ambient (Fin 6) =>
      ambientWeight J z.1 * ambientWeight J z.2 *
        ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖) := by
  obtain ⟨C,hC,h⟩ := InverseAmbientProfileTower.towerDensity_weighted (ι := ι) J g g₁ g₂ c₃
  convert (h i j outer b₁ b₂ b₃).1.const_mul (normalization ρ c₁ c₂ L) using 1 <;> first
  | rfl
  | (funext z; rw [densityTower_norm]; ring)

private theorem tower_bound_from_inner {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L C R : ℝ) (hC : 0 ≤ C) (_hR : 0 < R) (A J : ℕ)
    (hb : ∀ θ₁ θ₂ : ℝ, (1+R)^A * (∫ q : Ambient (Fin 6), ambientWeight J q *
        ‖density g g₁ g₂ c₃ ρ c₁ c₂ θ₁ θ₂ L q‖) ≤
      C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
        (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J))) :
    (1+R)^A * (∫ z : Ambient ι × Ambient (Fin 6),
      ambientWeight J z.1 * ambientWeight J z.2 *
        ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖) ≤
      C * (∫ p : Ambient ι, ambientWeight (requiredOuterOrder J) p *
        ‖fullProfileDensity outer b₁ b₂ b₃ p‖) := by
  let f := fun z : Ambient ι × Ambient (Fin 6) =>
    ambientWeight J z.1 * ambientWeight J z.2 *
      ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖
  have hi : Integrable f := densityTower_weighted_integrable i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L J
  have hi' : Integrable (fun z : Ambient ι × Ambient (Fin 6) => (1+R)^A*f z) := hi.const_mul _
  have hout := (InverseAmbientProfileTower.fullProfileDensity_weighted_integrable
    outer b₁ b₂ b₃ (requiredOuterOrder J)).const_mul C
  change (1+R)^A*(∫ z, f z) ≤ _
  rw [← integral_const_mul]
  rw [show (∫ z : Ambient ι × Ambient (Fin 6), (1+R)^A*f z) =
      ∫ p : Ambient ι, ∫ q : Ambient (Fin 6), (1+R)^A*f (p,q) by
    simpa only [Measure.volume_eq_prod] using integral_prod _ hi']
  rw [← integral_const_mul]
  have hip : Integrable (fun z : Ambient ι × Ambient (Fin 6) => (1+R)^A*f z) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hi'
  apply integral_mono hip.integral_prod_left hout
  intro p
  dsimp only
  have he : (∫ q : Ambient (Fin 6), (1+R)^A*f (p,q)) =
      ambientWeight J p * ‖fullProfileDensity outer b₁ b₂ b₃ p‖ *
        ((1+R)^A * ∫ q : Ambient (Fin 6), ambientWeight J q *
          ‖density g g₁ g₂ c₃ ρ c₁ c₂ (inheritedLeft i p) (inheritedRight j p) L q‖) := by
    simp only [f, densityTower, norm_mul]
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with q
    ring
  rw [he]
  have hw := inherited_pair_weight_bound i j J (InverseClippingProfiles.momentOrder J) p
  have hp : 0 ≤ ambientWeight J p := zero_le_one.trans (ambientWeight_one_le J p)
  calc
    _ ≤ (ambientWeight J p * ‖fullProfileDensity outer b₁ b₂ b₃ p‖) *
        (C*((1+‖inheritedLeft i p‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖inheritedRight j p‖)^(InverseClippingProfiles.momentOrder J))) :=
      mul_le_mul_of_nonneg_left (hb _ _) (mul_nonneg hp (norm_nonneg _))
    _ = (C*‖fullProfileDensity outer b₁ b₂ b₃ p‖) *
        (ambientWeight J p * ((1+‖inheritedLeft i p‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖inheritedRight j p‖)^(InverseClippingProfiles.momentOrder J))) := by ring
    _ ≤ (C*‖fullProfileDensity outer b₁ b₂ b₃ p‖) * ambientWeight (requiredOuterOrder J) p :=
      mul_le_mul_of_nonneg_left hw (mul_nonneg hC (norm_nonneg _))
    _ = _ := by ring

theorem second_profile_tower_uniform {ι : Type*} [Fintype ι]
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ c₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ (θ₁ θ₂ : ℝ) (y : Fin 6 → ℝ),
        (Real.exp (-6*L) : ℂ) * secondPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ (fun i y => U i (y+ρ i)) R y =
        ∫ p : Ambient (Fin 6), density G f₁ f₂ c₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      (∀ (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
        Integrable (fun z : Ambient ι × Ambient (Fin 6) =>
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖densityTower i j outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ∧
        (1+R)^A * (∫ z : Ambient ι × Ambient (Fin 6),
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖densityTower i j outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ≤
          C * (∫ p : Ambient ι, ambientWeight (requiredOuterOrder J) p *
            ‖fullProfileDensity outer b₁ b₂ b₃ p‖)) := by
  dsimp only
  obtain ⟨C,hC,hs⟩ := second_profile_common_measure U g₁ g₂ Φ M B m₁ m₂ b hM hB hU h₁ h₂ A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨c₃,hc₃⟩ := hs R hR
  refine ⟨c₃,?_⟩
  intro ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  refine ⟨fun θ₁ θ₂ => (hc₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL).1, ?_⟩
  intro i j outer b₁ b₂ b₃
  refine ⟨densityTower_weighted_integrable i j outer b₁ b₂ b₃ _ _ _ c₃ ρ c₁ c₂ L J, ?_⟩
  exact tower_bound_from_inner i j outer b₁ b₂ b₃ _ _ _ c₃ ρ c₁ c₂ L C R hC hR A J
    (fun θ₁ θ₂ => (hc₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL).2.2)

theorem densityTower_fubini {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ)
    (F : Ambient ι × Ambient (Fin 6) → ℂ) (hF : StronglyMeasurable F) (J : ℕ)
    (hbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    (∫ z, densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z * F z) =
      ∫ p, ∫ q, densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L (p,q) * F (p,q) :=
  density_test_fubini _ F
    (densityTower_joint_measurable i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L) hF J
    (densityTower_weighted_integrable i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L J) hbound

theorem actual_child_height_weight_bound (J K : ℕ) (p : Ambient (Fin 6)) :
    ambientWeight J p *
      ((1+‖profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 4‖)^K *
       (1+‖profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 5‖)^K) ≤
      ambientWeight (J+2*K) p := by
  simpa only [second_inherited_left_eq, second_inherited_right_eq, norm_neg] using
    inherited_pair_weight_bound (4 : Fin 6) 5 J K p

theorem normalization_eta_log (Z η : ℝ) (hZ : 0 < Z) :
    Real.exp (-6*(η*Real.log Z)) = Z^(-6*η) := by
  rw [Real.rpow_def_of_pos hZ]
  congr 1
  ring

theorem fresh_physical_profile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ Y L : ℝ)
    (hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (ω₁ ω₂ : ℝ → ℂ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hω₁ : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) ≠ 0 → ω₁ (q 4/X₀) = 1)
    (hω₂ : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) ≠ 0 → ω₂ (q 5/X₀) = 1)
    (hcut : ω₁ (q 4/X₀) ≠ 0 → ω₂ (q 5/X₀) ≠ 0 →
      ∀ i, V i (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i) = 1) :
    (Real.exp (-6*L) : ℂ) * secondNormProfile
      (fun x => W₁ (x/(G₀*V₀*X₀))) (fun x => W₂ (x/(G₀*V₀*X₀)))
      Φ (fun _ _ => 1) Y q =
      ((E₀*V₀*X₀ : ℝ) : ℂ)⁻¹ * (ω₁ (q 4/X₀)*ω₂ (q 5/X₀)) *
        ((Real.exp (-6*L) : ℂ)*secondPoissonProfile W₁ W₂ Φ V
          (Y*K₀/(E₀*V₀^2*X₀^2)) (secondRelativeLog q G₀ E₀ V₀ K₀ X₀)) := by
  by_cases hw₁ : ω₁ (q 4/X₀) = 0
  · have hW : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      exact zero_ne_one (hw₁.symm.trans (hω₁ hn))
    simp only [secondNormProfile,hW,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : ω₂ (q 5/X₀) = 0
  · have hW : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      exact zero_ne_one (hw₂.symm.trans (hω₂ hn))
    simp only [secondNormProfile,hW,hw₂,mul_zero,zero_mul,zero_div]
  have hm : secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
    (ω₁ (q 4/X₀)*ω₂ (q 5/X₀))*secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q := by
    by_cases h1 : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [hω₁ h1,hω₂ h2,one_mul]
  rw [hm, secondNormProfile_nominal W₁ W₂ Φ G₀ E₀ V₀ K₀ X₀ Y hG hE hV hK hX q hq]
  change _*( _*(_*secondNormProfile W₁ W₂ Φ (fun _ _ => 1) _
    (secondRelativeNorm q G₀ E₀ V₀ K₀ X₀))) = _
  rw [secondNormProfile_eq_full_of_windows W₁ W₂ Φ V _ _
    (secondRelativeNorm_pos q hq G₀ E₀ V₀ K₀ X₀ hG hE hV hK hX) (hcut hw₁ hw₂)]
  ring_nf
  rfl

theorem retained_clipping_parameter (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) (hret : w (q/Z^N) ≠ 0) :
    let c := Z^(max 0 N-N)
    1 ≤ c ∧ c ≤ b ∧ |Real.log c| ≤ Real.log b ∧
      Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b := by
  dsimp only
  have hc := InverseClippingProfiles.retained_clipped_column w Z N q a b hZ hq ha hb hw hret
  refine ⟨hc.1,hc.2.1,?_,hc.2.2.1⟩
  rw [abs_of_nonneg (Real.log_nonneg hc.1)]
  exact Real.log_le_log (zero_lt_one.trans_le hc.1) hc.2.1

theorem first_second_tower_uniform
    (W₁ W₂ : ℝ → ℂ) (a₀ b₀ : ℝ) (ha₀ : 0 < a₀)
    (hsW₁ : Function.support W₁ ⊆ Set.Icc a₀ b₀)
    (hsW₂ : Function.support W₂ ⊆ Set.Icc a₀ b₀)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ₁ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (MV : Fin 9 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hVS : ∀ i, HasCompactSupport (V i))
    (hMV : ∀ i, 0 ≤ MV i) (hVbox : ∀ i y, V i y ≠ 0 → |y| ≤ MV i)
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ₂ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A₁ A₂ J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    let outer := firstRootSchwartz V hV hVS
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 < R₁ → 0 < R₂ → ∃ b₃ c₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ₁ V R₁ y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 9 → ℝ,
          fullProfileDensity outer b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, kernelLogPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope
              (t₁,t₂,t₃) u i) (y i))) ∧
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ (θ₁ θ₂ : ℝ) (y : Fin 6 → ℝ),
        (Real.exp (-6*L) : ℂ) * secondPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ₂ (fun i y => U i (y+ρ i)) R₂ y =
        ∫ p : Ambient (Fin 6), density G f₁ f₂ c₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun z : Ambient (Fin 9) × Ambient (Fin 6) =>
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖densityTower 7 8 outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ∧
      (1+R₁)^A₁ * (1+R₂)^A₂ * (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖densityTower 7 8 outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ≤ C := by
  dsimp only
  obtain ⟨C₂,hC₂,hsecond⟩ := second_profile_tower_uniform (ι := Fin 9)
    U g₁ g₂ Φ₂ M B m₁ m₂ b hM hB hU h₁ h₂ A₂ J
  obtain ⟨b₁,b₂,C₁,hC₁,hfirst⟩ := first_full_profile_common_measure
    W₁ W₂ a₀ b₀ ha₀ hsW₁ hsW₂ hW₁ hW₂ Φ₁ V MV hV hVS hMV hVbox A₁ (requiredOuterOrder J)
  refine ⟨b₁,b₂,C₂*C₁,mul_nonneg hC₂ hC₁,?_⟩
  intro R₁ R₂ hR₁ hR₂
  obtain ⟨b₃,he₁,_,hb₁⟩ := hfirst R₁ hR₁
  obtain ⟨c₃,hc₃⟩ := hsecond R₂ hR₂
  refine ⟨b₃,c₃,he₁,?_⟩
  intro ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have h := hc₃ ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have ht := h.2 7 8 (firstRootSchwartz V hV hVS) b₁ b₂ b₃
  refine ⟨h.1,ht.1,?_⟩
  have hh := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ (1+R₁)^A₁ by positivity)
  have hh' := mul_le_mul_of_nonneg_left hb₁ hC₂
  calc
    _ = (1+R₁)^A₁ * ((1+R₂)^A₂ * (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖densityTower 7 8 (firstRootSchwartz V hV hVS) b₁ b₂ b₃
            (fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i))
            (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂)
            c₃ ρ c₁ c₂ L z‖)) := by ring
    _ ≤ (1+R₁)^A₁ * (C₂ * (∫ p : Ambient (Fin 9), ambientWeight (requiredOuterOrder J) p *
        ‖fullProfileDensity (firstRootSchwartz V hV hVS) b₁ b₂ b₃ p‖)) := hh
    _ ≤ C₂*C₁ := by
      simpa only [ambientWeight, tripleHeight, coordinateHeight, mul_assoc,
        mul_left_comm, mul_comm] using hh'

end InverseSecondProfileUniform

end

namespace InverseClippingProfiles
/-- Logarithmic exponents balancing the two first-pass source windows. -/
def firstBalancedSlope : Fin 9 → ℝ := ![1/2,1/2,1,-1,-(1/2),0,0,0,0]
end InverseClippingProfiles

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
