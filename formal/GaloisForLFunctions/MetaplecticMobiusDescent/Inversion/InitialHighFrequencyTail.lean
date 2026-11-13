/-
The initial high-frequency tail adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.InitialCallerWindows

/-!
# The initial high-frequency tail

Source keys, points and frequencies of the initial high-frequency tail; live ideal caps; the
physical limit and zero mode; rapid decay of the original physical tail.
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
open UniqueFactorizationMonoid
namespace InverseInitialPhysicalLimit
open Eisenstein CompletedGauss  FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialPhysicalReassembly
local notation "O"=> Eisenstein.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def physicalFrequency (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(h:O):ℂ:=
  ∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
    if Disjoint U T then ∑E∈G.powerset,
      initialPhysicalMode p hg Ψ j marks W Φ Z D m G U T E h else 0

include hp hcop in
theorem physicalFrequency_finite
    (hinj:Function.Injective (fun i=> Ideal.span {p i}))
    (pool:Finset ι)(freqT:Finset O)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ):
    (∑h∈freqT,physicalFrequency p hg pool Ψ j marks W Φ Z D m h)=
    physicalBlock p hg (pointSource pool (finiteSource pool freqT))
      (fun _=>1) Ψ j marks (fun x=> star (W x)) W Φ Z D m:=by
  rw [←finite_physical_reassembly p hp hcop hg hinj]
  unfold physicalFrequency
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd:Disjoint U T
  · simp only [hd,ite_true]
    exact Finset.sum_comm
  · simp only [hd,ite_false,Finset.sum_const_zero]

include hp hcop in
theorem physicalFrequency_hasSum
    (hinj:Function.Injective (fun i=> Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,lambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:0< Z):
    HasSum (physicalFrequency p hg pool Ψ j marks W Φ Z D m)
      (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
        if Disjoint U T then ∑E∈G.powerset,∑'h:O,
          initialPhysicalMode p hg Ψ j marks W Φ Z D m G U T E h else 0):=by
  unfold physicalFrequency
  apply hasSum_sum
  intro G hG
  apply hasSum_sum
  intro U hU
  apply hasSum_sum
  intro T hT
  by_cases hd:Disjoint U T
  · simp only [hd,ite_true]
    apply hasSum_sum
    intro E hE
    exact (initialPhysicalMode_summable p hp hg hinj hc hpr Ψ j marks W Φ hZ D m
      G U T E
      (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hU) Finset.disjoint_sdiff)
      (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff) hd).hasSum
  · simpa only [hd,ite_false] using (hasSum_zero : HasSum (fun _ : O=>(0:ℂ)) 0)

include hp hcop in
theorem original_input_zero_nonzero
    (hinj:Function.Injective (fun i=> Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,lambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:0< Z):
    (∑'u:O,Φ (‖ringComplex u‖^2/Z^m)*
      (‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) pool Ψ j 1 1
        (initialTest p marks W Z D) u‖^2:ℝ))=
    physicalFrequency p hg pool Ψ j marks W Φ Z D m 0+
      ∑'h:O,if h=0 then 0 else physicalFrequency p hg pool Ψ j marks W Φ Z D m h:=by
  rw [initial_input_physical p hp hg hinj hc hpr pool Ψ j marks W Φ hZ D m]
  have hs:=physicalFrequency_hasSum p hp hcop hg hinj hc hpr pool Ψ j marks W Φ Z D m hZ
  rw [←hs.tsum_eq]
  exact hs.summable.tsum_eq_add_tsum_ite 0

include hp hcop in
theorem nonzero_frequency_norm_le
    (hinj:Function.Injective (fun i=> Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,lambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m B:ℝ)(hZ:0< Z)
    (hfinite:∀freqT:Finset O,(0:O)∉freqT→
      ‖physicalBlock p hg (pointSource pool (finiteSource pool freqT))
        (fun _=>1) Ψ j marks (fun x=> star (W x)) W Φ Z D m‖≤ B):
    ‖∑'h:O,if h=0 then 0 else physicalFrequency p hg pool Ψ j marks W Φ Z D m h‖≤ B:=by
  have hs:=physicalFrequency_hasSum p hp hcop hg hinj hc hpr pool Ψ j marks W Φ Z D m hZ
  have hs0:Summable (fun h:O=> if h=0 then (0:ℂ) else
      physicalFrequency p hg pool Ψ j marks W Φ Z D m h):=by
    apply (hs.summable.indicator {h:O|h≠0}).congr
    intro h
    by_cases he:h=0 <;> simp [Set.indicator,he]
  apply InverseInitialHighFrequencyTail.norm_tsum_of_finite_bound _ hs0
  intro T
  let freqT:=T.filter (fun h:O=> h≠0)
  have hzero:(0:O)∉freqT:=by simp [freqT]
  have he:(∑h∈T,if h=0 then (0:ℂ) else physicalFrequency p hg pool Ψ j marks W Φ Z D m h)=
      ∑h∈freqT,physicalFrequency p hg pool Ψ j marks W Φ Z D m h:=by
    simp only [freqT,Finset.sum_filter,ite_not]
  rw [he,physicalFrequency_finite p hp hcop hg hinj]
  exact hfinite freqT hzero

end InverseInitialPhysicalLimit

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialZeroMode
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open  SchwartzPlanePoisson InverseMoment
open InverseInitialRayAttachment
local notation "O"=> Eisenstein.O

theorem marked_coefficient_mass (eps b B:ℝ)(heps:0< eps)(hb:0< b)(_hB:0≤ B):
    ∃C:ℝ,0< C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})(_hinj:Function.Injective (fun i=> Ideal.span {p i}))
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(m c d:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤ B)→(∀x,W x≠0→x≤ b)→∀X:ℝ,0< X→
      (∑A∈pool.powerset,‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d
        (fun A=> primeMark slots lists a A*W (primeProductNorm p A/X)) A‖^2)≤ C*X^(1+eps) := by
  obtain ⟨Cm,hCm,hm⟩:=finite_primeMark_small_power (eps/2) (by positivity)
  refine ⟨128*b*(Cm*b^(eps/2)*B)^2+1,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj pool Ψ hΨ m c d slots lists a hdis ha W hW hs X hX
  let T:=pool.powerset.filter (fun A=> W (primeProductNorm p A/X)≠0)
  have hXb:0< b*X:=mul_pos hb hX
  have hnorm:∀A∈T,primeProductNorm p A≤ b*X:=by
    intro A hA
    exact (div_le_iff₀ hX).mp (hs _ (Finset.mem_filter.mp hA).2)
  have hcard:(T.card:ℝ)≤128*(b*X):=by
    by_cases hsmall:1≤ b*X
    · let q : Finset ι → Ideal O := fun A => ∏ i ∈ A, Ideal.span {p i}
      have hq : Function.Injective q := primeIdealFamily_product_injective _ hinj
      have hc := EisensteinLatticeCount.finite_ideal_count_real (T.image q) (b*X) hsmall
        (by
          intro I hI
          obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hI
          exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i})))
        (by
          intro I hI
          obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hI
          exact (primeProductNorm_eq_ideal_norm p A).symm.trans_le (hnorm A hA))
      simpa only [Finset.card_image_of_injective T hq] using hc
    · have hz:T=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro A hA
        exact hsmall ((primeProductNorm_ge_one p hp A).trans (hnorm A hA))
      rw [hz]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  have he:(∑A∈pool.powerset,‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d
      (fun A=> primeMark slots lists a A*W (primeProductNorm p A/X)) A‖^2)=
      ∑A∈T,‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d
        (fun A=> primeMark slots lists a A*W (primeProductNorm p A/X)) A‖^2:=by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro A hA hn
    have hz:W (primeProductNorm p A/X)=0:=by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hA,hh⟩)
    simp only [secondInputCoefficient,hz,mul_zero,norm_zero,zero_pow (by decide:2≠0)]
  have hcoeff:∀A∈T,‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d
      (fun A=> primeMark slots lists a A*W (primeProductNorm p A/X)) A‖≤ Cm*(b*X)^(eps/2)*B:=by
    intro A hA
    apply (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d _ A).trans
    rw [norm_mul]
    apply mul_le_mul _ (hW _) (norm_nonneg _) (by positivity)
    exact (hm p hp hcop slots lists a hdis ha A).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (primeProductNorm_pos p hp A).le (hnorm A hA) (by positivity)) hCm.le)
  rw [he]
  calc
    _≤∑_A∈T,(Cm*(b*X)^(eps/2)*B)^2:=by
      apply Finset.sum_le_sum
      intro A hA
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoeff A hA) 2
    _=(T.card:ℝ)*(Cm*(b*X)^(eps/2)*B)^2:=by simp
    _≤(128*(b*X))*(Cm*(b*X)^(eps/2)*B)^2:=mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _=(128*b*(Cm*b^(eps/2)*B)^2)*X^(1+eps):=by
      rw [Real.mul_rpow hb.le hX.le,Real.rpow_add hX,Real.rpow_one]
      have hh:(X^(eps/2))^2=X^eps:=by
        rw [←Real.rpow_natCast,←Real.rpow_mul hX.le]
        congr 1
        norm_num
      calc
        _=(128*b*(Cm*b^(eps/2)*B)^2)*(X*(X^(eps/2))^2):=by ring
        _=_:=by rw [hh]
    _≤ _:=by nlinarith [Real.rpow_nonneg hX.le (1+eps)]

theorem marked_normalized_zero (eps b B:ℝ)(heps:0< eps)(hb:0< b)(hB:0≤ B)
    (Φ:𝓢(ℝ,ℂ)):
    ∃C:ℝ,0< C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})(_hinj:Function.Injective (fun i=> Ideal.span {p i}))
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(m c d:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤ B)→(∀x,W x≠0→x≤ b)→∀X Y:ℝ,0< X→0< Y→
      ∀K:Finset ι→Finset ι→Finset O,
      (∀G∈pool.powerset,∀E∈G.powerset,(0:O)∈K G E)→
      ‖(X⁻¹:ℂ)*truncatedSecondZero p hg pool Ψ m c d
        (fun A=> primeMark slots lists a A*W (primeProductNorm p A/X)) Φ Y K‖≤ C*Y*X^eps := by
  obtain ⟨Cm,hCm,hm⟩:=marked_coefficient_mass eps b B heps hb hB
  refine ⟨Cm*‖paperRadialFourier Φ 0‖+1,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj pool Ψ hΨ m c d slots lists a hdis ha W hW hs X Y hX hY K hK
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX]
  have hz:=truncatedSecondZero_norm_le p hg hinj pool Ψ m c d
    (fun A=> primeMark slots lists a A*W (primeProductNorm p A/X)) Φ Y K hK
  rw [abs_of_pos hY] at hz
  apply (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hX.le)).trans
  have hm':=hm p hp hcop hg hinj pool Ψ hΨ m c d slots lists a hdis ha W hW hs X hX
  calc
    _≤ X⁻¹*(Y*‖paperRadialFourier Φ 0‖*(Cm*X^(1+eps))):=by gcongr
    _=(Cm*‖paperRadialFourier Φ 0‖)*Y*X^eps:=by
      rw [Real.rpow_add hX,Real.rpow_one]
      field_simp
    _≤ _:=by nlinarith [mul_nonneg hY.le (Real.rpow_nonneg hX.le eps)]

end InverseInitialZeroMode

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialZeroMode
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open  SchwartzPlanePoisson InverseMoment
open InverseInitialRayAttachment
local notation "O"=> Eisenstein.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})(hinj:Function.Injective (fun i=> Ideal.span {p i}))
  (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(hpr:∀i,lambda^2∣p i-1)

include hinj hc hpr

include hp hcop in
theorem physical_zero_off_diagonal
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (G U T E:Finset ι)(hGU:Disjoint G U)(hGT:Disjoint G T)(hUT:Disjoint U T)(hne:U≠T):
    initialPhysicalMode p hg Ψ j σ W Φ Z D m G U T E 0=0 := by
  rw [←normalized_overlap_mode p hp hg hinj hc hpr Ψ j σ W Φ Z D m
    G U T E hGU hGT hUT 0,
    secondNormalizedGaussTerm_zero_of_ne p hp hg U T hne]
  simp

include hp hcop in
theorem physical_zero_empty
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (G E:Finset ι):
    initialPhysicalMode p hg Ψ j σ W Φ Z D m G ∅ ∅ E 0=
    ((Z^(-D):ℝ):ℂ)*(Z^m:ℝ)*paperRadialFourier Φ 0*
      ((‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ j 1 1 (fun _=>1) G‖^2:ℝ):ℂ)*
      star (initialTest p σ W Z D G)*initialTest p σ W Z D G*
      ((UniqueFactorizationMonoid.moebius (∏i∈E,Ideal.span {p i}):ℂ)/
        (‖ringComplex ((∏ i∈E,p i))‖^2:ℝ)) := by
  rw [←normalized_overlap_mode p hp hg hinj hc hpr Ψ j σ W Φ Z D m
    G ∅ ∅ E (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) (Finset.disjoint_empty_left _) 0,
    secondNormalizedGaussTerm_empty]
  have hcoef (H:Finset ι→ℂ):secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ j 1 1 H ∅=H ∅:=by
    simp [secondInputCoefficient,primeCoprimeMask,primeSubsetRow]
  simp only [overlapPairWeight,hcoef,supportMobius,Finset.card_empty,pow_zero,
    one_mul,Finset.union_empty,Finset.sdiff_self,Finset.union_self,
    Finset.prod_coe_sort,Finset.prod_empty,map_one,norm_one,Complex.ofReal_one,
    div_one,map_zero,norm_zero,zero_pow (by decide : 2≠0),mul_zero,zero_div,mul_one]
  ring

include hp hcop in
theorem physical_zero_sum
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ):
    (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
      if Disjoint U T then ∑E∈G.powerset,
        initialPhysicalMode p hg Ψ j σ W Φ Z D m G U T E 0 else 0)=
      ((Z^(-D):ℝ):ℂ)*truncatedSecondZero p hg pool Ψ j 1 1
        (initialTest p σ W Z D) Φ (Z^m) (fun _ _=>{0}) := by
  unfold truncatedSecondZero
  simp only [Finset.mem_singleton,ite_true,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single ∅]
    · simp only [Finset.disjoint_empty_left,ite_true]
      apply Finset.sum_congr rfl
      intro E hE
      rw [physical_zero_empty p hp hcop hg hinj hc hpr,
        prime_product_moebius (fun i => Ideal.span {p i})
          (fun i => Ideal.prime_of_isPrime (NeZero.ne _) inferInstance) hinj]
      simp only [supportMobius]
      ring
    · intro T hT hne
      simp only [Finset.disjoint_empty_left,ite_true]
      apply Finset.sum_eq_zero
      intro E hE
      exact physical_zero_off_diagonal p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m G ∅ T E
        (Finset.disjoint_empty_right _) (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff)
        (Finset.disjoint_empty_left _) hne.symm
    · simp
  · intro U hU hne
    apply Finset.sum_eq_zero
    intro T hT
    split_ifs with hUT
    · apply Finset.sum_eq_zero
      intro E hE
      have hneq:U≠T:=by
        intro he
        subst T
        exact hne (by simpa using Finset.disjoint_iff_inter_eq_empty.mp hUT)
      exact physical_zero_off_diagonal p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m G U T E
        (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hU) Finset.disjoint_sdiff)
        (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff) hUT hneq
    · rfl
  · simp

end InverseInitialZeroMode

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialZeroMode
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open  SchwartzPlanePoisson InverseMoment
open InverseInitialRayAttachment
local notation "O"=> Eisenstein.O

theorem physical_marked_zero_bound (loss L b B:ℝ)(hloss:0< loss)(hL:0≤ L)
    (hb:0< b)(hB:0≤ B)(Φ:𝓢(ℝ,ℂ)):
    ∃C:ℝ,0< C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})(_hinj:Function.Injective (fun i=> Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(j:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤ B)→(∀x,W x≠0→x≤ b)→
      ∀Z D m:ℝ,1≤ Z→D≤ L→
      ‖∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
        if Disjoint U T then ∑E∈G.powerset,
          initialPhysicalMode p hg Ψ j (primeMark slots lists a)
            W Φ Z D m G U T E 0 else 0‖≤ C*Z^(m+loss) := by
  let eps:=loss/(L+1)
  have heps:0< eps:=div_pos hloss (by linarith)
  obtain ⟨C,hC,hbound⟩:=marked_normalized_zero eps b B heps hb hB Φ
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc hpr pool Ψ hΨ j slots lists a hdis ha W hW hs Z D m hZ hD
  have hZ0:0< Z:=lt_of_lt_of_le zero_lt_one hZ
  rw [physical_zero_sum p hp hcop hg hinj hc hpr]
  have heq:((Z^(-D):ℝ):ℂ)=((Z^D:ℝ):ℂ)⁻¹:=by
    rw [Real.rpow_neg hZ0.le,Complex.ofReal_inv]
  rw [heq]
  have hb':=hbound p hp hcop hg hinj pool Ψ hΨ j 1 1 slots lists a hdis ha
    W hW hs (Z^D) (Z^m) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    (fun _ _=>{0}) (by intros; simp)
  change ‖_‖≤ C*Z^(m+loss)
  apply hb'.trans
  rw [←Real.rpow_mul hZ0.le, mul_assoc,←Real.rpow_add hZ0]
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ ?_) hC.le
  have hprod:D*eps≤ loss:=by
    apply (mul_le_mul_of_nonneg_right hD heps.le).trans
    dsimp [eps]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith:0< L+1)).mpr
    nlinarith
  linarith

end InverseInitialZeroMode

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialRetainedSupport
open Eisenstein   CompletedGauss
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialKernelBridge SecondPassArithmetic
local notation "O"=> Eisenstein.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

include hp hcop in
theorem live_cutoffs (hpr:∀i,lambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m:ℝ)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    W₁ (coordinates p x 0*coordinates p x 2*coordinates p x 4/Z^D)≠0 ∧
    W₂ (coordinates p x 0*coordinates p x 2*coordinates p x 5/Z^D)≠0 := by
  rw [physicalTerm_extracted p hp hcop hg hpr Ψ j σ W₁ W₂ Φ Z D m x hx ρ] at hne
  have hk:= (mul_ne_zero_iff.mp hne).2
  unfold physicalKernel at hk
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hk).1).1).2,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hk).1).2⟩

include hp hcop in
theorem live_whole_columns (hpr:∀i,lambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m b:ℝ)(hZ:0< Z)(hs₁:Function.support W₁⊆Set.Iic b)
    (hs₂:Function.support W₂⊆Set.Iic b)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    coordinates p x 0*coordinates p x 2*coordinates p x 4≤ b*Z^D ∧
    coordinates p x 0*coordinates p x 2*coordinates p x 5≤ b*Z^D := by
  obtain ⟨h₁,h₂⟩:=live_cutoffs p hp hcop hg hpr Ψ j σ W₁ W₂ Φ Z D m x hx ρ hne
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ D)).mp (hs₁ h₁),
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ D)).mp (hs₂ h₂)⟩

include hp in
omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
theorem ideal_coordinates_one (x:Point ι):
    1≤ coordinates p x 0 ∧ 1≤ coordinates p x 1 ∧ 1≤ coordinates p x 2 ∧
    1≤ coordinates p x 4 ∧ 1≤ coordinates p x 5 := by
  have hi (S:Finset ι):(1:ℝ)≤((sourceIdeal p S).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp S))
  exact ⟨hi _,hi _,hi _,hi _,hi _⟩

include hp hcop in
theorem live_ideal_caps (hpr:∀i,lambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m b:ℝ)(hZ:0< Z)(hs₁:Function.support W₁⊆Set.Iic b)
    (hs₂:Function.support W₂⊆Set.Iic b)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    coordinates p x 0≤ b*Z^D ∧ coordinates p x 1≤ b*Z^D ∧
    coordinates p x 2≤ b*Z^D ∧ coordinates p x 4≤ b*Z^D ∧
    coordinates p x 5≤ b*Z^D := by
  obtain ⟨h₁,h₂⟩:=live_whole_columns p hp hcop hg hpr Ψ j σ W₁ W₂ Φ
    Z D m b hZ hs₁ hs₂ x hx ρ hne
  obtain ⟨hC,hd,hs,hn₁,hn₂⟩:=ideal_coordinates_one p hp x
  have hpair:1≤ coordinates p x 0*coordinates p x 2:=by nlinarith
  have hcp:coordinates p x 0≤ coordinates p x 0*coordinates p x 2:=
    le_mul_of_one_le_right (by linarith) hs
  have hsp:coordinates p x 2≤ coordinates p x 0*coordinates p x 2:=
    le_mul_of_one_le_left (by linarith) hC
  have hbig:coordinates p x 0*coordinates p x 2≤ b*Z^D:=
    (le_mul_of_one_le_right (by positivity) hn₁).trans h₁
  have hdiv:coordinates p x 1≤ coordinates p x 0:=by
    change ((sourceIdeal p x.divisor).absNorm:ℝ)≤(sourceIdeal p x.common).absNorm
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _)))
      (map_dvd Ideal.absNorm (sourceIdeal_dvd p _ _ hx.divisor_subset))
  exact ⟨hcp.trans hbig,hdiv.trans (hcp.trans hbig),hsp.trans hbig,
    (le_mul_of_one_le_left (by linarith) hpair).trans h₁,
    (le_mul_of_one_le_left (by linarith) hpair).trans h₂⟩

end InverseInitialRetainedSupport

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialHighFrequencyTail
open Eisenstein  SchwartzPlanePoisson
open InverseInitialProfile
local notation "O" => Eisenstein.O

private theorem finite_sum_le_tsum_subtype (F : Finset O) (P : O → Prop)
    (hF : ∀ h ∈ F, P h) (b : O → ℝ) (hb : ∀ h, 0 ≤ b h)
    (hs : Summable (fun h : {h // P h} => b h.val)) :
    (∑ h ∈ F, b h) ≤ ∑' h : {h // P h}, b h.val := by
  let f : F → {h // P h} := fun h => ⟨h.val, hF h.val h.property⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {h // P h} => z.val) h)
  rw [← Finset.sum_coe_sort F]
  have ht : Summable (fun h : F => b h.val) := (hasSum_fintype _).summable
  simpa only [tsum_fintype] using
    ht.tsum_le_tsum_of_inj f hf (fun h _ => hb h.val) (fun _ => le_rfl) hs

theorem finite_radial_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0< C ∧
    ∀ (Φ : 𝓢(ℝ,ℂ)) (K T Γ : ℝ), 0< K → 0≤ T → 0≤Γ →
    ∀ (F : Finset O) (a : O→ℂ),
    (∀h∈F,T≤ K*‖ringComplex h‖^2) →
    (∀h∈F,‖a h‖≤Γ) →
    ‖∑h∈F,a h*paperRadialFourier Φ (K*‖ringComplex h‖^2)‖ ≤
      Γ*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 K)^2*(1+T)^A) := by
  obtain ⟨s,C,hC,hbound⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro Φ K T Γ hK hT hΓ F a hF ha
  have hsum := finite_sum_le_tsum_subtype F
    (fun h => T ≤ K * ‖ringComplex h‖^2) hF
    (fun h => ‖paperRadialFourier Φ (K * ‖ringComplex h‖^2)‖)
    (fun _ => norm_nonneg _)
    ((paperRadialFourier_lattice_summable_norm Φ K hK).subtype
      (fun h => T ≤ K * ‖ringComplex h‖^2))
  calc
    _ ≤ ∑h∈F,‖a h*paperRadialFourier Φ (K*‖ringComplex h‖^2)‖ := norm_sum_le _ _
    _ ≤ ∑h∈F,Γ*‖paperRadialFourier Φ (K*‖ringComplex h‖^2)‖ := by
      apply Finset.sum_le_sum
      intro h hh
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (ha h hh) (norm_nonneg _)
    _ = Γ*∑h∈F,‖paperRadialFourier Φ (K*‖ringComplex h‖^2)‖ := by rw [Finset.mul_sum]
    _ ≤ Γ*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ /
        ((min 1 K)^2*(1+T)^A)) :=
      mul_le_mul_of_nonneg_left (hsum.trans (hbound Φ K T hK hT)) hΓ
    _ = _ := by ring

theorem physicalKernel_frequency (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z D m C d v n₁ n₂ : ℝ) (h : O) :
    physicalKernel W₁ W₂ Φ Z D m ![C,d,v,‖ringComplex h‖^2,n₁,n₂] =
      ((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)*
      W₁ (C*v*n₁/Z^D)*W₂ (C*v*n₂/Z^D)*
      paperRadialFourier Φ ((Z^m/(d*v^2*n₁*n₂))*‖ringComplex h‖^2) := by
  simp [physicalKernel, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem physical_frequency_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0< C₀ ∧
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
      (Z D m C d v n₁ n₂ T Γ : ℝ),
    0< Z → 0< d → 0< v → 0< n₁ → 0< n₂ → 0≤ T → 0≤Γ →
    ∀ (F : Finset O) (a : O→ℂ),
    (∀h∈F,T≤(Z^m/(d*v^2*n₁*n₂))*‖ringComplex h‖^2) →
    (∀h∈F,‖a h‖≤Γ) →
    ‖∑h∈F,a h*physicalKernel W₁ W₂ Φ Z D m
      ![C,d,v,‖ringComplex h‖^2,n₁,n₂]‖ ≤
      Γ*‖((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)*
        W₁ (C*v*n₁/Z^D)*W₂ (C*v*n₂/Z^D)‖ *
      (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/(d*v^2*n₁*n₂)))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hbound⟩ := finite_radial_tail A
  refine ⟨s,C₀,hC₀,?_⟩
  intro W₁ W₂ Φ Z D m C d v n₁ n₂ T Γ hZ hd hv hn₁ hn₂ hT hΓ F a hF ha
  let b : ℂ := ((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)*
        W₁ (C*v*n₁/Z^D)*W₂ (C*v*n₂/Z^D)
  simp_rw [physicalKernel_frequency,←mul_assoc]
  simpa only [b,←mul_assoc] using hbound Φ (Z^m/(d*v^2*n₁*n₂)) T (Γ*‖b‖) (by positivity) hT
    (by positivity) F (fun h=> a h*b) hF (by
      intro h hh
      exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right (ha h hh) (norm_nonneg _)))

theorem correlated_scale_lower (Y C d v n₁ n₂ L : ℝ)
    (hY : 0< Y) (hC : 0< C) (hd : 0< d) (hv : 0< v)
    (hn₁ : 0< n₁) (hn₂ : 0< n₂) (hL : 0< L)
    (h₁ : C*v*n₁≤ L) (h₂ : C*v*n₂≤ L) :
    Y*C ^ 2/(d*L^2) ≤ Y/(d*v^2*n₁*n₂) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh := mul_le_mul h₁ h₂ (by positivity) hL.le
  nlinarith [mul_le_mul_of_nonneg_left hh (show 0≤ Y*d by positivity)]

end InverseInitialHighFrequencyTail

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialHighFrequencyTail
open InverseInitialProfile

theorem live_column_norm_bound (W : ℝ→ℂ) (b C v n X : ℝ)
    (hs : Function.support W⊆Set.Iic b) (hX : 0< X)
    (hw : W (C*v*n/X)≠0) : C*v*n≤ b*X := by
  exact (div_le_iff₀ hX).mp (hs hw)

theorem actual_radial_center_lower
    (Z D m B θ H η C d v n₁ n₂ L hnorm : ℝ)
    (hZ : 1≤ Z) (hd : 0< d) (hv : 0< v) (hn₁ : 0< n₁) (hn₂ : 0< n₂)
    (hL : 0< L) (hC : Z^B≤ C) (hdiv : d≤ Z^(θ+η))
    (hcol : L≤ Z^(D+η)) (hfreq : Z^H≤ hnorm)
    (h₁ : C*v*n₁≤ L) (h₂ : C*v*n₂≤ L) :
    Z^(radialCenter m H θ D B-3*η) ≤
      (Z^m/(d*v^2*n₁*n₂))*hnorm := by
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hc : 0< C := (Real.rpow_pos_of_pos hz B).trans_le hC
  have hh : 0≤ hnorm := (Real.rpow_pos_of_pos hz H).le.trans hfreq
  have hscale := correlated_scale_lower (Z^m) C d v n₁ n₂ L
    (by positivity) hc hd hv hn₁ hn₂ hL h₁ h₂
  calc
    _ = Z^m*(Z^B)^2*Z^H/(Z^(θ+η)*(Z^(D+η))^2) := by
      simp only [pow_two]
      rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,
        ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_sub hz]
      congr 1
      unfold radialCenter
      ring
    _ ≤ Z^m*C ^ 2*hnorm/(d*L^2) := by
      gcongr
    _ = (Z^m*C ^ 2/(d*L^2))*hnorm := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale hh

theorem high_radial_block_tail_gate
    (Z D m B θ H η τ C d v n₁ n₂ L hnorm : ℝ)
    (hZ : 1≤ Z) (hη : 0≤η) (hd : 0< d) (hv : 0< v)
    (hn₁ : 0< n₁) (hn₂ : 0< n₂) (hL : 0< L)
    (hC : Z^B≤ C) (hdiv : d≤ Z^(θ+η))
    (hcol : L≤ Z^(D+η)) (hfreq : Z^H≤ hnorm)
    (h₁ : C*v*n₁≤ L) (h₂ : C*v*n₂≤ L)
    (hhigh : 4*η+τ≤ radialCenter m H θ D B) :
    Z^τ ≤ (Z^m/(d*v^2*n₁*n₂))*hnorm := by
  exact (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)).trans
    (actual_radial_center_lower Z D m B θ H η C d v n₁ n₂ L hnorm
      hZ hd hv hn₁ hn₂ hL hC hdiv hcol hfreq h₁ h₂)

end InverseInitialHighFrequencyTail

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialHighFrequencyTail
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialEnergyCallerWeights
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι]

/-- Distinct prime supports inject into ideals of bounded norm. -/
theorem boundedPrimeSupports_card_explicit
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=> Ideal.span {p i}))
    (pool : Finset ι) (L : ℝ) (hL : 1≤L) :
    ((boundedPrimeSupports p pool L).card:ℝ)≤128*L := by
  let T := boundedPrimeSupports p pool L
  let q : Finset ι → Ideal O := fun A => ∏ i ∈ A, Ideal.span {p i}
  have hq : Function.Injective q := primeIdealFamily_product_injective _ hinj
  have hc := EisensteinLatticeCount.finite_ideal_count_real (T.image q) L hL
    (by
      intro I hI
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hI
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i})))
    (by
      intro I hI
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hI
      exact (primeProductNorm_eq_ideal_norm p A).symm.trans_le (Finset.mem_filter.mp hA).2)
  simpa only [Finset.card_image_of_injective T hq] using hc

theorem marked_support_norm_bound
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=> Ideal.span {p i}))
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hdis : (slots:Set σ).PairwiseDisjoint lists)
    (ha : ∀i∈slots,∀k∈lists i,‖a i k‖≤1)
    (S : Finset ι) (L : ℝ) (hL : 1≤ L) (hS : primeProductNorm p S≤ L) :
    ‖primeMark slots lists a S‖≤128*L := by
  have heq : boundedPrimeSupports p S L=S.powerset := by
    apply Finset.filter_eq_self.mpr
    intro U hU
    exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hU)).trans hS
  have hc := boundedPrimeSupports_card_explicit p hinj S L hL
  rw [heq,Finset.card_powerset] at hc
  exact (primeMark_norm_le_divisor_count slots lists a S hdis ha).trans (by exact_mod_cast hc)

theorem initialColumn_mark_factor
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (Ψ : O→*ℂ) (j C d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    initialColumn p hg Ψ j C d h H S =
      initialColumn p hg Ψ j C d h (fun _=>1) S * H S := by
  simp only [initialColumn,mul_one]

theorem initialColumn_mark_norm
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (hΨ : ∀n,‖Ψ n‖≤1)
    (j C d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    ‖initialColumn p hg Ψ j C d h H S‖≤‖H S‖ := by
  have hinj : Function.Injective (fun i => (Ideal.span {p i} : Ideal O)) := by
    intro i j hij
    by_contra hne
    have ht := (hcop hne).sup_eq
    rw [hij, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top ht
  have hcol := secondColumnCoefficient_norm_one_of_good p hp hinj hg hc S
  have hm := primeCoprimeMask_norm_le_one p S (j*C)
  have hr (a : O) := primeSubsetRow_norm_le_one p
    (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S a
  simp only [initialColumn,norm_mul,norm_star,hcol,one_mul]
  calc
    _ ≤ 1*1*1*1*‖H S‖ := by
      gcongr <;> first | exact hΨ _ | exact hm | exact hr _
    _ = _ := by ring

end InverseInitialHighFrequencyTail

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialHighFrequencyTail
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseInitialPhysicalMeasure
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]

def sourceKey (x : Point ι) : Fin 5→Finset ι :=
  ![x.common,x.divisor,x.overlap,x.left,x.right]

def sourcePoint (k : Fin 5→Finset ι) (h : O) : Point ι :=
  ⟨k 0,k 1,k 2,k 3,k 4,h⟩

omit [DecidableEq ι] in
theorem sourcePoint_key (x : Point ι) : sourcePoint (sourceKey x) x.frequency=x := by
  cases x
  rfl

def sourceKeys (S : Finset (Point ι)) : Finset (Fin 5→Finset ι) := S.image sourceKey

def sourceFrequencies (S : Finset (Point ι)) (k : Fin 5→Finset ι) : Finset O :=
  (S.filter (fun x=> sourceKey x=k)).image Point.frequency

theorem mem_sourceFrequencies (S : Finset (Point ι)) (k : Fin 5→Finset ι) (h : O) :
    h∈sourceFrequencies S k ↔ sourcePoint k h∈S := by
  constructor
  · intro hh
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hh
    obtain ⟨hx,hk⟩ := Finset.mem_filter.mp hx
    rw [←hk,←he,sourcePoint_key]
    exact hx
  · intro hh
    apply Finset.mem_image.mpr
    refine ⟨sourcePoint k h,Finset.mem_filter.mpr ⟨hh,?_⟩,rfl⟩
    funext i
    fin_cases i <;> rfl

theorem source_sum_fibers (S : Finset (Point ι)) (f : Point ι→ℂ) :
    ∑x∈S,f x = ∑k∈sourceKeys S,∑h∈sourceFrequencies S k,f (sourcePoint k h) := by
  rw [←Finset.sum_fiberwise_of_maps_to (s:=S) (t:=sourceKeys S) (g:=sourceKey)
    (fun x hx=> Finset.mem_image.mpr ⟨x,hx,rfl⟩) f]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sourceFrequencies,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [←(Finset.mem_filter.mp hx).2,sourcePoint_key]
  · intro x hx y hy hxy
    have hk := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    rw [←sourcePoint_key x,←sourcePoint_key y,hk,hxy]

theorem sourceKeys_card
    (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=> Ideal.span {p i}))
    (pool : Finset ι) (S : Finset (Point ι)) (L : ℝ) (hL : 1≤ L)
    (hpool : ∀x∈S,∀i,sourceKey x i⊆pool)
    (hnorm : ∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤ L) :
    ((sourceKeys S).card:ℝ)≤(128*L)^5 := by
  let T := boundedPrimeSupports p pool L
  have hsub : sourceKeys S⊆Fintype.piFinset (fun _ : Fin 5=> T) := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hpool x hx i),hnorm x hx i⟩
  have hc := Finset.card_le_card hsub
  have hcast : ((sourceKeys S).card:ℝ)≤(T.card:ℝ)^5 := by
    exact_mod_cast (by simpa using hc)
  exact hcast.trans (pow_le_pow_left₀ (by positivity)
    (boundedPrimeSupports_card_explicit p hinj pool L hL) 5)

end InverseInitialHighFrequencyTail

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialHighFrequencyTail
open Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerWeights InverseInitialProfile InverseInitialKernelBridge InverseInitialRayAttachment
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def originalCoefficient (Ψ : O→*ℂ) (j : O) (mark : Finset ι→ℂ)
    (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  (initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius x.overlap * secondRayCoefficient ρ) *
  star (initialColumn p hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) x.frequency (fun A=> mark (x.common∪A)) (x.overlap∪x.left)) *
  initialColumn p hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=> mark (x.common∪A)) (x.overlap∪x.right)

include hp hcop hg in
theorem physicalTerm_original_coefficient
    (Ψ : O→*ℂ) (j : O) (mark : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : SchwartzMap ℝ ℂ) (Z D m : ℝ)
    (x : Point ι) (hx : Valid x) (ρ : SecondRayIndex) :
    physicalTerm p hg Ψ j mark W₁ W₂ Φ Z D m x ρ =
      originalCoefficient p hg Ψ j mark x ρ *
      physicalKernel W₁ W₂ Φ Z D m (coordinates p x) := by
  unfold physicalTerm
  rw [sourceIdeal_union p _ _ hx.overlap_left,sourceIdeal_union p _ _ hx.overlap_right,
    physicalKernel_common_factor]
  rfl

include hp hcop hg in
theorem originalCoefficient_marked_bound
    (hinj : Function.Injective (fun i=> Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (hΨ : ∀n,‖Ψ n‖≤1) (j : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hdis : (slots:Set σ).PairwiseDisjoint lists)
    (ha : ∀i∈slots,∀k∈lists i,‖a i k‖≤1)
    (x : Point ι) (ρ : SecondRayIndex) (L : ℝ) (hL : 1≤ L)
    (hleft : primeProductNorm p x.common*primeProductNorm p x.overlap*
      primeProductNorm p x.left≤ L)
    (hright : primeProductNorm p x.common*primeProductNorm p x.overlap*
      primeProductNorm p x.right≤ L) :
    ‖originalCoefficient p hg Ψ j (primeMark slots lists a) x ρ‖≤
      ‖secondRayCoefficient ρ‖*(128*L)^2 := by
  have hmark (N : Finset ι)
      (hN : primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p N≤ L) :
      ‖primeMark slots lists a (x.common∪(x.overlap∪N))‖≤128*L := by
    apply marked_support_norm_bound p hp hinj slots lists a hdis ha _ L hL
    apply (primeProductNorm_union_le_mul p hp _ _).trans
    apply (mul_le_mul_of_nonneg_left (primeProductNorm_union_le_mul p hp _ _)
      (primeProductNorm_pos p hp _).le).trans
    simpa only [mul_assoc] using hN
  have hl := (initialColumn_mark_norm p hp hcop hg hc (secondRayMinus Ψ ρ)
    (fun n=>(secondRayMinus_norm_le Ψ ρ n).trans (hΨ n)) j (∏i∈x.common,p i)
    (divisor p x) x.frequency (fun A=> primeMark slots lists a (x.common∪A))
    (x.overlap∪x.left)).trans (hmark x.left hleft)
  have hr := (initialColumn_mark_norm p hp hcop hg hc (secondRayPlus Ψ ρ)
    (fun n=>(secondRayPlus_norm_le Ψ ρ n).trans (hΨ n)) j (∏i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=> primeMark slots lists a (x.common∪A))
    (x.overlap∪x.right)).trans (hmark x.right hright)
  have hb := initialBeta_norm_le_one p Ψ hΨ j x.common
  have hm := IdealCoprimeBilinearSieve.moebius_norm_le_one (sourceIdeal p x.divisor)
  have hv : ‖supportMobius x.overlap‖≤1 := (supportMobius_norm x.overlap).le
  simp only [originalCoefficient,norm_mul,norm_star]
  calc
    _ ≤ 1*1*1*‖secondRayCoefficient ρ‖*(128*L)*(128*L) := by gcongr
    _ = _ := by ring

end InverseInitialHighFrequencyTail

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialHighFrequencyTail
open Eisenstein  InverseInitialProfile
local notation "O"=> Eisenstein.O

theorem initial_denominator_bound (C d v n₁ n₂ L : ℝ)
    (hC : 1≤ C) (_hd : 0≤ d) (hv : 0≤ v) (hn₁ : 0≤ n₁) (hn₂ : 0≤ n₂)
    (hL : 0≤ L) (hdL : d≤ L) (h₁ : C*v*n₁≤ L) (h₂ : C*v*n₂≤ L) :
    d*v^2*n₁*n₂≤ L^3 := by
  have h₁' : v*n₁≤ L := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hv hn₁)]
  have h₂' : v*n₂≤ L := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hv hn₂)]
  have hh := mul_le_mul h₁' h₂' (mul_nonneg hv hn₂) hL
  have he := mul_le_mul hdL hh (by positivity) hL
  nlinarith

theorem initial_scalar_bound (Z D m d v n₁ n₂ : ℝ) (hZ : 0< Z)
    (hd : 1≤ d) (hv : 1≤ v) (hn₁ : 1≤ n₁) (hn₂ : 1≤ n₂) :
    ‖((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)‖≤ Z^(m-D) := by
  have hroot : 1≤ Real.sqrt (n₁*n₂) := by
    rw [Real.one_le_sqrt]
    exact one_le_mul_of_one_le_of_one_le hn₁ hn₂
  have hden : 1≤ d*v*Real.sqrt (n₁*n₂) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hd hv) hroot
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have h := div_le_self (show 0≤ Z^(-D)*Z^m by positivity) hden
  apply h.trans_eq
  rw [←Real.rpow_add hZ]
  congr 1
  ring

theorem physical_frequency_tail_uniform (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0< C₀ ∧
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
      (Z D m C d v n₁ n₂ L T Γ B₁ B₂ : ℝ),
    0< Z → 1≤ C → 1≤ d → 1≤ v → 1≤ n₁ → 1≤ n₂ → 1≤ L →
    d≤ L → C*v*n₁≤ L → C*v*n₂≤ L → 0≤ T → 0≤Γ → 0≤ B₁ → 0≤ B₂ →
    ‖W₁ (C*v*n₁/Z^D)‖≤ B₁ → ‖W₂ (C*v*n₂/Z^D)‖≤ B₂ →
    ∀ (F : Finset O) (a : O→ℂ),
    (∀h∈F,T≤(Z^m/(d*v^2*n₁*n₂))*‖ringComplex h‖^2) →
    (∀h∈F,‖a h‖≤Γ) →
    ‖∑h∈F,a h*physicalKernel W₁ W₂ Φ Z D m
      ![C,d,v,‖ringComplex h‖^2,n₁,n₂]‖ ≤
      Γ*Z^(m-D)*B₁*B₂*(C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hbound⟩ := physical_frequency_tail A
  refine ⟨s,C₀,hC₀,?_⟩
  intro W₁ W₂ Φ Z D m C d v n₁ n₂ L T Γ B₁ B₂ hZ hC hd hv hn₁ hn₂ hL
    hdL h₁ h₂ hT hΓ hB₁ hB₂ hw₁ hw₂ F a hF ha
  have hd0 : 0< d := zero_lt_one.trans_le hd
  have hv0 : 0< v := zero_lt_one.trans_le hv
  have hn₁0 : 0< n₁ := zero_lt_one.trans_le hn₁
  have hn₂0 : 0< n₂ := zero_lt_one.trans_le hn₂
  have hL0 : 0< L := zero_lt_one.trans_le hL
  have hden := initial_denominator_bound C d v n₁ n₂ L hC hd0.le hv0.le hn₁0.le hn₂0.le hL0.le hdL h₁ h₂
  have hK : Z^m/L^3≤ Z^m/(d*v^2*n₁*n₂) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hscalar := initial_scalar_bound Z D m d v n₁ n₂ hZ hd hv hn₁ hn₂
  apply (hbound W₁ W₂ Φ Z D m C d v n₁ n₂ T Γ hZ hd0 hv0 hn₁0 hn₂0 hT hΓ F a hF ha).trans
  simp only [norm_mul]
  have hnorm : ‖((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)‖*
      ‖W₁ (C*v*n₁/Z^D)‖*‖W₂ (C*v*n₂/Z^D)‖ ≤ Z^(m-D)*B₁*B₂ := by gcongr
  calc
    _ ≤ Γ*(Z^(m-D)*B₁*B₂)*(C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
      gcongr
    _ = _ := by ring

end InverseInitialHighFrequencyTail

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialHighFrequencyTail
open Eisenstein  FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialKernelBridge InverseInitialProfile
local notation "O"=> Eisenstein.O
variable {ι : Type*} [DecidableEq ι]

def keyNorms (p : ι→O) (k : Fin 5→Finset ι) : Fin 5→ℝ :=
  fun i=> primeProductNorm p (k i)

omit [DecidableEq ι] in
theorem coordinates_sourcePoint (p : ι→O) (k : Fin 5→Finset ι) (h : O) :
    coordinates p (sourcePoint k h)=
      ![keyNorms p k 0,keyNorms p k 1,keyNorms p k 2,‖ringComplex h‖^2,
        keyNorms p k 3,keyNorms p k 4] := by
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←ringComplex_norm_sq_eq_absNorm_span]
    rfl
  funext i
  fin_cases i <;> simp [coordinates,sourcePoint,physicalCoordinates,keyNorms,hn]

theorem original_frequency_fiber_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0< C₀ ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=> Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L T Γ B₁ B₂ : ℝ),
    0< Z → 1≤ L → 0≤ T → 0≤Γ → 0≤ B₁ → 0≤ B₂ →
    (∀x,‖W₁ x‖≤ B₁) → (∀x,‖W₂ x‖≤ B₂) →
    ∀ (k : Fin 5→Finset ι) (F : Finset O) (w : Point ι→ℂ) (ρ : SecondRayIndex),
    keyNorms p k 1≤ L →
    keyNorms p k 0*keyNorms p k 2*keyNorms p k 3≤ L →
    keyNorms p k 0*keyNorms p k 2*keyNorms p k 4≤ L →
    (∀h∈F,Valid (sourcePoint k h)) → (∀h∈F,‖w (sourcePoint k h)‖≤Γ) →
    (∀h∈F,T≤(Z^m/(keyNorms p k 1*(keyNorms p k 2)^2*
      keyNorms p k 3*keyNorms p k 4))*‖ringComplex h‖^2) →
    ‖∑h∈F,w (sourcePoint k h)*physicalTerm p hg Ψ j
      (primeMark slots lists a) W₁ W₂ Φ Z D m (sourcePoint k h) ρ‖ ≤
    (Γ*‖secondRayCoefficient ρ‖*(128*L)^2)*Z^(m-D)*B₁*B₂*
      (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
      ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hbound⟩ := physical_frequency_tail_uniform A
  refine ⟨s,C₀,hC₀,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc Ψ hΨ j slots lists a hdis ha
    W₁ W₂ Φ Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ k F w ρ hd hleft hright hvalid hw htail
  have hn (i : Fin 5) : 1≤ keyNorms p k i := primeProductNorm_ge_one p hp _
  have he : (∑h∈F,w (sourcePoint k h)*physicalTerm p hg Ψ j
      (primeMark slots lists a) W₁ W₂ Φ Z D m (sourcePoint k h) ρ) =
      ∑h∈F,(w (sourcePoint k h)*originalCoefficient p hg Ψ j
        (primeMark slots lists a) (sourcePoint k h) ρ)*
        physicalKernel W₁ W₂ Φ Z D m
        ![keyNorms p k 0,keyNorms p k 1,keyNorms p k 2,‖ringComplex h‖^2,
          keyNorms p k 3,keyNorms p k 4] := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [physicalTerm_original_coefficient p hp hcop hg Ψ j _ W₁ W₂ Φ Z D m _ (hvalid h hh) ρ,
      coordinates_sourcePoint]
    ring
  rw [he]
  apply hbound W₁ W₂ Φ Z D m (keyNorms p k 0) (keyNorms p k 1)
    (keyNorms p k 2) (keyNorms p k 3) (keyNorms p k 4) L T
    (Γ*‖secondRayCoefficient ρ‖*(128*L)^2) B₁ B₂ hZ (hn 0) (hn 1) (hn 2)
    (hn 3) (hn 4) hL hd hleft hright hT (by positivity) hB₁ hB₂ (hW₁ _) (hW₂ _) F _ htail
  intro h hh
  rw [norm_mul]
  have hc := originalCoefficient_marked_bound p hp hcop hg hinj hc Ψ hΨ j slots lists a
    hdis ha (sourcePoint k h) ρ L hL hleft hright
  calc
    _ ≤ Γ*(‖secondRayCoefficient ρ‖*(128*L)^2) := by gcongr; exact hw h hh
    _ = _ := by ring

end InverseInitialHighFrequencyTail

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialHighFrequencyTail
open InverseInitialPhysicalMeasure

theorem original_source_norm_fibers
    {ι ρ : Type*} [DecidableEq ι]
    (S : Finset (Point ι)) (R : Finset ρ) (f : Point ι→ρ→ℂ) (b : ρ→ℝ)
    (hb : ∀k∈sourceKeys S,∀r∈R,
      ‖∑h∈sourceFrequencies S k,f (sourcePoint k h) r‖≤ b r) :
    ‖∑x∈S,∑r∈R,f x r‖≤((sourceKeys S).card:ℝ)*(∑r∈R,b r) := by
  rw [source_sum_fibers]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑k∈sourceKeys S,∑r∈R,b r := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.sum_comm]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr=> hb k hk r hr))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end InverseInitialHighFrequencyTail

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialHighFrequencyTail
open Eisenstein  FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
local notation "O"=> Eisenstein.O

theorem original_physical_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0< C₀ ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=> Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L T Γ B₁ B₂ : ℝ),
    0< Z → 1≤ L → 0≤ T → 0≤Γ → 0≤ B₁ → 0≤ B₂ →
    (∀x,‖W₁ x‖≤ B₁) → (∀x,‖W₂ x‖≤ B₂) →
    ∀ (pool : Finset ι) (S : Finset (Point ι)) (w : Point ι→ℂ),
    (∀x∈S,Valid x) → (∀x∈S,‖w x‖≤Γ) →
    (∀x∈S,∀i,sourceKey x i⊆pool) →
    (∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤ L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤ L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤ L) →
    (∀x∈S,T≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖ringComplex x.frequency‖^2) →
    ‖physicalBlock p hg S w Ψ j (primeMark slots lists a) W₁ W₂ Φ Z D m‖ ≤
      (128*L)^7*Γ*(∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖)*Z^(m-D)*B₁*B₂*
        (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hfiber⟩ := original_frequency_fiber_tail A
  refine ⟨s,C₀,hC₀,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
    Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ pool S w hvalid hw hpool hnorm hleft hright htail
  let R : ℝ := Z^(m-D)*B₁*B₂*(C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
    ((min 1 (Z^m/L^3))^2*(1+T)^A)
  have hR : 0≤ R := by dsimp [R]; positivity
  let B : ℝ := Γ*(128*L)^2*R
  have hB : 0≤ B := by dsimp [B]; positivity
  have hkey (k) (hk : k∈sourceKeys S) (ρ : SecondRayIndex) :
      ‖∑h∈sourceFrequencies S k,
        w (sourcePoint k h)*physicalTerm p hg Ψ j (primeMark slots lists a)
          W₁ W₂ Φ Z D m (sourcePoint k h) ρ‖ ≤ B*‖secondRayCoefficient ρ‖ := by
    obtain ⟨x,hx,hk'⟩ := Finset.mem_image.mp hk
    have hkN (i) : keyNorms p k i=primeProductNorm p (sourceKey x i) := by rw [←hk'];rfl
    have hf (h) (hh : h∈sourceFrequencies S k) := (mem_sourceFrequencies S k h).mp hh
    have hkl : keyNorms p k 0*keyNorms p k 2*keyNorms p k 3≤ L := by
      simpa [←hk',keyNorms,sourceKey] using hleft x hx
    have hkr : keyNorms p k 0*keyNorms p k 2*keyNorms p k 4≤ L := by
      simpa [←hk',keyNorms,sourceKey] using hright x hx
    have htailk : ∀h∈sourceFrequencies S k,T≤(Z^m/(keyNorms p k 1*(keyNorms p k 2)^2*
        keyNorms p k 3*keyNorms p k 4))*‖ringComplex h‖^2 := by
      intro h hh
      simpa only [sourcePoint,keyNorms] using htail (sourcePoint k h) (hf h hh)
    have hb := hfiber p hp hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
      Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ k (sourceFrequencies S k) w ρ
      (by rw [hkN];exact hnorm x hx 1) hkl hkr
      (fun h hh=> hvalid (sourcePoint k h) (hf h hh))
      (fun h hh=> hw (sourcePoint k h) (hf h hh)) htailk
    apply hb.trans_eq
    dsimp [B,R]
    ring
  have hsum := original_source_norm_fibers S Finset.univ
    (fun x ρ=> w x*physicalTerm p hg Ψ j (primeMark slots lists a) W₁ W₂ Φ Z D m x ρ)
    (fun ρ=> B*‖secondRayCoefficient ρ‖) (fun k hk ρ _=> hkey k hk ρ)
  change ‖∑x∈S,∑ρ : SecondRayIndex,w x*physicalTerm p hg Ψ j
    (primeMark slots lists a) W₁ W₂ Φ Z D m x ρ‖≤ _
  apply hsum.trans
  rw [←Finset.mul_sum]
  calc
    _ ≤ (128*L)^5*(B*(∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖)) :=
      mul_le_mul_of_nonneg_right (sourceKeys_card p hp hinj pool S L hL hpool hnorm) (by positivity)
    _ = _ := by dsimp [B,R]; ring

end InverseInitialHighFrequencyTail

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialHighFrequencyTail

theorem initial_tail_power_cost (A : ℕ) (Z L Lcap m D τ : ℝ)
    (hZ : 1≤ Z) (hL : 1≤ L) (hcap : 0≤ Lcap) (hsize : L≤ Z^Lcap)
    (hm : -m≤ Lcap) (hmd : m-D≤ Lcap) :
    (128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A) ≤
      128^7*Z^(16*Lcap-τ*A) := by
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hl : 0< L := zero_lt_one.trans_le hL
  have hbase : Z^(-4*Lcap)≤ min 1 (Z^m/L^3) := by
    apply le_min
    · exact Real.rpow_le_one_of_one_le_of_nonpos hZ (by linarith)
    · calc
        _ = Z^(-Lcap)/(Z^Lcap)^3 := by
          rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
          congr 1
          norm_num
          ring
        _ ≤ Z^m/L^3 := by
          gcongr ; linarith
  calc
    _ ≤ (128*Z^Lcap)^7*Z^Lcap/((Z^(-4*Lcap))^2*(Z^τ)^A) := by
      gcongr ; linarith
    _ = 128^7*Z^(16*Lcap-τ*A) := by
      rw [mul_pow,←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,
        ←Real.rpow_mul_natCast hz.le]
      rw [mul_assoc,←Real.rpow_add hz,←Real.rpow_add hz,mul_div_assoc,
        ←Real.rpow_sub hz]
      congr 2
      norm_num
      ring

theorem initial_tail_rapid_order (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ A : ℕ, ∀ (Z L m D : ℝ), 1≤ Z → 1≤ L → 0≤ Lcap → L≤ Z^Lcap →
      -m≤ Lcap → m-D≤ Lcap →
      (128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A) ≤
        128^7*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((16*Lcap+saving)/τ)
  refine ⟨A,?_⟩
  intro Z L m D hZ hL hcap hsize hm hmd
  apply (initial_tail_power_cost A Z L Lcap m D τ hZ hL hcap hsize hm hmd).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have h := (div_lt_iff₀ hτ).mp hA
  nlinarith

end InverseInitialHighFrequencyTail

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace InverseInitialHighFrequencyTail
open Eisenstein  FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
local notation "O"=> Eisenstein.O

theorem original_physical_tail_rapid (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0< C₀ ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=> Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=> Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L Γ B₁ B₂ : ℝ),
    1≤ Z → 1≤ L → 0≤ Lcap → L≤ Z^Lcap → -m≤ Lcap → m-D≤ Lcap → 0≤Γ → 0≤ B₁ → 0≤ B₂ →
    (∀x,‖W₁ x‖≤ B₁) → (∀x,‖W₂ x‖≤ B₂) →
    ∀ (pool : Finset ι) (S : Finset (Point ι)) (w : Point ι→ℂ),
    (∀x∈S,Valid x) → (∀x∈S,‖w x‖≤Γ) →
    (∀x∈S,∀i,sourceKey x i⊆pool) →
    (∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤ L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤ L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤ L) →
    (∀x∈S,Z^τ≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖ringComplex x.frequency‖^2) →
    ‖physicalBlock p hg S w Ψ j (primeMark slots lists a) W₁ W₂ Φ Z D m‖ ≤
      C₀*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨A,hA⟩ := initial_tail_rapid_order Lcap saving τ hτ
  obtain ⟨s,C₀,hC₀,hraw⟩ := original_physical_tail A
  let R : ℝ := ∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖
  have hR : 0≤ R := Finset.sum_nonneg (fun _ _=> norm_nonneg _)
  refine ⟨s,128^7*(R+1)*C₀,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
    Z D m L Γ B₁ B₂ hZ hL hcap hsize hm hmd hΓ hB₁ hB₂ hW₁ hW₂ pool S w
    hvalid hw hpool hnorm hleft hright htail
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hb := hraw p hp hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
    Z D m L (Z^τ) Γ B₁ B₂ hz hL (by positivity) hΓ hB₁ hB₂ hW₁ hW₂
    pool S w hvalid hw hpool hnorm hleft hright htail
  have hs : 0≤ s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ := apply_nonneg _ _
  apply hb.trans
  calc
    _ = ((128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A))*
        (Γ*R*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) := by dsimp [R];ring
    _ ≤ (128^7*Z^(-saving))*(Γ*R*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) :=
      mul_le_mul_of_nonneg_right (hA Z L m D hZ hL hcap hsize hm hmd) (by positivity)
    _ ≤ (128^7*Z^(-saving))*(Γ*(R+1)*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) := by
      gcongr
      linarith
    _ = _ := by ring

end InverseInitialHighFrequencyTail

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
