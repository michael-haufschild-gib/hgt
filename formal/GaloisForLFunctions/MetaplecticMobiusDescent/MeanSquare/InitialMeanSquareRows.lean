/-
Initial mean-square rows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.ActualCuspFibers

/-!
# Initial mean-square rows

Second logarithmic indices, source rows and initial labels of the initial mean square
(`InitialMeanSquare`). Element rows inject into unit copies of ideal rows, and residue
reconstruction of initial rows and columns.
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

namespace CompletedUnitRows
open Eisenstein SchwartzPlanePoisson CompletedGauss CanonicalRowCompletion
open scoped BigOperators Classical
local instance : Finite Oˣ:=cubic_units_finite
local instance : Fintype Oˣ:=Fintype.ofFinite _

lemma exists_rowUnit (z : O) : ∃u : Oˣ,(u:O)*cubicIdealGenerator (Ideal.span {z})=z := by
  have ha : Associated (cubicIdealGenerator (Ideal.span {z})) z:=
    Ideal.span_singleton_eq_span_singleton.mp (span_cubicIdealGenerator (Ideal.span {z}))
  obtain ⟨u,hu⟩:=ha
  exact ⟨u,by simpa only [mul_comm] using hu⟩

/-- The unit relating an element to the chosen generator of its principal ideal. -/
def rowUnit (z : O) : Oˣ:=(exists_rowUnit z).choose

lemma rowUnit_spec (z : O) : (rowUnit z:O)*cubicIdealGenerator (Ideal.span {z})=z:=
  (exists_rowUnit z).choose_spec

def unitIdealPoint (z : O) : Oˣ×Ideal O:=(rowUnit z,Ideal.span {z})

lemma unitIdealPoint_injective : Function.Injective unitIdealPoint := by
  intro z w h
  have hu : rowUnit z=rowUnit w:=congrArg Prod.fst h
  have hI : Ideal.span {z}=Ideal.span {w}:=congrArg Prod.snd h
  rw [←rowUnit_spec z,←rowUnit_spec w,hu,hI]

/-- Element rows inject into finitely many unit copies of their ideal rows. -/
theorem sum_elements_le_units (T : Finset O) (v : O→ ℝ) (hv : ∀z,0≤ v z) :
    (∑z∈T,v z)≤ ∑u : Oˣ,∑I∈T.image (fun z=>Ideal.span {z}),v ((u:O)*cubicIdealGenerator I) := by
  let f : Oˣ×Ideal O→ ℝ:=fun p=>v ((p.1:O)*cubicIdealGenerator p.2)
  have he : (∑z∈T,v z)=∑p∈T.image unitIdealPoint,f p := by
    rw [Finset.sum_image (fun z _ w _ h=>unitIdealPoint_injective h)]
    apply Finset.sum_congr rfl
    intro z hz
    dsimp only [f,unitIdealPoint]
    rw [rowUnit_spec]
  have hsub : T.image unitIdealPoint⊆(Finset.univ : Finset Oˣ)×ˢT.image (fun z=>Ideal.span {z}) := by
    intro p hp
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_image_of_mem _ hz⟩
  rw [he]
  calc
    _≤ ∑p∈(Finset.univ : Finset Oˣ)×ˢT.image (fun z=>Ideal.span {z}),f p:=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _=>hv _)
    _=_:=by rw [Finset.sum_product]

lemma image_span_nonzero_norm (T : Finset O) (K : ℝ)
    (hT : ∀z∈T,z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤ K) :
    ∀I∈T.image (fun z=>Ideal.span {z}),I≠0 ∧ (Ideal.absNorm I:ℝ)≤ K := by
  intro I hI
  obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hI
  exact ⟨Ideal.span_singleton_eq_bot.not.mpr (hT z hz).1,(hT z hz).2⟩

/-- A common bound on each unit sector controls an arbitrary finite element family. -/
theorem sum_elements_le_units_bound (T : Finset O) (f : O → ℝ)
    (hf : ∀z,0≤f z) (E : ℝ) (hE : 0≤E)
    (h : ∀u : Oˣ,(∑I∈T.image (fun z=>Ideal.span {z}),f ((u:O)*cubicIdealGenerator I))≤E) :
    (∑z∈T,f z)≤((Fintype.card Oˣ:ℝ)+1)*E := by
  calc
    _≤∑u : Oˣ,∑I∈T.image (fun z=>Ideal.span {z}),f ((u:O)*cubicIdealGenerator I):=
      sum_elements_le_units T f hf
    _≤∑_u : Oˣ,E:=Finset.sum_le_sum (fun u _=>h u)
    _=(Fintype.card Oˣ:ℝ)*E:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _≤_:=mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hE

end CompletedUnitRows

namespace CanonicalRowCompletion.ActualCuspFiber
open Eisenstein SchwartzPlanePoisson CompletedGauss CompletedUnitRows
open SchwartzPlanePoisson.CanonicalQuadraticSieve SecondPassArithmetic
open scoped BigOperators Classical ContDiff
local instance : Finite Oˣ:=cubic_units_finite
local instance : Fintype Oˣ:=Fintype.ofFinite _

/-- The short completed estimate is uniform over the unit sectors of actual element rows. -/
theorem actual_short_element_energy
    (c : O) (hc : c≠0) [Fintype (O⧸Ideal.span {9*c})]
    (W : ℝ→ ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(K X H₀ : ℝ),1≤ K→ 1≤ H₀→ H₀^3≤ X→ ∀(m : O),m≠0→ 
    ∀(T : Finset O) (F : Ideal O),Squarefree F→ 
    (∀z∈T,z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤ K)→ 
    ∀(Ψ : O→*ℂ) (Qbase : Ideal O),
    Ideal.span {c}=Qbase*Ideal.span {(72:O)}→ 
    (∀x y : O,x-y∈Qbase→ Ψ x=Ψ y)→ (∀n,‖Ψ n‖≤ 1)→ lambda∣m→ (2:O)∣m→ 
    (∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)→ 
    (∀z∈T,IsCoprime (Ideal.span {c}) (rowResidualPart (Ideal.span {z}) (Ideal.span {m}*F)))→ 
      (∑z∈T,‖shortCompletedSum (rowTwist Ψ m (cubicIdealGenerator F) z) W X H₀‖^2)≤ 
      (C*(K*(Ideal.absNorm (Ideal.span {m}*F):ℝ))^(10*δ+2*ε)*
        (K+K^2*(Ideal.absNorm (Ideal.span {m}*F):ℝ)*H₀^3/X))*
          (descentLatticeConstant*Real.exp 1*(normLogBin H₀+1:ℝ))^2 := by
  obtain ⟨C,hC,hrow⟩:=actual_short_row_energy c hc W a b ha hs hW δ ε hδ hε
  refine ⟨((Fintype.card Oˣ:ℝ)+1)*C,by positivity,?_⟩
  intro K X H₀ hK hH₀ hX m hm T F hF hT Ψ Qbase hspan hperiod hnorm hmLam hm2 hbad hcop
  let rows:=T.image (fun z=>Ideal.span {z})
  have hrows:=image_span_nonzero_norm T K hT
  have hcoprows (I : Ideal O) (hI : I∈rows) :
      IsCoprime (Ideal.span {c}) (rowResidualPart I (Ideal.span {m}*F)) := by
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hI
    exact hcop z hz
  let E:=(C*(K*(Ideal.absNorm (Ideal.span {m}*F):ℝ))^(10*δ+2*ε)*
    (K+K^2*(Ideal.absNorm (Ideal.span {m}*F):ℝ)*H₀^3/X))*
      (descentLatticeConstant*Real.exp 1*(normLogBin H₀+1:ℝ))^2
  have hX0 : 0<X:=(pow_pos (lt_of_lt_of_le zero_lt_one hH₀) 3).trans_le hX
  have hE : 0≤ E:=by dsimp only [E]; positivity
  have hu (u : Oˣ) :
      (∑I∈rows,‖shortCompletedSum (rowTwist Ψ m (cubicIdealGenerator F)
        ((u:O)*cubicIdealGenerator I)) W X H₀‖^2)≤ E:=
    hrow K X H₀ hK hH₀ hX m hm rows F hF hrows u Ψ Qbase hspan hperiod hnorm
      hmLam hm2 hbad hcoprows
  have hb:=sum_elements_le_units_bound T
    (fun z=>‖shortCompletedSum (rowTwist Ψ m (cubicIdealGenerator F) z) W X H₀‖^2)
    (fun z=>sq_nonneg _) E hE hu
  exact hb.trans_eq (by dsimp only [E]; ring)

end CanonicalRowCompletion.ActualCuspFiber

open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels
open CanonicalCoefficientClass TruncatedPrincipalPoisson
open scoped BigOperators Classical

/-- The initial row geometry places every prime-product mask in the canonical rank domain. -/
theorem initialCanonicalState {ι : Type*}
    (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (bad : Ideal O) (base Ψ : O→*ℂ) (hΨ : IsBaseRayTwist base Ψ)
    (Z η X F K : ℝ) (hZ : 1≤Z) (hη : 0≤η) (hX : 0<X) (hF : 1≤F) (hK : 1≤K)
    (R : Finset ι) (T : Finset (Ideal O×O))
    (hmass : X*F≤Z^2) (hinv : K*primeProductNorm p R≤X*F*Z^(-(1:ℝ)/20))
    (hlabels : ∀z∈T,z.1≠0 ∧ Squarefree z.1 ∧ IsCoprime z.1 bad ∧ (Ideal.absNorm z.1:ℝ)≤F) :
    CanonicalStateCondition base bad Z η Ψ
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) R) (T.image Prod.fst) X F K := by
  have hN:=primeProductNorm_ge_one p hp R
  have hdecay : Z^(-(1:ℝ)/20)≤1:=by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hZ (by norm_num : -(1:ℝ)/20≤0)
  have hKmass : K≤X*F :=
    (le_mul_of_one_le_right (zero_le_one.trans hK) hN).trans
      (hinv.trans (mul_le_of_le_one_right (mul_nonneg hX.le (zero_le_one.trans hF)) hdecay))
  refine ⟨hΨ,primeSubsetGenerator_ne_zero _ _,hX,hF,hK,
    (hKmass.trans hmass).trans (pow_le_pow_right₀ hZ (by decide : (2:ℕ)≤3)),
    hmass.trans (canonicalRankMass_initial Z _),?_,?_⟩
  · rw [primeSubsetGenerator_norm_sq,←primeProductNorm_eq_ideal_norm]
    apply hinv.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hX.le (zero_le_one.trans hF))
    apply Real.rpow_le_rpow_of_exponent_le hZ
    unfold canonicalRankMargin
    have hn : 0≤η*((3000-fixedDepthRank Z K:ℕ):ℝ):=mul_nonneg hη (Nat.cast_nonneg _)
    linarith
  · intro I hI
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hI
    exact hlabels z hz

/-- One fixed threshold supplies all large-scale requirements of the rank induction. -/
theorem canonicalInitialThreshold (S : Finset (Ideal O)) :
    ∃Z₀ : ℝ,1≤Z₀ ∧ ∀Z : ℝ,Z₀≤Z →
      1<Z ∧ Real.exp 9000≤Z ∧
      2*‖ringComplex (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) := by
  let c:=2*‖ringComplex (excludedGenerator S)‖^2
  let Z₀:=2+Real.exp 9000+c^80
  have hc : 0≤c:=by dsimp only [c]; positivity
  have hp : 0≤c^80:=pow_nonneg hc _
  have he:=Real.exp_pos (9000:ℝ)
  refine ⟨Z₀,by dsimp only [Z₀]; linarith,?_⟩
  intro Z hZ
  have hZ1 : 1<Z:=by dsimp only [Z₀] at hZ; linarith
  refine ⟨hZ1,by dsimp only [Z₀] at hZ; linarith,?_⟩
  have hpow : c^80≤Z:=by dsimp only [Z₀] at hZ; linarith
  have hh:=(Real.le_rpow_inv_iff_of_pos hc (zero_le_one.trans hZ1.le) (by norm_num : (0:ℝ)<80)).mpr
    (show c^(80:ℝ)≤Z by simpa only [Real.rpow_ofNat] using hpow)
  simpa only [one_div] using hh

end CanonicalRowCompletion

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels
open scoped BigOperators Classical
variable {ι : Type*} [DecidableEq ι] (p : ι→O)

/-- Fixing the primes left after removing the divisor fixes the initial mask. -/
def InSourceSector (R : Finset ι) (x : SecondExpansionData ι) : Prop :=
  x.divisor⊆x.sourceCommon ∧ x.sourceCommon\x.divisor=R

/-- Initial rows are the empty-cube case of the existing divisor tuple. -/
def sourceTuple (x : SecondExpansionData ι) : SecondPassFiber.OldTuple:=
  actualSecondTuple p ∅ ∅ ∅ x.divisor x.overlap (fun _=>0) (fun _=>0)
    (fun _=>false) (fun _=>false) x.frequency

def sourceLabel (x : SecondExpansionData ι) : Ideal O:=
  (∏i∈x.divisor,Ideal.span {p i})*(∏i∈x.overlap,Ideal.span {p i})

def sourceRow (x : SecondExpansionData ι) : O:=(∏i∈x.divisor,p i)*x.frequency

lemma sourceTuple_newLabel (x : SecondExpansionData ι) :
    SecondPassFiber.newLabel (sourceTuple p x)=sourceLabel p x := by
  rw [sourceTuple,actualSecondTuple_newLabel]
  simp [actualSecondLabel,jLabel,primeProduct,sourceLabel]

lemma sourceTuple_newRow (x : SecondExpansionData ι) :
    SecondPassFiber.newRow (sourceTuple p x)=sourceRow p x := by
  rw [sourceTuple,actualSecondTuple_newRow]
  simp only [actualSecondRow,sourceRow,Finset.prod_empty,one_mul]

lemma sourceLabel_span (x : SecondExpansionData ι) :
    Ideal.span {(∏i∈x.divisor,p i)*(∏i∈x.overlap,p i)}=sourceLabel p x := by
  rw [←Ideal.span_singleton_mul_span_singleton,span_finset_prime_product,span_finset_prime_product]
  rfl

lemma sourceTuple_valid (x : SecondExpansionData ι) :
    SecondPassFiber.Valid (sourceTuple p x) (sourceLabel p x) 1 (sourceRow p x) := by
  have hh:=actualSecondTuple_valid p ∅ ∅ ∅ x.divisor x.overlap
    (Finset.disjoint_empty_left _) (Finset.empty_subset _)
    (fun _=>0) (fun _=>0) (fun _=>false) (fun _=>false)
    (fun i hi=>False.elim (Finset.notMem_empty i hi)) x.frequency
  simpa [sourceTuple,actualSecondLabel,actualSecondRow,sourceLabel,sourceRow,
    jLabel,b0Label,primeProduct] using hh

/-- Divisor, overlap, and frequency recover the row once its residual prime support is fixed. -/
theorem sourceTuple_injective (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i})) (R : Finset ι) :
    Set.InjOn (sourceTuple p) {x | InSourceSector R x} := by
  intro x hx y hy he
  have hE : x.divisor=y.divisor := by
    apply primeIdealFamily_product_injective (fun i=>Ideal.span {p i}) hinj
    have hh:=congrArg (fun t : SecondPassFiber.OldTuple=>t.core 2) he
    change (∏i∈x.divisor,Ideal.span {p i})=(∏i∈y.divisor,Ideal.span {p i}) at hh
    exact hh
  have hV : x.overlap=y.overlap:=
    primeIdealFamily_product_injective (fun i=>Ideal.span {p i}) hinj
      (congrArg SecondPassFiber.OldTuple.v he)
  have hk : x.frequency=y.frequency := by
    have hh:=congrArg SecondPassFiber.newRow he
    rw [sourceTuple_newRow,sourceTuple_newRow] at hh
    dsimp only [sourceRow] at hh
    rw [hE] at hh
    exact mul_left_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)) hh
  have hG : x.sourceCommon=y.sourceCommon := by
    calc
      _=x.divisor∪R:=by rw [←hx.2,Finset.union_sdiff_of_subset hx.1]
      _=y.divisor∪R:=by rw [hE]
      _=_:=by rw [←hy.2,Finset.union_sdiff_of_subset hy.1]
  exact SecondExpansionData.ext hG hE hV hk

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels
open SecondPassIntegration SecondPassFiber JointLogSeparation
open scoped BigOperators Classical SchwartzMap

/-- Fixing the residual support allows the existing divisor-tuple estimate to bound initial sources. -/
theorem uniform_initial_source_density_transfer (ε : ℝ) (hε : 0<ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7→ℝ→ℂ) (M : Fin 7→ℝ)
    (hM : ∀j,0≤M j) (hV : ∀j x,V j x≠0→|x|≤M j) (A J : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀ρ : ℝ,0<ρ →
      ∀{ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i}) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (H₁ H₂ : Finset ι→ℂ) (R : Finset ι) (s : Finset (SecondExpansionData ι))
      (T : Finset (Ideal O×O)) (w : SecondExpansionData ι→ℂ) (B L : ℝ)
      (pool : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O)
      (z ud ue uv kap : SecondExpansionData ι→ℝ) (X₁ X₂ : ℝ),
      0≤B → 0≤L → (∀x∈s,InSourceSector R x) →
      (∀x∈s,(sourceLabel p x,sourceRow p x)∈T) →
      (∀t∈T,t.1≠0) → (∀t∈T,(Ideal.absNorm t.1:ℝ)≤L) →
      (∀x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖≤B) →
      (1+ρ)^A*‖∑x∈s,w x*postCommonSmoothPair p hg H₁ H₂ pool Ψ₁ Ψ₂ m
        ((∏i∈x.divisor,p i)*(∏i∈x.overlap,p i)) (sourceRow p x) (-sourceRow p x)
        A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ ρ‖≤
      B*C*L^ε*densityChildEnergy p hg H₁ H₂ pool Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ J := by
  obtain ⟨C,hC,ht⟩:=full_uniform_tuple_density_transfer ε hε A₁ A₂ W V M hM hV A J
  refine ⟨C,hC,?_⟩
  intro ρ hρ ι _ p hp _ hg hinj H₁ H₂ R s T w B L pool Ψ₁ Ψ₂ m
    z ud ue uv kap X₁ X₂ hB hL hs hT hT0 hTL hw
  let pick (t : OldTuple) : SecondExpansionData ι:=
    if h : ∃x∈s,sourceTuple p x=t then h.choose else ⟨∅,∅,∅,0⟩
  have hchoice (t : OldTuple) (ht : t∈s.image (sourceTuple p)) :
      pick t∈s ∧ sourceTuple p (pick t)=t := by
    have he : ∃x∈s,sourceTuple p x=t:=Finset.mem_image.mp ht
    dsimp only [pick]
    rw [dif_pos he]
    exact he.choose_spec
  have hpick (x : SecondExpansionData ι) (hx : x∈s) : pick (sourceTuple p x)=x := by
    obtain ⟨hm,he⟩:=hchoice _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    exact sourceTuple_injective p hp hinj R (hs _ hm) (hs x hx) he
  let label (t : OldTuple):=(∏i∈(pick t).divisor,p i)*(∏i∈(pick t).overlap,p i)
  have hvalid (t : OldTuple) (ht : t∈s.image (sourceTuple p)) :
      Valid t (newLabel t) 1 (newRow t) := by
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp ht
    rw [sourceTuple_newLabel,sourceTuple_newRow]
    exact sourceTuple_valid p x
  have htargets (t : OldTuple) (ht : t∈s.image (sourceTuple p)) : (newLabel t,newRow t)∈T := by
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp ht
    rw [sourceTuple_newLabel,sourceTuple_newRow]
    exact hT x hx
  have hlabel (t : OldTuple) (ht : t∈s.image (sourceTuple p)) : Ideal.span {label t}=newLabel t := by
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp ht
    dsimp only [label]
    rw [hpick x hx,sourceTuple_newLabel]
    exact sourceLabel_span p x
  have hb:=ht ρ hρ p hg H₁ H₂ (s.image (sourceTuple p)) T 1 (fun t=>w (pick t)) B L label
    pool Ψ₁ Ψ₂ m (fun t=>z (pick t)) (fun t=>ud (pick t)) (fun t=>ue (pick t))
    (fun t=>uv (pick t)) (fun t=>kap (pick t)) X₁ X₂
    one_ne_zero hB hL hvalid htargets hT0 hTL
    (fun t ht=>hw _ (hchoice t ht).1) hlabel
  have hsum : tupleSourceSum p hg H₁ H₂ (s.image (sourceTuple p)) (fun t=>w (pick t)) label
      pool Ψ₁ Ψ₂ m A₁ A₂ W V (fun t=>z (pick t)) (fun t=>ud (pick t))
      (fun t=>ue (pick t)) (fun t=>uv (pick t)) (fun t=>kap (pick t)) X₁ X₂ ρ=
      ∑x∈s,w x*postCommonSmoothPair p hg H₁ H₂ pool Ψ₁ Ψ₂ m
        ((∏i∈x.divisor,p i)*(∏i∈x.overlap,p i)) (sourceRow p x) (-sourceRow p x)
        A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ ρ := by
    unfold tupleSourceSum
    rw [Finset.sum_image (fun x hx y hy he=>sourceTuple_injective p hp hinj R (hs x hx) (hs y hy) he)]
    apply Finset.sum_congr rfl
    intro x hx
    dsimp only [label]
    rw [hpick x hx,sourceTuple_newRow]
  rw [hsum] at hb
  simpa only [map_one,Nat.cast_one,mul_one] using hb

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels
open SecondPassIntegration JointLogSeparation
open scoped BigOperators Classical SchwartzMap ContDiff
variable {ι : Type*} [DecidableEq ι] (p : ι→O)

def sourceLogZ (Z X : ℝ) (x : SecondExpansionData ι) : ℝ:=
  Real.log (primeProductNorm p x.overlap*X/(Z/primeProductNorm p x.sourceCommon))
def sourceLogE (E : ℝ) (x : SecondExpansionData ι) : ℝ:=
  Real.log (elementNorm (∏i∈x.divisor,p i)/E)
def sourceLogV (V : ℝ) (x : SecondExpansionData ι) : ℝ:=
  Real.log (primeProductNorm p x.overlap/V)
def sourceLogK (K : ℝ) (x : SecondExpansionData ι) : ℝ:=
  Real.log (elementNorm (sourceRow p x)/K)

/-- Initial normalized sources use the same compact profiles as the general two-pass source. -/
theorem initial_fixed_source_profiles
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0≤A)
    (hU : ∀u,g u≠0→U u=1) (hgA : ∀u,g u≠0→|u|≤A) :
    ∃(A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7→ℝ→ℂ),
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i u,windows i u≠0→|u|≤A+2+1) ∧
      ∀{ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
      (pool R : Finset ι) (s : Finset (SecondExpansionData ι)) (Ψ : O→*ℂ) (m : O)
      (Z H E V X K : ℝ) (negative : Bool) (r : QuadraticRayRing)
      (ray a b : QuadraticRayRing×QuadraticRayRing),
      0<Z → 0<E → 0<V → 0<X → 0<K →
      (∀x∈s,InSourceSector R x) → (∀x∈s,x.frequency≠0) →
      (∀x∈s,|sourceLogZ p Z X x|≤2) → (∀x∈s,|sourceLogE p E x|≤2) →
      (∀x∈s,|sourceLogV p V x|≤2) → (∀x∈s,|sourceLogK p K x|≤2) →
      (∑x∈s,secondFixedExpansionTerm p hg pool Ψ m 1 1
        (normalizedColumn p (fun T=>g (columnLog p Z T))) W H negative r ray a b x)=
      ∑x∈s,secondFixedOuterWeight p hg Ψ m 1 1 Z H negative r ray a b x*
        postCommonSmoothPair p hg
          (combinedFixedColumn p hg negative b.1 a.1 (fun _=>1))
          (combinedFixedColumn p hg negative b.2 a.2 (fun _=>1)) pool Ψ Ψ
          (m*∏i∈R,p i) ((∏i∈x.divisor,p i)*(∏i∈x.overlap,p i))
          (sourceRow p x) (-sourceRow p x) A₁ A₂ W windows
          (sourceLogZ p Z X x) 0 (sourceLogE p E x) (sourceLogV p V x) (sourceLogK p K x)
          X X (H*K/(E^2*V^2*X^2)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩:=full_uniform_fixedExpansion_smooth_profiles
    U hUc hUs g W A 2 hA (by norm_num) hU hgA
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hg pool R s Ψ m Z H E V X K negative r ray a b
    hZ hE hV hX hK hs hk hz he hv hkap
  apply Finset.sum_congr rfl
  intro x hx
  have hzero : |Real.log (elementNorm (1:O)/(1:ℝ))|≤2 := by
    norm_num [elementNorm]
  have hh:=hid p hp hg pool Ψ m 1 1 one_ne_zero Z H 0 hZ negative r ray a b x
    (hs x hx).1 (hk x hx) 1 E V X K (by norm_num) hE hV hX hK
    (hz x hx) hzero (he x hx) (hv x hx) (by simpa only [sourceLogK,sourceRow,one_mul] using hkap x hx)
  simpa only [frequencyTwist_zero,neg_zero,one_mul,mul_one,elementNorm,map_one,norm_one,
    one_pow,div_one,Real.log_one,mul_neg,sourceRow,sourceLogZ,sourceLogE,sourceLogV,sourceLogK,
    (hs x hx).2] using hh

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels
open SecondPassIntegration JointLogSeparation
open scoped BigOperators Classical SchwartzMap ContDiff

/-- Each initial logarithmic sector is bounded by its actual descendant density energy. -/
theorem initial_sector_density_bound
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0≤A) (hgA : ∀u,g u≠0→|u|≤A)
    (ε : ℝ) (hε : 0<ε) (N J : ℕ) :
    ∃(windows : Fin 7→ℝ→ℂ) (C : ℝ),0≤C ∧
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i u,windows i u≠0→|u|≤A+2+1) ∧
      ∀{ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i})) (hpr : ∀i,lambda^2∣p i-1)
      (pool R : Finset ι) (s : Finset (SecondExpansionData ι)) (T : Finset (Ideal O×O))
      (Ψ : O→*ℂ) (m : O) (Z H E V X K L : ℝ) (negative : Bool) (r : QuadraticRayRing)
      (ray a b : QuadraticRayRing×QuadraticRayRing),
      0<Z → 0<H → 0<E → 0<V → 0<X → 0<K → 0≤L → (∀u,‖Ψ u‖≤1) →
      (∀x∈s,InSourceSector R x) → (∀x∈s,x.frequency≠0) →
      (∀x∈s,|sourceLogZ p Z X x|≤2) → (∀x∈s,|sourceLogE p E x|≤2) →
      (∀x∈s,|sourceLogV p V x|≤2) → (∀x∈s,|sourceLogK p K x|≤2) →
      (∀x∈s,(sourceLabel p x,sourceRow p x)∈T) →
      (∀t∈T,t.1≠0) → (∀t∈T,(Ideal.absNorm t.1:ℝ)≤L) →
      (1+H*K/(E^2*V^2*X^2))^N*
        ‖∑x∈s,secondFixedExpansionTerm p hg pool Ψ m 1 1
          (normalizedColumn p (fun T=>g (columnLog p Z T))) W H negative r ray a b x‖≤
      C*H*primeProductNorm p R/Z^2*‖rayQuadraticPair ray.1 ray.2‖*L^ε*
        densityChildEnergy p hg
          (combinedFixedColumn p hg negative b.1 a.1 (fun _=>1))
          (combinedFixedColumn p hg negative b.2 a.2 (fun _=>1))
          pool Ψ Ψ (m*∏i∈R,p i) T (windows 5) (windows 6) X X J := by
  obtain ⟨U,hUc,hUs,hUone,_⟩:=exists_complex_smooth_cutoff A hA
  have hU : ∀u,g u≠0→U u=1:=fun u hu=>hUone u (hgA u hu)
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hprofiles⟩:=initial_fixed_source_profiles
    U hUc hUs g W A hA hU hgA
  obtain ⟨Cw,hCw,hw⟩:=outerWindow_global_bound windows hwc (fun i=>(hws i).continuous)
  have hrad : 0≤A+2+1:=by linarith
  obtain ⟨Ct,hCt,htransfer⟩:=uniform_initial_source_density_transfer ε hε A₁ A₂ W windows
    (fun _=>A+2+1) (fun _=>hrad) hwb N J
  refine ⟨windows,Cw*Ct,mul_nonneg hCw hCt,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hg hinj hpr pool R s T Ψ m Z H E V X K L negative r ray a b
    hZ hH hE hV hX hK hL hΨ hs hk hz he hv hkap hT hT0 hTL
  let B:=H*primeProductNorm p R/Z^2*‖rayQuadraticPair ray.1 ray.2‖*Cw
  have hNR:=primeProductNorm_pos p hp R
  have hB : 0≤B:=by dsimp only [B]; positivity
  have hweight (x : SecondExpansionData ι) (hx : x∈s) :
      ‖secondFixedOuterWeight p hg Ψ m 1 1 Z H negative r ray a b x‖*
        ‖outerWindow windows (sourceLogZ p Z X x) 0 (sourceLogE p E x)
          (sourceLogV p V x) (sourceLogK p K x)‖≤B := by
    have ho:=secondFixedOuterWeight_norm_le p hp hg hinj hpr Ψ hΨ m 1 1 Z H hZ hH.le
      negative r ray a b x (hs x hx).1
    rw [(hs x hx).2] at ho
    exact mul_le_mul ho (hw _ _ _ _ _) (norm_nonneg _) (by positivity)
  have hρ : 0<H*K/(E^2*V^2*X^2):=by positivity
  have hb:=htransfer (H*K/(E^2*V^2*X^2)) hρ p hp hg hinj
    (combinedFixedColumn p hg negative b.1 a.1 (fun _=>1))
    (combinedFixedColumn p hg negative b.2 a.2 (fun _=>1)) R s T
    (secondFixedOuterWeight p hg Ψ m 1 1 Z H negative r ray a b) B L pool Ψ Ψ
    (m*∏i∈R,p i) (sourceLogZ p Z X) (fun _=>0) (sourceLogE p E)
    (sourceLogV p V) (sourceLogK p K) X X hB hL hs hT hT0 hTL hweight
  rw [hprofiles p hp hg pool R s Ψ m Z H E V X K negative r ray a b
    hZ hE hV hX hK hs hk hz he hv hkap]
  exact hb.trans_eq (by dsimp only [B]; ring)

end InitialMeanSquare

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CanonicalCoefficientClass
open scoped BigOperators Classical

/-- Initial scale and mask inequalities imply the canonical state for any nonzero mask. -/
theorem initialCanonicalState_mask
    (bad : Ideal O) (base Ψ : O→*ℂ) (hΨ : IsBaseRayTwist base Ψ)
    (m : O) (hm : m≠0) (Z η X F K : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hX : 0<X) (hF : 1≤F) (hK : 1≤K)
    (T : Finset (Ideal O×O)) (hmass : X*F≤Z^2)
    (hinv : K*‖ringComplex m‖^2≤X*F*Z^(-(1:ℝ)/20))
    (hlabels : ∀z∈T,z.1≠0 ∧ Squarefree z.1 ∧ IsCoprime z.1 bad ∧ (Ideal.absNorm z.1:ℝ)≤F) :
    CanonicalStateCondition base bad Z η Ψ m (T.image Prod.fst) X F K := by
  have hN:=element_norm_ge_one m hm
  have hdecay : Z^(-(1:ℝ)/20)≤1:=by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hZ (by norm_num : -(1:ℝ)/20≤0)
  have hKmass : K≤X*F :=
    (le_mul_of_one_le_right (zero_le_one.trans hK) hN).trans
      (hinv.trans (mul_le_of_le_one_right (mul_nonneg hX.le (zero_le_one.trans hF)) hdecay))
  refine ⟨hΨ,hm,hX,hF,hK,
    (hKmass.trans hmass).trans (pow_le_pow_right₀ hZ (by decide : (2:ℕ)≤3)),
    hmass.trans (canonicalRankMass_initial Z _),?_,?_⟩
  · apply hinv.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hX.le (zero_le_one.trans hF))
    apply Real.rpow_le_rpow_of_exponent_le hZ
    unfold canonicalRankMargin
    have hn : 0≤η*((3000-fixedDepthRank Z K:ℕ):ℝ):=mul_nonneg hη (Nat.cast_nonneg _)
    linarith
  · intro I hI
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hI
    exact hlabels z hz

end CanonicalRowCompletion

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels SecondPassIntegration
open scoped BigOperators Classical

abbrev SecondLogIndex:=ℕ×ℕ×ℕ
def secondLogE (j : SecondLogIndex) : ℝ:=normLogScale j.1
def secondLogV (j : SecondLogIndex) : ℝ:=normLogScale j.2.1
def secondLogK (j : SecondLogIndex) : ℝ:=normLogScale j.2.2

def initialLogColumn (Z B : ℝ) (j : SecondLogIndex) : ℝ:=Z/(secondLogE j*secondLogV j*B)
def initialLogLabel (j : SecondLogIndex) : ℝ:=secondLogE j*secondLogV j*Real.exp 2
def initialRadial (Z H B : ℝ) (j : SecondLogIndex) : ℝ:=H*secondLogK j*B^2/Z^2

variable {ι : Type*} [DecidableEq ι] (p : ι→O)
def initialLogIndex (x : SecondExpansionData ι) : SecondLogIndex:=
  (normLogBin (primeProductNorm p x.divisor),normLogBin (primeProductNorm p x.overlap),
    normLogBin (elementNorm (sourceRow p x)))

lemma sourceRow_ne_zero (hp : ∀i,p i≠0) (x : SecondExpansionData ι) (hk : x.frequency≠0) :
    sourceRow p x≠0:=mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)) hk

lemma sourceLabel_norm (x : SecondExpansionData ι) :
    (Ideal.absNorm (sourceLabel p x):ℝ)=primeProductNorm p x.divisor*primeProductNorm p x.overlap := by
  rw [sourceLabel,map_mul,Nat.cast_mul,←primeProductNorm_eq_ideal_norm,←primeProductNorm_eq_ideal_norm]

/-- Logarithmic representatives keep all four profile arguments in one fixed compact interval. -/
theorem initial_log_coordinates (hp : ∀i,p i≠0) (Z : ℝ) (hZ : 0 < Z)
    (R : Finset ι) (x : SecondExpansionData ι) (hs : InSourceSector R x) (hk : x.frequency≠0) :
    let j:=initialLogIndex p x
    let X:=initialLogColumn Z (primeProductNorm p R) j
    |sourceLogZ p Z X x| ≤ 2 ∧ |sourceLogE p (secondLogE j) x| ≤ 2 ∧
      |sourceLogV p (secondLogV j) x| ≤ 2 ∧ |sourceLogK p (secondLogK j) x| ≤ 2 := by
  dsimp only
  have he:=normLogBin_error _ (primeProductNorm_ge_one p hp x.divisor)
  have hv:=normLogBin_error _ (primeProductNorm_ge_one p hp x.overlap)
  have hk':=normLogBin_error _ (element_norm_ge_one _ (sourceRow_ne_zero p hp x hk))
  have hE0:=(primeProductNorm_pos p hp x.divisor).ne'
  have hV0:=(primeProductNorm_pos p hp x.overlap).ne'
  have hB0:=(primeProductNorm_pos p hp R).ne'
  have hE1:=(normLogScale_pos (normLogBin (primeProductNorm p x.divisor))).ne'
  have hV1:=(normLogScale_pos (normLogBin (primeProductNorm p x.overlap))).ne'
  have hG : primeProductNorm p x.sourceCommon=primeProductNorm p x.divisor*primeProductNorm p R := by
    rw [←hs.2,←primeProductNorm_union p _ _ disjoint_sdiff_self_right,Finset.union_sdiff_of_subset hs.1]
  have hratio : primeProductNorm p x.overlap*initialLogColumn Z (primeProductNorm p R)
      (initialLogIndex p x)/(Z/primeProductNorm p x.sourceCommon)=
      (primeProductNorm p x.divisor/normLogScale (normLogBin (primeProductNorm p x.divisor)))*
      (primeProductNorm p x.overlap/normLogScale (normLogBin (primeProductNorm p x.overlap))) := by
    simp only [initialLogColumn,initialLogIndex,secondLogE,secondLogV,hG]
    field_simp [hZ.ne',hB0,hE0,hE1,hV1] <;> ring
  refine ⟨?_,?_,?_,?_⟩
  · unfold sourceLogZ
    rw [hratio,Real.log_mul (div_ne_zero hE0 hE1) (div_ne_zero hV0 hV1),
      abs_of_nonneg (add_nonneg he.1 hv.1)]
    linarith only [he.2,hv.2]
  · change |Real.log (primeProductNorm p x.divisor/normLogScale (normLogBin _))| ≤ 2
    rw [abs_of_nonneg he.1]
    linarith only [he.2]
  · change |Real.log (primeProductNorm p x.overlap/normLogScale (normLogBin _))| ≤ 2
    rw [abs_of_nonneg hv.1]
    linarith only [hv.2]
  · change |Real.log (‖ringComplex (sourceRow p x)‖^2/normLogScale (normLogBin (‖ringComplex (sourceRow p x)‖^2)))| ≤ 2
    rw [abs_of_nonneg hk'.1]
    linarith only [hk'.2]

/-- One logarithmic index bounds the label and the nonzero descendant row. -/
theorem initial_log_target_bounds (hp : ∀i,p i≠0) (x : SecondExpansionData ι) (hk : x.frequency≠0) :
    (Ideal.absNorm (sourceLabel p x):ℝ) ≤ initialLogLabel (initialLogIndex p x) ∧
      ‖ringComplex (sourceRow p x)‖^2 ≤ secondLogK (initialLogIndex p x)*Real.exp 1 := by
  have he:=(normLogBin_scale_bounds _ (primeProductNorm_ge_one p hp x.divisor)).2
  have hv:=(normLogBin_scale_bounds _ (primeProductNorm_ge_one p hp x.overlap)).2
  have hk':=(normLogBin_scale_bounds _ (element_norm_ge_one _ (sourceRow_ne_zero p hp x hk))).2
  refine ⟨?_,hk'⟩
  rw [sourceLabel_norm]
  have hh:=mul_le_mul he hv (primeProductNorm_pos p hp _).le
    (mul_nonneg (normLogScale_pos _).le (Real.exp_pos _).le)
  simpa only [initialLogLabel,initialLogIndex,secondLogE,secondLogV,
    show (2:ℝ)=1+1 by norm_num,Real.exp_add,mul_assoc,mul_left_comm,mul_comm] using hh

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels SecondPassIntegration
open scoped BigOperators Classical

theorem initial_log_mass (Z B : ℝ) (hB : B≠0) (j : SecondLogIndex) :
    initialLogColumn Z B j*initialLogLabel j=Z/B*Real.exp 2 := by
  have he := (normLogScale_pos j.1).ne'
  have hv := (normLogScale_pos j.2.1).ne'
  unfold initialLogColumn initialLogLabel secondLogE secondLogV
  field_simp

theorem initial_log_radial (Z H B : ℝ) (hZ : Z≠0) (hB : B≠0) (j : SecondLogIndex) :
    H*secondLogK j/(secondLogE j^2*secondLogV j^2*initialLogColumn Z B j^2)=
      H*secondLogK j*B^2/Z^2 := by
  have he := (normLogScale_pos j.1).ne'
  have hv := (normLogScale_pos j.2.1).ne'
  unfold initialLogColumn secondLogE secondLogV
  field_simp

lemma initialLogColumn_pos (Z B : ℝ) (j : SecondLogIndex) (hZ : 0 < Z) (hB : 0 < B) :
    0 < initialLogColumn Z B j :=
  div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hB)

lemma initialLogColumn_le (Z B : ℝ) (j : SecondLogIndex) (hZ : 0 ≤ Z) (hB : 1 ≤ B) :
    initialLogColumn Z B j ≤ Z := div_le_self hZ
  (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _)) hB)


theorem initial_radial_invariant (Z B c σ θ deltaLoss κ : ℝ) (j : SecondLogIndex)
    (hZ : 1 ≤ Z) (hB : 0 < B) (hc : 0 ≤ c) (hcZ : c ≤ Z^deltaLoss)
    (hmargin : deltaLoss+θ ≤ σ-κ)
    (hrad : initialRadial Z (Z^(1+σ)) B j ≤ Z^θ) :
    (secondLogK j*Real.exp 2)*(c*B) ≤ 
      initialLogColumn Z B j*initialLogLabel j*Z^(-κ) := by
  have hZ0 := zero_lt_one.trans_le hZ
  have hH : 0 < Z^(1+σ) := Real.rpow_pos_of_pos hZ0 _
  have hm : 0 < initialLogColumn Z B j*initialLogLabel j := by
    rw [initial_log_mass Z B hB.ne' j]
    positivity
  have he : Z/Z^(1+σ)=Z^(-σ) := by
    rw [show -σ=(1 : ℝ)-(1+σ) by ring,Real.rpow_sub hZ0,Real.rpow_one]
  have hid : (secondLogK j*Real.exp 2)*(c*B)/(initialLogColumn Z B j*initialLogLabel j)=
      c*(Z/(Z^(1+σ)))*(Z^(1+σ)*secondLogK j*B^2/Z^2) := by
    rw [initial_log_mass Z B hB.ne' j]
    have hE := (Real.exp_pos (2 : ℝ)).ne'
    have hz := hZ0.ne'
    have hh := hH.ne'
    field_simp

  rw [mul_comm (initialLogColumn Z B j*initialLogLabel j)]
  apply (div_le_iff₀ hm).mp
  rw [hid,he]
  calc
    c*Z^(-σ)*(Z^(1+σ)*secondLogK j*B^2/Z^2) ≤ c*Z^(-σ)*Z^θ :=
      mul_le_mul_of_nonneg_left hrad (mul_nonneg hc (Real.rpow_nonneg hZ0.le _))
    _ ≤ Z^deltaLoss*Z^(-σ)*Z^θ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcZ (Real.rpow_nonneg hZ0.le _)) (Real.rpow_nonneg hZ0.le _)
    _ = Z^(deltaLoss-σ+θ) := by rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]; congr 1
    _ ≤ Z^(-κ) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)


/-- A retained radial sector satisfies the initial rank mass and mask inequalities. -/
theorem initial_retained_geometry (Z B c σ θ δ : ℝ) (j : SecondLogIndex)
    (hZ : 1 ≤ Z) (hlarge : Real.exp 2 ≤ Z) (hB : 1 ≤ B) (hc : 0 ≤ c)
    (hcZ : c ≤ Z^δ) (hmargin : δ+θ ≤ σ-(1:ℝ)/20)
    (hrad : initialRadial Z (Z^(1+σ)) B j ≤ Z^θ) :
    0 < initialLogColumn Z B j ∧ 1 ≤ initialLogLabel j ∧ 1 ≤ secondLogK j*Real.exp 2 ∧
      initialLogColumn Z B j*initialLogLabel j ≤ Z^2 ∧
      (secondLogK j*Real.exp 2)*(c*B) ≤ 
        initialLogColumn Z B j*initialLogLabel j*Z^(-(1:ℝ)/20) := by
  have hZ0:=zero_lt_one.trans_le hZ
  have hB0:=zero_lt_one.trans_le hB
  refine ⟨initialLogColumn_pos Z B j hZ0 hB0,?_,?_,?_,?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _))
      (Real.one_le_exp (by norm_num))
  · exact one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  · rw [initial_log_mass Z B hB0.ne' j]
    calc
      _ ≤ Z*Real.exp 2:=mul_le_mul_of_nonneg_right (div_le_self hZ0.le hB) (Real.exp_pos _).le
      _ ≤ Z^2:=by simpa only [pow_two] using mul_le_mul_of_nonneg_left hlarge hZ0.le
  · simpa only [neg_div] using initial_radial_invariant Z B c σ θ δ ((1:ℝ)/20) j hZ hB0 hc hcZ hmargin hrad

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels SecondPassIntegration
open scoped BigOperators Classical SchwartzMap
variable {ι : Type*} [DecidableEq ι] (p : ι→O)

def initialSquarefreeSector (s : Finset (SecondExpansionData ι)) : Finset (SecondExpansionData ι):=
  s.filter (fun x=>Squarefree (sourceLabel p x))

def initialSourceTargets (s : Finset (SecondExpansionData ι)) : Finset (Ideal O×O):=
  (initialSquarefreeSector p s).image (fun x=>(sourceLabel p x,sourceRow p x))

lemma sourceLabel_ne_zero (hp : ∀i,p i≠0) (x : SecondExpansionData ι) : sourceLabel p x≠0 := by
  rw [←sourceLabel_span]
  exact Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
    (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

lemma sourceLabel_coprime (bad : Ideal O) (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (x : SecondExpansionData ι) : IsCoprime (sourceLabel p x) bad:=
  (IsCoprime.prod_left (fun i _=>hbad i)).mul_left
    (IsCoprime.prod_left (fun i _=>hbad i))

/-- The arithmetic coefficient vanishes when the initial descendant label is not squarefree. -/
theorem initial_fixed_source_squarefree [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (H : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
    (Y : ℝ) (negative : Bool) (r : QuadraticRayRing)
    (ray a b : QuadraticRayRing×QuadraticRayRing)
    (s : Finset (SecondExpansionData ι)) (hs : ∀x∈s,x.divisor⊆x.sourceCommon) :
    (∑x∈s,secondFixedExpansionTerm p hg pool Ψ m 1 1 H W Y negative r ray a b x)=
      ∑x∈initialSquarefreeSector p s,
        secondFixedExpansionTerm p hg pool Ψ m 1 1 H W Y negative r ray a b x := by
  rw [initialSquarefreeSector,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hsf : Squarefree (sourceLabel p x)
  · rw [if_pos hsf]
  · rw [if_neg hsf]
    have hw : secondArithmeticWeight p hg Ψ m 1 1 ray x=0 := by
      by_contra hn
      have hh:=secondArithmeticWeight_squarefree p hg hinj Ψ m 1 1 ray x
        (hs x hx) (by simp) hn
      apply hsf
      simpa [sourceLabel] using hh
    unfold secondArithmeticWeight at hw
    simp only [secondFixedExpansionTerm,hw,zero_mul]

/-- Targets in a fixed bin satisfy the label, row, and excluded-prime conditions. -/
theorem initial_source_target_geometry (hp : ∀i,p i≠0)
    (bad : Ideal O) (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (s : Finset (SecondExpansionData ι)) (j : SecondLogIndex)
    (hk : ∀x∈s,x.frequency≠0) (hj : ∀x∈s,initialLogIndex p x=j) :
    ∀t∈initialSourceTargets p s,t.1≠0 ∧ Squarefree t.1 ∧ IsCoprime t.1 bad ∧
      (Ideal.absNorm t.1:ℝ) ≤ initialLogLabel j ∧ t.2≠0 ∧
      ‖ringComplex t.2‖^2 ≤ secondLogK j*Real.exp 2 := by
  intro t ht
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp ht
  obtain ⟨hxs,hxsf⟩:=Finset.mem_filter.mp hx
  have hb:=initial_log_target_bounds p hp x (hk x hxs)
  rw [hj x hxs] at hb
  exact ⟨sourceLabel_ne_zero p hp x,hxsf,sourceLabel_coprime p bad hbad x,hb.1,
    sourceRow_ne_zero p hp x (hk x hxs),hb.2.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num)) (normLogScale_pos _).le)⟩

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels SecondPassIntegration
open scoped BigOperators Classical

def secondLogBinBox (U K : ℝ) : Finset SecondLogIndex:=
  (Finset.range (normLogBin U+1)).product
    ((Finset.range (normLogBin U+1)).product (Finset.range (normLogBin K+1)))

lemma secondLogBinBox_card (U K : ℝ) :
    (secondLogBinBox U K).card=(normLogBin U+1)^2*(normLogBin K+1) := by
  simp only [secondLogBinBox,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.card_product,Finset.card_range]
  ring

lemma initialLogLabel_ge_one (j : SecondLogIndex) : 1 ≤ initialLogLabel j:=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _))
    (Real.one_le_exp (by norm_num))

variable {ι : Type*} [DecidableEq ι] (p : ι→O)

def initialSupportedPool (pool : Finset ι) (K : Finset ι→Finset ι→Finset O) (Z M : ℝ) :
    Finset (SecondExpansionData ι):=
  (secondExpansionPool pool (fun G E=>(K G E).erase 0)).filter (SecondSourceSupport p Z M)

def initialLogSector (pool R : Finset ι) (K : Finset ι→Finset ι→Finset O)
    (Z M : ℝ) (j : SecondLogIndex) : Finset (SecondExpansionData ι):=
  (initialSupportedPool p pool K Z M).filter
    (fun x=>x.sourceCommon\x.divisor=R ∧ initialLogIndex p x=j)

lemma initialLogSector_geometry (pool R : Finset ι) (K : Finset ι→Finset ι→Finset O)
    (Z M : ℝ) (j : SecondLogIndex) (x : SecondExpansionData ι)
    (hx : x∈initialLogSector p pool R K Z M j) :
    InSourceSector R x ∧ x.frequency≠0 ∧ initialLogIndex p x=j ∧ SecondSourceSupport p Z M x := by
  obtain ⟨hx,hR,hj⟩:=Finset.mem_filter.mp hx
  obtain ⟨hx,hs⟩:=Finset.mem_filter.mp hx
  have hm:=(mem_secondExpansionPool _ _ x).mp hx
  exact ⟨⟨hm.2.1,hR⟩,(Finset.mem_erase.mp hm.2.2.2).1,hj,hs⟩

lemma initial_source_support_bounds (hp : ∀i,p i≠0) (Z M : ℝ)
    (x : SecondExpansionData ι) (hs : SecondSourceSupport p Z M x) (hE : x.divisor⊆x.sourceCommon) :
    primeProductNorm p x.sourceCommon ≤ Z*Real.exp M ∧
      primeProductNorm p x.divisor ≤ Z*Real.exp M ∧ primeProductNorm p x.overlap ≤ Z*Real.exp M := by
  have hG : primeProductNorm p x.sourceCommon ≤ Z*Real.exp M:=
    (le_mul_of_one_le_right (primeProductNorm_pos p hp _).le (primeProductNorm_ge_one p hp _)).trans hs.2
  exact ⟨hG,(primeProductNorm_mono p hp hE).trans hG,
    (le_mul_of_one_le_left (primeProductNorm_pos p hp _).le (primeProductNorm_ge_one p hp _)).trans hs.2⟩

lemma initialLogIndex_mem_box (hp : ∀i,p i≠0) (Z M K : ℝ) (x : SecondExpansionData ι)
    (hs : SecondSourceSupport p Z M x) (hE : x.divisor⊆x.sourceCommon)
    (hk : x.frequency≠0) (hK : elementNorm (sourceRow p x) ≤ K) :
    initialLogIndex p x∈secondLogBinBox (Z*Real.exp M) K := by
  obtain ⟨hG,hE',hV⟩:=initial_source_support_bounds p hp Z M x hs hE
  simp only [initialLogIndex,secondLogBinBox,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range,Nat.lt_succ_iff]
  exact ⟨normLogBin_mono (primeProductNorm_pos p hp _) hE',
    normLogBin_mono (primeProductNorm_pos p hp _) hV,
    normLogBin_mono (elementNorm_pos _ (sourceRow_ne_zero p hp x hk)) hK⟩

lemma initialLogLabel_cap (U K : ℝ) (hU : 1 ≤ U) (j : SecondLogIndex)
    (hj : j∈secondLogBinBox U K) : initialLogLabel j ≤ U^2*Real.exp 2 := by
  have hj' : j.1 < normLogBin U+1 ∧ j.2.1 < normLogBin U+1 ∧ j.2.2 < normLogBin K+1:=by
    simpa only [secondLogBinBox,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range] using hj
  have he : secondLogE j ≤ U:=by
    apply le_trans _ (normLogBin_scale_bounds U hU).1
    unfold secondLogE normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.1
  have hv : secondLogV j ≤ U:=by
    apply le_trans _ (normLogBin_scale_bounds U hU).1
    unfold secondLogV normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.2.1
  unfold initialLogLabel
  simpa only [pow_two] using mul_le_mul_of_nonneg_right
    (mul_le_mul he hv (normLogScale_pos _).le (zero_le_one.trans hU)) (Real.exp_pos 2).le

lemma initial_bin_row_scale_le (U K : ℝ) (hK : 1 ≤ K) (j : SecondLogIndex)
    (hj : j∈secondLogBinBox U K) : secondLogK j ≤ K := by
  have hj' : j.1 < normLogBin U+1 ∧ j.2.1 < normLogBin U+1 ∧ j.2.2 < normLogBin K+1:=by
    simpa only [secondLogBinBox,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range] using hj
  have hscale : secondLogK j ≤ normLogScale (normLogBin K):=by
    unfold secondLogK normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.2.2
  exact hscale.trans (normLogBin_scale_bounds K hK).1

/-- Three logarithmic indices and the harmonic support sum cost arbitrarily small powers. -/
theorem initial_log_harmonic_small_power (η : ℝ) (hη : 0 < η) :
    ∃C : ℝ,0 < C ∧ ∀Y U K : ℝ,1 ≤ Y → 0 < U → 0 < K → U ≤ Y → K ≤ Y →
      ((secondLogBinBox U K).card:ℝ)*(descentLatticeConstant*Real.exp 1*(normLogBin U+1:ℝ)) ≤ C*Y^η := by
  obtain ⟨C,hC,hbound⟩:=globalLogFactor_small_power η hη
  have hdc:=descentLatticeConstant_pos
  refine ⟨descentLatticeConstant*Real.exp 1*C,by positivity,?_⟩
  intro Y U K hY hU hK hUY hKY
  let B:=1+Real.log 27+22*Real.log Y
  have hlog:=Real.log_nonneg hY
  have h27 : 0 ≤ Real.log 27:=Real.log_nonneg (by norm_num)
  have hB : 1 ≤ B:=by dsimp [B]; linarith
  have hu:=normLogBin_le_log_upper U Y hU.le hUY hY
  have hk:=normLogBin_le_log_upper K Y hK.le hKY hY
  have huB : (normLogBin U:ℝ)+1 ≤ B:=by dsimp [B]; linarith
  have hkB : (normLogBin K:ℝ)+1 ≤ B:=by dsimp [B]; linarith
  have hcard : ((secondLogBinBox U K).card:ℝ) ≤ B^3:=by
    rw [secondLogBinBox_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ B^2*B:=mul_le_mul (pow_le_pow_left₀ (by positivity) huB 2) hkB (by positivity) (sq_nonneg B)
      _=B^3:=by ring
  have hh : descentLatticeConstant*Real.exp 1*(normLogBin U+1:ℝ) ≤ descentLatticeConstant*Real.exp 1*B:=
    mul_le_mul_of_nonneg_left huB (by positivity)
  calc
    _ ≤ B^3*(descentLatticeConstant*Real.exp 1*B):=mul_le_mul hcard hh (by positivity) (by positivity)
    _=descentLatticeConstant*Real.exp 1*B^4:=by ring
    _ ≤ descentLatticeConstant*Real.exp 1*B^10:=mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hB (by decide)) (by positivity)
    _ ≤ descentLatticeConstant*Real.exp 1*(C*Y^η):=mul_le_mul_of_nonneg_left (hbound Y hY) (by positivity)
    _= _:=by ring

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels SecondPassIntegration
open scoped BigOperators Classical SchwartzMap

/-- Total mass of the finite quadratic residue factors. -/
def initialRayMass : ℝ:=∑ray : QuadraticRayRing×QuadraticRayRing,‖rayQuadraticPair ray.1 ray.2‖

lemma initialRayMass_nonneg : 0 ≤ initialRayMass:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)

variable {ι : Type*} [DecidableEq ι] (p : ι→O)

theorem initial_harmonic_aggregation [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (U K D : ℝ) (hD : 0 ≤ D)
    (a : (QuadraticRayRing×QuadraticRayRing)→Finset ι→SecondLogIndex→ℝ)
    (ha : ∀ray,∀R∈boundedPrimeSupports p pool U,∀j∈secondLogBinBox U K,
      a ray R j ≤ D/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖) :
    (∑ray : QuadraticRayRing×QuadraticRayRing,∑R∈boundedPrimeSupports p pool U,
      ∑j∈secondLogBinBox U K,a ray R j) ≤ 
      D*initialRayMass*((secondLogBinBox U K).card:ℝ)*
        (descentLatticeConstant*Real.exp 1*(normLogBin U+1:ℝ)) := by
  let B:=secondLogBinBox U K
  let C:=descentLatticeConstant*Real.exp 1*(normLogBin U+1:ℝ)
  have hsum:=primeSupport_inverse_sum p hinj (boundedPrimeSupports p pool U) U
    (fun R hR=>(Finset.mem_filter.mp hR).2)
  have hinner (ray : QuadraticRayRing×QuadraticRayRing) :
      (∑R∈boundedPrimeSupports p pool U,∑j∈B,a ray R j) ≤ 
        (D*‖rayQuadraticPair ray.1 ray.2‖*(B.card:ℝ))*C := by
    calc
      _ ≤ ∑R∈boundedPrimeSupports p pool U,∑_j∈B,
          D/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖:=by
        apply Finset.sum_le_sum
        intro R hR
        exact Finset.sum_le_sum (fun j hj=>ha ray R hR j hj)
      _=(D*‖rayQuadraticPair ray.1 ray.2‖*(B.card:ℝ))*
          ∑R∈boundedPrimeSupports p pool U,1/primeProductNorm p R:=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro R hR
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
      _ ≤ _:=mul_le_mul_of_nonneg_left hsum (by positivity)
  calc
    _ ≤ ∑ray : QuadraticRayRing×QuadraticRayRing,(D*‖rayQuadraticPair ray.1 ray.2‖*(B.card:ℝ))*C:=
      Finset.sum_le_sum (fun ray _=>hinner ray)
    _= _:=by
      unfold initialRayMass
      simp only [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hray
      ring

/-- Every supported row belongs to a bounded residual support and one logarithmic bin. -/
theorem initial_supported_pool_binning (hp : ∀i,p i≠0)
    (pool : Finset ι) (K : Finset ι→Finset ι→Finset O) (Z M Kmax : ℝ)
    (hK : ∀x∈initialSupportedPool p pool K Z M,elementNorm (sourceRow p x) ≤ Kmax)
    (f : SecondExpansionData ι→ℂ) :
    (∑x∈initialSupportedPool p pool K Z M,f x)=
      ∑R∈boundedPrimeSupports p pool (Z*Real.exp M),∑j∈secondLogBinBox (Z*Real.exp M) Kmax,
        ∑x∈initialLogSector p pool R K Z M j,f x := by
  let s:=initialSupportedPool p pool K Z M
  let Q:=(boundedPrimeSupports p pool (Z*Real.exp M)).product (secondLogBinBox (Z*Real.exp M) Kmax)
  let key:=fun x : SecondExpansionData ι=>(x.sourceCommon\x.divisor,initialLogIndex p x)
  have hm (x : SecondExpansionData ι) (hx : x∈s) : key x∈Q := by
    obtain ⟨hx',hs⟩:=Finset.mem_filter.mp hx
    have hp':=(mem_secondExpansionPool _ _ x).mp hx'
    have hbounds:=initial_source_support_bounds p hp Z M x hs hp'.2.1
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.sdiff_subset.trans hp'.1),?_⟩,?_⟩
    · exact (primeProductNorm_mono p hp Finset.sdiff_subset).trans hbounds.1
    · exact initialLogIndex_mem_box p hp Z M Kmax x hs hp'.2.1
        (Finset.mem_erase.mp hp'.2.2.2).1 (hK x hx)
  have he:=(Finset.sum_fiberwise_of_maps_to hm f).symm
  simp only [Q,Finset.product_eq_sprod,Finset.sum_product] at he
  exact he.trans (by
    apply Finset.sum_congr rfl
    intro R hR
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr _ (fun _ _=>rfl)
    apply Finset.filter_congr
    intro x hx
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩
    · rintro ⟨h₁,h₂⟩
      exact Prod.ext h₁ h₂)

/-- Removing unsupported rows and partitioning the rest preserves the literal fixed-residue source. -/
theorem initial_fixed_source_eq_bins (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i})
    (pool : Finset ι) (K : Finset ι→Finset ι→Finset O) (Ψ : O→*ℂ)
    (g W : 𝓢(ℝ,ℂ)) (Z H M Kmax : ℝ) (hZ : 0 < Z) (hgM : ∀u,g u≠0→|u| ≤ M)
    (negative : Bool) (r : QuadraticRayRing) (ray a b : QuadraticRayRing×QuadraticRayRing)
    (hK : ∀x∈initialSupportedPool p pool K Z M,elementNorm (sourceRow p x) ≤ Kmax) :
    (∑x∈secondExpansionPool pool (fun G E=>(K G E).erase 0),
      secondFixedExpansionTerm p hg pool Ψ 1 1 1
        (normalizedColumn p (fun T=>g (columnLog p Z T))) W H negative r ray a b x)=
    ∑R∈boundedPrimeSupports p pool (Z*Real.exp M),∑j∈secondLogBinBox (Z*Real.exp M) Kmax,
      ∑x∈initialLogSector p pool R K Z M j,
        secondFixedExpansionTerm p hg pool Ψ 1 1 1
          (normalizedColumn p (fun T=>g (columnLog p Z T))) W H negative r ray a b x := by
  rw [←initial_supported_pool_binning p hp pool K Z M Kmax hK]
  unfold initialSupportedPool
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : SecondSourceSupport p Z M x
  · rw [if_pos hs]
  · rw [if_neg hs]
    exact secondFixedExpansionTerm_zero_off_support p hp hg pool Ψ 1 1 1 g W Z H M hZ hgM
      negative r ray a b x ((mem_secondExpansionPool _ _ x).mp hx).2.1 hs

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels SecondPassIntegration
open JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
local instance : Finite Oˣ:=cubic_units_finite
local instance : Fintype Oˣ:=Fintype.ofFinite _

/-- The elementary density bound is quadratic in the column-label mass. -/
theorem initial_density_elementary_squared_mass
    {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i})) (hpr : ∀i,lambda^2∣p i-1)
    (H₁ H₂ : Finset ι→ℂ) (hH₁ : ∀S,‖H₁ S‖ ≤ 1) (hH₂ : ∀S,‖H₂ S‖ ≤ 1)
    (pool : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (hΨ₁ : ∀u,‖Ψ₁ u‖ ≤ 1) (hΨ₂ : ∀u,‖Ψ₂ u‖ ≤ 1)
    (m : O) (T : Finset (Ideal O×O)) (V₁ V₂ : ℝ→ℂ)
    (X L K A M : ℝ) (J : ℕ) (hX : 0 < X) (hL : 1 ≤ L) (hK : 1 ≤ K) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV₁ : ∀u,‖V₁ u‖ ≤ M) (hV₂ : ∀u,‖V₂ u‖ ≤ M)
    (hs₁ : ∀u,V₁ u≠0→|u| ≤ A) (hs₂ : ∀u,V₂ u≠0→|u| ≤ A)
    (hT : ∀t∈T,t.1≠0 ∧ (Ideal.absNorm t.1:ℝ) ≤ L ∧ ‖ringComplex t.2‖^2 ≤ K) :
    densityChildEnergy p hg H₁ H₂ pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J) ≤ 
      ((Fintype.card Oˣ:ℝ)*(diagonalControl sieveCutoff)^4*(Real.exp A*M)^2*
        (∫t : ℝ,firstLogDensity 0 t)^3)*K*(X*L)^2 := by
  let C:=(Fintype.card Oˣ:ℝ)*(diagonalControl sieveCutoff)^4*(Real.exp A*M)^2*
    (∫t : ℝ,firstLogDensity 0 t)^3
  have hI : 0 ≤ ∫t : ℝ,firstLogDensity 0 t:=integral_nonneg (fun t=>firstLogDensity_nonneg 0 t)
  have hC : 0 ≤ C:=by dsimp [C]; positivity
  have hd:=childDensity_elementary_all_scales p hp hg hinj hpr H₁ H₂ hH₁ hH₂ pool Ψ₁ Ψ₂
    hΨ₁ hΨ₂ m T V₁ V₂ X L K A M J hX hL hK hA hM hV₁ hV₂ hs₁ hs₂ hT
  have hXL : 0 < X*L:=mul_pos hX (zero_lt_one.trans_le hL)
  have hx : X ≤ X*L:=le_mul_of_one_le_right hX.le hL
  calc
    _ ≤ (C*K*X)*(X*L):=(div_le_iff₀ hXL).mp hd
    _ ≤ (C*K*(X*L))*(X*L):=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hx (mul_nonneg hC (zero_le_one.trans hK))) hXL.le
    _= _:=by dsimp only [C]; ring

/-- One power of radial decay absorbs the descendant row scale. -/
theorem initial_radial_absorbs_row (Z H B k : ℝ) (N : ℕ)
    (hZ : 0 < Z) (hH : 0 ≤ H) (hB : 1 ≤ B) (hk : 0 ≤ k) :
    H*k/(1+H*k*B^2/Z^2)^(N+1) ≤ Z^2/(1+H*k*B^2/Z^2)^N := by
  let r:=H*k*B^2/Z^2
  have hr : 0 ≤ r:=by dsimp [r]; positivity
  have h1 : 0 < 1+r:=by linarith
  have hnum : H*k ≤ Z^2*r:=by
    have he : Z^2*r=H*k*B^2:=by dsimp [r]; field_simp
    rw [he]
    exact le_mul_of_one_le_right (mul_nonneg hH hk) (one_le_pow₀ hB)
  change H*k/(1+r)^(N+1) ≤ Z^2/(1+r)^N
  calc
    _ ≤ Z^2*r/(1+r)^(N+1):=div_le_div_of_nonneg_right hnum (pow_nonneg h1.le _)
    _ ≤ Z^2*(1+r)/(1+r)^(N+1):=div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg Z)) (pow_nonneg h1.le _)
    _= _:=by rw [pow_succ]; field_simp [h1.ne'] <;> ring

/-- All initial bins have arbitrarily strong radial decay, with an elementary polynomial cost. -/
theorem initial_fixed_source_radial_decay
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A) (hgA : ∀u,g u≠0→|u| ≤ A) (N : ℕ) :
    ∃C : ℝ,0 < C ∧ ∀{ι : Type} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i})) (hpr : ∀i,lambda^2∣p i-1)
      (pool R : Finset ι) (s : Finset (SecondExpansionData ι)) (Ψ : O→*ℂ)
      (Z H : ℝ) (negative : Bool) (r : QuadraticRayRing) (ray a b : QuadraticRayRing×QuadraticRayRing)
      (j : SecondLogIndex),
      0 < Z → 0 < H → (∀u,‖Ψ u‖ ≤ 1) → (∀x∈s,InSourceSector R x) →
      (∀x∈s,x.frequency≠0) → (∀x∈s,initialLogIndex p x=j) →
      ‖∑x∈s,secondFixedExpansionTerm p hg pool Ψ 1 1 1
        (normalizedColumn p (fun T=>g (columnLog p Z T))) W H negative r ray a b x‖ ≤ 
        C*Z^2/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖*initialLogLabel j/
          (1+initialRadial Z H (primeProductNorm p R) j)^N := by
  obtain ⟨windows,Ct,hCt,hwc,hws,hwb,ht⟩:=initial_sector_density_bound g W A hA hgA 1 (by norm_num) (N+1) 0
  have hb (i : Fin 7) : ∃B : ℝ,0 ≤ B ∧ ∀u,‖windows i u‖ ≤ B:=by
    obtain ⟨B,hB⟩:=((hwc i).isCompact_range (hws i).continuous).bddAbove_image continuous_norm.continuousOn
    have hh (u : ℝ) : ‖windows i u‖ ≤ B:=hB ⟨windows i u,⟨u,rfl⟩,rfl⟩
    exact ⟨B,(norm_nonneg _).trans (hh 0),hh⟩
  obtain ⟨M₁,hM₁,hv₁⟩:=hb 5
  obtain ⟨M₂,hM₂,hv₂⟩:=hb 6
  let M:=max M₁ M₂
  let Ce:=(Fintype.card Oˣ:ℝ)*(diagonalControl sieveCutoff)^4*(Real.exp (A+2+1)*M)^2*
    (∫t : ℝ,firstLogDensity 0 t)^3
  have hI : 0 ≤ ∫t : ℝ,firstLogDensity 0 t:=integral_nonneg (fun t=>firstLogDensity_nonneg 0 t)
  have hCe : 0 ≤ Ce:=by dsimp [Ce]; positivity
  let C:=Ct*Ce*Real.exp 6
  have hC : 0 ≤ C:=by dsimp [C]; positivity
  refine ⟨C+1,by linarith,?_⟩
  intro ι _ p hp _ hg hinj hpr pool R s Ψ Z H negative r ray a b j hZ hH hΨ hs hk hj
  let X:=initialLogColumn Z (primeProductNorm p R) j
  let T:=initialSourceTargets p s
  have hBp:=primeProductNorm_pos p hp R
  have hX : 0 < X:=initialLogColumn_pos _ _ _ hZ hBp
  have hL:=initialLogLabel_ge_one j
  have hK : 1 ≤ secondLogK j*Real.exp 2:=one_le_mul_of_one_le_of_one_le
    (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  have htarget:=initial_source_target_geometry p hp 1 (fun _=>Ideal.isCoprime_iff_sup_eq.mpr (by simp)) s j hk hj
  have hc₁ (U : Finset ι) : ‖combinedFixedColumn p hg negative b.1 a.1 (fun _=>1) U‖ ≤ 1:=by
    simpa only [norm_one] using combinedFixedColumn_norm_le p hg negative b.1 a.1 (fun _=>1) U
  have hc₂ (U : Finset ι) : ‖combinedFixedColumn p hg negative b.2 a.2 (fun _=>1) U‖ ≤ 1:=by
    simpa only [norm_one] using combinedFixedColumn_norm_le p hg negative b.2 a.2 (fun _=>1) U
  have hdensity:=initial_density_elementary_squared_mass p hp hg hinj hpr _ _ hc₁ hc₂ pool Ψ Ψ hΨ hΨ
    (∏i∈R,p i) T (windows 5) (windows 6) X (initialLogLabel j) (secondLogK j*Real.exp 2)
    (A+2+1) M 0 hX hL hK (by linarith) (hM₁.trans (le_max_left _ _))
    (fun u=>(hv₁ u).trans (le_max_left _ _)) (fun u=>(hv₂ u).trans (le_max_right _ _))
    (hwb 5) (hwb 6) (fun t ht=>⟨(htarget t ht).1,(htarget t ht).2.2.2.1,(htarget t ht).2.2.2.2.2⟩)
  have hcoords (x : SecondExpansionData ι) (hx : x∈initialSquarefreeSector p s) := by
    have hxs:=(Finset.mem_filter.mp hx).1
    have hh:=initial_log_coordinates p hp Z hZ R x (hs x hxs) (hk x hxs)
    dsimp only at hh
    rw [hj x hxs] at hh
    exact hh
  have hsource:=ht p hp hg hinj hpr pool R (initialSquarefreeSector p s) T Ψ 1 Z H
    (secondLogE j) (secondLogV j) X (secondLogK j) (initialLogLabel j) negative r ray a b
    hZ hH (normLogScale_pos _) (normLogScale_pos _) hX (normLogScale_pos _) (zero_le_one.trans hL) hΨ
    (fun x hx=>hs x (Finset.mem_filter.mp hx).1) (fun x hx=>hk x (Finset.mem_filter.mp hx).1)
    (fun x hx=>(hcoords x hx).1) (fun x hx=>(hcoords x hx).2.1)
    (fun x hx=>(hcoords x hx).2.2.1) (fun x hx=>(hcoords x hx).2.2.2)
    (fun x hx=>Finset.mem_image_of_mem _ hx) (fun t ht=>(htarget t ht).1)
    (fun t ht=>(htarget t ht).2.2.2.1)
  dsimp only [X] at hsource
  rw [initial_log_radial Z H _ hZ.ne' hBp.ne' j] at hsource
  simp only [one_mul,Real.rpow_one] at hsource
  rw [initial_fixed_source_squarefree p hg hinj pool Ψ 1
    (normalizedColumn p (fun T=>g (columnLog p Z T))) W H negative r ray a b s
    (fun x hx=>(hs x hx).1)]
  have hρ : 0 ≤ initialRadial Z H (primeProductNorm p R) j:=by
    have hk0:=(normLogScale_pos j.2.2).le
    dsimp only [initialRadial,secondLogK]
    positivity
  have hden : 0 < (1+initialRadial Z H (primeProductNorm p R) j)^(N+1):=by positivity
  have hf : 0 ≤ Ct*H*primeProductNorm p R/Z^2*‖rayQuadraticPair ray.1 ray.2‖*initialLogLabel j:=by positivity
  have htotal:=hsource.trans (mul_le_mul_of_nonneg_left hdensity hf)
  have heq : Real.exp 2*(Real.exp 2)^2=Real.exp 6:=by rw [pow_two,←Real.exp_add,←Real.exp_add]; norm_num
  have halgebra : (Ct*H*primeProductNorm p R/Z^2*‖rayQuadraticPair ray.1 ray.2‖*initialLogLabel j)*
      (Ce*(secondLogK j*Real.exp 2)*(X*initialLogLabel j)^2)=
      (C/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖*initialLogLabel j)*(H*secondLogK j):=by
    dsimp only [X]
    rw [initial_log_mass Z _ hBp.ne' j,mul_pow,div_pow]
    dsimp only [C]
    rw [←heq]
    field_simp <;> ring
  change _ ≤ (Ct*H*primeProductNorm p R/Z^2*‖rayQuadraticPair ray.1 ray.2‖*initialLogLabel j)*
      (Ce*(secondLogK j*Real.exp 2)*(X*initialLogLabel j)^2) at htotal
  rw [halgebra] at htotal
  rw [mul_comm ((1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+1))] at htotal
  have hb:=(le_div_iff₀ hden).mpr htotal
  calc
    _ ≤ (C/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖*initialLogLabel j)*
        (H*secondLogK j/(1+initialRadial Z H (primeProductNorm p R) j)^(N+1)):=by
      simpa only [mul_div_assoc] using hb
    _ ≤ (C/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖*initialLogLabel j)*
        (Z^2/(1+initialRadial Z H (primeProductNorm p R) j)^N):=mul_le_mul_of_nonneg_left
      (initial_radial_absorbs_row Z H (primeProductNorm p R) (secondLogK j) N hZ hH.le
        (primeProductNorm_ge_one p hp R) (normLogScale_pos _).le) (by positivity)
    _=C*Z^2/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖*initialLogLabel j/
        (1+initialRadial Z H (primeProductNorm p R) j)^N:=by ring
    _ ≤ _:=by gcongr; linarith

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels
open scoped BigOperators Classical

/-- Polynomial support and row cutoffs leave only a small-power loss after bin aggregation. -/
theorem initial_label_log_budget (η Ccap : ℝ) (hη : 0 < η) (hcap : 1 ≤ Ccap) :
    ∃C : ℝ,0 < C ∧ ∀Z U K : ℝ,1 ≤ Z → 0 < U → 0 < K →
      U ≤ Ccap*Z^17 → K ≤ Ccap*Z^17 →
      (U^2*Real.exp 2)^η*((secondLogBinBox U K).card:ℝ)*
        (descentLatticeConstant*Real.exp 1*(normLogBin U+1:ℝ)) ≤ C*Z^(51*η) := by
  obtain ⟨C,hC,hlog⟩:=initial_log_harmonic_small_power η hη
  refine ⟨C*(Real.exp 2)^η*Ccap^(3*η),by positivity,?_⟩
  intro Z U K hZ hU hK hUY hKY
  have hZ0:=zero_lt_one.trans_le hZ
  have hcap0:=zero_lt_one.trans_le hcap
  let Y:=Ccap*Z^17
  have hY : 1 ≤ Y:=one_le_mul_of_one_le_of_one_le hcap (one_le_pow₀ hZ)
  have hY0:=zero_lt_one.trans_le hY
  have hdc:=descentLatticeConstant_pos
  have hlogs:=hlog Y U K hY hU hK hUY hKY
  have hlabel : (U^2*Real.exp 2)^η ≤ (Y^2*Real.exp 2)^η:=Real.rpow_le_rpow
    (by positivity) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hU.le hUY 2) (Real.exp_pos _).le) hη.le
  calc
    _=(U^2*Real.exp 2)^η*(((secondLogBinBox U K).card:ℝ)*
        (descentLatticeConstant*Real.exp 1*(normLogBin U+1:ℝ))):=by ring
    _ ≤ (Y^2*Real.exp 2)^η*(C*Y^η):=mul_le_mul hlabel hlogs (by positivity) (by positivity)
    _=C*(Real.exp 2)^η*Y^(3*η):=by
      rw [Real.mul_rpow (sq_nonneg Y) (Real.exp_pos _).le,←Real.rpow_natCast_mul hY0.le]
      norm_num
      rw [show 3*η=2*η+η by ring,Real.rpow_add hY0]
      ring
    _=(C*(Real.exp 2)^η*Ccap^(3*η))*Z^(51*η):=by
      dsimp [Y]
      rw [Real.mul_rpow hcap0.le (pow_nonneg hZ0.le _),←Real.rpow_natCast_mul hZ0.le]
      norm_num
      ring_nf

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels SecondPassIntegration
open scoped BigOperators Classical SchwartzMap

/-- The discarded radial bins have any prescribed power saving. -/
theorem initial_high_radial_sum
    (g W : 𝓢(ℝ,ℂ)) (A Ccap θ τ : ℝ) (hA : 0 ≤ A) (hcap : 1 ≤ Ccap)
    (hgA : ∀u,g u≠0→|u| ≤ A) (hθ : 0 < θ) :
    ∃C : ℝ,0 < C ∧ ∀{ι : Type} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i})) (hpr : ∀i,lambda^2∣p i-1)
      (pool : Finset ι) (K : Finset ι→Finset ι→Finset O) (Ψ : O→*ℂ)
      (Z H Kmax : ℝ) (negative : Bool) (r : QuadraticRayRing) (a b : QuadraticRayRing×QuadraticRayRing),
      1 ≤ Z → 0 < H → 0 < Kmax → (∀u,‖Ψ u‖ ≤ 1) →
      Z*Real.exp A ≤ Ccap*Z^17 → Kmax ≤ Ccap*Z^17 →
      (∑ray : QuadraticRayRing×QuadraticRayRing,∑R∈boundedPrimeSupports p pool (Z*Real.exp A),
        ∑j∈secondLogBinBox (Z*Real.exp A) Kmax,
          if Z^θ < initialRadial Z H (primeProductNorm p R) j then
            ‖∑x∈initialLogSector p pool R K Z A j,
              secondFixedExpansionTerm p hg pool Ψ 1 1 1
                (normalizedColumn p (fun T=>g (columnLog p Z T))) W H negative r ray a b x‖ else 0) ≤ C*Z^(-τ) := by
  obtain ⟨N,hN⟩:=exists_nat_gt ((21+τ)/θ)
  have horder : 21+τ ≤ θ*(N:ℝ):=by
    have hh:=(div_lt_iff₀ hθ).mp hN
    nlinarith only [hh]
  obtain ⟨Cb,hCb,hbin⟩:=initial_fixed_source_radial_decay g W A hA hgA N
  obtain ⟨Cl,hCl,hlog⟩:=initial_log_harmonic_small_power 1 (by norm_num)
  have hmass:=initialRayMass_nonneg
  let C0:=Cb*(Real.exp A)^2*Real.exp 2*initialRayMass*Cl*Ccap
  have hC0 : 0 ≤ C0:=by dsimp [C0]; positivity
  refine ⟨C0+1,by linarith,?_⟩
  intro ι _ p hp _ hg hinj hpr pool K Ψ Z H Kmax negative r a b hZ hH hK hΨ hUcap hKcap
  have hZp:=zero_lt_one.trans_le hZ
  let U:=Z*Real.exp A
  have hU : 1 ≤ U:=one_le_mul_of_one_le_of_one_le hZ (Real.one_le_exp hA)
  let B:=Cb*Z^2*(U^2*Real.exp 2)/(Z^θ)^N
  have hB : 0 ≤ B:=by dsimp [B]; positivity
  let f:=fun (ray : QuadraticRayRing×QuadraticRayRing) (R : Finset ι) (j : SecondLogIndex)=>
    if Z^θ < initialRadial Z H (primeProductNorm p R) j then
      ‖∑x∈initialLogSector p pool R K Z A j,secondFixedExpansionTerm p hg pool Ψ 1 1 1
        (normalizedColumn p (fun T=>g (columnLog p Z T))) W H negative r ray a b x‖ else 0
  have hpoint (ray : QuadraticRayRing×QuadraticRayRing) (R : Finset ι)
      (hR : R∈boundedPrimeSupports p pool U) (j : SecondLogIndex) (hj : j∈secondLogBinBox U Kmax) :
      f ray R j ≤ B/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖ := by
    dsimp only [f]
    have hRp:=primeProductNorm_pos p hp R
    split_ifs with hrad
    · have hs:=initialLogSector_geometry p pool R K Z A j
      have hb:=hbin p hp hg hinj hpr pool R (initialLogSector p pool R K Z A j) Ψ Z H
        negative r ray a b j hZp hH hΨ (fun x hx=>(hs x hx).1)
        (fun x hx=>(hs x hx).2.1) (fun x hx=>(hs x hx).2.2.1)
      have hden : (Z^θ)^N ≤ (1+initialRadial Z H (primeProductNorm p R) j)^N:=
        pow_le_pow_left₀ (Real.rpow_nonneg hZp.le _) (by linarith) N
      have hnum : 0 ≤ Cb*Z^2/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖*initialLogLabel j:=by
        have hl:=initialLogLabel_ge_one j
        positivity
      calc
        _ ≤ Cb*Z^2/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖*initialLogLabel j/
            (1+initialRadial Z H (primeProductNorm p R) j)^N:=hb
        _ ≤ Cb*Z^2/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖*initialLogLabel j/(Z^θ)^N:=
          div_le_div_of_nonneg_left hnum (pow_pos (Real.rpow_pos_of_pos hZp _) _) hden
        _ ≤ Cb*Z^2/primeProductNorm p R*‖rayQuadraticPair ray.1 ray.2‖*(U^2*Real.exp 2)/(Z^θ)^N:=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (initialLogLabel_cap U Kmax hU j hj)
            (by positivity)) (by positivity)
        _= _:=by dsimp [B]; ring
    · positivity
  have hsum:=initial_harmonic_aggregation p hinj pool U Kmax B hB f hpoint
  have hY : 1 ≤ Ccap*Z^17:=one_le_mul_of_one_le_of_one_le hcap (one_le_pow₀ hZ)
  have hlogs:=hlog (Ccap*Z^17) U Kmax hY (zero_lt_one.trans_le hU) hK hUcap hKcap
  rw [Real.rpow_one] at hlogs
  have hscalar : Z^(21:ℕ)/(Z^θ)^N ≤ Z^(-τ):=by
    have he : Z^(21:ℕ)/(Z^θ)^N=Z^((21:ℝ)-θ*(N:ℝ)):=by
      rw [Real.rpow_sub hZp,Real.rpow_mul_natCast hZp.le]
      norm_cast
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ B*initialRayMass*((secondLogBinBox U Kmax).card:ℝ)*
        (descentLatticeConstant*Real.exp 1*(normLogBin U+1:ℝ)):=hsum
    _=(B*initialRayMass)*(((secondLogBinBox U Kmax).card:ℝ)*
        (descentLatticeConstant*Real.exp 1*(normLogBin U+1:ℝ))):=by ring
    _ ≤ (B*initialRayMass)*(Cl*(Ccap*Z^17)):=mul_le_mul_of_nonneg_left hlogs (by positivity)
    _=C0*(Z^(21:ℕ)/(Z^θ)^N):=by dsimp [B,U,C0]; ring
    _ ≤ C0*Z^(-τ):=mul_le_mul_of_nonneg_left hscalar hC0
    _ ≤ (C0+1)*Z^(-τ):=mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZp.le _)

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels SecondPassIntegration
open scoped BigOperators Classical

/-- A polynomial frequency disk makes the complementary source tail negligible. -/
def initialFrequencyCutoff (A Z H : ℝ) : Finset O:=secondTailCutoff (Z*Real.exp A) H (Z^12)

def initialRowCutoff (A Z : ℝ) : ℝ:=Real.exp (4*A)*Z^17

lemma initial_polynomial_caps (A Z : ℝ) (hA : 0 ≤ A) (hZ : 1 ≤ Z) :
    1 ≤ Real.exp (4*A) ∧ 0 < initialRowCutoff A Z ∧ Z*Real.exp A ≤ Real.exp (4*A)*Z^17 := by
  have hZp:=zero_lt_one.trans_le hZ
  refine ⟨Real.one_le_exp (by linarith),by unfold initialRowCutoff; positivity,?_⟩
  have he : Real.exp A ≤ Real.exp (4*A):=Real.exp_le_exp.mpr (by linarith)
  have hz : Z ≤ Z^17:=by simpa only [pow_one] using pow_le_pow_right₀ hZ (by decide : 1 ≤ 17)
  calc
    _ ≤ Z^17*Real.exp (4*A):=mul_le_mul hz he (Real.exp_pos _).le (pow_nonneg hZp.le _)
    _= _:=by ring

/-- Supported source rows fit the polynomial row cutoff for the concrete frequency disk. -/
theorem initial_frequency_cutoff_row_bound {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) (pool : Finset ι) (A Z H : ℝ)
    (hA : 0 ≤ A) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    ∀x∈initialSupportedPool p pool (fun _ _=>initialFrequencyCutoff A Z H) Z A,
      elementNorm (sourceRow p x) ≤ initialRowCutoff A Z := by
  intro x hx
  obtain ⟨hx,hs⟩:=Finset.mem_filter.mp hx
  have hm:=(mem_secondExpansionPool _ _ x).mp hx
  have hb:=(initial_source_support_bounds p hp Z A x hs hm.2.1).2.1
  have hZp:=zero_lt_one.trans_le hZ
  have hHp:=zero_lt_one.trans_le hH
  have hf:=secondTailCutoff_norm_sq_le (Z*Real.exp A) H (Z^12) (by positivity) hHp
    (by positivity) x.frequency (Finset.mem_erase.mp hm.2.2.2).2
  have he : elementNorm (sourceRow p x)=primeProductNorm p x.divisor*‖ringComplex x.frequency‖^2:=by
    simp only [elementNorm,sourceRow,map_mul,norm_mul,mul_pow,primeProductNorm]
  rw [he]
  calc
    _ ≤ (Z*Real.exp A)*(Z^12*(Z*Real.exp A)^3/H):=
      mul_le_mul hb hf (sq_nonneg _) (by positivity)
    _=(Z^12*(Z*Real.exp A)^4)/H:=by ring
    _ ≤ Z^12*(Z*Real.exp A)^4:=div_le_self (by positivity) hH
    _=(Real.exp A)^4*Z^16:=by ring
    _=Real.exp (4*A)*Z^16:=by rw [←Real.exp_nat_mul]; norm_num
    _ ≤ initialRowCutoff A Z:=by
      unfold initialRowCutoff
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ (by decide)) (Real.exp_pos _).le

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels SecondPassIntegration
open scoped BigOperators Classical SchwartzMap

/-- The concrete frequency disk controls the entire complementary lattice tail uniformly in the prime pool. -/
theorem initial_source_tail_bound
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A) (hgA : ∀u,g u≠0→|u| ≤ A) :
    ∃C : ℝ,0 < C ∧ ∀{ι : Type} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i})) (pool : Finset ι) (Ψ : O→*ℂ)
      (Z H : ℝ) (negative : Bool) (r : QuadraticRayRing),
      1 ≤ Z → 1 ≤ H → (∀u,‖Ψ u‖ ≤ 1) →
      ‖secondSourceTail p hp hg pool Ψ 1 1 1
        (firstFixedColumn p hg negative r (normalizedColumn p (fun T=>g (columnLog p Z T))))
        W H (fun _ _=>initialFrequencyCutoff A Z H)‖ ≤ C*H := by
  obtain ⟨s,Cs,hCs,hbound⟩:=full_uniform_secondSourceTail_bounded_test 1
  let B:=SchwartzMap.seminorm ℝ 0 0 g
  let CW:=Cs*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B:=apply_nonneg _ _
  have hCW : 0 ≤ CW:=mul_nonneg hCs.le (apply_nonneg _ _)
  let C0:=(diagonalControl sieveCutoff)^4*B^2*CW*4*(Real.exp A)^10
  have hC0 : 0 ≤ C0:=by dsimp [C0]; positivity
  refine ⟨C0+1,by linarith,?_⟩
  intro ι _ p hp _ hg hinj pool Ψ Z H negative r hZ hH hΨ
  let L:=Z*Real.exp A
  have hZp:=zero_lt_one.trans_le hZ
  have hHp:=zero_lt_one.trans_le hH
  have hL : 1 ≤ L:=one_le_mul_of_one_le_of_one_le hZ (Real.one_le_exp hA)
  let col:=firstFixedColumn p hg negative r (normalizedColumn p (fun T=>g (columnLog p Z T)))
  have hcol (U : Finset ι) : ‖col U‖ ≤ B:=
    (firstFixedColumn_norm_le p hg negative r _ U).trans (normalizedColumn_schwartz_bound p hp g Z U)
  have hsupp (U : Finset ι) (hU : col U≠0) : primeProductNorm p U ≤ L := by
    have hn : normalizedColumn p (fun T=>g (columnLog p Z T)) U≠0:=by
      intro hz
      have hh:=firstFixedColumn_norm_le p hg negative r (normalizedColumn p (fun T=>g (columnLog p Z T))) U
      rw [hz,norm_zero] at hh
      exact hU (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
    have hg0 : g (columnLog p Z U)≠0:=by
      intro hz
      exact hn (by simp only [normalizedColumn,hz,zero_div])
    exact columnLog_norm_upper p hp Z A hZp U ((le_abs_self _).trans (hgA _ hg0))
  have hb:=hbound p hp hg hinj pool Ψ 1 1 1 col W B L H (Z^12) hΨ hB hL hHp
    (by positivity) hcol hsupp
  have hL3 : 1 ≤ L^3:=one_le_pow₀ hL
  have hscale : 1+L^3/H ≤ 2*L^3:=by
    have hh:=div_le_self (pow_nonneg (zero_le_one.trans hL) 3) hH
    linarith
  have hr : Z^10/(1+Z^12) ≤ (1:ℝ):=by
    apply (div_le_one (by positivity : 0 < 1+Z^12)).mpr
    exact (pow_le_pow_right₀ hZ (by decide : 10 ≤ 12)).trans (by linarith)
  calc
    _ ≤ (diagonalControl sieveCutoff*L)^4*(B^2*(H*CW*(1+L^3/H)^2/(1+Z^12)^1)):=hb
    _ ≤ (diagonalControl sieveCutoff*L)^4*(B^2*(H*CW*(2*L^3)^2/(1+Z^12))):=by
      rw [pow_one]
      gcongr
    _=C0*H*(Z^10/(1+Z^12)):=by dsimp [C0,L]; ring
    _ ≤ C0*H:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr (mul_nonneg hC0 hHp.le)
    _ ≤ (C0+1)*H:=mul_le_mul_of_nonneg_right (by linarith) hHp.le

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels SecondPassIntegration
open scoped BigOperators Classical SchwartzMap

/-- The zero frequency is bounded by the normalized diagonal column mass. -/
theorem initial_zero_frequency_bound
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hgA : ∀u,g u≠0→|u| ≤ A) :
    ∃C : ℝ,0 < C ∧ ∀{ι : Type} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i})) (pool : Finset ι) (Ψ : O→*ℂ)
      (Z H : ℝ) (negative : Bool) (r : QuadraticRayRing),
      0 < Z → 0 ≤ H → (∀u,‖Ψ u‖ ≤ 1) →
      ‖truncatedSecondZero p hg pool Ψ 1 1 1
        (firstFixedColumn p hg negative r (normalizedColumn p (fun T=>g (columnLog p Z T))))
        W H (fun _ _=>initialFrequencyCutoff A Z H)‖ ≤ C*H := by
  obtain ⟨Cm,hCm,hmass⟩:=full_uniform_normalized_second_mass g A hgA
  refine ⟨‖paperRadialFourier W 0‖*Cm+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj pool Ψ Z H negative r hZ hH hΨ
  have hm:=(Finset.sum_le_sum (fun U (hU : U∈pool.powerset)=>pow_le_pow_left₀ (norm_nonneg _)
    (secondInputCoefficient_fixedColumn_norm_le p hg Ψ 1 1 1 negative r
      (normalizedColumn p (fun T=>g (columnLog p Z T))) U) 2)).trans
      (hmass p hp hg hinj pool Ψ hΨ 1 1 1 Z hZ)
  have hz:=truncatedSecondZero_norm_le p hg hinj pool Ψ 1 1 1
    (firstFixedColumn p hg negative r (normalizedColumn p (fun T=>g (columnLog p Z T))))
    W H (fun _ _=>initialFrequencyCutoff A Z H)
    (fun _ _ _ _=>zero_mem_secondTailCutoff (Z*Real.exp A) H (Z^12))
  rw [abs_of_nonneg hH] at hz
  calc
    _ ≤ H*‖paperRadialFourier W 0‖*Cm:=hz.trans (mul_le_mul_of_nonneg_left hm (by positivity))
    _ ≤ (‖paperRadialFourier W 0‖*Cm+1)*H:=by nlinarith only [hH]

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CanonicalRowCompletion
open scoped BigOperators Classical

lemma cubicTwoSupplement_mod_four (x y : O) (hxy : x-y∈Ideal.span {(4:O)}) :
    cubicTwoSupplement x=cubicTwoSupplement y := by
  have h2 : x-y∈cubicTwoIdeal:=by
    obtain ⟨k,hk⟩:=Ideal.mem_span_singleton.mp hxy
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-2*k,?_⟩
    change x-y=(-2:O)*(-2*k)
    rw [hk]
    ring
  change complexCubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal x)=
    complexCubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal y)
  rw [Ideal.Quotient.eq.mpr h2]

/-- The phase at four is constant on a primary residue class modulo four. -/
def initialResiduePhase (r : QuadraticRayRing) : ℂ:=cubicTwoSupplement (Quotient.out r)

lemma initialResiduePhase_mk (x : O) :
    initialResiduePhase (Ideal.Quotient.mk (Ideal.span {(4:O)}) x)=cubicTwoSupplement x :=
  cubicTwoSupplement_mod_four _ _ (Ideal.Quotient.eq.mp (Quotient.out_eq _))

lemma initialResiduePhase_norm (r : QuadraticRayRing) : ‖initialResiduePhase r‖ ≤ 1:=
  cubicTwoSupplement_norm _

variable {ι : Type*} [DecidableEq ι] (p : ι→O)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

lemma initial_row_four (hodd : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀i,lambda^2∣p i-1) (U : Finset ι) :
    primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) U 4=
      cubicTwoSupplement (∏i∈U,p i) := by
  simp only [primeSubsetRow,map_ofNat,map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  have hgen : primaryGenerator (Ideal.span {p i}) (hg i)=p i:=by
    have hspec:=primaryGenerator_spec (Ideal.span {p i}) (hg i)
    exact primary_associated_eq _ _ (Ideal.span_singleton_eq_span_singleton.mp hspec.1.symm)
      hspec.2 (hpr i)
  have hh:=complexSextic_four_eq_fixed_two (Ideal.span {p i}) (hg i) (hodd i)
  rw [hgen] at hh
  exact hh

/-- Residue columns reconstruct the original column after cancelling their fixed cubic phase. -/
theorem initial_column_residue_reconstruction
    (hodd : ∀i,ringChar (O⧸Ideal.span {p i})≠2) (hpr : ∀i,lambda^2∣p i-1)
    (H : Finset ι→ℂ) (U : Finset ι) :
    H U=∑r : QuadraticRayRing,initialResiduePhase r*firstFixedColumn p hg false r H U := by
  have hfour:=primeSubsetRow_diagonal p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) U 4
  rw [primeCoprimeMask_four p hodd U] at hfour
  symm
  simp only [firstFixedColumn,firstResidueMask,Bool.false_eq_true,ite_false,mul_one,
    mul_ite,mul_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [initialResiduePhase_mk,←initial_row_four p hg hodd hpr U]
  calc
    _=(star (primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) U 4)*
        primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) U 4)*H U:=by ring
    _=H U:=by rw [hfour,one_mul]

/-- The original row is a finite linear combination of the controlled residue rows. -/
theorem initial_row_residue_reconstruction
    (hodd : ∀i,ringChar (O⧸Ideal.span {p i})≠2) (hpr : ∀i,lambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (H : Finset ι→ℂ) (z : O) :
    inputConjugateRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) pool Ψ 1 1 1 H z=
      ∑r : QuadraticRayRing,initialResiduePhase r*
        inputConjugateRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) pool Ψ 1 1 1
          (firstFixedColumn p hg false r H) z := by
  unfold inputConjugateRow supportConjugateSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  have hh:=initial_column_residue_reconstruction p hg hodd hpr H U
  unfold secondInputCoefficient
  rw [hh]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  ring

end InitialMeanSquare

namespace InitialMeanSquare
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CanonicalRowCompletion
open scoped BigOperators Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι→O)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

/-- Cauchy--Schwarz removes the finite residue decomposition at constant cost. -/
theorem initial_row_residue_norm_sq
    (hodd : ∀i,ringChar (O⧸Ideal.span {p i})≠2) (hpr : ∀i,lambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (H : Finset ι→ℂ) (z : O) :
    ‖inputConjugateRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) pool Ψ 1 1 1 H z‖^2 ≤ 
      (Fintype.card QuadraticRayRing:ℝ)*∑r : QuadraticRayRing,
        ‖inputConjugateRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) pool Ψ 1 1 1
          (firstFixedColumn p hg false r H) z‖^2 := by
  rw [initial_row_residue_reconstruction p hg hodd hpr]
  apply (cover_norm_sum_sq_le_card Finset.univ _).trans
  rw [Finset.card_univ]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro r hr
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (initialResiduePhase_norm r)

/-- A positive Schwartz cutoff controls any finite subfamily of rows in its unit disk. -/
theorem initial_input_finite_majorant (pool : Finset ι) (Ψ : O→*ℂ) (col : Finset ι→ℂ)
    (H : ℝ) (hH : 0 < H) (R : Finset O) (hR : ∀z∈R,‖ringComplex z‖^2 ≤ H) :
    (∑z∈R,‖inputConjugateRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i))
      pool Ψ 1 1 1 col z‖^2) ≤ 
      ‖∑'z : O,sieveCutoff (‖ringComplex z‖^2/H)*
        (‖inputConjugateRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i))
          pool Ψ 1 1 1 col z‖^2:ℝ)‖ := by
  let χ:=fun i=>complexSexticChar (Ideal.span {p i}) (hg i)
  let a:=fun U=>supportMobius U*secondInputCoefficient p χ Ψ 1 1 1 col U
  let row:=inputConjugateRow p χ pool Ψ 1 1 1 col
  have hrow (z : O) : ‖row z‖=‖∑U∈pool.powerset,star (a U)*primeSubsetRow p χ U z‖ := by
    rw [←norm_star (row z)]
    simp only [row,inputConjugateRow,supportConjugateSum,a,star_sum,star_mul,star_star]
    congr 1
    apply Finset.sum_congr rfl
    intro U hU
    exact mul_comm _ _
  have hs:=primeSubsetRow_mean_summable p χ pool.powerset (fun U=>U) (fun U=>star (a U))
    sieveCutoff H hH
  have hs' : Summable (fun z : O=>sieveCutoff (‖ringComplex z‖^2/H)*(‖row z‖^2:ℝ)):=
    hs.congr (fun z=>by rw [hrow])
  let F:=fun z : O=>sieveBump (‖ringComplex z‖^2/H)*‖row z‖^2
  have hF (z : O) : 0 ≤ F z:=mul_nonneg sieveBump.nonneg (sq_nonneg _)
  have he (z : O) : sieveCutoff (‖ringComplex z‖^2/H)*(‖row z‖^2:ℝ)=(F z:ℂ):=by
    simp only [F,sieveCutoff_apply,Complex.ofReal_mul]
  have hFs : Summable F:=hs'.norm.congr (fun z=>by
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hF z)])
  calc
    _=∑z∈R,F z:=by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [F,sieveBump_eq_one (div_nonneg (sq_nonneg _) hH.le)
        ((div_le_one hH).mpr (hR z hz)),one_mul]
      rfl
    _ ≤ ∑'z : O,F z:=hFs.sum_le_tsum R (fun z _=>hF z)
    _= _:=by
      change _=‖∑'z : O,sieveCutoff (‖ringComplex z‖^2/H)*(‖row z‖^2:ℝ)‖
      rw [tsum_congr he,←Complex.ofReal_tsum,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (tsum_nonneg hF)]

end InitialMeanSquare

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
