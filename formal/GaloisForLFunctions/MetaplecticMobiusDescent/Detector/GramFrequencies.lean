/-
Gram frequencies adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.GramPeriodicPoisson

/-!
# Gram frequencies

Gram frequencies, canonical lattice blocks and shell profiles; exceptional frequencies and
common residual scales; nonexceptional primes force zero residue mean; weighted frequency
sums.
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
open scoped Classical
namespace ProbeGramCommon
open ProbePhysical _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

abbrev PrimaryElement := {n : O // Supported (Ideal.span {n}) ∧ lambda^2∣n-1}

def primaryIdealEquiv : SupportedIdeal≃PrimaryElement where
  toFun I := ⟨primaryIdealGenerator I.val,(supported_span_primaryIdealGenerator_iff _).mpr I.property,
    (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ I.property)).2⟩
  invFun n := ⟨Ideal.span {n.val},n.property.1⟩
  left_inv I := Subtype.ext (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ I.property)).1
  right_inv n := Subtype.ext (primaryIdealGenerator_span n.val (supported_element_ne_zero _ n.property.1) n.property.2)

lemma primaryCoefficient_nonzero_supported (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (n : O) (hn : primaryCoefficient S hS σ n≠0) :
    Supported (Ideal.span {n}) ∧ lambda^2∣n-1 := by
  have hp : lambda^2∣n-1 := by
    by_contra h
    exact hn (by simp [primaryCoefficient,h])
  have hc : IsCoprime (calibrationForSet S hS).generator n := by
    by_contra h
    exact hn (by rw [primaryCoefficient,if_pos hp,gramCoefficientExtension_zero S hS σ n h])
  have hb := calibration_generator_bad S hS hbad
  exact ⟨supported_of_coprime_bad _ n hb.1 hb.2 hc,hp⟩

lemma primary_factor_right (A n : O) (hA : lambda^2∣A-1) (hAn : lambda^2∣A*n-1) : lambda^2∣n-1 := by
  have h := dvd_sub hAn (hA.mul_right n)
  convert h using 1 ; ring

lemma primaryCoefficient_residual (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (A n : O) (hA : lambda^2∣A-1)
    (hn : primaryCoefficient S hS σ (A*n)≠0) :
    Supported (Ideal.span {n}) ∧ lambda^2∣n-1 := by
  have hs := primaryCoefficient_nonzero_supported S hS hbad σ (A*n) hn
  have hsp : Supported (Ideal.span {A}*Ideal.span {n}) := by
    rw [Ideal.span_singleton_mul_span_singleton]
    exact hs.1
  exact ⟨((supported_mul_iff _ _).mp hsp).2,primary_factor_right A n hA hs.2⟩

theorem primary_ideal_tsum (f : O→ℂ)
    (hz : ∀n,¬(Supported (Ideal.span {n}) ∧ lambda^2∣n-1)→ f n=0) :
    (∑'I : SupportedIdeal,f (primaryIdealGenerator I.val))=∑'n : O,f n := by
  have he := primaryIdealEquiv.tsum_eq (fun n : PrimaryElement=> f n.val)
  change (∑'I : SupportedIdeal,f (primaryIdealGenerator I.val))=∑'n : PrimaryElement,f n.val at he
  rw [he]
  exact tsum_subtype_eq_of_support_subset (by intro n hn;by_contra h;exact hn (hz n h))

theorem primary_ideal_pair_tsum (f : O→ O→ℂ)
    (hl : ∀n m,¬(Supported (Ideal.span {n}) ∧ lambda^2∣n-1)→ f n m=0)
    (hr : ∀n m,¬(Supported (Ideal.span {m}) ∧ lambda^2∣m-1)→ f n m=0) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,f (primaryIdealGenerator I.val) (primaryIdealGenerator J.val))=
      ∑'n : O,∑'m : O,f n m := by
  have hinner (n : O) : (∑'J : SupportedIdeal,f n (primaryIdealGenerator J.val))=∑'m : O,f n m :=
    primary_ideal_tsum (fun m=> f n m) (fun m h=> hr n m h)
  simp_rw [hinner]
  apply primary_ideal_tsum (fun n=>∑'m : O,f n m)
  intro n hn
  simp only [hl n _ hn,tsum_zero]

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open ProbePhysical _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

lemma jointExtension_zero_off_primary_left (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : O)
    (hCd : lambda^2∣C*d-1) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ)
    (n m : O) (hn : ¬(Supported (Ideal.span {n}) ∧ lambda^2∣n-1)) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)=0 := by
  have hz : primaryCoefficient S hS σ (C*(d*n))=0 := by
    by_contra h
    apply hn
    apply primaryCoefficient_residual S hS hbad σ (C*d) n hCd
    simpa only [mul_assoc] using h
  simp only [jointExtension,jointFixed,hz,zero_mul]

lemma jointExtension_zero_off_primary_right (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : O)
    (hCd : lambda^2∣C*d-1) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ)
    (n m : O) (hm : ¬(Supported (Ideal.span {m}) ∧ lambda^2∣m-1)) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)=0 := by
  have hz : primaryCoefficient S hS σ (C*(d*m))=0 := by
    by_contra h
    apply hm
    apply primaryCoefficient_residual S hS hbad σ (C*d) m hCd
    simpa only [mul_assoc] using h
  simp only [jointExtension,jointFixed,hz,star_zero,mul_zero,zero_mul]

theorem jointExtension_ideal_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : O)
    (hCd : lambda^2∣C*d-1) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ) (W : O→ O→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      jointExtension S hS σ C k u a b r hr P hg c (d*primaryIdealGenerator I.val) (d*primaryIdealGenerator J.val)*
        W (primaryIdealGenerator I.val) (primaryIdealGenerator J.val))=
      ∑'n : O,∑'m : O,jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)*W n m := by
  apply primary_ideal_pair_tsum (fun n m=> jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)*W n m)
  · intro n m hn
    rw [jointExtension_zero_off_primary_left S hS hbad σ C k d hCd u a b r hr P hg c n m hn,zero_mul]
  · intro n m hm
    rw [jointExtension_zero_off_primary_right S hS hbad σ C k d hCd u a b r hr P hg c n m hm,zero_mul]

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CompletedGauss  UniqueFactorizationMonoid
open CenteredMomentMobiusRegroup
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma divisorPool_supported (G : Finset SupportedIdeal) (D : Id) (hD : D∈divisorPool G Subtype.val) :
    Supported D := by
  obtain ⟨J,hJ,hd⟩ := Finset.mem_biUnion.mp hD
  exact gram_supported_divisor J.val D J.property ((mem_idealDivisors J.property.1).mp hd)

def poolDivisor (G : Finset SupportedIdeal) (D : Id) : SupportedIdeal :=
  if hD : D∈divisorPool G Subtype.val then ⟨D,divisorPool_supported G D hD⟩
  else ⟨1,by
    constructor
    · exact one_ne_zero
    · intro P hP
      change P∈normalizedFactors (1:Id) at hP
      rw [normalizedFactors_one] at hP
      simp at hP⟩

lemma poolDivisor_val (G : Finset SupportedIdeal) (D : Id) (hD : D∈divisorPool G Subtype.val) :
    (poolDivisor G D).val=D := by simp [poolDivisor,hD]

lemma finite_pair_eq_tsum (F G : Finset SupportedIdeal) (f : SupportedIdeal→ SupportedIdeal→ℂ)
    (hf : ∀I J,I∉F ∨ J∉G→ f I J=0) :
    (∑I∈F,∑J∈G,f I J)=∑'I : SupportedIdeal,∑'J : SupportedIdeal,f I J := by
  have hinner (I : SupportedIdeal) : (∑J∈G,f I J)=∑'J : SupportedIdeal,f I J :=
    (tsum_eq_sum (fun J hJ=> hf I J (Or.inr hJ))).symm
  simp_rw [hinner]
  symm
  apply tsum_eq_sum
  intro I hI
  simp only [hf I _ (Or.inl hI),tsum_zero]

theorem finite_pair_mobius_dilation (F G : Finset SupportedIdeal)
    (f : SupportedIdeal→ SupportedIdeal→ℂ) (hf : ∀I J,I∉F ∨ J∉G→ f I J=0) :
    (∑I∈F,∑J∈G,if IsCoprime I.val J.val then f I J else 0)=
      ∑D∈divisorPool G Subtype.val,(moebius D:ℂ)*
        ∑'I : SupportedIdeal,∑'J : SupportedIdeal,
          f (supportedIdealProduct (poolDivisor G D) I) (supportedIdealProduct (poolDivisor G D) J) := by
  rw [finite_pair_mobius F G Subtype.val Subtype.val (fun J _=> J.property.1) f]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hd := poolDivisor_val G D hD
  rw [finite_pair_eq_tsum F G (fun I J=> if D∣I.val ∧ D∣J.val then f I J else 0) (by
    intro I J h
    simp only [hf I J h,ite_self])]
  convert supported_divisor_pair_tsum (poolDivisor G D) f using 1
  rw [hd]

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open ProbePhysical _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

lemma primary_product (C d : O) (hC : lambda^2∣C-1) (hd : lambda^2∣d-1) : lambda^2∣C*d-1 := by
  have h := dvd_add (hC.mul_right d) hd
  convert h using 1 ; ring

theorem jointExtension_divisor_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k : O) (hC : lambda^2∣C-1)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ)
    (D : SupportedIdeal) (W : O→ O→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      if D.val∣I.val ∧ D.val∣J.val then
        jointExtension S hS σ C k u a b r hr P hg c (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)*
          W (primaryIdealGenerator I.val) (primaryIdealGenerator J.val) else 0)=
      ∑'n : O,∑'m : O,
        jointExtension S hS σ C k u a b r hr P hg c (primaryIdealGenerator D.val*n) (primaryIdealGenerator D.val*m)*
          W (primaryIdealGenerator D.val*n) (primaryIdealGenerator D.val*m) := by
  rw [supported_divisor_pair_tsum D (fun I J=>
    jointExtension S hS σ C k u a b r hr P hg c (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)*
      W (primaryIdealGenerator I.val) (primaryIdealGenerator J.val))]
  simp only [supported_dilation_generator]
  have hd : lambda^2∣primaryIdealGenerator D.val-1 :=
    (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ D.property)).2
  exact jointExtension_ideal_lattice S hS hbad σ C k (primaryIdealGenerator D.val) (primary_product C _ hC hd)
    u a b r hr P hg c (fun n m=> W (primaryIdealGenerator D.val*n) (primaryIdealGenerator D.val*m))

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbeGramCommon
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open  UniqueFactorizationMonoid
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
local notation "Joint" => ProbeGramPeriodicPoisson.Joint

/-- A nonexceptional prime forces zero residue mean and hence decay by Poisson summation. -/
theorem literal_nonexceptional_block (A : ℕ) (hA : 2< A) (a₀ b₀ : ℝ)
    (ha₀ : 0< a₀) (hab : a₀< b₀) :
    ∃H : Finset (ℕ×ℕ),∃K : ℝ,0< K ∧
      ∀{ι : Type*}[Fintype ι],∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C k : O)(_hC : C≠0)(_hk0 : k≠0)(u : Oˣ)(a b : ℕ)(r : O)
      (hr : Supported (Ideal.span {r})),k=u.val*lambda^a*(2:O)^b*r→
      ∀(P : ι→ Id)[_hmax : ∀i,(P i).IsMaximal](hg : ∀i,lambda∉P i)(c : ι→ℕ),
      (∀i,1≤ c i)→ Ideal.span {C}=∏i,P i^c i→
      ∀(p : Id)[_hpmax : p.IsMaximal],p≠0→∀_hgp : lambda∉p,
      ringChar (O⧸p)≠2→(¬p∣jointFixedModulus S hS)→(¬p∣∏i,P i)→
      (¬6∣(normalizedFactors (Ideal.span {k})).count p)→
      ∀(W : SchwartzMap Joint ℂ),ProbeGramAnnularLattice.AnnularSupport a₀ b₀ W→
      ∀(d : O)(N : ℝ),0< N→
      Summable (fun m : O×O=> jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
      ‖∑'m : O×O,jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)‖≤
        K*ProbeGramLatticeDecay.sourceControl H W*(Ideal.absNorm (Ideal.span {C}):ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
            Ideal.absNorm (Ideal.span {k})/N)^A) := by
  obtain ⟨H,K,hK,hengine⟩ := ProbeGramPeriodicPoisson.ideal_annular_periodic_bound A hA a₀ b₀ ha₀ hab
  refine ⟨H,K,hK,?_⟩
  intro ι inst S hS σ C k hC hk0 u a b r hr hk P hmax hg c hc hfac p hpmax hp0 hgp hchar hfixed hcommon he W hW d N hN
  have hcount : (normalizedFactors (Ideal.span {k})).count p=
      (normalizedFactors (Ideal.span {r})).count p := by
    rw [hk]
    exact good_factor_count p hgp hchar u a b r ((_root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve.supported_iff_native _).mp hr)
  have heR : ¬6∣(normalizedFactors (Ideal.span {r})).count p := hcount ▸ he
  obtain ⟨M,hM,hMN,hres⟩ := exists_nonexceptional_residue S hS σ C k hC hk0 u a b r hr hk
    P hg c hc hfac p hp0 hgp hchar hfixed hcommon heR
  let : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient hM
  let : Fintype (O⧸M) := Fintype.ofFinite _
  obtain ⟨f,hf,hfn,hfm⟩ := hres d
  have hmean : (∑'v : (O⧸M)×(O⧸M),f v.1 v.2)=0 := by
    rw [tsum_fintype,Fintype.sum_prod_type]
    exact hfm
  have hh := hengine W hW M hM (fun v=> f v.1 v.2) (Ideal.absNorm (Ideal.span {C}))
    (Nat.cast_nonneg _) (fun v=> hfn v.1 v.2) hmean N hN
  have hfun : (fun m : O×O=> f (ProbeGramPeriodicPoisson.idealQuotientPair M m).1
      (ProbeGramPeriodicPoisson.idealQuotientPair M m).2*W (ProbeGramLatticeDecay.physicalPoint N m))=
      (fun m : O×O=> jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)) := by
    funext m
    rw [ProbeGramPeriodicPoisson.idealQuotientPair,hf]
  rw [hfun] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by unfold ProbeGramLatticeDecay.sourceControl;positivity)
  apply min_le_min_left
  apply pow_le_pow_left₀ (by positivity)
  apply div_le_div_of_nonneg_right _ hN.le
  exact_mod_cast hMN

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open ProbePhysical _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CompletedGauss 
local notation "O" => Eisenstein.O

 def residualScale (C D : SupportedIdeal) (Y : ℝ) : ℝ :=
  Y/((Ideal.absNorm C.val:ℝ)*Ideal.absNorm D.val)

lemma residualScale_pos (C D : SupportedIdeal) (Y : ℝ) (hY : 0< Y) : 0< residualScale C D Y := by
  have hc : (0:ℝ)< Ideal.absNorm C.val := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr C.property.1)
  have hd : (0:ℝ)< Ideal.absNorm D.val := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr D.property.1)
  exact div_pos hY (mul_pos hc hd)

lemma residual_column_ratio (C D I : SupportedIdeal) (Y : ℝ) (hY : 0< Y) :
    (Ideal.absNorm (supportedIdealProduct C (supportedIdealProduct D I)).val:ℝ)/Y=
      (Ideal.absNorm I.val:ℝ)/residualScale C D Y := by
  simp only [supportedIdealProduct,map_mul,Nat.cast_mul,residualScale]
  field_simp

 def frequencyScale (C : SupportedIdeal) (k : O) (Y Q : ℝ) : ℝ :=
  (Ideal.absNorm C.val:ℝ)*‖ringComplex k‖^2/(Y^2/Q)

lemma frequencyScale_nonneg (C : SupportedIdeal) (k : O) (Y Q : ℝ) (hQ : 0≤ Q) :
    0≤ frequencyScale C k Y Q := by unfold frequencyScale;positivity

theorem original_kernel_residual_scale (C D I J : SupportedIdeal) (k : O)
    (Y Q : ℝ) (hY : 0< Y) (hQ : 0< Q) :
    Q*‖ringComplex (primaryIdealGenerator C.val*k)‖^2/
      ‖ringComplex (primaryIdealGenerator (supportedIdealProduct C (supportedIdealProduct D I)).val*
        primaryIdealGenerator (supportedIdealProduct C (supportedIdealProduct D J)).val)‖^2=
      frequencyScale C k Y Q/
        (((Ideal.absNorm I.val:ℝ)/residualScale C D Y)*((Ideal.absNorm J.val:ℝ)/residualScale C D Y)) := by
  rw [lowGram_kernel_scale Y Q hY hQ _ _ (primaryIdealGenerator C.val*k),
    residual_column_ratio C D I Y hY,residual_column_ratio C D J Y hY]
  rw [map_mul,norm_mul,mul_pow,ringComplex_norm_sq_eq_absNorm_span,
    (primaryIdealGenerator_spec C.val (supported_primaryIdealGenerator_ne_zero C.val C.property)).1]
  unfold frequencyScale
  ring

lemma physicalPoint_first_norm (N : ℝ) (hN : 0< N) (m : O×O) :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).1‖^2=‖ringComplex m.1‖^2/N := by
  simp only [ProbeGramLatticeDecay.physicalPoint,ProbeGramLatticeDecay.point,WithLp.ofLp_toLp]
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.sqrt_pos.mpr hN),div_pow,Real.sq_sqrt hN.le]

lemma physicalPoint_second_norm (N : ℝ) (hN : 0< N) (m : O×O) :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).2‖^2=‖ringComplex m.2‖^2/N := by
  simp only [ProbeGramLatticeDecay.physicalPoint,ProbeGramLatticeDecay.point,WithLp.ofLp_toLp]
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.sqrt_pos.mpr hN),div_pow,Real.sq_sqrt hN.le]

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbeGramCommon
open ProbePhysical SchwartzPlanePoisson

def shellProfile (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ) : ℂ :=
  lowGramProfile W v x*star (lowGramProfile W v y)*paperRadialFourier U (T/(x*y))

lemma shellProfile_zero_left (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ)
    (hx : W x=0) : shellProfile W v U T x y=0 := by
  simp [shellProfile,lowGramProfile,hx]

lemma shellProfile_zero_right (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ)
    (hy : W y=0) : shellProfile W v U T x y=0 := by
  simp [shellProfile,lowGramProfile,hy]

theorem shellProfile_weighted_bound (a b B : ℝ) (ha : 0< a) (hB : 0≤ B) (A : ℕ) :
    ∃s : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧
      ∀(W : ℝ→ℂ),(Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤ B)→
      ∀(U : SchwartzMap ℝ ℂ)(v T x y : ℝ),0≤ T→
        (1+T)^A*‖shellProfile W v U T x y‖≤
          C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := by
  obtain ⟨s,C,hC,hpaper⟩ := paperRadialFourier_euler_source_weighted_bound A 0
  refine ⟨s,(1+B/a)^2*(1+b^2)^A*C,by positivity,?_⟩
  intro W hs hW U v T x y hT
  by_cases hx : W x=0
  · rw [shellProfile_zero_left _ _ _ _ _ _ hx,norm_zero,mul_zero]
    positivity
  by_cases hy : W y=0
  · rw [shellProfile_zero_right _ _ _ _ _ _ hy,norm_zero,mul_zero]
    positivity
  have hxa := (hs hx).1
  have hya := (hs hy).1
  have hxb := (hs hx).2
  have hyb := (hs hy).2
  have hx0 := ha.trans_le hxa
  have hy0 := ha.trans_le hya
  have hxy : 0< x*y := mul_pos hx0 hy0
  have hxyb : x*y≤ b^2 := by nlinarith [mul_le_mul hxb hyb hy0.le (hx0.le.trans hxb)]
  have ht : 0≤ T/(x*y) := div_nonneg hT hxy.le
  have hp := hpaper U 0 (by omega) (T/(x*y)) ht
  simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hp
  have hscale : 1+T≤(1+b^2)*(1+T/(x*y)) := by
    have he : T=(x*y)*(T/(x*y)) := by field_simp
    have hbound := mul_le_mul_of_nonneg_right hxyb ht
    rw [←he] at hbound
    nlinarith [sq_nonneg b]
  have hp' : (1+T)^A*‖paperRadialFourier U (T/(x*y))‖≤
      (1+b^2)^A*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) := by
    calc
      _ ≤ ((1+b^2)*(1+T/(x*y)))^A*‖paperRadialFourier U (T/(x*y))‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hscale _) (norm_nonneg _)
      _ = (1+b^2)^A*((1+T/(x*y))^A*‖paperRadialFourier U (T/(x*y))‖) := by rw [mul_pow];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  have hwx : ‖lowGramProfile W v x‖≤1+B/a := by
    rw [lowGramProfile_norm W v x hx0]
    exact (div_le_div₀ hB (hW x) ha hxa).trans (by linarith)
  have hwy : ‖lowGramProfile W v y‖≤1+B/a := by
    rw [lowGramProfile_norm W v y hy0]
    exact (div_le_div₀ hB (hW y) ha hya).trans (by linarith)
  rw [shellProfile,norm_mul,norm_mul,norm_star]
  calc
    _ = (‖lowGramProfile W v x‖*‖lowGramProfile W v y‖)*
        ((1+T)^A*‖paperRadialFourier U (T/(x*y))‖) := by ring
    _ ≤ (1+B/a)^2*((1+b^2)^A*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      apply mul_le_mul _ hp' (by positivity) (by positivity)
      nlinarith [mul_le_mul hwx hwy (norm_nonneg _) (by positivity : 0≤1+B/a)]
    _ = _ := by ring

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open Eisenstein 
local notation "O" => Eisenstein.O

theorem annular_element_count (F : Finset O) (b N : ℝ) (hb : 0≤ b) (hN : 0≤ N)
    (hzero : ∀z∈F,z≠0) (hbound : ∀z∈F,‖ringComplex z‖^2≤ b*N) :
    (F.card:ℝ)≤128*b*N := by
  by_cases hF : F.Nonempty
  · obtain ⟨z,hz⟩ := hF
    have hscale : 1≤ b*N := (SchwartzPlanePoisson.one_le_eisenstein_norm_sq z (hzero z hz)).trans (hbound z hz)
    simpa only [mul_assoc] using EisensteinLatticeCount.finite_element_count_real F (b*N) hscale hbound
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF,Finset.card_empty,Nat.cast_zero]
    positivity

theorem annular_pair_count (F G : Finset O) (b N : ℝ) (hb : 0≤ b) (hN : 0≤ N)
    (hFzero : ∀z∈F,z≠0) (hGzero : ∀z∈G,z≠0)
    (hFbound : ∀z∈F,‖ringComplex z‖^2≤ b*N)
    (hGbound : ∀z∈G,‖ringComplex z‖^2≤ b*N) :
    ((F×ˢG).card:ℝ)≤(128*b)^2*N^2 := by
  rw [Finset.card_product,Nat.cast_mul]
  have hf := annular_element_count F b N hb hN hFzero hFbound
  have hg := annular_element_count G b N hb hN hGzero hGbound
  calc
    _ ≤ (128*b*N)*(128*b*N) := mul_le_mul hf hg (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbeGramCommon
open ProbePhysical _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CompletedGauss 
local notation "O" => Eisenstein.O

def shellLatticeColumns (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0< N) : Finset O :=
  (elementWindow_finite_support W hW N hN).toFinset

lemma shellLatticeColumns_mem (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0< N) (n : O) :
    n∈shellLatticeColumns W hW N hN ↔ W (‖ringComplex n‖^2/N)≠0 := by
  simp only [shellLatticeColumns,Set.Finite.mem_toFinset,Function.mem_support]
  rw [ringComplex_norm_sq_eq_absNorm_span]
  rfl

lemma shellLatticeColumns_nonzero (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0< N)
    (a b : ℝ) (ha : 0< a) (hs : Function.support W⊆Set.Icc a b) (n : O)
    (hn : n∈shellLatticeColumns W hW N hN) : n≠0 := by
  intro hz
  have hh := (hs ((shellLatticeColumns_mem W hW N hN n).mp hn)).1
  simp only [hz,map_zero,norm_zero,zero_pow (by decide : 2≠0),zero_div] at hh
  linarith

lemma shellLatticeColumns_norm (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0< N)
    (a b : ℝ) (hs : Function.support W⊆Set.Icc a b) (n : O)
    (hn : n∈shellLatticeColumns W hW N hN) : ‖ringComplex n‖^2≤ b*N :=
  (div_le_iff₀ hN).mp (hs ((shellLatticeColumns_mem W hW N hN n).mp hn)).2

lemma shell_lattice_support (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0< N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (n m : O)
    (h : n∉shellLatticeColumns W hW N hN ∨ m∉shellLatticeColumns W hW N hN) :
    shellProfile W v U T (‖ringComplex n‖^2/N) (‖ringComplex m‖^2/N)=0 := by
  rcases h with h|h
  · apply shellProfile_zero_left
    simpa only [shellLatticeColumns_mem,not_not] using h
  · apply shellProfile_zero_right
    simpa only [shellLatticeColumns_mem,not_not] using h

lemma shell_lattice_summable (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0< N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (f : O→ O→ℂ) :
    Summable (fun m : O×O=> f m.1 m.2*shellProfile W v U T (‖ringComplex m.1‖^2/N) (‖ringComplex m.2‖^2/N)) := by
  apply summable_of_ne_finset_zero (s:=(shellLatticeColumns W hW N hN)×ˢ(shellLatticeColumns W hW N hN))
  intro m hm
  have h : m.1∉shellLatticeColumns W hW N hN ∨ m.2∉shellLatticeColumns W hW N hN := by simpa only [Finset.mem_product,not_and_or] using hm
  rw [shell_lattice_support W hW N hN U v T m.1 m.2 h,mul_zero]

lemma shell_lattice_tsum (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0< N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (f : O→ O→ℂ) :
    (∑'m : O×O,f m.1 m.2*shellProfile W v U T (‖ringComplex m.1‖^2/N) (‖ringComplex m.2‖^2/N))=
      ∑n∈shellLatticeColumns W hW N hN,∑m∈shellLatticeColumns W hW N hN,
        f n m*shellProfile W v U T (‖ringComplex n‖^2/N) (‖ringComplex m‖^2/N) := by
  rw [tsum_eq_sum (s:=(shellLatticeColumns W hW N hN)×ˢ(shellLatticeColumns W hW N hN)) (by
    intro m hm
    have h : m.1∉shellLatticeColumns W hW N hN ∨ m.2∉shellLatticeColumns W hW N hN := by simpa only [Finset.mem_product,not_and_or] using hm
    rw [shell_lattice_support W hW N hN U v T m.1 m.2 h,mul_zero])]
  exact Finset.sum_product _ _ _

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open  CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

lemma primary_norm (I : SupportedIdeal) :
    ‖ringComplex (primaryIdealGenerator I.val)‖^2=(Ideal.absNorm I.val:ℝ) := by
  rw [ringComplex_norm_sq_eq_absNorm_span,
    (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ I.property)).1]

lemma shell_dilated_column (D I : SupportedIdeal) (N : ℝ) :
    (Ideal.absNorm (supportedIdealProduct D I).val:ℝ)/N=
      ‖ringComplex (primaryIdealGenerator I.val)‖^2/(N/Ideal.absNorm D.val) := by
  rw [primary_norm,supported_dilation_norm,Nat.cast_mul]
  rw [div_div_eq_mul_div]
  ring

lemma shell_window_support (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0< N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (I J : SupportedIdeal)
    (h : I∉lowGaussColumns W hW N hN ∨ J∉lowGaussColumns W hW N hN) :
    shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N)=0 := by
  rcases h with h|h
  · apply shellProfile_zero_left
    simpa only [lowGaussColumns_mem,not_not] using h
  · apply shellProfile_zero_right
    simpa only [lowGaussColumns_mem,not_not] using h

theorem original_window_mobius_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k : O) (hC : lambda^2∣C-1)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0< N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) :
    (∑I∈lowGaussColumns W hW N hN,∑J∈lowGaussColumns W hW N hN,
      if IsCoprime I.val J.val then
        jointExtension S hS σ C k u a b r hr P hg c (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)*
          shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N) else 0)=
      ∑D∈divisorPool (lowGaussColumns W hW N hN) Subtype.val,(moebius D:ℂ)*
        ∑'n : O,∑'m : O,
          jointExtension S hS σ C k u a b r hr P hg c (primaryIdealGenerator D*n) (primaryIdealGenerator D*m)*
            shellProfile W v U T (‖ringComplex n‖^2/(N/Ideal.absNorm D))
              (‖ringComplex m‖^2/(N/Ideal.absNorm D)) := by
  let F := lowGaussColumns W hW N hN
  let f := fun I J : SupportedIdeal=> jointExtension S hS σ C k u a b r hr P hg c
    (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)*
      shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N)
  have hf : ∀I J,I∉F ∨ J∉F→f I J=0 := by
    intro I J h
    dsimp [f]
    rw [shell_window_support W hW N hN U v T I J h,mul_zero]
  change (∑I∈F,∑J∈F,if IsCoprime I.val J.val then f I J else 0)=_
  rw [finite_pair_mobius_dilation F F f hf]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  let D₀ := poolDivisor F D
  have hd : D₀.val=D := poolDivisor_val F D hD
  have hdp : lambda^2∣primaryIdealGenerator D₀.val-1 :=
    (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ D₀.property)).2
  have he := jointExtension_ideal_lattice S hS hbad σ C k (primaryIdealGenerator D₀.val)
    (primary_product C _ hC hdp) u a b r hr P hg c
    (fun n m=> shellProfile W v U T (‖ringComplex n‖^2/(N/Ideal.absNorm D₀.val))
      (‖ringComplex m‖^2/(N/Ideal.absNorm D₀.val)))
  dsimp only [f]
  simp only [supported_dilation_generator,shell_dilated_column]
  convert he using 1
  rw [hd]

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open  CenteredMomentMobiusRegroup UniqueFactorizationMonoid
open CenteredMomentSupportedCorrelation SchwartzPlanePoisson
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

def commonResidualScale (C : SupportedIdeal) (Y : ℝ) : ℝ := Y/Ideal.absNorm C.val
lemma commonResidualScale_pos (C : SupportedIdeal) (Y : ℝ) (hY : 0< Y) : 0< commonResidualScale C Y :=
  div_pos hY (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr C.property.1))
lemma common_column_ratio (C I : SupportedIdeal) (Y : ℝ) :
    (Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y=(Ideal.absNorm I.val:ℝ)/commonResidualScale C Y := by
  rw [supported_dilation_norm,Nat.cast_mul,commonResidualScale,div_div_eq_mul_div]
  ring
lemma common_kernel_scale (C I J : SupportedIdeal) (k : O) (Y Q : ℝ) (hY : 0< Y) (hQ : 0< Q) :
    Q*‖ringComplex (primaryIdealGenerator C.val*k)‖^2/
      ‖ringComplex (primaryIdealGenerator (supportedIdealProduct C I).val*primaryIdealGenerator (supportedIdealProduct C J).val)‖^2=
      frequencyScale C k Y Q/
        (((Ideal.absNorm I.val:ℝ)/commonResidualScale C Y)*((Ideal.absNorm J.val:ℝ)/commonResidualScale C Y)) := by
  rw [lowGram_kernel_scale Y Q hY hQ,common_column_ratio,common_column_ratio,
    map_mul,norm_mul,mul_pow,primary_norm]
  unfold frequencyScale
  ring

theorem original_common_window_source (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C : SupportedIdeal) (k : O)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : lambda^2∣r-1) (hk : k=u.val*lambda^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (hcop : Pairwise (Function.onFun IsCoprime P)) (he : C.val=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0< Y) (hQ : 0< Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    let N:=commonResidualScale C Y
    let hN:=commonResidualScale_pos C Y hY
    let F:=lowGaussColumns W hW N hN
    (∑I∈F,∑J∈F,if IsCoprime I.val J.val then
      (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
      star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y))*
      actualCorrelation (primaryIdealGenerator (supportedIdealProduct C I).val)
        (primaryIdealGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryIdealGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryIdealGenerator_iff _).mpr (supportedIdealProduct C J).property)
        (primaryIdealGenerator C.val*k)*
      paperRadialFourier U (Q*‖ringComplex (primaryIdealGenerator C.val*k)‖^2/
        ‖ringComplex (primaryIdealGenerator (supportedIdealProduct C I).val*primaryIdealGenerator (supportedIdealProduct C J).val)‖^2)
      else 0)=
      ∑D∈divisorPool F Subtype.val,(moebius D:ℂ)*∑'n : O,∑'m : O,
        jointExtension S hS σ (primaryIdealGenerator C.val) k u a b r hr P hg c (primaryIdealGenerator D*n) (primaryIdealGenerator D*m)*
          shellProfile W v U (frequencyScale C k Y Q) (‖ringComplex n‖^2/(N/Ideal.absNorm D))
            (‖ringComplex m‖^2/(N/Ideal.absNorm D)) := by
  dsimp only
  have hpc : lambda^2∣primaryIdealGenerator C.val-1 :=
    (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ C.property)).2
  rw [←original_window_mobius_lattice S hS hbad σ (primaryIdealGenerator C.val) k hpc
    u a b r hr P hg c W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)
    U v (frequencyScale C k Y Q)]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs with hIJ
  · have hni : Supported (Ideal.span {primaryIdealGenerator I.val}) := (supported_span_primaryIdealGenerator_iff _).mpr I.property
    have hnj : Supported (Ideal.span {primaryIdealGenerator J.val}) := (supported_span_primaryIdealGenerator_iff _).mpr J.property
    have hpi : lambda^2∣primaryIdealGenerator I.val-1 := (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ I.property)).2
    have hpj : lambda^2∣primaryIdealGenerator J.val-1 := (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ J.property)).2
    have hij : IsCoprime (primaryIdealGenerator I.val) (primaryIdealGenerator J.val) := by
      apply (Ideal.isCoprime_span_singleton_iff _ _).mp
      simpa only [(primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ I.property)).1,
        (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ J.property)).1] using hIJ
    have hf : Ideal.span {primaryIdealGenerator C.val}=∏i,P i^c i := by
      rw [(primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ C.property)).1,he]
    rw [jointExtension_source S hS σ (primaryIdealGenerator C.val) k
      ((supported_span_primaryIdealGenerator_iff _).mpr C.property) u a b r hr hpr hk P hg c hc hcop hf
      _ _ hni hnj hpi hpj hij]
    rw [lowGramCoefficient_eq_primary S hS hbad σ,lowGramCoefficient_eq_primary S hS hbad σ,
      common_kernel_scale C I J k Y Q hY hQ,common_column_ratio,common_column_ratio]
    simp only [supported_dilation_generator,shellProfile,star_mul]
    ring
  · rfl

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open  UniqueFactorizationMonoid 
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma jointProfile_physicalPoint (W : ℝ→ℂ) (U : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0< a) (hab : a< b) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (v T : ℝ) (hT : 0≤ T) (N : ℝ) (hN : 0< N) (m : O×O) :
    ProbeGramJointConstruction.jointProfile W U a b ha hab hs hW v T hT
      (ProbeGramLatticeDecay.physicalPoint N m)=
      shellProfile W v U T (‖ringComplex m.1‖^2/N) (‖ringComplex m.2‖^2/N) := by
  rw [ProbeGramJointConstruction.jointProfile_apply]
  unfold ProbeGramJointConstruction.rawProfile ProbeGramJointConstruction.q1 ProbeGramJointConstruction.q2
  change lowGramProfile W v _ * star (lowGramProfile W v _) * _ = _
  have h₁ : ‖WithLp.fst (ProbeGramLatticeDecay.physicalPoint N m)‖^2=‖ringComplex m.1‖^2/N := physicalPoint_first_norm N hN m
  have h₂ : ‖WithLp.snd (ProbeGramLatticeDecay.physicalPoint N m)‖^2=‖ringComplex m.2‖^2/N := physicalPoint_second_norm N hN m
  rw [h₁,h₂]
  rfl

theorem literal_nonexceptional_source (A B : ℕ) (hA : 2< A) (a₀ b₀ : ℝ)
    (ha₀ : 0< a₀) (hab : a₀< b₀) :
    ∃(J : ℕ)(H : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0< K ∧
      ∀{ι : Type*}[Fintype ι],∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C k : O)(_hC : C≠0)(_hk0 : k≠0)(u : Oˣ)(a b : ℕ)(r : O)
      (hr : Supported (Ideal.span {r})),k=u.val*lambda^a*(2:O)^b*r→
      ∀(P : ι→Id)[_hmax : ∀i,(P i).IsMaximal](hg : ∀i,lambda∉P i)(c : ι→ℕ),
      (∀i,1≤ c i)→Ideal.span {C}=∏i,P i^c i→
      ∀(p : Id)[_hpmax : p.IsMaximal],p≠0→∀_hgp : lambda∉p,
      ringChar (O⧸p)≠2→(¬p∣jointFixedModulus S hS)→(¬p∣∏i,P i)→
      (¬6∣(normalizedFactors (Ideal.span {k})).count p)→
      ∀(U : SchwartzMap ℝ ℂ)(v T : ℝ),0≤ T→∀(d : O)(N : ℝ),0< N→
      Summable (fun m : O×O=> jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖ringComplex m.1‖^2/N) (‖ringComplex m.2‖^2/N)) ∧
      ‖∑'m : O×O,jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖ringComplex m.1‖^2/N) (‖ringComplex m.2‖^2/N)‖≤
        K*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B*
          (Ideal.absNorm (Ideal.span {C}):ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
            Ideal.absNorm (Ideal.span {k})/N)^A) := by
  obtain ⟨H₀,K₀,hK₀,hblock⟩ := literal_nonexceptional_block A hA a₀ b₀ ha₀ hab
  obtain ⟨J,H,hprofile⟩ := ProbeGramJointProfile.jointProfile_uniform_degree a₀ b₀ ha₀ hab B H₀
  refine ⟨J,H,?_⟩
  intro W hs hW
  obtain ⟨K₁,hK₁,hprofile⟩ := hprofile W hs hW
  refine ⟨K₀*K₁,mul_pos hK₀ hK₁,?_⟩
  intro ι inst S hS σ C k hC hk0 u a b r hr hk P hmax hg c hc hfac p hpmax hp0 hgp hchar hfixed hcommon he U v T hT d N hN
  let V := ProbeGramJointConstruction.jointProfile W U a₀ b₀ ha₀ hab hs hW v T hT
  have hv := ProbeGramJointConstruction.jointProfile_annularSupport W U a₀ b₀ ha₀ hab hs hW v T hT
  have hb := hblock S hS σ C k hC hk0 u a b r hr hk P hg c hc hfac p hp0 hgp hchar hfixed hcommon he V hv d N hN
  have hfun : (fun m : O×O=> jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
      V (ProbeGramLatticeDecay.physicalPoint N m))=
      (fun m : O×O=> jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖ringComplex m.1‖^2/N) (‖ringComplex m.2‖^2/N)) := by
    funext m
    rw [jointProfile_physicalPoint W U a₀ b₀ ha₀ hab hs hW v T hT N hN m]
  rw [hfun] at hb
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hm : 0≤ min (1:ℝ) (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
      Ideal.absNorm (Ideal.span {k})/N)^A) := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hprofile U v T hT) hK₀.le)
        (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {C})))) (sq_nonneg N)) hm
  convert hh using 1 ; ring

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open   UniqueFactorizationMonoid
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

abbrev GramFrequency := {k : O // k≠0}
abbrev GramPrime (C : SupportedIdeal) := {P : Id // P∈CubicEisenstein.primeSupport C.val}
def gramPrime (C : SupportedIdeal) (P : GramPrime C) : Id := P.val
instance gramPrimeMaximal (C : SupportedIdeal) (P : GramPrime C) : (gramPrime C P).IsMaximal :=
  (Ideal.isPrime_of_prime (CenteredMomentNaturalRowSource.support_prime C.val P.val P.property)).isMaximal (CenteredMomentNaturalRowSource.support_prime C.val P.val P.property).ne_zero

def gramExponent (C : SupportedIdeal) (P : GramPrime C) : ℕ := (normalizedFactors C.val).count P.val
lemma gramExponent_pos (C : SupportedIdeal) (P : GramPrime C) : 1≤ gramExponent C P :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property)
lemma gramPrime_good (C : SupportedIdeal) (P : GramPrime C) : lambda∉gramPrime C P :=
  (supported_factors_good C.val C.property P.val (Multiset.mem_toFinset.mp P.property)).2.1
lemma gramPrime_coprime (C : SupportedIdeal) : Pairwise (Function.onFun IsCoprime (gramPrime C)) := by
  intro P Q hpq
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hpq)
lemma gramPrime_product (C : SupportedIdeal) : C.val=∏P : GramPrime C,gramPrime C P^gramExponent C P := by
  calc
    C.val=(normalizedFactors C.val).prod := (Ideal.prod_normalizedFactors_eq_self C.property.1).symm
    _=∏P∈CubicEisenstein.primeSupport C.val,P^(normalizedFactors C.val).count P := Finset.prod_multiset_count _
    _=_ := (Finset.prod_coe_sort _ _).symm

instance gramPrimePowerFinite (C : SupportedIdeal) (P : GramPrime C) :
    Finite (O⧸gramPrime C P^gramExponent C P) :=
  Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ (CenteredMomentNaturalRowSource.support_prime C.val P.val P.property).ne_zero)
instance gramPrimePowerFintype (C : SupportedIdeal) (P : GramPrime C) :
    Fintype (O⧸gramPrime C P^gramExponent C P) := Fintype.ofFinite _
instance gramProductFinite (C : SupportedIdeal) : Finite (O⧸∏P : GramPrime C,gramPrime C P^gramExponent C P) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  rw [←gramPrime_product C]
  exact C.property.1
instance gramProductFintype (C : SupportedIdeal) : Fintype (O⧸∏P : GramPrime C,gramPrime C P^gramExponent C P) := Fintype.ofFinite _

structure GramNumeratorData (k : GramFrequency) where
  unit : Oˣ
  lambdaExponent : ℕ
  twoExponent : ℕ
  good : O
  supported : Supported (Ideal.span {good})
  primary : lambda^2∣good-1
  factor : k.val=unit.val*lambda^lambdaExponent*(2:O)^twoExponent*good

lemma gramNumeratorData_nonempty (k : GramFrequency) : Nonempty (GramNumeratorData k) := by
  obtain ⟨u,a,b,r,hr,hpr,hf⟩ := exists_supported_numerator_factorization k.val k.property
  exact ⟨⟨u,a,b,r,(supported_iff_native _).mpr hr,hpr,hf⟩⟩
def gramNumeratorData (k : GramFrequency) : GramNumeratorData k := Classical.choice (gramNumeratorData_nonempty k)

/-- Assemble the joint correlation from the prime factors of the common ideal. -/
def canonicalJoint (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (n m : O) : ℂ :=
  let f:=gramNumeratorData k
  jointExtension S hS σ (primaryIdealGenerator C.val) k.val f.unit f.lambdaExponent f.twoExponent
    f.good f.supported (gramPrime C) (gramPrime_good C) (gramExponent C) n m

lemma canonicalJoint_norm (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (n m : O) : ‖canonicalJoint S hS σ C k n m‖≤(Ideal.absNorm C.val:ℝ) := by
  have hh := jointExtension_norm S hS σ (primaryIdealGenerator C.val) k.val
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramPrime C) (gramPrime_good C)
    (gramExponent C) (gramExponent_pos C) n m
  simpa only [←gramPrime_product C,canonicalJoint] using hh

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredExceptionalCount
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def exceptionalModulus (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) : Id :=
  jointFixedModulus S hS*C.val
lemma exceptionalModulus_nonzero (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) :
    exceptionalModulus S hS C≠0 := mul_ne_zero (jointFixedModulus_nonzero S hS) C.property.1
lemma exceptionalModulus_norm (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) :
    Ideal.absNorm (exceptionalModulus S hS C)=Ideal.absNorm (jointFixedModulus S hS)*Ideal.absNorm C.val :=
  map_mul Ideal.absNorm _ _

/-- Outside the fixed modulus, exceptional frequencies have valuations divisible by six. -/
def ExceptionalFrequency (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) (k : GramFrequency) : Prop :=
  ∀p∉CubicEisenstein.primeSupport (exceptionalModulus S hS C),valuation (Ideal.span {k.val}) p%6=0

lemma nonexceptional_prime (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) (k : GramFrequency)
    (hk : ¬ExceptionalFrequency S hS C k) :
    ∃p : Id,Prime p ∧ p∉CubicEisenstein.primeSupport (exceptionalModulus S hS C) ∧
      ¬6∣(normalizedFactors (Ideal.span {k.val})).count p := by
  unfold ExceptionalFrequency at hk
  push_neg at hk
  obtain ⟨p,hp,he⟩ := hk
  have hcount : (normalizedFactors (Ideal.span {k.val})).count p≠0 := by
    intro hz
    apply he
    simp [valuation,hz]
  have hprime := prime_of_normalized_factor p (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcount))
  exact ⟨p,hprime,hp,fun hd=> he (Nat.mod_eq_zero_of_dvd hd)⟩

lemma outside_exceptional_not_dvd (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal)
    (p : Id) (hp : Prime p) (hout : p∉CubicEisenstein.primeSupport (exceptionalModulus S hS C)) :
    (¬p∣jointFixedModulus S hS) ∧ (¬p∣∏i : GramPrime C,gramPrime C i) := by
  have hnot : ¬p∣exceptionalModulus S hS C := by
    intro hd
    apply hout
    exact Multiset.mem_toFinset.mpr ((Ideal.mem_normalizedFactors_iff (exceptionalModulus_nonzero S hS C)).mpr
      ⟨Ideal.isPrime_of_prime hp,Ideal.dvd_iff_le.mp hd⟩)
  refine ⟨fun hd=> hnot (dvd_mul_of_dvd_left hd _),?_⟩
  intro hd
  apply hnot
  apply dvd_mul_of_dvd_right
  apply dvd_trans hd
  calc
    _∣∏i : GramPrime C,gramPrime C i^gramExponent C i :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun i _=> dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (gramExponent_pos C i)))
    _=C.val := (gramPrime_product C).symm

lemma outside_exceptional_good (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal)
    (p : Id) (hp : Prime p) (hout : p∉CubicEisenstein.primeSupport (exceptionalModulus S hS C)) :
    lambda∉p ∧ ringChar (O⧸p)≠2 := by
  let : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hle : exceptionalModulus S hS C≤ Ideal.span {(72:O)} :=
    le_trans Ideal.mul_le_right Ideal.mul_le_left
  have hh := CenteredExceptionalProfile.outside_fixed_support _ (exceptionalModulus_nonzero S hS C) hle p hp hout
  exact ⟨hh.1,quotient_char_ne_two_of_two_not_mem p hh.2.1⟩

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open  UniqueFactorizationMonoid
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def canonicalLatticeBlock (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (d : O) (W : ℝ→ℂ) (U : SchwartzMap ℝ ℂ)
    (v T N : ℝ) : ℂ :=
  ∑'m : O×O,canonicalJoint S hS σ C k (d*m.1) (d*m.2)*
    shellProfile W v U T (‖ringComplex m.1‖^2/N) (‖ringComplex m.2‖^2/N)

theorem canonical_nonexceptional_block (A B : ℕ) (hA : 2< A) (a₀ b₀ : ℝ)
    (ha₀ : 0< a₀) (hab : a₀< b₀) :
    ∃(J : ℕ)(H : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0< K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency),¬ExceptionalFrequency S hS C k→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v T N : ℝ),0≤ T→0< N→
        ‖canonicalLatticeBlock S hS σ C k d W U v T N‖≤
        K*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B*
          (Ideal.absNorm C.val:ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*
            Ideal.absNorm (Ideal.span {k.val})/N)^A) := by
  obtain ⟨J,H,hsource⟩ := literal_nonexceptional_source A B hA a₀ b₀ ha₀ hab
  refine ⟨J,H,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hsource⟩ := hsource W hs hW
  refine ⟨K,hK,?_⟩
  intro S hS σ C k hk d U v T N hT hN
  obtain ⟨p,hp,hout,he⟩ := nonexceptional_prime S hS C k hk
  let : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := outside_exceptional_good S hS C p hp hout
  have hd := outside_exceptional_not_dvd S hS C p hp hout
  have hcspan := (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ C.property)).1
  have hf : Ideal.span {primaryIdealGenerator C.val}=∏i : GramPrime C,gramPrime C i^gramExponent C i := hcspan.trans (gramPrime_product C)
  have hh := hsource S hS σ (primaryIdealGenerator C.val) k.val
    (supported_primaryIdealGenerator_ne_zero _ C.property) k.property
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramNumeratorData k).factor
    (gramPrime C) (gramPrime_good C) (gramExponent C) (gramExponent_pos C) hf
    p hp.ne_zero hg.1 hg.2 hd.1 hd.2 he U v T hT d N hN
  simpa only [canonicalLatticeBlock,canonicalJoint,hcspan] using hh.2

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open  CenteredMomentMobiusRegroup UniqueFactorizationMonoid
open CenteredMomentSupportedCorrelation SchwartzPlanePoisson
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def originalCommonBlock (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0< Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  let N:=commonResidualScale C Y
  let hN:=commonResidualScale_pos C Y hY
  let F:=lowGaussColumns W hW N hN
  (∑I∈F,∑J∈F,if IsCoprime I.val J.val then
      (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
      star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y))*
      actualCorrelation (primaryIdealGenerator (supportedIdealProduct C I).val)
        (primaryIdealGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryIdealGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryIdealGenerator_iff _).mpr (supportedIdealProduct C J).property)
        (primaryIdealGenerator C.val*k.val)*
      paperRadialFourier U (Q*‖ringComplex (primaryIdealGenerator C.val*k.val)‖^2/
        ‖ringComplex (primaryIdealGenerator (supportedIdealProduct C I).val*primaryIdealGenerator (supportedIdealProduct C J).val)‖^2)
      else 0)

theorem originalCommonBlock_eq_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C : SupportedIdeal) (k : GramFrequency)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0< Y) (hQ : 0< Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    originalCommonBlock S hS σ C k W hW Y Q hY U v=
      ∑D∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val,
        (moebius D:ℂ)*canonicalLatticeBlock S hS σ C k (primaryIdealGenerator D) W U v
          (frequencyScale C k.val Y Q) (commonResidualScale C Y/Ideal.absNorm D) := by
  have hh := original_common_window_source S hS hbad σ C k.val
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramNumeratorData k).primary
    (gramNumeratorData k).factor (gramPrime C) (gramPrime_good C) (gramExponent C)
    (gramExponent_pos C) (gramPrime_coprime C) (gramPrime_product C) W hW Y Q hY hQ U v
  change originalCommonBlock S hS σ C k W hW Y Q hY U v=_ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hD0 := (divisorPool_supported _ D hD).1
  have hN : 0< commonResidualScale C Y/(Ideal.absNorm D:ℝ) :=
    div_pos (commonResidualScale_pos C Y hY) (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0))
  exact (shell_lattice_summable W hW _ hN U v (frequencyScale C k.val Y Q)
    (fun n m=> canonicalJoint S hS σ C k (primaryIdealGenerator D*n) (primaryIdealGenerator D*m))).tsum_prod.symm

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion 
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

theorem canonical_trivial_block (a b B : ℝ) (ha : 0< a) (hb : 0≤ b) (hB : 0≤ B) (A : ℕ) :
    ∃s : Finset (ℕ×ℕ),∃K : ℝ,0< K ∧
      ∀(W : ℝ→ℂ)(_hcompact : HasCompactSupport W),
      (Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤ B)→
      ∀(U : SchwartzMap ℝ ℂ)(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency)(d : O)(N T v : ℝ),0< N→0≤ T→
      (1+T)^A*‖canonicalLatticeBlock S hS σ C k d W U v T N‖≤
        K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Ideal.absNorm C.val:ℝ)*N^2 := by
  obtain ⟨s,K,hK,hprofile⟩ := shellProfile_weighted_bound a b B ha hB A
  refine ⟨s,(1+128*b)^2*K,by positivity,?_⟩
  intro W hcompact hs hW U S hS σ C k d N T v hN hT
  let F:=shellLatticeColumns W hcompact N hN
  let G:=F
  have hF0 : ∀z∈F,z≠0 := shellLatticeColumns_nonzero W hcompact N hN a b ha hs
  have hG0 : ∀z∈G,z≠0 := hF0
  have hFN : ∀z∈F,‖ringComplex z‖^2≤ b*N := shellLatticeColumns_norm W hcompact N hN a b hs
  have hGN : ∀z∈G,‖ringComplex z‖^2≤ b*N := hFN
  unfold canonicalLatticeBlock
  rw [shell_lattice_tsum W hcompact N hN U v T (fun n m=> canonicalJoint S hS σ C k (d*n) (d*m))]
  have hcoef (n m : O) : ‖canonicalJoint S hS σ C k (d*n) (d*m)‖≤(Ideal.absNorm C.val:ℝ) :=
    canonicalJoint_norm S hS σ C k _ _
  have hpoint (n m : O) : (1+T)^A*‖canonicalJoint S hS σ C k (d*n) (d*m)*
      shellProfile W v U T (‖ringComplex n‖^2/N) (‖ringComplex m‖^2/N)‖≤
      (Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) := by
    rw [norm_mul]
    calc
      _ = ‖canonicalJoint S hS σ C k (d*n) (d*m)‖*
          ((1+T)^A*‖shellProfile W v U T (‖ringComplex n‖^2/N) (‖ringComplex m‖^2/N)‖) := by ring
      _ ≤ _ := mul_le_mul (hcoef n m) (hprofile W hs hW U v T _ _ hT) (by positivity) (by positivity)
  have hcount := annular_pair_count F G b N hb hN.le hF0 hG0 hFN hGN
  calc
    _ ≤ (1+T)^A*(∑n∈F,∑m∈G,‖canonicalJoint S hS σ C k (d*n) (d*m)*
        shellProfile W v U T (‖ringComplex n‖^2/N) (‖ringComplex m‖^2/N)‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _=> norm_sum_le _ _)
    _ ≤ (F.card:ℝ)*G.card*((Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      simp_rw [Finset.mul_sum]
      calc
        _ ≤ ∑n∈F,∑m∈G,(Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) :=
          Finset.sum_le_sum (fun n _=> Finset.sum_le_sum (fun m _=> hpoint n m))
        _ = _ := by simp;ring
    _ ≤ ((128*b)^2*N^2)*((Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Finset.card_product,Nat.cast_mul] using hcount
    _ ≤ _ := by
      have hb' : (128*b)^2≤(1+128*b)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hb' (show 0≤ N^2*((Ideal.absNorm C.val:ℝ)*
        (K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) by positivity)]

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => Eisenstein.O

lemma supportedIdealProduct_injective (C : SupportedIdeal) : Function.Injective (supportedIdealProduct C) := by
  intro I J h
  apply Subtype.ext
  exact mul_left_cancel₀ C.property.1 (congrArg Subtype.val h)

def commonPool (F : Finset SupportedIdeal) : Finset SupportedIdeal :=
  (F×ˢF).image (fun p=> gcdCommon p.1 p.2)
def commonColumns (F : Finset SupportedIdeal) (C : SupportedIdeal) : Finset SupportedIdeal :=
  F.preimage (supportedIdealProduct C) (supportedIdealProduct_injective C).injOn
lemma commonColumns_mem (F : Finset SupportedIdeal) (C I : SupportedIdeal) :
    I∈commonColumns F C ↔ supportedIdealProduct C I∈F := Finset.mem_preimage

def commonTriples (F : Finset SupportedIdeal) : Finset ((_C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal)) :=
  (commonPool F).sigma (fun C=>(commonColumns F C×ˢcommonColumns F C).filter (fun p=> IsCoprime p.1.val p.2.val))

theorem finite_pair_gcd (F : Finset SupportedIdeal) (f : SupportedIdeal→SupportedIdeal→ℂ) :
    (∑I∈F,∑J∈F,f I J)=
      ∑C∈commonPool F,∑I∈commonColumns F C,∑J∈commonColumns F C,
        if IsCoprime I.val J.val then f (supportedIdealProduct C I) (supportedIdealProduct C J) else 0 := by
  have he : (∑p∈F×ˢF,f p.1 p.2)=
      ∑t∈commonTriples F,f (supportedIdealProduct t.1 t.2.1) (supportedIdealProduct t.1 t.2.2) := by
    apply Finset.sum_bij (fun p _=>⟨gcdCommon p.1 p.2,gcdLeft p.1 p.2,gcdRight p.1 p.2⟩)
    · intro p hp
      have hl : supportedIdealProduct (gcdCommon p.1 p.2) (gcdLeft p.1 p.2)=p.1 := Subtype.ext (gcd_common_left _ _)
      have hr : supportedIdealProduct (gcdCommon p.1 p.2) (gcdRight p.1 p.2)=p.2 := Subtype.ext (gcd_common_right _ _)
      simp only [commonTriples,Finset.mem_sigma,Finset.mem_filter,Finset.mem_product,commonColumns_mem]
      exact ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,⟨by rw [hl];exact (Finset.mem_product.mp hp).1,by rw [hr];exact (Finset.mem_product.mp hp).2⟩,gcd_residual_coprime _ _⟩
    · intro p hp q hq he
      have hc := congrArg Sigma.fst he
      have hl := congrArg (fun t : (C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal)=> t.2.1) he
      have hr := congrArg (fun t : (C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal)=> t.2.2) he
      apply Prod.ext <;> apply Subtype.ext
      · rw [←gcd_common_left p.1 p.2,←gcd_common_left q.1 q.2]
        rw [show gcdCommon p.1 p.2=gcdCommon q.1 q.2 from hc,show gcdLeft p.1 p.2=gcdLeft q.1 q.2 from hl]
      · rw [←gcd_common_right p.1 p.2,←gcd_common_right q.1 q.2]
        rw [show gcdCommon p.1 p.2=gcdCommon q.1 q.2 from hc,show gcdRight p.1 p.2=gcdRight q.1 q.2 from hr]
    · intro t ht
      have ht' : t.1∈commonPool F ∧ (t.2.1∈commonColumns F t.1 ∧ t.2.2∈commonColumns F t.1) ∧ IsCoprime t.2.1.val t.2.2.val := by
        simpa only [commonTriples,Finset.mem_sigma,Finset.mem_filter,Finset.mem_product] using ht
      let u : CoprimeTriple:=⟨(t.1,t.2),ht'.2.2⟩
      refine ⟨(supportedIdealProduct t.1 t.2.1,supportedIdealProduct t.1 t.2.2),?_,?_⟩
      · exact Finset.mem_product.mpr ⟨(commonColumns_mem F _ _).mp ht'.2.1.1,(commonColumns_mem F _ _).mp ht'.2.1.2⟩
      · have h:=congrArg Subtype.val (gcdTriple_multiply u)
        exact congrArg (fun p : SupportedIdeal×(SupportedIdeal×SupportedIdeal)=>(⟨p.1,p.2⟩ : (C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal))) h
    · intro p hp
      have hl : supportedIdealProduct (gcdCommon p.1 p.2) (gcdLeft p.1 p.2)=p.1 := Subtype.ext (gcd_common_left _ _)
      have hr : supportedIdealProduct (gcdCommon p.1 p.2) (gcdRight p.1 p.2)=p.2 := Subtype.ext (gcd_common_right _ _)
      simp only [hl,hr]
  rw [Finset.sum_product] at he
  rw [he,commonTriples,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.sum_filter,Finset.sum_product]

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss 
open CenteredMomentSupportedCorrelation SchwartzPlanePoisson
local notation "O" => Eisenstein.O

lemma actual_correlation_radial_summable (I J : SupportedIdeal) (C : O) (hC : C≠0)
    (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0< Q) :
    Summable (fun k : O=> actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
      ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
      ((supported_span_primaryIdealGenerator_iff _).mpr J.property) (C*k)*
      paperRadialFourier U (Q*‖ringComplex (C*k)‖^2/
        ‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2)) := by
  let t:=Q*‖ringComplex C‖^2/‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2
  have hc : 0<‖ringComplex C‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hC))
  have hd : 0<‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero (mul_ne_zero
      (supported_primaryIdealGenerator_ne_zero _ I.property) (supported_primaryIdealGenerator_ne_zero _ J.property))))
  have ht : 0< t := div_pos (mul_pos hQ hc) hd
  have hs := paperRadialFourier_lattice_summable_norm U t ht
  let B : ℝ := (Ideal.absNorm I.val:ℝ)*Ideal.absNorm J.val
  have hb (k : O) : ‖actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
      ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
      ((supported_span_primaryIdealGenerator_iff _).mpr J.property) (C*k)‖≤ B := by
    have hh := CenteredMomentTail.actualCorrelation_norm_le (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
      ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
      ((supported_span_primaryIdealGenerator_iff _).mpr J.property) (C*k)
    simpa only [(primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ I.property)).1,
      (primaryIdealGenerator_spec _ (supported_primaryIdealGenerator_ne_zero _ J.property)).1] using hh
  have harg (k : O) : Q*‖ringComplex (C*k)‖^2/‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2=t*‖ringComplex k‖^2 := by
    simp only [map_mul,norm_mul,mul_pow,t]
    ring
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun k=> norm_nonneg _) _ (hs.mul_left B)
  intro k
  rw [norm_mul,harg]
  exact mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _)

lemma originalCommonBlock_summable (S : Finset (Ideal O)) (hS : ∀p∈S,p.IsMaximal)
    (σ : RayFourExpansion.RayRing) (C : SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0< Y) (hQ : 0< Q) (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    Summable (fun k : GramFrequency=> originalCommonBlock S hS σ C k W hW Y Q hY U v) := by
  unfold originalCommonBlock
  apply summable_sum
  intro I hI
  apply summable_sum
  intro J hJ
  by_cases hij : IsCoprime I.val J.val
  · simp only [hij,ite_true]
    have hs := (actual_correlation_radial_summable (supportedIdealProduct C I) (supportedIdealProduct C J)
      (primaryIdealGenerator C.val) (supported_primaryIdealGenerator_ne_zero _ C.property) U Q hQ).subtype (fun k : O=> k≠0)
    simpa only [Function.comp_def,mul_assoc] using hs.mul_left
      ((lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
       star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y)))
  · simpa only [hij,ite_false] using (summable_zero : Summable (fun _ : GramFrequency=>(0:ℂ)))

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss 
open CenteredMomentSupportedCorrelation SchwartzPlanePoisson
local notation "O" => Eisenstein.O

lemma nonzero_tsum_indicator (f : O→ℂ) :
    (∑'k : O,if k=0 then 0 else f k)=∑'k : GramFrequency,f k.val := by
  rw [←tsum_subtype_eq_of_support_subset (s:={k : O | k≠0}) (by
    intro k hk hz
    subst k
    exact hk (by simp))]
  apply tsum_congr
  intro k
  exact if_neg k.property

def gramFrequencyNeg : GramFrequency≃GramFrequency where
  toFun k:=⟨-k.val,neg_ne_zero.mpr k.property⟩
  invFun k:=⟨-k.val,neg_ne_zero.mpr k.property⟩
  left_inv k:=Subtype.ext (neg_neg k.val)
  right_inv k:=Subtype.ext (neg_neg k.val)

lemma actual_common_nonzero_tsum (C n₁ n₂ : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁})) (h₂ : Supported (Ideal.span {n₂}))
    (F : O→ℂ) :
    (∑'j : GramFrequency,actualCorrelation (C*n₁) (C*n₂)
      (supported_mul_elements C n₁ hC h₁) (supported_mul_elements C n₂ hC h₂) j.val*F j.val)=
      ∑'k : GramFrequency,actualCorrelation (C*n₁) (C*n₂)
        (supported_mul_elements C n₁ hC h₁) (supported_mul_elements C n₂ hC h₂) (C*k.val)*F (C*k.val) := by
  have hh := actual_common_frequency_tsum C n₁ n₂ hC h₁ h₂ (fun j=> if j=0 then 0 else F j)
  have hc0 := supported_element_ne_zero C hC
  simp only [mul_ite,mul_zero,mul_eq_zero,hc0,false_or] at hh
  simpa only [nonzero_tsum_indicator] using hh

lemma actual_gcd_nonzero_frequency_source (I J : SupportedIdeal) (U : SchwartzMap ℝ ℂ) (Q : ℝ) :
    (∑'h : GramFrequency,actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
      ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
      ((supported_span_primaryIdealGenerator_iff _).mpr J.property) (-h.val)*
      paperRadialFourier U (Q*‖ringComplex h.val‖^2/‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2))=
      ∑'k : GramFrequency,actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
        ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
        ((supported_span_primaryIdealGenerator_iff _).mpr J.property) (primaryIdealGenerator (gcdCommon I J).val*k.val)*
        paperRadialFourier U (Q*‖ringComplex (primaryIdealGenerator (gcdCommon I J).val*k.val)‖^2/
          ‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2) := by
  have hn := gramFrequencyNeg.tsum_eq (fun h : GramFrequency=>
    actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
      ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
      ((supported_span_primaryIdealGenerator_iff _).mpr J.property) h.val*
      paperRadialFourier U (Q*‖ringComplex h.val‖^2/‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2))
  simp only [gramFrequencyNeg,Equiv.coe_fn_mk,map_neg,norm_neg] at hn
  rw [hn]
  have hh := actual_common_nonzero_tsum (primaryIdealGenerator (gcdCommon I J).val)
    (primaryIdealGenerator (gcdLeft I J).val) (primaryIdealGenerator (gcdRight I J).val)
    ((supported_span_primaryIdealGenerator_iff _).mpr (gcdCommon I J).property)
    ((supported_span_primaryIdealGenerator_iff _).mpr (gcdLeft I J).property)
    ((supported_span_primaryIdealGenerator_iff _).mpr (gcdRight I J).property)
    (fun h=> paperRadialFourier U (Q*‖ringComplex h‖^2/
      ‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2))
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J] using hh

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss  RayFourExpansion
open CenteredMomentSupportedCorrelation SchwartzPlanePoisson CenteredMomentGaussEnergy
local notation "O" => Eisenstein.O

lemma original_pair_zero_split (I J : SupportedIdeal) (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0< Q) :
    (∑'h : O,actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
      ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
      ((supported_span_primaryIdealGenerator_iff _).mpr J.property) (-h)*
      paperRadialFourier U (Q*‖ringComplex h‖^2/‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2))=
      actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
        ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
        ((supported_span_primaryIdealGenerator_iff _).mpr J.property) 0*paperRadialFourier U 0+
      ∑'h : GramFrequency,actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
        ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
        ((supported_span_primaryIdealGenerator_iff _).mpr J.property) (-h.val)*
        paperRadialFourier U (Q*‖ringComplex h.val‖^2/‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2) := by
  have hs := actual_correlation_radial_summable I J (-1) (by norm_num) U Q hQ
  simp only [neg_one_mul,map_neg,norm_neg] at hs
  have hh := hs.tsum_eq_add_tsum_ite 0
  simpa only [neg_zero,map_zero,norm_zero,zero_pow (by decide : 2≠0),mul_zero,zero_div,nonzero_tsum_indicator] using hh

theorem original_energy_nonzero (C : CalibrationData) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y : ℝ) (hY : 0< Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0< Q) :
    gaussEnergy (lowGaussColumns W hW Y hY) (fun I=> primaryIdealGenerator I.val)
      (fun I=>(supported_span_primaryIdealGenerator_iff _).mpr I.property)
      (lowGaussColumn C W Y σ v) U Q=
      lowGramZeroMode C W hW Y hY σ v U Q+
      ((Q/Y^3:ℝ):ℂ)*∑I∈lowGaussColumns W hW Y hY,∑J∈lowGaussColumns W hW Y hY,
        ((lowGramCoefficient C σ I*lowGramProfile W v ((Ideal.absNorm I.val:ℝ)/Y))*
          star (lowGramCoefficient C σ J*lowGramProfile W v ((Ideal.absNorm J.val:ℝ)/Y)))*
        ∑'h : GramFrequency,actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
          ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
          ((supported_span_primaryIdealGenerator_iff _).mpr J.property) (-h.val)*
          paperRadialFourier U (Q*‖ringComplex h.val‖^2/‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2) := by
  rw [lowGram_source_poisson C W hW Y hY σ v U Q hQ,lowGramZeroMode_eq_source]
  simp_rw [original_pair_zero_split _ _ U Q hQ,mul_add,Finset.sum_add_distrib]
  simp only [mul_add]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  ring

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss

lemma commonColumns_window (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0< Y) (C : SupportedIdeal) :
    commonColumns (lowGaussColumns W hW Y hY) C=
      lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY) := by
  ext I
  rw [commonColumns_mem,lowGaussColumns_mem,lowGaussColumns_mem,common_column_ratio]

theorem original_window_gcd (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0< Y)
    (f : SupportedIdeal→SupportedIdeal→ℂ) :
    (∑I∈lowGaussColumns W hW Y hY,∑J∈lowGaussColumns W hW Y hY,f I J)=
      ∑C∈commonPool (lowGaussColumns W hW Y hY),
        ∑I∈lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY),
        ∑J∈lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY),
        if IsCoprime I.val J.val then f (supportedIdealProduct C I) (supportedIdealProduct C J) else 0 := by
  rw [finite_pair_gcd]
  simp_rw [commonColumns_window]

lemma commonPool_norm_bound (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0< Y)
    (a b : ℝ) (hs : Function.support W⊆Set.Icc a b)
    (C : SupportedIdeal) (hC : C∈commonPool (lowGaussColumns W hW Y hY)) :
    (Ideal.absNorm C.val:ℝ)≤ b*Y := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hC
  have hnp : (Ideal.absNorm p.1.val:ℝ)≤ b*Y :=
    (div_le_iff₀ hY).mp (hs ((lowGaussColumns_mem W hW Y hY p.1).mp (Finset.mem_product.mp hp).1)).2
  have hg : Ideal.absNorm (gcdCommon p.1 p.2).val≤ Ideal.absNorm p.1.val :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.1.property.1))
      (map_dvd Ideal.absNorm (gcd_dvd_left p.1.val p.2.val))
  exact (by exact_mod_cast hg : (Ideal.absNorm (gcdCommon p.1 p.2).val:ℝ)≤ Ideal.absNorm p.1.val).trans hnp

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap
namespace ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss  RayFourExpansion
open CenteredMomentSupportedCorrelation SchwartzPlanePoisson CenteredMomentGaussEnergy
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma gcdCommon_product_coprime (C I J : SupportedIdeal) (h : IsCoprime I.val J.val) :
    gcdCommon (supportedIdealProduct C I) (supportedIdealProduct C J)=C := by
  have hh:=congrArg (fun t : CoprimeTriple=> t.val.1) (gcdTriple_multiply ⟨(C,I,J),h⟩)
  exact hh

def originalPairWeight (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (W : ℝ→ℂ) (Y v : ℝ) (I J : SupportedIdeal) : ℂ :=
  (lowGramCoefficient (calibrationForSet S hS) σ I*lowGramProfile W v ((Ideal.absNorm I.val:ℝ)/Y))*
    star (lowGramCoefficient (calibrationForSet S hS) σ J*lowGramProfile W v ((Ideal.absNorm J.val:ℝ)/Y))

theorem original_nonzero_common_sum (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0< Y) (hQ : 0< Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    (∑I∈lowGaussColumns W hW Y hY,∑J∈lowGaussColumns W hW Y hY,
      originalPairWeight S hS σ W Y v I J*
      ∑'h : GramFrequency,actualCorrelation (primaryIdealGenerator I.val) (primaryIdealGenerator J.val)
        ((supported_span_primaryIdealGenerator_iff _).mpr I.property)
        ((supported_span_primaryIdealGenerator_iff _).mpr J.property) (-h.val)*
        paperRadialFourier U (Q*‖ringComplex h.val‖^2/‖ringComplex (primaryIdealGenerator I.val*primaryIdealGenerator J.val)‖^2))=
      ∑C∈commonPool (lowGaussColumns W hW Y hY),∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v := by
  simp_rw [actual_gcd_nonzero_frequency_source]
  rw [original_window_gcd]
  apply Finset.sum_congr rfl
  intro C hC
  let F:=lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)
  let f := fun (I J : SupportedIdeal) (k : GramFrequency)=>
    if IsCoprime I.val J.val then
      originalPairWeight S hS σ W Y v (supportedIdealProduct C I) (supportedIdealProduct C J)*
      actualCorrelation (primaryIdealGenerator (supportedIdealProduct C I).val) (primaryIdealGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryIdealGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryIdealGenerator_iff _).mpr (supportedIdealProduct C J).property) (primaryIdealGenerator C.val*k.val)*
      paperRadialFourier U (Q*‖ringComplex (primaryIdealGenerator C.val*k.val)‖^2/
        ‖ringComplex (primaryIdealGenerator (supportedIdealProduct C I).val*primaryIdealGenerator (supportedIdealProduct C J).val)‖^2) else 0
  have hf (I J : SupportedIdeal) : Summable (f I J) := by
    by_cases hij : IsCoprime I.val J.val
    · have hh := ((actual_correlation_radial_summable (supportedIdealProduct C I) (supportedIdealProduct C J)
        (primaryIdealGenerator C.val) (supported_primaryIdealGenerator_ne_zero _ C.property) U Q hQ).subtype (fun k : O=> k≠0)).mul_left
          (originalPairWeight S hS σ W Y v (supportedIdealProduct C I) (supportedIdealProduct C J))
      simpa only [f,hij,ite_true,Function.comp_def,mul_assoc] using hh
    · simpa only [f,hij,ite_false] using (summable_zero : Summable (fun _ : GramFrequency=>(0:ℂ)))
  have hr : (∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v)=
      ∑I∈F,∑J∈F,∑'k : GramFrequency,f I J k := by
    change (∑'k : GramFrequency,∑I∈F,∑J∈F,f I J k)=_
    rw [Summable.tsum_finsetSum (fun I hI=> summable_sum (fun J hJ=> hf I J))]
    apply Finset.sum_congr rfl
    intro I hI
    exact Summable.tsum_finsetSum (fun J hJ=> hf I J)
  rw [hr]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases hij : IsCoprime I.val J.val
  · simp only [hij,ite_true,f,gcdCommon_product_coprime C I J hij]
    rw [←tsum_mul_left]
    apply tsum_congr
    intro k
    ring
  · simp only [hij,ite_false,f,tsum_zero]

/-- Split the original energy into its zero mode and nonzero-frequency blocks indexed by the gcd. -/
theorem original_energy_common_blocks (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0< Y) (hQ : 0< Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    gaussEnergy (lowGaussColumns W hW Y hY) (fun I=> primaryIdealGenerator I.val)
      (fun I=>(supported_span_primaryIdealGenerator_iff _).mpr I.property)
      (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q=
      lowGramZeroMode (calibrationForSet S hS) W hW Y hY σ v U Q+
      ((Q/Y^3:ℝ):ℂ)*(∑C∈commonPool (lowGaussColumns W hW Y hY),
        ∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v) := by
  rw [original_energy_nonzero _ _ _ _ _ _ _ _ _ hQ]
  congr 1
  congr 1
  exact original_nonzero_common_sum S hS σ W hW Y Q hY hQ U v

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open CenteredExceptionalCount 
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def lowGramRemainders (F : Finset O) : Finset Id :=
  F.image (fun z=> sixthRemainder (Ideal.span {z}))

lemma lowGramRemainders_nonzero (F : Finset O) (R : Id) (hR : R∈lowGramRemainders F) : R≠0 := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hR
  exact sixthRemainder_ne_zero _

theorem lowGramRemainders_card (F : Finset O) (G : Id)
    (hres : ∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0) :
    (lowGramRemainders F).card≤6^(primeSupport G).card := by
  have hlt (R : lowGramRemainders F) (P : Id) : valuation R.val P<6 := by
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp R.property
    rw [←he]
    exact sixthRemainder_valuation_lt _ _
  let code : lowGramRemainders F→(primeSupport G→Fin 6) := fun R P=>⟨valuation R.val P.val,hlt R P.val⟩
  have hinj : Function.Injective code := by
    intro R T he
    apply Subtype.ext
    apply ideal_eq_of_valuation_eq (lowGramRemainders_nonzero F R.val R.property)
      (lowGramRemainders_nonzero F T.val T.property)
    intro P
    by_cases hp : P∈primeSupport G
    · exact congrArg Fin.val (congrFun he ⟨P,hp⟩)
    · obtain ⟨r,hr,her⟩ := Finset.mem_image.mp R.property
      obtain ⟨t,ht,het⟩ := Finset.mem_image.mp T.property
      rw [←her,←het,sixthRemainder_valuation,sixthRemainder_valuation,hres r hr P hp,hres t ht P hp]
  have hh := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using hh

theorem lowGramExceptional_raw_count (F : Finset O) (G : Id) (H : ℝ) (hH : 0≤ H)
    (hF : ∀z∈F,z≠0)
    (hres : ∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0)
    (hN : ∀z∈F,(Ideal.absNorm (Ideal.span {z}):ℝ)≤ H) :
    (F.card:ℝ)≤768*(6:ℝ)^(primeSupport G).card*H^(1/6:ℝ) := by
  have hh := element_count_remainder_family F (lowGramRemainders F)
    (lowGramRemainders_nonzero F) H hH hF (fun z hz=> Finset.mem_image.mpr ⟨z,hz,rfl⟩) hN
  calc
    _ ≤ ∑R∈lowGramRemainders F,768*(H/(Ideal.absNorm R:ℝ))^(1/6:ℝ) := hh
    _ ≤ ∑_R∈lowGramRemainders F,768*H^(1/6:ℝ) := by
      apply Finset.sum_le_sum
      intro R hR
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow (div_nonneg hH (Nat.cast_nonneg _)) _ (by norm_num)
      exact div_le_self hH (norm_one_le (lowGramRemainders_nonzero F R hR))
    _ = (lowGramRemainders F).card*(768*H^(1/6:ℝ)) := by simp
    _ ≤ ((6:ℝ)^(primeSupport G).card)*(768*H^(1/6:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast lowGramRemainders_card F G hres
    _ = _ := by ring

/-- Sixth-power remainders bound exceptional frequencies by a sixth power of the norm cutoff. -/
theorem lowGramExceptional_count (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀G : Id,G≠0→∀F : Finset O,∀H : ℝ,0≤ H→
      (∀z∈F,z≠0)→
      (∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0)→
      (∀z∈F,(Ideal.absNorm (Ideal.span {z}):ℝ)≤ H)→
      (F.card:ℝ)≤ C*(Ideal.absNorm G:ℝ)^ε*H^(1/6:ℝ) := by
  obtain ⟨C,hC,hb⟩ := CompletedGauss.prime_support_subsets_bound (ε/3) (by positivity)
  refine ⟨768*C ^ 3,by positivity,?_⟩
  intro G hG F H hH hF hres hN
  have hp : (6:ℝ)^(primeSupport G).card≤ C ^ 3*(Ideal.absNorm G:ℝ)^ε := by
    calc
      _ ≤ ((2:ℝ)^3)^(primeSupport G).card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = ((2:ℝ)^(primeSupport G).card)^3 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
      _ ≤ (C*(Ideal.absNorm G:ℝ)^(ε/3))^3 := pow_le_pow_left₀ (by positivity) (hb G hG) 3
      _ = _ := by
        rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg (Ideal.absNorm G))]
        congr 2
        norm_num
  apply (lowGramExceptional_raw_count F G H hH hF hres hN).trans
  calc
    _ ≤ 768*(C ^ 3*(Ideal.absNorm G:ℝ)^ε)*H^(1/6:ℝ) := by gcongr
    _ = _ := by ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion 
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

lemma min_product_amplification (L T : ℝ) (hL : 0≤ L) (hT : 0≤ T) (A : ℕ) :
    min 1 ((L*T)^A)≤(1+T)^A*min 1 (L^A) := by
  by_cases h : L^A≤1
  · rw [min_eq_right h]
    apply (min_le_right _ _).trans
    rw [mul_pow,mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT (by linarith) _) (pow_nonneg hL _)
  · rw [min_eq_left (le_of_not_ge h),mul_one]
    exact (min_le_left _ _).trans (one_le_pow₀ (by linarith))

lemma frequencyScale_ratio (C : SupportedIdeal) (k : GramFrequency) (Y Q : ℝ) :
    frequencyScale C k.val Y Q=(Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/Ideal.absNorm C.val) := by
  rw [frequencyScale,ringComplex_norm_sq_eq_absNorm_span,div_div_eq_mul_div]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem canonical_nonexceptional_weighted (A : ℕ) (hA : 2< A) (a₀ b₀ : ℝ)
    (ha₀ : 0< a₀) (hab : a₀< b₀) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0< K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency),¬ExceptionalFrequency S hS C k→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v H N : ℝ),0< H→0< N→
        ‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
          (Ideal.absNorm C.val:ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A)*
          (1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := by
  obtain ⟨J,H₀,hblock⟩ := canonical_nonexceptional_block A (A+2) hA a₀ b₀ ha₀ hab
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hblock⟩ := hblock W hs hW
  refine ⟨K,hK,?_⟩
  intro S hS σ C k hk d U v H N hH hN
  let t : ℝ := (Ideal.absNorm (Ideal.span {k.val}):ℝ)/H
  let L : ℝ := (Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N
  have ht : 0≤ t := by dsimp [t];positivity
  have hL : 0≤ L := by dsimp [L];positivity
  have htp : 0<1+t := by linarith
  have he : (Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*Ideal.absNorm (Ideal.span {k.val})/N=L*t := by
    dsimp [L,t]
    field_simp
  have hb := hblock S hS σ C k hk d U v t N ht hN
  rw [he] at hb
  apply hb.trans
  calc
    _≤ K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+t)^(A+2)*
        (Ideal.absNorm C.val:ℝ)*N^2*((1+t)^A*min 1 (L^A)) :=
      mul_le_mul_of_nonneg_left (min_product_amplification L t hL ht A) (by positivity)
    _=K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Ideal.absNorm C.val:ℝ)*N^2*
        min 1 (L^A)*(1+t)^(-2:ℝ) := by
      rw [Real.rpow_neg htp.le,Real.rpow_two,pow_add]
      field_simp
    _=_ := rfl

end ProbeGramCommon
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace ProbeGramFrequencySummation
local notation "O" => Eisenstein.O

def frequencyNorm (k : O) : ℝ := Ideal.absNorm (Ideal.span {k})

lemma frequencyNorm_nonneg (k : O) : 0 ≤ frequencyNorm k := Nat.cast_nonneg _

lemma frequencyNorm_one_le (k : O) (hk : k ≠ 0) : 1 ≤ frequencyNorm k := by
  unfold frequencyNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hk))

theorem finite_weighted_of_count {α : Type*} (E : Finset α) (q : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (C d H : ℝ) (hC : 0 ≤ C) (hd : d ≤ 1) (hH : 0 < H)
    (hcount : ∀ F : Finset α, F ⊆ E → ∀ R : ℝ, 0 < R →
      (∀ x ∈ F, q x ≤ R) → (F.card : ℝ) ≤ C * R ^ d) :
    ∑ x ∈ E, (1 + q x / H) ^ (-2 : ℝ) ≤ 4 * C * H ^ d := by
  have hex (x : α) : ∃ n : ℕ, (2:ℝ)^n ≤ 1 + q x / H ∧
      1 + q x / H < (2:ℝ)^(n+1) :=
    exists_nat_pow_near (by linarith [div_nonneg (hq x) hH.le]) (by norm_num)
  let bin (x : α) : ℕ := Classical.choose (hex x)
  have hlo (x : α) : (2:ℝ)^(bin x) ≤ 1 + q x / H := (Classical.choose_spec (hex x)).1
  have hhi (x : α) : 1 + q x / H < (2:ℝ)^(bin x+1) := (Classical.choose_spec (hex x)).2
  have hbin (n : ℕ) :
      ∑ x ∈ E.filter (fun x => bin x = n), (1 + q x / H) ^ (-2 : ℝ) ≤
        (2*C*H^d) * (1/2:ℝ)^n := by
    let F := E.filter (fun x => bin x = n)
    have hcard : (F.card:ℝ) ≤ C * ((2:ℝ)^(n+1)*H)^d := by
      apply hcount F (Finset.filter_subset _ _) _ (by positivity)
      intro x hx
      have he := (Finset.mem_filter.mp hx).2
      have hh := hhi x
      rw [he] at hh
      have hqdiv : q x/H ≤ (2:ℝ)^(n+1) := by linarith
      exact (div_le_iff₀ hH).mp hqdiv
    have hweight (x : α) (hx : x∈F) : (1+q x/H)^(-2:ℝ) ≤ (1/4:ℝ)^n := by
      have hl := hlo x
      rw [(Finset.mem_filter.mp hx).2] at hl
      apply (Real.rpow_le_rpow_of_nonpos (by positivity) hl (by norm_num)).trans_eq
      rw [Real.rpow_neg (by positivity), Real.rpow_two, ← pow_mul, Nat.mul_comm, pow_mul, ← inv_pow]
      norm_num
    have hp : ((2:ℝ)^(n+1))^d ≤ (2:ℝ)^(n+1) :=
      Real.rpow_le_self_of_one_le (one_le_pow₀ (by norm_num)) hd
    calc
      _ ≤ (F.card:ℝ)*(1/4:ℝ)^n := by
        apply (Finset.sum_le_sum hweight).trans_eq
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C*((2:ℝ)^(n+1)*H)^d)*(1/4:ℝ)^n :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (C*((2:ℝ)^(n+1)*H^d))*(1/4:ℝ)^n := by
        rw [Real.mul_rpow (by positivity) hH.le]
        gcongr
      _ = (2*C*H^d)*((2:ℝ)^n*(1/4:ℝ)^n) := by rw [pow_succ]; ring
      _ = _ := by rw [←mul_pow]; norm_num
  have hsum : (∑ x∈E,(1+q x/H)^(-2:ℝ)) =
      ∑ n∈E.image bin, ∑ x∈E.filter (fun x=> bin x=n), (1+q x/H)^(-2:ℝ) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) _
  rw [hsum]
  apply (Finset.sum_le_sum (fun n _=> hbin n)).trans
  have hs := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).mul_left (2*C*H^d)
  apply (Summable.sum_le_tsum _ (by intro n _; positivity) hs).trans_eq
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)]
  ring

theorem nonzero_frequency_count (E : Finset O) (R : ℝ) (hR : 0 < R)
    (hE : ∀ k∈E, k≠0) (hN : ∀ k∈E, frequencyNorm k≤ R) :
    (E.card:ℝ) ≤ 128*R := by
  by_cases hr : 1≤ R
  · apply EisensteinLatticeCount.finite_element_count_real E R hr
    intro k hk
    simpa only [ringComplex_norm_sq_eq_absNorm_span,frequencyNorm]
      using hN k hk
  · have he : E=∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro k hk
      have hh := frequencyNorm_one_le k (hE k hk)
      have hb := hN k hk
      linarith)
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem frequency_weighted_sum :
    ∃ K : ℝ, 0< K ∧ ∀ (E : Finset O) (H : ℝ), 0< H →
      (∀ k∈E,k≠0) →
      ∑ k∈E,(1+frequencyNorm k/H)^(-2:ℝ) ≤ K*H := by
  refine ⟨512,by norm_num,?_⟩
  intro E H hH hE
  have hh := finite_weighted_of_count E frequencyNorm frequencyNorm_nonneg
    128 1 H (by norm_num) (by norm_num) hH (by
      intro F hFE R hR hN
      simpa only [Real.rpow_one] using
        nonzero_frequency_count F R hR (fun k hk=> hE k (hFE hk)) hN)
  norm_num only [Real.rpow_one,show (4:ℝ)*128=512 by norm_num] at hh
  exact hh

theorem exceptional_frequency_weighted_sum (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ, 0< K ∧ ∀ G : Ideal O, G≠0 → ∀ (E : Finset O) (H : ℝ), 0< H →
      (∀ k∈E,k≠0) →
      (∀ k∈E,∀ P∉CubicEisenstein.primeSupport G,
        CenteredExceptionalCount.valuation (Ideal.span {k}) P % 6=0) →
      ∑ k∈E,(1+frequencyNorm k/H)^(-2:ℝ) ≤
        K*(Ideal.absNorm G:ℝ)^ε*H^(1/6:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := ProbePhysical.lowGramExceptional_count ε hε
  refine ⟨4*C,by positivity,?_⟩
  intro G hG E H hH hE hres
  have hh := finite_weighted_of_count E frequencyNorm frequencyNorm_nonneg
    (C*(Ideal.absNorm G:ℝ)^ε) (1/6) H (by positivity) (by norm_num) hH (by
      intro F hFE R hR hN
      exact hcount G hG F R hR.le (fun k hk=> hE k (hFE hk))
        (fun k hk=> hres k (hFE hk)) hN)
  convert hh using 1
  ring

end ProbeGramFrequencySummation

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
