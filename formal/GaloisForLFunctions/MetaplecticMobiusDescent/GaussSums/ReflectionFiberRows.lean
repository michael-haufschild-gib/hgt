/-
Reflection fiber rows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.GaussSums.FreeReflectionPools

/-!
# Reflection fiber rows

The convergent reflected series is a finite sum of exceptional local branches. Representative
row fibers, fiber reconstruction and ramified branch phases; the actual cusp coefficient is
four times the quadratic-sieve coefficient.
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

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection
open scoped BigOperators Classical ContDiff

def normalizedCuspBranchCoefficient {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N})
    (u : Oˣ) (m : ℕ) (I J : Ideal O) : ℂ :=
  ramifiedBracketPhase P hg j u m*completedCuspArray N c s b u m I J*
    reflectedBranch P hg j e (primaryIdealGenerator I) (primaryIdealGenerator J)/
    (completedCuspArrayWeight m I J:ℂ)

lemma normalizedCuspCoefficient_eq_sum_branches {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N})
    (u : Oˣ) (m : ℕ) (I J : Ideal O) :
    normalizedCuspCoefficient P hg j N c s b u m I J=
      ∑e : ι→Fin 3,normalizedCuspBranchCoefficient P hg j e N c s b u m I J := by
  simp only [normalizedCuspCoefficient,prod_bracket_eq_full_branches,
    Finset.mul_sum,Finset.sum_div,normalizedCuspBranchCoefficient]

lemma reflectedBranch_norm_le_product_bound {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) :
    ‖reflectedBranch P hg j e n b‖≤bracketProductBound P j := by
  rw [reflectedBranch,norm_prod]
  apply Finset.prod_le_prod (fun _ _=>norm_nonneg _)
  intro i hi
  exact (reflectedLocalPiece_norm_le (P i) (hg i) (j i) (e i) n b).trans
    (Finset.single_le_sum (fun v _=>(reflectedLocalSize_pos (P i) (j i) v).le) (Finset.mem_univ (e i)))

lemma normalizedCuspBranchCoefficient_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N})
    (u : Oˣ) (m : ℕ) (I J : NonzeroDualIdeal) :
    ‖normalizedCuspBranchCoefficient P hg j e N c s b u m I.val J.val‖≤bracketProductBound P j := by
  have hw:=completedCuspArrayWeight_ge_one m I J
  have hw0 : 0≤completedCuspArrayWeight m I.val J.val:=zero_le_one.trans hw
  rw [normalizedCuspBranchCoefficient,norm_div,norm_mul,norm_mul,ramifiedBracketPhase_norm,one_mul,
    Complex.norm_real,Real.norm_of_nonneg hw0]
  apply (div_le_div_of_nonneg_right
    ((mul_le_of_le_one_left (norm_nonneg _) (completedCuspArray_norm N c s b u m I.val J.val)).trans
      (reflectedBranch_norm_le_product_bound P hg j e _ _)) hw0).trans
  exact div_le_self (bracketProductBound_pos P j).le hw

lemma normalizedCuspBranchKernel_summable {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (V : ℝ→ℂ) (a b₀ : ℝ) (ha : 0<a) (hs : Function.support V⊆Set.Icc a b₀)
    (hV : ContDiff ℝ ∞ V) (scale : ℝ) (hscale : 0<scale) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ‖rawDualKernelTerm V scale 1 completedRamifiedStep
        (normalizedCuspBranchCoefficient P hg j e N c s b u) x‖) :=
  rawDualKernelTerm_summable_norm V a b₀ ha hs hV scale 1 completedRamifiedStep
    (bracketProductBound P j) hscale zero_lt_one completedRamifiedStep_gt_one
    (bracketProductBound_pos P j).le _ (normalizedCuspBranchCoefficient_norm P hg j e N c s b u)

/-- The convergent reflected series is the finite sum of its exceptional local branches. -/
theorem normalizedCuspKernel_tsum_branches {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (V : ℝ→ℂ) (a b₀ : ℝ) (ha : 0<a) (hs : Function.support V⊆Set.Icc a b₀)
    (hV : ContDiff ℝ ∞ V) (scale : ℝ) (hscale : 0<scale) :
    (∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      rawDualKernelTerm V scale 1 completedRamifiedStep
        (normalizedCuspCoefficient P hg j N c s b u) x)=
    ∑e : ι→Fin 3,∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      rawDualKernelTerm V scale 1 completedRamifiedStep
        (normalizedCuspBranchCoefficient P hg j e N c s b u) x := by
  have hpoint (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
      rawDualKernelTerm V scale 1 completedRamifiedStep
        (normalizedCuspCoefficient P hg j N c s b u) x=
      ∑e : ι→Fin 3,rawDualKernelTerm V scale 1 completedRamifiedStep
        (normalizedCuspBranchCoefficient P hg j e N c s b u) x := by
    simp only [rawDualKernelTerm,normalizedCuspCoefficient_eq_sum_branches,Finset.sum_mul]
  rw [tsum_congr hpoint,Summable.tsum_finsetSum
    (fun e _=>(normalizedCuspBranchKernel_summable P hg j e N c s b u V a b₀ ha hs hV scale hscale).of_norm)]

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection
open scoped BigOperators Classical ContDiff

/-- Residual primes have exponent one, so all their nonzero exceptional labels vanish. -/
theorem normalizedCuspKernel_drop_residual {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (E : α⊕β≃ι) (hj : ∀a,j (E (Sum.inl a))=1)
    (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (V : ℝ→ℂ) (scale : ℝ) :
    (∑e : ι→Fin 3,∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      rawDualKernelTerm V scale 1 completedRamifiedStep
        (normalizedCuspBranchCoefficient P hg j e N c s b u) x)=
    ∑e : β→Fin 3,∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      rawDualKernelTerm V scale 1 completedRamifiedStep
        (normalizedCuspBranchCoefficient P hg j (residualLabelVia E e) N c s b u) x := by
  apply sum_labels_drop_residual_equiv E
  intro e he
  trans ∑'_x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,(0:ℂ)
  · apply tsum_congr
    intro x
    simp only [rawDualKernelTerm,normalizedCuspBranchCoefficient,
      reflectedBranch_residual_zero_equiv E P hg j hj e he,mul_zero,zero_div,zero_mul]
  · exact tsum_zero

lemma normalizedCuspBranchCoefficient_residual {ι β : Type*} [Fintype ι] [Fintype β]
    (k : Ideal O) (hk : quadraticIdealAdmissible k)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (R : β→Ideal O) [∀i,(R i).IsMaximal] (hR : ∀i,lambda∉R i)
    (E : primeSupport k⊕β≃ι)
    (hres : ∀r,P (E (Sum.inl r))=r.val) (hnonres : ∀r,P (E (Sum.inr r))=R r)
    (j : ι→ℕ) (l : β→ℕ) (hjres : ∀r,j (E (Sum.inl r))=1)
    (hjnonres : ∀r,j (E (Sum.inr r))=l r) (e : β→Fin 3)
    (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (m : ℕ) (n v : Ideal O) :
    normalizedCuspBranchCoefficient P hg j (residualLabelVia E e) N c s b u m n v=
      ramifiedBracketPhase P hg j u m*completedCuspArray N c s b u m n v*
        (canonicalQuadraticRowOfIdeal k (primaryIdealGenerator n)*
          canonicalQuadraticRowOfIdeal k (primaryIdealGenerator v))*
        reflectedBranch R hR l e (primaryIdealGenerator n) (primaryIdealGenerator v)/
        (completedCuspArrayWeight m n v:ℂ) := by
  rw [normalizedCuspBranchCoefficient,
    reflectedBranch_residual_coefficient k hk P hg R hR E hres hnonres j l hjres hjnonres]
  ring

lemma normalizedCuspBranch_support {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (hcop : Pairwise (fun i k=>IsCoprime (P i) (P k))) (j : ι→ℕ) (e : ι→Fin 3)
    (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N})
    (u : Oˣ) (m : ℕ) (I J : Ideal O)
    (hne : normalizedCuspBranchCoefficient P hg j e N c s b u m I J≠0) :
    reflectionExtractedDivisor P j e 1∣I ∧ reflectionExtractedDivisor P j e 2∣J := by
  apply completedCuspBranch_support P hg hcop j e N c s b u m I J
  intro hz
  exact hne (by simp only [normalizedCuspBranchCoefficient,mul_assoc,hz,mul_zero,zero_div])

theorem normalizedCuspBranchKernel_tsum_extract {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (hcop : Pairwise (fun i k=>IsCoprime (P i) (P k))) (j : ι→ℕ) (e : ι→Fin 3)
    (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (V : ℝ→ℂ) (scale : ℝ) :
    let D:=reflectionExtractedDivisor P j e 1
    let E:=reflectionExtractedDivisor P j e 2
    let hD:=reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e 1
    let hE:=reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e 2
    (∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      rawDualKernelTerm V scale 1 completedRamifiedStep
        (normalizedCuspBranchCoefficient P hg j e N c s b u) x)=
    ∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      rawDualKernelTerm V scale 1 completedRamifiedStep
        (normalizedCuspBranchCoefficient P hg j e N c s b u) (nonzeroDualDilation D E hD hE x) := by
  dsimp only
  apply tsum_nonzeroDualDilation
  intro x hx
  exact normalizedCuspBranch_support P hg hcop j e N c s b u x.1 x.2.1.val x.2.2.val
    (mul_ne_zero_iff.mp hx).1

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection CompletedDyadic
open scoped BigOperators Classical

/-- After divisor extraction, the actual cusp coefficient is four times the quadratic-sieve coefficient. -/
theorem normalizedCuspBranchCoefficient_extracted {ι β : Type*} [Fintype ι] [Fintype β]
    (k : Ideal O) (hk : quadraticIdealAdmissible k)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (R : β→Ideal O) [∀i,(R i).IsMaximal] (hR : ∀i,lambda∉R i)
    (E : primeSupport k⊕β≃ι)
    (hres : ∀r,P (E (Sum.inl r))=r.val) (hnonres : ∀r,P (E (Sum.inr r))=R r)
    (j : ι→ℕ) (l : β→ℕ) (hjres : ∀r,j (E (Sum.inl r))=1)
    (hjnonres : ∀r,j (E (Sum.inr r))=l r) (e : β→Fin 3)
    (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (m : ℕ) (n v : Ideal O) :
    let D:=reflectionExtractedDivisor R l e 1
    let H:=reflectionExtractedDivisor R l e 2
    normalizedCuspBranchCoefficient P hg j (residualLabelVia E e) N c s b u m (D*n) (H*v)=
      4*canonicalRawBranchCoefficient R hR l e 1 completedRamifiedStep
        (fun m n v=>completedCuspArray N c s b u m (D*n) (H*v))
        (fun m=>ramifiedBracketPhase P hg j u m*residualArgumentPhase k D H) k m n v := by
  dsimp only
  rw [normalizedCuspBranchCoefficient_residual k hk P hg R hR E hres hnonres j l hjres hjnonres,
    canonicalRawBranchCoefficient_cusp,completedCuspArrayWeight_step]
  simp only [ramifiedScale,one_mul]

lemma reflectionExtractedDivisor_transport {ι : Type*} [Fintype ι]
    (P R : ι→Ideal O) (hP : ∀i,P i=R i) (j l : ι→ℕ) (hj : ∀i,j i=l i)
    (e : ι→Fin 3) (v : Fin 3) :
    reflectionExtractedDivisor P j e v=reflectionExtractedDivisor R l e v := by
  simp only [reflectionExtractedDivisor,hP,hj]

lemma reflectionExtractedDivisor_residual_model {ι β : Type*} [Fintype ι] [Fintype β]
    (k : Ideal O) (P : ι→Ideal O) (R : β→Ideal O) (E : primeSupport k⊕β≃ι)
    (hnonres : ∀r,P (E (Sum.inr r))=R r)
    (j : ι→ℕ) (l : β→ℕ) (hjres : ∀r,j (E (Sum.inl r))=1)
    (hjnonres : ∀r,j (E (Sum.inr r))=l r) (e : β→Fin 3) (v : Fin 3) :
    reflectionExtractedDivisor P j (residualLabelVia E e) v=reflectionExtractedDivisor R l e v := by
  rw [reflectionExtractedDivisor_drop_residual_equiv E P j hjres]
  exact reflectionExtractedDivisor_transport _ _ hnonres _ _ hjnonres _ _

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion SecondPassArithmetic
open scoped BigOperators Classical

lemma primeProduct_norm_fourth {ι : Type*} [Fintype ι] (p : ι→O) :
    ‖ringComplex (∏i,p i)‖^4=(Ideal.absNorm (∏i,Ideal.span {p i}):ℝ)^2 := by
  rw [show (4:ℕ)=2*2 by decide,pow_mul,ringComplex_norm_sq_eq_absNorm_span,
    span_finset_prime_product]

lemma fixedCuspReflectionScale_linear (s : FixedCuspSector) (c : O) (X Y : ℝ) :
    fixedCuspReflectionScale s c (X/Y)=fixedCuspReflectionScale s c 1*X/Y := by
  unfold fixedCuspReflectionScale
  ring

lemma completedRawKernelScale_eq {ι : Type*} [Fintype ι]
    (K X level : ℝ) (I F Q k : Ideal O) (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (e : ι→Fin 3) (hK : 0<completedResidualScale K I Q) (hX : 0<X)
    (hlevel : 0<level) (hk : k≠0) :
    (completedBranchScale K (X/level) I F Q P e)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k:ℝ))^2=
      X*(Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 1):ℝ)*
        (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 2):ℝ)^3/
        (level*((Ideal.absNorm k:ℝ)*(Ideal.absNorm (∏i,P i):ℝ))^2) := by
  have hp:=nonzeroDualIdeal_norm_pos
    ⟨∏i,P i,Finset.prod_ne_zero_iff.mpr (fun i _=>NeZero.ne (P i))⟩
  have hd:=nonzeroDualIdeal_norm_pos
    ⟨reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 1,
      reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) _ e 1⟩
  have he:=nonzeroDualIdeal_norm_pos
    ⟨reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 2,
      reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) _ e 2⟩
  have hkn:=nonzeroDualIdeal_norm_pos ⟨k,hk⟩
  unfold completedBranchScale
  field_simp [hK.ne',hX.ne',hlevel.ne',hkn.ne',hp.ne',hd.ne',he.ne']
  <;> ring

/-- The reflected cusp scale equals the scale in the dyadic quadratic-sieve kernel. -/
theorem fixedCusp_kernel_extracted_scale {ι β : Type*} [Fintype ι] [Fintype β]
    (p : ι→O) (P : β→Ideal O) [∀i,(P i).IsMaximal]
    (I F Q k : Ideal O) (hk : k≠0)
    (hprod : (∏i,Ideal.span {p i})=k*∏i,P i)
    (e : β→Fin 3) (s : FixedCuspSector) (c : O) (hc : c≠0)
    (K X q : ℝ) (hK : 0<completedResidualScale K I Q) (hX : 0<X)
    (m : ℕ) (n b : Ideal O) :
    let D:=reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 1
    let E:=reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 2
    let level:=(fixedCuspReflectionScale s c 1)⁻¹
    fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4)*(q^m)^3*
      (Ideal.absNorm (D*n):ℝ)*(Ideal.absNorm (E*b):ℝ)^3=
      ((completedBranchScale K (X/level) I F Q P e)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k:ℝ))^2)*(q^m)^3*
        (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3 := by
  dsimp only
  have hl:=fixedCuspReflectionScale_pos s c hc 1 zero_lt_one
  rw [completedRawKernelScale_eq K X _ I F Q k P e hK hX (inv_pos.mpr hl) hk,
    primeProduct_norm_fourth,hprod,fixedCuspReflectionScale_linear]
  simp only [map_mul,Nat.cast_mul,div_eq_mul_inv,mul_inv_rev,inv_inv,mul_pow]
  ring

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection
open scoped BigOperators Classical ContDiff
local instance : Finite Oˣ:=cubic_units_finite
local instance : Fintype Oˣ:=Fintype.ofFinite _

/-- Each completed cusp divisor series is a finite sum of convergent normalized branches. -/
theorem fixedCuspDivisorSeries_unit_branches {ι : Type*} [Fintype ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hg : ∀i,lambda∉Ideal.span {p i}) (N c : O) (hc : c≠0)
    (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (j : ι→ℕ) (hj : ∀i,j i<6)
    (V : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hs : Function.support V⊆Set.Icc A B)
    (hV : ContDiff ℝ ∞ V) (X : ℝ) (hX : 0<X) (β : ℂ) :
    β*fixedCuspDivisorSeries p hg N c s b j V X=
      ((β/(gaussScale (fun i=>O⧸Ideal.span {p i}) j:ℂ))*(completedCuspArrayConstant s:ℂ))*
      ∑u : Oˣ,∑e : ι→Fin 3,∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
        rawDualKernelTerm V (fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4)) 1
          completedRamifiedStep (normalizedCuspBranchCoefficient (fun i=>Ideal.span {p i}) hg j e N c s b u) x := by
  rw [fixedCuspDivisorSeries_fullDual p hp hg N c hc s b j hj V A B hA hs hV X hX β]
  have hp0 : ringComplex (∏i,p i)≠0:=ringComplex_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  have hscale : 0<fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4):=
    fixedCuspReflectionScale_pos s c hc _ (div_pos hX (pow_pos (norm_pos_iff.mpr hp0) _))
  have hsum:=normalizedCuspFullKernel_summable (fun i=>Ideal.span {p i}) hg j N c s b
    V A B hA hs hV _ hscale
  rw [hsum.of_norm.tsum_prod,tsum_fintype]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  exact normalizedCuspKernel_tsum_branches _ hg j N c s b u V A B hA hs hV _ hscale

/-- Only labels on nonresidual primes survive in the reflected divisor series. -/
theorem fixedCuspDivisorSeries_residual_branches {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hg : ∀i,lambda∉Ideal.span {p i}) (N c : O) (hc : c≠0)
    (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (j : ι→ℕ) (hj : ∀i,j i<6)
    (E : α⊕β≃ι) (hres : ∀a,j (E (Sum.inl a))=1)
    (V : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hs : Function.support V⊆Set.Icc A B)
    (hV : ContDiff ℝ ∞ V) (X : ℝ) (hX : 0<X) (γ : ℂ) :
    γ*fixedCuspDivisorSeries p hg N c s b j V X=
      ((γ/(gaussScale (fun i=>O⧸Ideal.span {p i}) j:ℂ))*(completedCuspArrayConstant s:ℂ))*
      ∑u : Oˣ,∑e : β→Fin 3,∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
        rawDualKernelTerm V (fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4)) 1
          completedRamifiedStep
            (normalizedCuspBranchCoefficient (fun i=>Ideal.span {p i}) hg j (residualLabelVia E e) N c s b u) x := by
  rw [fixedCuspDivisorSeries_unit_branches p hp hg N c hc s b j hj V A B hA hs hV X hX γ]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  exact normalizedCuspKernel_drop_residual _ hg j E hres N c s b u V _

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection CanonicalRowCompletion
open scoped BigOperators Classical

/-- A cusp branch with its forced ideal divisors extracted. -/
def canonicalCuspRawValue {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (N c : O) (s : FixedCuspSector)
    (b : O⧸Ideal.span {N}) (u : Oˣ) (σ : ℕ→ℂ) (k : Ideal O)
    (V : ℝ→ℂ) (scale : ℝ) : ℂ :=
  let D:=reflectionExtractedDivisor P j e 1
  let H:=reflectionExtractedDivisor P j e 2
  ∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
    rawDualKernelTerm V scale 1 completedRamifiedStep
      (canonicalRawBranchCoefficient P hg j e 1 completedRamifiedStep
        (fun m n v=>completedCuspArray N c s b u m (D*n) (H*v))
        (fun m=>σ m*residualArgumentPhase k D H) k) x

/-- Divisor extraction identifies an actual cusp branch with the native quadratic-sieve series. -/
theorem normalizedCuspKernel_eq_rawBranch {ι β : Type*} [Fintype ι] [Fintype β]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i})
    (hcop : Pairwise (fun i r=>IsCoprime (Ideal.span {p i}) (Ideal.span {p r})))
    (R : β→Ideal O) [∀i,(R i).IsMaximal] (hR : ∀i,lambda∉R i)
    (I F Q k : Ideal O) (hk : quadraticIdealAdmissible k)
    (E : primeSupport k⊕β≃ι)
    (hres : ∀r,Ideal.span {p (E (Sum.inl r))}=r.val)
    (hnonres : ∀r,Ideal.span {p (E (Sum.inr r))}=R r)
    (j : ι→ℕ) (hjres : ∀r,j (E (Sum.inl r))=1)
    (hjnonres : ∀r,j (E (Sum.inr r))=completedLocalExponent I F (R r))
    (e : β→Fin 3) (N c : O) (hc : c≠0) (s : FixedCuspSector)
    (b : O⧸Ideal.span {N}) (u : Oˣ) (V : ℝ→ℂ)
    (K X : ℝ) (hK : 0<completedResidualScale K I Q) (hX : 0<X) :
    (∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      rawDualKernelTerm V (fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4)) 1
        completedRamifiedStep
        (normalizedCuspBranchCoefficient (fun i=>Ideal.span {p i}) hg j
          (residualLabelVia E e) N c s b u) x)=
    4*canonicalCuspRawValue R hR (fun i=>completedLocalExponent I F (R i)) e N c s b u
      (ramifiedBracketPhase (fun i=>Ideal.span {p i}) hg j u) k V
      ((completedBranchScale K (X/(fixedCuspReflectionScale s c 1)⁻¹) I F Q R e)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k:ℝ))^2) := by
  let D:=reflectionExtractedDivisor R (fun i=>completedLocalExponent I F (R i)) e 1
  let H:=reflectionExtractedDivisor R (fun i=>completedLocalExponent I F (R i)) e 2
  have hD:=reflectionExtractedDivisor_ne_zero R (fun i=>NeZero.ne (R i))
    (fun i=>completedLocalExponent I F (R i)) e 1
  have hH:=reflectionExtractedDivisor_ne_zero R (fun i=>NeZero.ne (R i))
    (fun i=>completedLocalExponent I F (R i)) e 2
  have hdiv (v : Fin 3) := reflectionExtractedDivisor_residual_model k
    (fun i=>Ideal.span {p i}) R E hnonres j (fun i=>completedLocalExponent I F (R i))
    hjres hjnonres e v
  have hprod : (∏i,Ideal.span {p i})=k*∏i,R i :=
    active_product_admissible_equiv k hk.2.1 (fun i=>Ideal.span {p i}) R E hres hnonres
  rw [canonicalCuspRawValue,←tsum_mul_left]
  calc
    _=∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
        rawDualKernelTerm V (fixedCuspReflectionScale s c (X/‖ringComplex (∏i,p i)‖^4)) 1
          completedRamifiedStep
          (normalizedCuspBranchCoefficient (fun i=>Ideal.span {p i}) hg j
            (residualLabelVia E e) N c s b u) (nonzeroDualDilation D H hD hH x) := by
      apply tsum_nonzeroDualDilation
      intro x hx
      have hs:=normalizedCuspBranch_support (fun i=>Ideal.span {p i}) hg hcop j
        (residualLabelVia E e) N c s b u x.1 x.2.1.val x.2.2.val (mul_ne_zero_iff.mp hx).1
      rw [hdiv 1,hdiv 2] at hs
      exact hs
    _=_ := by
      apply tsum_congr
      intro x
      dsimp only [rawDualKernelTerm,nonzeroDualDilation]
      rw [normalizedCuspBranchCoefficient_extracted k hk (fun i=>Ideal.span {p i}) hg
        R hR E hres hnonres j (fun i=>completedLocalExponent I F (R i)) hjres hjnonres]
      simp only [one_mul]
      rw [fixedCusp_kernel_extracted_scale p R I F Q k hk.2.1.ne_zero hprod e s c hc
        K X completedRamifiedStep hK hX x.1 x.2.1.val x.2.2.val]
      ring

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection CanonicalRowCompletion
open scoped BigOperators Classical ContDiff
local instance : Finite Oˣ:=cubic_units_finite
local instance : Fintype Oˣ:=Fintype.ofFinite _

/-- The cusp divisor series is exactly the finite sum of residual quadratic-sieve branches. -/
theorem fixedCuspDivisorSeries_raw_branches {ι β : Type*} [Fintype ι] [Fintype β]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hg : ∀i,lambda∉Ideal.span {p i})
    (hcop : Pairwise (fun i r=>IsCoprime (Ideal.span {p i}) (Ideal.span {p r})))
    (R : β→Ideal O) [∀i,(R i).IsMaximal] (hR : ∀i,lambda∉R i)
    (I F Q k : Ideal O) (hk : quadraticIdealAdmissible k)
    (E : primeSupport k⊕β≃ι)
    (hres : ∀r,Ideal.span {p (E (Sum.inl r))}=r.val)
    (hnonres : ∀r,Ideal.span {p (E (Sum.inr r))}=R r)
    (j : ι→ℕ) (hj : ∀i,j i<6) (hjres : ∀r,j (E (Sum.inl r))=1)
    (hjnonres : ∀r,j (E (Sum.inr r))=completedLocalExponent I F (R r))
    (N c : O) (hc : c≠0) (s : FixedCuspSector) (b : O⧸Ideal.span {N})
    (V : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hs : Function.support V⊆Set.Icc A B)
    (hV : ContDiff ℝ ∞ V) (K X : ℝ)
    (hK : 0<completedResidualScale K I Q) (hX : 0<X) (γ : ℂ) :
    γ*fixedCuspDivisorSeries p hg N c s b j V X=
      (4*(γ/(gaussScale (fun i=>O⧸Ideal.span {p i}) j:ℂ))*(completedCuspArrayConstant s:ℂ))*
      ∑u : Oˣ,∑e : β→Fin 3,
        canonicalCuspRawValue R hR (fun i=>completedLocalExponent I F (R i)) e N c s b u
          (ramifiedBracketPhase (fun i=>Ideal.span {p i}) hg j u) k V
          ((completedBranchScale K (X/(fixedCuspReflectionScale s c 1)⁻¹) I F Q R e)⁻¹*
            (completedResidualScale K I Q/(Ideal.absNorm k:ℝ))^2) := by
  rw [fixedCuspDivisorSeries_residual_branches p hp hg N c hc s b j hj E hjres
    V A B hA hs hV X hX γ]
  simp_rw [normalizedCuspKernel_eq_rawBranch p hg hcop R hR I F Q k hk E hres hnonres
    j hjres hjnonres _ N c hc s b _ V K X hK hX]
  simp only [←Finset.mul_sum]
  ring

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion
open scoped BigOperators Classical

def representativeRowFiber (rows:Finset (Ideal O)) (I Q:Ideal O) : Finset (Ideal O) :=
  completedRowFiber rows Q (rowPowerfulPart I) (rowMaskPart I Q)

/-- Recover a row from its fixed powerful and mask parts and its residual ideal. -/
def reconstructFiberRow (I Q k:Ideal O) : Ideal O :=
  rowPowerfulPart I*rowMaskPart I Q*k

lemma reconstructFiberRow_ne_zero (I Q k:Ideal O) (hk:k≠0) : reconstructFiberRow I Q k≠0 :=
  mul_ne_zero (mul_ne_zero (rowPowerfulPart_ne_zero I)
    (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)) hk

lemma reconstructFiberRow_of_original (rows:Finset (Ideal O)) (I Q J:Ideal O)
    (hJ:J∈representativeRowFiber rows I Q) (hJ0:J≠0) :
    reconstructFiberRow I Q (rowResidualPart J Q)=J := by
  obtain ⟨_,hA,hT⟩:=Finset.mem_filter.mp hJ
  rw [reconstructFiberRow,←hA,←hT]
  exact row_powerful_mask_residual_product J Q hJ0

lemma residual_reconstructFiberRow (rows:Finset (Ideal O)) (I Q k:Ideal O)
    (hk:k≠0) (hmem:reconstructFiberRow I Q k∈representativeRowFiber rows I Q) :
    rowResidualPart (reconstructFiberRow I Q k) Q=k := by
  have he:=reconstructFiberRow_of_original rows I Q _ hmem (reconstructFiberRow_ne_zero I Q k hk)
  exact mul_left_cancel₀ (mul_ne_zero (rowPowerfulPart_ne_zero I)
    (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)) he

lemma representativeRowFiber_injective (rows:Finset (Ideal O)) (I Q:Ideal O)
    (hrows:∀J∈rows,J≠0) :
    Set.InjOn (fun J=>rowResidualPart J Q) (representativeRowFiber rows I Q) :=
  rowResidualPart_injective_on_fiber rows Q (rowPowerfulPart I) (rowMaskPart I Q) hrows

def fiberResidualIndex (rows:Finset (Ideal O)) (I Q:Ideal O) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (J:representativeRowFiber rows I Q) : idealRange (completedResidualScale K I Q) :=
  ⟨rowResidualPart J.val Q,completedRowFiber_residual_range rows Q
    (rowPowerfulPart I) (rowMaskPart I Q) hbad K hrows J.val J.property⟩

lemma fiberResidualIndex_injective (rows:Finset (Ideal O)) (I Q:Ideal O) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K) :
    Function.Injective (fiberResidualIndex rows I Q K hbad hrows) := by
  intro J lengthScale he
  apply Subtype.ext
  apply representativeRowFiber_injective rows I Q (fun J hJ=>(hrows J hJ).1) J.property lengthScale.property
  exact congrArg Subtype.val he

/-- Extend row coefficients by zero using the unique reconstructed row. -/
def extendFiberRowScalar {α:Type*} (rows:Finset (Ideal O)) (I Q:Ideal O) (K:ℝ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (k:idealRange (completedResidualScale K I Q)) : ℂ :=
  if h:reconstructFiberRow I Q k.val∈representativeRowFiber rows I Q then
    scalar a ⟨reconstructFiberRow I Q k.val,h⟩ else 0

lemma extendFiberRowScalar_norm_le_one {α:Type*} (rows:Finset (Ideal O)) (I Q:Ideal O) (K:ℝ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (hscalar:∀a J,‖scalar a J‖≤1)
    (a:α) (k:idealRange (completedResidualScale K I Q)) :
    ‖extendFiberRowScalar rows I Q K scalar a k‖≤1 := by
  unfold extendFiberRowScalar
  split_ifs
  · exact hscalar _ _
  · simp

lemma extendFiberRowScalar_zero {α:Type*} (rows:Finset (Ideal O)) (I Q:Ideal O) (K:ℝ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (k:idealRange (completedResidualScale K I Q))
    (hk:reconstructFiberRow I Q k.val∉representativeRowFiber rows I Q) :
    extendFiberRowScalar rows I Q K scalar a k=0 := by
  simp only [extendFiberRowScalar,dif_neg hk]

lemma extendFiberRowScalar_at_original {α:Type*} (rows:Finset (Ideal O)) (I Q:Ideal O) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (J:representativeRowFiber rows I Q) :
    extendFiberRowScalar rows I Q K scalar a (fiberResidualIndex rows I Q K hbad hrows J)=scalar a J := by
  have hJ0:J.val≠0:=(hrows J.val (Finset.mem_filter.mp J.property).1).1
  have he:=reconstructFiberRow_of_original rows I Q J.val J.property hJ0
  simp only [extendFiberRowScalar,fiberResidualIndex,he,dif_pos J.property]

def extendSelectedFiberRowScalar {α τ:Type*} [DecidableEq τ]
    (rows:Finset (Ideal O)) (I Q:Ideal O) (K:ℝ)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (t:τ) (a:α)
    (k:idealRange (completedResidualScale K I Q)) : ℂ :=
  extendFiberRowScalar rows I Q K (fun a J=>if selector a J=t then scalar a J else 0) a k

lemma extendSelectedFiberRowScalar_norm_le_one {α τ:Type*} [DecidableEq τ]
    (rows:Finset (Ideal O)) (I Q:Ideal O) (K:ℝ)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (hscalar:∀a J,‖scalar a J‖≤1)
    (t:τ) (a:α) (k:idealRange (completedResidualScale K I Q)) :
    ‖extendSelectedFiberRowScalar rows I Q K selector scalar t a k‖≤1 := by
  apply extendFiberRowScalar_norm_le_one
  intro a J
  split_ifs
  · exact hscalar a J
  · simp

lemma extendSelectedFiberRowScalar_at_original {α τ:Type*} [DecidableEq τ]
    (rows:Finset (Ideal O)) (I Q:Ideal O) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (t:τ) (a:α)
    (J:representativeRowFiber rows I Q) :
    extendSelectedFiberRowScalar rows I Q K selector scalar t a
      (fiberResidualIndex rows I Q K hbad hrows J)=
        if selector a J=t then scalar a J else 0 :=
  extendFiberRowScalar_at_original rows I Q K hbad hrows _ a J

lemma sum_extendSelectedFiberRowScalar {α τ:Type*} [Fintype τ] [DecidableEq τ]
    (rows:Finset (Ideal O)) (I Q:Ideal O) (K:ℝ)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (k:idealRange (completedResidualScale K I Q)) :
    (∑t:τ,extendSelectedFiberRowScalar rows I Q K selector scalar t a k)=
      extendFiberRowScalar rows I Q K scalar a k := by
  by_cases hk:reconstructFiberRow I Q k.val∈representativeRowFiber rows I Q
  · simp [extendSelectedFiberRowScalar,extendFiberRowScalar,hk]
  · simp only [extendSelectedFiberRowScalar,extendFiberRowScalar,dif_neg hk,Finset.sum_const_zero]


end CompletedGauss

namespace CompletedGauss.FreeReflection
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

/-- Zero padding the valid six-label encodings preserves the inactive local weight. -/
def reflectionSixInactiveWeight (I F Q Q0 : Ideal O) (e : pool I Q Q0→Fin 6) : ℂ :=
  if reflectionSixValid e then reflectionInactiveStratumWeight I F Q Q0 (reflectionSixSupport e) else 0

lemma reflectionSixInactiveWeight_norm (I F Q Q0 : Ideal O) (e : pool I Q Q0→Fin 6) :
    ‖reflectionSixInactiveWeight I F Q Q0 e‖≤1 := by
  unfold reflectionSixInactiveWeight
  split_ifs
  · exact reflectionInactiveStratumWeight_norm I F Q Q0 _
  · simp only [norm_zero,zero_le_one]

lemma reflectionSixInactiveWeight_encode (I F Q Q0 : Ideal O)
    (A : Finset (pool I Q Q0)) (e : A→Fin 3) :
    reflectionSixInactiveWeight I F Q Q0 (encodeReflectionSix ⟨A,e⟩)=
      reflectionInactiveStratumWeight I F Q Q0 A := by
  rw [reflectionSixInactiveWeight,if_pos (encodeReflectionSix_valid _),reflectionSixSupport_encode]

theorem sum_reflectionSixInactiveWeight_unpad (I F Q Q0 : Ideal O)
    (f : (pool I Q Q0→Fin 6)→ℂ) :
    (∑e : pool I Q Q0→Fin 6,reflectionSixInactiveWeight I F Q Q0 e*f e)=
      ∑A : Finset (pool I Q Q0),∑e : A→Fin 3,
        reflectionInactiveStratumWeight I F Q Q0 A*f (encodeReflectionSix ⟨A,e⟩) := by
  rw [sum_active_exceptional_eq_six]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hv : reflectionSixValid e
  · rw [if_pos hv,encode_decodeReflectionSix e hv,reflectionSixInactiveWeight,if_pos hv]
    rfl
  · rw [if_neg hv,reflectionSixInactiveWeight,if_neg hv,zero_mul]

end CompletedGauss.FreeReflection

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion
open scoped BigOperators Classical

@[reducible] def fixedCuspRayFintype (c : O) (hc : c≠0) : Fintype (FixedCuspRay c) := by
  letI : Finite (FixedCuspRay c):=fixedCuspRay_finite c hc
  exact Fintype.ofFinite _

def fixedCuspRayCount (c : O) (hc : c≠0) : ℕ :=
  @Fintype.card (FixedCuspRay c) (fixedCuspRayFintype c hc)

def fixedCuspRayEquiv (c : O) (hc : c≠0) : FixedCuspRay c≃Fin (fixedCuspRayCount c hc) :=
  @Fintype.equivFin (FixedCuspRay c) (fixedCuspRayFintype c hc)

namespace FreeReflection

abbrev FixedCuspBranchIndex (c : O) (I Q Q0 : Ideal O) :=
  FixedCuspRay c×(pool I Q Q0→Fin 6)

/-- A fixed ray supplies a row-independent cusp array to each local branch. -/
def sixFixedCuspBranch (c : O) (hc : c≠0) (I F Q Q0 : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (K : ℝ) (r : FixedCuspRay c) (e : pool I Q Q0→Fin 6)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hσ : ∀m k,‖σ m k‖≤1) :
    ReflectedBranchData (fixedCuspLevelBound c hc) K I F Q :=
  let d:=sixReflectedBranch I F Q Q0 hI hQ K (fixedCuspLevelBound c hc) (fixedCuspRayLevel c r)
    (fixedCuspRayLevel_pos c hc r) (fixedCuspRayLevel_le c hc r) e
    (fun _ _ _=>0) (by intro m n b; simp only [norm_zero,zero_le_one]) σ hσ
  d.withCompletedCuspArray (243*c) r.2.1.val r.2.2.1 r.2.2.2.1 r.2.2.2.2 σ hσ

/-- All cusp rays and six-label local choices form a finite reflected family. -/
def fixedCuspFiber (c : O) (hc : c≠0) (I F Q Q0 : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (K : ℝ) (w : FixedCuspBranchIndex c I Q Q0→ℂ) (hw : ∀x,‖w x‖≤1)
    (σ : FixedCuspBranchIndex c I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hσ : ∀x m k,‖σ x m k‖≤1) :
    ReflectedFiberData (fixedCuspRayCount c hc) (fixedCuspLevelBound c hc) K I F Q where
  pool:=pool I Q Q0
  maximal:=pool_maximal I Q Q0
  divides:=pool_divides I Q Q0 hI hQ
  branch:=fun x=>sixFixedCuspBranch c hc I F Q Q0 hI hQ K
    ((fixedCuspRayEquiv c hc).symm x.1) x.2
    (σ ((fixedCuspRayEquiv c hc).symm x.1,x.2))
    (hσ ((fixedCuspRayEquiv c hc).symm x.1,x.2))
  weight:=fun x=>w ((fixedCuspRayEquiv c hc).symm x.1,x.2)*
    reflectionSixInactiveWeight I F Q Q0 x.2
  weight_bound:=by
    intro x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw _)).trans
      (reflectionSixInactiveWeight_norm I F Q Q0 x.2)

theorem fixedCuspFiber_branch (c : O) (hc : c≠0) (I F Q Q0 : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (K : ℝ) (w : FixedCuspBranchIndex c I Q Q0→ℂ) (hw : ∀x,‖w x‖≤1)
    (σ : FixedCuspBranchIndex c I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hσ : ∀x m k,‖σ x m k‖≤1) (r : FixedCuspRay c) (e : pool I Q Q0→Fin 6) :
    (fixedCuspFiber c hc I F Q Q0 hI hQ K w hw σ hσ).branch (fixedCuspRayEquiv c hc r,e)=
      sixFixedCuspBranch c hc I F Q Q0 hI hQ K r e (σ (r,e)) (hσ (r,e)) := by
  dsimp only [fixedCuspFiber]
  simp only [Equiv.symm_apply_apply]

theorem fixedCuspFiber_value (c : O) (hc : c≠0) (I F Q Q0 : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (K : ℝ) (w : FixedCuspBranchIndex c I Q Q0→ℂ) (hw : ∀x,‖w x‖≤1)
    (σ : FixedCuspBranchIndex c I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hσ : ∀x m k,‖σ x m k‖≤1)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) :
    letI : Fintype (FixedCuspRay c):=fixedCuspRayFintype c hc
    (fixedCuspFiber c hc I F Q Q0 hI hQ K w hw σ hσ).value W X ρ q k=
      ∑r : FixedCuspRay c,∑A : Finset (pool I Q Q0),∑e : A→Fin 3,
        reflectionInactiveStratumWeight I F Q Q0 A*w (r,encodeReflectionSix ⟨A,e⟩)*
          (sixFixedCuspBranch c hc I F Q Q0 hI hQ K r (encodeReflectionSix ⟨A,e⟩)
            (σ (r,encodeReflectionSix ⟨A,e⟩)) (hσ (r,encodeReflectionSix ⟨A,e⟩))).value W X ρ q k := by
  letI : Fintype (FixedCuspRay c):=fixedCuspRayFintype c hc
  rw [ReflectedFiberData.value,Fintype.sum_prod_type]
  calc
    _=∑r : FixedCuspRay c,∑e : pool I Q Q0→Fin 6,
        reflectionSixInactiveWeight I F Q Q0 e*
          (w (r,e)*(sixFixedCuspBranch c hc I F Q Q0 hI hQ K r e
            (σ (r,e)) (hσ (r,e))).value W X ρ q k) := by
      apply Fintype.sum_equiv (fixedCuspRayEquiv c hc).symm
      intro t
      apply Finset.sum_congr rfl
      intro e he
      dsimp only [fixedCuspFiber]
      ring
    _=_ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro e he
      exact (mul_assoc _ _ _).symm

end FreeReflection
end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson NormalizedReflection
open scoped BigOperators Classical
local instance : Fintype FixedCuspSector:=Fintype.ofFinite _

/-- A single constant bounds the cusp coefficient normalization over all sectors. -/
def fixedCuspArrayBound : ℝ := 1+∑s : FixedCuspSector,completedCuspArrayConstant s

lemma fixedCuspArrayBound_pos : 0<fixedCuspArrayBound := by
  have hs : 0≤∑s : FixedCuspSector,completedCuspArrayConstant s :=
    Finset.sum_nonneg (fun s _=>(completedCuspArrayConstant_pos s).le)
  exact add_pos_of_pos_of_nonneg zero_lt_one hs

lemma completedCuspArrayConstant_le (s : FixedCuspSector) :
    completedCuspArrayConstant s≤fixedCuspArrayBound := by
  have h:=Finset.single_le_sum (fun t _=>(completedCuspArrayConstant_pos t).le) (Finset.mem_univ s)
  exact h.trans (le_add_of_nonneg_left zero_le_one)

lemma completedCuspArrayConstant_ratio_norm (s : FixedCuspSector) :
    ‖((completedCuspArrayConstant s/fixedCuspArrayBound:ℝ):ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_of_nonneg
    (div_nonneg (completedCuspArrayConstant_pos s).le fixedCuspArrayBound_pos.le)]
  exact (div_le_one fixedCuspArrayBound_pos).mpr (completedCuspArrayConstant_le s)

/-- The Fourier coefficient, normalized Gauss phase, and cusp constant have norm at most one. -/
def normalizedCuspRowScalar (fourier phase : ℂ) (gauss : ℝ) (s : FixedCuspSector) : ℂ :=
  fourier*((phase/(gauss:ℂ))/9)*((completedCuspArrayConstant s/fixedCuspArrayBound:ℝ):ℂ)

lemma normalizedCuspRowScalar_norm (fourier phase : ℂ) (gauss : ℝ) (s : FixedCuspSector)
    (hf : ‖fourier‖≤1) (hp : ‖phase/(gauss:ℂ)‖≤9) :
    ‖normalizedCuspRowScalar fourier phase gauss s‖≤1 := by
  have hd : ‖(phase/(gauss:ℂ))/9‖≤1 := by
    rw [norm_div,show ‖(9:ℂ)‖=(9:ℝ) by norm_num]
    exact (div_le_one (by norm_num)).mpr hp
  rw [normalizedCuspRowScalar,norm_mul,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) hf).trans hd)).trans
    (completedCuspArrayConstant_ratio_norm s)

lemma normalizedCuspRowScalar_reconstruct (fourier phase : ℂ) (gauss : ℝ) (s : FixedCuspSector) :
    (36*(fixedCuspArrayBound:ℂ))*normalizedCuspRowScalar fourier phase gauss s=
      fourier*(4*(phase/(gauss:ℂ))*(completedCuspArrayConstant s:ℂ)) := by
  have hc : (fixedCuspArrayBound:ℂ)≠0:=Complex.ofReal_ne_zero.mpr fixedCuspArrayBound_pos.ne'
  simp only [normalizedCuspRowScalar,Complex.ofReal_div]
  calc
    _=(36/9:ℂ)*fourier*(phase/(gauss:ℂ))*(completedCuspArrayConstant s:ℂ)*
        ((fixedCuspArrayBound:ℂ)*(fixedCuspArrayBound:ℂ)⁻¹) := by ring
    _=_ := by rw [mul_inv_cancel₀ hc]; ring

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion
open scoped BigOperators Classical

lemma canonicalCuspRawValue_mul_phase {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (N c : O) (s : FixedCuspSector)
    (b : O⧸Ideal.span {N}) (u : Oˣ) (σ : ℕ→ℂ) (k : Ideal O)
    (V : ℝ→ℂ) (scale : ℝ) (a : ℂ) :
    canonicalCuspRawValue P hg j e N c s b u (fun m=>a*σ m) k V scale=
      a*canonicalCuspRawValue P hg j e N c s b u σ k V scale := by
  rw [canonicalCuspRawValue,canonicalCuspRawValue,←tsum_mul_left]
  apply tsum_congr
  intro x
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient]
  ring

namespace ReflectedBranchData
variable {levelBound K : ℝ} {I F Q : Ideal O}
variable (d : ReflectedBranchData levelBound K I F Q)

lemma rawValue_congr_phase_at (η : ℕ→Ideal O→Ideal O→ℂ)
    (σ τ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q))
    (h : ∀m,σ m k=τ m k) :
    d.rawValue η σ W X ρ q k=d.rawValue η τ W X ρ q k := by
  unfold rawValue
  apply tsum_congr
  intro x
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient,h]

lemma rawValue_mul_phase (η : ℕ→Ideal O→Ideal O→ℂ)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) (a : ℂ) :
    d.rawValue η (fun m k=>a*σ m k) W X ρ q k=a*d.rawValue η σ W X ρ q k := by
  rw [rawValue,rawValue,←tsum_mul_left]
  apply tsum_congr
  intro x
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient]
  ring

lemma rawValue_cusp (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (W : ℝ→ℂ) (X : ℝ) (k : idealRange (completedResidualScale K I Q)) :
    letI : ∀p : d.primes,p.val.IsMaximal:=d.maximal
    let D:=reflectionExtractedDivisor (fun p : d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1
    let H:=reflectionExtractedDivisor (fun p : d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2
    d.rawValue (d.cuspAmplitude N c s b u)
      (fun m k=>σ m k*residualArgumentPhase k.val D H) W X 1 completedRamifiedStep k=
    canonicalCuspRawValue (fun p : d.primes=>p.val) d.good
      (fun p=>completedLocalExponent I F p.val) d.label N c s b u (fun m=>σ m k) k.val (Vstar W)
      ((completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes=>p.val) d.label)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k.val:ℝ))^2) := rfl

end ReflectedBranchData
end CompletedGauss

namespace CompletedGauss.FreeReflection
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

def supportActivePoolEquiv (I Q Q0:Ideal O) (e:pool I Q Q0 → Fin 6) :
    reflectionSixSupport e ≃ reflectionActivePool I Q Q0 e where
  toFun b:=⟨b.val.val,(mem_reflectionActivePool I Q Q0 e b.val).mpr
    (Finset.mem_filter.mp b.property).2⟩
  invFun P:=⟨⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem_reflectionActivePool I Q Q0 e _).mp P.property⟩⟩
  left_inv _b:=rfl
  right_inv _P:=rfl

lemma supportActivePoolEquiv_val (I Q Q0:Ideal O) (e:pool I Q Q0 → Fin 6)
    (b:reflectionSixSupport e) :
    (supportActivePoolEquiv I Q Q0 e b).val=b.val.val := rfl

lemma supportActivePoolEquiv_symm_val (I Q Q0:Ideal O) (e:pool I Q Q0 → Fin 6)
    (P:reflectionActivePool I Q Q0 e) :
    ((supportActivePoolEquiv I Q Q0 e).symm P).val.val=P.val := rfl

lemma supportActivePoolEquiv_label (I Q Q0:Ideal O) (e:pool I Q Q0 → Fin 6)
    (b:reflectionSixSupport e) :
    reflectionActiveLabel I Q Q0 e (supportActivePoolEquiv I Q Q0 e b)=
      reflectionSixLabel (e b.val) := rfl

def encodedActivePoolEquiv (I Q Q0:Ideal O) (B:Finset (pool I Q Q0)) (l:B → Fin 3) :
    B ≃ reflectionActivePool I Q Q0 (encodeReflectionSix ⟨B,l⟩) where
  toFun b:=⟨b.val.val,by
    rw [reflectionActivePool_encode]
    exact Finset.mem_image.mpr ⟨b.val,b.property,rfl⟩⟩
  invFun P:=⟨⟨P.val,reflectionActivePool_subset I Q Q0 _ P.property⟩,by
    have hp:P.val∈B.image Subtype.val:=by
      simpa only [reflectionActivePool_encode] using P.property
    obtain ⟨b,hb,he⟩:=Finset.mem_image.mp hp
    have he':b=⟨P.val,reflectionActivePool_subset I Q Q0 _ P.property⟩:=Subtype.ext he
    exact he' ▸ hb⟩
  left_inv b:=rfl
  right_inv P:=rfl

lemma encodedActivePoolEquiv_val (I Q Q0:Ideal O) (B:Finset (pool I Q Q0)) (l:B → Fin 3)
    (b:B) : (encodedActivePoolEquiv I Q Q0 B l b).val=b.val.val := rfl

lemma encodedActivePoolEquiv_label (I Q Q0:Ideal O) (B:Finset (pool I Q Q0)) (l:B → Fin 3)
    (b:B) :
    reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,l⟩) (encodedActivePoolEquiv I Q Q0 B l b)=l b := by
  change reflectionSixLabel (encodeReflectionSix ⟨B,l⟩ b.val)=l b
  apply Fin.ext
  simp only [encodeReflectionSix,dif_pos b.property,reflectionSixLabel]
  change (3+(l b).val)%3=(l b).val
  have hlt:=(l b).isLt
  omega

lemma encodedActivePoolEquiv_divisor (I F Q Q0:Ideal O)
    (B:Finset (pool I Q Q0)) (l:B → Fin 3) (side:Fin 3) :
    reflectionExtractedDivisor
      (fun P:reflectionActivePool I Q Q0 (encodeReflectionSix ⟨B,l⟩)=>P.val)
      (fun P=>completedLocalExponent I F P.val)
      (reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,l⟩)) side=
    reflectionExtractedDivisor (fun b:B=>b.val.val)
      (fun b=>completedLocalExponent I F b.val.val) l side := by
  unfold reflectionExtractedDivisor
  symm
  apply Fintype.prod_equiv (encodedActivePoolEquiv I Q Q0 B l)
  intro b
  rw [encodedActivePoolEquiv_label]
  rfl


end CompletedGauss.FreeReflection

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

lemma reflectionExtractedDivisor_congrEquiv {α β : Type*} [Fintype α] [Fintype β]
    (P : α→Ideal O) (R : β→Ideal O) (E : α≃β) (hP : ∀i,P i=R (E i))
    (j : α→ℕ) (l : β→ℕ) (hj : ∀i,j i=l (E i))
    (e : α→Fin 3) (f : β→Fin 3) (he : ∀i,e i=f (E i)) (v : Fin 3) :
    reflectionExtractedDivisor P j e v=reflectionExtractedDivisor R l f v := by
  unfold reflectionExtractedDivisor
  rw [←E.prod_comp]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hP,hj,he]

lemma reflectedBranch_congrEquiv {α β : Type*} [Fintype α] [Fintype β]
    (P : α→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (R : β→Ideal O) [∀i,(R i).IsMaximal] (hR : ∀i,lambda∉R i)
    (E : α≃β) (hP : ∀i,P i=R (E i))
    (j : α→ℕ) (l : β→ℕ) (hj : ∀i,j i=l (E i))
    (e : α→Fin 3) (f : β→Fin 3) (he : ∀i,e i=f (E i)) (n b : O) :
    reflectedBranch P hg j e n b=reflectedBranch R hR l f n b := by
  unfold reflectedBranch
  rw [←E.prod_comp]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hj,he]
  exact reflectedLocalPiece_ideal_congr _ _ _ _ (hP i) _ _ _ _

/-- Relabeling the active primes preserves the full extracted cusp series. -/
theorem canonicalCuspRawValue_congrEquiv {α β : Type*} [Fintype α] [Fintype β]
    (P : α→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (R : β→Ideal O) [∀i,(R i).IsMaximal] (hR : ∀i,lambda∉R i)
    (E : α≃β) (hP : ∀i,P i=R (E i))
    (j : α→ℕ) (l : β→ℕ) (hj : ∀i,j i=l (E i))
    (e : α→Fin 3) (f : β→Fin 3) (he : ∀i,e i=f (E i))
    (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (σ : ℕ→ℂ) (k : Ideal O) (V : ℝ→ℂ) (scale : ℝ) :
    canonicalCuspRawValue P hg j e N c s b u σ k V scale=
      canonicalCuspRawValue R hR l f N c s b u σ k V scale := by
  have hd:=reflectionExtractedDivisor_congrEquiv P R E hP j l hj e f he
  simp only [canonicalCuspRawValue,hd]
  apply tsum_congr
  intro x
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient,reflectedDyadicCoefficient,hd,
    reflectedBranch_congrEquiv P hg R hR E hP j l hj e f he]

end CompletedGauss

namespace CompletedGauss.FreeReflection
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion
open scoped BigOperators Classical ContDiff

/-- Bounded coefficients on a row fiber extend to all residual quadratic rows. -/
def fixedCuspFiberFromRows (c : O) (hc : c≠0) (rows : Finset (Ideal O))
    (I F Q Q0 : Ideal O) (hI : I≠0) (hQ : Q≠0) (K : ℝ)
    (scalar : (FixedCuspBranchIndex c I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar : ∀a J,‖scalar a J‖≤1) :
    ReflectedFiberData (fixedCuspRayCount c hc) (fixedCuspLevelBound c hc) K I F Q :=
  fixedCuspFiber c hc I F Q Q0 hI hQ K (fun _=>1) (by intro x; simp only [norm_one,le_refl])
    (fun x m=>extendFiberRowScalar rows I Q K scalar (x,m))
    (fun x m=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar (x,m))

/-- The dyadic family evaluates to the convergent cusp kernel series on its residual shell. -/
theorem sixFixedCuspBranch_value (c : O) (hc : c≠0) (I F Q Q0 : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (K : ℝ) (r : FixedCuspRay c) (e : pool I Q Q0→Fin 6)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hσ : ∀m k,‖σ m k‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X)
    (hK : 0<completedResidualScale K I Q) (k : idealRange (completedResidualScale K I Q))
    (hk : completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    let d:=sixReflectedBranch I F Q Q0 hI hQ K (fixedCuspLevelBound c hc) (fixedCuspRayLevel c r)
      (fixedCuspRayLevel_pos c hc r) (fixedCuspRayLevel_le c hc r) e
      (fun _ _ _=>0) (by intro m n b; simp only [norm_zero,zero_le_one]) σ hσ
    (sixFixedCuspBranch c hc I F Q Q0 hI hQ K r e σ hσ).value W X 1 completedRamifiedStep k=
      d.rawValue (d.cuspAmplitude (243*c) r.2.1.val r.2.2.1 r.2.2.2.1 r.2.2.2.2)
        σ W X 1 completedRamifiedStep k := by
  dsimp only
  let d:=sixReflectedBranch I F Q Q0 hI hQ K (fixedCuspLevelBound c hc) (fixedCuspRayLevel c r)
    (fixedCuspRayLevel_pos c hc r) (fixedCuspRayLevel_le c hc r) e
    (fun _ _ _=>0) (by intro m n b; simp only [norm_zero,zero_le_one]) σ hσ
  exact d.withCanonicalCuspArray_value
    (d.cuspAmplitude (243*c) r.2.1.val r.2.2.1 r.2.2.2.1 r.2.2.2.2)
    (fun m n v=>d.cuspAmplitude_norm (243*c) r.2.1.val r.2.2.1 r.2.2.2.1 r.2.2.2.2 m n.val v.val)
    σ hσ W a b ha hs hW X 1 completedRamifiedStep hX zero_lt_one completedRamifiedStep_gt_one hK k hk

theorem fixedCuspFiberFromRows_value (c : O) (hc : c≠0) (rows : Finset (Ideal O))
    (I F Q Q0 : Ideal O) (hI : I≠0) (hQ : Q≠0) (K : ℝ)
    (scalar : (FixedCuspBranchIndex c I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar : ∀a J,‖scalar a J‖≤1)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) :
    letI : Fintype (FixedCuspRay c):=fixedCuspRayFintype c hc
    (fixedCuspFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).value W X ρ q k=
      ∑r : FixedCuspRay c,∑A : Finset (pool I Q Q0),∑e : A→Fin 3,
        reflectionInactiveStratumWeight I F Q Q0 A*
          (sixFixedCuspBranch c hc I F Q Q0 hI hQ K r (encodeReflectionSix ⟨A,e⟩)
            (fun m=>extendFiberRowScalar rows I Q K scalar ((r,encodeReflectionSix ⟨A,e⟩),m))
            (fun m=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar
              ((r,encodeReflectionSix ⟨A,e⟩),m))).value W X ρ q k := by
  letI : Fintype (FixedCuspRay c):=fixedCuspRayFintype c hc
  rw [fixedCuspFiberFromRows,fixedCuspFiber_value]
  simp only [mul_one]

end CompletedGauss.FreeReflection

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion
open scoped BigOperators Classical

lemma completedBranchScale_congrEquiv {α β : Type*} [Fintype α] [Fintype β]
    (K X : ℝ) (I F Q : Ideal O) (P : α→ Ideal O) (R : β→ Ideal O)
    (E : α≃β) (hP : ∀i,P i=R (E i))
    (e : α→ Fin 3) (f : β→ Fin 3) (he : ∀i,e i=f (E i)) :
    completedBranchScale K X I F Q P e=completedBranchScale K X I F Q R f := by
  have hd:=reflectionExtractedDivisor_congrEquiv P R E hP
    (fun i=>completedLocalExponent I F (P i)) (fun i=>completedLocalExponent I F (R i))
    (fun i=>congrArg (completedLocalExponent I F) (hP i)) e f he
  have hp : (∏i,P i)=∏i,R i := by
    rw [←E.prod_comp]
    exact Finset.prod_congr rfl (fun i _=>hP i)
  simp only [completedBranchScale,hd,hp]

namespace FreeReflection

/-- Encoding a local branch preserves its scale and extracted cusp series. -/
theorem canonicalCuspRawValue_encoded (I F Q Q0 : Ideal O)
    (B : Finset (pool I Q Q0)) (e : B→ Fin 3)
    (N c : O) (s : FixedCuspSector) (b : O⧸Ideal.span {N}) (u : Oˣ)
    (σ : ℕ→ ℂ) (k : Ideal O) (V : ℝ→ ℂ) (K X : ℝ) :
    let A:=reflectionActivePool I Q Q0 (encodeReflectionSix ⟨B,e⟩)
    letI : ∀P : B,P.val.val.IsMaximal:=fun P=>pool_maximal I Q Q0 P.val
    letI : ∀P : A,P.val.IsMaximal:=fun P=>pool_maximal I Q Q0
      ⟨P.val,reflectionActivePool_subset I Q Q0 _ P.property⟩
    canonicalCuspRawValue (fun P : B=>P.val.val)
      (fun P=>pool_good I Q Q0 P.val) (fun P=>completedLocalExponent I F P.val.val) e
      N c s b u σ k V
      ((completedBranchScale K X I F Q (fun P : B=>P.val.val) e)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k:ℝ))^2)=
    canonicalCuspRawValue (fun P : A=>P.val)
      (fun P=>pool_good I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 _ P.property⟩)
      (fun P=>completedLocalExponent I F P.val)
      (reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,e⟩)) N c s b u σ k V
      ((completedBranchScale K X I F Q (fun P : A=>P.val)
        (reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,e⟩)))⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k:ℝ))^2) := by
  dsimp only
  let A:=reflectionActivePool I Q Q0 (encodeReflectionSix ⟨B,e⟩)
  letI : ∀P : B,P.val.val.IsMaximal:=fun P=>pool_maximal I Q Q0 P.val
  letI : ∀P : A,P.val.IsMaximal:=fun P=>pool_maximal I Q Q0
    ⟨P.val,reflectionActivePool_subset I Q Q0 _ P.property⟩
  let E:=encodedActivePoolEquiv I Q Q0 B e
  have hlabel (P : B) : e P=reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,e⟩) (E P) :=
    (encodedActivePoolEquiv_label I Q Q0 B e P).symm
  have hscale:=completedBranchScale_congrEquiv K X I F Q (fun P : B=>P.val.val)
    (fun P : A=>P.val) E (fun _=>rfl) e
    (reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,e⟩)) hlabel
  refine (congrArg
    (fun scale : ℝ=>canonicalCuspRawValue (fun P : B=>P.val.val)
      (fun P=>pool_good I Q Q0 P.val) (fun P=>completedLocalExponent I F P.val.val) e
      N c s b u σ k V (scale⁻¹*(completedResidualScale K I Q/(Ideal.absNorm k:ℝ))^2))
    hscale).trans ?_
  exact canonicalCuspRawValue_congrEquiv
    (fun P : B=>P.val.val) (fun P=>pool_good I Q Q0 P.val)
    (fun P : A=>P.val)
    (fun P=>pool_good I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 _ P.property⟩)
    E (fun _=>rfl) (fun P : B=>completedLocalExponent I F P.val.val)
    (fun P : A=>completedLocalExponent I F P.val) (fun _=>rfl)
    e (reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,e⟩)) hlabel N c s b u σ k V
    ((completedBranchScale K X I F Q (fun P : A=>P.val)
      (reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,e⟩)))⁻¹*
      (completedResidualScale K I Q/(Ideal.absNorm k:ℝ))^2)

end FreeReflection
end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

/-- Summing all fixed cusp rays selects the denominator, sector, and residue of each row. -/
theorem sum_selected_cusp_rays {H D S B U : Type*}
    [Fintype H] [Fintype D] [Fintype S] [Fintype B] [Fintype U]
    (choose : H→D×S×B) (f : H×D×S×B×U→ℂ) :
    (∑r : H×D×S×B×U,
      if r.2.1=(choose r.1).1 ∧ r.2.2.1=(choose r.1).2.1 ∧ r.2.2.2.1=(choose r.1).2.2
        then f r else 0)=
      ∑h : H,∑u : U,f (h,(choose h).1,(choose h).2.1,(choose h).2.2,u) := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_eq_single (choose h).1]
  · rw [Finset.sum_eq_single (choose h).2.1]
    · rw [Finset.sum_eq_single (choose h).2.2]
      · simp
      · intro b hb hne
        simp [hne]
      · simp
    · intro s hs hne
      simp [hne]
    · simp
  · intro d hd hne
    simp [hne]
  · simp

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion
open scoped BigOperators Classical

lemma representativeFiber_parts (rows : Finset (Ideal O)) (I Q : Ideal O)
    (J : representativeRowFiber rows I Q) :
    rowPowerfulPart J.val=rowPowerfulPart I ∧ rowMaskPart J.val Q=rowMaskPart I Q :=
  (Finset.mem_filter.mp J.property).2

lemma representativeFiber_residualScale (rows : Finset (Ideal O)) (I Q : Ideal O)
    (J : representativeRowFiber rows I Q) (K : ℝ) :
    completedResidualScale K J.val Q=completedResidualScale K I Q := by
  have hs:=representativeFiber_parts rows I Q J
  exact completedResidualScale_eq_on_fiber K J.val I Q hs.1 hs.2

/-- Fixing the powerful and mask parts carries an ideal norm shell to its residual shell. -/
theorem representativeFiber_residual_shell (rows : Finset (Ideal O)) (I Q : Ideal O) (K : ℝ)
    (hrows : ∀J∈rows,J≠0 ∧ K/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤K)
    (J : representativeRowFiber rows I Q) :
    0<completedResidualScale K I Q ∧
      completedResidualScale K I Q/2≤(Ideal.absNorm (rowResidualPart J.val Q):ℝ) := by
  have hJ:=hrows J.val (Finset.mem_filter.mp J.property).1
  rw [←representativeFiber_residualScale rows I Q J K]
  refine ⟨lt_of_lt_of_le zero_lt_one (one_le_completedResidualScale K J.val Q hJ.1 hJ.2.2),?_⟩
  rw [rowResidualPart_norm J.val Q hJ.1,completedResidualScale]
  have hlo:=div_le_div_of_nonneg_right hJ.2.1
    (show 0≤(Ideal.absNorm (rowPowerfulPart J.val):ℝ)*(Ideal.absNorm (rowMaskPart J.val Q):ℝ) by positivity)
  calc
    _=(K/2)/((Ideal.absNorm (rowPowerfulPart J.val):ℝ)*
        (Ideal.absNorm (rowMaskPart J.val Q):ℝ)) := by ring
    _≤_:=hlo

end CompletedGauss

namespace CompletedGauss.FreeReflection
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion
open scoped BigOperators Classical ContDiff

/-- The selected fixed ray has the extended coefficient of the original row family. -/
lemma fixedCuspFiberFromRows_branch (c : O) (hc : c≠0) (rows : Finset (Ideal O))
    (I F Q Q0 : Ideal O) (hI : I≠0) (hQ : Q≠0) (K : ℝ)
    (scalar : (FixedCuspBranchIndex c I Q Q0×ℕ) → representativeRowFiber rows I Q → ℂ)
    (hscalar : ∀a J,‖scalar a J‖≤1) (r : FixedCuspRay c) (e : pool I Q Q0 → Fin 6) :
    (fixedCuspFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).branch
      (fixedCuspRayEquiv c hc r,e)=
      sixFixedCuspBranch c hc I F Q Q0 hI hQ K r e
        (fun n=>extendFiberRowScalar rows I Q K scalar ((r,e),n))
        (fun n=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar ((r,e),n)) :=
  fixedCuspFiber_branch c hc I F Q Q0 hI hQ K (fun _=>1)
    (by intro x; simp only [norm_one,le_refl])
    (fun x n=>extendFiberRowScalar rows I Q K scalar (x,n))
    (fun x n=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar (x,n)) r e

/-- The finite fiber value is the weighted sum of its decoded branches. -/
theorem fixedCuspFiberFromRows_branch_sum (c : O) (hc : c≠0) (rows : Finset (Ideal O))
    (I F Q Q0 : Ideal O) (hI : I≠0) (hQ : Q≠0) (K : ℝ)
    (scalar : (FixedCuspBranchIndex c I Q Q0×ℕ) → representativeRowFiber rows I Q → ℂ)
    (hscalar : ∀a J,‖scalar a J‖≤1) (W : ℝ → ℂ) (X ρ q : ℝ)
    (k : idealRange (completedResidualScale K I Q)) :
    letI : Fintype (FixedCuspRay c):=fixedCuspRayFintype c hc
    let d:=fixedCuspFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar
    d.value W X ρ q k=
      ∑r : FixedCuspRay c,∑B : Finset (pool I Q Q0),
        reflectionInactiveStratumWeight I F Q Q0 B*∑e : B → Fin 3,
          (d.branch (fixedCuspRayEquiv c hc r,encodeReflectionSix ⟨B,e⟩)).value W X ρ q k := by
  letI : Fintype (FixedCuspRay c):=fixedCuspRayFintype c hc
  dsimp only
  rw [fixedCuspFiberFromRows_value]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro B hB
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [fixedCuspFiberFromRows_branch]
  rfl

/-- On an original row, the reflected branch has exactly that row's coefficient. -/
theorem fixedCuspFiberFromRows_branch_value (c : O) (hc : c≠0) (rows : Finset (Ideal O))
    (I F Q Q0 : Ideal O) (hI : I≠0) (hQ : Q≠0) (K : ℝ)
    (scalar : (FixedCuspBranchIndex c I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar : ∀a J,‖scalar a J‖≤1)
    (hbad : ∀P∈fixedBadPrimes,P∣Q)
    (hrows : ∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (J : representativeRowFiber rows I Q) (r : FixedCuspRay c) (e : pool I Q Q0→Fin 6)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X)
    (hK : 0<completedResidualScale K I Q)
    (hk : completedResidualScale K I Q/2≤(Ideal.absNorm (rowResidualPart J.val Q):ℝ)) :
    let σ:=fun m=>extendFiberRowScalar rows I Q K scalar ((r,e),m)
    let hσ:=fun m=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar ((r,e),m)
    let d:=sixReflectedBranch I F Q Q0 hI hQ K (fixedCuspLevelBound c hc) (fixedCuspRayLevel c r)
      (fixedCuspRayLevel_pos c hc r) (fixedCuspRayLevel_le c hc r) e
      (fun _ _ _=>0) (by intro m n b; simp only [norm_zero,zero_le_one]) σ hσ
    let k:=fiberResidualIndex rows I Q K hbad hrows J
    ((fixedCuspFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).branch
      (fixedCuspRayEquiv c hc r,e)).value W X 1 completedRamifiedStep k=
      d.rawValue (d.cuspAmplitude (243*c) r.2.1.val r.2.2.1 r.2.2.2.1 r.2.2.2.2)
        (fun m _=>scalar ((r,e),m) J) W X 1 completedRamifiedStep k := by
  dsimp only
  let σ : ℕ → idealRange (completedResidualScale K I Q) → ℂ :=
    fun n=>extendFiberRowScalar rows I Q K scalar ((r,e),n)
  let hσ : ∀n k,‖σ n k‖≤1 :=
    fun n=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar ((r,e),n)
  let k:=fiberResidualIndex rows I Q K hbad hrows J
  let d:=sixReflectedBranch I F Q Q0 hI hQ K (fixedCuspLevelBound c hc) (fixedCuspRayLevel c r)
    (fixedCuspRayLevel_pos c hc r) (fixedCuspRayLevel_le c hc r) e
    (fun _ _ _=>0) (by intro n v b; simp only [norm_zero,zero_le_one]) σ hσ
  have hb:=congrArg
    (fun b : ReflectedBranchData (fixedCuspLevelBound c hc) K I F Q =>
      b.value W X 1 completedRamifiedStep k)
    (fixedCuspFiberFromRows_branch c hc rows I F Q Q0 hI hQ K scalar hscalar r e)
  refine hb.trans ((sixFixedCuspBranch_value c hc I F Q Q0 hI hQ K r e σ hσ
    W a b ha hs hW X hX hK k hk).trans ?_)
  exact d.rawValue_congr_phase_at
    (d.cuspAmplitude (243*c) r.2.1.val r.2.2.1 r.2.2.2.1 r.2.2.2.2)
    σ (fun n _=>scalar ((r,e),n) J) W X 1 completedRamifiedStep k
    (fun n=>extendFiberRowScalar_at_original rows I Q K hbad hrows scalar ((r,e),n) J)

end CompletedGauss.FreeReflection

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical

/-- The active cusp stratum after the zero Fourier coefficients have been separated. -/
def cuspStratumValue {ι : Type*} [Fintype ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (j : ι→ℕ) (N c : O) (s : Finset ι→FixedCuspSector)
    (b : Finset ι→O⧸Ideal.span {N}) (phase : Finset ι→ℂ)
    (V : ℝ→ℂ) (X : ℝ) (A : Finset ι) : ℂ :=
  phase A*fixedCuspDivisorSeries (fun P : A=>p P.val) (fun P=>hg P.val)
    N c (s A) (b A) (fun P=>j P.val) V X

end CompletedGauss

namespace CompletedGauss.FreeReflection
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion
open scoped BigOperators Classical ContDiff

/-- The row scalar absorbs the Fourier, ramified, and extracted-divisor phases. -/
def cuspRowScalar (I F Q Q0 : Ideal O) (e : pool I Q Q0→ Fin 6)
    (α τ : ℂ) (k : Ideal O) : ℂ :=
  let P:=reflectionActivePool I Q Q0 e
  α*τ*residualArgumentPhase k
    (reflectionExtractedDivisor (fun p : P=>p.val) (fun p=>completedLocalExponent I F p.val)
      (reflectionActiveLabel I Q Q0 e) 1)
    (reflectionExtractedDivisor (fun p : P=>p.val) (fun p=>completedLocalExponent I F p.val)
      (reflectionActiveLabel I Q Q0 e) 2)

lemma cuspRowScalar_norm (I F Q Q0 : Ideal O) (e : pool I Q Q0→ Fin 6)
    (α τ : ℂ) (k : Ideal O) (hα : ‖α‖≤ 1) (hτ : ‖τ‖≤ 1) :
    ‖cuspRowScalar I F Q Q0 e α τ k‖≤ 1 := by
  simp only [cuspRowScalar,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) hα).trans hτ)).trans
    (residualArgumentPhase_norm_le_one _ _ _)

/-- The extended row scalar recovers the exact cusp branch on the original ideal row. -/
theorem fixedCuspFiberFromRows_branch_cusp_value (c : O) (hc : c≠0) (rows : Finset (Ideal O))
    (I F Q Q0 : Ideal O) (hI : I≠0) (hQ : Q≠0) (K : ℝ)
    (scalar : (FixedCuspBranchIndex c I Q Q0×ℕ)→  representativeRowFiber rows I Q→ ℂ)
    (hscalar : ∀a J,‖scalar a J‖≤ 1)
    (hbad : ∀P∈fixedBadPrimes,P∣Q)
    (hrows : ∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤ K)
    (J : representativeRowFiber rows I Q) (r : FixedCuspRay c) (e : pool I Q Q0→ Fin 6)
    (α : ℂ) (τ : ℕ→ ℂ)
    (hrow : ∀n,scalar ((r,e),n) J=
      cuspRowScalar I F Q Q0 e α (τ n) (rowResidualPart J.val Q))
    (W : ℝ→ ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X)
    (hK : 0<completedResidualScale K I Q)
    (hk : completedResidualScale K I Q/2≤ (Ideal.absNorm (rowResidualPart J.val Q):ℝ)) :
    let P:=reflectionActivePool I Q Q0 e
    letI : ∀p : P,p.val.IsMaximal:=fun p=>pool_maximal I Q Q0
      ⟨p.val,reflectionActivePool_subset I Q Q0 e p.property⟩
    let k:=fiberResidualIndex rows I Q K hbad hrows J
    ((fixedCuspFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).branch
      (fixedCuspRayEquiv c hc r,e)).value W X 1 completedRamifiedStep k=
    α*canonicalCuspRawValue (fun p : P=>p.val)
      (fun p=>pool_good I Q Q0 ⟨p.val,reflectionActivePool_subset I Q Q0 e p.property⟩)
      (fun p=>completedLocalExponent I F p.val) (reflectionActiveLabel I Q Q0 e)
      (243*c) r.2.1.val r.2.2.1 r.2.2.2.1 r.2.2.2.2 τ (rowResidualPart J.val Q) (Vstar W)
      ((completedBranchScale K (X/fixedCuspRayLevel c r) I F Q (fun p : P=>p.val)
        (reflectionActiveLabel I Q Q0 e))⁻¹*
          (completedResidualScale K I Q/(Ideal.absNorm (rowResidualPart J.val Q):ℝ))^2) := by
  dsimp only
  let P:=reflectionActivePool I Q Q0 e
  letI : ∀p : P,p.val.IsMaximal:=fun p=>pool_maximal I Q Q0
    ⟨p.val,reflectionActivePool_subset I Q Q0 e p.property⟩
  rw [fixedCuspFiberFromRows_branch_value c hc rows I F Q Q0 hI hQ K scalar hscalar
    hbad hrows J r e W a b ha hs hW X hX hK hk]
  simp_rw [hrow]
  change canonicalCuspRawValue _ _ _ _ _ _ _ _ _ (fun n=>α*τ n) _ _ _=_
  exact canonicalCuspRawValue_mul_phase _ _ _ _ _ _ _ _ _ τ _ _ _ α

end CompletedGauss.FreeReflection

namespace CompletedGauss
open scoped BigOperators Classical

/-- Finite ray selectors collect the active local branches of one original row. -/
theorem finite_selected_cusp_branch_collection {H D S B U A : Type*} {E : A→Type*}
    [Fintype H] [Fintype D] [Fintype S] [Fintype B] [Fintype U] [Fintype A]
    [∀a,Fintype (E a)] [rays : Fintype (H×D×S×B×U)]
    (f : H×D×S×B×U→(a : A)→E a→ℂ)
    (g : H→U→(a : A)→E a→ℂ) (chosen : H→A→D×S×B) (w : A→ℂ)
    (hf : ∀r a e,f r a e=
      if r.2.1=(chosen r.1 a).1 ∧ r.2.2.1=(chosen r.1 a).2.1 ∧
          r.2.2.2.1=(chosen r.1 a).2.2 then g r.1 r.2.2.2.2 a e else 0) :
    (∑r : H×D×S×B×U,∑a,w a*∑e,f r a e)=
      ∑h : H,∑a,w a*∑u : U,∑e,g h u a e := by
  have hi : rays = @instFintypeProd H (D×S×B×U) inferInstance inferInstance:=Subsingleton.elim _ _
  cases hi
  have hp (a : A) (e : E a) :
      (∑r : H×D×S×B×U,f r a e)=∑h : H,∑u : U,g h u a e := by
    simp_rw [hf]
    exact sum_selected_cusp_rays (fun h=>chosen h a) (fun r=>g r.1 r.2.2.2.2 a e)
  calc
    _=∑a,w a*∑e,∑r : H×D×S×B×U,f r a e := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [←Finset.mul_sum,Finset.sum_comm]
    _=∑a,w a*∑h : H,∑u : U,∑e,g h u a e := by
      simp_rw [hp]
      apply Finset.sum_congr rfl
      intro a ha
      apply congrArg (fun z : ℂ=>w a*z)
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      exact Finset.sum_comm
    _=_ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]

end CompletedGauss

open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion SecondPassArithmetic
open SchwartzPlanePoisson.CanonicalQuadraticSieve
open scoped BigOperators Classical

/-- The short cube range fits inside the completed scale under the rank margin. -/
theorem short_cube_scale_algebra (z K R X F h : ℝ)
    (hz : 1≤z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F) (hFz : F≤z)
    (hh : 1≤h) (hhz : h≤z) (hmargin : K*R*z^25≤X*F) :
    1≤X/h^3 ∧ K^2*R*F*h^3/X≤K := by
  have hz0 : 0<z := by linarith
  have hF0 : 0<F := by linarith
  have hh0 : 0<h := by linarith
  have hKR : 1≤K*R := by nlinarith
  have hp4 : z^4≤z^25 := pow_le_pow_right₀ hz (by norm_num)
  have hp5 : z^5≤z^25 := pow_le_pow_right₀ hz (by norm_num)
  have hsmall : h^3*F≤z^25 := by
    calc
      _ ≤ z^3*z := by gcongr
      _ = z^4 := by ring
      _ ≤ _ := hp4
  have hcube : h^3≤X := by
    have h1 : h^3*F≤X*F := hsmall.trans ((le_mul_of_one_le_left (by positivity) hKR).trans hmargin)
    exact (mul_le_mul_iff_left₀ hF0).mp (by simpa only [mul_comm F] using h1)
  have hX : 0<X := (pow_pos hh0 3).trans_le hcube
  refine ⟨(le_div_iff₀ (pow_pos hh0 3)).mpr (by simpa using hcube),?_⟩
  have hfh : F^2*h^3≤z^25 := by
    calc
      _ ≤ z^2*z^3 := by gcongr
      _ = z^5 := by ring
      _ ≤ _ := hp5
  have hprod : K*R*F*h^3≤X := by
    have hn : K*R*(F^2*h^3)≤X*F :=
      (mul_le_mul_of_nonneg_left hfh (by positivity)).trans hmargin
    apply (mul_le_mul_iff_right₀ hF0).mp
    nlinarith
  apply (div_le_iff₀ hX).mpr
  nlinarith [mul_le_mul_of_nonneg_left hprod (show 0≤K by linarith)]

theorem short_cube_scales (Z K R X F h : ℝ)
    (hZ : 1≤Z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F)
    (hFZ : F≤Z^(1/1000:ℝ)) (hh : 1≤h) (hhZ : h≤Z^(1/1000:ℝ))
    (hmargin : K*R≤X*F*Z^(-(1/40:ℝ))) :
    1≤X/h^3 ∧ K^2*R*F*h^3/X≤K := by
  have hZ0 : 0<Z := by linarith
  have hz : 1≤Z^(1/1000:ℝ) := Real.one_le_rpow hZ (by norm_num)
  have he : (Z^(1/1000:ℝ))^25=Z^(1/40:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ0.le]
    norm_num
  apply short_cube_scale_algebra _ K R X F h hz hK hR hF hFZ hh hhZ
  rw [he]
  have hm := mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg hZ0.le (1/40:ℝ))
  have hp : Z^(-(1/40:ℝ))*Z^(1/40:ℝ)=1 := by
    rw [←Real.rpow_add hZ0]
    norm_num
  calc
    _ ≤ X*F*Z^(-(1/40:ℝ))*Z^(1/40:ℝ) := hm
    _ = X*F := by rw [mul_assoc (X*F),hp,mul_one]

end CompletedGauss

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace NormalizedReflection
variable {F : Type*} [Field F] [Fintype F]

def unitArgumentFactor (χ : MulChar F ℂ) (j : ℕ) (z : F) : ℂ :=
  if j=4 then 1 else (χ^(j+2))⁻¹ z

theorem bracket_mul_unit (χ : MulChar F ℂ) (j : ℕ) (z x : F) (hz : z≠0) :
    bracket χ j (z*x)=unitArgumentFactor χ j z*bracket χ j x := by
  by_cases hj4 : j=4
  · simp [unitArgumentFactor,bracket,hj4,hz]
  · by_cases hj0 : j=0
    · subst j
      simp only [unitArgumentFactor,bracket,show (0:ℕ)≠4 by decide,ite_false,ite_true,
        zero_add,map_mul]
      ring
    · simp only [unitArgumentFactor,bracket,if_neg hj4,if_neg hj0,map_mul]

theorem unitArgumentFactor_norm (χ : MulChar F ℂ) (j : ℕ) (z : F) (hz : z≠0) :
    ‖unitArgumentFactor χ j z‖=1 := by
  by_cases hj : j=4
  · simp [unitArgumentFactor,hj]
  · rw [unitArgumentFactor,if_neg hj]
    exact finiteMulChar_unit_norm ((χ^(j+2))⁻¹) (Units.mk0 z hz)

end NormalizedReflection
namespace CompletedGauss
open Eisenstein NormalizedReflection

theorem unit_ramified_quotient_ne_zero (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (u : Oˣ) (m : ℕ) :
    Ideal.Quotient.mk P ((u:O)*lambda^m)≠0 := by
  rw [map_mul,map_pow]
  apply mul_ne_zero
  · exact (u.isUnit.map (Ideal.Quotient.mk P)).ne_zero
  · exact pow_ne_zero _ (fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h))

def ramifiedBranchPhase {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (u : Oˣ) (m : ℕ) : ℂ :=
  ∏i,unitArgumentFactor (complexSexticChar (P i) (hg i)) (j i)
    (Ideal.Quotient.mk (P i) ((u:O)*lambda^m))

theorem ramifiedBranchPhase_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (u : Oˣ) (m : ℕ) : ‖ramifiedBranchPhase P hg j u m‖=1 := by
  rw [ramifiedBranchPhase,norm_prod]
  have hh (i : ι) := unitArgumentFactor_norm (complexSexticChar (P i) (hg i)) (j i)
    _ (unit_ramified_quotient_ne_zero (P i) (hg i) u m)
  simp only [hh,Finset.prod_const_one]

theorem ramified_bracket_full_expansion {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (u : Oˣ) (m : ℕ) (n b : O) :
    (∏i,bracket (complexSexticChar (P i) (hg i)) (j i)
      (Ideal.Quotient.mk (P i) ((u:O)*lambda^m*(n*b^3))))=
      ramifiedBranchPhase P hg j u m*∑e : ι→Fin 3,reflectedBranch P hg j e n b := by
  have hl (i : ι) : bracket (complexSexticChar (P i) (hg i)) (j i)
      (Ideal.Quotient.mk (P i) ((u:O)*lambda^m*(n*b^3)))=
      unitArgumentFactor (complexSexticChar (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) ((u:O)*lambda^m))*
      bracket (complexSexticChar (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (n*b^3)) := by
    rw [map_mul]
    exact bracket_mul_unit _ _ _ _ (unit_ramified_quotient_ne_zero (P i) (hg i) u m)
  simp_rw [hl]
  rw [Finset.prod_mul_distrib,prod_bracket_eq_full_branches P hg j n b]
  rfl

end CompletedGauss

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
