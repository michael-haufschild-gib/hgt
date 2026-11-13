/-
Reopened canonical rows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.CanonicalDualZeroModes
import GaloisForLFunctions.MetaplecticMobiusDescent.GaussSums.RayExpansionsAndCompletedSums

/-!
# Reopened canonical rows

Reopened canonical rows and their smoothed sources. Coefficient mass at most one gives convex
quadratic bounds; residue sectors are convex sums of multiplicative twists; the canonical
density constant and the first quantitative budget.
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

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open scoped Classical
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

theorem fixedChildRow_residue_expansion
    (hc : ∀i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (pool : Finset ι) (Ψ : O →* ℂ) (m f y : O)
    (r : QuadraticRayRing) (H : Finset ι → ℂ) :
    fixedChildRow p hg pool Ψ m (firstResidueMask p r H) f y =
      ∑χ : RayCharacter,residueCoeff r χ*fixedChildRow p hg pool (Ψ*rayMonoid χ) m H f y := by
  unfold fixedChildRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hr := residue_expansion r (∏i∈S,p i) (prime_product_unit_mod_four p hc S)
  have hmask : firstResidueMask p r H S =
      (∑χ : RayCharacter,residueCoeff r χ*rayMonoid χ (∏i∈S,p i))*H S := by
    rw [←hr]
    unfold firstResidueMask
    split_ifs <;> simp only [one_mul,zero_mul]
  simp only [secondChildColumn,hmask,MonoidHom.mul_apply,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ _
  ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open scoped Classical

/-- An absolute coefficient mass at most one gives a convex quadratic bound. -/
theorem norm_sq_sum_le_weighted {α : Type*} (S : Finset α) (c a : α → ℂ)
    (hc : (∑i∈S,‖c i‖)≤1) :
    ‖∑i∈S,c i*a i‖^2 ≤ ∑i∈S,‖c i‖*‖a i‖^2 := by
  have h := DescentWeightedCauchy.weighted_cauchy_sq S c a (fun _=>1)
  simp only [star_one,mul_one,norm_one,one_pow] at h
  exact h.trans (mul_le_of_le_one_right (Finset.sum_nonneg (fun i _=>by positivity)) hc)

theorem nonzeroRowMajorant_weighted_bound {α : Type*} (S : Finset α)
    (w : α → ℝ) (P : O → ℂ) (Q : α → O → ℂ) (K : ℝ) (hK : 0<K)
    (hpoint : ∀z,‖P z‖^2≤∑i∈S,w i*‖Q i z‖^2) :
    (nonzeroRowMajorantSum P K).re ≤ ∑i∈S,w i*(nonzeroRowMajorantSum (Q i) K).re := by
  simp_rw [nonzeroRowMajorantSum_exact_disk _ K hK,Complex.re_sum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  calc
    _ ≤ ∑z∈(firstFrequencyDisk (2*K)).erase 0,
        (rowMajorant (‖ringComplex z‖^2/K)).re*(∑i∈S,w i*‖Q i z‖^2) :=
      Finset.sum_le_sum (fun z _=>mul_le_mul_of_nonneg_left (hpoint z) (rowMajorant_nonneg _))
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro z hz
      ring

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

/-- A fixed residue sector is bounded by a convex sum of multiplicative twists. -/
theorem canonicalSmoothedEnergy_residue_bound
    (hc : ∀i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (labels : Finset (Ideal O))
    (r : QuadraticRayRing) (H : Finset ι → ℂ) (K : ℝ) (hK : 0<K) :
    canonicalSmoothedEnergy p hg pool Ψ m labels (firstResidueMask p r H) K ≤
      ∑χ : RayCharacter,‖residueCoeff r χ‖*
        canonicalSmoothedEnergy p hg pool (Ψ*rayMonoid χ) m labels H K := by
  unfold canonicalSmoothedEnergy
  simp only [Complex.re_sum]
  calc
    _ ≤ ∑I∈labels,∑χ : RayCharacter,‖residueCoeff r χ‖*
        (nonzeroRowMajorantSum (fixedChildRow p hg pool (Ψ*rayMonoid χ) m H (cubicIdealGenerator I)) K).re := by
      apply Finset.sum_le_sum
      intro I hI
      apply nonzeroRowMajorant_weighted_bound Finset.univ (fun χ=>‖residueCoeff r χ‖) _ _ K hK
      intro z
      rw [fixedChildRow_residue_expansion p hg hc]
      exact norm_sq_sum_le_weighted Finset.univ _ _ (residueCoeff_sum_norm_le_one r)
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

theorem canonicalSmoothedEnergy_residue_uniform
    (hc : ∀i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (labels : Finset (Ideal O))
    (r : QuadraticRayRing) (H : Finset ι → ℂ) (K E : ℝ) (hK : 0<K) (hE : 0≤E)
    (hb : ∀χ : RayCharacter,canonicalSmoothedEnergy p hg pool (Ψ*rayMonoid χ) m labels H K≤E) :
    canonicalSmoothedEnergy p hg pool Ψ m labels (firstResidueMask p r H) K≤E := by
  apply (canonicalSmoothedEnergy_residue_bound p hg hc pool Ψ m labels r H K hK).trans
  calc
    _ ≤ ∑χ : RayCharacter,‖residueCoeff r χ‖*E :=
      Finset.sum_le_sum (fun χ _=>mul_le_mul_of_nonneg_left (hb χ) (norm_nonneg _))
    _ = (∑χ : RayCharacter,‖residueCoeff r χ‖)*E := (Finset.sum_mul _ _ _).symm
    _ ≤ E := mul_le_of_le_one_left hE (residueCoeff_sum_norm_le_one r)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open scoped Classical

lemma nonzeroRowMajorantSum_neg (P : O → ℂ) (K : ℝ) :
    nonzeroRowMajorantSum (fun z=>P (-z)) K=nonzeroRowMajorantSum P K := by
  simpa only [nonzeroRowMajorantSum,Equiv.neg_apply,neg_eq_zero,map_neg,norm_neg] using
    (Equiv.neg O).tsum_eq (fun z : O=>if z=0 then 0 else
      rowMajorant (‖ringComplex z‖^2/K)*(‖P z‖^2 : ℝ))

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

theorem fixedChildRow_residue_sign (pool : Finset ι) (Ψ : O →* ℂ) (m f y : O)
    (negative : Bool) (r : QuadraticRayRing) (H : Finset ι → ℂ) :
    fixedChildRow p hg pool Ψ m
      (firstResidueMask p r (fun S=>(if negative then
        primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S (-1) else 1)*H S)) f y =
      fixedChildRow p hg pool Ψ m (firstResidueMask p r H) f (if negative then -y else y) := by
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hr : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏i∈S,p i)=r
  · simp only [secondChildColumn,firstResidueMask,if_pos hr]
    cases negative
    · simp only [Bool.false_eq_true,ite_false,one_mul]
    · simp only [ite_true,show -y=(-1)*y by ring,subsetRow_mul]
      ring
  · simp only [secondChildColumn,firstResidueMask,if_neg hr,mul_zero]

/-- The combined phases preserve radial energy; incompatible residue sectors vanish. -/
theorem canonicalSmoothedEnergy_combined_eq
    (hc : ∀i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (labels : Finset (Ideal O))
    (negative : Bool) (r s : QuadraticRayRing) (H : Finset ι → ℂ) (K : ℝ) :
    canonicalSmoothedEnergy p hg pool Ψ m labels (combinedFixedColumn p hg negative r s H) K =
      if r=s then canonicalSmoothedEnergy p hg pool Ψ m labels (firstResidueMask p r H) K else 0 := by
  rw [combinedFixedColumn_eq_residue p hg hc]
  by_cases hrs : r=s
  · rw [if_pos hrs,if_pos hrs]
    unfold canonicalSmoothedEnergy
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    have hrow : fixedChildRow p hg pool Ψ m
        (firstResidueMask p r (fun S=>(if negative then
          primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S (-1) else 1)*H S))
        (cubicIdealGenerator I) =
        fun z=>fixedChildRow p hg pool Ψ m (firstResidueMask p r H)
          (cubicIdealGenerator I) (if negative then -z else z) := by
      funext z
      exact fixedChildRow_residue_sign p hg pool Ψ m _ z negative r H
    rw [hrow]
    cases negative
    · rfl
    · exact nonzeroRowMajorantSum_neg _ K
  · simp only [if_neg hrs,canonicalSmoothedEnergy,nonzeroRowMajorantSum,fixedChildRow,
      secondChildColumn,mul_zero,Finset.sum_const_zero,norm_zero,zero_pow (by decide : (2:ℕ)≠0),
      Complex.ofReal_zero,ite_self,tsum_zero,Complex.zero_re]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open scoped Classical
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

/-- A uniform bound over multiplicative twists also controls both residue phases. -/
theorem canonicalLogEnergy_combined_uniform
    (hc : ∀i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (labels : Finset (Ideal O))
    (negative : Bool) (r s : QuadraticRayRing) (H : Finset ι → ℂ)
    (V : ℝ → ℂ) (X K E : ℝ) (hK : 0<K) (hE : 0≤E)
    (hb : ∀χ : RayCharacter,canonicalLogEnergy p hg H pool (Ψ*rayMonoid χ) m labels V X K≤E) :
    canonicalLogEnergy p hg (combinedFixedColumn p hg negative r s H) pool Ψ m labels V X K≤E := by
  unfold canonicalLogEnergy
  rw [combinedFixedColumn_mul,canonicalSmoothedEnergy_combined_eq p hg hc]
  by_cases hrs : r=s
  · rw [if_pos hrs]
    exact canonicalSmoothedEnergy_residue_uniform p hg hc pool Ψ m labels r
      (fun S=>H S*V (columnLog p X S)) K E hK hE hb
  · rw [if_neg hrs]
    exact hE

end SecondPassArithmetic

open scoped Classical
open scoped Classical SchwartzMap

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap
private theorem finite_bounded_rows_smoothed_expand {β : Type*}
    (C : Finset β) (a : β→ℂ) (r : β→O→ℂ) (hr : ∀b∈C,∀z,‖r b z‖≤1)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑'z:O,W (‖ringComplex z‖^2/K)*(‖∑b∈C,a b*r b z‖^2:ℝ))=
      ∑b∈C,∑c∈C,(star (a b)*a c)*∑'z:O,(star (r b z)*r c z)*W (‖ringComplex z‖^2/K) := by
  have hs (b c : β) (hb:b∈C) (hc:c∈C) : Summable (fun z:O =>
      (star (r b z)*r c z)*W (‖ringComplex z‖^2/K)) := by
    have hW : Summable (fun z:O=>‖W (‖ringComplex z‖^2/K)‖) := by
      simpa only [scaledRadialTest_apply] using
        actual_eisenstein_summable_norm
          (scaledRadialTest W K hK)
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun z=>norm_nonneg _) _ hW
    intro z
    simp only [norm_mul,norm_star]
    calc
      _ ≤ 1*1*‖W (‖ringComplex z‖^2/K)‖ := by
        gcongr
        · exact hr b hb z
        · exact hr c hc z
      _ = _ := by ring
  have he (z:O) : W (‖ringComplex z‖^2/K)*(‖∑b∈C,a b*r b z‖^2:ℝ)=
      ∑b∈C,∑c∈C,(star (a b)*a c)*((star (r b z)*r c z)*W (‖ringComplex z‖^2/K)) := by
    rw [Complex.sq_norm (∑b∈C,a b*r b z),Complex.normSq_eq_conj_mul_self]
    simp only [map_sum,map_mul,starRingEnd_apply]
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun b hb=>summable_sum (fun c hc=>(hs b c hb hc).mul_left _))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Summable.tsum_finsetSum (fun c hc=>(hs b c hb hc).mul_left _)]
  apply Finset.sum_congr rfl
  intro c hc
  exact tsum_mul_left

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma multiplicityRow_norm_le_one (B : Finset ι) (v : ι→ℕ) (z:O) :
    ‖multiplicityRow p hg B v z‖≤1 := by
  simp only [multiplicityRow,norm_prod,norm_pow]
  calc
    _ ≤ ∏i∈B,(1:ℝ) := by
      apply Finset.prod_le_prod (fun i hi=>by positivity)
      intro i hi
      apply pow_le_one₀ (norm_nonneg _)
      let : Fintype (O⧸Ideal.span {p i}) := Fintype.ofFinite _
      exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by simp

omit [DecidableEq ι] in
lemma multiplicityRow_support (B : Finset ι) (v : ι→₀ℕ) (hv : v.support⊆B) (z:O) :
    multiplicityRow p hg B v z =
      multiplicityRow p hg v.support v z := by
  unfold multiplicityRow
  symm
  apply Finset.prod_subset hv
  intro i hi hn
  have hv0 : v i=0 := by simpa only [Finsupp.mem_support_iff,not_not] using hn
  simp only [hv0,pow_zero]

def reopenedCanonicalRow (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) (z:O) : ℂ :=
  ∑v∈Q,∑S∈pool.powerset,
    (β v*canonicalSourceCoefficient p hg Ψ m f H S)*
    (multiplicityRow p hg pool v z^3*
      primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S z)

theorem reopenedCanonicalRow_smoothed_expand
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀v∈Q,v.support⊆pool)
    (β : (ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑'z:O,W (‖ringComplex z‖^2/K)*(‖reopenedCanonicalRow p hg pool Q β Ψ m f H z‖^2:ℝ))=
      ∑v₂∈Q,∑v₁∈Q,(star (β v₂)*β v₁)*
        canonicalCubeCorrelation p hg pool (v₁.support∪v₂.support) v₁ v₂ Ψ Ψ m m f H H W K := by
  let a : (ι→₀ℕ)×Finset ι→ℂ := fun b=>β b.1*canonicalSourceCoefficient p hg Ψ m f H b.2
  let r : (ι→₀ℕ)×Finset ι→O→ℂ := fun b z=>
    multiplicityRow p hg pool b.1 z^3*
      primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) b.2 z
  have hr (b : (ι→₀ℕ)×Finset ι) (hb:b∈Q×ˢpool.powerset) (z:O) : ‖r b z‖≤1 := by
    dsimp [r]
    rw [norm_mul,norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (multiplicityRow_norm_le_one p hg pool b.1 z))).trans
      (primeSubsetRow_norm_le_one p _ _ _)
  have he:=finite_bounded_rows_smoothed_expand (Q×ˢpool.powerset) a r hr W K hK
  simp only [Finset.sum_product] at he
  change (∑'z:O,W (‖ringComplex z‖^2/K)*
    (‖reopenedCanonicalRow p hg pool Q β Ψ m f H z‖^2:ℝ))=_ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro v₂ hv₂
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v₁ hv₁
  simp only [canonicalCubeCorrelation,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  have hB₁ : v₁.support⊆v₁.support∪v₂.support:=Finset.subset_union_left
  have hB₂ : v₂.support⊆v₁.support∪v₂.support:=Finset.subset_union_right
  have hr₁ (z:O) : multiplicityRow p hg pool v₁ z=
      multiplicityRow p hg (v₁.support∪v₂.support) v₁ z := by
    rw [multiplicityRow_support p hg pool v₁ (hQ v₁ hv₁),multiplicityRow_support p hg _ v₁ hB₁]
  have hr₂ (z:O) : multiplicityRow p hg pool v₂ z=
      multiplicityRow p hg (v₁.support∪v₂.support) v₂ z := by
    rw [multiplicityRow_support p hg pool v₂ (hQ v₂ hv₂),multiplicityRow_support p hg _ v₂ hB₂]
  simp only [a,r,canonicalCubeSourcePair,star_mul,hr₁,hr₂]
  have ht : (∑'z:O,(star (primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S z)*
      star (multiplicityRow p hg (v₁.support∪v₂.support) v₂ z^3)*
      (multiplicityRow p hg (v₁.support∪v₂.support) v₁ z^3*
      primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) T z))*W (‖ringComplex z‖^2/K))=
      ∑'z:O,(star (primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S z)*
      primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) T z*
      star (multiplicityRow p hg (v₁.support∪v₂.support) v₂ z^3)*
      multiplicityRow p hg (v₁.support∪v₂.support) v₁ z^3)*W (‖ringComplex z‖^2/K) := by
    apply tsum_congr
    intro z
    ring
  rw [ht]
  ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap
theorem reopenedCanonicalRow_smoothed_eq_source {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ : ∀ v ∈ Q,v.support ⊆ pool)
    (labels : Finset (Ideal O)) (β : Ideal O → (ι →₀ ℕ) → ℂ)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (K ell : ℝ) (hK : 0 < K) :
    (∑ I ∈ labels,∑' z : O,W (‖ringComplex z‖^2/K)*
      (‖reopenedCanonicalRow p hg pool Q (β I) Ψ m (cubicIdealGenerator I)
        (fun S => g (columnLog p ell S)) z‖^2 : ℝ)) =
    canonicalSourceTotal p hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W K ell := by
  rw [canonicalSourceTotal,sum_reopenedCubeFamily]
  simp only [reopenedPairCoefficient,CubeCoordinates.support]
  calc
    _ = ∑ I ∈ labels,∑ v₂ ∈ Q,∑ v₁ ∈ Q,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (cubicIdealGenerator I) (fun S => g (columnLog p ell S))
          (fun S => g (columnLog p ell S)) W K := by
      apply Finset.sum_congr rfl
      intro I hI
      exact reopenedCanonicalRow_smoothed_expand p hg pool Q hQ (β I) Ψ m
        (cubicIdealGenerator I) (fun S => g (columnLog p ell S)) W K hK
    _ = ∑ v₂ ∈ Q,∑ v₁ ∈ Q,∑ I ∈ labels,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (cubicIdealGenerator I) (fun S => g (columnLog p ell S))
          (fun S => g (columnLog p ell S)) W K := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      apply Finset.sum_congr rfl
      intro v₁ hv₁
      have hs : v₁.support∪v₂.support ⊆ pool := Finset.union_subset (hQ v₁ hv₁) (hQ v₂ hv₂)
      simp_rw [canonicalCubeCorrelation_eq_blocks p hp hcop hg hinj hpr pool v₁ v₂ hs,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₂ hA₂
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₁ hA₁
      rw [Finset.sum_comm]

theorem reopenedCanonicalRow_smoothed_split {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ : ∀ v ∈ Q,v.support ⊆ pool)
    (labels : Finset (Ideal O)) (β : Ideal O → (ι →₀ ℕ) → ℂ)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (Ksrc K ell : ℝ)
    (hKsrc : 0 < Ksrc) (hK : 0 ≤ K) :
    (∑ I ∈ labels,∑' z : O,W (‖ringComplex z‖^2/Ksrc)*
      (‖reopenedCanonicalRow p hg pool Q (β I) Ψ m (cubicIdealGenerator I)
        (fun S => g (columnLog p ell S)) z‖^2 : ℝ)) =
    canonicalSourceZero p hp hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc ell+
    canonicalSourceFinite p hp hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc K ell+
    canonicalSourceTail p hp hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc K ell := by
  rw [reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m g W Ksrc ell hKsrc]
  exact canonicalSourceTotal_split p hp hg hinj hc pool (reopenedCubeFamily Q) labels
    (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc K ell hKsrc hK

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap ContDiff
theorem padded_orientedTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ Ksrc K ell B F H U : ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖ringComplex x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ ≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := padded_orientedCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  obtain ⟨windows₁,C₁,Cd₁,Ct₁,hC₁,hCd₁,hCt₁,hwc₁,hws₁,hwb₁,hleft⟩ :=
    globalCubeInputFamilyEnergy_quantitative_transfer ε hε g₁ V₁ M₁ hM₁ hg₁ true A J N
  obtain ⟨windows₂,C₂,Cd₂,Ct₂,hC₂,hCd₂,hCt₂,hwc₂,hws₂,hwb₂,hright⟩ :=
    globalCubeInputFamilyEnergy_quantitative_transfer ε hε g₂ V₂ M₂ hM₂ hg₂ false A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCfirst,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  have hB0 : 0<B := by linarith
  let T := fun b => globalCubeFirstTargets p b (s b)
  have hT0 (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) : z≠0 :=
    globalCubeFirstTargets_ne_zero p hp b (s b) (fun x hx=>Squarefree.ne_zero (hsf b hb x hx)) (hs0 b hb) z hz
  have hT (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) :=
    globalCubeFirstTargets_norm_bound p hp b (s b) K ell B F hK hell hB0 hF
      (hb₁ b hb) (hb₂ b hb) (hf b hb) (hh b hb) z hz
  have hTc (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F false (b.withCommon ∅) := by
    rw [globalFirstPooledRow_side]
    exact hT b hb z hz
  have hblock := hfirst p hp hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ Ksrc K ell B F
    (globalFirstRowCap K ell B F) hKsrc hK hell hB0 hF hΨ₁ hΨ₂ (fun b hb => (hw b hb).1) ha
    (fun b hb => globalFirstPooledRow_le_cap p hp K ell B F hK hell hB0 hF b (hadm b hb) (hb₁ b hb) (hb₂ b hb))
    hsf hs0 (fun b _ x hx => globalCubeFirstTargets_mem p b (s b) x hx) hT0 hT
  have hl := hleft p hp hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₁ m₁ T
    hΓ hw hK hell hB hF hH hU hellU1 hadm hΨ₁ hb₁ hb₂ hT
  have hr := hright p hp hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₂ m₂ T
    hΓ hw hK hell hB hF hH hU hellU2 hadm hΨ₂ hb₁ hb₂ hTc
  have hprefix : 0≤(Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss :=
    mul_nonneg (mul_nonneg (div_nonneg hKsrc.le hK.le) hCfirst) (Real.rpow_nonneg (globalFirstRowCap_pos K ell B F hK hell hB0 hF).le _)
  exact hblock.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hprefix)
    (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (mul_nonneg hprefix (Real.sqrt_nonneg _)))

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap ContDiff
theorem padded_rawCanonicalTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (hWin₁ : ∀ t,g₁ t≠0 → V₁ t=1) (hWin₂ : ∀ t,g₂ t≠0 → V₂ t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ Ksrc K ell B F H U : ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖ringComplex x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,rawCanonicalBlock p hp hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell‖ ≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hc₁,hs₁,hb₁,hc₂,hs₂,hb₂,htransfer⟩ :=
    padded_orientedTwoPassage_quantitative W g₁ g₂ V₁ V₂ M₁ M₂ N₁ N₂ hM₁ hM₂ hN₁ hN₂ hg₁ hg₂ hV₁ hV₂ ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hc₁,hs₁,hb₁,hc₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh

  let a' := fun b : GlobalCubeBlock ι => fun x => supportMobius b.firstDivisor*a b x
  have heq : (∑b∈blocks,rawCanonicalBlock p hp hg pool b (s b) (a b)
      Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell)=
      ∑b∈blocks,orientedCubeFirstBlock p hp hg pool b (s b) (a' b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell := by
    apply Finset.sum_congr rfl
    intro b hb
    exact rawCanonicalBlock_eq_oriented p hp hg pool b (hadm b hb) (s b) (a b)
      Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell hell hWin₁ hWin₂
  rw [heq]
  apply htransfer p hp hinj hcop hg hc hpr pool blocks s a' w Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw _ hadm hb₁ hb₂ hsf hs0 hf hh
  intro b hb x hx
  simpa only [a',norm_mul,supportMobius_norm,one_mul] using ha b hb x hx

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap ContDiff
theorem canonicalSource_twoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀t,g₁ t≠0→|t|≤M₁) (hg₂ : ∀t,g₂ t≠0→|t|≤M₂)
    (hV₁ : ∀t,V₁ t≠0→|t|≤N₁) (hV₂ : ∀t,V₂ t≠0→|t|≤N₂)
    (hWin₁ : ∀t,g₁ t≠0→V₁ t=1) (hWin₂ : ∀t,g₂ t≠0→V₂ t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M₁+6+1) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M₂+6+1) ∧
      ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ)
      (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (Γ Ksrc K ell B F H U:ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U →
      ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,Squarefree I) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      ‖(ell*B^2*F:ℂ)⁻¹*
        (canonicalSourceTotal p hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
         canonicalSourceZero p hp hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
         canonicalSourceTail p hp hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell)‖≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hg pool (canonicalSourceBlocks pool bs)
          Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true)*
        Real.sqrt (globalFirstQuantitativeBudget p hg pool (canonicalSourceBlocks pool bs)
          Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,htransfer⟩:=
    padded_rawCanonicalTwoPassage_quantitative W g₁ g₂ V₁ V₂ M₁ M₂ N₁ N₂ hM₁ hM₂ hN₁ hN₂
      hg₁ hg₂ hV₁ hV₂ hWin₁ hWin₂ ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool bs labels a Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hMU₁ hMU₂ hΨ₁ hΨ₂ ha hadm hleft hright hsf hf
  have hcenter : canonicalSourceTotal p hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
      canonicalSourceZero p hp hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
      canonicalSourceTail p hp hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell=
      canonicalSourceFinite p hp hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell := by
    rw [canonicalSourceTotal_split p hp hg hinj hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell hKsrc hK.le]
    ring
  rw [hcenter,canonicalSourceFinite_eq_raw]
  apply htransfer p hp hinj hcop hg hc hpr pool (canonicalSourceBlocks pool bs)
    (canonicalBlockFrequencies p K ell labels) (canonicalBlockCoefficient p hg a Ψ₁ Ψ₂ m₁ m₂)
    (fun _=>Γ) Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U hΓ hKsrc hK hell hB hF hH hU hMU₁ hMU₂ hΨ₁ hΨ₂
  · exact fun q hq=>⟨hΓ,le_rfl⟩
  · exact fun q hq x hx=>canonicalBlockCoefficient_bound p hp hg hinj hpr pool bs labels a Ψ₁ Ψ₂ m₁ m₂ Γ K ell hΓ hΨ₁ hΨ₂ ha q hq x hx
  · exact canonicalSourceBlocks_admissible pool bs hadm
  · exact fun q hq=>(canonicalSourceBlocks_cube_norms p pool bs B hleft hright q hq).1
  · exact fun q hq=>(canonicalSourceBlocks_cube_norms p pool bs B hleft hright q hq).2
  · intro q hq x hx
    exact hsf x.1 (Finset.mem_product.mp hx).1
  · intro q hq x hx
    exact (Finset.mem_erase.mp (Finset.mem_product.mp hx).2).1
  · intro q hq x hx
    exact hf x.1 (Finset.mem_product.mp hx).1
  · intro q hq x hx
    exact (mem_firstFrequencyDisk _ _).mp (Finset.mem_erase.mp (Finset.mem_product.mp hx).2).2

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

section
lemma firstTail_inverse_scale_bound (K D U:ℝ) (hK:0<K) (hD:0<D) (hU:D≤U):
    ((min 1 (K/D))⁻¹)^2≤(1+U/K)^2 := by
  have hU0:0≤U/K:=div_nonneg (hD.le.trans hU) hK.le
  have hi:(min 1 (K/D))⁻¹≤1+U/K:=by
    by_cases h:1≤K/D
    · rw [min_eq_left h,inv_one];linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)),inv_div]
      exact (div_le_div_of_nonneg_right hU hK.le).trans (by linarith)
  exact pow_le_pow_left₀ (inv_nonneg.mpr (le_min zero_le_one (div_pos hK hD).le)) hi 2

lemma firstTail_scalar_bound (K D E U₁ U₂ lengthScale B G₁ G₂ P H:ℝ) (A:ℕ)
    (hK:0<K) (hD:0<D) (hE:0<E) (hU₁:0<U₁) (hU₂:0<U₂)
    (hL:0≤lengthScale) (hG₁:0≤G₁) (hG₂:0≤G₂) (hP:0≤P) (hH:0≤H)
    (hDb:D≤lengthScale*B^2) (hEb:E≤B^2) (hU₁b:U₁≤lengthScale) (hU₂b:U₂≤lengthScale):
    ((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*(G₁*G₂*K)*
      (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+H)^A))≤
    ((1+diagonalControl sieveCutoff)*lengthScale)^2*(G₁*G₂*K)*P*(1+lengthScale^3*B^4/K)^2/(1+H)^A := by
  have hdc := diagonalControl_nonneg sieveCutoff
  have hden:D*E*U₁*U₂≤lengthScale^3*B^4:=by
    calc
      _ ≤ (lengthScale*B^2)*B^2*lengthScale*lengthScale:=mul_le_mul
        (mul_le_mul (mul_le_mul hDb hEb hE.le (mul_nonneg hL (sq_nonneg _))) hU₁b hU₁.le (by positivity))
        hU₂b hU₂.le (by positivity)
      _ = _:=by ring
  have hi:=firstTail_inverse_scale_bound K (D*E*U₁*U₂) (lengthScale^3*B^4) hK (by positivity) hden
  have hpref:((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*(G₁*G₂*K)≤((1+diagonalControl sieveCutoff)*lengthScale)^2*(G₁*G₂*K):=by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      _ ≤ ((1+diagonalControl sieveCutoff)*lengthScale)*((1+diagonalControl sieveCutoff)*lengthScale):=mul_le_mul (mul_le_mul_of_nonneg_left hU₁b (by positivity))
        (mul_le_mul_of_nonneg_left hU₂b (by positivity)) (by positivity) (by positivity)
      _ = _:=by ring
  calc
    _ = (((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*(G₁*G₂*K))*P*((min 1 (K/(D*E*U₁*U₂)))⁻¹)^2/(1+H)^A:=by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_pow];ring
    _ ≤ _:=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hpref hP) hi (sq_nonneg _) (by positivity)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma cubeCoordinates_radical_bound (b:CubeCoordinates ι) (B:ℝ) (hB:0≤B)
    (hb₁:‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤B):
    primeProductNorm p b.support≤B^2 := by
  have hd:(∏i∈b.support,p i)∣primeProduct p b.support b.leftExponent*primeProduct p b.support b.rightExponent:=by
    rw [←primeProduct_add p]
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    simpa only [pow_one] using pow_dvd_pow (p i) (b.support_pos i hi)
  have hb0:=mul_ne_zero (primeProduct_ne_zero p hp b.support b.leftExponent)
    (primeProduct_ne_zero p hp b.support b.rightExponent)
  have hn:=element_norm_le_of_dvd hb0 hd
  simp only [map_mul,norm_mul,mul_pow] at hn
  exact hn.trans (by simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma cubeSourceDivisor_norm_bound (b:CubeCoordinates ι) (C D:Finset ι) (B lengthScale:ℝ)
    (hB:0≤B) (hL:0≤lengthScale) (hCB:Disjoint C b.support)
    (hb₁:‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤B)
    (hC:primeProductNorm p C≤lengthScale)
    (hD:D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit):
    primeProductNorm p D≤lengthScale*B^2 := by
  calc
    _ ≤ primeProductNorm p (C∪b.support):=primeProductNorm_mono p hp
      (hD.trans (Finset.union_subset_union_right (Finset.filter_subset _ _)))
    _ = primeProductNorm p C*primeProductNorm p b.support:=primeProductNorm_union p _ _ hCB
    _ ≤ _:=mul_le_mul hC (cubeCoordinates_radical_bound p hp b B hB hb₁ hb₂)
      (primeProductNorm_pos p hp _).le hL

lemma cubeSourceDivisors_card
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (b:CubeCoordinates ι) (C:Finset ι) (B lengthScale:ℝ) (hB:0<B) (hL:0<lengthScale) (hCB:Disjoint C b.support)
    (hb₁:‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤B)
    (hC:primeProductNorm p C≤lengthScale):
    ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)≤(1+diagonalControl sieveCutoff)*(lengthScale*B^2) := by
  let M:=C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit
  have he:boundedPrimeSupports p M (lengthScale*B^2)=M.powerset:=by
    apply Finset.filter_eq_self.mpr
    intro D hD
    exact cubeSourceDivisor_norm_bound p hp b C D B lengthScale hB.le hL.le hCB hb₁ hb₂ hC (Finset.mem_powerset.mp hD)
  rw [←he]
  exact boundedPrimeSupports_card_positive p hp hinj M _ (mul_pos hL (sq_pos_of_pos hB))

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma sourceMobiusDivisor_norm_le_one (D:Finset ι):
    ‖supportMobius D/(primeProductNorm p D:ℂ)‖≤1 := by
  have hmu : ‖supportMobius D‖≤1 := le_of_eq (supportMobius_norm D)
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (primeProductNorm_pos p hp D)]
  exact (div_le_div_of_nonneg_right hmu (primeProductNorm_pos p hp D).le).trans
    ((div_le_one (primeProductNorm_pos p hp D)).mpr (primeProductNorm_ge_one p hp D))

end

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

section

open Eisenstein SchwartzPlanePoisson
open FirstPassCubeLabels


section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem canonicalCubeDualTail_support
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (g₁ g₂ W:𝓢(ℝ,ℂ))
    (ell K M:ℝ) (hell:0<ell) (hgM:∀t,g₁ t≠0→t≤M)
    (hC:¬primeProductNorm p C≤ell*Real.exp M) (T:Finset ι→Finset O):
    canonicalCubeDualTail p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K T=0 := by
  have hz (S:Finset ι):g₁ (columnLog p ell ((b.rightDivisor∪C)∪S))=0:=by
    by_contra h
    exact hC ((primeProductNorm_mono p hp
      (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)).trans
      (columnLog_norm_upper p hp ell M hell _ (hgM _ h)))
  have hcoef (S:Finset ι):canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun R=>g₁ (columnLog p ell R)) S=0:=by
    simp only [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn,ite_true,hz,mul_zero,zero_mul]
  simp only [canonicalCubeDualTail,actualFirstKernel,threeGaussRowFactor,hcoef,mul_zero,
    star_zero,zero_mul,ite_self,Finset.sum_const_zero,tsum_zero]

end

theorem full_uniform_canonicalSourceTail_bound (ε:ℝ) (hε:0<ε) (A:ℕ):
    ∃(s:Finset (ℕ×ℕ)) (C:ℝ),0<C ∧
    ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ M₁ M₂ Ksrc K ell B F lengthScale:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<Ksrc → 0<K → 0<ell → 1≤B → 1≤F → 1≤lengthScale →
      ell*Real.exp M₁≤lengthScale → ell*Real.exp M₂≤lengthScale →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) →
      (∀t,g₁ t≠0→t≤M₁) → (∀t,g₂ t≠0→t≤M₂) →
      ‖canonicalSourceTail p hp hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell‖≤
      C*B^(4+ε)*lengthScale^4*F*Γ*(G₁*G₂*Ksrc)*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*
        (1+lengthScale^3*B^4/Ksrc)^2/(1+(Ksrc/K)/Real.exp (M₁+M₂))^A := by
  have hdc := diagonalControl_nonneg sieveCutoff
  obtain ⟨s,Ct,hCt,hkernel⟩:=full_uniform_canonicalSource_kernel_tail A
  obtain ⟨Cb,hCb,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨s,Cb*(1+diagonalControl sieveCutoff)^5*Ct,by positivity,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Γ G₁ G₂ M₁ M₂ Ksrc K ell B F lengthScale
    hΓ hG₁ hG₂ hKsrc hK hell hB hF hL hL₁ hL₂ hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha hg₁ hg₂ hM₁ hM₂
  have hB0:0<B:=zero_lt_one.trans_le hB
  have hL0:0<lengthScale:=zero_lt_one.trans_le hL
  let P:=Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let H:ℝ:=(Ksrc/K)/Real.exp (M₁+M₂)
  let Q:ℝ:=((1+diagonalControl sieveCutoff)*lengthScale)^2*(G₁*G₂*Ksrc)*P*(1+lengthScale^3*B^4/Ksrc)^2/(1+H)^A
  have hP:0≤P:=by dsimp [P];positivity
  have hH:0≤H:=by dsimp [H];positivity
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hlabel:(labels.card:ℝ)≤(1+diagonalControl sieveCutoff)*F:=(finite_ideal_card_bound labels F hF hIF).trans
    (mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans hF))
  have hbcount:(bs.card:ℝ)≤Cb*B^(1+ε)*B:=by
    apply hcount p hp hinj bs B B hB hB0.le hadm hb₁ hb₂
    intro b hb
    have hn:primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)≤B^2:=
      (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
        (cubeCoordinates_radical_bound p hp b B hB0.le (hb₁ b hb) (hb₂ b hb))
    change ‖ringComplex (∏i∈cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖^2≤B^2 at hn
    nlinarith [norm_nonneg (ringComplex (∏i∈cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i))]
  let z (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal O):ℂ:=
    canonicalCubeDualTail p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ (cubicIdealGenerator I)
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W Ksrc (canonicalSourceCutoff p K ell b C)
  have hblock (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι) (hC:C∈boundedPrimeSupports p (pool\b.support) lengthScale) (I:Ideal O):
      ‖z b C I‖≤((1+diagonalControl sieveCutoff)*(lengthScale*B^2))*Q:=by
    have hCb:primeProductNorm p C≤lengthScale:=(Finset.mem_filter.mp hC).2
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hiB=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hiB)
    let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
    let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
    let U₁:=X₁*Real.exp M₁
    let U₂:=X₂*Real.exp M₂
    let E:=primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
    have hU₁:0<U₁:=mul_pos (div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))) (Real.exp_pos _)
    have hU₂:0<U₂:=mul_pos (div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))) (Real.exp_pos _)
    have hE:0<E:=primeProductNorm_pos p hp _
    have hU₁b:U₁≤lengthScale:=(mul_le_mul_of_nonneg_right (div_le_self hell.le
      (one_le_mul_of_one_le_of_one_le (primeProductNorm_ge_one p hp _) (primeProductNorm_ge_one p hp _))) (Real.exp_pos M₁).le).trans hL₁
    have hU₂b:U₂≤lengthScale:=(mul_le_mul_of_nonneg_right (div_le_self hell.le
      (one_le_mul_of_one_le_of_one_le (primeProductNorm_ge_one p hp _) (primeProductNorm_ge_one p hp _))) (Real.exp_pos M₂).le).trans hL₂
    have hEb:E≤B^2:=(primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
      (cubeCoordinates_radical_bound p hp b B hB0.le (hb₁ b hb) (hb₂ b hb))
    have hlocal (D:Finset ι) (hD:D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset):
        ‖∑'h:{h:O // h∉canonicalSourceCutoff p K ell b C D},actualFirstKernel p hp hg (pool\(b.support∪C)) b.support
          (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
          (canonicalCubeResidual p hg b C true Ψ₁ m₁ (cubicIdealGenerator I) (fun S=>g₁ (columnLog p ell S)))
          (canonicalCubeResidual p hg b C false Ψ₂ m₂ (cubicIdealGenerator I) (fun S=>g₂ (columnLog p ell S)))
          W (fun _=>1) (fun _=>1) 1 1 Ksrc ((∏i∈D,p i)) h.val‖≤Q:=by
      have hDb:=cubeSourceDivisor_norm_bound p hp b C D B lengthScale hB0.le hL0.le hCB (hb₁ b hb) (hb₂ b hb) hCb (Finset.mem_powerset.mp hD)
      exact (hkernel p hp hinj hcop hg hc pool b (hadm b hb) C D hCB Ψ₁ Ψ₂ hΨ₁ hΨ₂
        m₁ m₂ (cubicIdealGenerator I) g₁ g₂ W G₁ G₂ M₁ M₂ Ksrc K ell hG₁ hG₂ hKsrc hK hell hg₁ hg₂ hM₁ hM₂).trans
        (firstTail_scalar_bound Ksrc (primeProductNorm p D) E U₁ U₂ lengthScale B G₁ G₂ P H A
          hKsrc (primeProductNorm_pos p hp _) hE hU₁ hU₂ hL0.le hG₁ hG₂ hP hH hDb hEb hU₁b hU₂b)
    dsimp only [z,canonicalCubeDualTail]
    rw [norm_mul]
    calc
      _ ≤ ‖∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
          supportMobius D/(primeProductNorm p D:ℂ)*
          ∑'h:{h:O // h∉canonicalSourceCutoff p K ell b C D},actualFirstKernel p hp hg (pool\(b.support∪C)) b.support
            (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
            (canonicalCubeResidual p hg b C true Ψ₁ m₁ (cubicIdealGenerator I) (fun S=>g₁ (columnLog p ell S)))
            (canonicalCubeResidual p hg b C false Ψ₂ m₂ (cubicIdealGenerator I) (fun S=>g₂ (columnLog p ell S)))
            W (fun _=>1) (fun _=>1) 1 1 Ksrc ((∏i∈D,p i)) h.val‖:=
        mul_le_of_le_one_left (norm_nonneg _) (canonicalCubeOuter_norm_le_one p hp hg hinj hpr b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _)
      _ ≤ ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,Q:=by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro D hD
        rw [norm_mul]
        exact (mul_le_mul (sourceMobiusDivisor_norm_le_one p hp D) (hlocal D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul Q)
      _ = ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)*Q:=by simp
      _ ≤ _:=mul_le_mul_of_nonneg_right (cubeSourceDivisors_card p hp hinj b C B lengthScale hB0 hL0 hCB (hb₁ b hb) (hb₂ b hb) hCb) hQ
  have hcommon (b:CubeCoordinates ι) (hb:b∈bs):
      ‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤
      ((1+diagonalControl sieveCutoff)*lengthScale)*((1+diagonalControl sieveCutoff)*F)*Γ*(((1+diagonalControl sieveCutoff)*(lengthScale*B^2))*Q):=by
    have heq:(∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I)=
        ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,a b C I*z b C I:=by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro C hC hnot
      have hn:¬primeProductNorm p C≤ell*Real.exp M₁:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h.trans hL₁⟩)
      apply Finset.sum_eq_zero
      intro I hI
      rw [show z b C I=0 from canonicalCubeDualTail_support p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ _ g₁ g₂ W ell Ksrc M₁ hell hM₁ hn _,mul_zero]
    rw [heq]
    calc
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,‖a b C I*z b C I‖:=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC=>norm_sum_le _ _))
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,Γ*(((1+diagonalControl sieveCutoff)*(lengthScale*B^2))*Q):=by
        apply Finset.sum_le_sum
        intro C hC
        apply Finset.sum_le_sum
        intro I hI
        rw [norm_mul]
        exact mul_le_mul (ha b hb C (Finset.mem_filter.mp hC).1 I hI) (hblock b hb C hC I) (norm_nonneg _) hΓ
      _ = ((boundedPrimeSupports p (pool\b.support) lengthScale).card:ℝ)*(labels.card:ℝ)*Γ*(((1+diagonalControl sieveCutoff)*(lengthScale*B^2))*Q):=by simp;ring
      _ ≤ _:=by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hΓ
        exact mul_le_mul (boundedPrimeSupports_card_positive p hp hinj _ lengthScale hL0) hlabel (Nat.cast_nonneg _) (by positivity)
  change ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤_
  calc
    _ ≤ ∑b∈bs,‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖:=norm_sum_le _ _
    _ ≤ ∑b∈bs,((1+diagonalControl sieveCutoff)*lengthScale)*((1+diagonalControl sieveCutoff)*F)*Γ*(((1+diagonalControl sieveCutoff)*(lengthScale*B^2))*Q):=Finset.sum_le_sum hcommon
    _ = (bs.card:ℝ)*(((1+diagonalControl sieveCutoff)*lengthScale)*((1+diagonalControl sieveCutoff)*F)*Γ*(((1+diagonalControl sieveCutoff)*(lengthScale*B^2))*Q)):=by simp
    _ ≤ (Cb*B^(1+ε)*B)*(((1+diagonalControl sieveCutoff)*lengthScale)*((1+diagonalControl sieveCutoff)*F)*Γ*(((1+diagonalControl sieveCutoff)*(lengthScale*B^2))*Q)):=
      mul_le_mul_of_nonneg_right hbcount (by positivity)
    _ = _:=by
      dsimp [Q,P,H]
      rw [Real.rpow_add hB0,Real.rpow_add hB0]
      norm_num
      ring

end

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration MeasureTheory
open scoped Classical

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀i,(Ideal.span {p i}).IsMaximal]

def globalQuantitativeSource (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
    (K ell B F M H U : ℝ) (side : Bool) : Finset (GlobalSecondData ι) :=
  globalFirstSupportedPool p pool
    ((globalFirstFamilySet pool blocks).filter
      (fun b => primeProductNorm p b.common ≤ U ∧ primeProductNorm p b.firstCommon ≤ U))
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side

theorem globalQuantitativeSource_block_mem (pool : Finset ι)
    (blocks : Finset (GlobalCubeBlock ι)) (K ell B F M H U : ℝ) (side : Bool)
    (x : GlobalSecondData ι) (hx : x∈globalQuantitativeSource p pool blocks K ell B F M H U side) :
    x.first.block∈blocks := by
  have hx' := (mem_globalFirstExpansionPool pool _ _ x).mp (Finset.mem_filter.mp hx).1
  exact ((mem_globalFirstFamilySet pool blocks x.first).mp (Finset.mem_filter.mp hx'.1).1).1

theorem globalQuantitativeSource_frequency_ne_zero (pool : Finset ι)
    (blocks : Finset (GlobalCubeBlock ι)) (K ell B F M H U : ℝ) (side : Bool)
    (x : GlobalSecondData ι) (hx : x∈globalQuantitativeSource p pool blocks K ell B F M H U side) :
    x.source.frequency ≠ 0 :=
  globalFirstSupportedPool_frequency_ne_zero p pool _ _ ell M side x hx

end

/-- The complete first-pass bound from uniform control of the retained child densities. -/
theorem globalFirstQuantitativeBudget_canonical_bound (deltaLoss:ℝ) (hδ:0<deltaLoss) (ε:ℝ) (hε:0<ε):
    ∃Clo Chi:ℝ,0<Clo ∧ 0<Chi ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i})) (hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (blocks:Finset (GlobalCubeBlock ι)) (side:Bool)
      (Ψ:O→*ℂ) (m:O) (windows:Fin 7→ℝ→ℂ)
      (C Cd Ct Γ E K ell B F M H U Z θ A₀ Vmax:ℝ) (N J Ntail:ℕ),
      0≤C → 0≤Γ → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀u,‖Ψ u‖≤1) →
      (∀b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (let source := globalQuantitativeSource p pool blocks K ell B F M H U side
       ∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
        (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),
        ∀s q:QuadraticRayRing×QuadraticRayRing,∀q₀∈globalBinTriples p source side j,
        densityChildEnergy p hg
          (combinedFixedColumn p hg side q.1 s.1 (fun _=>1))
          (combinedFixedColumn p hg side q.2 s.2 (fun _=>1)) pool Ψ Ψ
          (fixedTripleMask m q₀) (globalArithmeticTargets p source side q₀ j) (windows 5) (windows 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J)≤
          E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2) →
      globalFirstQuantitativeBudget p hg pool blocks Ψ m windows C Cd Ct Γ ε K ell B F M H U
        (N+1) (2*J) Ntail side≤
        (2*(Fintype.card (QuadraticRayRing×QuadraticRayRing):ℝ))*(∫t:ℝ,firstLogDensity 0 t)*Γ*((ell*B^3)*F)*
          ((B*U)^ε*(Cd+Ct*(U*globalFirstTailFactor K ell B F U H Ntail))+
            C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
              (E*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N))) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩:=globalChildBudget_canonical_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hg hinj hpr pool blocks side Ψ m windows C Cd Ct Γ E K ell B F M H U Z θ A₀ Vmax N J Ntail
    hC hΓ hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hb₁ hb₂ he
  let source:=globalQuantitativeSource p pool blocks K ell B F M H U side
  have hk:∀x∈source,x.source.frequency≠0:=
    fun x hx=>globalQuantitativeSource_frequency_ne_zero p pool blocks K ell B F M H U side x hx
  have hb₁':∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B:=
    fun x hx=>hb₁ x.first.block (globalQuantitativeSource_block_mem p pool blocks K ell B F M H U side x hx)
  have hb₂':∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B:=
    fun x hx=>hb₂ x.first.block (globalQuantitativeSource_block_mem p pool blocks K ell B F M H U side x hx)
  have hr:=hbound p hp hg hinj hpr pool source side Ψ m windows (Γ*C) E K ell B F M H U Z θ A₀ Vmax N J
    (mul_nonneg hΓ hC) hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂
    hΨ hk hb₁' hb₂' he
  have hI:0≤∫t:ℝ,firstLogDensity 0 t:=integral_nonneg (fun t=>firstLogDensity_nonneg 0 t)
  unfold globalFirstQuantitativeBudget
  dsimp only
  apply (mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hr) le_rfl)
    (mul_nonneg (by positivity) hI)).trans_eq
  ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration MeasureTheory RayFourExpansion
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

/-- Unit multiplicity and the three height-density integrals. -/
def canonicalDensityConstant (E:ℝ) (J:ℕ) (t:ℝ):ℝ:=
  (Fintype.card Oˣ:ℝ)*E*(1+‖t‖)^(2*J)*(∫s:ℝ,firstLogDensity 0 s)^3

lemma canonicalDensityConstant_nonneg (E:ℝ) (hE:0≤E) (J:ℕ) (t:ℝ):
    0≤canonicalDensityConstant E J t:=by
  have hi:0≤∫s:ℝ,firstLogDensity 0 s:=integral_nonneg (fun s=>firstLogDensity_nonneg 0 s)
  unfold canonicalDensityConstant
  positivity

/-- Uniform canonical bounds for ray twists control every retained residue density. -/
theorem globalFirstQuantitativeBudget_state_bound (deltaLoss:ℝ) (hδ:0<deltaLoss) (ε:ℝ) (hε:0<ε):
    ∃Clo Chi:ℝ,0<Clo ∧ 0<Chi ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2) (hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (blocks:Finset (GlobalCubeBlock ι)) (side:Bool)
      (Ψ:O→*ℂ) (m:O) (windows:Fin 7→ℝ→ℂ)
      (C Cd Ct Γ E oldHeight K ell B F M H U Z θ A₀ Vmax:ℝ) (N J Ntail:ℕ),
      0≤C → 0≤Γ → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀u,‖Ψ u‖≤1) →
      (∀b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈blocks,‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (let source := globalQuantitativeSource p pool blocks K ell B F M H U side
       ∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
        (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),
        ∀q₀∈globalBinTriples p source side j,∀χ:RayCharacter,∀t:ℝ,
        (canonicalLogEnergy p hg (fun _=>1) pool (normHeightTwist (Ψ*rayMonoid χ) t)
          (fixedTripleMask m q₀) (globalCanonicalLabels p source side q₀ j)
          (orientedLogProfile true (windows 5)) (globalPooledColumnScale ell j) (globalLogRep j 8*Real.exp 1)≤
          E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2*(1+‖t‖)^(2*J)) ∧
        (canonicalLogEnergy p hg (fun _=>1) pool (normHeightTwist (Ψ*rayMonoid χ) t)
          (fixedTripleMask m q₀) (globalCanonicalLabels p source side q₀ j)
          (orientedLogProfile false (windows 6)) (globalPooledColumnScale ell j) (globalLogRep j 8*Real.exp 1)≤
          E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2*(1+‖t‖)^(2*J))) →
      globalFirstQuantitativeBudget p hg pool blocks (normHeightTwist Ψ oldHeight) m windows C Cd Ct Γ ε K ell B F M H U
        (N+1) (2*J) Ntail side≤
        (2*(Fintype.card (QuadraticRayRing×QuadraticRayRing):ℝ))*(∫t:ℝ,firstLogDensity 0 t)*Γ*((ell*B^3)*F)*
          ((B*U)^ε*(Cd+Ct*(U*globalFirstTailFactor K ell B F U H Ntail))+
            C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
              (canonicalDensityConstant E J oldHeight*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N))) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩:=globalFirstQuantitativeBudget_canonical_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hg hinj hc hpr pool blocks side Ψ m windows C Cd Ct Γ E oldHeight K ell B F M H U Z θ A₀ Vmax N J Ntail
    hC hΓ hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hb₁ hb₂ he
  apply hbound p hp hg hinj hpr pool blocks side (normHeightTwist Ψ oldHeight) m windows
    C Cd Ct Γ (canonicalDensityConstant E J oldHeight) K ell B F M H U Z θ A₀ Vmax N J Ntail
    hC hΓ (canonicalDensityConstant_nonneg E hE J oldHeight) hU hK hell hB hF hH
    hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂
    (fun u=>(normHeightTwist_norm_le Ψ oldHeight u).trans (hΨ u)) hb₁ hb₂
  dsimp only
  intro j hj s q q₀ hq
  let source:=globalQuantitativeSource p pool blocks K ell B F M H U side
  have hk:∀x∈source,x.source.frequency≠0:=
    fun x hx=>globalQuantitativeSource_frequency_ne_zero p pool blocks K ell B F M H U side x hx
  have hkc:0<globalLogRep j 8*Real.exp 1:=mul_pos (globalLogRep_pos j 8) (Real.exp_pos 1)
  have hb (negative:Bool) (r v:QuadraticRayRing) (t:ℝ):
      canonicalLogEnergy p hg (combinedFixedColumn p hg side r v (fun _=>1)) pool
        (normHeightTwist Ψ t) (fixedTripleMask m q₀) (globalCanonicalLabels p source side q₀ j)
        (orientedLogProfile negative (if negative then windows 5 else windows 6))
        (globalPooledColumnScale ell j) (globalLogRep j 8*Real.exp 1)≤
        E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2*(1+‖t‖)^(2*J):=by
    apply canonicalLogEnergy_combined_uniform p hg hc pool (normHeightTwist Ψ t)
      (fixedTripleMask m q₀) (globalCanonicalLabels p source side q₀ j) side r v (fun _=>1)
      _ _ _ _ hkc (by positivity)
    intro χ
    rw [←normHeightTwist_mul]
    cases negative
    · exact (he j hj q₀ hq χ t).2
    · exact (he j hj q₀ hq χ t).1
  have hd:=densityChildEnergy_from_canonical_state p hp hg
    (combinedFixedColumn p hg side q.1 s.1 (fun _=>1))
    (combinedFixedColumn p hg side q.2 s.2 (fun _=>1)) pool Ψ Ψ
    (fixedTripleMask m q₀) (globalArithmeticTargets p source side q₀ j)
    (globalCanonicalLabels p source side q₀ j) (windows 5) (windows 6)
    (globalPooledColumnScale ell j) (globalPooledLabelScale j) (globalLogRep j 8*Real.exp 1)
    E oldHeight oldHeight J (globalPooledColumnScale_pos ell hell j) hkc hE
    (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩)
    (fun z hz=>(globalArithmeticTargets_bounds p hp source side q₀ j hk z hz).2.2)
    (globalArithmeticTargets_ne_zero p hp source side q₀ j hk)
    (hb true q.1 s.1) (hb false q.2 s.2)
  exact hd.trans_eq (by unfold canonicalDensityConstant;rw [two_mul,pow_add];ring)

end SecondPassArithmetic

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
