/-
The second Poisson pass adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.SieveComposition

/-!
# The second Poisson pass

Prime-product norms and the Möbius sign on squarefree supports. The dual row of the second
pass keeps its trace Gauss factor and signed divisor expansion; labelled child energies push
forward to the fixed second mode.
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

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι]

/-- The Möbius sign on a finite squarefree prime support. -/
def supportMobius (S : Finset ι) : ℂ := (-1) ^ S.card

lemma supportMobius_union (S T : Finset ι) (h : Disjoint S T) :
    supportMobius (S ∪ T) = supportMobius S*supportMobius T := by
  rw [supportMobius,Finset.card_union_of_disjoint h,pow_add]
  rfl

lemma star_supportMobius (S : Finset ι) : star (supportMobius S) = supportMobius S := by
  simp only [supportMobius,star_pow,star_neg,star_one]

lemma supportMobius_sq (S : Finset ι) : supportMobius S*supportMobius S = 1 := by
  change (-1 : ℂ) ^ S.card*(-1) ^ S.card = 1
  rw [←mul_pow]
  norm_num

variable (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)

/-- The puncture mask and both fixed character arguments remain in each column. -/
def secondInputCoefficient (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏ i ∈ S, p i)*primeCoprimeMask p S m*
    primeSubsetRow p χ S c ^ 4*primeSubsetRow p χ S d*H S

lemma secondInputCoefficient_union (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (G U : Finset ι) (hd : Disjoint G U) :
    secondInputCoefficient p χ Ψ m c d H (G ∪ U) =
      secondInputCoefficient p χ Ψ m c d (fun _ => 1) G*
        secondInputCoefficient p χ Ψ m c d (fun V => H (G ∪ V)) U := by
  simp only [secondInputCoefficient,Finset.prod_union hd,map_mul,
    primeCoprimeMask,Finset.prod_union hd,primeSubsetRow_union p χ G U hd,mul_pow,mul_one]
  ring

def supportConjugateSum (F : Finset ι) (a : Finset ι → ℂ) (z : O) : ℂ :=
  ∑ S ∈ F.powerset, supportMobius S*a S*star (primeSubsetRow p χ S z)

def inputConjugateRow (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (z : O) : ℂ :=
  supportConjugateSum p χ F (secondInputCoefficient p χ Ψ m c d H) z

/-- Common support produces its coprimality mask before Poisson reflection. -/
theorem inputConjugateRow_sq_overlap
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (z : O) :
    (↑(‖inputConjugateRow p χ F Ψ m c d H z‖ ^ 2) : ℂ) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then
          (↑(‖secondInputCoefficient p χ Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
          primeCoprimeMask p G z *
          (star (supportMobius U *
            secondInputCoefficient p χ Ψ m c d (fun S => H (G ∪ S)) U) *
            (supportMobius V *
              secondInputCoefficient p χ Ψ m c d (fun S => H (G ∪ S)) V) *
            (primeSubsetRow p χ U z *
              star (primeSubsetRow p χ V z))) else 0 := by
  have hnorm (a : ℂ) : (↑(‖a‖ ^ 2) : ℂ) = star a * a := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hnorm]
  unfold inputConjugateRow supportConjugateSum
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [FiniteOverlapDecomposition.sum_pair_eq_overlap]
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · rw [if_pos hd, if_pos hd]
    have hGU : Disjoint G U := Finset.disjoint_left.mpr (fun i hi hu =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hu)).2 hi)
    have hGV : Disjoint G V := Finset.disjoint_left.mpr (fun i hi hv =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hV) hv)).2 hi)
    rw [supportMobius_union G U hGU, supportMobius_union G V hGV,
      secondInputCoefficient_union p χ Ψ m c d H G U hGU,
      secondInputCoefficient_union p χ Ψ m c d H G V hGV,
      primeSubsetRow_union p χ G U hGU,
      primeSubsetRow_union p χ G V hGV]
    simp only [star_mul, star_star, star_supportMobius]
    have hmu := supportMobius_sq G
    have hrow := primeSubsetRow_diagonal p χ G z
    rw [hnorm]
    calc
      _ = (supportMobius G * supportMobius G) *
        (star (secondInputCoefficient p χ Ψ m c d (fun _ => 1) G) *
          secondInputCoefficient p χ Ψ m c d (fun _ => 1) G) *
        (star (primeSubsetRow p χ G z) *
          primeSubsetRow p χ G z) *
        (star (supportMobius U *
            secondInputCoefficient p χ Ψ m c d (fun S => H (G ∪ S)) U) *
          (supportMobius V *
            secondInputCoefficient p χ Ψ m c d (fun S => H (G ∪ S)) V) *
          (primeSubsetRow p χ U z *
            star (primeSubsetRow p χ V z))) := by
          simp only [star_mul, star_supportMobius]
          ring
      _ = _ := by
        rw [hmu, hrow]
        simp only [star_mul, star_supportMobius]
        ring
  · simp [hd]


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)

def overlapPairWeight (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (G U V : Finset ι) : ℂ :=
  (‖secondInputCoefficient p χ Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ)*
    (star (supportMobius U*secondInputCoefficient p χ Ψ m c d (fun S => H (G ∪ S)) U)*
      (supportMobius V*secondInputCoefficient p χ Ψ m c d (fun S => H (G ∪ S)) V))

def maskedSecondSource (G U V : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑' z : O, primeCoprimeMask p G z*
    (star (primeSubsetRow p χ V z)*primeSubsetRow p χ U z)*W (‖ringComplex z‖ ^ 2/Y)

lemma maskedSecondSource_summable (G U V : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => primeCoprimeMask p G z*
      (star (primeSubsetRow p χ V z)*primeSubsetRow p χ U z)*W (‖ringComplex z‖ ^ 2/Y)) := by
  have hs : Summable (fun z : O => ‖W (‖ringComplex z‖ ^ 2/Y)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W Y hY)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro z
  rw [norm_mul,norm_mul,norm_mul,norm_star]
  have hrow : ‖primeSubsetRow p χ V z‖*‖primeSubsetRow p χ U z‖ ≤ 1 :=
    (mul_le_mul (primeSubsetRow_norm_le_one p χ V z) (primeSubsetRow_norm_le_one p χ U z)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hm : ‖primeCoprimeMask p G z‖*(‖primeSubsetRow p χ V z‖*‖primeSubsetRow p χ U z‖) ≤ 1 :=
    (mul_le_mul (primeCoprimeMask_norm_le_one p G z) hrow (by positivity) (by norm_num)).trans_eq (one_mul 1)
  exact mul_le_of_le_one_left (norm_nonneg _) hm

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)

theorem inputConjugateRow_smoothed_overlap
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖ringComplex z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p χ F Ψ m c d H z‖ ^ 2) : ℂ)) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then overlapPairWeight p χ Ψ m c d H G U V *
          maskedSecondSource p χ G U V W Y else 0 := by
  let f := fun (G U V : Finset ι) (z : O) => if Disjoint U V then
    overlapPairWeight p χ Ψ m c d H G U V *
      (primeCoprimeMask p G z *
        (star (primeSubsetRow p χ V z) *
          primeSubsetRow p χ U z) * W (‖ringComplex z‖ ^ 2 / Y))
    else 0
  have hf (G U V : Finset ι) : Summable (f G U V) := by
    by_cases hd : Disjoint U V
    · simpa only [f, if_pos hd] using
        (maskedSecondSource_summable p χ G U V W Y hY).mul_left (overlapPairWeight p χ Ψ m c d H G U V)
    · simp only [f, if_neg hd]
      exact summable_zero
  have he (z : O) : W (‖ringComplex z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p χ F Ψ m c d H z‖ ^ 2) : ℂ) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset, f G U V z := by
    rw [inputConjugateRow_sq_overlap p χ]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro G hG
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    by_cases hd : Disjoint U V
    · simp only [f, if_pos hd, overlapPairWeight]
      ring
    · simp [f, hd]
  rw [tsum_congr he]
  rw [Summable.tsum_finsetSum (fun G _ => summable_sum (fun U _ => summable_sum (fun V _ => hf G U V)))]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Summable.tsum_finsetSum (fun U _ => summable_sum (fun V _ => hf G U V))]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Summable.tsum_finsetSum (fun V _ => hf G U V)]
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · simp only [f, if_pos hd, maskedSecondSource]
    exact tsum_mul_left
  · simp [f, hd]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)

/-- The dual row keeps its exact trace Gauss factor and signed divisor expansion. -/
def maskedSecondDual (hp : ∀ i, p i ≠ 0)
    (G U V : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  let ap : ↥((V \ U) ∪ (U \ V)) → O := fun i => p i.val
  let ac := activePrimeRowCharacter p χ V U
  let n := ∏ i, ap i
  ((Y : ℂ)*primeRowTraceGauss ap (fun i => hp i.val) ac/(‖ringComplex n‖ ^ 2 : ℝ))*
    ∑ E ∈ G.powerset,
      ((-1 : ℂ) ^ E.card*primeCuspRowCharacter ap ac (∏ i ∈ E, p i)/
        (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ))*
        ∑' k : O, primeCuspRowCharacter ap (fun i => (ac i)⁻¹) k*
          paperRadialFourier W (Y*‖ringComplex k‖ ^ 2/
            (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2*‖ringComplex n‖ ^ 2))

theorem masked_pair_second_poisson (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (hχ : ∀ i, χ i ≠ 1)
    (G U V : Finset ι) (hd : Disjoint U V)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    maskedSecondSource p χ G U V W Y = maskedSecondDual p χ hp G U V W Y := by
  have hcop : Pairwise (Function.onFun IsCoprime p) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp
      (Ideal.isCoprime_of_isMaximal (hinj.ne hij))
  have hpair (z : O) : star (primeSubsetRow p χ V z)*primeSubsetRow p χ U z =
      primeCuspRowCharacter (fun i : ↥((V \ U) ∪ (U \ V)) => p i.val)
        (activePrimeRowCharacter p χ V U) z := by
    rw [primeSubsetRow_pair_active,Finset.disjoint_iff_inter_eq_empty.mp hd.symm]
    simp only [primeCoprimeMask,Finset.prod_empty,one_mul]
  unfold maskedSecondSource
  simp_rw [hpair]
  exact prime_row_trace_masked_poisson (fun i : ↥((V \ U) ∪ (U \ V)) => p i.val)
    (fun i => hp i.val) (hinj.comp Subtype.val_injective) (activePrimeRowCharacter p χ V U)
    (activePrimeRowCharacter_ne_one p χ hχ V U) p hp hcop G W Y hY

/-- Exact second reflection after common-prime terms have been regrouped. -/
theorem inputConjugateRow_smoothed_second_poisson (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (hχ : ∀ i, χ i ≠ 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖ringComplex z‖ ^ 2/Y)*
      (‖inputConjugateRow p χ F Ψ m c d H z‖ ^ 2 : ℝ)) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then overlapPairWeight p χ Ψ m c d H G U V*
          maskedSecondDual p χ hp G U V W Y else 0 := by
  rw [inputConjugateRow_smoothed_overlap p χ F Ψ m c d H W Y hY]
  apply Finset.sum_congr rfl
  intro G _
  apply Finset.sum_congr rfl
  intro U _
  apply Finset.sum_congr rfl
  intro V _
  by_cases hd : Disjoint U V
  · rw [if_pos hd,if_pos hd,masked_pair_second_poisson p χ hp hinj hχ G U V hd W Y hY]
  · simp only [if_neg hd]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson CubicJacobi
open scoped Classical

variable {ι : Type*} [DecidableEq ι]

/-- Squaring the sextic row gives the actual cubic symbol of its prime product. -/
lemma sexticRow_square_symbol (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (x : O) :
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S x ^ 2 =
      ringComplex (symbol x (∏ i ∈ S, p i)) := by
  induction S using Finset.induction_on with
  | empty => simp only [primeSubsetRow,Finset.prod_empty,one_pow,symbol_one,map_one]
  | @insert i S hi ih =>
    have hprime : complexSexticChar (Ideal.span {p i}) (hg i) (Ideal.Quotient.mk (Ideal.span {p i}) x) ^ 2 =
        ringComplex (symbol x (p i)) := by
      rw [←MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0),
        (complexSexticChar_powers (Ideal.span {p i}) (hg i)).1]
      rw [symbol,idealSymbol_prime _ (hg i)]
      rfl
    simpa only [primeSubsetRow,Finset.prod_insert hi,mul_pow,symbol_mul_denominator,map_mul,hprime]
      using congrArg (fun z : ℂ => ringComplex (symbol x (p i))*z) ih

lemma sexticRow_star_square (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (x : O) :
    star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S x ^ 2) =
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S x ^ 4 := by
  simp only [primeSubsetRow,←Finset.prod_pow,star_prod]
  apply Finset.prod_congr rfl
  intro i _
  let χ := complexSexticChar (Ideal.span {p i}) (hg i)
  have he : (χ ^ 2)⁻¹ = χ ^ 4 := by
    calc
      _ = χ ^ 4*(χ ^ 6)⁻¹ := by group
      _ = _ := by rw [(complexSexticChar_powers (Ideal.span {p i}) (hg i)).2.2,inv_one,mul_one]
  change star (χ (Ideal.Quotient.mk (Ideal.span {p i}) x) ^ 2) =
    χ (Ideal.Quotient.mk (Ideal.span {p i}) x) ^ 4
  rw [←MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0),MulChar.star_apply',he,
    MulChar.pow_apply' _ (by decide : (4 : ℕ) ≠ 0)]

/-- Normalized cubic Gauss coefficient with the inverse angular factor. -/
def secondColumnCoefficient (p : ι → O) (S : Finset ι) : ℂ :=
  star (ringComplex (∏ i ∈ S, p i)/(‖ringComplex (∏ i ∈ S, p i)‖ : ℂ))*
    normalizedCubicUnitGauss (∏ i ∈ S, p i)

lemma secondColumnCoefficient_norm_one (p : ι → O) (hp : ∀ i, Prime (p i))
    (hprimary : ∀ i, lambda ^ 2 ∣ p i-1) (hcop : Pairwise (Function.onFun IsCoprime p))
    (S : Finset ι) : ‖secondColumnCoefficient p S‖ = 1 := by
  have hn : ‖ringComplex (∏ i ∈ S, p i)‖ ≠ 0 := norm_ne_zero_iff.mpr
    (ringComplex_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)))
  rw [secondColumnCoefficient,norm_mul,norm_star,norm_div,Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _),div_self hn,
    normalizedCubicUnitGauss_prime_product_norm S p (fun i _ => hp i) (fun i _ => hprimary i)
      (fun i _ j _ hij => hcop hij),one_mul]

/-- Cubic reciprocity makes the cross coefficient the fourth power of a sextic row. -/
lemma secondColumnCoefficient_union (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i-1) (hcop : Pairwise (Function.onFun IsCoprime p))
    (S T : Finset ι) (hd : Disjoint S T) :
    secondColumnCoefficient p (S ∪ T) = secondColumnCoefficient p S*secondColumnCoefficient p T*
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T (∏ i ∈ S, p i) ^ 4 := by
  have ha : (∏ i ∈ S, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hb : (∏ i ∈ T, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hab : IsCoprime (∏ i ∈ S, p i) (∏ i ∈ T, p i) :=
    IsCoprime.prod_left (fun i hi => IsCoprime.prod_right (fun j hj => hcop
      (fun he => Finset.disjoint_left.mp hd hi (by simpa only [he] using hj))))
  have hG := congrArg star (normalizedCubicUnitGauss_coprime_product _ _ ha hb
    (primary_finset_product S p (fun i _ => hprimary i))
    (primary_finset_product T p (fun i _ => hprimary i)) hab)
  simp only [star_star,star_mul] at hG
  rw [←sexticRow_square_symbol p hg T (∏ i ∈ S, p i),sexticRow_star_square p hg] at hG
  simp only [secondColumnCoefficient,Finset.prod_union hd,map_mul,norm_mul,
    Complex.ofReal_mul,div_eq_mul_inv,mul_inv_rev,star_mul]
  rw [hG]
  ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)

lemma subsetMask_union (S T : Finset ι) (hd : Disjoint S T) (x : O) :
    primeCoprimeMask p (S ∪ T) x = primeCoprimeMask p S x*primeCoprimeMask p T x :=
  Finset.prod_union hd

lemma subsetRow_mul (S : Finset ι) (x y : O) :
    primeSubsetRow p χ S (x*y) = primeSubsetRow p χ S x*primeSubsetRow p χ S y := by
  simp only [primeSubsetRow,map_mul,Finset.prod_mul_distrib]

include χ in
lemma subsetMask_mul (S : Finset ι) (x y : O) :
    primeCoprimeMask p S (x*y) = primeCoprimeMask p S x*primeCoprimeMask p S y := by
  rw [←primeSubsetRow_diagonal p χ S (x*y),subsetRow_mul p χ,
    ←primeSubsetRow_diagonal p χ S x,←primeSubsetRow_diagonal p χ S y,star_mul]
  ring

lemma mask_star_row (S : Finset ι) (e : O) :
    primeCoprimeMask p S e*star (primeSubsetRow p χ S e) = star (primeSubsetRow p χ S e) := by
  rw [primeCoprimeMask_indicator]
  split_ifs with h
  · exact one_mul _
  · push_neg at h
    obtain ⟨i,hi,hd⟩ := h
    have hz : primeSubsetRow p χ S e = 0 := by
      apply Finset.prod_eq_zero hi
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd),MulChar.map_zero]
    rw [hz,star_zero,mul_zero]

variable (hg : ∀ i, lambda ∉ Ideal.span {p i})

lemma sexticRow_star (S : Finset ι) (x : O) :
    star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S x) =
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S x ^ 5 := by
  simp only [primeSubsetRow,star_prod,←Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  let χ := complexSexticChar (Ideal.span {p i}) (hg i)
  have he : χ⁻¹ = χ ^ 5 := by
    calc
      _ = χ ^ 5*(χ ^ 6)⁻¹ := by group
      _ = _ := by rw [(complexSexticChar_powers (Ideal.span {p i}) (hg i)).2.2,inv_one,mul_one]
  change star (χ (Ideal.Quotient.mk (Ideal.span {p i}) x)) =
    χ (Ideal.Quotient.mk (Ideal.span {p i}) x) ^ 5
  rw [MulChar.star_apply',he,MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0)]

/-- The inverse sextic argument becomes a fourth-power label and one ordinary row factor. -/
lemma second_child_masked (S : Finset ι) (m r c d e k v : O) :
    primeCoprimeMask p S (m*(e*r))*
      star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S e)*
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S d*
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S k*
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S c ^ 4*
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S v ^ 4 =
    primeCoprimeMask p S (m*r)*
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (d*e*k)*
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (c*e*v) ^ 4 := by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  have hm := mask_star_row p χ S e
  rw [subsetMask_mul p χ S m (e*r),subsetMask_mul p χ S e r,subsetMask_mul p χ S m r]
  calc
    _ = (primeCoprimeMask p S m*primeCoprimeMask p S r)*
        (primeCoprimeMask p S e*star (primeSubsetRow p χ S e))*
        primeSubsetRow p χ S d*primeSubsetRow p χ S k*
        primeSubsetRow p χ S c ^ 4*primeSubsetRow p χ S v ^ 4 := by ring
    _ = _ := by
      rw [hm,sexticRow_star p hg]
      simp only [subsetRow_mul,mul_pow]
      ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondPreColumn (Ψ : O →* ℂ) (m c d e k : O)
    (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  secondColumnCoefficient p S * Ψ (∏ i ∈ S, p i) *
    primeCoprimeMask p S m *
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S c ^ 4 *
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S d *
    star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S e) *
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S k * H S

def secondChildColumn (Ψ : O →* ℂ) (m f y : O)
    (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  secondColumnCoefficient p S * Ψ (∏ i ∈ S, p i) *
    primeCoprimeMask p S m *
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S f ^ 4 *
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S y * H S

theorem secondPreColumn_union (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m r c d e k : O) (H : Finset ι → ℂ)
    (V N : Finset ι) (hd : Disjoint V N) :
    secondPreColumn p hg Ψ (m * (e * r)) c d e k H (V ∪ N) =
      secondPreColumn p hg Ψ (m * (e * r)) c d e k (fun _ => 1) V *
      secondChildColumn p hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
        (fun U => H (V ∪ U)) N := by
  have hA := secondColumnCoefficient_union p hp hg hpr hcop V N hd
  have hrow := second_child_masked p hg N m r c d e k (∏ i ∈ V, p i)
  simp only [secondPreColumn, secondChildColumn, hA, Finset.prod_union hd,
    map_mul, primeSubsetRow_union p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) V N hd, subsetMask_union p V N hd,
    mul_pow, star_mul, mul_one]
  calc
    _ = (secondColumnCoefficient p V * Ψ (∏ i ∈ V, p i) *
      primeCoprimeMask p V (m * (e * r)) *
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) V c ^ 4 *
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) V d *
      star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) V e) *
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) V k) *
      (secondColumnCoefficient p N * Ψ (∏ i ∈ N, p i) *
        (primeCoprimeMask p N (m * (e * r)) *
          star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) N e) *
          primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) N d *
          primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) N k *
          primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) N c ^ 4 *
          primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) N (∏ i ∈ V, p i) ^ 4) *
        H (V ∪ N)) := by ring
    _ = _ := by rw [hrow]; ring


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondSeparatedPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset,
    if Disjoint S T then
      star (secondPreColumn p hg Ψ₁ (m * (e * r)) c d e k₁ H₁ S) *
        secondPreColumn p hg Ψ₂ (m * (e * r)) c d e k₂ H₂ T
    else 0

def secondCommonWeight (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O) (V : Finset ι) : ℂ :=
  supportMobius V *
    star (secondPreColumn p hg Ψ₁ (m * (e * r)) c d e k₁ (fun _ => 1) V) *
      secondPreColumn p hg Ψ₂ (m * (e * r)) c d e k₂ (fun _ => 1) V

def secondChildSum (F V : Finset ι) (Ψ : O →* ℂ)
    (m r c d e k : O) (H : Finset ι → ℂ) : ℂ :=
  ∑ N ∈ (F \ V).powerset,
    secondChildColumn p hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
      (fun U => H (V ∪ U)) N

theorem secondSeparatedPair_eq_children (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (H₁ H₂ : Finset ι → ℂ) :
    secondSeparatedPair p hg F Ψ₁ Ψ₂ m r c d e k₁ k₂ H₁ H₂ =
      ∑ V ∈ F.powerset, secondCommonWeight p hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
        star (secondChildSum p hg F V Ψ₁ m r c d e k₁ H₁) *
          secondChildSum p hg F V Ψ₂ m r c d e k₂ H₂ := by
  unfold secondSeparatedPair
  rw [CoprimeMobiusExtension.double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro V hV
  rw [secondCommonWeight, supportMobius]
  simp only [secondChildSum, star_sum, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N₁ hN₁
  apply Finset.sum_congr rfl
  intro N₂ hN₂
  have hdis₁ : Disjoint V N₁ := Finset.disjoint_left.mpr (fun i hi hn =>
    (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN₁) hn)).2 hi)
  have hdis₂ : Disjoint V N₂ := Finset.disjoint_left.mpr (fun i hi hn =>
    (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN₂) hn)).2 hi)
  rw [secondPreColumn_union p hg hp hcop hpr Ψ₁ m r c d e k₁ H₁ V N₁ hdis₁,
    secondPreColumn_union p hg hp hcop hpr Ψ₂ m r c d e k₂ H₂ V N₂ hdis₂,
    star_mul]
  ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondChildEnergy (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (H : Finset ι → ℂ) (negative : Bool) : ℝ :=
  ∑ V ∈ F.powerset, ‖secondCommonWeight p hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V‖ *
    ‖secondChildSum p hg F V (if negative then Ψ₁ else Ψ₂)
      m r c d e (if negative then k₁ else k₂) H‖ ^ 2

theorem secondSeparatedPair_norm_le (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (H₁ H₂ : Finset ι → ℂ) :
    ‖secondSeparatedPair p hg F Ψ₁ Ψ₂ m r c d e k₁ k₂ H₁ H₂‖ ≤
      Real.sqrt (secondChildEnergy p hg F Ψ₁ Ψ₂ m r c d e k₁ k₂ H₁ true) *
        Real.sqrt (secondChildEnergy p hg F Ψ₁ Ψ₂ m r c d e k₁ k₂ H₂ false) := by
  rw [secondSeparatedPair_eq_children p hg hp hcop hpr]
  have h := DescentWeightedCauchy.weighted_cauchy F.powerset
    (secondCommonWeight p hg Ψ₁ Ψ₂ m r c d e k₁ k₂)
    (fun V => secondChildSum p hg F V Ψ₂ m r c d e k₂ H₂)
    (fun V => secondChildSum p hg F V Ψ₁ m r c d e k₁ H₁)
  simp only [secondChildEnergy, ite_true, Bool.false_eq_true, ite_false]
  convert h using 1
  · congr 2
    funext V
    ring
  · ring

end SecondPassArithmetic

namespace SchwartzPlanePoisson
open Eisenstein CubicJacobi
open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

lemma primeCubicRow_symbol (x : O) :
    (∏ i, complexCubicChar (Ideal.span {p i}) (hg i)
      (Ideal.Quotient.mk (Ideal.span {p i}) x)) = ringComplex (symbol x (∏ i, p i)) := by
  have h := SecondPassArithmetic.sexticRow_square_symbol p hg Finset.univ x
  simp only [primeSubsetRow,←Finset.prod_pow] at h
  simp_rw [←MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0),
    (complexSexticChar_powers _ _).1] at h
  exact h

include hinj in
/-- The cubic CRT Gauss sum equals the existing sum over invertible residues. -/
theorem primeRowTraceGauss_cubic :
    primeRowTraceGauss p hp (fun i => complexCubicChar (Ideal.span {p i}) (hg i)) =
      cubicUnitGaussSum 1 (∏ i, p i) := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let e := primeProductCRT p hinj
  let χ := fun i => complexCubicChar (Ideal.span {p i}) (hg i)
  let A : O ⧸ Ideal.span {c} → ℂ := fun x =>
    (∏ i, χ i (e x i))*residueTraceQuotientChar 1 c hc x
  have hs : Function.support A ⊆ {x | IsUnit x} := by
    intro x hx
    have hn : ∀ i, e x i ≠ 0 := by
      intro i hi
      have hz : (∏ j, χ j (e x j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi,MulChar.map_zero])
      apply hx
      change (∏ j, χ j (e x j))*residueTraceQuotientChar 1 c hc x = 0
      rw [hz,zero_mul]
    have hu : IsUnit (e x) := ⟨
      { val := e x
        inv := fun i => (e x i)⁻¹
        val_inv := by funext i; exact mul_inv_cancel₀ (hn i)
        inv_val := by funext i; exact inv_mul_cancel₀ (hn i) },rfl⟩
    have hu' := hu.map e.symm.toMonoidHom
    change IsUnit (e.symm (e x)) at hu'
    rwa [e.symm_apply_apply] at hu'
  rw [primeRowTraceGauss_eq_crt p hp hinj]
  change (∑ x, A x) = _
  trans ∑' x : O ⧸ Ideal.span {c}, A x
  · exact (tsum_fintype A).symm
  rw [←tsum_subtype_eq_of_support_subset hs,cubicUnitGaussSum]
  apply tsum_congr
  intro x
  have hx := principalResidueRep_spec c x.val
  have hr (z : O) : (∏ i, χ i (e (Ideal.Quotient.mk (Ideal.span {c}) z) i)) =
      ringComplex (symbol z c) := by
    change (∏ i, complexCubicChar (Ideal.span {p i}) (hg i)
      (primeProductCRT p hinj (Ideal.Quotient.mk (Ideal.span {∏ i, p i}) z) i)) =
        ringComplex (symbol z (∏ i, p i))
    simp only [primeProductCRT_mk]
    exact primeCubicRow_symbol p hg z
  change (∏ i, χ i (e x.val i))*residueTraceQuotientChar 1 c hc x.val = _
  conv_lhs => rw [←hx]
  rw [hr,residueTraceQuotientChar_mk]

end SchwartzPlanePoisson

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The finite phase left after removing the angular factor from Möbius conversion. -/
def secondTraceRayFactor : ℂ :=
  (∏ i, complexSexticChar (Ideal.span {p i}) (hg i) (4 : O ⧸ Ideal.span {p i}))/
    QuadraticPhase.Eisenstein.fixedDualAverage (∏ i, p i)

/-- Signed, normalized sextic reflection restores the cubic column coefficient. -/
theorem primeRowTraceGauss_mobius_conversion (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i-1) :
    ((-1 : ℂ) ^ Fintype.card ι*
      star (primeRowTraceGauss p hp (fun i => complexSexticChar (Ideal.span {p i}) (hg i))))/
        (‖ringComplex (∏ i, p i)‖ : ℂ) =
      secondTraceRayFactor p hg*secondColumnCoefficient p Finset.univ := by
  let c := ∏ i, p i
  let n : ℂ := ‖ringComplex c‖
  let Z := ∏ i, complexSexticChar (Ideal.span {p i}) (hg i) (4 : O ⧸ Ideal.span {p i})
  let G₁ := primeRowTraceGauss p hp (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
  let G₂ := primeRowTraceGauss p hp (fun i => complexCubicChar (Ideal.span {p i}) (hg i))
  let G₃ := primeRowTraceGauss p hp (fun i => complexQuadraticChar (Ideal.span {p i}))
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hcC : ringComplex c ≠ 0 := ringComplex_ne_zero hc
  have hn : n ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hcC)
  have hG₃ : G₃ ≠ 0 := primeRowTraceGauss_ne_zero p hp hinj _
    (fun i => complexQuadraticChar_ne_one _ (hodd i))
  have hprod : Z*G₁*G₂ = (-1 : ℂ) ^ Fintype.card ι*ringComplex c*G₃ :=
    primeRowTraceGauss_sextic_product p hp hinj hg hodd hpr
  have hnorm := (prime_row_trace_poisson p hp hinj _
    (fun i => complexSexticChar_ne_one _ (hg i))).1
  have hmass : G₁*star G₁ = n ^ 2 := by
    rw [←starRingEnd_apply,Complex.mul_conj']
    dsimp only [n,G₁,c]
    exact_mod_cast hnorm
  have hconverted : (-1 : ℂ) ^ Fintype.card ι*star G₁ =
      (Z*n ^ 2/(ringComplex c*G₃))*G₂ := by
    apply mul_left_cancel₀ (mul_ne_zero hcC hG₃)
    calc
      _ = ((-1 : ℂ) ^ Fintype.card ι*ringComplex c*G₃)*star G₁ := by ring
      _ = (Z*G₁*G₂)*star G₁ := by rw [hprod]
      _ = Z*(G₁*star G₁)*G₂ := by ring
      _ = _ := by rw [hmass]; field_simp
  have hquad : G₃ = n*QuadraticPhase.Eisenstein.fixedDualAverage c :=
    primeRowTraceGauss_quadratic p hp hinj hodd
  have hphase : QuadraticPhase.Eisenstein.fixedDualAverage c ≠ 0 := by
    intro hz
    apply hG₃
    rw [hquad,hz,mul_zero]
  have hcstar : ringComplex c*star (ringComplex c) = n ^ 2 := by
    rw [←starRingEnd_apply,Complex.mul_conj']
  have hangle : star (ringComplex c/n) = n/ringComplex c := by
    have hnstar : star n = n := Complex.conj_ofReal _
    apply (eq_div_iff hcC).mpr
    change (starRingEnd ℂ) (ringComplex c/n)*ringComplex c = n
    change (starRingEnd ℂ) n = n at hnstar
    rw [map_div₀,hnstar]
    field_simp [hn]
    simpa only [pow_two,mul_comm,starRingEnd_apply] using hcstar
  change ((-1 : ℂ) ^ Fintype.card ι*star G₁)/n = _
  have hcubic : G₂ = cubicUnitGaussSum 1 c := primeRowTraceGauss_cubic p hp hinj hg
  rw [hconverted,hquad,hcubic]
  change (Z*n ^ 2/(ringComplex c*(n*QuadraticPhase.Eisenstein.fixedDualAverage c)))*
      cubicUnitGaussSum 1 c/n =
    (Z/QuadraticPhase.Eisenstein.fixedDualAverage c)*
      (star (ringComplex c/n)*(cubicUnitGaussSum 1 c/n))
  rw [hangle]
  field_simp [hn,hcC,hphase]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson CubicJacobi
open scoped Classical

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

lemma subsetRow_mul_star_of_coprime
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S : Finset ι) (z : O)
    (hz : IsCoprime (∏ i ∈ S, p i) z) :
    primeSubsetRow p χ S z*star (primeSubsetRow p χ S z) = 1 := by
  rw [mul_comm,primeSubsetRow_diagonal,primeCoprimeMask_indicator]
  apply if_pos
  intro i hi hdiv
  have hu := hz.isUnit_of_dvd' (Finset.dvd_prod_of_mem p hi) hdiv
  exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top
    (Ideal.span_singleton_eq_top.mpr hu)

variable (hg : ∀ i, lambda ∉ Ideal.span {p i})

lemma sexticRow_cube (S : Finset ι) (z : O) :
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S z ^ 3 =
      primeSubsetRow p (fun i => complexQuadraticChar (Ideal.span {p i})) S z := by
  simp only [primeSubsetRow,←Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [←MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0),
    (complexSexticChar_powers _ _).2.1]

/-- Cubic reciprocity leaves only the quadratic cross phase in a mixed sextic product. -/
theorem sexticRow_cross_phase (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i-1) (S T : Finset ι) (hd : Disjoint S T) :
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (∏ i ∈ T, p i)*
      star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T (∏ i ∈ S, p i)) =
    rayQuadraticPair (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i))
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ T, p i)) := by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  let a := primeSubsetRow p χ S (∏ i ∈ T, p i)
  let b := primeSubsetRow p χ T (∏ i ∈ S, p i)
  have hcop := prime_subsets_coprime p hinj S T hd
  have hb : b*star b = 1 := subsetRow_mul_star_of_coprime p χ T _ hcop.symm
  have hsquare : a ^ 2 = b ^ 2 := by
    change primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S
      (∏ i ∈ T, p i) ^ 2 =
        primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T (∏ i ∈ S, p i) ^ 2
    rw [sexticRow_square_symbol p hg,sexticRow_square_symbol p hg]
    rw [symbol_reciprocity _ _
      (primary_finset_product T p (fun i _ => hpr i))
      (primary_finset_product S p (fun i _ => hpr i))]
  have ha3 : a ^ 3 = quadraticSubsetSymbol p S T := sexticRow_cube p hg S _
  have hb3 : b ^ 3 = quadraticSubsetSymbol p T S := sexticRow_cube p hg T _
  have hq : quadraticSubsetSymbol p T S ^ 2 = 1 := quadraticSubsetRow_sq p T _ hcop.symm
  change a*star b = _
  calc
    _ = (a*star b)*(b*star b) ^ 2 := by rw [hb,one_pow,mul_one]
    _ = a ^ 3*star b ^ 3 := by rw [mul_pow,←hsquare]; ring
    _ = quadraticSubsetSymbol p S T*quadraticSubsetSymbol p T S := by
      rw [ha3,←star_pow,hb3,quadraticSubsetSymbol_star]
    _ = _ := by
      rw [quadraticSubsetSymbol_reciprocity p hp hinj hodd S T,mul_assoc,
        ←pow_two,hq,mul_one,rayQuadraticPair_mk]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

/-- Möbius conversion contributes a factor of modulus one. -/
theorem secondTraceRayFactor_norm_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    ‖secondTraceRayFactor p hg‖ = 1 := by
  have hv (i : ι) : ‖complexSexticChar (Ideal.span {p i}) (hg i) (4 : O ⧸ Ideal.span {p i})‖ = 1 := by
    have htwo : (2 : O ⧸ Ideal.span {p i}) ≠ 0 := Ring.two_ne_zero (hodd i)
    have hfour : (4 : O ⧸ Ideal.span {p i}) ≠ 0 := by
      convert pow_ne_zero 2 htwo using 1
      norm_num
    apply Complex.norm_eq_one_of_pow_eq_one (n := 6) _ (by decide)
    rw [←MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0),
      (complexSexticChar_powers _ _).2.2]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hfour)
  rw [secondTraceRayFactor,norm_div,norm_prod,prime_quadratic_phase_norm p hp hinj hodd]
  simp only [hv,Finset.prod_const_one,div_one]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def subsetTraceGauss (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S : Finset ι) : ℂ :=
  primeRowTraceGauss (fun i : S => p i.val) (fun i => hp i.val) (fun i => χ i.val)

def subsetTraceRayFactor (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) : ℂ :=
  secondTraceRayFactor (fun i : S => p i.val) (fun i => hg i.val)

theorem subsetTraceGauss_eq_residueRowGauss
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S : Finset ι) :
    subsetTraceGauss p hp χ S = residueRowGauss (∏ i ∈ S, p i)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) (primeSubsetRow p χ S) := by
  have hf : (primeCuspRowCharacter (fun i : S => p i.val) (fun i => χ i.val) : O → ℂ) =
      primeSubsetRow p χ S := funext (primeCuspRowCharacter_restrict p χ S)
  have h := primeRowTraceGauss_eq_residueRowGauss (fun i : S => p i.val)
    (fun i => hp i.val) (fun i => χ i.val)
  rw [hf] at h
  simpa only [subsetTraceGauss,Finset.prod_coe_sort] using h

theorem subsetTraceGauss_inverse
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S : Finset ι) :
    subsetTraceGauss p hp (fun i => (χ i)⁻¹) S =
      primeSubsetRow p χ S (-1)*star (subsetTraceGauss p hp χ S) := by
  simpa only [subsetTraceGauss,primeCuspRowCharacter_restrict] using
    primeRowTraceGauss_inverse (fun i : S => p i.val) (fun i => hp i.val)
      (hinj.comp Subtype.val_injective) (fun i => χ i.val)

theorem subsetTraceGauss_mobius_conversion
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i-1) (S : Finset ι) :
    supportMobius S*star (subsetTraceGauss p hp
      (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S)/
        (‖ringComplex (∏ i ∈ S, p i)‖ : ℂ) =
      subsetTraceRayFactor p hg S*secondColumnCoefficient p S := by
  simpa only [supportMobius,subsetTraceGauss,subsetTraceRayFactor,
    secondColumnCoefficient,Finset.prod_coe_sort,Fintype.card_coe] using
    primeRowTraceGauss_mobius_conversion (fun i : S => p i.val) (fun i => hg i.val)
      (fun i => hp i.val) (hinj.comp Subtype.val_injective) (fun i => hodd i.val)
      (fun i => hpr i.val)

include hp in
theorem subsetTraceRayFactor_norm_one
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    ‖subsetTraceRayFactor p hg S‖ = 1 :=
  secondTraceRayFactor_norm_one (fun i : S => p i.val) (fun i => hp i.val)
    (hinj.comp Subtype.val_injective) (fun i => hg i.val) (fun i => hodd i.val)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)

lemma primeSubsetRow_congr (S : Finset ι) (x y : O)
    (h : (∏ i ∈ S, p i) ∣ x-y) : primeSubsetRow p χ S x = primeSubsetRow p χ S y := by
  have h' := primeCuspRowCharacter_congr (fun i : S => p i.val)
    (fun i => χ i.val) x y (by simpa only [Finset.prod_coe_sort] using h)
  simpa only [primeCuspRowCharacter_restrict] using h'

include hinj in
/-- CRT splits a mixed row into its two exact Gauss factors and reciprocal row values. -/
theorem mixed_subset_traceGauss_split (S T : Finset ι) (hd : Disjoint S T) :
    residueRowGauss ((∏ i ∈ S, p i)*(∏ i ∈ T, p i))
      (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
        (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))
      (fun z => primeSubsetRow p χ S z*star (primeSubsetRow p χ T z)) =
    primeSubsetRow p χ S (∏ i ∈ T, p i)*star (primeSubsetRow p χ T (∏ i ∈ S, p i))*
      subsetTraceGauss p hp χ S*
      (primeSubsetRow p χ T (-1)*star (subsetTraceGauss p hp χ T)) := by
  let c := ∏ i ∈ S, p i
  let d := ∏ i ∈ T, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let A := primeCuspRowCharacter (fun i : S => p i.val) (fun i => χ i.val)
  let B := (starRingEnd ℂ).toMonoidHom.comp
    (primeCuspRowCharacter (fun i : T => p i.val) (fun i => χ i.val))
  have hA (z : O) : A z = primeSubsetRow p χ S z := primeCuspRowCharacter_restrict p χ S z
  have hB (z : O) : B z = star (primeSubsetRow p χ T z) := by
    change star (primeCuspRowCharacter (fun i : T => p i.val) (fun i => χ i.val) z) = _
    rw [primeCuspRowCharacter_restrict]
  have hBi (z : O) : B z = primeSubsetRow p (fun i => (χ i)⁻¹) T z := by
    rw [hB]
    simp only [primeSubsetRow,star_prod,MulChar.star_apply']
  have hAc (x y : O) (h : c ∣ x-y) : A x = A y := by
    rw [hA,hA]
    exact primeSubsetRow_congr p χ S x y h
  have hBd (x y : O) (h : d ∣ x-y) : B x = B y := by
    rw [hB,hB,primeSubsetRow_congr p χ T x y h]
  have ha : residueRowGauss c hc A = subsetTraceGauss p hp χ S := by
    rw [show (A : O → ℂ) = primeSubsetRow p χ S from funext hA]
    exact (subsetTraceGauss_eq_residueRowGauss p hp χ S).symm
  have hb : residueRowGauss d hd0 B = subsetTraceGauss p hp (fun i => (χ i)⁻¹) T := by
    rw [show (B : O → ℂ) = primeSubsetRow p (fun i => (χ i)⁻¹) T from funext hBi]
    exact (subsetTraceGauss_eq_residueRowGauss p hp (fun i => (χ i)⁻¹) T).symm
  have hAB : ((A : O → ℂ)*B) = fun z => primeSubsetRow p χ S z*star (primeSubsetRow p χ T z) := by
    funext z
    change A z*B z = _
    rw [hA,hB]
  have h := residueRowGauss_mul c d hc hd0 (prime_subsets_coprime p hinj S T hd) A B hAc hBd
  rw [hAB,ha,hb,subsetTraceGauss_inverse p hp hinj χ T,hA,hB] at h
  exact h

/-- The active prime character used by Poisson is the same mixed CRT row. -/
theorem active_traceGauss_eq_mixed (S T : Finset ι) (hd : Disjoint S T) :
    primeRowTraceGauss (fun i : ↥((T \ S) ∪ (S \ T)) => p i.val)
      (fun i => hp i.val) (activePrimeRowCharacter p χ T S) =
    residueRowGauss ((∏ i ∈ S, p i)*(∏ i ∈ T, p i))
      (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
        (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))
      (fun z => primeSubsetRow p χ S z*star (primeSubsetRow p χ T z)) := by
  have hn : (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val) =
      (∏ i ∈ S, p i)*(∏ i ∈ T, p i) := by
    rw [Finset.prod_coe_sort,Finset.sdiff_eq_self_of_disjoint hd.symm,
      Finset.sdiff_eq_self_of_disjoint hd,Finset.prod_union hd.symm,mul_comm]
  have hr : (primeCuspRowCharacter (fun i : ↥((T \ S) ∪ (S \ T)) => p i.val)
      (activePrimeRowCharacter p χ T S) : O → ℂ) =
      fun z => primeSubsetRow p χ S z*star (primeSubsetRow p χ T z) := by
    funext z
    have h := primeSubsetRow_pair_active p χ T S z
    rw [Finset.disjoint_iff_inter_eq_empty.mp hd.symm] at h
    simp only [primeCoprimeMask,Finset.prod_empty,one_mul] at h
    exact h.symm.trans (mul_comm _ _)
  rw [primeRowTraceGauss_eq_residueRowGauss,hr]
  congr 1

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hpr : ∀ i, lambda ^ 2 ∣ p i-1)

include hinj hodd hpr in
/-- The two Möbius signs restore cubic columns; only a finite quadratic cross phase remains. -/
theorem mixed_traceGauss_restoration (S T : Finset ι) (hd : Disjoint S T) :
    let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
    supportMobius S*supportMobius T*
      primeRowTraceGauss (fun i : ↥((T \ S) ∪ (S \ T)) => p i.val)
        (fun i => hp i.val) (activePrimeRowCharacter p χ T S)/
      ((‖ringComplex (∏ i ∈ S, p i)‖ : ℂ)*(‖ringComplex (∏ i ∈ T, p i)‖ : ℂ)) =
    rayQuadraticPair (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i))
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ T, p i))*
      star (subsetTraceRayFactor p hg S*secondColumnCoefficient p S)*
      (subsetTraceRayFactor p hg T*secondColumnCoefficient p T)*primeSubsetRow p χ T (-1) := by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  dsimp only
  have hs := subsetTraceGauss_mobius_conversion p hp hinj hg hodd hpr S
  have ht := subsetTraceGauss_mobius_conversion p hp hinj hg hodd hpr T
  have hsstar : supportMobius S*subsetTraceGauss p hp χ S/
      (‖ringComplex (∏ i ∈ S, p i)‖ : ℂ) =
      star (subsetTraceRayFactor p hg S*secondColumnCoefficient p S) := by
    have h := congrArg (starRingEnd ℂ) hs
    rw [map_div₀,map_mul,Complex.conj_ofReal] at h
    simpa only [starRingEnd_apply,star_supportMobius,star_star] using h
  rw [active_traceGauss_eq_mixed p hp χ S T hd,
    mixed_subset_traceGauss_split p hp hinj χ S T hd,
    sexticRow_cross_phase p hg hp hinj hodd hpr S T hd]
  calc
    _ = rayQuadraticPair (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i))
        (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ T, p i))*
      (supportMobius S*subsetTraceGauss p hp χ S/(‖ringComplex (∏ i ∈ S, p i)‖ : ℂ))*
      (supportMobius T*star (subsetTraceGauss p hp χ T)/(‖ringComplex (∏ i ∈ T, p i)‖ : ℂ))*
      primeSubsetRow p χ T (-1) := by ring
    _ = _ := by rw [hsstar,ht]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The exact normalized mixed Gauss factor with its divisor and dual-row arguments. -/
def secondNormalizedGaussTerm (S T : Finset ι) (e k : O) : ℂ :=
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  let ap : ↥((T \ S) ∪ (S \ T)) → O := fun i => p i.val
  let ac := activePrimeRowCharacter p χ T S
  primeRowTraceGauss ap (fun i => hp i.val) ac/
      ((‖ringComplex (∏ i ∈ S, p i)‖ : ℂ)*(‖ringComplex (∏ i ∈ T, p i)‖ : ℂ))*
    primeCuspRowCharacter ap ac e*primeCuspRowCharacter ap (fun i => (ac i)⁻¹) k

theorem secondGaussTerm_restoration
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i-1)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d e k : O) (H₁ H₂ : Finset ι → ℂ)
    (S T : Finset ι) (hd : Disjoint S T) :
    let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
    star (supportMobius S*secondInputCoefficient p χ Ψ₁ m c d H₁ S)*
      (supportMobius T*secondInputCoefficient p χ Ψ₂ m c d H₂ T)*
      secondNormalizedGaussTerm p hp hg S T e k =
    rayQuadraticPair (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i))
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ T, p i))*
      star (secondPreColumn p hg Ψ₁ m c d e k
        (fun U => subsetTraceRayFactor p hg U*H₁ U) S)*
      secondPreColumn p hg Ψ₂ m c d e (-k)
        (fun U => subsetTraceRayFactor p hg U*H₂ U) T := by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  let ap : ↥((T \ S) ∪ (S \ T)) → O := fun i => p i.val
  let ac := activePrimeRowCharacter p χ T S
  have hr (z : O) : primeCuspRowCharacter ap ac z =
      star (primeSubsetRow p χ T z)*primeSubsetRow p χ S z := by
    have h := primeSubsetRow_pair_active p χ T S z
    rw [Finset.disjoint_iff_inter_eq_empty.mp hd.symm] at h
    simpa only [primeCoprimeMask,Finset.prod_empty,one_mul] using h.symm
  have hi (z : O) : primeCuspRowCharacter ap (fun i => (ac i)⁻¹) z =
      star (primeCuspRowCharacter ap ac z) := by
    change (∏ i, (ac i)⁻¹ (Ideal.Quotient.mk (Ideal.span {ap i}) z)) =
      star (∏ i, ac i (Ideal.Quotient.mk (Ideal.span {ap i}) z))
    simp only [star_prod,MulChar.star_apply']
  have hk : primeSubsetRow p χ T (-k) =
      primeSubsetRow p χ T (-1)*primeSubsetRow p χ T k := by
    simpa only [neg_one_mul] using subsetRow_mul p χ T (-1) k
  have hrestore := mixed_traceGauss_restoration p hp hinj hg hodd hpr S T hd
  dsimp only at hrestore ⊢
  let C₁ := secondInputCoefficient p χ Ψ₁ m c d H₁ S
  let C₂ := secondInputCoefficient p χ Ψ₂ m c d H₂ T
  calc
    _ = (supportMobius S*supportMobius T*primeRowTraceGauss ap (fun i => hp i.val) ac/
        ((‖ringComplex (∏ i ∈ S, p i)‖ : ℂ)*(‖ringComplex (∏ i ∈ T, p i)‖ : ℂ)))*
      star C₁*C₂*primeCuspRowCharacter ap ac e*
        primeCuspRowCharacter ap (fun i => (ac i)⁻¹) k := by
      simp only [secondNormalizedGaussTerm,star_mul,star_supportMobius]
      dsimp only [C₁,C₂,ap,ac,χ]
      ring
    _ = _ := by
      rw [hrestore,hi,hr,hr]
      simp only [secondPreColumn,secondInputCoefficient,C₁,C₂,star_mul,star_star]
      dsimp only [χ] at hk ⊢
      rw [hk]
      ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- A residue mask absorbs the remaining unit phase into the freely weighted column. -/
def secondRayMask (r : QuadraticRayRing) (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  if Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i) = r
  then subsetTraceRayFactor p hg S*H S else 0

theorem secondRayMask_norm_le (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (r : QuadraticRayRing) (H : Finset ι → ℂ) (S : Finset ι) :
    ‖secondRayMask p hg r H S‖ ≤ ‖H S‖ := by
  unfold secondRayMask
  split_ifs
  · rw [norm_mul,subsetTraceRayFactor_norm_one p hp hinj hg hodd S,one_mul]
  · rw [norm_zero]
    exact norm_nonneg _

lemma secondPreColumn_rayMask (r : QuadraticRayRing) (Ψ : O →* ℂ)
    (m c d e k : O) (H : Finset ι → ℂ) (S : Finset ι) :
    secondPreColumn p hg Ψ m c d e k (secondRayMask p hg r H) S =
      if Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i) = r then
        secondPreColumn p hg Ψ m c d e k (fun U => subsetTraceRayFactor p hg U*H U) S
      else 0 := by
  by_cases h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i) = r
  · simp only [secondPreColumn,secondRayMask,if_pos h]
  · simp only [secondPreColumn,secondRayMask,if_neg h,mul_zero]

/-- Two fixed residue classes separate the entire mixed Gauss coefficient. -/
theorem secondGaussTerm_residue_separation (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i-1)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d e k : O) (H₁ H₂ : Finset ι → ℂ)
    (S T : Finset ι) (hd : Disjoint S T) :
    let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
    star (supportMobius S*secondInputCoefficient p χ Ψ₁ m c d H₁ S)*
      (supportMobius T*secondInputCoefficient p χ Ψ₂ m c d H₂ T)*
      secondNormalizedGaussTerm p hp hg S T e k =
    ∑ z : QuadraticRayRing × QuadraticRayRing, rayQuadraticPair z.1 z.2*
      star (secondPreColumn p hg Ψ₁ m c d e k (secondRayMask p hg z.1 H₁) S)*
      secondPreColumn p hg Ψ₂ m c d e (-k) (secondRayMask p hg z.2 H₂) T := by
  dsimp only
  rw [secondGaussTerm_restoration p hp hg hinj hodd hpr Ψ₁ Ψ₂ m c d e k H₁ H₂ S T hd]
  simp only [Fintype.sum_prod_type,secondPreColumn_rayMask]
  have hstar (P : Prop) [Decidable P] (a : ℂ) :
      star (if P then a else 0) = if P then star a else 0 := by
    split_ifs <;> simp only [star_zero]
  simp only [hstar,mul_ite,ite_mul,mul_zero,zero_mul]
  simp

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The normalized arithmetic pair appearing in the second Poisson reflection. -/
def secondActualPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    star (supportMobius S*secondInputCoefficient p χ Ψ₁ (m*(e*r)) c d H₁ S)*
      (supportMobius T*secondInputCoefficient p χ Ψ₂ (m*(e*r)) c d H₂ T)*
      secondNormalizedGaussTerm p hp hg S T e k else 0

theorem secondActualPair_eq_separated
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i-1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (H₁ H₂ : Finset ι → ℂ) :
    secondActualPair p hp hg F Ψ₁ Ψ₂ m r c d e k H₁ H₂ =
      ∑ z : QuadraticRayRing × QuadraticRayRing, rayQuadraticPair z.1 z.2*
        secondSeparatedPair p hg F Ψ₁ Ψ₂ m r c d e k (-k)
          (secondRayMask p hg z.1 H₁) (secondRayMask p hg z.2 H₂) := by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  have hh (S T : Finset ι) :
      (if Disjoint S T then
        star (supportMobius S*secondInputCoefficient p χ Ψ₁ (m*(e*r)) c d H₁ S)*
          (supportMobius T*secondInputCoefficient p χ Ψ₂ (m*(e*r)) c d H₂ T)*
          secondNormalizedGaussTerm p hp hg S T e k else 0) =
      ∑ z : QuadraticRayRing × QuadraticRayRing, rayQuadraticPair z.1 z.2*
        (if Disjoint S T then
          star (secondPreColumn p hg Ψ₁ (m*(e*r)) c d e k (secondRayMask p hg z.1 H₁) S)*
            secondPreColumn p hg Ψ₂ (m*(e*r)) c d e (-k) (secondRayMask p hg z.2 H₂) T else 0) := by
    by_cases hd : Disjoint S T
    · simpa only [if_pos hd,mul_assoc] using
        secondGaussTerm_residue_separation p hg hp hinj hodd hpr Ψ₁ Ψ₂
          (m*(e*r)) c d e k H₁ H₂ S T hd
    · simp only [if_neg hd,mul_zero,Finset.sum_const_zero]
  dsimp only [χ] at hh
  unfold secondActualPair
  simp_rw [hh]
  calc
    _ = ∑ S ∈ F.powerset, ∑ z : QuadraticRayRing × QuadraticRayRing, ∑ T ∈ F.powerset,
        rayQuadraticPair z.1 z.2*(if Disjoint S T then
          star (secondPreColumn p hg Ψ₁ (m*(e*r)) c d e k (secondRayMask p hg z.1 H₁) S)*
            secondPreColumn p hg Ψ₂ (m*(e*r)) c d e (-k) (secondRayMask p hg z.2 H₂) T else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [secondSeparatedPair,Finset.mul_sum]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondTotalWeight (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (z : (QuadraticRayRing × QuadraticRayRing) × Finset ι) : ℂ :=
  rayQuadraticPair z.1.1 z.1.2*secondCommonWeight p hg Ψ₁ Ψ₂ m r c d e k (-k) z.2

def secondTotalEnergy (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : Finset ι → ℂ) (negative : Bool) : ℝ :=
  ∑ z : QuadraticRayRing × QuadraticRayRing, ∑ V ∈ F.powerset,
    ‖secondTotalWeight p hg Ψ₁ Ψ₂ m r c d e k (z,V)‖*
      ‖secondChildSum p hg F V (if negative then Ψ₁ else Ψ₂) m r c d e (if negative then k else -k)
        (secondRayMask p hg (if negative then z.1 else z.2) H)‖ ^ 2

theorem secondActualPair_eq_children (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i-1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (H₁ H₂ : Finset ι → ℂ) :
    secondActualPair p hp hg F Ψ₁ Ψ₂ m r c d e k H₁ H₂ =
      ∑ z : QuadraticRayRing × QuadraticRayRing, ∑ V ∈ F.powerset,
        secondTotalWeight p hg Ψ₁ Ψ₂ m r c d e k (z,V)*
          star (secondChildSum p hg F V Ψ₁ m r c d e k (secondRayMask p hg z.1 H₁))*
          secondChildSum p hg F V Ψ₂ m r c d e (-k) (secondRayMask p hg z.2 H₂) := by
  have hcop : Pairwise (Function.onFun IsCoprime p) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp
      (Ideal.isCoprime_of_isMaximal (hinj.ne hij))
  rw [secondActualPair_eq_separated p hp hg hinj hodd hpr]
  simp only [secondSeparatedPair_eq_children p hg hp hcop hpr,
    Finset.mul_sum,secondTotalWeight,mul_assoc]

/-- Actual second-pass arithmetic is bounded by the two descendant energies. -/
theorem secondActualPair_norm_le (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i-1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (H₁ H₂ : Finset ι → ℂ) :
    ‖secondActualPair p hp hg F Ψ₁ Ψ₂ m r c d e k H₁ H₂‖ ≤
      Real.sqrt (secondTotalEnergy p hg F Ψ₁ Ψ₂ m r c d e k H₁ true)*
        Real.sqrt (secondTotalEnergy p hg F Ψ₁ Ψ₂ m r c d e k H₂ false) := by
  rw [secondActualPair_eq_children p hg hp hinj hodd hpr]
  have h := DescentWeightedCauchy.weighted_cauchy
    ((Finset.univ : Finset (QuadraticRayRing × QuadraticRayRing)) ×ˢ F.powerset)
    (secondTotalWeight p hg Ψ₁ Ψ₂ m r c d e k)
    (fun z => secondChildSum p hg F z.2 Ψ₂ m r c d e (-k) (secondRayMask p hg z.1.2 H₂))
    (fun z => secondChildSum p hg F z.2 Ψ₁ m r c d e k (secondRayMask p hg z.1.1 H₁))
  simp only [Finset.sum_product,secondTotalEnergy,ite_true,Bool.false_eq_true,ite_false] at h ⊢
  convert h using 1
  · congr 2
    funext z
    congr 1
    funext V
    ring
  · ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

lemma secondRayMask_continuous (r : QuadraticRayRing) (H : ℝ → Finset ι → ℂ)
    (hc : ∀ S, Continuous (fun t => H t S)) (S : Finset ι) :
    Continuous (fun t => secondRayMask p hg r (H t) S) := by
  unfold secondRayMask
  split_ifs
  · exact continuous_const.mul (hc S)
  · exact continuous_const

lemma secondRayMask_norm_time (r : QuadraticRayRing) (H : ℝ → Finset ι → ℂ)
    (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) (t : ℝ) (S : Finset ι) :
    ‖secondRayMask p hg r (H t) S‖ = ‖secondRayMask p hg r (H 0) S‖ := by
  unfold secondRayMask
  split_ifs
  · simp only [norm_mul,hn]
  · rfl

theorem secondChildSum_continuous (F V : Finset ι) (Ψ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => H t S)) :
    Continuous (fun t : ℝ => secondChildSum p hg F V Ψ m r c d e k (H t)) := by
  unfold secondChildSum
  apply continuous_finsetSum
  intro N _
  have hh := hc (V ∪ N)
  unfold secondChildColumn
  fun_prop

theorem secondChildSum_uniform_bound (F V : Finset ι) (Ψ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖secondChildSum p hg F V Ψ m r c d e k (H t)‖ ≤ M := by
  refine ⟨∑ N ∈ (F \ V).powerset,
    ‖secondChildColumn p hg Ψ (m*r) (c*e*∏ i ∈ V, p i) (d*e*k)
      (fun U => H 0 (V ∪ U)) N‖,by positivity,?_⟩
  intro t
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro N _
  simp only [secondChildColumn,norm_mul,hn]
  exact le_rfl

theorem secondTotalEnergy_nonneg (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : Finset ι → ℂ) (negative : Bool) :
    0 ≤ secondTotalEnergy p hg F Ψ₁ Ψ₂ m r c d e k H negative := by
  unfold secondTotalEnergy
  positivity

theorem secondTotalEnergy_continuous (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => H t S)) (negative : Bool) :
    Continuous (fun t => secondTotalEnergy p hg F Ψ₁ Ψ₂ m r c d e k (H t) negative) := by
  unfold secondTotalEnergy
  apply continuous_finsetSum
  intro z _
  apply continuous_finsetSum
  intro V _
  exact continuous_const.mul ((secondChildSum_continuous p hg F V
    (if negative then Ψ₁ else Ψ₂) m r c d e (if negative then k else -k)
    (fun t => secondRayMask p hg (if negative then z.1 else z.2) (H t))
    (secondRayMask_continuous p hg _ H hc)).norm.pow 2)

theorem secondTotalEnergy_uniform_bound (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) (negative : Bool) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, secondTotalEnergy p hg F Ψ₁ Ψ₂ m r c d e k (H t) negative ≤ M := by
  choose M hM hbound using fun (z : QuadraticRayRing × QuadraticRayRing) (V : Finset ι) =>
    secondChildSum_uniform_bound p hg F V (if negative then Ψ₁ else Ψ₂)
      m r c d e (if negative then k else -k)
      (fun t => secondRayMask p hg (if negative then z.1 else z.2) (H t))
      (secondRayMask_norm_time p hg _ H hn)
  refine ⟨∑ z : QuadraticRayRing × QuadraticRayRing, ∑ V ∈ F.powerset,
    ‖secondTotalWeight p hg Ψ₁ Ψ₂ m r c d e k (z,V)‖*(M z V) ^ 2,by positivity,?_⟩
  intro t
  apply Finset.sum_le_sum
  intro z _
  apply Finset.sum_le_sum
  intro V _
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hbound z V t) 2) (norm_nonneg _)

theorem secondTotalEnergy_integrable (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => H t S))
    (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) (negative : Bool) (b : 𝓢(ℝ, ℂ)) :
    Integrable (fun t => ‖b t‖*secondTotalEnergy p hg F Ψ₁ Ψ₂ m r c d e k (H t) negative) volume := by
  obtain ⟨M,hM,hb⟩ := secondTotalEnergy_uniform_bound p hg F Ψ₁ Ψ₂ m r c d e k H hn negative
  apply b.integrable.norm.mul_bdd (c := M)
  · exact (secondTotalEnergy_continuous p hg F Ψ₁ Ψ₂ m r c d e k H hc negative).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (secondTotalEnergy_nonneg p hg F Ψ₁ Ψ₂ m r c d e k (H t) negative)]
      exact hb t)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem second_integral_norm_le_energy
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : ℝ → Finset ι → ℂ)
    (hc₁ : ∀ S, Continuous (fun t => H₁ t S))
    (hc₂ : ∀ S, Continuous (fun t => H₂ t S))
    (hn₁ : ∀ t S, ‖H₁ t S‖ = ‖H₁ 0 S‖)
    (hn₂ : ∀ t S, ‖H₂ t S‖ = ‖H₂ 0 S‖) (b : 𝓢(ℝ, ℂ)) :
    ‖∫ t : ℝ, b t * secondActualPair p hp hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) (H₂ t)‖ ≤
      Real.sqrt (∫ t : ℝ, ‖b t‖ * secondTotalEnergy p hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) true) *
      Real.sqrt (∫ t : ℝ, ‖b t‖ * secondTotalEnergy p hg F Ψ₁ Ψ₂ m r c d e k (H₂ t) false) := by
  let E₁ := fun t => secondTotalEnergy p hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) true
  let E₂ := fun t => secondTotalEnergy p hg F Ψ₁ Ψ₂ m r c d e k (H₂ t) false
  let w := fun t : ℝ => ‖b t‖
  have hE₁ : ∀ t, 0 ≤ E₁ t := fun t => secondTotalEnergy_nonneg p hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) true
  have hE₂ : ∀ t, 0 ≤ E₂ t := fun t => secondTotalEnergy_nonneg p hg F Ψ₁ Ψ₂ m r c d e k (H₂ t) false
  have hw : ∀ t, 0 ≤ w t := fun t => norm_nonneg _
  have i₁ : Integrable (fun t => w t * E₁ t) volume :=
    secondTotalEnergy_integrable p hg F Ψ₁ Ψ₂ m r c d e k H₁ hc₁ hn₁ true b
  have i₂ : Integrable (fun t => w t * E₂ t) volume :=
    secondTotalEnergy_integrable p hg F Ψ₁ Ψ₂ m r c d e k H₂ hc₂ hn₂ false b
  let f := fun t => Real.sqrt (w t * E₁ t)
  let g := fun t => Real.sqrt (w t * E₂ t)
  have hf : Continuous f := Real.continuous_sqrt.comp (b.continuous.norm.mul
    (secondTotalEnergy_continuous p hg F Ψ₁ Ψ₂ m r c d e k H₁ hc₁ true))
  have hg' : Continuous g := Real.continuous_sqrt.comp (b.continuous.norm.mul
    (secondTotalEnergy_continuous p hg F Ψ₁ Ψ₂ m r c d e k H₂ hc₂ false))
  have hfsq (t : ℝ) : f t ^ 2 = w t * E₁ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₁ t))
  have hgsq (t : ℝ) : g t ^ 2 = w t * E₂ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₂ t))
  have mf : MemLp f 2 volume := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    (by simpa only [hfsq] using i₁)
  have mg : MemLp g 2 volume := (memLp_two_iff_integrable_sq hg'.aestronglyMeasurable).mpr
    (by simpa only [hgsq] using i₂)
  have hfg (t : ℝ) : f t * g t = w t * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by
    dsimp only [f, g]
    rw [Real.sqrt_mul (hw t), Real.sqrt_mul (hw t)]
    calc
      _ = (Real.sqrt (w t))^2 * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw t)]
  have hnorm : ‖∫ t : ℝ, b t * secondActualPair p hp hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) (H₂ t)‖ ≤
      ∫ t : ℝ, f t * g t := by
    apply norm_integral_le_of_norm_le (mf.integrable_mul mg)
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Pi.mul_apply]
      rw [hfg, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (secondActualPair_norm_le p hg hp hinj hc hpr F Ψ₁ Ψ₂ m r c d e k (H₁ t) (H₂ t)) (hw t))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₁ t)))
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₂ t)))
    (show MemLp f (ENNReal.ofReal (2 : ℝ)) volume by simpa using mf)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) volume by simpa using mg)
  have hfinal : (∫ t : ℝ, f t * g t) ≤
      Real.sqrt (∫ t : ℝ, w t * E₁ t) * Real.sqrt (∫ t : ℝ, w t * E₂ t) := by
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
    change (∫ t : ℝ, f t * g t) ≤
      Real.sqrt (∫ t : ℝ, f t ^ 2) * Real.sqrt (∫ t : ℝ, g t ^ 2) at hh
    simpa only [hfsq, hgsq] using hh
  exact hnorm.trans hfinal


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson MeasureTheory
open scoped Classical SchwartzMap

def primeProductNorm {ι : Type*} (p : ι → O) (S : Finset ι) : ℝ :=
  ‖ringComplex (∏ i ∈ S, p i)‖ ^ 2

theorem primeProductNorm_pos {ι : Type*} (p : ι → O) (hp : ∀ i, p i ≠ 0) (S : Finset ι) :
    0 < primeProductNorm p S :=
  pow_pos (norm_pos_iff.mpr (ringComplex_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))) 2

theorem primeProductNorm_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (S T : Finset ι) (hd : Disjoint S T) :
    primeProductNorm p (S ∪ T) = primeProductNorm p S * primeProductNorm p T := by
  simp only [primeProductNorm, Finset.prod_union hd, map_mul, norm_mul, mul_pow]

def columnLog {ι : Type*} (p : ι → O) (X : ℝ) (S : Finset ι) : ℝ :=
  Real.log (primeProductNorm p S / X)

def firstDualScale {ι : Type*} (p : ι → O) (C : Finset ι)
    (lengthScale X₁ X₂ : ℝ) (d h : O) : ℝ :=
  lengthScale * ‖ringComplex h‖ ^ 2 /
    (‖ringComplex d‖ ^ 2 * primeProductNorm p C * X₁ * X₂)

theorem actual_radial_argument {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (N P C : Finset ι)
    (hNP : Disjoint N P) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (lengthScale X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (d h : O) :
    firstDualScale p C lengthScale X₁ X₂ d h * Real.exp (-(columnLog p X₁ N) - columnLog p X₂ P) =
      lengthScale * ‖ringComplex h‖ ^ 2 /
        (‖ringComplex d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ C)) := by
  rw [primeProductNorm_union p (N ∪ P) C (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩),
    primeProductNorm_union p N P hNP]
  simp only [columnLog, sub_eq_add_neg, Real.exp_add, Real.exp_neg]
  rw [Real.exp_log (div_pos (primeProductNorm_pos p hp N) hX₁),
    Real.exp_log (div_pos (primeProductNorm_pos p hp P) hX₂)]
  simp only [firstDualScale, div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp [ne_of_gt hX₁, ne_of_gt hX₂]

def normalizedColumn {ι : Type*} (p : ι → O) (C : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  C S / (‖ringComplex (∏ i ∈ S, p i)‖ : ℂ)

theorem integrable_log_pair (b : 𝓢(ℝ, ℂ)) (x y : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ => b t * (kernelLogPhase t x * kernelLogPhase t y * c)) volume := by
  apply b.integrable.mul_bdd (c := ‖c‖)
  · exact (((kernelLogPhase_continuous_left x).mul (kernelLogPhase_continuous_left y)).mul_const c).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by simp only [norm_mul, kernelLogPhase_norm, one_mul, le_refl])

def firstLogDensity (J : ℕ) (t : ℝ) : ℝ := ((1 + ‖t‖) ^ (J + 2))⁻¹

theorem firstLogDensity_nonneg (J : ℕ) (t : ℝ) : 0 ≤ firstLogDensity J t := by
  unfold firstLogDensity
  positivity

theorem firstLogDensity_integrable (J : ℕ) : Integrable (firstLogDensity J) volume := by
  have h := integrable_one_add_norm (E := ℝ) («μ» := (volume : Measure ℝ))
    (r := (J + 2 : ℕ)) (by norm_num; linarith [Nat.cast_nonneg (α := ℝ) J])
  convert h using 1
  funext t
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rfl

theorem firstLogDensity_moment_integrable (J : ℕ) :
    Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * firstLogDensity J t) volume := by
  convert firstLogDensity_integrable 0 using 1
  funext t
  have ht : 1 + ‖t‖ ≠ 0 := ne_of_gt (by positivity)
  simp only [firstLogDensity, zero_add, pow_add, mul_inv_rev]
  field_simp

theorem two_variable_radial_envelope (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W (R * Real.exp (-x-y)) =
        ∫ t : ℝ, (V₁ x * kernelLogPhase t (-x)) * (V₂ y * kernelLogPhase t (-y)) * b t) ∧
      (∀ t : ℝ, (1 + R) ^ A * ‖b t‖ ≤ K * firstLogDensity J t) := by
  let V : Bool → ℝ → ℂ := fun j => if j then V₂ else V₁
  let M : Bool → ℝ := fun j => if j then M₂ else M₁
  have hM : ∀ j, 0 ≤ M j := by intro j; cases j <;> assumption
  have hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j := by
    intro j; cases j
    · exact hV₁
    · exact hV₂
  obtain ⟨K, hK, hsep⟩ := paperRadialFourier_log_separation_envelope
    V (fun _ => -1) M hM hV W A (J + 2)
  refine ⟨K, hK.le, ?_⟩
  intro R hR
  obtain ⟨b, hb, _, _, hpoint⟩ := hsep R hR
  refine ⟨b, ?_, ?_⟩
  · intro x y
    have hs := hb (fun j => if j then y else x)
    simpa only [V, Fintype.prod_bool, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
      neg_one_mul, mul_neg_one, sub_eq_add_neg, add_comm, mul_comm, mul_left_comm, mul_assoc] using hs
  · intro t
    rw [firstLogDensity, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t‖) (J + 2))).mpr
    simpa only [Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using hpoint t


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondGaussTerm
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (H₁ H₂ : Finset ι → ℂ)
    (S T : Finset ι) : ℂ :=
  star (supportMobius S *
    secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ₁ (m * (e * r)) c d H₁ S) *
  (supportMobius T *
    secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ₂ (m * (e * r)) c d H₂ T) *
    secondNormalizedGaussTerm p hp hg S T e k

def actualSecondKernel
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    (star (V₁ (columnLog p X₁ S)) * V₂ (columnLog p X₂ T)) *
    ((Y : ℂ) / (‖ringComplex (∏ i ∈ S ∪ T, p i)‖ : ℂ)) *
    paperRadialFourier W (Y * ‖ringComplex k‖ ^ 2 /
      (‖ringComplex e‖ ^ 2 * primeProductNorm p (S ∪ T))) *
    secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T
    else 0

def secondLogTest (V : ℝ → ℂ) (X t : ℝ) (negative : Bool) (S : Finset ι) : ℂ :=
  (V (columnLog p X S) *
    (if negative then star (kernelLogPhase t (-(columnLog p X S))) else kernelLogPhase t (-(columnLog p X S)))) /
      (‖ringComplex (∏ i ∈ S, p i)‖ : ℂ)

theorem secondGaussTerm_log_twist
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ t : ℝ) (S T : Finset ι) :
    secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) S T =
    (kernelLogPhase t (-(columnLog p X₁ S)) * kernelLogPhase t (-(columnLog p X₂ T))) *
      (star (V₁ (columnLog p X₁ S)) * V₂ (columnLog p X₂ T) *
        secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e k
          (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T) := by
  simp only [secondGaussTerm, secondInputCoefficient, secondLogTest, normalizedColumn,
    ite_true, Bool.false_eq_true, ite_false, star_mul, star_div₀, star_star,
    one_div, star_inv₀]
  ring

theorem actualSecondKernel_eq_integral
   
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ x y : ℝ, star (V₁ x) * V₂ y *
      paperRadialFourier W (firstDualScale p ∅ Y X₁ X₂ e k * Real.exp (-x-y)) =
      ∫ t : ℝ, (star (V₁ x) * kernelLogPhase t (-x)) * (V₂ y * kernelLogPhase t (-y)) * b t) :
    Integrable (fun t : ℝ => b t * secondActualPair p hp hg F Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false)) volume ∧
    actualSecondKernel p hp hg F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y =
      (Y : ℂ) * ∫ t : ℝ, b t * secondActualPair p hp hg F Ψ₁ Ψ₂ m r c d e k
        (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) := by
  let G := fun (t : ℝ) (S T : Finset ι) => if Disjoint S T then b t *
    secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) S T else 0
  have hGi (S T : Finset ι) : Integrable (fun t => G t S T) volume := by
    by_cases hd : Disjoint S T
    · simp only [G, if_pos hd, secondGaussTerm_log_twist]
      convert integrable_log_pair b (-(columnLog p X₁ S)) (-(columnLog p X₂ T))
        (star (V₁ (columnLog p X₁ S)) * V₂ (columnLog p X₂ T) *
          secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e k
            (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T) using 1
    · simp only [G, if_neg hd]
      exact integrable_zero _ _ _
  have hGs (t : ℝ) : (∑ S ∈ F.powerset, ∑ T ∈ F.powerset, G t S T) =
      b t * secondActualPair p hp hg F Ψ₁ Ψ₂ m r c d e k
        (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) := by
    simp only [G, secondActualPair, secondGaussTerm, Finset.mul_sum, mul_ite, mul_zero]
  have hI : Integrable (fun t => ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, G t S T) volume :=
    integrable_finsetSum _ (fun S _ => integrable_finsetSum _ (fun T _ => hGi S T))
  constructor
  · simpa only [hGs] using hI
  · rw [← integral_congr_ae (Filter.Eventually.of_forall hGs)]
    rw [integral_finsetSum _ (fun S _ => integrable_finsetSum _ (fun T _ => hGi S T)), Finset.mul_sum]
    unfold actualSecondKernel
    apply Finset.sum_congr rfl
    intro S hS
    rw [integral_finsetSum _ (fun T _ => hGi S T), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hd : Disjoint S T
    · simp only [G, if_pos hd, secondGaussTerm_log_twist]
      have harg := actual_radial_argument p hp S T ∅ hd
        (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) Y X₁ X₂ hX₁ hX₂ e k
      simp only [Finset.union_empty] at harg
      rw [← harg]
      have hn : secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e k
          (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T =
        ((‖ringComplex (∏ i ∈ S, p i)‖ : ℂ)⁻¹ * (‖ringComplex (∏ i ∈ T, p i)‖ : ℂ)⁻¹) *
          secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T := by
        simp only [secondGaussTerm, secondInputCoefficient, normalizedColumn, one_div,
          mul_one, star_mul, map_inv₀, Complex.star_def, Complex.conj_ofReal]
        ring
      rw [hn]
      rw [Finset.prod_union hd]
      simp only [map_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
      have hh := congrArg (fun z : ℂ => (Y : ℂ) * z *
        ((‖ringComplex (∏ i ∈ S, p i)‖ : ℂ)⁻¹ * (‖ringComplex (∏ i ∈ T, p i)‖ : ℂ)⁻¹) *
          secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T)
        (hsep (columnLog p X₁ S) (columnLog p X₂ T))
      rw [← integral_const_mul, ← integral_mul_const, ← integral_mul_const] at hh
      convert hh using 1
      · ring
      · rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        ring
    · simp [hd, G]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem secondLogTest_continuous (V : ℝ → ℂ) (X : ℝ) (negative : Bool) (S : Finset ι) :
    Continuous (fun t : ℝ => secondLogTest p V X t negative S) := by
  have h := kernelLogPhase_continuous_left (-(columnLog p X S))
  cases negative <;> simp only [secondLogTest, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem secondLogTest_norm (V : ℝ → ℂ) (X t : ℝ) (negative : Bool) (S : Finset ι) :
    ‖secondLogTest p V X t negative S‖ = ‖secondLogTest p V X 0 negative S‖ := by
  cases negative <;> simp only [secondLogTest, Bool.false_eq_true, ite_false, ite_true,
    norm_div, norm_mul, norm_star, kernelLogPhase_norm]

def secondKernelEnergy (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (V : ℝ → ℂ) (X : ℝ) (negative : Bool) (b : 𝓢(ℝ, ℂ)) : ℝ :=
  ∫ t : ℝ, ‖b t‖ * secondTotalEnergy p hg F Ψ₁ Ψ₂ m r c d e k
    (secondLogTest p V X t negative) negative

theorem actual_second_kernel_uniform_energy_envelope
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ x, V₂ x ≠ 0 → |x| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ e k : O, e ≠ 0 → k ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p ∅ Y X₁ X₂ e k) ^ A * ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ∀ (Ψ₁ Ψ₂ : O →* ℂ) (m r c d : O),
          ‖actualSecondKernel p hp hg F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y‖ ≤
            Y * Real.sqrt (secondKernelEnergy p hg F Ψ₁ Ψ₂ m r c d e k V₁ X₁ true b) *
              Real.sqrt (secondKernelEnergy p hg F Ψ₁ Ψ₂ m r c d e k V₂ X₂ false b) := by
  have hV₁' : ∀ x, star (V₁ x) ≠ 0 → |x| ≤ M₁ := by
    intro x hx
    exact hV₁ x (by intro h; simp [h] at hx)
  obtain ⟨K, hK, hs⟩ := two_variable_radial_envelope W (fun x => star (V₁ x)) V₂
    M₁ M₂ hM₁ hM₂ hV₁' hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro Y hY e k he hk
  have hR : 0 < firstDualScale p ∅ Y X₁ X₂ e k := by
    unfold firstDualScale
    exact div_pos (mul_pos hY (pow_pos (norm_pos_iff.mpr (ringComplex_ne_zero hk)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (ringComplex_ne_zero he)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hsep, hb⟩ := hs _ hR
  refine ⟨b, hb, ?_⟩
  intro Ψ₁ Ψ₂ m r c d
  rw [(actualSecondKernel_eq_integral p hp hg F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y
    hX₁ hX₂ b hsep).2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  have hi := second_integral_norm_le_energy p hp hg hinj hc hpr F Ψ₁ Ψ₂ m r c d e k
    (fun t => secondLogTest p V₁ X₁ t true) (fun t => secondLogTest p V₂ X₂ t false)
    (secondLogTest_continuous p V₁ X₁ true) (secondLogTest_continuous p V₂ X₂ false)
    (fun t S => secondLogTest_norm p V₁ X₁ t true S)
    (fun t S => secondLogTest_norm p V₂ X₂ t false S) b
  change Y * _ ≤ Y * Real.sqrt _ * Real.sqrt _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hi hY.le

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SecondPassFiber
open scoped Classical

theorem second_energy_selected_family {κ : Type*} [Fintype κ] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ)
      (P : κ → Ideal O × O → ℂ) (sel : OldTuple → κ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (sel x) (newLabel x, newRow x)‖ ^ 2) ≤
      B * C * (lengthScale * Ideal.absNorm b0) ^ ε *
        ∑ u : κ, ∑ z ∈ t, ‖P u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := SecondPassFiber.second_energy_pushforward ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w B lengthScale P sel hb0 hB hL hvalid hmap ht hnorm hw
  calc
    _ ≤ ∑ x ∈ s, ‖w x‖ * ∑ u : κ, ‖P u (newLabel x, newRow x)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.single_le_sum
        (s := Finset.univ) (a := sel x)
        (f := fun u : κ => ‖P u (newLabel x, newRow x)‖ ^ 2)
        (fun u _ => sq_nonneg _) (Finset.mem_univ (sel x))
    _ = ∑ u : κ, ∑ x ∈ s, ‖w x‖ * ‖P u (newLabel x, newRow x)‖ ^ 2 := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ u : κ, B * C * (lengthScale * Ideal.absNorm b0) ^ ε * ∑ z ∈ t, ‖P u z‖ ^ 2 := by
      exact Finset.sum_le_sum (fun u _ => hb s t b0 w (P u) B lengthScale hb0 hB hL hvalid hmap ht hnorm hw)
    _ = _ := by rw [Finset.mul_sum]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SecondPassFiber
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

def tupleLabelElement (x : OldTuple) : O :=
  cubicIdealGenerator (x.core 0) * cubicIdealGenerator (x.core 1) * cubicIdealGenerator (x.core 2) * cubicIdealGenerator x.v

theorem tupleLabelElement_span (x : OldTuple) :
    Ideal.span {tupleLabelElement x} = newLabel x := by
  simp only [tupleLabelElement, newLabel, ← Ideal.span_singleton_mul_span_singleton, span_cubicIdealGenerator]

theorem exists_label_unit (f : O) (I : Ideal O) (hf : Ideal.span {f} = I) :
    ∃ u : Oˣ, f = (u : O) * cubicIdealGenerator I := by
  have hs : Ideal.span {cubicIdealGenerator I} = Ideal.span {f} := (span_cubicIdealGenerator I).trans hf.symm
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

def tupleLabelUnit (x : OldTuple) : Oˣ :=
  Classical.choose (exists_label_unit (tupleLabelElement x) (newLabel x) (tupleLabelElement_span x))

theorem tupleLabelUnit_spec (x : OldTuple) :
    tupleLabelElement x = (tupleLabelUnit x : O) * cubicIdealGenerator (newLabel x) :=
  Classical.choose_spec (exists_label_unit (tupleLabelElement x) (newLabel x) (tupleLabelElement_span x))

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def fixedChildRow (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (f y : O) : ℂ :=
  ∑ N ∈ F.powerset, secondChildColumn p hg Ψ m f y H N

def idealChildRow (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (u : Oˣ) (z : Ideal O × O) : ℂ :=
  fixedChildRow p hg F Ψ m H ((u : O) * cubicIdealGenerator z.1)
    (if negative then -z.2 else z.2)

theorem tuple_child_eq_unit_sector (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (x : OldTuple) :
    fixedChildRow p hg F Ψ m H (tupleLabelElement x)
      (if negative then -newRow x else newRow x) =
    idealChildRow p hg F Ψ m H negative (tupleLabelUnit x) (newLabel x, newRow x) := by
  rw [tupleLabelUnit_spec]
  rfl

theorem fixed_child_second_energy_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (negative : Bool),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ *
        ‖fixedChildRow p hg F Ψ m H (tupleLabelElement x)
          (if negative then -newRow x else newRow x)‖ ^ 2) ≤
      B * C * (lengthScale * Ideal.absNorm b0) ^ ε *
        ∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hg F Ψ m H negative u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := second_energy_selected_family (κ := Oˣ) ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w B lengthScale F Ψ m H negative hb0 hB hL hvalid hmap ht hnorm hw
  have hh := hb s t b0 w B lengthScale (idealChildRow p hg F Ψ m H negative)
    tupleLabelUnit hb0 hB hL hvalid hmap ht hnorm hw
  convert hh using 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [tuple_child_eq_unit_sector]

/-- The finite unit sectors contribute only their fixed cardinality. -/
theorem idealChildRow_unit_energy_le (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (t : Finset (Ideal O × O)) (E : ℝ)
    (hE : ∀ u : Oˣ, (∑ z ∈ t, ‖idealChildRow p hg F Ψ m H negative u z‖ ^ 2) ≤ E) :
    (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hg F Ψ m H negative u z‖ ^ 2) ≤
      (Fintype.card Oˣ : ℝ) * E := by
  calc
    _ ≤ ∑ u : Oˣ, E := Finset.sum_le_sum (fun u _ => hE u)
    _ = _ := by simp

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SecondPassFiber
open scoped Classical
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

def fixedSecondMode (s : Finset OldTuple) (w : OldTuple → ℂ) (label : OldTuple → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  ∑ x ∈ s, w x *
    star (fixedChildRow p hg F Ψ₁ m H₁ (label x) (newRow x)) *
      fixedChildRow p hg F Ψ₂ m H₂ (label x) (-newRow x)


end

theorem full_uniform_labeled_child_second_energy_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (negative : Bool),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
      (∑ x ∈ s, ‖w x‖ *
        ‖fixedChildRow p hg F Ψ m H (label x)
          (if negative then -newRow x else newRow x)‖ ^ 2) ≤
      B * C * (lengthScale * Ideal.absNorm b0) ^ ε *
        ∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hg F Ψ m H negative u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := second_energy_selected_family (κ := Oˣ) ε hε
  refine ⟨C, hC, ?_⟩
  intro ι _ p _ hg
    s t b0 w B lengthScale label F Ψ m H negative hb0 hB hL hvalid hmap ht hnorm hw hlabel
  let sel : OldTuple → Oˣ := fun x => if hx : x ∈ s then
    Classical.choose (exists_label_unit (label x) (newLabel x) (hlabel x hx)) else 1
  have hsel (x : OldTuple) (hx : x ∈ s) : label x = (sel x : O) * cubicIdealGenerator (newLabel x) := by
    simp only [sel, dif_pos hx]
    exact Classical.choose_spec (exists_label_unit (label x) (newLabel x) (hlabel x hx))
  have hh := hb s t b0 w B lengthScale (idealChildRow p hg F Ψ m H negative)
    sel hb0 hB hL hvalid hmap ht hnorm hw
  convert hh using 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [hsel x hx]
  rfl

theorem full_uniform_fixed_second_mode_transfer (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
      ‖fixedSecondMode p hg s w label F Ψ₁ Ψ₂ m H₁ H₂‖ ≤
        (B * C * (lengthScale * Ideal.absNorm b0)^ε) *
        Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hg F Ψ₁ m H₁ false u z‖ ^ 2) *
        Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hg F Ψ₂ m H₂ true u z‖ ^ 2) := by
  obtain ⟨C, hC, hpush⟩ := full_uniform_labeled_child_second_energy_pushforward ε hε
  refine ⟨C, hC, ?_⟩
  intro ι _ p _ hg
  have hpush := hpush p hg
  intro s t b0 w B lengthScale label F Ψ₁ Ψ₂ m H₁ H₂ hb0 hB hL hv hm ht hn hw hl
  let P₁ := fun x => fixedChildRow p hg F Ψ₁ m H₁ (label x) (newRow x)
  let P₂ := fun x => fixedChildRow p hg F Ψ₂ m H₂ (label x) (-newRow x)
  have h₁ := hpush s t b0 w B lengthScale label F Ψ₁ m H₁ false hb0 hB hL hv hm ht hn hw hl
  have h₂ := hpush s t b0 w B lengthScale label F Ψ₂ m H₂ true hb0 hB hL hv hm ht hn hw hl
  simp only [Bool.false_eq_true, ite_false, ite_true] at h₁ h₂
  let D : ℝ := B * C * (lengthScale * Ideal.absNorm b0)^ε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCau := DescentWeightedCauchy.weighted_cauchy s w P₂ P₁
  have hmode : fixedSecondMode p hg s w label F Ψ₁ Ψ₂ m H₁ H₂ =
      ∑ x ∈ s, w x * P₂ x * star (P₁ x) := by
    unfold fixedSecondMode
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [P₁, P₂]
    ring
  rw [hmode]
  apply hCau.trans
  calc
    _ ≤ Real.sqrt (D * (∑ u : Oˣ, ∑ z ∈ t,
        ‖idealChildRow p hg F Ψ₂ m H₂ true u z‖ ^ 2)) *
      Real.sqrt (D * (∑ u : Oˣ, ∑ z ∈ t,
        ‖idealChildRow p hg F Ψ₁ m H₁ false u z‖ ^ 2)) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul hD, Real.sqrt_mul hD]
      calc
        _ = (Real.sqrt D)^2 *
          Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hg F Ψ₁ m H₁ false u z‖ ^ 2) *
          Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hg F Ψ₂ m H₂ true u z‖ ^ 2) := by ring
        _ = _ := by rw [Real.sq_sqrt hD]

end SecondPassArithmetic

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
