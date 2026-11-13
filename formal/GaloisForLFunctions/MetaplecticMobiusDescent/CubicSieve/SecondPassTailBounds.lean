/-
Tail bounds of the second pass adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.LogarithmicBinsAndCubeBlocks

/-!
# Tail bounds of the second pass

Primitive trace Gauss normalization leaves coefficients of norm at most one; finite lattice
cutoffs and uniform polynomial decay of the discarded source of bounded supported columns.
Excluded cube primes divide the coprimality mask or the retained label.
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

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

/-- Primitive trace Gauss normalization leaves a coefficient of norm at most one. -/
theorem secondPairRadialMode_norm_le
    {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (hχ : ∀ i, χ i ≠ 1)
    (S T : Finset ι) (e k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let n := ∏ i : ↥((T \ S) ∪ (S \ T)), p i.val
    ‖secondPairRadialMode p χ hp S T e k W Y‖ ≤
      (Y / ‖ringComplex n‖) * ‖paperRadialFourier W
        ((Y / (‖ringComplex e‖ ^ 2 * ‖ringComplex n‖ ^ 2)) * ‖ringComplex k‖ ^ 2)‖ := by
  let ap : ↥((T \ S) ∪ (S \ T)) → O := fun i => p i.val
  let ac := activePrimeRowCharacter p χ T S
  let n := ∏ i, ap i
  have hn : 0 < ‖ringComplex n‖ := norm_pos_iff.mpr
    (ringComplex_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i.val)))
  have hGauss : ‖primeRowTraceGauss ap (fun i => hp i.val) ac‖ = ‖ringComplex n‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    exact (prime_row_trace_poisson ap (fun i => hp i.val)
      (hinj.comp Subtype.val_injective) ac (activePrimeRowCharacter_ne_one p χ hχ T S)).1
  have hscalar : ‖(Y : ℂ) * primeRowTraceGauss ap (fun i => hp i.val) ac /
      (‖ringComplex n‖ ^ 2 : ℝ)‖ = Y / ‖ringComplex n‖ := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hY.le,
      hGauss, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    field_simp [ne_of_gt hn]
  have he := primeCuspRowCharacter_norm_le_one ap ac e
  have hk := primeCuspRowCharacter_norm_le_one ap (fun i => (ac i)⁻¹) k
  change ‖(((Y : ℂ) * primeRowTraceGauss ap (fun i => hp i.val) ac /
    (‖ringComplex n‖ ^ 2 : ℝ)) * primeCuspRowCharacter ap ac e *
    primeCuspRowCharacter ap (fun i => (ac i)⁻¹) k) * _‖ ≤ _
  rw [norm_mul, norm_mul, norm_mul, hscalar]
  rw [show Y * ‖ringComplex k‖ ^ 2 / (‖ringComplex e‖ ^ 2 * ‖ringComplex n‖ ^ 2) =
    (Y / (‖ringComplex e‖ ^ 2 * ‖ringComplex n‖ ^ 2)) * ‖ringComplex k‖ ^ 2 by ring]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_right (mul_nonneg (div_pos hY hn).le (norm_nonneg _)) hk).trans
      (mul_le_of_le_one_right (div_pos hY hn).le he)) (norm_nonneg _)

theorem full_uniform_secondPairRadialMode_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i})),
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H →
      let n := ∏ i : ↥((T \ S) ∪ (S \ T)), p i.val
      let scale := Y / (‖ringComplex e‖^2 * ‖ringComplex n‖^2)
      (∑' k : {k : O // H ≤ scale * ‖ringComplex k‖^2},
        ‖secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k.val W Y‖) ≤
      (Y / ‖ringComplex n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^A)) := by
  obtain ⟨s,C,hC,hbound⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj
    S T e he W Y H hY hH
  dsimp only
  let n := ∏ i : ↥((T \ S) ∪ (S \ T)), p i.val
  let scale := Y / (‖ringComplex e‖^2 * ‖ringComplex n‖^2)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hnorm : 0 < ‖ringComplex n‖ := norm_pos_iff.mpr (ringComplex_ne_zero hn)
  have hscale : 0 < scale := div_pos hY
    (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero he))) (sq_pos_of_pos hnorm))
  let tailSet : Set O := {k | H ≤ scale * ‖ringComplex k‖^2}
  let c := Y / ‖ringComplex n‖
  have hc0 : 0 ≤ c := (div_pos hY hnorm).le
  have hpnt (k : tailSet) : ‖secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k.val W Y‖ ≤
      c * ‖paperRadialFourier W (scale * ‖ringComplex k.val‖^2)‖ := by
    exact secondPairRadialMode_norm_le p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp
      hinj (fun i => complexSexticChar_ne_one (Ideal.span {p i}) (hg i)) S T e k.val W Y hY
  have hmajor : Summable (fun k : tailSet =>
      c * ‖paperRadialFourier W (scale * ‖ringComplex k.val‖^2)‖) :=
    ((paperRadialFourier_lattice_summable_norm W scale hscale).subtype tailSet).mul_left c
  have hsmall : Summable (fun k : tailSet => ‖secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k.val W Y‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑' k : tailSet, c * ‖paperRadialFourier W
          (scale * ‖ringComplex k.val‖^2)‖ := hsmall.tsum_le_tsum hpnt hmajor
    _ = c * ∑' k : tailSet, ‖paperRadialFourier W
          (scale * ‖ringComplex k.val‖^2)‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound W scale H hscale hH) hc0

theorem full_uniform_secondPairRadialMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i})),
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H → ∀ K : Finset O,
      let n := ∏ i : ↥((T \ S) ∪ (S \ T)), p i.val
      let scale := Y / (‖ringComplex e‖^2 * ‖ringComplex n‖^2)
      (∀ k : O, k ∉ K → H ≤ scale * ‖ringComplex k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k.val W Y‖ ≤
        (Y/‖ringComplex n‖) *
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondPairRadialMode_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj
  have hb := hb p hp hg hinj
  intro S T e he W Y H hY hH K
  dsimp only
  intro hK
  let n := ∏ i : ↥((T \ S) ∪ (S \ T)), p i.val
  let scale := Y / (‖ringComplex e‖^2 * ‖ringComplex n‖^2)
  let small : Set O := {k | k ∉ K}
  let large : Set O := {k | H ≤ scale * ‖ringComplex k‖^2}
  let f : small → large := fun k => ⟨k.val,hK k.val k.property⟩
  have hi : Function.Injective f := by
    intro a b heq
    exact Subtype.ext (congrArg (fun z : large => z.val) heq)
  have hs := (secondPairRadialMode_summable p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e he W Y hY).norm
  calc
    _ ≤ ∑' k : small, ‖secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k.val W Y‖ :=
      norm_tsum_le_tsum_norm (hs.subtype small)
    _ ≤ ∑' k : large, ‖secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k.val W Y‖ :=
      (hs.subtype small).tsum_le_tsum_of_inj f hi (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
        (hs.subtype large)
    _ ≤ _ := hb S T e he W Y H hY hH


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def residualPairWeight (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι) : ℂ :=
  star (supportMobius S * secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ₁ m c d H₁ S) *
    (supportMobius T * secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ₂ m c d H₂ T)

theorem residualSecondMode_tail_eq (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m c d : O) (H₁ H₂ : Finset ι → ℂ) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (K : Finset O) :
    (∑' k : {k : O // k ∉ K}, residualSecondMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp F G Ψ₁ Ψ₂ m c d H₁ H₂ e k.val W Y) =
    ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset, if Disjoint S T then
      residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
        ∑' k : {k : O // k ∉ K}, secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k.val W Y else 0 := by
  have hs (S T : Finset ι) : Summable (fun k : {k : O // k ∉ K} =>
      if Disjoint S T then residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
        secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k.val W Y else 0) := by
    by_cases hd : Disjoint S T
    · simp only [if_pos hd]
      exact ((secondPairRadialMode_summable p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e he W Y hY).subtype _).mul_left _
    · simp only [if_neg hd]
      exact summable_zero
  change (∑' k : {k : O // k ∉ K}, ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset,
    if Disjoint S T then residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
      secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k.val W Y else 0) = _
  rw [Summable.tsum_finsetSum (fun S _ => summable_sum (fun T _ => hs S T))]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Summable.tsum_finsetSum (fun T _ => hs S T)]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd, tsum_mul_left]
  · simp [hd]

def residualTailCost (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m c d : O) (H₁ H₂ : Finset ι → ℂ) (e : O) (Y H : ℝ) (A : ℕ) (P : ℝ) : ℝ :=
  ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset, if Disjoint S T then
    let n := ∏ i : ↥((T \ S) ∪ (S \ T)), p i.val
    let scale := Y / (‖ringComplex e‖^2 * ‖ringComplex n‖^2)
    ‖residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T‖ *
      ((Y/‖ringComplex n‖) * (P / ((min 1 scale)^2 * (1+H)^A)))
    else 0


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

theorem full_uniform_residualSecondMode_tail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i})),
    ∀ (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ)
      (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H → ∀ K : Finset O,
      (∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T ≠ 0 →
        ∀ k : O, k ∉ K →
          H ≤ (Y / (‖ringComplex e‖^2 * ‖ringComplex (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val)‖^2)) *
            ‖ringComplex k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, residualSecondMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp F G Ψ₁ Ψ₂ m c d H₁ H₂ e k.val W Y‖ ≤
      residualTailCost p hg F G Ψ₁ Ψ₂ m c d H₁ H₂ e Y H A (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondPairRadialMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj
  have hb := hb p hp hg hinj
  intro F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y H hY hH K hK
  rw [residualSecondMode_tail_eq p hp hg F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y hY K]
  unfold residualTailCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd, norm_mul]
    by_cases hw : residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T = 0
    · simp only [hw, norm_zero, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (hb S T e he W Y H hY hH K (hK S hS T hT hd hw)) (norm_nonneg _)
  · simp [hd]

theorem full_uniform_secondSourceTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i})),
    ∀ (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (Hcol : Finset ι → ℂ)
      (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E ∈ G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E →
          H ≤ (Y / (‖ringComplex (∏ i ∈ E, p i)‖^2 *
            ‖ringComplex (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val)‖^2)) * ‖ringComplex k‖^2) →
      ‖secondSourceTail p hp hg F Ψ m c d Hcol W Y K‖ ≤
      ∑ G ∈ F.powerset, ∑ E ∈ G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E‖ *
        residualTailCost p hg F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
          (∏ i ∈ E, p i) Y H A
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_residualSecondMode_tail_bound A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj
  have hb := hb p hp hg hinj
  intro F Ψ m c d Hcol W Y H hY hH K hK
  unfold secondSourceTail
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro G hG
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro E hE
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simp_rw [← residualSecondMode_eq_frequencyKernel p hp hg hinj F G E
    (Finset.mem_powerset.mp hE) Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))]
  exact hb F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
    (∏ i ∈ E, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
    W Y H hY hH (K G E) (hK G hG E hE)


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

lemma supportMobius_norm (S : Finset ι) : ‖supportMobius S‖ = 1 := by
  simp only [supportMobius, norm_pow, norm_neg, norm_one, one_pow]

def boundedPrimeSupports (F : Finset ι) (X : ℝ) : Finset (Finset ι) :=
  F.powerset.filter (fun S => primeProductNorm p S ≤ X)

theorem boundedPrimeSupports_card
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (F : Finset ι) (X : ℝ) (hX : 1 ≤ X) :
    ((boundedPrimeSupports p F X).card : ℝ) ≤ diagonalControl sieveCutoff * X := by
  let q : Finset ι → Ideal O := fun S => ∏ i ∈ S, Ideal.span {p i}
  have hq : Function.Injective q := primeIdealFamily_product_injective _ hinj
  let I := (boundedPrimeSupports p F X).image q
  have hcard : I.card = (boundedPrimeSupports p F X).card := Finset.card_image_of_injective _ hq
  rw [← hcard]
  apply finite_ideal_card_bound I X hX
  intro J hJ
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hJ
  rw [← primeProductNorm_eq_ideal_norm p S]
  exact (Finset.mem_filter.mp hS).2

theorem secondInputCoefficient_norm_le_test
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (H : Finset ι → ℂ) (S : Finset ι) :
    ‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d H S‖ ≤ ‖H S‖ := by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  have h1 : ‖Ψ (∏ i ∈ S, p i)‖ * ‖primeCoprimeMask p S m‖ ≤ 1 :=
    mul_le_one₀ (hΨ _) (norm_nonneg _) (primeCoprimeMask_norm_le_one p S m)
  have h2 : ‖primeSubsetRow p χ S c‖ ^ 4 ≤ 1 :=
    (pow_le_pow_left₀ (norm_nonneg _) (primeSubsetRow_norm_le_one p χ S c) 4).trans_eq (one_pow _)
  have h3 : (‖Ψ (∏ i ∈ S, p i)‖ * ‖primeCoprimeMask p S m‖ *
      ‖primeSubsetRow p χ S c‖ ^ 4) * ‖primeSubsetRow p χ S d‖ ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ h1 (pow_nonneg (norm_nonneg _) _) h2)
      (norm_nonneg _) (primeSubsetRow_norm_le_one p χ S d)
  simp only [secondInputCoefficient, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) h3

include hp in
theorem secondSourceCommonCoefficient_norm_le_one
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (G E : Finset ι) :
    ‖secondSourceCommonCoefficient p hg Ψ m c d G E‖ ≤ 1 := by
  have hA : ‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
      Ψ m c d (fun _ => 1) G‖ ≤ 1 := by
    simpa only [norm_one] using secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d (fun _ => 1) G
  have hA2 := (pow_le_pow_left₀ (norm_nonneg _) hA 2).trans_eq (one_pow 2)
  have hN := primeProductNorm_ge_one p hp E
  have hNpos := primeProductNorm_pos p hp E
  simp only [secondSourceCommonCoefficient, norm_mul, norm_div,
    Complex.norm_of_nonneg (sq_nonneg _), supportMobius_norm]
  change _ * (1 / primeProductNorm p E) ≤ 1
  exact (mul_le_of_le_one_left (div_nonneg zero_le_one hNpos.le) hA2).trans
    ((div_le_one hNpos).mpr hN)

lemma residualPairWeight_test_ne_zero
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι)
    (hw : residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T ≠ 0) : H₁ S ≠ 0 ∧ H₂ T ≠ 0 := by
  constructor
  · intro hz
    apply hw
    simp only [residualPairWeight, secondInputCoefficient, hz, mul_zero, star_zero, zero_mul]
  · intro hz
    apply hw
    simp only [residualPairWeight, secondInputCoefficient, hz, mul_zero]

theorem active_norm_sq_disjoint (S T : Finset ι) (hd : Disjoint S T) :
    ‖ringComplex (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val)‖ ^ 2 =
      primeProductNorm p S * primeProductNorm p T := by
  rw [Finset.prod_coe_sort]
  simp only [Finset.sdiff_eq_self_of_disjoint hd, Finset.sdiff_eq_self_of_disjoint hd.symm]
  rw [Finset.prod_union hd.symm, map_mul, norm_mul, mul_pow]
  exact mul_comm _ _

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

theorem tail_radial_scalar_le (Y E n lengthScale H P : ℝ) (A : ℕ)
    (hY : 0 < Y) (hE : 0 < E) (hn : 1 ≤ n) (hL : 1 ≤ lengthScale)
    (hden : E*n^2 ≤ lengthScale^3) (hH : 0 ≤ H) (hP : 0 ≤ P) :
    (Y/n) * (P / ((min 1 (Y/(E*n^2)))^2 * (1+H)^A)) ≤
      Y*P*(1+lengthScale^3/Y)^2 / (1+H)^A := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have he : 0 < E*n^2 := mul_pos hE (sq_pos_of_pos hn0)
  have hs : 0 < Y/(E*n^2) := div_pos hY he
  have hr : 0 ≤ lengthScale^3/Y := div_nonneg (pow_nonneg (zero_le_one.trans hL) _) hY.le
  have hi : (min 1 (Y/(E*n^2)))⁻¹ ≤ 1+lengthScale^3/Y := by
    by_cases h : 1 ≤ Y/(E*n^2)
    · rw [min_eq_left h, inv_one]
      linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)), inv_div]
      exact (div_le_div_of_nonneg_right hden hY.le).trans (by linarith)
  have hi0 : 0 ≤ (min 1 (Y/(E*n^2)))⁻¹ := inv_nonneg.mpr (le_min zero_le_one hs.le)
  have hi2 := pow_le_pow_left₀ hi0 hi 2
  have hyn : Y/n ≤ Y := div_le_self hY.le hn
  calc
    _ = (Y/n)*P*((min 1 (Y/(E*n^2)))⁻¹)^2 / (1+H)^A := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith) _)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hyn hP) hi2 (sq_nonneg _) (mul_nonneg hY.le hP)

theorem sum_pair_indicator {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (U : ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, if P a ∧ P b then U else 0) =
      ((s.filter P).card : ℝ)^2 * U := by
  calc
    _ = ∑ a ∈ s.filter P, ∑ b ∈ s.filter P, U := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : P a
      · simp only [h, true_and, ite_true]
      · simp only [h, false_and, ite_false, Finset.sum_const_zero]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, pow_two]; ring


variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem residualPairWeight_bounded_test
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O)
    (Hcol : Finset ι → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (G S T : Finset ι) :
    ‖residualPairWeight p hg Ψ Ψ m c d
      (fun U => Hcol (G ∪ U)) (fun U => Hcol (G ∪ U)) S T‖ ≤ B^2 := by
  simp only [residualPairWeight, norm_mul, norm_star, supportMobius_norm, one_mul]
  have hS := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (fun U => Hcol (G ∪ U)) S).trans (hcol _)
  have hT := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (fun U => Hcol (G ∪ U)) T).trans (hcol _)
  simpa only [pow_two] using mul_le_mul hS hT (norm_nonneg _) hB

include hp hinj
theorem residualTailCost_bounded_test
    (F G E : Finset ι) (hEG : E ⊆ G) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (Hcol : Finset ι → ℂ) (B Y H lengthScale P : ℝ) (A : ℕ)
    (hB : 0 ≤ B) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (hsupport : ∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) :
    residualTailCost p hg F G Ψ Ψ m c d
      (fun S => Hcol (G∪S))
      (fun S => Hcol (G∪S))
      (∏ i ∈ E, p i) Y H A P ≤
      if primeProductNorm p G ≤ lengthScale then
        (diagonalControl sieveCutoff*lengthScale)^2 * (B^2 *
          (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) else 0 := by
  have hdiag := diagonalControl_nonneg sieveCutoff
  let C := B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let w := residualPairWeight p hg Ψ Ψ m c d
    (fun S => Hcol (G∪S))
    (fun S => Hcol (G∪S))
  have hsupp (S T : Finset ι) (hw : w S T ≠ 0) :
      primeProductNorm p G ≤ lengthScale ∧ primeProductNorm p E ≤ lengthScale ∧
      primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale := by
    obtain ⟨hS,hT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
    have hGS := hsupport (G ∪ S) hS
    have hGT := hsupport (G ∪ T) hT
    have hG := (primeProductNorm_mono p hp Finset.subset_union_left).trans hGS
    exact ⟨hG, (primeProductNorm_mono p hp hEG).trans hG,
      (primeProductNorm_mono p hp Finset.subset_union_right).trans hGS,
      (primeProductNorm_mono p hp Finset.subset_union_right).trans hGT⟩
  by_cases hG : primeProductNorm p G ≤ lengthScale
  · rw [if_pos hG]
    calc
      _ ≤ ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset,
          if primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale then C else 0 := by
        unfold residualTailCost
        apply Finset.sum_le_sum
        intro S hS
        apply Finset.sum_le_sum
        intro T hT
        by_cases hd : Disjoint S T
        · rw [if_pos hd]
          dsimp only
          by_cases hw : w S T = 0
          · change ‖w S T‖ * _ ≤ _
            rw [hw, norm_zero, zero_mul]
            split_ifs <;> positivity
          · obtain ⟨_,hE,hSn,hTn⟩ := hsupp S T hw
            rw [if_pos ⟨hSn,hTn⟩]
            have hn2 : ‖ringComplex (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val)‖^2 =
                primeProductNorm p S * primeProductNorm p T := active_norm_sq_disjoint p S T hd
            have hn : 1 ≤ ‖ringComplex (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val)‖ := by
              have hpS := primeProductNorm_ge_one p hp S
              have hpT := primeProductNorm_ge_one p hp T
              have hpST : 1 ≤ primeProductNorm p S * primeProductNorm p T := one_le_mul_of_one_le_of_one_le hpS hpT
              rw [← hn2] at hpST
              nlinarith [norm_nonneg (ringComplex (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val))]
            have hNe : 0 < ‖ringComplex (∏ i ∈ E, p i)‖^2 :=
              primeProductNorm_pos p hp E
            have hden : ‖ringComplex (∏ i ∈ E, p i)‖^2 *
                ‖ringComplex (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val)‖^2 ≤ lengthScale^3 := by
              rw [show ‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 = primeProductNorm p E from rfl, hn2]
              have hST := mul_le_mul hSn hTn (primeProductNorm_pos p hp T).le
                (zero_le_one.trans hL)
              have hEST := mul_le_mul hE hST
                (mul_nonneg (primeProductNorm_pos p hp S).le
                  (primeProductNorm_pos p hp T).le) (zero_le_one.trans hL)
              nlinarith
            have hscalar := tail_radial_scalar_le Y
              (‖ringComplex (∏ i ∈ E, p i)‖^2)
              (‖ringComplex (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val)‖) lengthScale H P A hY hNe hn hL hden hH hP
            exact mul_le_mul (residualPairWeight_bounded_test p hg Ψ hΨ m c d Hcol B hB hcol G S T)
              hscalar (by positivity) (sq_nonneg _)
        · rw [if_neg hd]
          split_ifs <;> positivity
      _ = ((boundedPrimeSupports p (F\G) lengthScale).card : ℝ)^2 * C :=
        sum_pair_indicator (F\G).powerset (fun S => primeProductNorm p S ≤ lengthScale) C
      _ ≤ (diagonalControl sieveCutoff*lengthScale)^2 * C := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (boundedPrimeSupports_card p hinj (F\G) lengthScale hL) 2) hC
  · rw [if_neg hG]
    have hz : residualTailCost p hg F G Ψ Ψ m c d
        (fun S => Hcol (G∪S))
        (fun S => Hcol (G∪S))
        (∏ i ∈ E, p i) Y H A P = 0 := by
      unfold residualTailCost
      apply Finset.sum_eq_zero
      intro S hS
      apply Finset.sum_eq_zero
      intro T hT
      by_cases hd : Disjoint S T
      · rw [if_pos hd]
        have hw : w S T = 0 := by
          by_contra hw
          exact hG (hsupp S T hw).1
        change ‖w S T‖ * _ = 0
        rw [hw, norm_zero, zero_mul]
      · rw [if_neg hd]
    exact hz.le

theorem secondSourceTailCost_bounded_test
    (F : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (Hcol : Finset ι → ℂ) (B Y H lengthScale P : ℝ) (A : ℕ)
    (hB : 0 ≤ B) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (hsupport : ∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) :
    (∑ G ∈ F.powerset, ∑ E ∈ G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E‖ *
      residualTailCost p hg F G Ψ Ψ m c d
        (fun S => Hcol (G∪S))
        (fun S => Hcol (G∪S))
        (∏ i ∈ E, p i) Y H A P) ≤
      (diagonalControl sieveCutoff*lengthScale)^4 * (B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) := by
  have hdiag := diagonalControl_nonneg sieveCutoff
  let C := B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcount : 0 ≤ diagonalControl sieveCutoff*lengthScale := by positivity
  calc
    _ ≤ ∑ G ∈ F.powerset, if primeProductNorm p G ≤ lengthScale then (diagonalControl sieveCutoff*lengthScale)^3*C else 0 := by
      apply Finset.sum_le_sum
      intro G hG
      by_cases hGn : primeProductNorm p G ≤ lengthScale
      · rw [if_pos hGn]
        have heq : boundedPrimeSupports p G lengthScale = G.powerset := by
          apply Finset.filter_eq_self.mpr
          intro E hE
          exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hE)).trans hGn
        have hcard : (G.powerset.card : ℝ) ≤ diagonalControl sieveCutoff*lengthScale := by
          simpa only [heq] using boundedPrimeSupports_card p hinj G lengthScale hL
        calc
          _ ≤ ∑ E ∈ G.powerset, (diagonalControl sieveCutoff*lengthScale)^2*C := by
            apply Finset.sum_le_sum
            intro E hE
            have hr := residualTailCost_bounded_test p hp hg hinj F G E (Finset.mem_powerset.mp hE)
              Ψ hΨ m c d Hcol B Y H lengthScale P A hB hY hH hP hL hcol hsupport
            rw [if_pos hGn] at hr
            have hc := secondSourceCommonCoefficient_norm_le_one p hp hg Ψ hΨ m c d G E
            exact (mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans
              (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg _) hC))
          _ = (G.powerset.card : ℝ)*((diagonalControl sieveCutoff*lengthScale)^2*C) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (diagonalControl sieveCutoff*lengthScale)*((diagonalControl sieveCutoff*lengthScale)^2*C) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (sq_nonneg _) hC)
          _ = _ := by ring
      · rw [if_neg hGn]
        apply Finset.sum_nonpos
        intro E hE
        have hr := residualTailCost_bounded_test p hp hg hinj F G E (Finset.mem_powerset.mp hE)
          Ψ hΨ m c d Hcol B Y H lengthScale P A hB hY hH hP hL hcol hsupport
        rw [if_neg hGn] at hr
        exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hr
    _ = ((boundedPrimeSupports p F lengthScale).card : ℝ)*((diagonalControl sieveCutoff*lengthScale)^3*C) := by
      rw [← Finset.sum_filter]
      simp only [boundedPrimeSupports, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (diagonalControl sieveCutoff*lengthScale)*((diagonalControl sieveCutoff*lengthScale)^3*C) :=
      mul_le_mul_of_nonneg_right (boundedPrimeSupports_card p hinj F lengthScale hL)
        (mul_nonneg (pow_nonneg hcount _) hC)
    _ = _ := by ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

/-- A finite lattice cutoff for columns whose squared norms are bounded by L. -/
def secondTailCutoff (L Y H : ℝ) : Finset O :=
  (Eisenstein.finite_norm_sublevel (Real.sqrt (H * L ^ 3 / Y))).toFinset

lemma secondTailCutoff_complement (L Y H : ℝ) (hL : 0 ≤ L) (hY : 0 < Y) (hH : 0 ≤ H)
    (k : O) (hk : k ∉ secondTailCutoff L Y H) : H * L ^ 3 ≤ Y * ‖ringComplex k‖ ^ 2 := by
  have hout : Real.sqrt (H * L ^ 3 / Y) < ‖ringComplex k‖ := by
    apply lt_of_not_ge
    intro h
    apply hk
    simpa only [secondTailCutoff, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using h
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hout.le 2
  rw [Real.sq_sqrt (div_nonneg (mul_nonneg hH (pow_nonneg hL _)) hY.le)] at hs
  simpa only [mul_comm] using (div_le_iff₀ hY).mp hs

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
theorem secondTailCutoff_uniform
    (Ψ : O →* ℂ) (m c d : O) (Hcol : Finset ι → ℂ) (L Y H : ℝ)
    (hL : 1 ≤ L) (hY : 0 < Y) (hH : 0 ≤ H)
    (hsupport : ∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ L)
    (G E S T : Finset ι) (hEG : E ⊆ G) (hST : Disjoint S T)
    (hw : residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G ∪ U)) (fun U => Hcol (G ∪ U)) S T ≠ 0)
    (k : O) (hk : k ∉ secondTailCutoff L Y H) :
    H ≤ (Y / (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 *
      ‖ringComplex (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val)‖ ^ 2)) * ‖ringComplex k‖ ^ 2 := by
  obtain ⟨hs, ht⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hGS := hsupport (G ∪ S) hs
  have hGT := hsupport (G ∪ T) ht
  have hG := (primeProductNorm_mono p hp Finset.subset_union_left).trans hGS
  have hE := (primeProductNorm_mono p hp hEG).trans hG
  have hS := (primeProductNorm_mono p hp Finset.subset_union_right).trans hGS
  have hT := (primeProductNorm_mono p hp Finset.subset_union_right).trans hGT
  have hE0 := primeProductNorm_pos p hp E
  have hS0 := primeProductNorm_pos p hp S
  have hT0 := primeProductNorm_pos p hp T
  rw [active_norm_sq_disjoint p S T hST]
  change H ≤ (Y / (primeProductNorm p E * (primeProductNorm p S * primeProductNorm p T))) * _
  have hden : primeProductNorm p E * (primeProductNorm p S * primeProductNorm p T) ≤ L ^ 3 := by
    calc
      _ ≤ L * (L * L) := mul_le_mul hE
        (mul_le_mul hS hT hT0.le (zero_le_one.trans hL)) (mul_nonneg hS0.le hT0.le) (zero_le_one.trans hL)
      _ = _ := by ring
  rw [show Y / (primeProductNorm p E * (primeProductNorm p S * primeProductNorm p T)) *
      ‖ringComplex k‖ ^ 2 = Y * ‖ringComplex k‖ ^ 2 /
        (primeProductNorm p E * (primeProductNorm p S * primeProductNorm p T)) by ring]
  apply (le_div_iff₀ (mul_pos hE0 (mul_pos hS0 hT0))).mpr
  exact (mul_le_mul_of_nonneg_left hden hH).trans
    (secondTailCutoff_complement L Y H (zero_le_one.trans hL) hY hH k hk)

/-- Uniform polynomial decay for the complete discarded source of bounded supported columns. -/
theorem full_uniform_secondSourceTail_bounded_test (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
      [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (Hcol : Finset ι → ℂ)
      (W : 𝓢(ℝ, ℂ)) (B L Y H : ℝ),
      (∀ a, ‖Ψ a‖ ≤ 1) → 0 ≤ B → 1 ≤ L → 0 < Y → 0 ≤ H →
      (∀ U, ‖Hcol U‖ ≤ B) → (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ L) →
      ‖secondSourceTail p hp hg F Ψ m c d Hcol W Y (fun _ _ => secondTailCutoff L Y H)‖ ≤
        (diagonalControl sieveCutoff * L) ^ 4 *
          (B ^ 2 * (Y * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            (1 + L ^ 3 / Y) ^ 2 / (1 + H) ^ A)) := by
  obtain ⟨s, C, hC, hb⟩ := full_uniform_secondSourceTail_bound A
  refine ⟨s, C, hC, ?_⟩
  intro ι _ p hp _ hg hinj F Ψ m c d Hcol W B L Y H hΨ hB hL hY hH hcol hsupp
  have h := hb p hp hg hinj F Ψ m c d Hcol W Y H hY hH
    (fun _ _ => secondTailCutoff L Y H) (by
      intro G hG E hE S hS T hT hST hw k hk
      exact secondTailCutoff_uniform p hp hg Ψ m c d Hcol L Y H hL hY hH hsupp
        G E S T (Finset.mem_powerset.mp hE) hST hw k hk)
  exact h.trans (secondSourceTailCost_bounded_test p hp hg hinj F Ψ hΨ m c d Hcol
    B Y H L (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) A hB hY hH
    (mul_nonneg hC.le (apply_nonneg _ _)) hL hcol hsupp)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem primeCoprimeMask_congr_span (S : Finset ι) {a b : O}
    (h : Ideal.span {a} = Ideal.span {b}) : primeCoprimeMask p S a = primeCoprimeMask p S b := by
  have hm (i : ι) : p i ∣ a ↔ p i ∣ b := by
    rw [← Ideal.mem_span_singleton, ← Ideal.mem_span_singleton,
      ← Ideal.span_singleton_le_iff_mem, h, Ideal.span_singleton_le_iff_mem]
  simp only [primeCoprimeMask_indicator, hm]

theorem secondChildColumn_congr_mask_span (Ψ : O →* ℂ) {a b : O}
    (h : Ideal.span {a} = Ideal.span {b}) (f y : O) (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hg Ψ a f y H S = secondChildColumn p hg Ψ b f y H S := by
  simp only [secondChildColumn, primeCoprimeMask_congr_span p S h]

theorem fixedChildRow_congr_mask_span (F : Finset ι) (Ψ : O →* ℂ) {a b : O}
    (h : Ideal.span {a} = Ideal.span {b}) (H : Finset ι → ℂ) (f y : O) :
    fixedChildRow p hg F Ψ a H f y = fixedChildRow p hg F Ψ b H f y := by
  simp only [fixedChildRow, secondChildColumn_congr_mask_span p hg Ψ h]

theorem secondChildColumn_fixed_mask (Ψ : O →* ℂ) (m g f y : O)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hg Ψ (m * g) f y H S =
      primeCoprimeMask p S g * secondChildColumn p hg Ψ m f y H S := by
  rw [secondChildColumn, subsetMask_mul p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S m g]
  unfold secondChildColumn
  ring

theorem fixedChildRow_fixed_pool (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (f y : O) :
    fixedChildRow p hg (F \ G) Ψ m H f y =
      fixedChildRow p hg F Ψ (m * ∏ i ∈ G, p i) H f y := by
  unfold fixedChildRow
  rw [sum_remove_common_pool p hinj]
  simp only [secondChildColumn_fixed_mask]

theorem secondChildColumn_zero_of_mask_label_mem (Ψ : O →* ℂ) (m f y : O)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hmf : m * f ∈ Ideal.span {p i}) : secondChildColumn p hg Ψ m f y H S = 0 := by
  rcases (inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hmf with hm | hf
  · have hz : primeCoprimeMask p S m = 0 := by
      rw [primeCoprimeMask_indicator]
      exact if_neg (fun h => h i hi (Ideal.mem_span_singleton.mp hm))
    simp only [secondChildColumn, hz, mul_zero, zero_mul]
  · have hz : primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S f = 0 := by
      apply Finset.prod_eq_zero hi
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, MulChar.map_zero]
    simp only [secondChildColumn, hz, zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, zero_mul]

theorem fixedChildRow_restore_killed_pool (F B : Finset ι) (Ψ : O →* ℂ)
    (m f y : O) (H : Finset ι → ℂ) (hB : ∀ i ∈ B, m * f ∈ Ideal.span {p i}) :
    fixedChildRow p hg (F \ B) Ψ m H f y = fixedChildRow p hg F Ψ m H f y := by
  unfold fixedChildRow
  apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
  intro S hS hn
  have hd : ¬ Disjoint B S := by
    intro hd
    apply hn
    apply Finset.mem_powerset.mpr
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hS) hi,
      fun hiB => Finset.disjoint_left.mp hd hiB hi⟩
  obtain ⟨i, hiB, hiS⟩ := Finset.not_disjoint_iff.mp hd
  exact secondChildColumn_zero_of_mask_label_mem p hg Ψ m f y H S i hiS (hB i hiB)

def globalSecondMask (m : O) (x : GlobalSecondData ι) : O :=
  (m * globalFirstBadLabel p x.first * ∏ i ∈ x.source.sourceCommon \ x.source.divisor, p i) *
    ∏ i ∈ x.firstCommon, p i

def fixedTripleMask (m : O) (q : Ideal O × Ideal O × Ideal O) : O :=
  m * cubicIdealGenerator q.1 * cubicIdealGenerator q.2.1 * cubicIdealGenerator q.2.2

theorem globalSecondMask_span (m : O) (x : GlobalSecondData ι) :
    Ideal.span {globalSecondMask p m x} = Ideal.span {fixedTripleMask m (globalSecondFixedTriple p x)} := by
  simp only [globalSecondMask, fixedTripleMask, globalSecondFixedTriple, globalFirstBadLabel,
    GlobalSecondData.first, ← Ideal.span_singleton_mul_span_singleton, span_cubicIdealGenerator,
    span_finset_prime_product]
  ring

/-- Every excluded cube prime divides either the coprimality mask or the retained label. -/
theorem globalSecondMask_kills_cube_common (m : O) (x : GlobalSecondData ι) :
    ∀ i ∈ x.cube.support ∪ x.common, globalSecondMask p m x * globalSecondLabel p x ∈ Ideal.span {p i} := by
  intro i hi
  let J := jLabel p x.cube.support (fun i => x.cube.leftExponent i + x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit
  let b0 := globalFirstBadLabel p x.first
  rcases Finset.mem_union.mp hi with hi | hi
  · have hd : p i ∣ J * b0 := (Finset.dvd_prod_of_mem p hi).trans
      (cubeRadical_dvd_jLabel_b0 p x.cube.support
        (fun i => x.cube.leftExponent i + x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit x.cube.support_pos)
    have he : globalSecondMask p m x * globalSecondLabel p x =
        (J * b0) * (m * (∏ i ∈ x.source.sourceCommon \ x.source.divisor, p i) *
          (∏ i ∈ x.firstCommon, p i) * (∏ i ∈ x.common, p i) *
          (∏ i ∈ x.source.divisor, p i) * ∏ i ∈ x.source.overlap, p i) := by
      dsimp only [globalSecondMask, globalSecondLabel, J, b0]
      ring
    rw [he]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_left hd _)
  · apply Ideal.mem_span_singleton.mpr
    have hd : p i ∣ globalSecondLabel p x := by
      unfold globalSecondLabel
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem p hi) _) _) _
    exact dvd_mul_of_dvd_right hd _

theorem globalSecondRawRow_fixed_pool (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (x : GlobalSecondData ι) (y : O) :
    fixedChildRow p hg (globalFirstRawPool F x.first) Ψ
      (m * globalFirstBadLabel p x.first * ∏ i ∈ x.source.sourceCommon \ x.source.divisor, p i)
      H (globalSecondLabel p x) y =
      fixedChildRow p hg F Ψ (fixedTripleMask m (globalSecondFixedTriple p x)) H (globalSecondLabel p x) y := by
  rw [globalFirstRawPool, fixedChildRow_fixed_pool p hg hinj]
  change fixedChildRow p hg (F \ (x.cube.support ∪ x.common)) Ψ (globalSecondMask p m x)
    H (globalSecondLabel p x) y = _
  rw [fixedChildRow_restore_killed_pool p hg F (x.cube.support ∪ x.common) Ψ
    (globalSecondMask p m x) (globalSecondLabel p x) y H (globalSecondMask_kills_cube_common p m x)]
  exact fixedChildRow_congr_mask_span p hg F Ψ (globalSecondMask_span p m x) H _ _

end SecondPassArithmetic

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic SecondPassIntegration JointLogSeparation
open scoped Classical SchwartzMap

/-- The two compact logarithmic profiles combine before frequency twisting. -/
def firstCoreBaseProfile (g V : 𝓢(ℝ, ℂ)) (negative : Bool) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (firstColumnProfile negative V) g

def firstCoreModeProfile (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  frequencyTwist (firstCoreBaseProfile g V negative) (firstSignedHeight negative t)

theorem firstCoreBaseProfile_apply (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (s : ℝ) :
    firstCoreBaseProfile g V negative s = g s * (if negative then star (V s) else V s) := by
  cases negative <;>
    simp only [firstCoreBaseProfile, firstColumnProfile, Bool.false_eq_true, ite_false, ite_true,
      SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.hasTemperateGrowth _),
      smul_eq_mul, conjugateProfile_apply] <;> ring

theorem firstCoreModeProfile_apply (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t s : ℝ) :
    firstCoreModeProfile g V negative t s = g s *
      (if negative then star (V s * kernelLogPhase t (-s)) else V s * kernelLogPhase t (-s)) := by
  cases negative <;>
    simp only [firstCoreModeProfile, frequencyTwist_apply, firstSignedHeight,
      firstCoreBaseProfile_apply, Bool.false_eq_true, ite_false, ite_true,
      star_mul, kernelLogPhase_neg_right, kernelLogPhase_conjugate, neg_neg] <;> ring

theorem firstCoreModeProfile_norm (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t s : ℝ) :
    ‖firstCoreModeProfile g V negative t s‖ = ‖g s‖ * ‖V s‖ := by
  rw [firstCoreModeProfile_apply]
  cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    norm_mul, norm_star, kernelLogPhase_norm, mul_one]

theorem firstCoreModeProfile_support (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t s : ℝ)
    (h : firstCoreModeProfile g V negative t s ≠ 0) : g s ≠ 0 ∧ V s ≠ 0 := by
  have hn : ‖g s‖ * ‖V s‖ ≠ 0 := by
    rw [← firstCoreModeProfile_norm g V negative t s]
    exact norm_ne_zero_iff.mpr h
  exact ⟨norm_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1,
    norm_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).2⟩

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)

include hp in
theorem firstCoreTest_eq_normalized_mode (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t : ℝ)
    (D S : Finset ι) (hDS : Disjoint D S) (X : ℝ) (hX : 0 < X) :
    firstCoreTest (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X)
        negative t D S =
      (‖ringComplex (∏ i ∈ D, p i)‖ : ℂ)⁻¹ *
        normalizedColumn p (fun A => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) A)) S := by
  have hlog : columnLog p X (D ∪ S) = columnLog p (X / primeProductNorm p D) S := by
    unfold columnLog
    rw [primeProductNorm_union p D S hDS]
    congr 1
    field_simp [ne_of_gt (primeProductNorm_pos p hp D)]
  simp only [firstCoreTest, normalizedColumn, hlog,
    Finset.prod_union hDS, map_mul, norm_mul, Complex.ofReal_mul, firstCoreModeProfile_apply]
  ring

variable [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
theorem firstCoreInputRow_eq_mode_row
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (c d : O) (t : ℝ) (z : O) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative r Ψ m
      (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d t z =
      (‖ringComplex (∏ i ∈ D, p i)‖ : ℂ)⁻¹ *
      inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D) Ψ
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (firstFixedColumn p hg negative r (normalizedColumn p (fun A => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) A)))) z := by
  unfold firstCoreInputRow inputConjugateRow supportConjugateSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hDS : Disjoint D S := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hS) disjoint_sdiff_self_right
  unfold secondInputCoefficient firstFixedColumn firstResidueMask
  by_cases hr : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i) = r
  · simp only [if_pos hr, firstCoreTest_eq_normalized_mode p hp g V negative t D S hDS X hX]
    ring
  · simp only [if_neg hr, zero_mul, mul_zero]

end FirstPassCubeLabels

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The finite expansion with fixed first- and second-pass residue columns. -/
def secondFixedExpansionTerm (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (negative : Bool) (r : QuadraticRayRing)
    (ray s q : QuadraticRayRing × QuadraticRayRing) (x : SecondExpansionData ι) : ℂ :=
  secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor *
    secondTotalWeight p hg Ψ Ψ m (∏ i ∈ x.sourceCommon \ x.divisor, p i) c d
      (∏ i ∈ x.divisor, p i) x.frequency (ray, x.overlap) *
    twoPassResidueWeight p hg negative negative x.sourceCommon x.overlap r r ray s q *
    fixedChildKernelPair p hg F Ψ Ψ (m * ∏ i ∈ x.sourceCommon \ x.divisor, p i)
      (c * (∏ i ∈ x.divisor, p i) * ∏ i ∈ x.overlap, p i)
      (d * (∏ i ∈ x.divisor, p i) * x.frequency) (d * (∏ i ∈ x.divisor, p i) * (-x.frequency))
      (combinedFixedColumn p hg negative q.1 s.1 (fun U => H ((x.sourceCommon ∪ x.overlap) ∪ U)))
      (combinedFixedColumn p hg negative q.2 s.2 (fun U => H ((x.sourceCommon ∪ x.overlap) ∪ U)))
      (fun N M => secondFrequencyTest p (∏ i ∈ x.divisor, p i) x.frequency W Y
        (x.overlap ∪ N) (x.overlap ∪ M))

theorem secondExpansionTerm_eq_fixed_residues
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (negative : Bool) (r : QuadraticRayRing)
    (ray : QuadraticRayRing × QuadraticRayRing) (x : SecondExpansionData ι) :
    secondExpansionTerm p hg F Ψ m c d (firstFixedColumn p hg negative r H) W Y ray x =
      ∑ s : QuadraticRayRing × QuadraticRayRing, ∑ q : QuadraticRayRing × QuadraticRayRing,
        secondFixedExpansionTerm p hg F Ψ m c d H W Y negative r ray s q x := by
  unfold secondExpansionTerm
  dsimp only
  rw [secondChildKernelPair_two_pass_residues]
  simp only [Finset.mul_sum, secondFixedExpansionTerm, mul_assoc]

/-- All three finite residue indices can be chosen before summing the arithmetic data. -/
theorem truncatedSecondSource_eq_fixed_residues (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (negative : Bool) (r : QuadraticRayRing)
    (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg F Ψ m c d (firstFixedColumn p hg negative r H) W Y K =
      ∑ ray : QuadraticRayRing × QuadraticRayRing,
        ∑ s : QuadraticRayRing × QuadraticRayRing, ∑ q : QuadraticRayRing × QuadraticRayRing,
          ∑ x ∈ secondExpansionPool F K,
            secondFixedExpansionTerm p hg F Ψ m c d H W Y negative r ray s q x := by
  rw [truncatedSecondSource_eq_expansionPool p hp hg hinj hc hpr]
  simp_rw [secondExpansionTerm_eq_fixed_residues]
  apply Finset.sum_congr rfl
  intro ray _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  exact Finset.sum_comm

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)

include hp in
theorem columnLog_norm_upper (X M : ℝ) (hX : 0 < X) (S : Finset ι)
    (h : columnLog p X S ≤ M) : primeProductNorm p S ≤ X * Real.exp M := by
  have he : primeProductNorm p S = X * Real.exp (columnLog p X S) := by
    rw [columnLog, Real.exp_log (div_pos (primeProductNorm_pos p hp S) hX)]
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) hX.le

include hp in
theorem normalizedColumn_schwartz_bound (g : 𝓢(ℝ, ℂ)) (X : ℝ) (S : Finset ι) :
    ‖normalizedColumn p (fun U => g (columnLog p X U)) S‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
  have hN := primeProductNorm_ge_one p hp S
  have hn : 1 ≤ ‖ringComplex (∏ i ∈ S, p i)‖ := by
    dsimp only [primeProductNorm] at hN
    nlinarith only [hN, norm_nonneg (ringComplex (∏ i ∈ S, p i))]
  simp only [normalizedColumn, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  exact (div_le_self (norm_nonneg _) hn).trans (g.norm_le_seminorm ℝ _)

variable [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
theorem fixedFirstCoreTest_norm_le (g V : 𝓢(ℝ, ℂ)) (X : ℝ) (side : Bool)
    (r : QuadraticRayRing) (t : ℝ) (D S : Finset ι) :
    ‖firstFixedColumn p hg side r (firstCoreTest
      (normalizedColumn p (fun U => g (columnLog p X U))) V (columnLog p X) side t D) S‖ ≤
      SchwartzMap.seminorm ℝ 0 0 g * SchwartzMap.seminorm ℝ 0 0 V := by
  apply (firstFixedColumn_norm_le p hg side r _ S).trans
  have hnorm : ‖firstCoreTest (normalizedColumn p (fun U => g (columnLog p X U)))
      V (columnLog p X) side t D S‖ =
      ‖normalizedColumn p (fun U => g (columnLog p X U)) (D ∪ S)‖ * ‖V (columnLog p X (D ∪ S))‖ := by
    cases side <;> simp only [firstCoreTest, Bool.false_eq_true, ite_false, ite_true,
      norm_mul, norm_star, kernelLogPhase_norm, mul_one]
  rw [hnorm]
  exact mul_le_mul (normalizedColumn_schwartz_bound p hp g X (D ∪ S))
    (V.norm_le_seminorm ℝ _) (norm_nonneg _) (apply_nonneg _ _)

include hp in
theorem fixedFirstCoreTest_support (g V : 𝓢(ℝ, ℂ)) (X M : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) (side : Bool) (r : QuadraticRayRing) (t : ℝ)
    (D S : Finset ι)
    (h : firstFixedColumn p hg side r (firstCoreTest
      (normalizedColumn p (fun U => g (columnLog p X U))) V (columnLog p X) side t D) S ≠ 0) :
    primeProductNorm p S ≤ X * Real.exp M := by
  have hcore : firstCoreTest (normalizedColumn p (fun U => g (columnLog p X U)))
      V (columnLog p X) side t D S ≠ 0 := by
    intro hz
    have hn := firstFixedColumn_norm_le p hg side r
      (firstCoreTest (normalizedColumn p (fun U => g (columnLog p X U))) V (columnLog p X) side t D) S
    rw [hz, norm_zero] at hn
    exact (norm_pos_iff.mpr h).not_ge hn
  have hg0 : g (columnLog p X (D ∪ S)) ≠ 0 := by
    intro hz
    apply hcore
    simp only [firstCoreTest, normalizedColumn, hz, zero_div, zero_mul]
  exact (primeProductNorm_mono p hp Finset.subset_union_right).trans
    (columnLog_norm_upper p hp X M hX (D ∪ S) ((le_abs_self _).trans (hgM _ hg0)))

/-- The tail bound for first-pass columns is uniform in their logarithmic frequency and residues. -/
theorem full_uniform_firstCoreSourceTail_bound (A : ℕ) (g V W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
      [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F D : Finset ι) (Ψ : O →* ℂ) (m c d : O) (X M Y H : ℝ),
      (∀ a, ‖Ψ a‖ ≤ 1) → 0 < X → 0 < Y → 0 ≤ H →
      (∀ u, g u ≠ 0 → |u| ≤ M) → ∀ (side : Bool) (r : QuadraticRayRing) (t : ℝ),
      let L := 1 + X * Real.exp M
      ‖secondSourceTail p hp hg F Ψ m c d
        (firstFixedColumn p hg side r (firstCoreTest
          (normalizedColumn p (fun U => g (columnLog p X U))) V (columnLog p X) side t D))
        W Y (fun _ _ => secondTailCutoff L Y H)‖ ≤
        C * L ^ 4 * Y * (1 + L ^ 3 / Y) ^ 2 / (1 + H) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := full_uniform_secondSourceTail_bounded_test A
  let B := SchwartzMap.seminorm ℝ 0 0 g * SchwartzMap.seminorm ℝ 0 0 V
  let C₀ := (diagonalControl sieveCutoff) ^ 4 * B ^ 2 *
    (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  refine ⟨1 + C₀, by positivity, ?_⟩
  intro ι _ p hp _ hg hinj F D Ψ m c d X M Y H hΨ hX hY hH hgM side r t
  dsimp only
  let L := 1 + X * Real.exp M
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact le_add_of_nonneg_right (mul_nonneg hX.le (Real.exp_pos M).le)
  have hh := hb p hp hg hinj F Ψ m c d _ W B L Y H hΨ
    (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) hL hY hH
    (fixedFirstCoreTest_norm_le p hp hg g V X side r t D)
    (fun S hS => (fixedFirstCoreTest_support p hp hg g V X M hX hgM side r t D S hS).trans
      (by dsimp only [L]; linarith))
  apply hh.trans
  calc
    _ = C₀ * L ^ 4 * Y * (1 + L ^ 3 / Y) ^ 2 / (1 + H) ^ A := by dsimp only [C₀]; ring
    _ ≤ _ := by gcongr; linarith

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

def globalFirstTailLength {ι : Type*} [DecidableEq ι] (p : ι → O)
    (ell M : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  1 + globalFirstBlockColumnScale p ell side b * Real.exp M

/-- The global tail has one constant for every residue, frequency and prime family. -/
theorem globalFirstSourceTail_bound (A : ℕ) (g V W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
      [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
      (Ψ : O →* ℂ) (m : O) (ell M H : ℝ) (side : Bool) (r : QuadraticRayRing) (t : ℝ)
      (Y : GlobalFirstData ι → ℝ),
      (∀ a, ‖Ψ a‖ ≤ 1) → 0 < ell → 0 ≤ H →
      (∀ u, g u ≠ 0 → |u| ≤ M) → (∀ b ∈ s, 0 < Y b) →
      ‖globalFirstSourceTail p hp hg pool s w Ψ m g V W ell side r t Y
        (fun b _ _ => secondTailCutoff (globalFirstTailLength p ell M side b) (Y b) H)‖ ≤
        C / (1 + H) ^ A * ∑ b ∈ s, ‖w b‖ * (globalFirstTailLength p ell M side b) ^ 4 *
          Y b * (1 + (globalFirstTailLength p ell M side b) ^ 3 / Y b) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := full_uniform_firstCoreSourceTail_bound A g V W
  refine ⟨C, hC, ?_⟩
  intro ι _ p hp _ hg hinj pool s w Ψ m ell M H side r t Y hΨ hell hH hgM hY
  unfold globalFirstSourceTail
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ b ∈ s, ‖w b‖ *
        (C * (globalFirstTailLength p ell M side b) ^ 4 * Y b *
          (1 + (globalFirstTailLength p ell M side b) ^ 3 / Y b) ^ 2 / (1 + H) ^ A) := by
      apply Finset.sum_le_sum
      intro b hbmem
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact hb p hp hg hinj (globalFirstRawPool pool b) b.firstCommon Ψ
        (m * globalFirstBadLabel p b) (globalFirstRetainedLabel p b) (∏ i ∈ b.firstDivisor, p i)
        (globalFirstBlockColumnScale p ell side b) M (Y b) H hΨ
        (div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _)))
        (hY b hbmem) hH hgM side r t
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- First-pass finite row energies are bounded by the exact finite source and its complete tail. -/
theorem globalFirstFiniteEnergy_le_sources
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
    (hw : ∀ b ∈ s, 0 ≤ w b) (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ, ℂ))
    (ell : ℝ) (side : Bool) (r : QuadraticRayRing) (t : ℝ) (Y : GlobalFirstData ι → ℝ)
    (hY : ∀ b ∈ s, 0 < Y b) (T : GlobalFirstData ι → Finset O)
    (hT : ∀ b ∈ s, ∀ z ∈ T b, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) :
    (∑ b ∈ s, w b * ∑ z ∈ T b, ‖globalFirstCoreRow p hg pool Ψ m g V ell side r t b z‖ ^ 2) ≤
      ‖globalFirstTruncatedSource p hp hg pool s (fun b => (w b : ℂ)) Ψ m g V rowMajorant ell side r t Y cutoff‖ +
      ‖globalFirstSourceTail p hp hg pool s (fun b => (w b : ℂ)) Ψ m g V rowMajorant ell side r t Y cutoff‖ := by
  let S := fun b => ∑' z : O, rowMajorant (‖ringComplex z‖ ^ 2 / Y b) *
    (‖globalFirstCoreRow p hg pool Ψ m g V ell side r t b z‖ ^ 2 : ℝ)
  calc
    _ ≤ ∑ b ∈ s, w b * (S b).re := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left
        (finite_row_energy_le_rowMajorant _ (T b) (Y b) (hY b hb) (hT b hb)) (hw b hb)
    _ = (∑ b ∈ s, (w b : ℂ) * S b).re := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    _ = (globalFirstTruncatedSource p hp hg pool s (fun b => (w b : ℂ)) Ψ m g V rowMajorant ell side r t Y cutoff +
        globalFirstSourceTail p hp hg pool s (fun b => (w b : ℂ)) Ψ m g V rowMajorant ell side r t Y cutoff).re :=
      congrArg Complex.re (globalFirstCoreRows_eq_truncated_add_tail p hp hg hinj pool s
        (fun b => (w b : ℂ)) Ψ m g V rowMajorant ell side r t Y hY cutoff)
    _ ≤ _ := by
      rw [Complex.add_re]
      exact add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _)

end SecondPassArithmetic

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson JointLogSeparation SecondPassArithmetic
open scoped Classical SchwartzMap ContDiff

/-- Removing common prime factors shifts the logarithmic scale. -/
theorem normalizedColumn_pair_extract_fixed_profiles {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G S T : Finset ι)
    (hGS : Disjoint G S) (hGT : Disjoint G T)
    (X : ℝ) (hX : 0 < X) (U : ℝ → ℂ)
    (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    star (normalizedColumn p (fun A => g₁ (columnLog p X A)) (G ∪ S)) *
      normalizedColumn p (fun A => g₂ (columnLog p X A)) (G ∪ T) =
      (X : ℂ)⁻¹ *
        star (halfNormalizationCLM U g₁ (columnLog p (X / primeProductNorm p G) S)) *
        halfNormalizationCLM U g₂ (columnLog p (X / primeProductNorm p G) T) := by
  have hG := primeProductNorm_pos p hp G
  have hs : primeProductNorm p G * (X / primeProductNorm p G) / X = 1 := by
    field_simp [ne_of_gt hG, ne_of_gt hX]
  simpa only [hs, Real.log_one, zero_add, conjugateProfile_apply] using
    normalizedColumn_pair_union p hp G S T hGS hGT X (X / primeProductNorm p G)
      hX (div_pos hX hG) U hUc hUs g₁ g₂ hU₁ hU₂

/-- The normalized source contributes its height divided by the original column scale. -/
theorem secondFrequencyTest_normalized_shift {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G S T : Finset ι)
    (hGS : Disjoint G S) (hGT : Disjoint G T)
    (e k : O) (X Y : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    (star (normalizedColumn p (fun A => g₁ (columnLog p X A)) (G ∪ S)) *
      normalizedColumn p (fun A => g₂ (columnLog p X A)) (G ∪ T)) *
      secondFrequencyTest p e k W Y S T =
      ((Y : ℂ) / X) * radialPairKernel p e k W
        (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂)
        (X / primeProductNorm p G) (X / primeProductNorm p G) Y S T := by
  rw [normalizedColumn_pair_extract_fixed_profiles p hp G S T hGS hGT X hX U hUc hUs
    g₁ g₂ hU₁ hU₂]
  simp only [secondFrequencyTest, radialPairKernel, normalizedColumn, star_div₀,
    Complex.star_def, Complex.conj_ofReal, div_eq_mul_inv, mul_inv_rev, map_mul, map_inv₀]
  ring

end SecondPassIntegration

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem combinedFixedColumn_test_factor (negative : Bool) (r s : QuadraticRayRing)
    (H : Finset ι → ℂ) (N : Finset ι) :
    combinedFixedColumn p hg negative r s H N =
      combinedFixedColumn p hg negative r s (fun _ => 1) N * H N := by
  simp only [combinedFixedColumn, secondRayColumn, firstFixedColumn, firstResidueMask]
  split_ifs <;> ring

end FirstPassCubeLabels

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration JointLogSeparation
open scoped Classical SchwartzMap ContDiff

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem fixedChildKernelPair_const_kernel
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (H₁ H₂ : Finset ι → ℂ) (a : ℂ) (K : Finset ι → Finset ι → ℂ) :
    fixedChildKernelPair p hg F Ψ₁ Ψ₂ m f y₁ y₂ H₁ H₂ (fun S T => a * K S T) =
      a * fixedChildKernelPair p hg F Ψ₁ Ψ₂ m f y₁ y₂ H₁ H₂ K := by
  simp only [fixedChildKernelPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N _
  apply Finset.sum_congr rfl
  intro M _
  ring

/-- Source primes annihilate every column where a kernel extension could differ. -/
theorem weighted_fixedChildKernelPair_congr_off_source
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k : O) (ray : QuadraticRayRing × QuadraticRayRing)
    (H₁ H₂ : Finset ι → ℂ) (K L : Finset ι → Finset ι → ℂ)
    (hKL : ∀ S T, Disjoint G S → Disjoint G T → K S T = L S T) :
    secondTotalWeight p hg Ψ₁ Ψ₂ m (∏ i ∈ G \ E, p i) c d (∏ i ∈ E, p i) k (ray,V) *
      fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m * ∏ i ∈ G \ E, p i)
        (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i)
        (d * (∏ i ∈ E, p i) * k) (d * (∏ i ∈ E, p i) * (-k)) H₁ H₂
        (fun N M => K (V ∪ N) (V ∪ M)) =
    secondTotalWeight p hg Ψ₁ Ψ₂ m (∏ i ∈ G \ E, p i) c d (∏ i ∈ E, p i) k (ray,V) *
      fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m * ∏ i ∈ G \ E, p i)
        (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i)
        (d * (∏ i ∈ E, p i) * k) (d * (∏ i ∈ E, p i) * (-k)) H₁ H₂
        (fun N M => L (V ∪ N) (V ∪ M)) := by
  by_cases hGV : Disjoint G V
  · simp only [fixedChildKernelPair, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro N _
    apply Finset.sum_congr rfl
    intro M _
    by_cases hGN : Disjoint G N
    · by_cases hGM : Disjoint G M
      · rw [hKL _ _ (Finset.disjoint_union_right.mpr ⟨hGV,hGN⟩)
          (Finset.disjoint_union_right.mpr ⟨hGV,hGM⟩)]
      · rw [secondChildColumn_zero_of_source_overlap p hg Ψ₂ m c
          (d * (∏ i ∈ E, p i) * (-k)) H₂ G E V M hGM]
        ring
    · rw [secondChildColumn_zero_of_source_overlap p hg Ψ₁ m c
        (d * (∏ i ∈ E, p i) * k) H₁ G E V N hGN, star_zero]
      ring
  · rw [secondTotalWeight_zero_of_source_overlap p hg Ψ₁ Ψ₂ m c d k G E V hEG ray hGV]
    simp only [zero_mul]

/-- Fixed residue columns retain the arithmetic phases while profiles enter the kernel. -/
theorem fixedChildKernelPair_combined_tests
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (negative₁ negative₂ : Bool) (r₁ r₂ s₁ s₂ : QuadraticRayRing)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    fixedChildKernelPair p hg F Ψ₁ Ψ₂ m f y₁ y₂
      (combinedFixedColumn p hg negative₁ r₁ s₁ H₁)
      (combinedFixedColumn p hg negative₂ r₂ s₂ H₂) K =
    fixedChildKernelPair p hg F Ψ₁ Ψ₂ m f y₁ y₂
      (combinedFixedColumn p hg negative₁ r₁ s₁ (fun _ => 1))
      (combinedFixedColumn p hg negative₂ r₂ s₂ (fun _ => 1))
      (fun N M => (star (H₁ N) * H₂ M) * K N M) := by
  unfold fixedChildKernelPair
  apply Finset.sum_congr rfl
  intro N _
  apply Finset.sum_congr rfl
  intro M _
  have h₁ := combinedFixedColumn_test_factor p hg negative₁ r₁ s₁ H₁ N
  have h₂ := combinedFixedColumn_test_factor p hg negative₂ r₂ s₂ H₂ M
  simp only [secondChildColumn, h₁, h₂, star_mul]
  ring

/-- The source height and column normalization become a single outer scalar. -/
theorem weighted_fixedChildKernelPair_normalized (hp : ∀ i, p i ≠ 0)
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k : O) (ray : QuadraticRayRing × QuadraticRayRing)
    (negative₁ negative₂ : Bool) (r₁ r₂ s₁ s₂ : QuadraticRayRing)
    (X Y : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ u, g₁ u ≠ 0 → U u = 1)
    (hU₂ : ∀ u, g₂ u ≠ 0 → U u = 1) :
    secondTotalWeight p hg Ψ₁ Ψ₂ m (∏ i ∈ G \ E, p i) c d (∏ i ∈ E, p i) k (ray,V) *
      fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m * ∏ i ∈ G \ E, p i)
        (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i)
        (d * (∏ i ∈ E, p i) * k) (d * (∏ i ∈ E, p i) * (-k))
        (combinedFixedColumn p hg negative₁ r₁ s₁
          (fun N => normalizedColumn p (fun A => g₁ (columnLog p X A)) ((G ∪ V) ∪ N)))
        (combinedFixedColumn p hg negative₂ r₂ s₂
          (fun N => normalizedColumn p (fun A => g₂ (columnLog p X A)) ((G ∪ V) ∪ N)))
        (fun N M => secondFrequencyTest p (∏ i ∈ E, p i) k W Y (V ∪ N) (V ∪ M)) =
    (((Y : ℂ) / X) * secondTotalWeight p hg Ψ₁ Ψ₂ m
      (∏ i ∈ G \ E, p i) c d (∏ i ∈ E, p i) k (ray,V)) *
      fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m * ∏ i ∈ G \ E, p i)
        (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i)
        (d * (∏ i ∈ E, p i) * k) (d * (∏ i ∈ E, p i) * (-k))
        (combinedFixedColumn p hg negative₁ r₁ s₁ (fun _ => 1))
        (combinedFixedColumn p hg negative₂ r₂ s₂ (fun _ => 1))
        (fun N M => radialPairKernel p (∏ i ∈ E, p i) k W
          (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂)
          (X / primeProductNorm p G) (X / primeProductNorm p G) Y (V ∪ N) (V ∪ M)) := by
  rw [fixedChildKernelPair_combined_tests]
  simp only [Finset.union_assoc]
  have hn := weighted_fixedChildKernelPair_congr_off_source p hg G E hEG F V Ψ₁ Ψ₂ m c d k ray
    (combinedFixedColumn p hg negative₁ r₁ s₁ (fun _ => 1))
    (combinedFixedColumn p hg negative₂ r₂ s₂ (fun _ => 1))
    (fun S T => (star (normalizedColumn p (fun A => g₁ (columnLog p X A)) (G ∪ S)) *
      normalizedColumn p (fun A => g₂ (columnLog p X A)) (G ∪ T)) *
      secondFrequencyTest p (∏ i ∈ E, p i) k W Y S T)
    (fun S T => ((Y : ℂ) / X) * radialPairKernel p (∏ i ∈ E, p i) k W
      (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂)
      (X / primeProductNorm p G) (X / primeProductNorm p G) Y S T)
    (fun S T hGS hGT => secondFrequencyTest_normalized_shift p hp G S T hGS hGT
      (∏ i ∈ E, p i) k X Y hX U hUc hUs g₁ g₂ W hU₁ hU₂)
  rw [fixedChildKernelPair_const_kernel] at hn
  exact hn.trans (by ring)

end SecondPassArithmetic

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson JointLogSeparation SecondPassArithmetic
open scoped Classical SchwartzMap ContDiff

theorem full_uniform_normalized_child_tests
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i}),
      ∀ (D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (H₁ H₂ : Finset ι → ℂ),
        d ≠ 0 → e ≠ 0 → k ≠ 0 →
        |Real.log (primeProductNorm p V * X₀ / X)| ≤ B →
        |Real.log (elementNorm d / D)| ≤ B →
        |Real.log (elementNorm e / E)| ≤ B →
        |Real.log (primeProductNorm p V / V₀)| ≤ B →
        |Real.log (elementNorm (d*e*k) / K)| ≤ B →
        fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k) (d*e*(-k)) H₁ H₂
          (fun N M => radialPairKernel p e k W g₁ g₂ X X Y (V∪N) (V∪M)) =
        (X : ℂ)⁻¹ * postCommonSmoothPair p hg H₁ H₂ F Ψ₁ Ψ₂ (m*r)
          (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) A₁ A₂ W windows
          (Real.log (primeProductNorm p V * X₀ / X)) (Real.log (elementNorm d / D))
          (Real.log (elementNorm e / E)) (Real.log (primeProductNorm p V / V₀))
          (Real.log (elementNorm (d*e*k) / K)) X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  obtain ⟨U, hUc, hUs, hUone, hUsupp, hUzero⟩ :=
    JointLogSeparation.exists_complex_smooth_cutoff A hA
  have hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₁ s hs)
  have hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₂ s hs)
  let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
  let A₂ := halfNormalizationCLM U g₂
  have hA₁ : ∀ s, A₁ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply halfNormalization_support_bound U hUc hUs g₁ A hg₁ s
    intro hz
    exact hs (by simp [A₁, hz])
  have hA₂ : ∀ s, A₂ s ≠ 0 → |s| ≤ A :=
    halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨windows, hwc, hws, hwb, hwo, hwt⟩ := exists_fixed_sector_windows A B hA hB
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro ι _ p hp _ hg D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F V Ψ₁ Ψ₂ m r c d e k H₁ H₂ hd he hk hz hud hue huv hkap
  apply fixedChildKernelPair_eq_postCommon p hp hg F V Ψ₁ Ψ₂ m r c d e k H₁ H₂ hd he hk
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs g₁ g₂ W hU₁ hU₂ windows
  · exact hwo _ _ _ _ _ hz hud hue huv hkap
  · exact fun a ha => hwt A₁ _ hA₁ hz 5 a ha
  · exact fun a ha => hwt A₂ _ hA₂ hz 6 a ha

end SecondPassIntegration

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def globalActualResidualScale (ell : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℝ :=
  globalFirstColumnScale p ell x side /
    (primeProductNorm p x.firstCommon * primeProductNorm p x.source.divisor *
      primeProductNorm p (x.source.sourceCommon \ x.source.divisor))

include hp in
theorem globalActualResidualScale_pos (ell : ℝ) (hell : 0 < ell) (side : Bool) (x : GlobalSecondData ι) :
    0 < globalActualResidualScale p ell side x :=
  div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (mul_pos (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
      (primeProductNorm_pos p hp _))

theorem globalResidualScale_eq (ell : ℝ) (side : Bool) (x : GlobalSecondData ι)
    (hE : x.source.divisor ⊆ x.source.sourceCommon) :
    (globalFirstColumnScale p ell x side / primeProductNorm p x.firstCommon) /
      primeProductNorm p x.source.sourceCommon = globalActualResidualScale p ell side x := by
  have hnorm : primeProductNorm p x.source.sourceCommon =
      primeProductNorm p x.source.divisor *
        primeProductNorm p (x.source.sourceCommon \ x.source.divisor) := by
    rw [← primeProductNorm_union p _ _ disjoint_sdiff_self_right,
      Finset.union_sdiff_of_subset hE]
  rw [hnorm]
  unfold globalActualResidualScale
  ring

def globalBinZ (ell : ℝ) (side : Bool) (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  Real.log (primeProductNorm p x.source.overlap * globalPooledColumnScale ell j /
    globalActualResidualScale p ell side x)

def globalBinUd (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  Real.log (primeProductNorm p x.firstDivisor / globalLogRep j 5)

def globalBinUe (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  Real.log (primeProductNorm p x.source.divisor / globalLogRep j 6)

def globalBinUv (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  Real.log (primeProductNorm p x.source.overlap / globalLogRep j 7)

def globalBinKap (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  Real.log (‖ringComplex (SecondPassFiber.newRow (globalSecondTuple p x))‖ ^ 2 / globalLogRep j 8)

include hp in
/-- Six logarithmic bin errors bound every coordinate of the normalized kernel. -/
theorem globalPooled_log_coordinates (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    let j := globalScaleIndex p side x
    |globalBinZ p ell side j x| ≤ 6 ∧ |globalBinUd p j x| ≤ 6 ∧
    |globalBinUe p j x| ≤ 6 ∧ |globalBinUv p j x| ≤ 6 ∧ |globalBinKap p j x| ≤ 6 := by
  let j := globalScaleIndex p side x
  have hpos (i : Fin 10) : 0 < globalScaleVector p side x i :=
    zero_lt_one.trans_le (globalScaleVector_ge_one p hp side x hk i)
  have herr (i : Fin 10) := globalScaleIndex_error p hp side x hk i
  have hn (i : Fin 10) : globalScaleVector p side x i / globalLogRep j i ≠ 0 :=
    div_ne_zero (hpos i).ne' (globalLogRep_pos j i).ne'
  have hprod : primeProductNorm p x.source.overlap * globalPooledColumnScale ell j /
      globalActualResidualScale p ell side x =
      (globalScaleVector p side x 0 / globalLogRep j 0) *
      (globalScaleVector p side x 1 / globalLogRep j 1) *
      (globalScaleVector p side x 2 / globalLogRep j 2) *
      (globalScaleVector p side x 3 / globalLogRep j 3) *
      (globalScaleVector p side x 6 / globalLogRep j 6) *
      (globalScaleVector p side x 7 / globalLogRep j 7) := by
    have h (i : Fin 10) := (globalLogRep_pos j i).ne'
    have hA := (primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
    have hC := (primeProductNorm_pos p hp x.common).ne'
    have ht := (primeProductNorm_pos p hp x.firstCommon).ne'
    have he := (primeProductNorm_pos p hp x.source.divisor).ne'
    have hr := (primeProductNorm_pos p hp (x.source.sourceCommon \ x.source.divisor)).ne'
    change _ = (primeProductNorm p (x.cube.sideDivisor side) / globalLogRep j 0) *
      (primeProductNorm p x.common / globalLogRep j 1) *
      (primeProductNorm p x.firstCommon / globalLogRep j 2) *
      (primeProductNorm p (x.source.sourceCommon \ x.source.divisor) / globalLogRep j 3) *
      (primeProductNorm p x.source.divisor / globalLogRep j 6) *
      (primeProductNorm p x.source.overlap / globalLogRep j 7)
    unfold globalPooledColumnScale globalActualResidualScale globalFirstColumnScale
    field_simp [h, ne_of_gt hell, hA, hC, ht, he, hr] <;> ring
  have hlog : 0 ≤ globalBinZ p ell side j x ∧ globalBinZ p ell side j x ≤ 6 := by
    unfold globalBinZ
    have h01 := mul_ne_zero (hn 0) (hn 1)
    have h012 := mul_ne_zero h01 (hn 2)
    have h0123 := mul_ne_zero h012 (hn 3)
    have h01236 := mul_ne_zero h0123 (hn 6)
    rw [hprod, Real.log_mul h01236 (hn 7), Real.log_mul h0123 (hn 6),
      Real.log_mul h012 (hn 3), Real.log_mul h01 (hn 2), Real.log_mul (hn 0) (hn 1)]
    constructor
    · linarith only [(herr 0).1, (herr 1).1, (herr 2).1, (herr 3).1, (herr 6).1, (herr 7).1]
    · linarith only [(herr 0).2, (herr 1).2, (herr 2).2, (herr 3).2, (herr 6).2, (herr 7).2]
  have hsmall (i : Fin 10) : |Real.log (globalScaleVector p side x i / globalLogRep j i)| ≤ 6 := by
    rw [abs_of_nonneg (herr i).1]
    exact (herr i).2.trans (by norm_num)
  exact ⟨(abs_of_nonneg hlog.1).trans_le hlog.2, hsmall 5, hsmall 6, hsmall 7, hsmall 8⟩

def globalBinRadial (ell Y : ℝ) (j : GlobalLogIndex) : ℝ :=
  Y * globalLogRep j 8 /
    (globalLogRep j 5 * (globalLogRep j 6)^2 * (globalLogRep j 7)^2 * (globalPooledColumnScale ell j)^2)

theorem globalBinRadial_pos (ell Y : ℝ) (hell : 0 < ell) (hY : 0 < Y) (j : GlobalLogIndex) :
    0 < globalBinRadial ell Y j := by
  have h5 := globalLogRep_pos j 5
  have h6 := globalLogRep_pos j 6
  have h7 := globalLogRep_pos j 7
  have h8 := globalLogRep_pos j 8
  have hX := globalPooledColumnScale_pos ell hell j
  unfold globalBinRadial
  positivity

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- Agreement on the finite prime pool suffices to extract a scalar from both source columns. -/
theorem truncatedSecondSource_congr_scaled
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H H' : Finset ι → ℂ) (a : ℂ)
    (hH : ∀ S ⊆ F, H S = a * H' S) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg F Ψ m c d H W Y K =
      (star a * a) * truncatedSecondSource p hp hg F Ψ m c d H' W Y K := by
  simp only [truncatedSecondSource, secondFrequencyKernel, secondKernelPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd, secondGaussTerm, secondInputCoefficient,
      hH (G ∪ S) (Finset.union_subset (Finset.mem_powerset.mp hG) (Finset.mem_powerset.mp hS)),
      hH (G ∪ T) (Finset.union_subset (Finset.mem_powerset.mp hG) (Finset.mem_powerset.mp hT)), star_mul]
    ring
  · simp only [if_neg hd, mul_zero]

/-- The first common divisor contributes its reciprocal squared norm to the second source. -/
theorem truncatedSecondSource_firstCore_mode
    (F D : Finset ι) (hDF : Disjoint D F) (Ψ : O →* ℂ) (m c d : O)
    (g V W : 𝓢(ℝ, ℂ)) (X Y : ℝ) (hX : 0 < X)
    (side : Bool) (r : QuadraticRayRing) (t : ℝ)
    (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg F Ψ m c d
      (firstFixedColumn p hg side r (firstCoreTest
        (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) side t D)) W Y K =
    (primeProductNorm p D : ℂ)⁻¹ * truncatedSecondSource p hp hg F Ψ m c d
      (firstFixedColumn p hg side r (normalizedColumn p (fun A => firstCoreModeProfile g V side t
        (columnLog p (X / primeProductNorm p D) A)))) W Y K := by
  have he := truncatedSecondSource_congr_scaled p hp hg F Ψ m c d
    (firstFixedColumn p hg side r (firstCoreTest
      (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) side t D))
    (firstFixedColumn p hg side r (normalizedColumn p (fun A => firstCoreModeProfile g V side t
      (columnLog p (X / primeProductNorm p D) A))))
    (‖ringComplex (∏ i ∈ D, p i)‖ : ℂ)⁻¹ (by
      intro S hS
      have hh := firstCoreTest_eq_normalized_mode p hp g V side t D S
        (Finset.disjoint_of_subset_right hS hDF) X hX
      simp only [firstFixedColumn, firstResidueMask]
      split_ifs <;> (try simp only [hh]) <;> ring) W Y K
  simpa only [primeProductNorm, Complex.ofReal_pow, star_inv₀, Complex.star_def,
    Complex.conj_ofReal, inv_pow, pow_two, Complex.ofReal_mul, mul_inv_rev] using he

end SecondPassArithmetic

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson JointLogSeparation SecondPassArithmetic
open scoped Classical SchwartzMap ContDiff

theorem normalized_conjugate_frequencyTwist (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    conjugateProfile (halfNormalizationCLM U (frequencyTwist g t)) =
      frequencyTwist (conjugateProfile (halfNormalizationCLM U g)) (-t) := by
  rw [halfNormalization_twist U hUc hUs]
  ext s
  simp only [conjugateProfile_apply, frequencyTwist_apply, star_mul, kernelLogPhase_conjugate]
  ring

theorem full_uniform_twisted_normalized_child_tests
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (θ₁ θ₂ D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (H₁ H₂ : Finset ι → ℂ),
        d ≠ 0 → e ≠ 0 → k ≠ 0 →
        |Real.log (primeProductNorm p V * X₀ / X)| ≤ B →
        |Real.log (elementNorm d / D)| ≤ B →
        |Real.log (elementNorm e / E)| ≤ B →
        |Real.log (primeProductNorm p V / V₀)| ≤ B →
        |Real.log (elementNorm (d*e*k) / K)| ≤ B →
        fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k) (d*e*(-k)) H₁ H₂
          (fun N M => radialPairKernel p e k W (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) X X Y (V∪N) (V∪M)) =
        (X : ℂ)⁻¹ * postCommonSmoothPair p hg H₁ H₂ F Ψ₁ Ψ₂ (m*r)
          (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows
          (Real.log (primeProductNorm p V * X₀ / X)) (Real.log (elementNorm d / D))
          (Real.log (elementNorm e / E)) (Real.log (primeProductNorm p V / V₀))
          (Real.log (elementNorm (d*e*k) / K)) X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  obtain ⟨U, hUc, hUs, hUone, hUsupp, hUzero⟩ :=
    JointLogSeparation.exists_complex_smooth_cutoff A hA
  have hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₁ s hs)
  have hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₂ s hs)
  let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
  let A₂ := halfNormalizationCLM U g₂
  have hA₁ : ∀ s, A₁ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply halfNormalization_support_bound U hUc hUs g₁ A hg₁ s
    intro hz
    exact hs (by simp [A₁, hz])
  have hA₂ : ∀ s, A₂ s ≠ 0 → |s| ≤ A :=
    halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨windows, hwc, hws, hwb, hwo, hwt⟩ := exists_fixed_sector_windows A B hA hB
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro ι _ p hp _ hg
    θ₁ θ₂ D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F V Ψ₁ Ψ₂ m r c d e k H₁ H₂ hd he hk hz hud hue huv hkap
  have htw₁ : ∀ s, frequencyTwist g₁ θ₁ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₁ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have htw₂ : ∀ s, frequencyTwist g₂ θ₂ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₂ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hsupp₁ : ∀ s, frequencyTwist A₁ (-θ₁) s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply hA₁ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hsupp₂ : ∀ s, frequencyTwist A₂ θ₂ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply hA₂ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hh := fixedChildKernelPair_eq_postCommon p hp hg F V Ψ₁ Ψ₂ m r c d e k H₁ H₂ hd he hk
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs
    (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W htw₁ htw₂ windows
  dsimp only at hh
  rw [normalized_conjugate_frequencyTwist U hUc hUs,
    halfNormalization_twist U hUc hUs] at hh
  exact hh (hwo _ _ _ _ _ hz hud hue huv hkap)
    (fun a ha => hwt (frequencyTwist A₁ (-θ₁)) _ hsupp₁ hz 5 a ha)
    (fun a ha => hwt (frequencyTwist A₂ θ₂) _ hsupp₂ hz 6 a ha)


end SecondPassIntegration

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
