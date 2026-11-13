/-
Divisor blocks and radial kernel transfer adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.QuadraticMaskIdeals
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.CoprimeBilinearSieve

/-!
# Divisor blocks and radial kernel transfer

Coprime bilinear blocks with fixed divisor masks reduce to operator norms by two divisor
Cauchy inequalities. The logarithmic kernel phase `kernelLogPhase`, Euler-weighted radial
Fourier bounds, and the transfer of radial matrix kernels (`QuadraticKernelTransfer`).
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

namespace IdealDivisorBilinearBlocks
open Eisenstein FiniteSieveOperator DivisorBlockCauchy IdealCoprimeBilinearSieve

/-- A coprime bilinear block with fixed divisor masks on its two columns. -/
def blockValue {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (left : n → Ideal O) (right : p → Ideal O)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  ∑ i, ‖∑ j, ∑ k, if left j ⊔ right k = ⊤ then
    star (A D i j * (if D ∣ left j then a j else 0)) *
      (B E i k * (if E ∣ right k then b k else 0)) else 0‖

lemma blockValue_nonneg {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (left : n → Ideal O) (right : p → Ideal O)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : 0 ≤ blockValue left right A B a b D E :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- Two divisor Cauchy inequalities reduce the block to ordinary operator norms. -/
theorem divisor_block_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (left : n → Ideal O) (right : p → Ideal O)
    (hl : ∀ j, left j ≠ 0) (hr : ∀ k, right k ≠ 0)
    (N₁ N₂ : ℝ) (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hlN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N₁)
    (hrN : ∀ k, (Ideal.absNorm (right k) : ℝ) ≤ N₂)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (UA UB : ℝ) (hUA : 0 ≤ UA) (hUB : 0 ≤ UB)
    (hA : ∀ D ∈ S, ‖operator (A D)‖ ^ 2 ≤ UA)
    (hB : ∀ E ∈ T, ‖operator (B E)‖ ^ 2 ≤ UB) :
    (∑ D ∈ S, ∑ E ∈ T, blockValue left right A B a b D E) ^ 2 ≤
      (S.card : ℝ) * T.card * UA * UB *
        (divisorConstant ε hε * N₁ ^ ε) ^ 2 *
        (divisorConstant ε hε * N₂ ^ ε) ^ 2 *
        (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) := by
  let EL (D : Ideal O) : ℝ := ∑ j, ‖if D ∣ left j then a j else 0‖ ^ 2
  let ER (E : Ideal O) : ℝ := ∑ k, ‖if E ∣ right k then b k else 0‖ ^ 2
  let C := UA * UB * (divisorConstant ε hε * N₁ ^ ε) * (divisorConstant ε hε * N₂ ^ ε)
  have hd := (divisorConstant_pos ε hε).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hEL (D) : 0 ≤ EL D := by dsimp [EL]; positivity
  have hER (E) : 0 ≤ ER E := by dsimp [ER]; positivity
  have hp (D : Ideal O) (hD : D ∈ S) (E : Ideal O) (hE : E ∈ T) :
      (blockValue left right A B a b D E) ^ 2 ≤ C * EL D * ER E := by
    have h := ideal_coprime_bilinear_operator_bound ε hε left right hl hr N₁ N₂ hlN hrN
      (A D) (B E) (fun j => if D ∣ left j then a j else 0)
      (fun k => if E ∣ right k then b k else 0)
    change (blockValue left right A B a b D E) ^ 2 ≤
      (‖operator (A D)‖ ^ 2 * (divisorConstant ε hε * N₁ ^ ε) * EL D) *
      (‖operator (B E)‖ ^ 2 * (divisorConstant ε hε * N₂ ^ ε) * ER E) at h
    apply h.trans
    calc
      _ ≤ (UA * (divisorConstant ε hε * N₁ ^ ε) * EL D) *
          (UB * (divisorConstant ε hε * N₂ ^ ε) * ER E) := by
        gcongr
        · exact hA D hD
        · exact hB E hE
      _ = _ := by dsimp [C]; ring
  have hc := rectangular_cauchy S T (blockValue left right A B a b) EL ER C hC hp
  have hL := divisor_mask_energy_small_power ε hε S left hl N₁ hlN a
  have hR := divisor_mask_energy_small_power ε hε T right hr N₂ hrN b
  change (∑ D ∈ S, EL D) ≤ _ at hL
  change (∑ E ∈ T, ER E) ≤ _ at hR
  calc
    _ ≤ (S.card : ℝ) * T.card * C * (∑ D ∈ S, EL D) * (∑ E ∈ T, ER E) := hc
    _ ≤ (S.card : ℝ) * T.card * C *
        ((divisorConstant ε hε * N₁ ^ ε) * ∑ j, ‖a j‖ ^ 2) *
        ((divisorConstant ε hε * N₂ ^ ε) * ∑ k, ‖b k‖ ^ 2) := by gcongr
    _ = _ := by dsimp [C]; ring

end IdealDivisorBilinearBlocks

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein IdealDivisorBilinearBlocks DivisorBlockCauchy

def quotientBlock {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  blockValue (fun j => (left j).val) (fun k => (right k).val)
    (fun D => quotientMatrix D rows left) (fun E => quotientMatrix E rows right) a b D E

/-- Removing divisors shrinks the two conductor ranges independently. -/
theorem quotient_divisor_block_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) (hN : 0 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ))
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N) (a : n → ℂ) (b : p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 ≤
      (S.card : ℝ) * T.card * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
        (divisorConstant ε hε * N ^ ε) ^ 4 * (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) := by
  have hA (D : Ideal O) (hD : D ∈ S) :
      ‖FiniteSieveOperator.operator (quotientMatrix D rows left)‖ ^ 2 ≤ sieveNorm M (N / D₁) := by
    have hD0 : D ≠ 0 := by
      intro hz
      have hn := hS D hD
      simp only [hz, map_zero, Nat.cast_zero] at hn
      exact (not_le_of_gt hD₁) hn
    exact (quotientMatrix_squared_norm_le D hD0 rows left hr hl M N hrows hleft).trans
      (sieveNorm_mono le_rfl (div_le_div_of_nonneg_left hN hD₁ (hS D hD)))
  have hB (E : Ideal O) (hE : E ∈ T) :
      ‖FiniteSieveOperator.operator (quotientMatrix E rows right)‖ ^ 2 ≤ sieveNorm M (N / D₂) := by
    have hE0 : E ≠ 0 := by
      intro hz
      have hn := hT E hE
      simp only [hz, map_zero, Nat.cast_zero] at hn
      exact (not_le_of_gt hD₂) hn
    exact (quotientMatrix_squared_norm_le E hE0 rows right hr hri M N hrows hright).trans
      (sieveNorm_mono le_rfl (div_le_div_of_nonneg_left hN hD₂ (hT E hE)))
  have h := divisor_block_bound ε hε S T (fun j => (left j).val) (fun k => (right k).val)
    (fun j => primaryIdealGenerator_ne_zero_ideal _ (left j).property.1)
    (fun k => primaryIdealGenerator_ne_zero_ideal _ (right k).property.1)
    N N hN hN hleft hright
    (fun D => quotientMatrix D rows left) (fun E => quotientMatrix E rows right) a b
    (sieveNorm M (N / D₁)) (sieveNorm M (N / D₂)) (sieveNorm_nonneg _ _) (sieveNorm_nonneg _ _) hA hB
  change (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 ≤ _ at h
  convert h using 1 <;> ring

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson
open Eisenstein

/-- The quadratic character vanishes outside its squarefree odd conductor family. -/
def canonicalQuadraticRowOfIdeal (I : Ideal O) (z : O) : ℂ :=
  if h : quadraticIdealAdmissible I then canonicalQuadraticRow ⟨I, h⟩ z else 0

lemma canonicalQuadraticRowOfIdeal_norm_le_one (I : Ideal O) (z : O) :
    ‖canonicalQuadraticRowOfIdeal I z‖ ≤ 1 := by
  unfold canonicalQuadraticRowOfIdeal
  split_ifs
  · exact canonicalQuadraticRow_norm_le_one _ _
  · simp

namespace CanonicalQuadraticSieve
open IdealDivisorBilinearBlocks DivisorBlockCauchy

/-- The original characters, before their common divisor is removed. -/
def originalBlock {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  blockValue (fun j => (left j).val) (fun k => (right k).val)
    (fun _ i j => canonicalQuadraticRow (left j) (primaryIdealGenerator (rows i).val))
    (fun _ i k => canonicalQuadraticRow (right k) (primaryIdealGenerator (rows i).val)) a b D E

lemma original_entry_factor {m n : Type*} (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal)
    (a : n → ℂ) (D : Ideal O) (i : m) (j : n) :
    canonicalQuadraticRow (cols j) (primaryIdealGenerator (rows i).val) *
        (if D ∣ (cols j).val then a j else 0) =
      canonicalQuadraticRowOfIdeal D (primaryIdealGenerator (rows i).val) *
        (quotientMatrix D rows cols i j * (if D ∣ (cols j).val then a j else 0)) := by
  by_cases h : D ∣ (cols j).val
  · simp only [if_pos h, quotientMatrix, dif_pos h, canonicalQuadraticRowOfIdeal,
      dif_pos (quadraticIdealAdmissible_of_dvd (cols j).property h)]
    rw [canonicalQuadraticRow_divisor_factor (cols j) D h]
    exact mul_assoc _ _ _
  · simp only [if_neg h, mul_zero]

lemma originalBlock_le_quotientBlock {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) :
    originalBlock rows left right a b D E ≤ quotientBlock rows left right a b D E := by
  apply Finset.sum_le_sum
  intro i _
  have he : (∑ j, ∑ k, if (left j).val ⊔ (right k).val = ⊤ then
      star (canonicalQuadraticRow (left j) (primaryIdealGenerator (rows i).val) *
        (if D ∣ (left j).val then a j else 0)) *
      (canonicalQuadraticRow (right k) (primaryIdealGenerator (rows i).val) *
        (if E ∣ (right k).val then b k else 0)) else 0) =
      (star (canonicalQuadraticRowOfIdeal D (primaryIdealGenerator (rows i).val)) *
        canonicalQuadraticRowOfIdeal E (primaryIdealGenerator (rows i).val)) *
      (∑ j, ∑ k, if (left j).val ⊔ (right k).val = ⊤ then
        star (quotientMatrix D rows left i j * (if D ∣ (left j).val then a j else 0)) *
          (quotientMatrix E rows right i k * (if E ∣ (right k).val then b k else 0)) else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : (left j).val ⊔ (right k).val = ⊤
    · rw [if_pos h, if_pos h, original_entry_factor rows left a D i j,
        original_entry_factor rows right b E i k, star_mul]
      ring
    · simp only [if_neg h, mul_zero]
  change ‖_‖ ≤ ‖_‖
  rw [he, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_mul, norm_star]
  exact (mul_le_mul (canonicalQuadraticRowOfIdeal_norm_le_one D _)
    (canonicalQuadraticRowOfIdeal_norm_le_one E _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- Divisor removal retains the original coprime bilinear block bound. -/
theorem original_divisor_block_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) (hN : 0 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ))
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N) (a : n → ℂ) (b : p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, originalBlock rows left right a b D E) ^ 2 ≤
      (S.card : ℝ) * T.card * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
        (divisorConstant ε hε * N ^ ε) ^ 4 * (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) := by
  apply le_trans _ (quotient_divisor_block_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright a b)
  apply pow_le_pow_left₀
  · exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => blockValue_nonneg ..))
  · exact Finset.sum_le_sum (fun D _ => Finset.sum_le_sum
      (fun E _ => originalBlock_le_quotientBlock rows left right a b D E))

end CanonicalQuadraticSieve
end SchwartzPlanePoisson

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein DivisorBlockCauchy IdealCoprimeBilinearSieve

/-- A fixed common ideal reduces the column norm by its exact norm. -/
theorem highKernel_commonFactorBlock_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ε : ℝ) (hε : 0 < ε) (D : QuadraticIdeal)
    (rows : m → QuadraticSupportedIdeal) (cols : n → QuadraticIdeal)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N)
    (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hcols : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N)
    (hK : ∀ i, K < (Ideal.absNorm (quadraticSquarefreePart (rows i).val) : ℝ)) (a : n → ℂ) :
    ‖commonFactorBlock D.val (fun i => primaryIdealGenerator (rows i).val) cols a‖ ≤
      highKernelNorm M (N / Ideal.absNorm D.val) K * (divisorConstant ε hε * N ^ ε) *
        ∑ j, ‖if D.val ∣ (cols j).val then a j else 0‖ ^ 2 := by
  classical
  have hD0 := primaryIdealGenerator_ne_zero_ideal D.val D.property.1
  have hDN : (1 : ℝ) ≤ Ideal.absNorm D.val := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hdiv : N / Ideal.absNorm D.val ≤ N := by
    exact div_le_self hN0 hDN
  let S : Finset n := Finset.univ.filter (fun j => D.val ∣ (cols j).val)
  have hS (j : S) : D.val ∣ (cols j.val).val := (Finset.mem_filter.mp j.property).2
  let q : S → QuadraticIdeal := fun j => ⟨quadraticIdealQuotient D.val (cols j.val).val,
    quadraticIdealQuotient_admissible (cols j.val).property (hS j)⟩
  have hq : Function.Injective q := by
    intro i j he
    apply Subtype.ext
    apply hc
    apply Subtype.ext
    apply quadraticIdealQuotient_injective D.val (hS i) (hS j)
    exact congrArg (fun I : QuadraticIdeal => I.val) he
  have hqn (j : S) : (Ideal.absNorm (q j).val : ℝ) ≤ N / Ideal.absNorm D.val := by
    change (Ideal.absNorm (quadraticIdealQuotient D.val (cols j.val).val) : ℝ) ≤ _
    rw [quadraticIdealQuotient_norm hD0 (hS j)]
    exact div_le_div_of_nonneg_right (hcols j.val) (Nat.cast_nonneg _)
  let A : Matrix m S ℂ := fun i j => canonicalQuadraticRow (q j) (primaryIdealGenerator (rows i).val)
  let v (i : m) : ℂ := canonicalQuadraticRow D (primaryIdealGenerator (rows i).val)
  let T (i : m) (j k : n) : ℂ := if (cols j).val ⊔ (cols k).val = D.val then
    star (canonicalQuadraticRow (cols j) (primaryIdealGenerator (rows i).val) * a j) *
      (canonicalQuadraticRow (cols k) (primaryIdealGenerator (rows i).val) * a k) else 0
  have hzero_left (i : m) (j k : n) (hj : j ∉ S) : T i j k = 0 := by
    apply if_neg
    intro he
    apply hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Ideal.dvd_iff_le.mpr (he ▸ (le_sup_left : (cols j).val ≤ (cols j).val ⊔ (cols k).val))⟩
  have hzero_right (i : m) (j k : n) (hk : k ∉ S) : T i j k = 0 := by
    apply if_neg
    intro he
    apply hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Ideal.dvd_iff_le.mpr (he ▸ (le_sup_right : (cols k).val ≤ (cols j).val ⊔ (cols k).val))⟩
  have heq (i : m) : (∑ j, ∑ k, T i j k) =
      star (v i) * v i *
        (∑ j : S, ∑ k : S, if (q j).val ⊔ (q k).val = ⊤ then
          star (A i j * a j.val) * (A i k * a k.val) else 0) := by
    calc
      _ = ∑ j ∈ S, ∑ k ∈ S, T i j k := by
        have hj : (∑ j, ∑ k, T i j k) = ∑ j ∈ S, ∑ k, T i j k := by
          symm
          apply Finset.sum_subset (Finset.subset_univ S)
          intro j _ hj
          exact Finset.sum_eq_zero (fun k _ => hzero_left i j k hj)
        rw [hj]
        apply Finset.sum_congr rfl
        intro j _
        symm
        exact Finset.sum_subset (Finset.subset_univ S) (fun k _ hk => hzero_right i j k hk)
      _ = ∑ j : S, ∑ k : S, T i j.val k.val := by
        rw [Finset.sum_coe_sort (s := S) (f := fun j => ∑ k : S, T i j k.val)]
        exact Finset.sum_congr rfl (fun j _ =>
          (Finset.sum_coe_sort (s := S) (f := fun k => T i j k)).symm)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        have hiff := quadraticIdealQuotient_coprime_iff D.val (cols j.val).val (cols k.val).val
          hD0 (hS j) (hS k)
        change (if (cols j.val).val ⊔ (cols k.val).val = D.val then _ else 0) = _
        by_cases h : (q j).val ⊔ (q k).val = ⊤
        · rw [if_pos (hiff.mp h), if_pos h]
          rw [canonicalQuadraticRow_divisor_factor (cols j.val) D.val (hS j),
            canonicalQuadraticRow_divisor_factor (cols k.val) D.val (hS k), star_mul, star_mul]
          change (star (a j.val) * (star (A i j) * star (v i))) * (v i * A i k * a k.val) = _
          simp only [star_mul]
          ring
        · rw [if_neg (fun hc => h (hiff.mpr hc)), if_neg h, mul_zero]
  have hn : ‖commonFactorBlock D.val (fun i => primaryIdealGenerator (rows i).val) cols a‖ ≤
      ∑ i, ‖∑ j : S, ∑ k : S, if (q j).val ⊔ (q k).val = ⊤ then
        star (A i j * a j.val) * (A i k * a k.val) else 0‖ := by
    change ‖∑ i, ∑ j, ∑ k, T i j k‖ ≤ _
    simp_rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul, norm_mul, norm_star]
    apply mul_le_of_le_one_left (norm_nonneg _)
    exact (mul_le_mul (canonicalQuadraticRow_norm_le_one D _)
      (canonicalQuadraticRow_norm_le_one D _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hb := ideal_coprime_bilinear_operator_bound ε hε
    (fun j : S => (q j).val) (fun j : S => (q j).val)
    (fun j => primaryIdealGenerator_ne_zero_ideal _ (q j).property.1)
    (fun j => primaryIdealGenerator_ne_zero_ideal _ (q j).property.1)
    N N (fun j => (hqn j).trans hdiv) (fun j => (hqn j).trans hdiv)
    A A (fun j : S => a j.val) (fun j : S => a j.val)
  have hL : 0 ≤ divisorConstant ε hε * N ^ ε :=
    mul_nonneg (divisorConstant_pos ε hε).le (Real.rpow_nonneg hN0 _)
  have hop := highKernel_family_squared_norm_le rows q hr hq M (N / Ideal.absNorm D.val) K hrows hqn hK
  have hs : (∑ j : S, ‖a j.val‖ ^ 2) = ∑ j, ‖if D.val ∣ (cols j).val then a j else 0‖ ^ 2 := by
    rw [Finset.sum_coe_sort (s := S) (f := fun j : n => ‖a j‖ ^ 2)]
    simp only [S, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  have hb' := (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (mul_nonneg (mul_nonneg (sq_nonneg _) hL) (by positivity))).mp
      (show (∑ i, ‖∑ j : S, ∑ k : S, if (q j).val ⊔ (q k).val = ⊤ then
        star (A i j * a j.val) * (A i k * a k.val) else 0‖) ^ 2 ≤
        (‖FiniteSieveOperator.operator A‖ ^ 2 * (divisorConstant ε hε * N ^ ε) * ∑ j : S, ‖a j.val‖ ^ 2) ^ 2 by
          simpa only [pow_two] using hb)
  apply hn.trans (hb'.trans _)
  rw [← hs]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hop hL) (by positivity)

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein DivisorBlockCauchy

/-- Large common conductors are absorbed into a shorter high-kernel column range. -/
theorem highKernel_large_commonFactorBlocks {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ε : ℝ) (hε : 0 < ε)
    (rows : m → QuadraticSupportedIdeal) (cols : n → QuadraticIdeal)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (S : Finset (Ideal O)) (hS : S ⊆ commonFactorPool cols) (G : ℝ) (hG : 0 < G)
    (hSG : ∀ D ∈ S, G ≤ (Ideal.absNorm D : ℝ))
    (M N K : ℝ) (hN : 1 ≤ N)
    (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hcols : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N)
    (hK : ∀ i, K < (Ideal.absNorm (quadraticSquarefreePart (rows i).val) : ℝ)) (a : n → ℂ) :
    (∑ D ∈ S, ‖commonFactorBlock D (fun i => primaryIdealGenerator (rows i).val) cols a‖) ≤
      highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have hL : 0 ≤ divisorConstant ε hε * N ^ ε :=
    mul_nonneg (divisorConstant_pos ε hε).le (Real.rpow_nonneg (zero_le_one.trans hN) _)
  have hb (D : Ideal O) (hD : D ∈ S) :
      ‖commonFactorBlock D (fun i => primaryIdealGenerator (rows i).val) cols a‖ ≤
      highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ (cols j).val then a j else 0‖ ^ 2 := by
    have hh := highKernel_commonFactorBlock_bound ε hε
      ⟨D, commonFactorPool_admissible cols D (hS hD)⟩ rows cols hr hc M N K hN hrows hcols hK a
    have hm := highKernelNorm_mono (M := M) (M' := M) (K := K) (K' := K) le_rfl
      (div_le_div_of_nonneg_left (zero_le_one.trans hN) hG (hSG D hD)) le_rfl
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hL) (by positivity))
  calc
    _ ≤ ∑ D ∈ S, highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) *
        ∑ j, ‖if D ∣ (cols j).val then a j else 0‖ ^ 2 := Finset.sum_le_sum hb
    _ = highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) *
        (∑ D ∈ S, ∑ j, ‖if D ∣ (cols j).val then a j else 0‖ ^ 2) := (Finset.mul_sum ..).symm
    _ ≤ highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) *
        ((divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (divisor_mask_energy_small_power ε hε S
        (fun j => (cols j).val) (fun j => primaryIdealGenerator_ne_zero_ideal _ (cols j).property.1)
        N hcols a) (mul_nonneg (highKernelNorm_nonneg _ _ _) hL)
    _ = _ := by ring

/-- Splitting common conductors separates the Poisson terms from a shorter recursive remainder. -/
theorem highKernel_energy_commonFactor_reduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ε : ℝ) (hε : 0 < ε)
    (rows : m → QuadraticSupportedIdeal) (cols : n → QuadraticIdeal)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (G : ℝ) (hG : 0 < G) (M N K : ℝ) (hN : 1 ≤ N)
    (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hcols : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N)
    (hK : ∀ i, K < (Ideal.absNorm (quadraticSquarefreePart (rows i).val) : ℝ)) (a : n → ℂ) :
    (∑ i, ‖∑ j, canonicalQuadraticRow (cols j) (primaryIdealGenerator (rows i).val) * a j‖ ^ 2) ≤
      (∑ D ∈ (commonFactorPool cols).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
        ‖commonFactorBlock D (fun i => primaryIdealGenerator (rows i).val) cols a‖) +
      highKernelNorm M (N / G) K * (divisorConstant ε hε * N ^ ε) ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  have he := energy_le_commonFactorBlocks (fun i => primaryIdealGenerator (rows i).val) cols a
  rw [← Finset.sum_filter_add_sum_filter_not (commonFactorPool cols)
    (fun D => (Ideal.absNorm D : ℝ) ≤ G)] at he
  exact he.trans (add_le_add le_rfl (highKernel_large_commonFactorBlocks ε hε rows cols hr hc _
    (Finset.filter_subset _ _) G hG (fun D hD => (lt_of_not_ge (Finset.mem_filter.mp hD).2).le)
    M N K hN hrows hcols hK a))

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid DivisorBlockCauchy IdealCoprimeBilinearSieve

/-- The surviving principal boundary gains the inverse square root of its cutoff. -/
theorem quadratic_boundary_operator_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK : 0 < K)
    (G : Ideal O) (hG : G ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, cols j ≠ 0) (N : ℝ) (hN : 0 ≤ N)
    (hcols : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (A : Matrix m n ℂ) (a : n → ℂ) (r : Ideal O → Ideal O → n → ℂ)
    (hr : ∀ D E j, ‖r D E j‖ ≤ 1) :
    ‖∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G, (moebius E : ℂ) *
      (∑ i, quadraticBoundaryWeight K (rows i) D E *
        (∑ j, ∑ k, if cols j ⊔ cols k = ⊤ then
          star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * ‖FiniteSieveOperator.operator A‖ ^ 2 *
          (divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) := by
  let B := (1 / Real.sqrt K) * ‖FiniteSieveOperator.operator A‖ ^ 2 *
    (divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2
  have hb (D : Ideal O) (hD : D ∈ idealDivisors G) (E : Ideal O) (hE : E ∈ idealDivisors G) :
      ‖(moebius E : ℂ) * (∑ i, quadraticBoundaryWeight K (rows i) D E *
        (∑ j, ∑ k, if cols j ⊔ cols k = ⊤ then
          star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ ≤ B := by
    have he := weighted_coprime_gram_bound ε hε cols hc N hN hcols A (fun j => a j * r D E j)
      (fun i => quadraticBoundaryWeight K (rows i) D E) (1 / Real.sqrt K) (by positivity)
      (fun i => quadraticBoundaryWeight_norm_le K hK (rows i) D E
        (IdealDivisorBound.divisor_ne_zero hG hD) (IdealDivisorBound.divisor_ne_zero hG hE))
    have hm : (∑ j, ‖a j * r D E j‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hr D E j)
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (moebius_norm_le_one E)).trans
    apply he.trans
    dsimp only [B]
    rw [← mul_assoc, ← mul_assoc]
    apply mul_le_mul_of_nonneg_left hm
    have hd := (divisorConstant_pos ε hε).le
    have hn := Real.rpow_nonneg hN ε
    positivity
  calc
    _ ≤ ∑ D ∈ idealDivisors G, ‖∑ E ∈ idealDivisors G, (moebius E : ℂ) *
        (∑ i, quadraticBoundaryWeight K (rows i) D E *
          (∑ j, ∑ k, if cols j ⊔ cols k = ⊤ then
            star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G, B := by
      apply Finset.sum_le_sum
      intro D hD
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun E hE => hb D hD E hE))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, B]; ring

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid

lemma quadraticPair_boundary_term (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J)
    (H D E : Ideal O) (hH : quadraticSupported H) (K : ℝ) (a b : ℂ) :
    (star a * b) * ((moebius E : ℂ) * normalizedQuadraticPair I J (H * D * E) *
      (quadraticCutoffDifference K H D : ℂ)) =
      (moebius E : ℂ) * quadraticBoundaryWeight K H D E *
        (star (canonicalQuadraticRow I (primaryIdealGenerator H) *
          (a * canonicalQuadraticRow I (cubicIdealGenerator D * cubicIdealGenerator E))) *
          (canonicalQuadraticRow J (primaryIdealGenerator H) *
            (b * canonicalQuadraticRow J (cubicIdealGenerator D * cubicIdealGenerator E)))) := by
  have hspan : Ideal.span {cubicIdealGenerator D * cubicIdealGenerator E} = D * E := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_cubicIdealGenerator, span_cubicIdealGenerator]
  have hde := canonicalQuadraticPairIdeal_span I J hray (cubicIdealGenerator D * cubicIdealGenerator E)
  rw [hspan] at hde
  have hp : canonicalQuadraticPairIdeal I J (H * D * E) =
      (canonicalQuadraticRow I (primaryIdealGenerator H) * canonicalQuadraticRow J (primaryIdealGenerator H)) *
      (canonicalQuadraticRow I (cubicIdealGenerator D * cubicIdealGenerator E) *
        canonicalQuadraticRow J (cubicIdealGenerator D * cubicIdealGenerator E)) := by
    rw [mul_assoc, canonicalQuadraticPairIdeal_mul I J hray,
      canonicalQuadraticPairIdeal_primary I J hray H hH.1, hde]
  rw [normalizedQuadraticPair, hp]
  simp only [quadraticBoundaryWeight, div_eq_mul_inv, star_mul, canonicalQuadraticRow_star]
  ring

namespace CanonicalQuadraticSieve

/-- The principal source/dual discrepancy, retaining the coprime column pairs. -/
def principalDifference {n : Type*} [Fintype n] (cols : n → QuadraticIdeal)
    (a : n → ℂ) (D : Ideal O) (K : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j).val (cols k).val then
    star (a j) * a k *
      (quadraticPairPartial (cols j) (cols k) K * quadraticPairDivisors (cols j) (cols k) (quadraticMaskIdeal D) -
       quadraticPairCoprimePartial (cols j) (cols k) (quadraticMaskIdeal D) K *
         quadraticPairDensity (cols j) (cols k) (quadraticMaskIdeal D)) else 0

/-- Cancellation leaves a boundary controlled by the smaller native quadratic sieve norm. -/
theorem principalDifference_bound {n : Type*} [Fintype n] [DecidableEq n]
    (cols : n → QuadraticIdeal) (hinj : Function.Injective cols)
    (N : ℝ) (hN : 0 ≤ N) (hcols : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N)
    (hray : ∀ j k, quadraticColumnRay (cols j) = quadraticColumnRay (cols k))
    (a : n → ℂ) (D : Ideal O) (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε) :
    ‖principalDifference cols a D K‖ ≤
      ((idealDivisors (quadraticMaskIdeal D)).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * sieveNorm K N * (DivisorBlockCauchy.divisorConstant ε hε * N ^ ε) *
          ∑ j, ‖a j‖ ^ 2) := by
  classical
  let rows : (coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K) → QuadraticIdeal := fun H => ⟨H.val, coprimeSquarefreeIdealBall_admissible D K H⟩
  let A : (coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K) → n → ℂ := fun H j => canonicalQuadraticRow (cols j) (primaryIdealGenerator H.val)
  let r (E F : Ideal O) (j : n) := canonicalQuadraticRow (cols j) (cubicIdealGenerator E * cubicIdealGenerator F)
  have hpoint (j k : n) :
      (if IsCoprime (cols j).val (cols k).val then star (a j) * a k *
        (quadraticPairPartial (cols j) (cols k) K * quadraticPairDivisors (cols j) (cols k) (quadraticMaskIdeal D) -
         quadraticPairCoprimePartial (cols j) (cols k) (quadraticMaskIdeal D) K * quadraticPairDensity (cols j) (cols k) (quadraticMaskIdeal D)) else 0) =
        ∑ E ∈ idealDivisors (quadraticMaskIdeal D), ∑ F ∈ idealDivisors (quadraticMaskIdeal D), ∑ H : (coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K),
          (moebius F : ℂ) * quadraticBoundaryWeight K H.val E F *
            (if IsCoprime (cols j).val (cols k).val then
              star (A H j * (a j * r E F j)) * (A H k * (a k * r E F k)) else 0) := by
    dsimp only [A, r]
    by_cases hc : IsCoprime (cols j).val (cols k).val
    · rw [if_pos hc, quadraticPair_main_difference (cols j) (cols k) (hray j k)
        (quadraticMaskIdeal D) (quadraticMaskIdeal_squarefree D) K]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro F hF
      apply Finset.sum_congr rfl
      intro H _
      rw [if_pos hc]
      exact quadraticPair_boundary_term (cols j) (cols k) (hray j k) H.val E F
        ⟨(rows H).property.1, (rows H).property.2.2⟩ K (a j) (a k)
    · simp only [hc, ite_false, mul_zero, Finset.sum_const_zero]
  have heq : principalDifference cols a D K =
      ∑ E ∈ idealDivisors (quadraticMaskIdeal D), ∑ F ∈ idealDivisors (quadraticMaskIdeal D), (moebius F : ℂ) *
        (∑ H : (coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K), quadraticBoundaryWeight K H.val E F *
          (∑ j, ∑ k, if (cols j).val ⊔ (cols k).val = ⊤ then
            star (A H j * (a j * r E F j)) * (A H k * (a k * r E F k)) else 0)) := by
    unfold principalDifference
    simp_rw [hpoint]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset n)) (t := idealDivisors (quadraticMaskIdeal D)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset (coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K)))]
    simp only [Finset.mul_sum, mul_assoc, Ideal.isCoprime_iff_sup_eq]
  rw [heq]
  have hb := quadratic_boundary_operator_bound ε hε K hK (quadraticMaskIdeal D) (quadraticMaskIdeal_squarefree D).ne_zero
    (fun H : (coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K) => H.val) (fun j => (cols j).val)
    (fun j => primaryIdealGenerator_ne_zero_ideal (cols j).val (cols j).property.1)
    N hN hcols A a r (fun E F j => canonicalQuadraticRow_norm_le_one (cols j) _)
  have hri : Function.Injective rows := fun H J h => Subtype.ext (congrArg (fun I : QuadraticIdeal => I.val) h)
  have hrows (H : (coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K)) : (Ideal.absNorm (rows H).val : ℝ) ≤ K :=
    (mem_squarefreeIdealBall.mp (Finset.mem_filter.mp H.property).1).2
  have hA : ‖FiniteSieveOperator.operator A‖ ^ 2 ≤ sieveNorm K N :=
    family_squared_norm_le rows cols hri hinj K N hrows hcols
  apply hb.trans
  have hd := (DivisorBlockCauchy.divisorConstant_pos ε hε).le
  have hn := Real.rpow_nonneg hN ε
  gcongr

end CanonicalQuadraticSieve
end SchwartzPlanePoisson

open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

/-- Prime valuations split every nonzero ideal into its squarefree and square factors. -/
def nonzeroIdealQuadraticPartsEquiv :
    NonzeroIdeal ≃ {B : Ideal O // Squarefree B} × NonzeroIdeal where
  toFun H := (⟨quadraticSquarefreePart H.val, quadraticSquarefreePart_squarefree H.val⟩,
    ⟨quadraticSquarePart H.val, quadraticSquarePart_ne_zero H.val⟩)
  invFun p := ⟨p.1.val * p.2.val ^ 2, mul_ne_zero p.1.property.ne_zero (pow_ne_zero _ p.2.property)⟩
  left_inv H := Subtype.ext (quadraticParts_mul_square H.val H.property)
  right_inv p := by
    have h := quadraticParts_of_squarefree p.1.val p.2.val p.1.property p.2.property
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

lemma canonicalQuadraticPairIdeal_square (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (A : Ideal O) :
    canonicalQuadraticPairIdeal I J (A ^ 2) =
      quadraticIdealMask I (cubicIdealGenerator A) * quadraticIdealMask J (cubicIdealGenerator A) := by
  have hs (L : QuadraticIdeal) : canonicalQuadraticRow L (cubicIdealGenerator A) ^ 2 =
      quadraticIdealMask L (cubicIdealGenerator A) := by
    simpa only [pow_two, canonicalQuadraticRow_mul] using
      canonicalQuadraticRow_square L (cubicIdealGenerator A)
  rw [pow_two, canonicalQuadraticPairIdeal_mul I J hray, ← pow_two,
    canonicalQuadraticPairIdeal, mul_pow, hs, hs]

lemma canonicalQuadraticPairIdeal_fourier_summable (I J : QuadraticIdeal)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    Summable (fun H : NonzeroIdeal => canonicalQuadraticPairIdeal I J H.val *
      paperRadialFourier W (t * (Ideal.absNorm H.val : ℝ))) := by
  have hinj : Function.Injective (fun H : NonzeroIdeal => cubicIdealGenerator H.val) :=
    cubicIdealGenerator_injective.comp Subtype.val_injective
  have hs := (canonicalQuadraticPair_fourier_summable I J W t ht).comp_injective hinj
  simpa only [Function.comp_def, ringComplex_norm_sq_eq_absNorm_span,
    span_cubicIdealGenerator, canonicalQuadraticPairIdeal] using hs

def quadraticDualSquarefreeLow (I J : QuadraticIdeal) (W : ℝ → ℂ) (t K : ℝ) : ℂ :=
  ∑' H : NonzeroIdeal, if (Ideal.absNorm (quadraticSquarefreePart H.val) : ℝ) ≤ K then
    canonicalQuadraticPairIdeal I J H.val * paperRadialFourier W (t * (Ideal.absNorm H.val : ℝ)) else 0

def quadraticDualSquarefreeTail (I J : QuadraticIdeal) (W : ℝ → ℂ) (t K : ℝ) : ℂ :=
  ∑' H : NonzeroIdeal, if K < (Ideal.absNorm (quadraticSquarefreePart H.val) : ℝ) then
    canonicalQuadraticPairIdeal I J H.val * paperRadialFourier W (t * (Ideal.absNorm H.val : ℝ)) else 0

lemma quadraticDual_low_add_tail (I J : QuadraticIdeal) (W : 𝓢(ℝ, ℂ))
    (t K : ℝ) (ht : 0 < t) :
    (∑' H : NonzeroIdeal, canonicalQuadraticPairIdeal I J H.val *
      paperRadialFourier W (t * (Ideal.absNorm H.val : ℝ))) =
      quadraticDualSquarefreeLow I J W t K + quadraticDualSquarefreeTail I J W t K := by
  let f : NonzeroIdeal → ℂ := fun H => canonicalQuadraticPairIdeal I J H.val *
    paperRadialFourier W (t * (Ideal.absNorm H.val : ℝ))
  have hs : Summable f := canonicalQuadraticPairIdeal_fourier_summable I J W t ht
  have hl : Summable (fun H : NonzeroIdeal =>
      if (Ideal.absNorm (quadraticSquarefreePart H.val) : ℝ) ≤ K then f H else 0) := hs.indicator _
  have hh : Summable (fun H : NonzeroIdeal =>
      if K < (Ideal.absNorm (quadraticSquarefreePart H.val) : ℝ) then f H else 0) := hs.indicator _
  change (∑' H, f H) =
    (∑' H, if (Ideal.absNorm (quadraticSquarefreePart H.val) : ℝ) ≤ K then f H else 0) +
    (∑' H, if K < (Ideal.absNorm (quadraticSquarefreePart H.val) : ℝ) then f H else 0)
  rw [← hl.tsum_add hh]
  apply tsum_congr
  intro H
  by_cases h : (Ideal.absNorm (quadraticSquarefreePart H.val) : ℝ) ≤ K
  · simp only [h, not_lt_of_ge h, ite_true, ite_false, add_zero]
  · simp only [h, lt_of_not_ge h, ite_true, ite_false, zero_add]

/-- The square variable contributes the joint coprimality mask, with no support restriction. -/
def quadraticDualPrincipalIdeal (I J : QuadraticIdeal) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' A : NonzeroIdeal,
    (quadraticIdealMask I (cubicIdealGenerator A.val) * quadraticIdealMask J (cubicIdealGenerator A.val)) *
      W ((Ideal.absNorm A.val : ℝ) / X)

lemma tsum_squarefree_norm_cutoff (K : ℝ) (f : Ideal O → ℂ) :
    (∑' B : {B : Ideal O // Squarefree B}, if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0) =
      ∑ B : squarefreeIdealBall K, f B.val := by
  let e : squarefreeIdealBall K → {B : Ideal O // Squarefree B} :=
    fun B => ⟨B.val, (mem_squarefreeIdealBall.mp B.property).1⟩
  have he : Function.Injective e := by
    intro B C h
    exact Subtype.ext (congrArg (fun D : {B : Ideal O // Squarefree B} => D.val) h)
  let F : {B : Ideal O // Squarefree B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs : Function.support F ⊆ Set.range e := by
    intro B hB
    have hN : (Ideal.absNorm B.val : ℝ) ≤ K := by
      by_contra hn
      exact hB (if_neg hn)
    exact ⟨⟨B.val, mem_squarefreeIdealBall.mpr ⟨B.property, hN⟩⟩, Subtype.ext rfl⟩
  have ht := he.tsum_eq hs
  change (∑' B, F B) = _
  rw [← ht, tsum_fintype]
  exact Finset.sum_congr rfl (fun B _ => if_pos (mem_squarefreeIdealBall.mp B.property).2)

/-- Low dual frequencies are a finite squarefree sum of principal square profiles. -/
theorem quadraticDualSquarefreeLow_principal_finite (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (W : 𝓢(ℝ, ℂ))
    (t K : ℝ) (ht : 0 < t) :
    quadraticDualSquarefreeLow I J W t K =
      ∑ B : squarefreeIdealBall K, canonicalQuadraticPairIdeal I J B.val *
        quadraticDualPrincipalIdeal I J (quadraticTransformedSquareProfile W)
          (Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) := by
  let G : NonzeroIdeal → ℂ := fun H => if (Ideal.absNorm (quadraticSquarefreePart H.val) : ℝ) ≤ K then
    canonicalQuadraticPairIdeal I J H.val * paperRadialFourier W (t * (Ideal.absNorm H.val : ℝ)) else 0
  let F : ({B : Ideal O // Squarefree B} × NonzeroIdeal) → ℂ := fun p =>
    if (Ideal.absNorm p.1.val : ℝ) ≤ K then
      canonicalQuadraticPairIdeal I J p.1.val *
        (quadraticIdealMask I (cubicIdealGenerator p.2.val) * quadraticIdealMask J (cubicIdealGenerator p.2.val)) *
          paperRadialFourier W (t * ((Ideal.absNorm p.1.val : ℝ) * (Ideal.absNorm p.2.val : ℝ) ^ 2)) else 0
  have hg : Summable G := (canonicalQuadraticPairIdeal_fourier_summable I J W t ht).indicator _
  have he (p : {B : Ideal O // Squarefree B} × NonzeroIdeal) :
      G (nonzeroIdealQuadraticPartsEquiv.symm p) = F p := by
    change (if (Ideal.absNorm (quadraticSquarefreePart (p.1.val * p.2.val ^ 2)) : ℝ) ≤ K then
      canonicalQuadraticPairIdeal I J (p.1.val * p.2.val ^ 2) *
        paperRadialFourier W (t * (Ideal.absNorm (p.1.val * p.2.val ^ 2) : ℝ)) else 0) = _
    rw [(quadraticParts_of_squarefree p.1.val p.2.val p.1.property p.2.property).1]
    simp only [F, canonicalQuadraticPairIdeal_mul I J hray,
      canonicalQuadraticPairIdeal_square I J hray, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  have hf : Summable F := (nonzeroIdealQuadraticPartsEquiv.symm.summable_iff.mpr hg).congr he
  calc
    _ = ∑' p, G (nonzeroIdealQuadraticPartsEquiv.symm p) :=
      (nonzeroIdealQuadraticPartsEquiv.symm.tsum_eq G).symm
    _ = ∑' p, F p := tsum_congr he
    _ = ∑' B : {B : Ideal O // Squarefree B}, ∑' A : NonzeroIdeal, F (B, A) := hf.tsum_prod
    _ = ∑' B : {B : Ideal O // Squarefree B}, if (Ideal.absNorm B.val : ℝ) ≤ K then
        canonicalQuadraticPairIdeal I J B.val * quadraticDualPrincipalIdeal I J
          (quadraticTransformedSquareProfile W) (Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) else 0 := by
      apply tsum_congr
      intro B
      by_cases hK : (Ideal.absNorm B.val : ℝ) ≤ K
      · rw [if_pos hK, quadraticDualPrincipalIdeal, ← tsum_mul_left]
        apply tsum_congr
        intro A
        have hB : 0 < (Ideal.absNorm B.val : ℝ) := by
          exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr B.property.ne_zero)
        have htb := mul_pos ht hB
        have harg : ((Ideal.absNorm A.val : ℝ) / Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) ^ 2 =
            t * ((Ideal.absNorm B.val : ℝ) * (Ideal.absNorm A.val : ℝ) ^ 2) := by
          rw [div_pow, Real.sq_sqrt (one_div_pos.mpr htb).le]
          field_simp
        simp only [F, if_pos hK, quadraticTransformedSquareProfile_apply, harg, mul_assoc]
      · simp only [F, if_neg hK, tsum_zero]
    _ = _ := tsum_squarefree_norm_cutoff K (fun B =>
      canonicalQuadraticPairIdeal I J B * quadraticDualPrincipalIdeal I J
        (quadraticTransformedSquareProfile W) (Real.sqrt (1 / (t * (Ideal.absNorm B : ℝ)))))

lemma quadraticPair_prime_mask (I J : QuadraticIdeal) (z : O) :
    primeCoprimeMask cubicIdealGenerator (primeSupport (I.val * J.val)) z =
      quadraticIdealMask I z * quadraticIdealMask J z := by
  have hIJ := mul_ne_zero (primaryIdealGenerator_ne_zero_ideal I.val I.property.1)
    (primaryIdealGenerator_ne_zero_ideal J.val J.property.1)
  have hc : IsCoprime (Ideal.span {z}) (I.val * J.val) ↔
      IsCoprime (Ideal.span {z}) I.val ∧ IsCoprime (Ideal.span {z}) J.val := by
    constructor
    · intro h
      exact ⟨h.mono (dvd_refl _) (dvd_mul_right I.val J.val),
        h.mono (dvd_refl _) (dvd_mul_left J.val I.val)⟩
    · rintro ⟨hI, hJ⟩
      exact hI.mul_right hJ
  rw [primeCoprimeMask_indicator]
  simp only [ideal_generator_dvd_iff,
    ← ideal_coprime_support_iff (Ideal.span {z}) (I.val * J.val) hIJ,
    quadraticIdealMask_indicator, hc]
  split_ifs <;> simp_all

/-- The unrestricted square-variable sum is exactly the prime-masked lattice sum. -/
theorem quadraticDualPrincipalIdeal_lattice (I J : QuadraticIdeal)
    (hnt : I.val ≠ 1 ∨ J.val ≠ 1) (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' z : O, primeCoprimeMask cubicIdealGenerator (primeSupport (I.val * J.val)) z *
      W (‖ringComplex z‖ ^ 2 / X)) =
      (Nat.card Oˣ : ℂ) * quadraticDualPrincipalIdeal I J W X := by
  let f : O → ℂ := fun z => primeCoprimeMask cubicIdealGenerator (primeSupport (I.val * J.val)) z *
    W (‖ringComplex z‖ ^ 2 / X)
  have hs : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_)
      (actual_eisenstein_summable_norm (scaledRadialTest W X hX))
    rw [scaledRadialTest_apply]
    change ‖primeCoprimeMask cubicIdealGenerator (primeSupport (I.val * J.val)) z *
      W (‖ringComplex z‖ ^ 2 / X)‖ ≤ ‖W (‖ringComplex z‖ ^ 2 / X)‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (primeCoprimeMask_norm_le_one _ _ _)
  have h0 : f 0 = 0 := by
    dsimp only [f]
    rw [quadraticPair_prime_mask, ← canonicalQuadraticRow_square, ← canonicalQuadraticRow_square,
      zero_pow (by decide : 2 ≠ 0), canonicalQuadraticPair_zero I J hnt, zero_mul]
  have hu (u : Oˣ) (z : O) : f ((u : O) * z) = f z := by
    dsimp only [f]
    rw [primeCoprimeMask_unit_mul, map_mul, norm_mul, norm_ringComplex_unit, one_mul]
  have he := tsum_unit_invariant_ideals f hs h0 hu
  simpa only [f, quadraticPair_prime_mask, ringComplex_norm_sq_eq_absNorm_span,
    span_cubicIdealGenerator, quadraticDualPrincipalIdeal] using he

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

lemma quadraticSquarefreePart_norm_le (H : Ideal O) (hH : H ≠ 0) :
    (Ideal.absNorm (quadraticSquarefreePart H) : ℝ) ≤ Ideal.absNorm H := by
  have hB : 1 ≤ Ideal.absNorm (quadraticSquarePart H) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (quadraticSquarePart_ne_zero H))
  have hn := congrArg Ideal.absNorm (quadraticParts_mul_square H hH)
  simp only [map_mul, map_pow] at hn
  exact_mod_cast (show Ideal.absNorm (quadraticSquarefreePart H) ≤ Ideal.absNorm H by
    rw [← hn]
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (Ideal.absNorm (quadraticSquarefreePart H)) (one_le_pow₀ hB))

/-- Schwartz decay controls the discarded dual squarefree part with arbitrary polynomial gain. -/
theorem quadraticDualSquarefreeTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (I J : QuadraticIdeal) (W : 𝓢(ℝ, ℂ)) (t K : ℝ), 0 < t → 0 ≤ K →
        ‖quadraticDualSquarefreeTail I J W t K‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 t) ^ 2 * (1 + t * K) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro I J W t K ht hK
  let S := {H : NonzeroIdeal | K < (Ideal.absNorm (quadraticSquarefreePart H.val) : ℝ)}
  let f : NonzeroIdeal → ℂ := fun H => canonicalQuadraticPairIdeal I J H.val *
    paperRadialFourier W (t * (Ideal.absNorm H.val : ℝ))
  have he : quadraticDualSquarefreeTail I J W t K = ∑' H : S, f H.val := by
    change (∑' H : NonzeroIdeal, S.indicator f H) = _
    exact (tsum_subtype S f).symm
  have hs : Summable (fun H : NonzeroIdeal => ‖paperRadialFourier W (t * (Ideal.absNorm H.val : ℝ))‖) := by
    have hi : Function.Injective (fun H : NonzeroIdeal => cubicIdealGenerator H.val) :=
      cubicIdealGenerator_injective.comp Subtype.val_injective
    have h := (paperRadialFourier_lattice_summable_norm W t ht).comp_injective hi
    simpa only [Function.comp_def, ringComplex_norm_sq_eq_absNorm_span, span_cubicIdealGenerator] using h
  let e : S → {z : O // t * K ≤ t * ‖ringComplex z‖ ^ 2} := fun H =>
    ⟨cubicIdealGenerator H.val.val, by
      rw [ringComplex_norm_sq_eq_absNorm_span, span_cubicIdealGenerator]
      exact mul_le_mul_of_nonneg_left
        (H.property.le.trans (quadraticSquarefreePart_norm_le H.val.val H.val.property)) ht.le⟩
  have hi : Function.Injective e := by
    intro H Q h
    apply Subtype.ext
    apply Subtype.ext
    apply cubicIdealGenerator_injective
    exact congrArg (fun z : {z : O // t * K ≤ t * ‖ringComplex z‖ ^ 2} => z.val) h
  have hsub : (∑' H : S, ‖paperRadialFourier W (t * (Ideal.absNorm H.val.val : ℝ))‖) ≤
      ∑' z : {z : O // t * K ≤ t * ‖ringComplex z‖ ^ 2},
        ‖paperRadialFourier W (t * ‖ringComplex z.val‖ ^ 2)‖ := by
    apply (hs.subtype S).tsum_le_tsum_of_inj e hi (fun _ _ => norm_nonneg _) (fun H => ?_)
      ((paperRadialFourier_lattice_summable_norm W t ht).subtype _)
    simp only [e, Function.comp_def, ringComplex_norm_sq_eq_absNorm_span,
      span_cubicIdealGenerator, le_refl]
  rw [he]
  apply (norm_tsum_le_tsum_norm
    ((canonicalQuadraticPairIdeal_fourier_summable I J W t ht).norm.subtype S)).trans
  apply le_trans _ (hsub.trans (hb W t (t * K) ht (mul_nonneg ht.le hK)))
  apply ((canonicalQuadraticPairIdeal_fourier_summable I J W t ht).norm.subtype S).tsum_le_tsum
    (fun H => ?_) (hs.subtype S)
  change ‖canonicalQuadraticPairIdeal I J H.val.val *
    paperRadialFourier W (t * (Ideal.absNorm H.val.val : ℝ))‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (canonicalQuadraticPairIdeal_norm_le_one I J H.val.val)

end SchwartzPlanePoisson

namespace LocalLogFourier
open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff

/-- Euler derivatives are ordinary derivatives along multiplicative flow. -/
noncomputable def eulerDeriv (F : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  iteratedDeriv j (fun t : ℝ => F (x * Real.exp t)) 0

theorem iteratedDeriv_log_eq_euler (F : ℝ → ℂ) (R s : ℝ) (j : ℕ) :
    iteratedDeriv j (fun z : ℝ => F (R * Real.exp z)) s =
      eulerDeriv F j (R * Real.exp s) := by
  let G : ℝ → ℂ := fun z => F (R * Real.exp z)
  have hshift : (fun t : ℝ => F ((R * Real.exp s) * Real.exp t)) =
      (fun t : ℝ => G (s + t)) := by
    funext t
    simp only [G, Real.exp_add, mul_assoc]
  unfold eulerDeriv
  rw [hshift]
  simpa [G] using (congrArg (fun h : ℝ → ℂ => h 0)
    (iteratedDeriv_comp_const_add j G s)).symm


end LocalLogFourier

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff

/-- Half the Euler operator governs a Schwartz profile composed with square root. -/
def halfEulerCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => ((x / 2 : ℝ) : ℂ))).comp
    (SchwartzMap.derivCLM ℂ ℂ)

@[simp] theorem halfEulerCLM_apply (g : 𝓢(ℝ, ℂ)) (s : ℝ) :
    halfEulerCLM g s = (s / 2 : ℝ) • deriv g s := by
  have hg : (fun x : ℝ => ((x / 2 : ℝ) : ℂ)).HasTemperateGrowth := by
    simp only [div_eq_mul_inv]
    fun_prop
  simp only [halfEulerCLM, ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.derivCLM_apply]
  rfl

theorem hasDerivAt_halfFlow (g : 𝓢(ℝ, ℂ)) (a t : ℝ) :
    HasDerivAt (fun y : ℝ => g (a * Real.exp (y / 2)))
      (halfEulerCLM g (a * Real.exp (t / 2))) t := by
  have hf : HasDerivAt (fun y : ℝ => a * Real.exp (y / 2))
      ((a * Real.exp (t / 2)) / 2) t := by
    simpa only [id_eq, div_eq_mul_inv, mul_one, one_mul, mul_assoc] using
      (((hasDerivAt_id t).div_const 2).exp.const_mul a)
  simpa only [halfEulerCLM_apply, Function.comp_def] using
    (g.hasDerivAt (a * Real.exp (t / 2))).scomp t hf

theorem iteratedDeriv_halfFlow (g : 𝓢(ℝ, ℂ)) (a : ℝ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun y : ℝ => g (a * Real.exp (y / 2))) t =
      ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g) (a * Real.exp (t / 2)) := by
  induction j generalizing g with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun y : ℝ => g (a * Real.exp (y / 2))) =
        fun y : ℝ => halfEulerCLM g (a * Real.exp (y / 2)) :=
      funext (fun y => (hasDerivAt_halfFlow g a y).deriv)
    rw [hd, ih (halfEulerCLM g),
      Function.iterate_succ_apply]

 theorem sqrt_exp_half (t : ℝ) : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
  rw [Real.sqrt_eq_iff_eq_sq (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

 theorem eulerDeriv_sqrt_profile (g : 𝓢(ℝ, ℂ)) (j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    LocalLogFourier.eulerDeriv (fun s => g (Real.sqrt s)) j x =
      ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g) (Real.sqrt x) := by
  unfold LocalLogFourier.eulerDeriv
  have hflow : (fun t : ℝ => g (Real.sqrt (x * Real.exp t))) =
      fun t : ℝ => g (Real.sqrt x * Real.exp (t / 2)) := by
    funext t
    rw [Real.sqrt_mul hx, sqrt_exp_half]
  rw [hflow, iteratedDeriv_halfFlow]
  simp

theorem contDiffOn_sqrt_profile (g : 𝓢(ℝ, ℂ)) :
    ContDiffOn ℝ ∞ (fun x : ℝ => g (Real.sqrt x)) (Set.Ioi 0) := by
  intro x hx
  exact ((g.smooth ⊤).contDiffAt.comp x
    (Real.contDiffAt_sqrt (ne_of_gt hx))).contDiffWithinAt

theorem contDiff_sqrt_profile_log (g : 𝓢(ℝ, ℂ)) (x : ℝ) (hx : 0 ≤ x) :
    ContDiff ℝ ∞ (fun t : ℝ => g (Real.sqrt (x * Real.exp t))) := by
  have heq : (fun t : ℝ => g (Real.sqrt (x * Real.exp t))) =
      fun t : ℝ => g (Real.sqrt x * Real.exp (t / 2)) := by
    funext t
    rw [Real.sqrt_mul hx, sqrt_exp_half]
  rw [heq]
  exact (g.smooth ⊤).comp (by fun_prop)

theorem sqrt_profile_rapid_bound (g : 𝓢(ℝ, ℂ)) (A : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ A * ‖g (Real.sqrt x)‖ ≤
      2 ^ A * (SchwartzMap.seminorm ℝ 0 0 g +
        SchwartzMap.seminorm ℝ (2 * A) 0 g) := by
  have hsmall := SchwartzMap.norm_le_seminorm ℝ g (Real.sqrt x)
  have hlarge := SchwartzMap.norm_pow_mul_le_seminorm ℝ g (2 * A) (Real.sqrt x)
  have hsqrt : ‖Real.sqrt x‖ ^ (2 * A) = x ^ A := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
      pow_mul, Real.sq_sqrt hx]
  rw [hsqrt] at hlarge
  have hs0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 g := by positivity
  have hsA : 0 ≤ SchwartzMap.seminorm ℝ (2 * A) 0 g := by positivity
  by_cases hx1 : x ≤ 1
  · have hp : (1 + x) ^ A ≤ (2 : ℝ) ^ A := by gcongr; linarith
    calc
      _ ≤ 2 ^ A * ‖g (Real.sqrt x)‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ 2 ^ A * SchwartzMap.seminorm ℝ 0 0 g := by gcongr
      _ ≤ _ := by gcongr; linarith
  · have hp : (1 + x) ^ A ≤ (2 * x) ^ A := by gcongr; linarith
    calc
      _ ≤ (2 * x) ^ A * ‖g (Real.sqrt x)‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ = 2 ^ A * (x ^ A * ‖g (Real.sqrt x)‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ A * SchwartzMap.seminorm ℝ (2 * A) 0 g := by gcongr
      _ ≤ _ := by gcongr; linarith

theorem eulerDeriv_sqrt_profile_rapid_bound (g : 𝓢(ℝ, ℂ)) (A j : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (fun s => g (Real.sqrt s)) j x‖ ≤
      2 ^ A * (SchwartzMap.seminorm ℝ 0 0
          ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g) +
        SchwartzMap.seminorm ℝ (2 * A) 0
          ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g)) := by
  rw [eulerDeriv_sqrt_profile g j x hx]
  exact sqrt_profile_rapid_bound _ A x hx

def halfEulerIterateCLM : ℕ → 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)
  | 0 => ContinuousLinearMap.id ℝ _
  | j + 1 => (halfEulerCLM.restrictScalars ℝ).comp (halfEulerIterateCLM j)

@[simp] theorem halfEulerIterateCLM_apply (j : ℕ) (g : 𝓢(ℝ, ℂ)) :
    halfEulerIterateCLM j g = (halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [halfEulerIterateCLM, ContinuousLinearMap.comp_apply,
      ih, Function.iterate_succ_apply']
    rfl

def paperFourierRayCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) := quadraticTransformedSquareCLM

@[simp] theorem paperFourierRayCLM_apply (W : 𝓢(ℝ, ℂ)) (s : ℝ) :
    paperFourierRayCLM W s =
      (2 / Real.sqrt 3 : ℝ) • radialFourierCLM W (paperFrequency (s : ℂ)) := by
  change (2 / Real.sqrt 3 : ℝ) •
    radialFourierCLM W (complexPoint 0 (((ringComplex omega).im)⁻¹ * s)) = _
  rw [paperFrequency_coordinates]
  simp only [Complex.ofReal_im, Complex.ofReal_re, zero_div, div_eq_mul_inv, zero_mul, mul_comm]

theorem paperRadialFourier_eq_ray (W : 𝓢(ℝ, ℂ)) :
    paperRadialFourier W = fun x : ℝ => paperFourierRayCLM W (Real.sqrt x) := by
  funext x
  rw [paperRadialFourier_eq_plane, paperFourierRayCLM_apply]

def paperEulerCLM (j : ℕ) : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (halfEulerIterateCLM j).comp paperFourierRayCLM

theorem paperRadialFourier_eulerDeriv (W : 𝓢(ℝ, ℂ)) (j : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    LocalLogFourier.eulerDeriv (paperRadialFourier W) j x =
      paperEulerCLM j W (Real.sqrt x) := by
  rw [paperRadialFourier_eq_ray, eulerDeriv_sqrt_profile _ j x hx]
  simp only [paperEulerCLM, ContinuousLinearMap.comp_apply, halfEulerIterateCLM_apply]

theorem paperRadialFourier_contDiffOn (W : 𝓢(ℝ, ℂ)) :
    ContDiffOn ℝ ∞ (paperRadialFourier W) (Set.Ioi 0) := by
  rw [paperRadialFourier_eq_ray]
  exact contDiffOn_sqrt_profile _

theorem paperRadialFourier_log_contDiff (W : 𝓢(ℝ, ℂ)) (x : ℝ) (hx : 0 ≤ x) :
    ContDiff ℝ ∞ (fun t : ℝ => paperRadialFourier W (x * Real.exp t)) := by
  rw [paperRadialFourier_eq_ray]
  exact contDiff_sqrt_profile_log _ x hx

theorem paperRadialFourier_euler_weighted_bound (W : 𝓢(ℝ, ℂ)) (A j : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤
      2 ^ A * (SchwartzMap.seminorm ℝ 0 0 (paperEulerCLM j W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (paperEulerCLM j W)) := by
  rw [paperRadialFourier_eulerDeriv W j x hx]
  exact sqrt_profile_rapid_bound _ A x hx

theorem schwartzCLM_family_finite_seminorm_control
    (T : ℕ → 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K →
        SchwartzMap.seminorm ℝ 0 0 (T j W) +
          SchwartzMap.seminorm ℝ (2 * A) 0 (T j W) ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let qj : ℕ → Seminorm ℝ 𝓢(ℝ, ℂ) := fun j =>
    (SchwartzMap.seminorm ℝ 0 0 + SchwartzMap.seminorm ℝ (2 * A) 0).comp
      (T j).toLinearMap
  let q : Seminorm ℝ 𝓢(ℝ, ℂ) := ∑ j ∈ Finset.range (K + 1), qj j
  have hqfun : (q : 𝓢(ℝ, ℂ) → ℝ) = fun W => ∑ j ∈ Finset.range (K + 1),
      (SchwartzMap.seminorm ℝ 0 0 (T j W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (T j W)) := by
    funext W
    simp [q, qj]
  have hq : Continuous q := by
    rw [hqfun]
    apply continuous_finsetSum
    intro j hj
    exact (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (0, 0)).comp
        (T j).continuous).add
      (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (2 * A, 0)).comp
        (T j).continuous)
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) q hq
  refine ⟨s, C, ?_, ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W j hj
    apply le_trans ?_ (Seminorm.le_def.mp hbound W)
    rw [hqfun]
    exact Finset.single_le_sum (f := fun i =>
      SchwartzMap.seminorm ℝ 0 0 (T i W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (T i W))
      (by intro i hi; positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem paperRadialFourier_euler_source_weighted_bound (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K → ∀ (x : ℝ), 0 ≤ x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hbound⟩ :=
    schwartzCLM_family_finite_seminorm_control paperEulerCLM A K
  refine ⟨s, 2 ^ A * C, by positivity, ?_⟩
  intro W j hj x hx
  apply (paperRadialFourier_euler_weighted_bound W A j x hx).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound W j hj) (show 0 ≤ (2 : ℝ) ^ A by positivity)

theorem paperRadialFourier_euler_source_decay (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K → ∀ (x : ℝ), 0 ≤ x →
        ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + x) ^ A := by
  obtain ⟨s, C, hC, hbound⟩ := paperRadialFourier_euler_source_weighted_bound A K
  refine ⟨s, C, hC, ?_⟩
  intro W j hj x hx
  apply (le_div_iff₀ (by positivity : 0 < (1 + x) ^ A)).mpr
  simpa only [mul_comm] using hbound W j hj x hx

theorem paperRadialFourier_euler_bound (W : 𝓢(ℝ, ℂ)) (A K : ℕ) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ j ≤ K, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤ CF := by
  obtain ⟨s, C, hC, hbound⟩ := paperRadialFourier_euler_source_weighted_bound A K
  refine ⟨C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, by positivity, ?_⟩
  intro j hj x hx
  exact hbound W j hj x hx.le

theorem compact_paperRadialFourier_regular
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (A K : ℕ) :
    ContDiffOn ℝ ∞ (paperRadialFourier W) (Set.Ioi 0) ∧
      ∃ CF : ℝ, 0 ≤ CF ∧ ∀ j ≤ K, ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤ CF := by
  exact ⟨paperRadialFourier_contDiffOn (hWc.toSchwartzMap hWs),
    paperRadialFourier_euler_bound (hWc.toSchwartzMap hWs) A K⟩


end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff

/-- Bounded logarithmic shifts preserve uniform decay of every radial Fourier derivative. -/
theorem paperRadialFourier_exp_local_derivative_bound (V : 𝓢(ℝ, ℂ))
    (M : ℝ) (hM : 0 ≤ M) (N j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ u : ℝ, |u| ≤ M →
      (1 + R) ^ N * ‖iteratedDeriv j (fun v : ℝ => paperRadialFourier V (R * Real.exp v)) u‖ ≤ C := by
  obtain ⟨s, C₀, hC₀, hb₀⟩ := paperRadialFourier_euler_source_weighted_bound N j
  let C := C₀ * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) V + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hb (x : ℝ) (hx : 0 < x) :
      (1 + x) ^ N * ‖LocalLogFourier.eulerDeriv (paperRadialFourier V) j x‖ ≤ C :=
    (hb₀ V j le_rfl x hx.le).trans (by dsimp [C]; linarith)
  refine ⟨Real.exp M ^ N * C, by positivity, ?_⟩
  intro R hR u hu
  have hMu : 0 ≤ M + u := by linarith [(abs_le.mp hu).1]
  have hE : 1 ≤ Real.exp M := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hM
  have hEu : 1 ≤ Real.exp M * Real.exp u := by
    rw [← Real.exp_add]
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hMu
  have hbase : 1 + R ≤ Real.exp M * (1 + R * Real.exp u) := by
    have hRu := mul_le_mul_of_nonneg_left hEu hR.le
    nlinarith only [hE, hRu]
  have hp : (1 + R) ^ N ≤ Real.exp M ^ N * (1 + R * Real.exp u) ^ N := by
    rw [← mul_pow]
    gcongr
  rw [LocalLogFourier.iteratedDeriv_log_eq_euler]
  calc
    _ ≤ (Real.exp M ^ N * (1 + R * Real.exp u) ^ N) *
        ‖LocalLogFourier.eulerDeriv (paperRadialFourier V) j (R * Real.exp u)‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = Real.exp M ^ N * ((1 + R * Real.exp u) ^ N *
        ‖LocalLogFourier.eulerDeriv (paperRadialFourier V) j (R * Real.exp u)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb _ (mul_pos hR (Real.exp_pos u))) (by positivity)


/-- Localization in a fixed logarithmic interval preserves uniform radial decay of every derivative. -/
theorem localized_paperRadialFourier_derivative_bound
    (V : 𝓢(ℝ, ℂ))
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (M : ℝ) (hM : 0 ≤ M)
    (hχs : Function.support χ ⊆ Set.Icc (-M) M) (N j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ u : ℝ,
      (1 + R) ^ N * ‖iteratedDeriv j (fun v : ℝ => χ v * paperRadialFourier V (R * Real.exp v)) u‖ ≤ C := by
  have hχb (i : ℕ) : ∃ D : ℝ, 0 < D ∧ ∀ u ∈ Set.Icc (-M) M, ‖iteratedDeriv i χ u‖ ≤ D := by
    obtain ⟨D, hD⟩ := isCompact_Icc.bddAbove_image
      (hχ.continuous_iteratedDeriv i (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))).norm.continuousOn
    exact ⟨|D| + 1, by positivity, fun u hu =>
      (hD (Set.mem_image_of_mem _ hu)).trans (by linarith [le_abs_self D])⟩
  choose D hD hDb using hχb
  have hkb (i : ℕ) := paperRadialFourier_exp_local_derivative_bound V M hM N i
  choose C hC hCb using hkb
  let B := ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℂ)‖ * D i * C (j - i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (hD i).le) (hC (j - i)).le)
  refine ⟨B + 1, by positivity, ?_⟩
  intro R hR u
  by_cases hu : u ∈ Set.Icc (-M) M
  · have hprod := iteratedDeriv_mul (n := j) (x := u)
      (hχ.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt
      ((paperRadialFourier_log_contDiff V R hR.le).of_le
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt
    change (1 + R) ^ N * ‖iteratedDeriv j (χ * (fun v : ℝ => paperRadialFourier V (R * Real.exp v))) u‖ ≤ _
    rw [hprod]
    calc
      _ ≤ (1 + R) ^ N * ∑ i ∈ Finset.range (j + 1),
          ‖(j.choose i : ℂ) * iteratedDeriv i χ u *
            iteratedDeriv (j - i) (fun v : ℝ => paperRadialFourier V (R * Real.exp v)) u‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ B := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hDi := (hD i).le
        have hCi := (hC (j - i)).le
        rw [norm_mul, norm_mul]
        calc
          _ = (‖(j.choose i : ℂ)‖ * ‖iteratedDeriv i χ u‖) *
              ((1 + R) ^ N * ‖iteratedDeriv (j - i) (fun v : ℝ => paperRadialFourier V (R * Real.exp v)) u‖) := by ring
          _ ≤ (‖(j.choose i : ℂ)‖ * D i) * C (j - i) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hDb i u hu) (norm_nonneg _))
              (hCb (j - i) R hR u (abs_le.mpr hu)) (by positivity) (by positivity)
      _ ≤ B + 1 := by linarith
  · have hsprod : Function.support (fun v : ℝ => χ v * paperRadialFourier V (R * Real.exp v)) ⊆ Set.Icc (-M) M := by
      intro v hv
      apply hχs
      intro hz
      exact hv (by simp only [hz, zero_mul])
    have hsd := (subset_tsupport (iteratedDeriv j (fun v : ℝ => χ v * paperRadialFourier V (R * Real.exp v)))).trans
      ((tsupport_iteratedDeriv_subset _ j).trans (closure_minimal hsprod isClosed_Icc))
    have hz : iteratedDeriv j (fun v : ℝ => χ v * paperRadialFourier V (R * Real.exp v)) u = 0 := by
      by_contra hn
      exact hu (hsd hn)
    rw [hz, norm_zero, mul_zero]
    positivity

/-- The Fourier transform of a localized radial transform decays uniformly in both parameters. -/
theorem localized_paperRadialFourier_fourier_bound
    (V : 𝓢(ℝ, ℂ))
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (M : ℝ) (hM : 0 ≤ M)
    (hχs : Function.support χ ⊆ Set.Icc (-M) M) (N J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ t : ℝ,
      (1 + R) ^ N * (1 + |t|) ^ J *
        ‖𝓕 (fun u : ℝ => χ u * paperRadialFourier V (R * Real.exp u)) t‖ ≤ C := by
  let F := fun R u : ℝ => χ u * paperRadialFourier V (R * Real.exp u)
  have hFs (R : ℝ) (_ : 0 < R) : Function.support (F R) ⊆ Set.Icc (-M) M := by
    intro u hu
    apply hχs
    intro hz
    exact hu (by simp only [F, hz, zero_mul])
  have hbase (j : ℕ) := compact_weighted_family_fourier_power_bound F (fun R => (1 + R) ^ N)
    (fun R hR => by positivity) (fun R hR => hχ.mul (paperRadialFourier_log_contDiff V R hR.le))
    (Set.Icc (-M) M) isCompact_Icc hFs
    (localized_paperRadialFourier_derivative_bound V χ hχ M hM hχs N) j
  obtain ⟨C₀, hC₀, hb₀⟩ := hbase 0
  obtain ⟨Cj, hCj, hbj⟩ := hbase J
  refine ⟨2 ^ J * (C₀ + Cj), by positivity, ?_⟩
  intro R hR t
  have hzero : (1 + R) ^ N * ‖𝓕 (F R) t‖ ≤ C₀ := by simpa only [pow_zero, one_mul] using hb₀ R hR t
  change (1 + R) ^ N * (1 + |t|) ^ J * ‖𝓕 (F R) t‖ ≤ _
  by_cases ht : |t| ≤ 1
  · have hp : (1 + |t|) ^ J ≤ (2 : ℝ) ^ J := by gcongr; linarith
    calc
      _ ≤ (1 + R) ^ N * 2 ^ J * ‖𝓕 (F R) t‖ := by gcongr
      _ = 2 ^ J * ((1 + R) ^ N * ‖𝓕 (F R) t‖) := by ring
      _ ≤ 2 ^ J * C₀ := mul_le_mul_of_nonneg_left hzero (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hp : (1 + |t|) ^ J ≤ (2 * |t|) ^ J := by gcongr; linarith
    calc
      _ ≤ (1 + R) ^ N * (2 * |t|) ^ J * ‖𝓕 (F R) t‖ := by gcongr
      _ = 2 ^ J * ((1 + R) ^ N * (|t| ^ J * ‖𝓕 (F R) t‖)) := by rw [mul_pow]; ring
      _ ≤ 2 ^ J * Cj := mul_le_mul_of_nonneg_left (hbj R hR t) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- A fixed smooth cutoff turns the radial transform into a uniformly rapidly decaying Fourier coefficient. -/
theorem localized_paperRadialFourier_fourier_envelope
    (V : 𝓢(ℝ, ℂ))
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (M : ℝ) (hM : 0 ≤ M)
    (hχs : Function.support χ ⊆ Set.Icc (-M) M) (N J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∃ B : SchwartzMap ℝ ℂ,
      (∀ u : ℝ, χ u * paperRadialFourier V (R * Real.exp u) = 𝓕⁻ (B : ℝ → ℂ) u) ∧
      Integrable (fun t : ℝ => (1 + |t|) ^ J * ‖B t‖) ∧
      (1 + R) ^ N * (∫ t : ℝ, (1 + |t|) ^ J * ‖B t‖) ≤ C ∧
      ∀ t : ℝ, (1 + R) ^ N * (1 + |t|) ^ J * ‖B t‖ ≤ C := by
  obtain ⟨C₁, hC₁, hb₁⟩ := localized_paperRadialFourier_fourier_bound V χ hχ M hM hχs N J
  obtain ⟨C₂, hC₂, hb₂⟩ := localized_paperRadialFourier_fourier_bound V χ hχ M hM hχs N (J + 2)
  let I : ℝ := ∫ t : ℝ, ((1 + |t|) ^ (2 : ℕ))⁻¹
  have hI : 0 ≤ I := integral_nonneg (fun _ => by positivity)
  refine ⟨C₁ + C₂ * (I + 1), by positivity, ?_⟩
  intro R hR
  have hc : HasCompactSupport (fun u : ℝ => χ u * paperRadialFourier V (R * Real.exp u)) := by
    apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-M) M) isCompact_Icc
    intro u hu
    apply hχs
    intro hz
    exact hu (by simp only [hz, zero_mul])
  let S : SchwartzMap ℝ ℂ := hc.toSchwartzMap (hχ.mul (paperRadialFourier_log_contDiff V R hR.le))
  refine ⟨𝓕 S, ?_⟩
  have he (u : ℝ) : χ u * paperRadialFourier V (R * Real.exp u) = 𝓕⁻ (𝓕 (S : ℝ → ℂ)) u :=
    (S.integrable.fourierInv_fourier_eq (𝓕 S).integrable S.continuous.continuousAt).symm
  have hbound := weighted_fourier_L1_bound (𝓕 (S : ℝ → ℂ)) (𝓕 S).continuous ((1 + R) ^ N) C₂
    (by positivity) hC₂.le J (hb₂ R hR)
  refine ⟨he, hbound.1, ?_, ?_⟩
  · exact hbound.2.trans (by change C₂ * I ≤ _; nlinarith only [hC₁, hC₂, hI])
  · intro t
    exact (hb₁ R hR t).trans (by nlinarith only [hC₂, hI])

/-- Coupled logarithmic factors separate into unitary characters with a uniform integrable Fourier envelope. -/
theorem paperRadialFourier_log_separation_envelope
    {ι : Type*} [Fintype ι] (W : ι → ℝ → ℂ) (slope M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i u, W i u ≠ 0 → |u| ≤ M i)
    (V : 𝓢(ℝ, ℂ)) (N J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∃ B : SchwartzMap ℝ ℂ,
      (∀ y : ι → ℝ, (∏ i, W i (y i)) * paperRadialFourier V (R * Real.exp (∑ i, slope i * y i)) =
        ∫ t : ℝ, (∏ i, W i (y i) * kernelLogPhase t (slope i * y i)) * B t) ∧
      Integrable (fun t : ℝ => (1 + |t|) ^ J * ‖B t‖) ∧
      (1 + R) ^ N * (∫ t : ℝ, (1 + |t|) ^ J * ‖B t‖) ≤ C ∧
      ∀ t : ℝ, (1 + R) ^ N * (1 + |t|) ^ J * ‖B t‖ ≤ C := by
  classical
  let L : ℝ := ∑ i, |slope i| * M i
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hM i))
  let χ₀ : ContDiffBump (0 : ℝ) :=
    ⟨L + 1, L + 2, by linarith, by linarith⟩
  let χ : ℝ → ℂ := fun u => (χ₀ u : ℂ)
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp χ₀.contDiff
  have hχs : Function.support χ ⊆ Set.Icc (-(L + 2)) (L + 2) := by
    intro u hu
    have hu₀ : u ∈ Function.support χ₀ := by
      change χ₀ u ≠ 0
      intro hz
      exact hu (by simp only [χ, hz, Complex.ofReal_zero])
    rw [χ₀.support_eq] at hu₀
    have habs : |u| < L + 2 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hu₀
    exact abs_le.mp habs.le
  have hχone (u : ℝ) (hu : |u| ≤ L) : χ u = 1 := by
    have hu₀ : u ∈ Metric.closedBall (0 : ℝ) χ₀.rIn := by
      change dist u 0 ≤ L + 1
      rw [Real.dist_eq, sub_zero]
      linarith
    simp only [χ, χ₀.one_of_mem_closedBall hu₀, Complex.ofReal_one]
  obtain ⟨C, hC, hb⟩ := localized_paperRadialFourier_fourier_envelope V
    χ hχ (L + 2) (by linarith) hχs N J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨B, hsep, hi, hI, hpt⟩ := hb R hR
  refine ⟨B, ?_, hi, hI, hpt⟩
  intro y
  have hprod (t : ℝ) : (∏ i, W i (y i) * kernelLogPhase t (slope i * y i)) =
      (∏ i, W i (y i)) * kernelLogPhase t (∑ i, slope i * y i) := by
    rw [Finset.prod_mul_distrib, kernelLogPhase_sum]
  simp_rw [hprod, mul_assoc]
  rw [integral_const_mul]
  by_cases hz : (∏ i, W i (y i)) = 0
  · simp only [hz, zero_mul]
  · congr 1
    have hwy (i : ι) : W i (y i) ≠ 0 := by
      exact (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)
    have hys : |∑ i, slope i * y i| ≤ L := by
      calc
        _ ≤ ∑ i, |slope i * y i| := by
          simpa only [Real.norm_eq_abs] using norm_sum_le (s := Finset.univ) (f := fun i => slope i * y i)
        _ ≤ L := Finset.sum_le_sum (fun i _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hW i (y i) (hwy i)) (abs_nonneg _))
    have he := hsep (∑ i, slope i * y i)
    rw [hχone _ hys, one_mul, Real.fourierInv_eq'] at he
    simp only [smul_eq_mul] at he
    convert he using 1
    apply integral_congr_ae
    filter_upwards [] with t
    congr 1
    unfold kernelLogPhase
    congr 1
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring



end SchwartzPlanePoisson

lemma kernelLogPhase_add (t x y : ℝ) :
    kernelLogPhase t (x + y) = kernelLogPhase t x * kernelLogPhase t y := by
  unfold kernelLogPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma kernelLogPhase_continuous_left (x : ℝ) : Continuous (fun t => kernelLogPhase t x) := by
  unfold kernelLogPhase
  fun_prop

namespace QuadraticKernelTransfer
open SchwartzPlanePoisson MeasureTheory
open scoped SchwartzMap

theorem sum_norm_integral_bound {ι : Type*} [Fintype ι]
    (b : ℝ → ℂ) (φ : ι → ℝ → ℂ) (H : ℝ)
    (hint : ∀ i, Integrable (fun t => b t * φ i t))
    (hb : Integrable (fun t => ‖b t‖))
    (hφ : ∀ t, (∑ i, ‖φ i t‖) ≤ H) :
    (∑ i, ‖∫ t, b t * φ i t‖) ≤ H * ∫ t, ‖b t‖ := by
  calc
    _ ≤ ∑ i, ∫ t, ‖b t * φ i t‖ := Finset.sum_le_sum (fun i _ => norm_integral_le_integral_norm _)
    _ = ∫ t, ∑ i, ‖b t * φ i t‖ := (integral_finsetSum _ (fun i _ => (hint i).norm)).symm
    _ ≤ ∫ t, H * ‖b t‖ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => by positivity)) (hb.const_mul H)
      filter_upwards [] with t
      simp only [norm_mul, ← Finset.mul_sum]
      calc
        _ ≤ ‖b t‖ * H := mul_le_mul_of_nonneg_left (hφ t) (norm_nonneg _)
        _ = _ := mul_comm _ _
    _ = _ := integral_const_mul _ _

theorem radial_two_variable_window (W : 𝓢(ℝ, ℂ))
    (L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ x y : ℝ, |x| ≤ L₁ → |y| ≤ L₂ →
        paperRadialFourier W (R * Real.exp (x+y)) =
          ∫ t, kernelLogPhase t x * kernelLogPhase t y * b t) ∧
      (1 + R) ^ A * (∫ t, ‖b t‖) ≤ C := by
  let V₁ : ℝ → ℂ := fun x => if |x| ≤ L₁ then 1 else 0
  let V₂ : ℝ → ℂ := fun x => if |x| ≤ L₂ then 1 else 0
  let V : Bool → ℝ → ℂ := fun j => if j then V₂ else V₁
  let lengthScale : Bool → ℝ := fun j => if j then L₂ else L₁
  have hL : ∀ j, 0 ≤ lengthScale j := by intro j; cases j <;> assumption
  have hV : ∀ j x, V j x ≠ 0 → |x| ≤ lengthScale j := by
    intro j x h
    cases j
    · change |x| ≤ L₁
      change (if |x| ≤ L₁ then (1 : ℂ) else 0) ≠ 0 at h
      by_contra hx
      exact h (by simp [hx])
    · change |x| ≤ L₂
      change (if |x| ≤ L₂ then (1 : ℂ) else 0) ≠ 0 at h
      by_contra hx
      exact h (by simp [hx])
  obtain ⟨C, hC, hs⟩ := paperRadialFourier_log_separation_envelope V (fun _ => 1) lengthScale hL hV W A 0
  refine ⟨C, hC.le, ?_⟩
  intro R hR
  obtain ⟨b, hb, _, hmass, _⟩ := hs R hR
  refine ⟨b, ?_, ?_⟩
  · intro x y hx hy
    have h := hb (fun j => if j then y else x)
    simpa only [V, V₁, V₂, lengthScale, Fintype.prod_bool, Fintype.sum_bool,
      Bool.false_eq_true, ↓reduceIte, if_pos hx, if_pos hy, one_mul, mul_one,
      add_comm, mul_comm, mul_left_comm, mul_assoc] using h
  · simpa only [pow_zero, one_mul] using hmass

theorem radial_phase_integrable (b : 𝓢(ℝ, ℂ)) (c : ℂ) (x y : ℝ) :
    Integrable (fun t => b t * (kernelLogPhase t x * (c * kernelLogPhase t y))) := by
  apply (b.integrable.norm.mul_const ‖c‖).mono'
  · have hx := kernelLogPhase_continuous_left x
    have hy := kernelLogPhase_continuous_left y
    exact (by fun_prop : Continuous (fun t => b t * (kernelLogPhase t x * (c * kernelLogPhase t y)))).aestronglyMeasurable
  · filter_upwards [] with t
    simp only [norm_mul, kernelLogPhase_norm, one_mul, mul_one]
    exact le_rfl

theorem radial_matrix_kernel_transfer (W : 𝓢(ℝ, ℂ))
    (L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n : Type*} [Fintype m] [Fintype n]
        (c : m → n → ℂ) (x : m → ℝ) (y : n → ℝ) (H : ℝ),
        0 ≤ H → (∀ i, |x i| ≤ L₁) → (∀ j, |y j| ≤ L₂) →
        (∀ t, (∑ i, ‖∑ j, c i j * kernelLogPhase t (y j)‖) ≤ H) →
        (1 + R) ^ A * (∑ i, ‖∑ j, c i j *
          paperRadialFourier W (R * Real.exp (x i + y j))‖) ≤ C * H := by
  obtain ⟨C, hC, hs⟩ := radial_two_variable_window W L₁ L₂ hL₁ hL₂ A
  refine ⟨C, hC, ?_⟩
  intro R hR m n _ _ c x y H hH hx hy hphase
  obtain ⟨b, hb, hmass⟩ := hs R hR
  let φ : m → ℝ → ℂ := fun i t => kernelLogPhase t (x i) * ∑ j, c i j * kernelLogPhase t (y j)
  have hint (i : m) : Integrable (fun t => b t * φ i t) := by
    have h := integrable_finsetSum (Finset.univ : Finset n)
      (fun j _ => radial_phase_integrable b (c i j) (x i) (y j))
    simpa only [φ, Finset.mul_sum] using h
  have hid (i : m) : (∑ j, c i j * paperRadialFourier W (R * Real.exp (x i + y j))) =
      ∫ t, b t * φ i t := by
    rw [show (fun t => b t * φ i t) = fun t =>
      ∑ j, b t * (kernelLogPhase t (x i) * (c i j * kernelLogPhase t (y j))) by
        funext t; simp only [φ, Finset.mul_sum]]
    rw [integral_finsetSum _ (fun j _ => radial_phase_integrable b (c i j) (x i) (y j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [hb _ _ (hx i) (hy j), ← integral_const_mul]
    congr 1
    funext t
    ring
  have hp (t : ℝ) : (∑ i, ‖φ i t‖) ≤ H := by
    simpa only [φ, norm_mul, kernelLogPhase_norm, one_mul] using hphase t
  have hi := sum_norm_integral_bound b φ H hint b.integrable.norm hp
  simp only [← hid] at hi
  calc
    _ ≤ (1 + R) ^ A * (H * ∫ t, ‖b t‖) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = H * ((1 + R) ^ A * ∫ t, ‖b t‖) := by ring
    _ ≤ H * C := mul_le_mul_of_nonneg_left hmass hH
    _ = _ := mul_comm _ _


end QuadraticKernelTransfer

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
