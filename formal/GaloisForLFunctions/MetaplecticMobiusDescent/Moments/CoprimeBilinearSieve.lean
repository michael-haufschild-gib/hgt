/-
The coprime bilinear sieve adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.FiniteSieveOperators

/-!
# The coprime bilinear sieve

Coprimality is an exact signed sum over common ideal divisors. Möbius expansion keeps the two
coefficient masks separate, so coprime restriction costs only a small power of both column
norms (`ideal_coprime_bilinear_operator_bound`).
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

namespace IdealCoprimeBilinearSieve
open Eisenstein UniqueFactorizationMonoid FiniteSieveOperator DivisorBlockCauchy

/-- Coprimality is an exact signed sum over common ideal divisors. -/
lemma common_divisor_indicator (S : Finset (Ideal O)) (I J : Ideal O)
    (hI : I ≠ 0) (hS : idealDivisors I ⊆ S) :
    (if I ⊔ J = ⊤ then (1 : ℂ) else 0) =
      ∑ D ∈ S, if D ∣ I ∧ D ∣ J then (moebius D : ℂ) else 0 := by
  have hG : I ⊔ J ≠ (0 : Ideal O) := by
    intro h
    exact hI (le_antisymm (h ▸ le_sup_left) bot_le)
  have hfilter : S.filter (fun D => D ∣ I ∧ D ∣ J) = idealDivisors (I ⊔ J) := by
    ext D
    simp only [Finset.mem_filter, mem_idealDivisors hG, Ideal.dvd_iff_le, sup_le_iff]
    constructor
    · exact And.right
    · intro h
      exact ⟨hS ((mem_idealDivisors hI).mpr (Ideal.dvd_iff_le.mpr h.1)), h⟩
  rw [← Finset.sum_filter, hfilter, sum_moebius_divisors _ hG]

lemma moebius_norm_le_one (D : Ideal O) : ‖(moebius D : ℂ)‖ ≤ 1 := by
  by_cases h : Squarefree D
  · rw [h.moebius_eq]
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow, norm_neg,
      norm_one, one_pow, le_refl]
  · rw [moebius_of_not_squarefree h, Int.cast_zero, norm_zero]
    norm_num

/-- Möbius expansion keeps left and right coefficient masks separate. -/
lemma bilinear_expansion {n p : Type*} [Fintype n] [Fintype p]
    (S : Finset (Ideal O)) (left : n → Ideal O) (right : p → Ideal O)
    (hl : ∀ j, left j ≠ 0) (hS : ∀ j, idealDivisors (left j) ⊆ S)
    (z : n → ℂ) (v : p → ℂ) :
    (∑ j, ∑ k, if left j ⊔ right k = ⊤ then star (z j) * v k else 0) =
      ∑ D ∈ S, (moebius D : ℂ) *
        (star (∑ j, if D ∣ left j then z j else 0) *
          (∑ k, if D ∣ right k then v k else 0)) := by
  have hp (j : n) (k : p) :
      (if left j ⊔ right k = ⊤ then star (z j) * v k else 0) =
        ∑ D ∈ S, (moebius D : ℂ) *
          (if D ∣ left j ∧ D ∣ right k then star (z j) * v k else 0) := by
    calc
      _ = (if left j ⊔ right k = ⊤ then (1 : ℂ) else 0) *
          (star (z j) * v k) := by split_ifs <;> simp
      _ = _ := by
        rw [common_divisor_indicator S _ _ (hl j) (hS j), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D _
        split_ifs <;> simp
  simp_rw [hp]
  calc
    _ = ∑ j, ∑ D ∈ S, ∑ k, (moebius D : ℂ) *
        (if D ∣ left j ∧ D ∣ right k then star (z j) * v k else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ D ∈ S, ∑ j, ∑ k, (moebius D : ℂ) *
        (if D ∣ left j ∧ D ∣ right k then star (z j) * v k else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      simp_rw [← Finset.mul_sum]
      congr 1
      simp only [star_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases hj : D ∣ left j <;> by_cases hk : D ∣ right k <;> simp [hj, hk]

/-- Coprime restriction costs only a small power of both column norms. -/
theorem ideal_coprime_bilinear_operator_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (left : n → Ideal O) (right : p → Ideal O)
    (hl : ∀ j, left j ≠ 0) (hr : ∀ k, right k ≠ 0)
    (N₁ N₂ : ℝ) (hlN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N₁)
    (hrN : ∀ k, (Ideal.absNorm (right k) : ℝ) ≤ N₂)
    (A : Matrix m n ℂ) (B : Matrix m p ℂ) (a : n → ℂ) (b : p → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if left j ⊔ right k = ⊤ then
      star (A i j * a j) * (B i k * b k) else 0‖) ^ 2 ≤
      (‖operator A‖ ^ 2 * (divisorConstant ε hε * N₁ ^ ε) * ∑ j, ‖a j‖ ^ 2) *
      (‖operator B‖ ^ 2 * (divisorConstant ε hε * N₂ ^ ε) * ∑ k, ‖b k‖ ^ 2) := by
  classical
  let S := Finset.univ.biUnion (fun j : n => idealDivisors (left j))
  have hS (j : n) : idealDivisors (left j) ⊆ S := by
    intro D hD
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hD⟩
  let X (D : Ideal O) (i : m) : ℂ := ∑ j, A i j * (if D ∣ left j then a j else 0)
  let Y (D : Ideal O) (i : m) : ℂ := ∑ k, B i k * (if D ∣ right k then b k else 0)
  have heq (i : m) :
      (∑ j, ∑ k, if left j ⊔ right k = ⊤ then
        star (A i j * a j) * (B i k * b k) else 0) =
        ∑ D ∈ S, (moebius D : ℂ) * (star (X D i) * Y D i) := by
    simpa only [X, Y, mul_ite, mul_zero] using
      bilinear_expansion S left right hl hS (fun j => A i j * a j) (fun k => B i k * b k)
  have hnorm :
      (∑ i, ‖∑ j, ∑ k, if left j ⊔ right k = ⊤ then
        star (A i j * a j) * (B i k * b k) else 0‖) ≤
        ∑ D ∈ S, ∑ i, ‖X D i‖ * ‖Y D i‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i _
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro D _
    rw [norm_mul, norm_mul, norm_star]
    exact mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (moebius_norm_le_one D)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (S ×ˢ (Finset.univ : Finset m))
    (fun di => ‖X di.1 di.2‖) (fun di => ‖Y di.1 di.2‖)
  simp only [Finset.sum_product] at hCS
  have hX : (∑ D ∈ S, ∑ i, ‖X D i‖ ^ 2) ≤
      ‖operator A‖ ^ 2 * (divisorConstant ε hε * N₁ ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
    calc
      _ ≤ ∑ D ∈ S, ‖operator A‖ ^ 2 * ∑ j, ‖if D ∣ left j then a j else 0‖ ^ 2 :=
        Finset.sum_le_sum (fun D _ => energy_bound A _)
      _ = ‖operator A‖ ^ 2 * (∑ D ∈ S, ∑ j, ‖if D ∣ left j then a j else 0‖ ^ 2) :=
        (Finset.mul_sum ..).symm
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (divisor_mask_energy_small_power ε hε S left hl N₁ hlN a) (sq_nonneg _)
  have hY : (∑ D ∈ S, ∑ i, ‖Y D i‖ ^ 2) ≤
      ‖operator B‖ ^ 2 * (divisorConstant ε hε * N₂ ^ ε) * ∑ k, ‖b k‖ ^ 2 := by
    calc
      _ ≤ ∑ D ∈ S, ‖operator B‖ ^ 2 * ∑ k, ‖if D ∣ right k then b k else 0‖ ^ 2 :=
        Finset.sum_le_sum (fun D _ => energy_bound B _)
      _ = ‖operator B‖ ^ 2 * (∑ D ∈ S, ∑ k, ‖if D ∣ right k then b k else 0‖ ^ 2) :=
        (Finset.mul_sum ..).symm
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (divisor_mask_energy_small_power ε hε S right hr N₂ hrN b) (sq_nonneg _)
  exact (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hnorm 2).trans
    (hCS.trans (mul_le_mul hX hY (by positivity) ((by positivity : 0 ≤ ∑ D ∈ S, ∑ i, ‖X D i‖ ^ 2).trans hX)))

end IdealCoprimeBilinearSieve

namespace IdealCoprimeBilinearSieve
open Eisenstein DivisorBlockCauchy FiniteSieveOperator

/-- A bounded row weight multiplies the coprime Gram bound by its supremum. -/
theorem weighted_coprime_gram_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ε : ℝ) (hε : 0 < ε)
    (cols : n → Ideal O) (hc : ∀ j, cols j ≠ 0) (N : ℝ) (hN : 0 ≤ N)
    (hcols : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N) (A : Matrix m n ℂ) (a : n → ℂ)
    (w : m → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) :
    ‖∑ i, w i * (∑ j, ∑ k, if cols j ⊔ cols k = ⊤ then
      star (A i j * a j) * (A i k * a k) else 0)‖ ≤
      C * (‖operator A‖ ^ 2 * (divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) := by
  have hs := ideal_coprime_bilinear_operator_bound ε hε cols cols hc hc N N hcols hcols A A a a
  have hb : 0 ≤ ‖operator A‖ ^ 2 * (divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
    have hd := (divisorConstant_pos ε hε).le
    have hn := Real.rpow_nonneg hN ε
    positivity
  have hsum : (∑ i, ‖∑ j, ∑ k, if cols j ⊔ cols k = ⊤ then
      star (A i j * a j) * (A i k * a k) else 0‖) ≤
      ‖operator A‖ ^ 2 * (divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
    nlinarith only [hs, hb]
  calc
    _ ≤ ∑ i, ‖w i‖ * ‖∑ j, ∑ k, if cols j ⊔ cols k = ⊤ then
        star (A i j * a j) * (A i k * a k) else 0‖ := by
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun i => w i *
        (∑ j, ∑ k, if cols j ⊔ cols k = ⊤ then star (A i j * a j) * (A i k * a k) else 0))
    _ ≤ ∑ i, C * ‖∑ j, ∑ k, if cols j ⊔ cols k = ⊤ then
        star (A i j * a j) * (A i k * a k) else 0‖ :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hw i) (norm_nonneg _))
    _ = C * ∑ i, ‖∑ j, ∑ k, if cols j ⊔ cols k = ⊤ then
        star (A i j * a j) * (A i k * a k) else 0‖ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hC

end IdealCoprimeBilinearSieve

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
