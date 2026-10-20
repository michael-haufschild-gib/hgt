import GaloisForLFunctions.BezoutValuationIncidence.MomentSignVisibilityAndZeroProductRelations

/-!
# Parseval for translated-moment arrays: the energy cost of a relation

The degree-`m` translated moments of a row form an array indexed by shift vectors
`v ∈ [0, P)^m`, `P = N!`. In the spectral form

`M_m(c; v) = Σ_{ζ ∈ T_N^m, Π ζ_i = 1} A_c(ζ) Π_i ζ_i^{v_i}`,  `A_c(ζ) = Π_i Y_c(ord ζ_i)`,

the array is a finite exponential sum in `v` over the zero-product tuples, and the multi-characters
are orthogonal over `[0, P)^m`. Hence the mean square over all shift vectors of the difference of
two moment arrays is the energy of the difference of their relation coefficients:

`P^{-m} Σ_v (M_m(c; v) - M_m(c'; v))² = Σ_{Π ζ_i = 1} (A_c(ζ) - A_{c'}(ζ))²`.

For the sign-scaled row with coordinates `εY` the right side is `Σ (Π Y)² (1 - Π ε)²`; for a sign
pattern it is four times the energy of the zero-product relations of odd `ε`-weight. Visibility of a
sign pattern at degree `m` is therefore measured, not only decided, by the relations of length `m`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The zero-product `m`-tuples of response frequencies. -/
def zeroProductTuples (N m : ℕ) : Finset (Fin m → ℂ) :=
  (Fintype.piFinset fun _ : Fin m => responseRoots N).filter fun ζ => ∏ i, ζ i = 1

/-- The relation coefficient `Π_i Y(ord ζ_i)` of a tuple. -/
def relationCoeff (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (ζ : Fin m → ℂ) : ℝ :=
  ∏ i, selbergMultiplesCoord N c (orderOf (ζ i))

theorem translatedMoment_eq_sum_relationCoeff (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (v : Fin m → ℕ) :
    (SieveMoments.translatedMoment N c v : ℂ) =
      ∑ ζ ∈ zeroProductTuples N m, (relationCoeff N c ζ : ℂ) * ∏ i, ζ i ^ v i := by
  rw [translatedMoment_eq_spectral]
  refine sum_congr rfl fun ζ _ => ?_
  rw [relationCoeff, Complex.ofReal_prod, ← prod_mul_distrib]

/-- Orthogonality of multi-characters over `[0, P)^m` for `P`-th roots of unity. -/
theorem sum_piFinset_prod_pow_mul_conj {P m : ℕ} (hP : 0 < P) {ζ ξ : Fin m → ℂ}
    (hζ : ∀ i, ζ i ^ P = 1) (hξ : ∀ i, ξ i ^ P = 1) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin m => range P), ∏ i, ζ i ^ v i * conj (ξ i ^ v i) =
      if ζ = ξ then (P : ℂ) ^ m else 0 := by
  classical
  rw [← prod_univ_sum (fun _ => range P) (fun i k => ζ i ^ k * conj (ξ i ^ k))]
  have hone : ∀ i, (∑ k ∈ range P, ζ i ^ k * conj (ξ i ^ k)) = if ζ i = ξ i then (P : ℂ) else 0 := by
    intro i
    have hnξ : ‖ξ i‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (hξ i) hP.ne'
    have hnζ : ‖ζ i‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (hζ i) hP.ne'
    have hrw : ∀ k, ζ i ^ k * conj (ξ i ^ k) = (ζ i * conj (ξ i)) ^ k := fun k => by
      rw [map_pow, mul_pow]
    simp_rw [hrw]
    split_ifs with heq
    · rw [heq, mul_comm, conj_mul_self_of_norm_eq_one hnξ]
      simp
    · have hz1 : ζ i * conj (ξ i) ≠ 1 := by
        intro h
        apply heq
        calc ζ i = ζ i * (conj (ξ i) * ξ i) := by rw [conj_mul_self_of_norm_eq_one hnξ, mul_one]
          _ = (ζ i * conj (ξ i)) * ξ i := by ring
          _ = ξ i := by rw [h, one_mul]
      have hzP : (ζ i * conj (ξ i)) ^ P = 1 := by rw [mul_pow, ← map_pow, hζ i, hξ i, map_one,
        one_mul]
      rw [geom_sum_eq hz1, hzP, sub_self, zero_div]
  simp_rw [hone]
  by_cases heq : ζ = ξ
  · rw [if_pos heq]
    simp [heq]
  · rw [if_neg heq]
    obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ ξ i := by
      by_contra h
      push Not at h
      exact heq (funext h)
    exact prod_eq_zero (mem_univ i) (if_neg hi)

/-- **Parseval for translated-moment arrays.** -/
theorem sum_sq_translatedMoment_sub_eq (N m : ℕ) (c c' : ℕ → ℝ) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin m => range N.factorial),
        (SieveMoments.translatedMoment N c v - SieveMoments.translatedMoment N c' v) ^ 2 =
      (N.factorial : ℝ) ^ m *
        ∑ ζ ∈ zeroProductTuples N m, (relationCoeff N c ζ - relationCoeff N c' ζ) ^ 2 := by
  classical
  have hP := Nat.factorial_pos N
  set S := zeroProductTuples N m
  set a : (Fin m → ℂ) → ℂ := fun ζ => ((relationCoeff N c ζ - relationCoeff N c' ζ : ℝ) : ℂ)
  have hroots : ∀ ζ ∈ S, ∀ i, ζ i ^ N.factorial = 1 := fun ζ hζ i =>
    pow_factorial_eq_one_of_mem_responseRoots
      ((Fintype.mem_piFinset.mp (mem_filter.mp hζ).1) i)
  have hD : ∀ v : Fin m → ℕ, ((SieveMoments.translatedMoment N c v -
      SieveMoments.translatedMoment N c' v : ℝ) : ℂ) = ∑ ζ ∈ S, a ζ * ∏ i, ζ i ^ v i := by
    intro v
    rw [Complex.ofReal_sub, translatedMoment_eq_sum_relationCoeff,
      translatedMoment_eq_sum_relationCoeff, ← sum_sub_distrib]
    refine sum_congr rfl fun ζ _ => ?_
    simp only [a]
    push_cast
    ring
  apply Complex.ofReal_injective
  push_cast
  have hsq : ∀ v : Fin m → ℕ, ((SieveMoments.translatedMoment N c v -
      SieveMoments.translatedMoment N c' v : ℝ) : ℂ) ^ 2 =
      ∑ ζ ∈ S, ∑ ξ ∈ S, a ζ * conj (a ξ) * ∏ i, ζ i ^ v i * conj (ξ i ^ v i) := by
    intro v
    have hreal : conj ((SieveMoments.translatedMoment N c v -
        SieveMoments.translatedMoment N c' v : ℝ) : ℂ) =
        ((SieveMoments.translatedMoment N c v - SieveMoments.translatedMoment N c' v : ℝ) : ℂ) :=
      Complex.conj_ofReal _
    rw [sq]
    nth_rewrite 2 [← hreal]
    rw [hD, map_sum, sum_mul_sum]
    refine sum_congr rfl fun ζ _ => sum_congr rfl fun ξ _ => ?_
    rw [map_mul, map_prod, prod_mul_distrib]
    ring
  have hlhs : ∑ v ∈ Fintype.piFinset (fun _ : Fin m => range N.factorial),
      (((SieveMoments.translatedMoment N c v : ℂ) - (SieveMoments.translatedMoment N c' v : ℂ)) ^ 2) =
      ∑ ζ ∈ S, ∑ ξ ∈ S, a ζ * conj (a ξ) * (if ζ = ξ then (N.factorial : ℂ) ^ m else 0) := by
    rw [sum_congr rfl fun v _ => by rw [← Complex.ofReal_sub, hsq v], sum_comm]
    refine sum_congr rfl fun ζ hζ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun ξ hξ => ?_
    rw [← mul_sum, sum_piFinset_prod_pow_mul_conj hP (hroots ζ hζ) (hroots ξ hξ)]
  rw [hlhs, mul_sum]
  refine sum_congr rfl fun ζ _ => ?_
  rw [sum_eq_single ζ (fun ξ _ hne => by rw [if_neg (Ne.symm hne), mul_zero])
    (fun h => absurd ‹ζ ∈ S› h), if_pos rfl]
  simp only [a, Complex.conj_ofReal]
  push_cast
  ring

/-- **The energy cost of a sign pattern.** For the sign-scaled row, the mean square of the moment
difference is `Σ (Π Y)² (1 - Π ε)²` over the zero-product tuples. -/
theorem sum_sq_translatedMoment_scaled_sub_eq (N m : ℕ) (c : ℕ → ℝ) (ε : ℕ → ℝ) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin m => range N.factorial),
        (SieveMoments.translatedMoment N (scaledSelbergRow N c ε) v -
          SieveMoments.translatedMoment N c v) ^ 2 =
      (N.factorial : ℝ) ^ m * ∑ ζ ∈ zeroProductTuples N m,
        relationCoeff N c ζ ^ 2 * (1 - ∏ i, ε (orderOf (ζ i))) ^ 2 := by
  rw [sum_sq_translatedMoment_sub_eq]
  congr 1
  refine sum_congr rfl fun ζ hζ => ?_
  have hcoord : ∀ i, selbergMultiplesCoord N (scaledSelbergRow N c ε) (orderOf (ζ i)) =
      ε (orderOf (ζ i)) * selbergMultiplesCoord N c (orderOf (ζ i)) := fun i =>
    selbergMultiplesCoord_scaledSelbergRow c ε (orderOf_mem_Icc_of_mem_responseRoots
      ((Fintype.mem_piFinset.mp (mem_filter.mp hζ).1) i))
  unfold relationCoeff
  simp only [hcoord, prod_mul_distrib]
  ring

private theorem sign_relation_term {m : ℕ} {ε : ℕ → ℝ} (hε : ∀ q, ε q = 1 ∨ ε q = -1)
    (ζ : Fin m → ℂ) (y : ℝ) :
    y * (1 - ∏ i, ε (orderOf (ζ i))) ^ 2 =
      4 * (if ∏ i, ε (orderOf (ζ i)) = -1 then y else 0) := by
  have hprod : ∀ s : Finset (Fin m), ∏ i ∈ s, ε (orderOf (ζ i)) = 1 ∨
      ∏ i ∈ s, ε (orderOf (ζ i)) = -1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => left; simp
    | insert j s hj ih =>
      rw [prod_insert hj]
      rcases hε (orderOf (ζ j)) with h1 | h1 <;> rcases ih with h2 | h2 <;>
        rw [h1, h2] <;> norm_num
  rcases hprod univ with h | h
  · rw [h, if_neg (by norm_num)]
    ring
  · rw [h, if_pos rfl]
    ring

/-- For a sign pattern the cost is four times the energy of the odd relations. -/
theorem sum_sq_translatedMoment_signFlip_sub_eq (N m : ℕ) (c : ℕ → ℝ) {ε : ℕ → ℝ}
    (hε : ∀ q, ε q = 1 ∨ ε q = -1) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin m => range N.factorial),
        (SieveMoments.translatedMoment N (scaledSelbergRow N c ε) v -
          SieveMoments.translatedMoment N c v) ^ 2 =
      4 * (N.factorial : ℝ) ^ m * ∑ ζ ∈ (zeroProductTuples N m).filter
        (fun ζ => ∏ i, ε (orderOf (ζ i)) = -1), relationCoeff N c ζ ^ 2 := by
  classical
  rw [sum_sq_translatedMoment_scaled_sub_eq,
    sum_congr rfl fun ζ _ => sign_relation_term hε ζ (relationCoeff N c ζ ^ 2), ← mul_sum,
    ← Finset.sum_filter]
  ring

end

end GaloisForLFunctions.BezoutValuationIncidence
