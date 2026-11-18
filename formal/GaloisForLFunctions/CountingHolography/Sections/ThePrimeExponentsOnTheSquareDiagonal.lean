import GaloisForLFunctions.CountingHolography.Sections.TheDyadicPrimeWeightOfSquareConductors
import GaloisForLFunctions.CountingHolography.Sections.ReducedOrdinaryPrimeProducts
import GaloisForLFunctions.CountingHolography.Sections.TheCoefficientIndependentPrimeMeshError

/-! # Approximation of the individual prime valuations on the diagonal

The floor costs at most one per ordinary prime, and the contact quadrature
has bounded error per row. The remaining displacement of the high conductor
has bounded total logarithmic weight before multiplication by n squared.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset ArithmeticFunction AbsoluteGeometryOfSpecZ ArithmeticCastelnuovoSeveri _root_.RHTower

/-- Prime valuation predicted by the fixed dyadic profile at multiplicity n. -/
def diagonalPrimeProfile (n k : ℕ) : ℝ := (n:ℝ)^2*((2/Real.sqrt k)*
  squareLogProfile (Real.log k-Real.log ((n:ℝ)^2)))

theorem diagonalPrimeProfile_eq_dilate {n k : ℕ} (hn : 0<n) (hk : 0<k) :
    diagonalPrimeProfile n k=2*(n:ℝ)*
      (squareLogProfile (Real.log ((k:ℝ)/(n:ℝ)^2))/Real.sqrt ((k:ℝ)/(n:ℝ)^2)) := by
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  rw [diagonalPrimeProfile,Real.log_div hk'.ne' (sq_pos_of_pos hn').ne',
    Real.sqrt_div hk'.le,Real.sqrt_sq hn'.le]
  field_simp [hn'.ne',(Real.sqrt_pos.mpr hk').ne']

/-- Total absolute error in the actual prime valuations, with logarithmic
prime weights. The same constant works at every positive conductor. -/
theorem diagonal_prime_exponent_profile_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
    (∑ k ∈ ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1)),
      |(deningerRatExp q k:ℝ)-diagonalPrimeProfile n k| * vonMangoldt k) ≤ C*(n:ℝ)^2 := by
  obtain ⟨D,hD,hd⟩ := dyadicPrimeContact_absolute_row_error
  obtain ⟨B,hB,hb⟩ := original_contact_quadrature
  obtain ⟨A,hA,ha⟩ := successorSquare_window_bound
  refine ⟨(1+B)*7*A^2+D,by positivity,fun {n} hn => ?_⟩
  let N := (2*n+1)^2+1
  let L := 3*windowEnd N
  let S := ordinaryPrimeLags L
  let d := successorSquareTriple n
  let a := n • d
  let X := contactMultiplicity (packet a) L (resolution a)
  let q := ordinaryPrimeGenerator a
  let F := fun k : ℕ => (2/Real.sqrt k)*squareLogProfile (Real.log k-Real.log ((n:ℝ)^2))
  have hrow (k : ℕ) (hk : k ∈ S) :
      |(deningerRatExp q k:ℝ)-diagonalPrimeProfile n k| ≤
        (1+B)+(n:ℝ)^2*|integratedContact d k-F k| := by
    have hp := (mem_filter.mp hk).2
    have hr : 1 ≤ Real.sqrt k := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hp.pos : (1:ℝ)≤k)
    have hx : |X k-integratedContact a k| ≤ B :=
      (hb N a hp.pos).trans (div_le_self hB hr)
    have he : deningerRatExp q k=⌊X k⌋ := by
      have h := ordinaryPrimeGenerator_exponent a k
      change deningerRatExp q k = if k ∈ S then ⌊X k⌋ else 0 at h
      exact h.trans (if_pos hk)
    have hf : |(⌊X k⌋:ℝ)-X k| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith only [Int.floor_le (X k),Int.sub_one_lt_floor (X k)]
    have ht := abs_sub_le (⌊X k⌋:ℝ) (X k) (integratedContact a k)
    have hu := abs_sub_le (⌊X k⌋:ℝ) (integratedContact a k) ((n:ℝ)^2*F k)
    have hm : |integratedContact a k-(n:ℝ)^2*F k|=(n:ℝ)^2*|integratedContact d k-F k| := by
      rw [show a=n • d from rfl,integratedContact_nsmul,← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg _)]
    rw [hm] at hu
    rw [he]
    change |(⌊X k⌋:ℝ)-(n:ℝ)^2*F k| ≤ _
    linarith only [hf,hx,ht,hu]
  have hmass : ∑ k ∈ S, vonMangoldt k ≤ 7*(A*n)^2 := (ordinaryPrimeLagSums L).1.trans
    (mul_le_mul_of_nonneg_left (ha hn) (by norm_num))
  change (∑ k ∈ S, |(deningerRatExp q k:ℝ)-diagonalPrimeProfile n k| * vonMangoldt k) ≤ _
  calc _ ≤ ∑ k ∈ S, ((1+B)+(n:ℝ)^2*|integratedContact d k-F k|)*vonMangoldt k :=
              sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hrow k hk) vonMangoldt_nonneg
    _ = (1+B)*(∑ k ∈ S, vonMangoldt k)+(n:ℝ)^2*
        (∑ k ∈ S, |integratedContact d k-F k| * vonMangoldt k) := by
      simp only [add_mul,sum_add_distrib,mul_assoc,← mul_sum]
    _ ≤ (1+B)*(7*(A*n)^2)+(n:ℝ)^2*D := add_le_add
      (mul_le_mul_of_nonneg_left hmass (by positivity)) (mul_le_mul_of_nonneg_left (hd hn) (sq_nonneg _))
    _ = _ := by ring

/-- The signed total multiplicity counts the numerator prime factors minus
the denominator prime factors, each counted with its full multiplicity. -/
def diagonalPrimeMultiplicity (n : ℕ) : ℤ :=
  ∑ k ∈ ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1)),
    deningerRatExp (ordinaryPrimeGenerator (n • successorSquareTriple n)) k

theorem diagonalPrimeMultiplicity_eq_cardFactors (n : ℕ) :
    let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
    diagonalPrimeMultiplicity n=(cardFactors q.num.natAbs:ℤ)-cardFactors q.den := by
  let a := n • successorSquareTriple n
  let q := ordinaryPrimeGenerator a
  let S := ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1))
  let U := (S ∪ q.num.natAbs.factorization.support) ∪ q.den.factorization.support
  have hS : S ⊆ U := subset_union_left.trans subset_union_left
  have hnum : q.num.natAbs.factorization.support ⊆ U := subset_union_right.trans subset_union_left
  have hden : q.den.factorization.support ⊆ U := subset_union_right
  have hread {j : ℕ} (hj : j.factorization.support ⊆ U) :
      (cardFactors j:ℤ)=∑ p ∈ U, (j.factorization p:ℤ) := by
    rw [cardFactors_eq_sum_factorization,j.factorization.sum_of_support_subset hj _ (fun _ _ => rfl),Nat.cast_sum]
  change (∑ p ∈ S, deningerRatExp q p)=(cardFactors q.num.natAbs:ℤ)-cardFactors q.den
  rw [hread hnum,hread hden,← sum_sub_distrib]
  calc _ = ∑ p ∈ U, deningerRatExp q p := sum_subset hS fun p _ hp => by
            have hh := ordinaryPrimeGenerator_exponent a p
            change deningerRatExp q p = if p ∈ S then _ else 0 at hh
            exact hh.trans (if_neg hp)
    _ = _ := sum_congr rfl fun _ _ => rfl

/-- Exact second-order expansion of the centered logarithmic weight, with
a uniform error from replacing the individual valuations by their profile. -/
theorem diagonal_prime_multiplicity_comparison : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
    let S := ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1))
    let T := Real.log ((n:ℝ)^2)
    |T^2*(diagonalPrimeMultiplicity n:ℝ)-T*Real.log (q:ℝ)+
      (∑ k ∈ S, Real.log k*(Real.log k-T)*diagonalPrimeProfile n k)-
      (∑ k ∈ S, (Real.log k-T)^2*diagonalPrimeProfile n k)| ≤
      (T^2/Real.log 2+T)*(C*(n:ℝ)^2) := by
  obtain ⟨C,hC,h⟩ := diagonal_prime_exponent_profile_error
  refine ⟨C,hC,fun {n} hn => ?_⟩
  let a := n • successorSquareTriple n
  let q := ordinaryPrimeGenerator a
  let S := ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1))
  let T := Real.log ((n:ℝ)^2)
  let K := T^2/Real.log 2+T
  let e := fun k : ℕ => (deningerRatExp q k:ℝ)
  let f := diagonalPrimeProfile n
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hT : 0 ≤ T := Real.log_nonneg (one_le_pow₀ (by exact_mod_cast hn : (1:ℝ)≤n))
  have hK : 0 ≤ K := add_nonneg (div_nonneg (sq_nonneg _) hlog.le) hT
  have hg : Real.log (q:ℝ)=∑ k ∈ S, Real.log k*e k := by
    rw [log_ordinaryPrimeGenerator]
    exact sum_congr rfl fun k hk => by
      have hp := (mem_filter.mp hk).2
      have he := ordinaryPrimeGenerator_exponent a k
      change deningerRatExp q k = if k ∈ S then _ else 0 at he
      rw [if_pos hk] at he
      change _ = Real.log k*(deningerRatExp q k:ℝ)
      rw [he,vonMangoldt_apply_prime hp]
      exact mul_comm _ _
  have hsum : (diagonalPrimeMultiplicity n:ℝ)=∑ k ∈ S, e k := by
    simp only [diagonalPrimeMultiplicity,Int.cast_sum]; rfl
  have hcoef {k : ℕ} (hk : k ∈ S) : |T^2-T*Real.log k| ≤ K*Real.log k := by
    have hk₂ := Real.log_le_log (by norm_num : (0:ℝ)<2)
      (by exact_mod_cast (mem_filter.mp hk).2.two_le : (2:ℝ)≤k)
    have hk₀ := hlog.le.trans hk₂
    have hu := mul_le_mul_of_nonneg_left hk₂ (div_nonneg (sq_nonneg T) hlog.le)
    rw [div_mul_cancel₀ _ hlog.ne'] at hu
    have hh := abs_sub (T^2) (T*Real.log k)
    simp only [abs_of_nonneg (sq_nonneg T),abs_of_nonneg (mul_nonneg hT hk₀)] at hh
    dsimp only [K]
    rw [add_mul]
    linarith only [hh,hu]
  change |T^2*(diagonalPrimeMultiplicity n:ℝ)-T*Real.log (q:ℝ)+
    (∑ k ∈ S, Real.log k*(Real.log k-T)*f k)-(∑ k ∈ S, (Real.log k-T)^2*f k)| ≤ _
  rw [hsum,hg,mul_sum,mul_sum,← sum_sub_distrib,← sum_add_distrib,← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ k ∈ S, K*(|e k-f k| * vonMangoldt k) := sum_le_sum fun k hk => by
              rw [show T^2*e k-T*(Real.log k*e k)+Real.log k*(Real.log k-T)*f k-
                (Real.log k-T)^2*f k=(T^2-T*Real.log k)*(e k-f k) by ring,
                abs_mul,vonMangoldt_apply_prime (mem_filter.mp hk).2]
              exact (mul_le_mul_of_nonneg_right (hcoef hk) (abs_nonneg _)).trans_eq (by ring)
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (h hn) hK

#print axioms diagonal_prime_multiplicity_comparison
#print axioms diagonal_prime_exponent_profile_error

end GaloisForLFunctions.CountingHolography.Sections
