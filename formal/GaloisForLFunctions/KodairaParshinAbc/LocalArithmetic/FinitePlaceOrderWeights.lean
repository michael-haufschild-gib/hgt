import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualTwoAdicDecomposition
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Recovering prime ideal exponents from weighted absolute values

With local logarithms divided by the global degree as in Ziegler
(arXiv:2609.15487, §2), division by log p recovers f/d times the
ideal exponent. At the dyadic places of the literal quaternion field
the multiplier is 1/4. The printed quotient for the integer two is 1/2,
whereas the prime ideal occurs twice.
-/

noncomputable section
open NumberField Ideal IsDedekindDomain Real
open scoped NumberField
namespace GaloisForLFunctions.KodairaParshinAbc
variable {K : Type*} [Field K] [NumberField K]

/-- Exponent recorded by a local logarithm normalized by the ambient degree. -/
def weightedPrimeOrder (p : ℕ) (v : FinitePlace K) (x : K) : ℝ :=
  (-log (v x) / Module.finrank ℚ K) / log p

/-- The actual exponent is recovered after including the inertia-degree factor. -/
theorem weightedPrimeOrder_eq (p : ℕ) (hp : p.Prime) (v : FinitePlace K)
    [v.maximalIdeal.asIdeal.LiesOver (span {(p:ℤ)})] (x : 𝓞 K) (hx : x ≠ 0) :
    weightedPrimeOrder p v x =
      (multiplicity v.maximalIdeal.asIdeal (span {x}) : ℝ) *
        ((span {(p:ℤ)}).inertiaDeg' v.maximalIdeal.asIdeal : ℕ) / Module.finrank ℚ K := by
  let P := v.maximalIdeal.asIdeal
  let m := multiplicity P (span {x})
  let f := (span {(p:ℤ)}).inertiaDeg' P
  have h := FinitePlace.apply_mul_absNorm_pow_eq_one v hx
  change v (x:K) * (P.absNorm:ℝ)^m = 1 at h
  rw [Ideal.absNorm_eq_pow_inertiaDeg' P hp, Nat.cast_pow] at h
  have hlog := congrArg log h
  have hp0 : (p:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hv : v (x:K) ≠ 0 := fun h0 => by rw [h0,zero_mul] at h; exact zero_ne_one h
  rw [Real.log_mul hv (pow_ne_zero _ (pow_ne_zero _ hp0)), Real.log_pow, Real.log_pow,
    Real.log_one] at hlog
  have hl : log (p:ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have he : -log (v (x:K)) = (m:ℝ)*(f:ℝ)*log (p:ℝ) := by linear_combination -hlog
  change -log (v (x:K)) / (Module.finrank ℚ K:ℝ) / log (p:ℝ) = (m:ℝ)*(f:ℝ) / _
  rw [he]
  field_simp [hl,hd]

/-- The uncorrected quotient equals the ideal order exactly at units or full residue degree. -/
theorem weightedPrimeOrder_eq_multiplicity_iff (p : ℕ) (hp : p.Prime) (v : FinitePlace K)
    [v.maximalIdeal.asIdeal.LiesOver (span {(p:ℤ)})] (x : 𝓞 K) (hx : x ≠ 0) :
    weightedPrimeOrder p v x = (multiplicity v.maximalIdeal.asIdeal (span {x}) : ℝ) ↔
      multiplicity v.maximalIdeal.asIdeal (span {x}) = 0 ∨
      (span {(p:ℤ)}).inertiaDeg' v.maximalIdeal.asIdeal = Module.finrank ℚ K := by
  rw [weightedPrimeOrder_eq p hp v x hx, div_eq_iff (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')]
  rw [mul_eq_mul_left_iff, or_comm]
  norm_cast

section Quaternion
open _root_.RHTower
local notation "L" => deningerQ8RootNumberNegOneTopField
attribute [local instance] q8DecompositionCharZeroK3 q8DecompositionFiniteDimensionalRatK3
  q8DecompositionNumberFieldK3 q8DecompositionIsGalois

/-- At every dyadic place of the quaternion field, the paper's logarithmic quotient is a quarter-order. -/
theorem quaternionDyadic_order (v : FinitePlace L) (hv : (2:𝓞 L) ∈ v.maximalIdeal.asIdeal)
    (x : 𝓞 L) (hx : x ≠ 0) :
    weightedPrimeOrder 2 v x = (multiplicity v.maximalIdeal.asIdeal (span {x}):ℝ)/4 := by
  let P := v.maximalIdeal.asIdeal
  letI : (span {(2:ℤ)}).IsMaximal := Int.prime_two.isMaximal_span_singleton
  letI : P.LiesOver (span {(2:ℤ)}) :=
    (Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)) Int.prime_two).2 hv
  have hd : Module.finrank ℚ L = 8 := by
    calc
      _ = Nat.card Gal(L/ℚ) := (IsGalois.card_aut_eq_finrank ℚ L).symm
      _ = Nat.card (QuaternionGroup 2) := Nat.card_congr deningerQ8RootNumberNegOne_galoisEquivQ8.toEquiv
      _ = 8 := by rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [weightedPrimeOrder_eq 2 Nat.prime_two v x hx, Ideal.inertiaDeg'_eq_inertiaDeg,
    q8Literal_two_inertiaDeg_eq_two P hv, hd]
  push_cast
  ring

/-- Two already gives an unconditional nonintegral reading, at an actual finite place. -/
theorem quaternionDyadic_nonintegral_reading :
    ∃ v : FinitePlace L, multiplicity v.maximalIdeal.asIdeal (span {(2:𝓞 L)}) = 2 ∧
      weightedPrimeOrder 2 v (2:L) = 1/2 := by
  let J := span {(2:ℤ)}
  letI : J.IsMaximal := Int.prime_two.isMaximal_span_singleton
  obtain ⟨P,hP,hPJ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) J
  letI : P.IsMaximal := hP
  letI : P.LiesOver J := hPJ
  have h2 : (2:𝓞 L) ∈ P := (Ideal.liesOver_span_iff hP.ne_top Int.prime_two).1 hPJ
  have hP0 : P ≠ ⊥ := fun h => by rw [h,Ideal.mem_bot] at h2; exact two_ne_zero h2
  let w : HeightOneSpectrum (𝓞 L) := ⟨P,inferInstance,hP0⟩
  let v := FinitePlace.mk w
  have hPv : v.maximalIdeal.asIdeal = P := congrArg HeightOneSpectrum.asIdeal (FinitePlace.maximalIdeal_mk w)
  have hm : J.map (algebraMap ℤ (𝓞 L)) = span {(2:𝓞 L)} := by simp [J,Ideal.map_span]
  have hn : J.map (algebraMap ℤ (𝓞 L)) ≠ ⊥ := by rw [hm]; simp
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity J P hn
  rw [hm,q8Literal_two_ramificationIdx_eq_two P h2] at he
  refine ⟨v,by rw [hPv]; exact he.symm,?_⟩
  have hval := quaternionDyadic_order v (by rw [hPv]; exact h2) (2:𝓞 L) two_ne_zero
  rw [hPv,← he] at hval
  norm_num at hval ⊢
  exact hval

end Quaternion
#print axioms weightedPrimeOrder_eq
#print axioms weightedPrimeOrder_eq_multiplicity_iff
#print axioms quaternionDyadic_order
#print axioms quaternionDyadic_nonintegral_reading
end GaloisForLFunctions.KodairaParshinAbc
