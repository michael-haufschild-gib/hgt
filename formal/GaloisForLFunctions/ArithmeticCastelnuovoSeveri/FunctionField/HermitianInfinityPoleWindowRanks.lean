import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianInfinityGapTriangle
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Complete bounded pole spaces on the geometric Hermitian normalization

Distinct nonzero valuation levels give independent vectors over trivially
valued constants. The reduced radical monomials span the actual infinity
window, so its dimension counts the achieved pole orders through the cutoff.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p^(s+1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "φ" => algebraMap E H
local notation "Xₕ" => algebraMap E[X] H (X : E[X])
local notation "z" => hermitianExtensionRadicalCoordinate p s E
local notation "V" => hermitianGeometricInfinityValuation p s

/-- Functions of distinct exact valuations are independent over a trivially valued constant field. -/
theorem linearIndependent_of_distinct_valuation {k L ι : Type*} [Field k] [Field L] [Algebra k L]
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (hconst : ∀ c : k, c ≠ 0 → v (algebraMap k L c) = 1)
    (f : ι → L) (hsep : Function.Injective (fun i => v (f i))) (hf : ∀ i, f i ≠ 0) :
    LinearIndependent k f := by
  classical
  rw [linearIndependent_iff']
  intro t a h i hi
  have hc (j : ι) (haj : a j ≠ 0) : v (a j • f j) = v (f j) := by
    rw [Algebra.smul_def,map_mul,hconst _ haj,one_mul]
  have hterm := valuation_terms_le_of_separated v t (fun j => a j • f j) (by
    intro j _ k _ hjk he
    by_cases hj : a j=0
    · rw [hj,zero_smul,map_zero]
    by_cases hk : a k=0
    · rwa [hk,zero_smul,map_zero] at he
    exact (hjk (hsep ((hc j hj).symm.trans (he.trans (hc k hk))))).elim) 0 (by rw [h,map_zero]) i hi
  by_contra hne
  rw [hc i hne] at hterm
  exact ((map_ne_zero v).2 (hf i)) (le_antisymm hterm zero_le)

/-- Functions in the affine normalization with pole of order at most m at infinity. -/
def hermitianInfinityPoleWindow (m : ℕ) : Submodule E H where
  carrier := {f | IsIntegral E[X] f ∧ V f ≤ WithZero.exp (m:ℤ)}
  zero_mem' := ⟨isIntegral_zero,by rw [map_zero]; exact zero_le⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, (V).map_add _ _ |>.trans (max_le hf.2 hg.2)⟩
  smul_mem' := by
    intro c f hf
    rw [Algebra.smul_def]
    have hc : IsIntegral E[X] (φ c) := by
      rw [IsScalarTower.algebraMap_apply E E[X] H]
      exact isIntegral_algebraMap
    refine ⟨hc.mul hf.1,?_⟩
    by_cases he : c=0
    · rw [he,map_zero,zero_mul,map_zero]; exact zero_le
    · rw [map_mul,hermitianGeometricInfinityValuation_constant p s c he,one_mul]; exact hf.2

/-- Bounded weight indices in the reduced basis, with radical exponent at most Q. -/
abbrev HermitianReducedPoleIndex (m : ℕ) :=
  {t : ℕ × Fin (Q+1) // (Q+1)*t.1+Q*t.2.val ≤ m}

/-- Infinity pole order of a reduced monomial. -/
def hermitianReducedPoleWeight {m : ℕ} (t : HermitianReducedPoleIndex p s m) : ℕ := (Q+1)*t.val.1+Q*t.val.2.val
/-- The corresponding function in the geometric Hermitian field. -/
def hermitianReducedPoleMonomial {m : ℕ} (t : HermitianReducedPoleIndex p s m) : H := Xₕ^t.val.1*z^t.val.2.val

private theorem weight_injective (m : ℕ) : Function.Injective (hermitianReducedPoleWeight p s (m:=m)) := by
  have h := kummerInfinity_primePower_poleDegree_coprime p s s 1
  rw [kummerInfinity_primePower_poleDegree,pow_one] at h
  exact fun _ _ he => Subtype.ext (coprime_monomialWeight_injective (Nat.succ_pos Q) h he)

private theorem monomial_value {m : ℕ} (t : HermitianReducedPoleIndex p s m) :
    V (hermitianReducedPoleMonomial p s t) = WithZero.exp (hermitianReducedPoleWeight p s t : ℤ) := by
  have h := hermitianGeometricInfinityValuation_polynomialMonomial p s (X^t.val.1 : E[X])
    (pow_ne_zero _ X_ne_zero) t.val.2
  simpa only [hermitianReducedPoleMonomial,hermitianReducedPoleWeight,map_pow,natDegree_X_pow] using h

/-- Reduced monomials of bounded weight are linearly independent over the actual constants. -/
theorem hermitianPoleMonomials_independent (m : ℕ) :
    LinearIndependent E (hermitianReducedPoleMonomial p s (m:=m)) := by
  apply linearIndependent_of_distinct_valuation V (hermitianGeometricInfinityValuation_constant p s)
  · intro a b he
    change V (hermitianReducedPoleMonomial p s a) = V (hermitianReducedPoleMonomial p s b) at he
    rw [monomial_value,monomial_value] at he
    exact weight_injective p s m (Nat.cast_injective (WithZero.exp_injective he))
  · intro a h
    have he := monomial_value p s a
    rw [h,map_zero] at he
    exact WithZero.exp_ne_zero he.symm

/-- The geometric pole window equals the span of its reduced monomials. -/
theorem hermitianInfinityPoleWindow_span (m : ℕ) :
    hermitianInfinityPoleWindow p s m = Submodule.span E (Set.range (hermitianReducedPoleMonomial p s (m:=m))) := by
  apply le_antisymm
  · intro f hf
    obtain ⟨a,ha,hb⟩ := hermitianGeometric_exists_bounded_polynomial_expansion p s f m
      ((hermitianGeometric_integral_iff_finite_valuations p s f).1 hf.1) hf.2
    rw [ha,hermitianGeometricPolynomialExpansion]
    apply Submodule.sum_mem
    intro i _
    let U := Submodule.span E (Set.range (hermitianReducedPoleMonomial p s (m:=m)))
    have he : algebraMap E[X] H (a i) * z^i.val =
        ∑ d ∈ (a i).support, (a i).coeff d • (Xₕ^d*z^i.val) := by
      conv_lhs => rw [(a i).as_sum_support_C_mul_X_pow,map_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul,map_pow,Algebra.smul_def,← mul_assoc]
      rfl
    rw [he]
    apply U.sum_mem
    intro d hd
    have hn : a i ≠ 0 := by intro h; rw [h,support_zero] at hd; exact Finset.notMem_empty d hd
    have hle := Nat.add_le_add_right (Nat.mul_le_mul_left (Q+1) ((a i).le_natDegree_of_mem_supp d hd)) (Q*i.val)
    exact U.smul_mem _ (Submodule.subset_span ⟨⟨(d,i),hle.trans (hb i hn)⟩,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,rfl⟩
    have hz : IsIntegral E[X] z := (hermitianGeometricIntegralRadical p s).property
    exact ⟨(show IsIntegral E[X] Xₕ from isIntegral_algebraMap).pow _ |>.mul (hz.pow _), by
      rw [monomial_value,WithZero.exp_le_exp]; exact_mod_cast t.property⟩

instance hermitianInfinityPoleWindow_finite (m : ℕ) : Module.Finite E (hermitianInfinityPoleWindow p s m) := by
  let e (t : HermitianReducedPoleIndex p s m) : Fin (m+1) := ⟨hermitianReducedPoleWeight p s t,
    Nat.lt_succ_of_le t.property⟩
  letI : Finite (HermitianReducedPoleIndex p s m) := Finite.of_injective e
    (fun a b h => weight_injective p s m (congrArg Fin.val h))
  rw [hermitianInfinityPoleWindow_span]
  exact Module.Finite.span_of_finite E (Set.finite_range _)

/-- The dimension of the complete window equals the number of nongaps through m. -/
theorem hermitianInfinityPoleWindow_dimension (m : ℕ) :
    Module.finrank E (hermitianInfinityPoleWindow p s m) =
      Nat.card {d : Fin (m+1) // d.val ∈ hermitianInfinityOrders p s} := by
  let e (t : HermitianReducedPoleIndex p s m) : {d : Fin (m+1) // d.val ∈ hermitianInfinityOrders p s} :=
    ⟨⟨hermitianReducedPoleWeight p s t,Nat.lt_succ_of_le t.property⟩,(hermitianInfinityOrders_iff p s _).2
      ⟨t.val.2.val,t.val.1,add_comm _ _⟩⟩
  have hi : Function.Injective e := fun a b h => weight_injective p s m
    (congrArg (fun d : {d : Fin (m+1) // d.val ∈ hermitianInfinityOrders p s} => d.val.val) h)
  have hs : Function.Surjective e := by
    intro d
    obtain ⟨i,j,he⟩ := hermitianInfinityOrders_reduced p s d.val.val d.property
    exact ⟨⟨(j,i),by rw [← he]; exact Nat.le_of_lt_succ d.val.isLt⟩,Subtype.ext (Fin.ext he.symm)⟩
  let ep := Equiv.ofBijective e ⟨hi,hs⟩
  letI : Finite (HermitianReducedPoleIndex p s m) := Finite.of_injective _ hi
  letI : Fintype (HermitianReducedPoleIndex p s m) := Fintype.ofFinite _
  rw [hermitianInfinityPoleWindow_span,finrank_span_eq_card (hermitianPoleMonomials_independent p s m),
    ← Nat.card_eq_fintype_card,Nat.card_congr ep]

#print axioms hermitianInfinityPoleWindow_finite
#print axioms linearIndependent_of_distinct_valuation
#print axioms hermitianPoleMonomials_independent
#print axioms hermitianInfinityPoleWindow_span
#print axioms hermitianInfinityPoleWindow_dimension
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
