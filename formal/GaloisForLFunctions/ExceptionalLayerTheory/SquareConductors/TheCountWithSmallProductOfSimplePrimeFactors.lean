import GaloisForLFunctions.ExceptionalLayerTheory.ASquareRootBoundFromThePowerfulDivisors
import GaloisForLFunctions.RHTower.SqrtTelescopeSums

/-!
# Counting integers by their prime factors of exponent one

After taking out the primes occurring exactly once, the residual integer
is a square times a cube. Summing the square-root row count over small
values of the extracted product costs only its square root.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
open private squareCubeMajorant squareCubeMajorant_sum squareCubeMajorant_nonneg cubeScale cubeScale_sq from
  GaloisForLFunctions.ExceptionalLayerTheory.ASquareRootBoundFromThePowerfulDivisors

/-- Product of the primes which divide n exactly once. -/
def simplePrimeProduct (n : ℕ) := ∏ p ∈ n.primeFactors, if n.factorization p=1 then p else 1

theorem simplePrimeProduct_pos (n : ℕ) : 0 < simplePrimeProduct n := by
  apply prod_pos
  intro p hp
  split_ifs
  · exact (Nat.prime_of_mem_primeFactors hp).pos
  · decide

private theorem split_block (p e : ℕ) (hp : 0 < p) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ p^e=(if e=1 then p else 1)*a^2*b^3 := by
  by_cases h : e=1
  · exact ⟨1,1,by decide,by decide,by simp [h]⟩
  simp only [if_neg h,one_mul]
  by_cases he : e%2=0
  · exact ⟨p^(e/2),1,pow_pos hp _,by decide,by rw [one_pow,mul_one,←pow_mul,show e/2*2=e by omega]⟩
  exact ⟨p^((e-3)/2),p,pow_pos hp _,hp,by rw [←pow_mul,←pow_add,show (e-3)/2*2+3=e by omega]⟩

/-- The same extracted product works in the exact square-cube factorization
at every positive integer. -/
theorem simple_square_cube_factorization {n : ℕ} (hn : 0 < n) :
    ∃ a b : ℕ, n = simplePrimeProduct n*(a+1)^2*(b+1)^3 := by
  have split (S : Finset ℕ) (hS : S ⊆ n.primeFactors) :
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
        (∏ p ∈ S,p^n.factorization p) = (∏ p ∈ S,if n.factorization p=1 then p else 1)*a^2*b^3 := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1,1,by decide,by decide,by simp⟩
    | @insert p S hp ih =>
      obtain ⟨a,b,ha,hb,hs⟩ := ih ((subset_insert _ _).trans hS)
      obtain ⟨u,v,hu,hv,he⟩ := split_block p (n.factorization p)
        (Nat.prime_of_mem_primeFactors (hS (mem_insert_self ..))).pos
      exact ⟨u*a,v*b,Nat.mul_pos hu ha,Nat.mul_pos hv hb,by rw [prod_insert hp,prod_insert hp,he,hs]; ring⟩
  obtain ⟨a,b,ha,hb,h⟩ := split n.primeFactors (Subset.refl _)
  rw [←Nat.prod_primeFactors_pow_factorization hn.ne'] at h
  exact ⟨a-1,b-1,by simpa only [simplePrimeProduct,Nat.sub_add_cancel ha,Nat.sub_add_cancel hb] using h⟩

/-- Uniform count at a fixed value of the simple product. -/
theorem fixed_simple_product_count {X m : ℕ} (hm : 0 < m) :
    ((((Icc 1 X).filter (fun n => simplePrimeProduct n=m)).card:ℕ):ℝ) ≤
      12*Real.sqrt ((X/m:ℕ):ℝ) := by
  classical
  let S := (Icc 1 X).filter fun n => simplePrimeProduct n=m
  have rep (n : ℕ) (hn : n ∈ S) : ∃ q : ℕ×ℕ, n=m*(q.2+1)^2*(q.1+1)^3 := by
    obtain ⟨a,b,he⟩ := simple_square_cube_factorization (mem_Icc.mp (mem_filter.mp hn).1).1
    exact ⟨(b,a),by simpa only [(mem_filter.mp hn).2] using he⟩
  let φ (n : ℕ) := if h : n ∈ S then (rep n h).choose else (0,0)
  have eq (n : ℕ) (hn : n ∈ S) : n=m*((φ n).2+1)^2*((φ n).1+1)^3 := by
    simpa only [φ,dif_pos hn] using (rep n hn).choose_spec
  have inj : Set.InjOn φ ↑S := fun i hi j hj e =>
    (eq i hi).trans ((congrArg (fun q : ℕ×ℕ => m*(q.2+1)^2*(q.1+1)^3) e).trans (eq j hj).symm)
  let J := 1+∑ n ∈ S, ((φ n).1+(φ n).2)
  have into (n : ℕ) (hn : n ∈ S) : φ n ∈ range J ×ˢ range J := by
    have h := single_le_sum (fun i (_ : i∈S) => Nat.zero_le ((φ i).1+(φ i).2)) hn
    exact mem_product.mpr ⟨mem_range.mpr (by dsimp only [J]; omega),mem_range.mpr (by dsimp only [J]; omega)⟩
  have unit (n : ℕ) (hn : n ∈ S) : 1 ≤ squareCubeMajorant (X/m) (φ n) := by
    have small := (mem_Icc.mp (mem_filter.mp hn).1).2
    rw [eq n hn,mul_assoc] at small
    have division : ((φ n).2+1)^2*((φ n).1+1)^3 ≤ X/m :=
      (Nat.le_div_iff_mul_le hm).mpr (by rwa [mul_comm])
    change 1 ≤ min 1 _
    apply le_min le_rfl
    rw [←cubeScale_sq]
    apply (one_le_div₀ (by positivity)).mpr
    exact_mod_cast division
  have bound := _root_.RHTower.GuthMaynard.sum_le_sum_of_injOn (F := fun _ => (1:ℝ)) inj into
    (fun q _ => squareCubeMajorant_nonneg (X/m) q) unit
  have cap : (∑ q ∈ range J ×ˢ range J,squareCubeMajorant (X/m) q) ≤ 12*Real.sqrt ((X/m:ℕ):ℝ) := by
    rcases Nat.eq_zero_or_pos (X/m) with hz | hq
    · simp [hz,squareCubeMajorant,cubeScale]
    · exact squareCubeMajorant_sum hq J
  simpa only [sum_const,nsmul_eq_mul,mul_one] using bound.trans cap

/-- At most 24√(XY) integers through X have product of their exponent-one
prime factors at most Y. The bound includes the powerful integers at Y=1. -/
theorem small_simple_product_count (X Y : ℕ) :
    ((((Icc 1 X).filter (fun n => simplePrimeProduct n ≤ Y)).card:ℕ):ℝ) ≤
      24*Real.sqrt X*Real.sqrt Y := by
  let S := (Icc 1 X).filter fun n => simplePrimeProduct n ≤ Y
  let F := fun m => (Icc 1 X).filter fun n => simplePrimeProduct n=m
  have union : S = (Icc 1 Y).biUnion F := by
    ext n
    simp only [S,F,mem_biUnion,mem_filter]
    exact ⟨fun h => ⟨_,mem_Icc.mpr ⟨simplePrimeProduct_pos n,h.2⟩,h.1,rfl⟩,
      fun ⟨_,hm,hn,eq⟩ => ⟨hn,eq.le.trans (mem_Icc.mp hm).2⟩⟩
  change (S.card:ℝ) ≤ _
  rw [union]
  apply (Nat.cast_le.mpr (card_biUnion_le ..)).trans
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ m ∈ Icc 1 Y, (12*Real.sqrt X)*(1/Real.sqrt m) := by
      apply sum_le_sum
      intro m hm
      have mp := (mem_Icc.mp hm).1
      have div : ((X/m:ℕ):ℝ) ≤ (X:ℝ)/m :=
        (le_div_iff₀ (Nat.cast_pos.mpr mp)).mpr (by exact_mod_cast Nat.div_mul_le_self X m)
      apply (fixed_simple_product_count (X:=X) mp).trans
      apply (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt div) (by norm_num : (0:ℝ)≤12)).trans_eq
      rw [Real.sqrt_div (Nat.cast_nonneg _)]
      ring
    _ ≤ _ := by
      rw [←mul_sum]
      exact (mul_le_mul_of_nonneg_left (_root_.RHTower.sum_inv_sqrt_le Y) (by positivity)).trans_eq (by ring)

#print axioms simple_square_cube_factorization
#print axioms fixed_simple_product_count
#print axioms small_simple_product_count
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
