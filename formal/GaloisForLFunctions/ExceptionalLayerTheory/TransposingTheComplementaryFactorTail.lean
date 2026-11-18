import GaloisForLFunctions.ExceptionalLayerTheory.AveragingThePrimeErrorAtAComplementaryBoundary
import GaloisForLFunctions.ExceptionalLayerTheory.CancellationAcrossTheSquareRootProductInterval
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorDilationChannels

/-!
# The centered boundary in a transposed complementary tail

Differencing the quotient weight replaces the tail in the complementary
factor by a difference of two centered floor primitives. The lower
boundary is independent of the new factor.
-/

noncomputable section
open Finset RHTower ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem sum_backward_difference (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ v ∈ Icc (a+1) b, (f v-f (v-1)))=f b-f a := by
  induction b, hab using Nat.le_induction with
  | base => rw [Icc_eq_empty (by omega),sum_empty,sub_self]
  | succ b hab ih =>
    rw [sum_Icc_succ_top (by omega),ih,Nat.add_sub_cancel]
    ring

/-- For a positive quotient the outer jumps recover its weight, including
the contribution at the first integer. -/
theorem outerJump_sum_at_positive (R : ℕ) {t : ℕ} (ht : 1≤t) :
    ∑ j ∈ Icc 1 t, outerJump R j = centeredPrimeWeight R t := by
  let f (j : ℕ) := if j=0 then (0 : ℝ) else centeredPrimeWeight R j
  change (∑ j ∈ Icc 1 t, (f j-f (j-1)))=_
  rw [sum_backward_difference f (Nat.zero_le t)]
  simp [f,Nat.ne_of_gt ht]

/-- Above a positive lower limit the constants in the two inner
primitives cancel. -/
theorem innerJump_sum_between {a b : ℕ} (D : ℕ) (ha : 1≤a) (hab : a≤b) :
    ∑ v ∈ Icc (a+1) b, innerJump D v = factorialBoundary (D+1) b-factorialBoundary (D+1) a := by
  let f (v : ℕ) := if v=0 then (0 : ℝ) else 1-factorialPrefix (D+1) v
  change (∑ v ∈ Icc (a+1) b, (f v-f (v-1)))=_
  rw [sum_backward_difference f hab]
  simp only [f,if_neg (Nat.ne_of_gt ha),if_neg (Nat.ne_of_gt (ha.trans hab)),factorialBoundary]
  ring

/-- Exact hyperbola identity for every positive lower complementary cutoff. -/
theorem complementary_tail_transpose (D R T : ℕ) {a : ℕ} (ha : 1≤a) :
    (∑ v ∈ Ioc a T, innerJump D v*centeredPrimeWeight R (T/v)) =
      (∑ j ∈ Icc 1 (T/(a+1)), outerJump R j*factorialBoundary (D+1) (T/j))-
        factorialBoundary (D+1) a*∑ j ∈ Icc 1 (T/(a+1)), outerJump R j := by
  rw [show Ioc a T=Icc (a+1) T by ext n; simp only [mem_Ioc,mem_Icc]; omega]
  calc _ = ∑ v ∈ Icc (a+1) T, ∑ j ∈ Icc 1 (T/v), outerJump R j*innerJump D v := by
            apply sum_congr rfl; intro v hv
            obtain ⟨hlo,hhi⟩ := mem_Icc.mp hv
            have hq : 1≤T/v := (Nat.le_div_iff_mul_le (by omega : 0<v)).mpr (by simpa only [one_mul] using hhi)
            rw [←sum_mul,outerJump_sum_at_positive R hq,mul_comm]
       _ = ∑ j ∈ Icc 1 (T/(a+1)), ∑ v ∈ Icc (a+1) (T/j), outerJump R j*innerJump D v :=
            sum_hyperbola_tail_swap_real T (a+1) _ (Nat.succ_pos a)
       _ = _ := by
            rw [mul_sum,←sum_sub_distrib]
            apply sum_congr rfl; intro j hj
            obtain ⟨hj₁,hhi⟩ := mem_Icc.mp hj
            have hmul := (Nat.le_div_iff_mul_le (Nat.succ_pos a)).mp hhi
            have hq : a+1≤T/j := (Nat.le_div_iff_mul_le hj₁).mpr (by rwa [Nat.mul_comm] at hmul)
            rw [←mul_sum,innerJump_sum_between D ha ((Nat.le_succ a).trans hq)]
            ring

/-- Mertens' first theorem sums a reciprocal-prime majorant uniformly in
the lower prime threshold. -/
theorem ordinaryFactorTail_reciprocal {F X : ℕ} (hx : 1≤X) {f : ℕ → ℝ} {C : ℝ} (hC : 0≤C)
    (hf : ∀ p ∈ (Ioc F X).filter Nat.Prime, |f p|≤C/p) :
    |ordinaryFactorTail F X f| ≤ C*((Real.log 4+4)*(1+Real.log X)) := by
  let S := (Ioc F X).filter Nat.Prime
  have hs : S ⊆ Icc 1 X := fun p hp =>
    mem_Icc.mpr ⟨(mem_filter.mp hp).2.pos,(mem_Ioc.mp (mem_filter.mp hp).1).2⟩
  have hm : (∑ p ∈ S, vonMangoldt p/p) ≤ (Real.log 4+4)*(1+Real.log X) := by
    apply (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))).trans
    have he : 1 ≤ Real.log 4+4 := by linarith only [Real.log_nonneg (by norm_num : (1 : ℝ)≤4)]
    have h := mul_le_mul_of_nonneg_right he (Real.log_natCast_nonneg X)
    linarith only [(abs_le.mp (Mertens.mertens_first X hx)).2,h]
  unfold ordinaryFactorTail
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ p ∈ S, C*(vonMangoldt p/p) := by
            apply sum_le_sum; intro p hp
            rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
            exact (mul_le_mul_of_nonneg_left (hf p hp) vonMangoldt_nonneg).trans_eq (by ring)
       _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left hm hC

/-- Differenced quotient weights have uniformly bounded individual jumps. -/
theorem outerJump_uniform :
    ∃ K : ℝ, 0≤K ∧ ∀ {R : ℕ}, 1≤R → ∀ j, |outerJump R j|≤K*R := by
  obtain ⟨K,hK,h⟩ := centeredPrimeWeight_uniform
  refine ⟨2*K,by positivity,?_⟩
  intro R hR j
  let f (i : ℕ) := if i=0 then (0 : ℝ) else centeredPrimeWeight R i
  have hf (i : ℕ) : |f i|≤K*R := by
    by_cases hi : i=0
    · simp only [f,if_pos hi,abs_zero]; positivity
    · simpa only [f,if_neg hi] using h hR i
  change |f j-f (j-1)|≤_
  exact (abs_sub _ _).trans ((add_le_add (hf j) (hf (j-1))).trans_eq (by ring))

/-- Averaging the actual prime row of outer jumps gives square-root
cost for its lower boundary at every starting point. -/
theorem averaged_ordinary_complementary_boundary {X D F A : ℕ} (hx : 1≤X) (hD : 1≤D)
    (β : ℕ → ℝ) {M : ℝ} (hM : 0≤M) (hβ : ∀ j, |β j|≤M) :
    let S := ⌊Real.sqrt X/(A+1 : ℕ)⌋₊+1
    |(∑ a ∈ Ico A (A+S), ordinaryFactorTail F X (fun p =>
      factorialBoundary D a*∑ j ∈ Icc 1 (X/p/(a+1)), β j))/(S : ℝ)| ≤
      mass D*((D : ℝ)/4)*M*Real.sqrt X*((Real.log 4+4)*(1+Real.log X)) := by
  intro S
  let H := mass D*((D : ℝ)/4)
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass hD 0)
  have hH : 0≤H := by dsimp [H]; positivity
  have hS : (0 : ℝ)<S := by exact_mod_cast (Nat.succ_pos _ : 0<S)
  have ha : (0 : ℝ)<(A+1 : ℕ) := by positivity
  have hscale : Real.sqrt X/(A+1 : ℕ)≤(S : ℝ) := by
    dsimp only [S]; push_cast; exact (Nat.lt_floor_add_one _).le
  have hz : (X : ℝ)/(A+1 : ℕ)≤Real.sqrt X*S := by
    apply (div_le_iff₀ ha).mpr
    exact (Real.mul_self_sqrt (Nat.cast_nonneg X)).symm.le.trans
      ((mul_le_mul_of_nonneg_left ((div_le_iff₀ ha).mp hscale) (Real.sqrt_nonneg _)).trans_eq (by ring))
  let f (p : ℕ) := ∑ a ∈ Ico A (A+S), factorialBoundary D a*∑ j ∈ Icc 1 (X/p/(a+1)), β j
  have hf (p : ℕ) (_hp : p ∈ (Ioc F X).filter Nat.Prime) :
      |f p|≤(H*M*(Real.sqrt X*S))/p := by
    apply (factorialBoundary_quotient_prefix hD (X/p) A (A+S) β).trans
    let U := X/p/(A+1)
    have hj : (∑ j ∈ Icc 1 U, |β j|) ≤ (U : ℝ)*M := by
      apply (sum_le_sum (fun j (_ : j ∈ Icc 1 U) => hβ j)).trans_eq
      rw [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
    have hu : (U : ℝ)≤(Real.sqrt X*S)/p := by
      dsimp only [U]
      rw [Nat.div_div_eq_div_mul,Nat.mul_comm p,←Nat.div_div_eq_div_mul]
      exact Nat.cast_div_le.trans (div_le_div_of_nonneg_right (Nat.cast_div_le.trans hz) (Nat.cast_nonneg p))
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu hM) hH
    exact (mul_le_mul_of_nonneg_left hj hH).trans (h.trans_eq (by ring))
  have heq : (∑ a ∈ Ico A (A+S), ordinaryFactorTail F X (fun p =>
      factorialBoundary D a*∑ j ∈ Icc 1 (X/p/(a+1)), β j))=ordinaryFactorTail F X f := by
    unfold ordinaryFactorTail
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => (mul_sum ..).symm
  rw [heq,abs_div,abs_of_nonneg hS.le]
  apply (div_le_iff₀ hS).mpr
  exact (ordinaryFactorTail_reciprocal hx (by positivity) hf).trans_eq (by dsimp [H]; ring)

#print axioms averaged_ordinary_complementary_boundary
#print axioms complementary_tail_transpose
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
