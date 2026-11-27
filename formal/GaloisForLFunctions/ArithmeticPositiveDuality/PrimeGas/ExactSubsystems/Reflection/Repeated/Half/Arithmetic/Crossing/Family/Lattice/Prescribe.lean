import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Synthesis
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Certificate
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Gibbs

/-! # Prescribing algebraic blind coordinates by quantum composition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice

open Finset Real Polynomial Set

private theorem coordinate_cosh (t : ℝ) : coordinate t=2*cosh t := by
  rw [coordinate,cosh_eq]; ring

theorem base_pos {t : ℝ} (ht : 0 < t) : 0 < base t := by
  apply mul_pos (sub_pos.mpr (exp_lt_exp.mpr (neg_lt_self ht)))
  rw [coordinate_cosh]
  linarith only [(one_lt_cosh.mpr ht.ne')]

/-- Positive probe coordinates cannot all be roots of a nonzero polynomial. -/
theorem exists_detecting_coordinate {Q : ℤ[X]} (hq : Q ≠ 0) :
    ∃ u : ℝ, 0 < u ∧ aeval (coordinate u) Q ≠ 0 := by
  let p := Q.map (algebraMap ℤ ℝ)
  have nz : p ≠ 0 := by
    intro zero
    apply hq
    apply Polynomial.map_injective (f := algebraMap ℤ ℝ) (Int.cast_injective (α := ℝ))
    simpa only [Polynomial.map_zero] using zero
  let nodes (n : ℕ) := coordinate ((n : ℝ)+1)
  have mono : StrictMono nodes := by
    intro i j lt
    have hi : (0 : ℝ) ≤ (i : ℝ)+1 := by positivity
    have hj : (0 : ℝ) ≤ (j : ℝ)+1 := by positivity
    change coordinate ((i : ℝ)+1) < coordinate ((j : ℝ)+1)
    rw [coordinate_cosh,coordinate_cosh]
    apply mul_lt_mul_of_pos_left _ zero_lt_two
    simpa only [cosh_lt_cosh,abs_of_nonneg hi,abs_of_nonneg hj,add_lt_add_iff_right,Nat.cast_lt] using lt
  by_contra! all
  apply (Set.infinite_range_of_injective mono.injective).not_finite
  apply (Polynomial.finite_setOf_isRoot nz).subset
  rintro _ ⟨n,rfl⟩
  change (Q.map (algebraMap ℤ ℝ)).eval (nodes n)=0
  rw [Polynomial.eval_map]
  exact all ((n : ℝ)+1) (by positivity)

/-- Shifting by a common integer converts the synthesized centered modes into
ordinary nonnegative occupations without changing their centered trace. -/
private theorem shift_levels {n : ℕ} (k : Fin n → ℤ) (mean : ∑ i, k i=0) :
    ∃ a : Fin n → ℕ, centered (levels a)=fun i => (k i : ℝ) := by
  let m : ℕ := ∑ i, (k i).natAbs
  let a (i : Fin n) := ((m : ℤ)+k i).toNat
  have lift (i : Fin n) : (a i : ℤ)=(m : ℤ)+k i := by
    have le : (k i).natAbs ≤ m := single_le_sum (f := fun j => (k j).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
    have abs := Int.le_natAbs (a := -k i)
    rw [Int.natAbs_neg] at abs
    exact Int.toNat_of_nonneg (by omega)
  have asReal : levels a=fun i => 1*(k i : ℝ)+(m : ℝ) := by
    funext i
    have r := congrArg (fun z : ℤ => (z : ℝ)) (lift i)
    simpa only [levels,Int.cast_natCast,Int.cast_add,one_mul,add_comm] using r
  have sumzero : (∑ i, (k i : ℝ))=0 := by rw [← Int.cast_sum,mean,Int.cast_zero]
  exact ⟨a,by rw [asReal,centered_affine,centered_eq_of_sum_zero sumzero]; simp only [one_mul]⟩

/-- Exact positive zero set of a synthesized spectrum: its coordinates are the
roots of the prescribed nonzero integer polynomial on \(2\cosh t>2\). -/
theorem polynomial_spectrum (Q : ℤ[X]) (hq : Q ≠ 0) :
    ∃ (n : ℕ) (a : Fin n → ℕ), ¬Reflects (levels a) ∧
      ∀ t : ℝ, 0 < t → (agrees (levels a) t ↔ aeval (coordinate t) Q=0) := by
  obtain ⟨n,k,mean,eq⟩ := polynomial_realized Q
  obtain ⟨a,shift⟩ := shift_levels k mean
  have test (t : ℝ) (ht : 0 < t) : agrees (levels a) t ↔ aeval (coordinate t) Q=0 := by
    rw [agrees_odd,shift,← show trace k t=oddTrace (fun i => (k i : ℝ)) t from rfl,eq,mul_eq_zero]
    exact or_iff_right (base_pos ht).ne'
  obtain ⟨u,hu,detect⟩ := exists_detecting_coordinate hq
  exact ⟨n,a,fun symm => detect ((test u hu).mp (reflection_agrees symm u)),test⟩

private theorem annihilator (A : Finset ℝ) (alg : ∀ x ∈ A, IsAlgebraic ℤ x) :
    ∃ Q : ℤ[X], Q ≠ 0 ∧ ∀ x ∈ A, aeval x Q=0 := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨1,one_ne_zero,fun _ hx => (notMem_empty _ hx).elim⟩
  | insert x A hx ih =>
    obtain ⟨P,hP,zero⟩ := ih (fun y hy => alg y (mem_insert_of_mem hy))
    obtain ⟨R,hR,root⟩ := alg x (mem_insert_self _ _)
    refine ⟨R*P,mul_ne_zero hR hP,fun y hy => ?_⟩
    rw [map_mul]
    rcases mem_insert.mp hy with rfl | mem
    · rw [root,zero_mul]
    · rw [zero y mem,mul_zero]

/-- Any finite family of positive logarithms of algebraic numbers above one
can be made simultaneously blind on the same asymmetric one-frequency spectrum. -/
theorem prescribed (A : Finset ℝ) (alg : ∀ x ∈ A, 1 < x ∧ IsAlgebraic ℚ x) :
    ∃ (n : ℕ) (a : Fin n → ℕ), ¬Reflects (levels a) ∧ ∀ x ∈ A, agrees (levels a) (log x) := by
  classical
  let c (x : ℝ) := x+x⁻¹
  have changed (x : ℝ) (hx : x ∈ A) : coordinate (log x)=c x := by
    simp only [coordinate,exp_neg,exp_log (zero_lt_one.trans (alg x hx).1),c]
  obtain ⟨Q,hQ,roots⟩ := annihilator (A.image c) (by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    have h := (alg x hx).2
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr (h.add (IsAlgebraic.inv_iff.mpr h)))
  obtain ⟨n,a,asym,test⟩ := polynomial_spectrum Q hQ
  exact ⟨n,a,asym,fun x hx => (test _ (log_pos (alg x hx).1)).mpr (by
    rw [changed x hx]; exact roots _ (mem_image_of_mem c hx))⟩

#print axioms polynomial_spectrum
#print axioms prescribed

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice
