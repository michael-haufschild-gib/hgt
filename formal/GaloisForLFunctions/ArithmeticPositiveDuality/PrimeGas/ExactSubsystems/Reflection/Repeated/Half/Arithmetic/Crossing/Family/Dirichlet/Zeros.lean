import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Certificate
import GaloisForLFunctions.HTGeometry.ExponentialPolynomialZeroBound

/-! # Finitely many real zeros of a nonzero prime polynomial along the shell powers -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Finset Real MvPolynomial Set
open GaloisForLFunctions.HTGeometry.ExpZeroBound (expPoly card_lt_of_expPoly_eq_zero')

private theorem frequency_injective : Function.Injective (fun v : Exponent => energy (label v)) := by
  intro a b h
  apply label.injective
  apply PNat.coe_injective
  have eq := congrArg exp h
  simp only [energy,exp_log (Nat.cast_pos.mpr (label a).pos),exp_log (Nat.cast_pos.mpr (label b).pos)] at eq
  exact_mod_cast eq

/-- The exponential-polynomial zero bound applies after unique factorization
separates the logarithms of all monomials in the support. -/
theorem finite_roots {P : PolynomialRing} (hp : P ≠ 0) :
    {t : ℝ | value t P=0}.Finite := by
  classical
  let e := P.support.equivFin.symm
  let v (i : Fin P.support.card) := (e i).val
  let E i := energy (label (v i))
  let C (i : Fin P.support.card) := Polynomial.C ((coeff (v i) P : ℤ) : ℝ)
  have inj : Function.Injective E := frequency_injective.comp (Subtype.val_injective.comp e.injective)
  obtain ⟨w,hw⟩ := support_nonempty.mpr hp
  have some : ∃ i, C i ≠ 0 := by
    refine ⟨e.symm ⟨w,hw⟩,?_⟩
    have nz : coeff w P ≠ 0 := mem_support_iff.mp hw
    simpa only [C,v,Equiv.apply_symm_apply,ne_eq,Polynomial.C_eq_zero,Int.cast_eq_zero] using nz
  have expansion (t : ℝ) : expPoly E C t=value t P := by
    let g (w : Exponent) := ((coeff w P : ℤ) : ℝ)*shellPower t (label w)
    rw [value_sum]
    calc expPoly E C t = ∑ i, g (v i) := by
           simp only [expPoly,C,E,g,shellPower_exp,Polynomial.eval_C,mul_comm t]
         _ = ∑ w : P.support, g w.val := Equiv.sum_comp e (fun w : P.support => g w.val)
         _ = _ := sum_attach P.support g
  by_contra infinite
  obtain ⟨S,sub,size⟩ := Set.Infinite.exists_subset_card_eq infinite (∑ i, ((C i).natDegree+1))
  exact (card_lt_of_expPoly_eq_zero' E C inj some S (fun t ht => (expansion t).trans (sub ht))).ne size

/-- One positive order avoids the real roots in both directions. -/
theorem detecting_order {P : PolynomialRing} (hp : P ≠ 0) :
    ∃ t : ℝ, 0<t ∧ value t P ≠ 0 ∧ value (-t) P ≠ 0 := by
  let Z := {t : ℝ | value t P=0}
  have finite : Z.Finite := finite_roots hp
  have neg : (Neg.neg ⁻¹' Z).Finite := finite.preimage neg_injective.injOn
  obtain ⟨t,ht,good⟩ := Set.Infinite.exists_notMem_finset (Set.Ioi_infinite (0 : ℝ))
    (finite.union neg).toFinset
  have avoid : t ∉ Z ∪ (Neg.neg ⁻¹' Z) := fun h => good ((finite.union neg).mem_toFinset.mpr h)
  exact ⟨t,ht,fun h => avoid (Or.inl h),fun h => avoid (Or.inr h)⟩

#print axioms finite_roots
#print axioms detecting_order

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
