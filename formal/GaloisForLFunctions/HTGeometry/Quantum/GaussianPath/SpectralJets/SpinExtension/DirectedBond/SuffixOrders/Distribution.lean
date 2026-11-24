import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.SuffixOrders.Patterns

/-! # Order distribution of independent directed spectral derivatives -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

private def wordSum (n : ℕ) (z : ℕ) := ∑ p : Pattern n, z^(patternWord n p).length

private theorem wordSum_step (n z : ℕ) : wordSum (n+1) z=1+(z+z^2)*wordSum n z := by
  change (∑ p : Option (Bool × Pattern n), z^(patternWord (n+1) p).length)=_
  simp only [Fintype.sum_option,Fintype.sum_prod_type,Fintype.sum_bool,patternWord,letters_length,
    List.length_nil,order,pow_add,pow_one,pow_zero,wordSum,add_mul,Finset.mul_sum]
  omega

theorem pattern_generating_function (n z : ℕ) :
    (∑ p : Pattern n, z^(patternWord n p).length)=∑ r∈Finset.range (n+1), (z+z^2)^r := by
  change wordSum n z=_
  induction n with
  | zero => change (∑ p : Unit, z^0)=_; simp
  | succ n ih =>
    rw [wordSum_step,ih,Finset.sum_range_succ' (fun r => (z+z^2)^r)]
    simp only [pow_succ,pow_zero,←Finset.sum_mul]
    ring

/-- The count by order is intrinsic to a nonsingular suffix minor. It is
independent of the Hamiltonian and of its energy and row labels. -/
theorem order_distribution {n : ℕ} {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (hcard : Fintype.card I=2^(n+1)) (j : Bool) (k : I) (w : I→List (Fin (n+1)))
    (hw : ∀ i, ∃ u, Suffix n u ∧ w i=letters j u)
    (read : List (Fin (n+1))→I→R)
    (hd : (of fun i l => if i=k then 1 else read (w i) l).det≠0) (z : ℕ) :
    (∑ i, if i=k then 0 else z^(w i).length)=z^order j*∑ r∈Finset.range (n+1), (z+z^2)^r := by
  obtain ⟨e,hk,he⟩ := enumerate_minor hcard j k w hw read hd
  let g (o : Option (Pattern n)) := o.elim 0 (fun p => z^(order j+(patternWord n p).length))
  have h (i) : (if i=k then 0 else z^(w i).length)= g (e i) := by
    by_cases hi : i=k
    · subst i; simp [hk,g]
    · obtain ⟨p,hp⟩ : ∃ p, e i=some p := by
        cases hh : e i with
        | none => exact (hi (e.injective (hh.trans hk.symm))).elim
        | some p => exact ⟨p,rfl⟩
      rw [if_neg hi,he i p hp,letters_length,hp]
      rfl
  simp only [h,Equiv.sum_comp e g,Fintype.sum_option,g,Option.elim_none,Option.elim_some,zero_add,
    pow_add,←Finset.mul_sum,pattern_generating_function]

#print axioms order_distribution
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
