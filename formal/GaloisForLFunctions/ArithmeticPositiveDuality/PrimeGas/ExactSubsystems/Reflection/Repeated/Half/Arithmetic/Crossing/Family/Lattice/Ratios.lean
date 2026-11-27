import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Prescribe

/-! # Exact exceptional ratios on a one-frequency occupation lattice -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice

open Finset Real Set

/-- The exceptional ratios on one frequency have an arithmetic description
independent of the spacing and of the number of copies of each energy. -/
theorem ratio_iff (r : ℝ) :
    r ∈ exceptional (fun n : ℕ => (n : ℝ)) ↔
      ∃ a b : ℝ, 1 < a ∧ 1 < b ∧ IsAlgebraic ℚ a ∧ IsAlgebraic ℚ b ∧ log a/log b=r := by
  constructor
  · intro h
    obtain ⟨p,⟨x,y⟩,⟨hx,hy⟩,ratio⟩ := mem_iUnion.mp h
    let k := p.2
    have asym : ¬Reflects (levels k) := hy.2.2
    have np : 0 < p.1 := by
      by_contra! small
      exact asym ⟨0,Equiv.refl _,fun i => (show False by have := i.isLt; omega).elim⟩
    let N : ℝ := p.1
    have pos : 0 < N := Nat.cast_pos.mpr np
    have alg (t : ℝ) (ht : agrees (levels k) t) : IsAlgebraic ℚ (exp (t/N)) := by
      apply (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp
      simpa only [Fintype.card_fin,N] using algebraic_coordinate k asym ht
    refine ⟨exp (x/N),exp (y/N),one_lt_exp_iff.mpr (div_pos hx.1 pos),one_lt_exp_iff.mpr (div_pos hy.1 pos),
      alg x hx.2.1,alg y hy.2.1,?_⟩
    rw [log_exp,log_exp,← ratio]
    change (x/N)/(y/N)=x/y
    field_simp [pos.ne',hy.1.ne']
  · rintro ⟨a,b,ha,hb,aa,ba,ratio⟩
    classical
    let A : Finset ℝ := {a,b}
    have property (x : ℝ) (hx : x ∈ A) : 1 < x ∧ IsAlgebraic ℚ x := by
      rcases mem_insert.mp hx with rfl | h
      · exact ⟨ha,aa⟩
      · obtain rfl := mem_singleton.mp h; exact ⟨hb,ba⟩
    obtain ⟨n,k,asym,hit⟩ := prescribed A property
    exact mem_iUnion.mpr ⟨⟨n,k⟩,(log a,log b),
      ⟨⟨log_pos ha,hit a (mem_insert_self _ _),asym⟩,⟨log_pos hb,hit b (mem_insert_of_mem (mem_singleton_self b)),asym⟩⟩,ratio⟩

#print axioms ratio_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice
