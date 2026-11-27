import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.Commensurate
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.FiniteOrders
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.ShellRelation
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.StabilizedSpectra

/-! # Stabilization of every resonance with a three-shell relation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Real Set

/-- For three distinct shells an integral relation already makes the union
of normalized forced targets finite at every rational dilation. The reference
shell is the smallest of the three. -/
theorem three_shell_finite (a b c : ℕ+) (ac : energy c<energy a) (bc : energy c<energy b)
    (ab : energy a ≠ energy b) (A B C : ℤ) (ha : A ≠ 0) (hb : B ≠ 0) (hc : C ≠ 0)
    {t : ℝ} (ht : 0<t) (rel : shellRelation A B C a b c t) : (accumulated t).Finite := by
  let E := delta a c
  let F := delta b c
  let α := (A : ℚ)/C
  let β := (B : ℚ)/C
  have ep : 0<E := sub_pos.mpr ac
  have fp : 0<F := sub_pos.mpr bc
  have different : E ≠ F := fun h => ab (sub_left_inj.mp h)
  have a0 : α ≠ 0 := div_ne_zero (Int.cast_ne_zero.mpr ha) (Int.cast_ne_zero.mpr hc)
  have b0 : β ≠ 0 := div_ne_zero (Int.cast_ne_zero.mpr hb) (Int.cast_ne_zero.mpr hc)
  by_cases ind : independentGaps E F
  · have finite := independent_triangle_finite ep fp different ind
      ⟨gapExp_one_algebraic a c,gapExp_one_algebraic b c⟩ α β a0 b0
    let Z := triangleOrders E F α β
    have neg : (Neg.neg ⁻¹' Z).Finite := finite.preimage neg_injective.injOn
    apply (finite.union neg).subset
    rintro u ⟨hu,m,hm,hit⟩
    have inside (v : ℝ) (s : TorsionSpecialization m t v) : v ∈ Z := by
      obtain ⟨U,V,up,vp,eq⟩ := twisted_relation hm hc rel s
      exact ⟨U,V,m,hm,up,vp,eq⟩
    rcases (scaled_forcing_iff ht hu hm).mp hit with plus | minus
    · exact Or.inl (inside u plus)
    · exact Or.inr (inside (-u) minus)
  · have alg := commensurate_coordinate ep fp ind α β t (normalized_source hc rel)
    apply algebraic_gap_finite a c ac ht
    rw [relativePower_exp]
    exact alg

theorem three_shell_stabilization (a b c : ℕ+) (ac : energy c<energy a) (bc : energy c<energy b)
    (ab : energy a ≠ energy b) (A B C : ℤ) (ha : A ≠ 0) (hb : B ≠ 0) (hc : C ≠ 0)
    {t : ℝ} (ht : 0<t) (rel : shellRelation A B C a b c t) :
    ∃ M : ℕ, 0<M ∧ ∀ k : ℕ, 0<k → ∃ S : Set ℝ, Attainable S ∧ t*↑(M*k) ∈ S ∧
      ∀ u : ℝ, 0<u → (u*↑(M*k) ∈ S ↔ u ∈ accumulated t) :=
  (finite_iff_stabilized ht).mp (three_shell_finite a b c ac bc ab A B C ha hb hc ht rel)

#print axioms three_shell_finite
#print axioms three_shell_stabilization

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
