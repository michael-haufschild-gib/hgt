import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.Reciprocal
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Descent.GapInvariant

/-! # Arithmetic restrictions on additional mutual triangle readings -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Set

private theorem real_gap_iff (a c : ℕ+) (s : ℝ) :
    IsAlgebraic ℚ (gapExp (delta a c) s) ↔ IsAlgebraic ℚ (relativePower s a c) := by
  have eq : gapExp (delta a c) s=(relativePower s a c : ℂ) := by rw [relativePower_exp]; rfl
  rw [eq]
  exact isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℚ ℝ ℂ) Complex.ofReal_injective

/-- Any mutual reading beyond the two real balances forces algebraicity of
both specified source gaps and transcendence of its ratio to the source. -/
theorem mutual_triangle_candidates (a b c : ℕ+) (ab : energy a<energy b) (bc : energy b<energy c)
    {t : ℝ} (ht : 0<t) (rel : shellPower t a+shellPower t b=shellPower t c) :
    ∃ w : ℝ, 0<w ∧ (∀ v, shellPower (-v) b+shellPower (-v) c=shellPower (-v) a ↔ v=w) ∧
      (∀ u ∈ mutualOrders t, u ≠ t → u ≠ w →
        algebraicPair (delta a c) (delta b c) t ∧ ¬IsAlgebraic ℚ (u/t)) ∧
      (¬algebraicPair (delta a c) (delta b c) t → mutualOrders t ⊆ {t,w}) := by
  obtain ⟨w,wp,reverse,_,all⟩ := unit_triangle_candidates a b c ab bc ht rel
  have extra (u : ℝ) (hit : u ∈ mutualOrders t) (diff : u ≠ t) (other : u ≠ w) :
      algebraicPair (delta a c) (delta b c) t ∧ ¬IsAlgebraic ℚ (u/t) := by
    have pair := ((all u hit.1).resolve_left diff).resolve_left other
    have back (d : ℕ+) (alg : IsAlgebraic ℚ (gapExp (delta d c) u)) :=
      (mutual_gap_iff ht hit d c).mpr ((real_gap_iff d c u).mp alg)
    have ac := back a pair.1
    have bc' := back b pair.2
    refine ⟨⟨(real_gap_iff a c t).mpr ac,(real_gap_iff b c t).mpr bc'⟩,?_⟩
    intro alg
    have ca : IsAlgebraic ℚ (relativePower t c a) := by
      simpa only [relativePower,inv_div] using ac.inv
    have one := (algebraic_gap_multiplier_iff c a (ab.trans bc) ht (div_pos hit.1.1 ht) ca alg).mp
      (by simpa only [div_mul_cancel₀ _ ht.ne'] using hit.1)
    exact diff ((div_eq_one_iff_eq ht.ne').mp one)
  refine ⟨w,wp,reverse,extra,?_⟩
  intro no u hit
  by_cases same : u=t
  · exact Or.inl same
  · have eq : u=w := by by_contra other; exact no (extra u hit same other).1
    exact Or.inr eq

#print axioms mutual_triangle_candidates

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
