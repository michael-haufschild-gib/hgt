import GaloisForLFunctions.HTGeometry.BriotBouquetTwoRootNoGo
import GaloisForLFunctions.HTGeometry.AutonomousPowerRigidity

/-!
# The Briot–Bouquet no-go

An entire solution of the autonomous equation `F' = c(F)` with `deg c ≥ 2` is constant.

Over `ℂ` the coefficient has a root, and the two cases are disjoint and exhaustive.  With two
distinct roots the solution omits both, its derivative is zero-free, and the second main theorem
forces logarithmic characteristic, hence polynomial growth, hence a degree contradiction.  With a
single root `a` the polynomial is `c = C(leadingCoeff)·(X − a)^{deg}`, and the substitution
`H = (F − a)^{deg−1}` turns the equation into a Riccati equation with no entire solution but zero.

Together with `BriotBouquetLinear`, which classifies the solutions when `deg c ≤ 1` as
`d + c·exp(a z)`, this is the full Briot–Bouquet classification for polynomial `c`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- If every root of a complex polynomial equals `a`, it is a constant times `(X − a)^{deg}`. -/
theorem eq_const_mul_pow_of_unique_root {c : ℂ[X]} (hc0 : c ≠ 0) {a : ℂ}
    (hall : ∀ b : ℂ, c.eval b = 0 → b = a) :
    c = Polynomial.C c.leadingCoeff * (Polynomial.X - Polynomial.C a) ^ c.natDegree := by
  classical
  have hsplits : c.Splits := IsAlgClosed.splits c
  have hprod := hsplits.eq_prod_roots
  have hcard : c.roots.card = c.natDegree := (Polynomial.splits_iff_card_roots).mp hsplits
  have hrep : c.roots = Multiset.replicate c.roots.card a := by
    refine Multiset.eq_replicate_card.mpr fun b hb => ?_
    exact hall b ((Polynomial.mem_roots hc0).mp hb)
  calc c = Polynomial.C c.leadingCoeff * (Multiset.map (fun x => X - C x) c.roots).prod := hprod
    _ = Polynomial.C c.leadingCoeff * (Polynomial.X - Polynomial.C a) ^ c.natDegree := by
        rw [hrep, hcard, Multiset.map_replicate, Multiset.prod_replicate]

/-- **The Briot–Bouquet no-go, all degrees at least two.**  An entire solution of `F' = c(F)` with
`deg c ≥ 2` is constant.  Over `ℂ` the coefficient has a root; either two distinct ones, and the
second main theorem applies, or exactly one, and `c` is a constant times a pure power. -/
theorem eq_const_of_deriv_eq_comp {c : ℂ[X]} {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (heq : ∀ z, deriv F z = c.eval (F z)) (hc : 2 ≤ c.natDegree) :
    ∃ b : ℂ, F = fun _ => b := by
  classical
  by_contra hnc
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
  by_cases htwo : ∃ a₁ a₂ : ℂ, a₁ ≠ a₂ ∧ c.eval a₁ = 0 ∧ c.eval a₂ = 0
  · obtain ⟨a₁, a₂, hane, hr₁, hr₂⟩ := htwo
    exact not_nonconstant_of_two_roots hF heq hc hane hr₁ hr₂ hnc
  · push Not at htwo
    have hdeg : 0 < c.degree := by
      rw [Polynomial.degree_eq_natDegree hc0]
      exact_mod_cast (by omega : 0 < c.natDegree)
    obtain ⟨a, ha⟩ := Complex.exists_root hdeg
    have haroot : c.eval a = 0 := ha
    have hall : ∀ b : ℂ, c.eval b = 0 → b = a := by
      intro b hb
      by_contra hne
      exact (htwo b a hne hb) haroot
    have hform := eq_const_mul_pow_of_unique_root hc0 hall
    have hlc : c.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hc0
    have heq' : ∀ z, deriv F z = c.leadingCoeff * (F z - a) ^ c.natDegree := by
      intro z
      rw [heq z]
      conv_lhs => rw [hform]
      simp
    exact hnc ⟨a, eq_const_of_deriv_eq_const_mul_pow hlc hc hF heq'⟩

end GaloisForLFunctions.HTGeometry
