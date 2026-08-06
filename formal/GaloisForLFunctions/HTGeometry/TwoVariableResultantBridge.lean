import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Elimination for a system in two variables

A system of two polynomial equations in two variables is written as a pair of polynomials in the
second variable with coefficients polynomials in the first.  Their resultant lies in the ideal they
generate, so it vanishes at the first coordinate of every common zero: eliminating the second
variable turns the system into a single polynomial condition on the first.

Mathlib has the resultant and the Bézout identity for it, but not this bridge to common zeros of a
two-variable system, which is what an elimination argument actually consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

section Eval

variable {K : Type*} [CommRing K]

/-- **Evaluating a two-variable polynomial at a point.**  The outer variable is evaluated at the
second coordinate, the inner one at the first. -/
noncomputable def evalPairHom (x y : K) : (K[X])[X] →+* K :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom x) y

theorem evalPairHom_C (x y : K) (r : K[X]) :
    evalPairHom x y (Polynomial.C r) = r.eval x := by
  simp [evalPairHom]

/-- **The resultant vanishes at the first coordinate of every common zero.**  It is a combination of
the two polynomials with polynomial coefficients, and the combination evaluates to zero there. -/
theorem eval_resultant_eq_zero_of_common_zero {f g : (K[X])[X]} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (H : m ≠ 0 ∨ n ≠ 0) {x y : K}
    (hfz : evalPairHom x y f = 0) (hgz : evalPairHom x y g = 0) :
    (f.resultant g m n).eval x = 0 := by
  obtain ⟨p, q, -, -, he⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg H
  have hval := congrArg (evalPairHom x y) he
  rw [evalPairHom_C, map_add, map_mul, map_mul, hfz, hgz, zero_mul, zero_mul, add_zero] at hval
  exact hval.symm

end Eval

section Count

variable {K : Type*} [CommRing K] [IsDomain K]

/-- **A nonzero resultant bounds the number of first coordinates of common zeros.** -/
theorem card_first_coords_le {f g : (K[X])[X]} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (H : m ≠ 0 ∨ n ≠ 0)
    (hres : f.resultant g m n ≠ 0) (s : Finset K)
    (hs : ∀ x ∈ s, ∃ y : K, evalPairHom x y f = 0 ∧ evalPairHom x y g = 0) :
    s.card ≤ (f.resultant g m n).natDegree := by
  classical
  have hsub : s ⊆ (f.resultant g m n).roots.toFinset := by
    intro x hx
    obtain ⟨y, hfy, hgy⟩ := hs x hx
    exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots hres).2
      (eval_resultant_eq_zero_of_common_zero hf hg H hfy hgy))
  calc s.card ≤ (f.resultant g m n).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (f.resultant g m n).roots := Multiset.toFinset_card_le _
    _ ≤ (f.resultant g m n).natDegree := Polynomial.card_roots' _

/-- **The first coordinates of the common zeros of a system with nonzero resultant are finite.** -/
theorem finite_first_coords {f g : (K[X])[X]} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (H : m ≠ 0 ∨ n ≠ 0)
    (hres : f.resultant g m n ≠ 0) :
    {x : K | ∃ y : K, evalPairHom x y f = 0 ∧ evalPairHom x y g = 0}.Finite := by
  classical
  refine Set.Finite.subset ((f.resultant g m n).roots.toFinset).finite_toSet ?_
  intro x hx
  obtain ⟨y, hfy, hgy⟩ := hx
  exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots hres).2
    (eval_resultant_eq_zero_of_common_zero hf hg H hfy hgy))


/-- **A two-variable system whose two eliminations are both nontrivial has finitely many common
zeros, bounded by the product of the two eliminant degrees.**  This is the elimination substitute
for an affine Bézout bound: each coordinate of a common zero is a root of the eliminant that removed
the other. -/
theorem card_common_zeros_le {f g f' g' : (K[X])[X]} {m n m' n' : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (H : m ≠ 0 ∨ n ≠ 0)
    (hres : f.resultant g m n ≠ 0)
    (hf' : f'.natDegree ≤ m') (hg' : g'.natDegree ≤ n') (H' : m' ≠ 0 ∨ n' ≠ 0)
    (hres' : f'.resultant g' m' n' ≠ 0)
    (hswapf : ∀ x y : K, evalPairHom y x f' = evalPairHom x y f)
    (hswapg : ∀ x y : K, evalPairHom y x g' = evalPairHom x y g)
    (s : Finset (K × K))
    (hs : ∀ p ∈ s, evalPairHom p.1 p.2 f = 0 ∧ evalPairHom p.1 p.2 g = 0) :
    s.card ≤ (f.resultant g m n).natDegree * (f'.resultant g' m' n').natDegree := by
  classical
  set R₁ : Finset K := (f.resultant g m n).roots.toFinset with hR₁
  set R₂ : Finset K := (f'.resultant g' m' n').roots.toFinset with hR₂
  have hsub : s ⊆ R₁ ×ˢ R₂ := by
    intro p hp
    obtain ⟨hfp, hgp⟩ := hs p hp
    refine Finset.mem_product.2 ⟨?_, ?_⟩
    · exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots hres).2
        (eval_resultant_eq_zero_of_common_zero hf hg H hfp hgp))
    · refine Multiset.mem_toFinset.2 ((Polynomial.mem_roots hres').2
        (eval_resultant_eq_zero_of_common_zero (x := p.2) (y := p.1) hf' hg' H' ?_ ?_))
      · rw [hswapf p.1 p.2]; exact hfp
      · rw [hswapg p.1 p.2]; exact hgp
  calc s.card ≤ (R₁ ×ˢ R₂).card := Finset.card_le_card hsub
    _ = R₁.card * R₂.card := Finset.card_product _ _
    _ ≤ (f.resultant g m n).natDegree * (f'.resultant g' m' n').natDegree := by
        refine Nat.mul_le_mul ?_ ?_
        · calc R₁.card ≤ Multiset.card (f.resultant g m n).roots := Multiset.toFinset_card_le _
            _ ≤ (f.resultant g m n).natDegree := Polynomial.card_roots' _
        · calc R₂.card ≤ Multiset.card (f'.resultant g' m' n').roots :=
              Multiset.toFinset_card_le _
            _ ≤ (f'.resultant g' m' n').natDegree := Polynomial.card_roots' _

end Count

end GaloisForLFunctions.HTGeometry
