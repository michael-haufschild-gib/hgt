import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.ArtinSchreierDeckAction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Artin–Schreier irreducibility from root sums

A proper monic factor of `X^p-X-a` produces a base-field root: divide the
sum of its roots by its degree. Frobenius additivity gives the defining
equation, while prime characteristic makes the degree invertible.
Thus the polynomial is irreducible exactly when it has no base-field root.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Polynomial
variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

omit [CharP K p] in
/-- The leading term of an Artin–Schreier equation is monic. -/
theorem monic_artinSchreierPolynomial (a : K) :
    (artinSchreierPolynomial p a).Monic := by
  change (X ^ p - X - C a : K[X]).Monic
  rw [sub_sub]
  apply monic_X_pow_sub
  rw [degree_X_add_C]
  exact_mod_cast (Fact.out : p.Prime).one_lt

omit [CharP K p] in
/-- The natural degree of an Artin–Schreier polynomial is its prime exponent. -/
theorem natDegree_artinSchreierPolynomial (a : K) :
    (artinSchreierPolynomial p a).natDegree = p :=
  natDegree_eq_of_degree_eq_some (degree_artinSchreierPolynomial p a)

private theorem sum_artinSchreier_roots (a : K) (s : Multiset K)
    (hs : ∀ x ∈ s, x ^ p - x = a) :
    s.sum ^ p - s.sum = (s.card : K) * a := by
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.sum_zero, Multiset.card_zero, Nat.cast_zero,
      zero_pow (Fact.out : p.Prime).ne_zero, sub_zero, zero_mul]
  | cons x s ih =>
    have hx := hs x (by simp only [Multiset.mem_cons, true_or])
    have ht := ih (fun y hy => hs y (by simp only [Multiset.mem_cons]; exact Or.inr hy))
    simp only [Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one,
      add_pow_char]
    linear_combination hx + ht

/-- The negative next coefficient of every monic factor solves the degree-scaled equation. -/
theorem artinSchreier_factor_trace (a : K) (g : K[X]) (hg : g.Monic)
    (hd : g ∣ artinSchreierPolynomial p a) :
    (-g.nextCoeff) ^ p - (-g.nextCoeff) = (g.natDegree : K) * a := by
  let φ := algebraMap K (AlgebraicClosure K)
  have hsplit : (g.map φ).Splits := IsAlgClosed.splits _
  have hsum : φ (-g.nextCoeff) = (g.map φ).roots.sum := by
    rw [map_neg, ← nextCoeff_map φ.injective g,
      hsplit.nextCoeff_eq_neg_sum_roots_of_monic (hg.map φ), neg_neg]
  have hcard : (g.map φ).roots.card = g.natDegree :=
    hsplit.natDegree_eq_card_roots.symm.trans (natDegree_map φ)
  have hr : ∀ x ∈ (g.map φ).roots, x ^ p - x = φ a := by
    intro x hx
    have he := ((mem_roots (hg.map φ).ne_zero).mp hx).dvd (map_dvd φ hd)
    change (map φ (X ^ p - X - C a)).eval x = 0 at he
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, eval_sub, eval_pow, eval_X, eval_C] at he
    exact sub_eq_zero.mp he
  apply φ.injective
  rw [map_sub, map_pow, map_mul, map_natCast, hsum,
    sum_artinSchreier_roots p (φ a) (g.map φ).roots hr, hcard]

/-- A proper positive-degree monic factor yields an explicit base-field primitive. -/
theorem artinSchreier_root_of_factor (a : K) (g : K[X]) (hg : g.Monic)
    (hd : g ∣ artinSchreierPolynomial p a)
    (hpos : 0 < g.natDegree) (hlt : g.natDegree < p) :
    ∃ b : K, b ^ p - b = a := by
  have hdeg : (g.natDegree : K) ≠ 0 := by
    intro hz
    exact Nat.not_dvd_of_pos_of_lt hpos hlt ((CharP.cast_eq_zero_iff K p _).mp hz)
  have hpow : (g.natDegree : K) ^ p = (g.natDegree : K) :=
    map_natCast (frobenius K p) g.natDegree
  refine ⟨-g.nextCoeff / (g.natDegree : K), ?_⟩
  rw [div_pow, hpow, ← sub_div, artinSchreier_factor_trace p a g hg hd]
  exact mul_div_cancel_left₀ a hdeg

/-- Artin–Schreier polynomials are irreducible exactly when their additive equation
has no solution in the coefficient field. -/
theorem irreducible_artinSchreierPolynomial_iff (a : K) :
    Irreducible (artinSchreierPolynomial p a) ↔ ¬ ∃ b : K, b ^ p - b = a := by
  constructor
  · intro hirr
    rintro ⟨b, hb⟩
    apply hirr.not_isRoot_of_natDegree_ne_one (by
      rw [natDegree_artinSchreierPolynomial]
      exact ne_of_gt (Fact.out : p.Prime).one_lt) (x := b)
    change (X ^ p - X - C a).eval b = 0
    simp only [eval_sub, eval_pow, eval_X, eval_C, hb, sub_self]
  · intro hn
    have hmonic := monic_artinSchreierPolynomial p a
    have hunit := not_isUnit_of_degree_pos (artinSchreierPolynomial p a) (by
      rw [degree_artinSchreierPolynomial]
      exact_mod_cast (Fact.out : p.Prime).pos)
    apply (irreducible_iff_lt_natDegree_lt hmonic.ne_zero hunit).mpr
    intro g hg hdeg hd
    rw [Finset.mem_Ioc, natDegree_artinSchreierPolynomial] at hdeg
    have hhalf : p / 2 < p := Nat.div_lt_self (Fact.out : p.Prime).pos (by decide)
    exact hn (artinSchreier_root_of_factor p a g hg hd hdeg.1 (hdeg.2.trans_lt hhalf))

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.monic_artinSchreierPolynomial
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.natDegree_artinSchreierPolynomial
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.artinSchreier_factor_trace
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.artinSchreier_root_of_factor
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.irreducible_artinSchreierPolynomial_iff
