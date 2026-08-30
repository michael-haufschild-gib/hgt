import Mathlib

/-!
# The universal composition-jet polynomials

Differentiating `Φ^{(j)} ∘ g` multiplies by `g'` and raises the outer order, while differentiating
`g^{(i)}` raises the inner order.  That is a derivation of a polynomial ring in two families of
variables, and iterating it starting from the outer value produces the Faà di Bruno polynomials

```text
(Φ ∘ g)^{(k)} = Ξ_k( Φ(g), …, Φ^{(k)}(g);  g', …, g^{(k)} ),
```

with `Ξ_k` **independent of `Φ` and `g`**.  This universality is what makes a composition-jet
argument uniform across a whole family of inner germs.

Everything here is algebraic: the only input is that the two jet families obey the chain-rule
recursion inside a differential ring.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- The variables of the composition-jet ring: `inl j` stands for the `j`-th derivative of the
outer germ evaluated along the inner one, `inr i` for the `(i+1)`-st derivative of the inner. -/
abbrev CompJetVar := ℕ ⊕ ℕ

section

variable (K : Type*) [Field K]

/-- The formal chain rule as a derivation of the composition-jet ring. -/
noncomputable def compJetDerivation :
    Derivation K (MvPolynomial CompJetVar K) (MvPolynomial CompJetVar K) :=
  MvPolynomial.mkDerivation K
    (Sum.elim (fun j : ℕ => X (Sum.inl (j + 1)) * X (Sum.inr 0)) (fun i : ℕ => X (Sum.inr (i + 1))))

@[simp] theorem compJetDerivation_X_inl (j : ℕ) :
    compJetDerivation K (X (Sum.inl j)) = X (Sum.inl (j + 1)) * X (Sum.inr 0) := by
  rw [compJetDerivation, mkDerivation_X]
  rfl

@[simp] theorem compJetDerivation_X_inr (i : ℕ) :
    compJetDerivation K (X (Sum.inr i)) = X (Sum.inr (i + 1)) := by
  rw [compJetDerivation, mkDerivation_X]
  rfl

/-- The universal composition-jet polynomials. -/
noncomputable def compJetPoly : ℕ → MvPolynomial CompJetVar K
  | 0 => X (Sum.inl 0)
  | (k + 1) => compJetDerivation K (compJetPoly k)

@[simp] theorem compJetPoly_zero : compJetPoly K 0 = X (Sum.inl 0) := rfl

@[simp] theorem compJetPoly_succ (k : ℕ) :
    compJetPoly K (k + 1) = compJetDerivation K (compJetPoly K k) := rfl

end

section

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra K R]

/-- **A derivation is determined on evaluations by its values on the variables.**  If a derivation
of `R` matches the formal chain rule on the evaluated variables, it matches it on every polynomial.
-/
theorem deriv_aeval_eq_aeval_compJetDerivation (D : Derivation ℤ R R)
    (hK : ∀ c : K, D (algebraMap K R c) = 0) (v : CompJetVar → R)
    (hinl : ∀ j : ℕ, D (v (Sum.inl j)) = v (Sum.inl (j + 1)) * v (Sum.inr 0))
    (hinr : ∀ i : ℕ, D (v (Sum.inr i)) = v (Sum.inr (i + 1))) (P : MvPolynomial CompJetVar K) :
    D (MvPolynomial.aeval v P) = MvPolynomial.aeval v (compJetDerivation K P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [hK a]
  | add p q hp hq => simp [hp, hq]
  | mul_X p w hp =>
      rw [map_mul, aeval_X, Derivation.leibniz, hp, Derivation.leibniz]
      simp only [smul_eq_mul]
      cases w with
      | inl j =>
          rw [compJetDerivation_X_inl, hinl j]
          simp only [map_add, map_mul, aeval_X]
      | inr i =>
          rw [compJetDerivation_X_inr, hinr i]
          simp only [map_add, map_mul, aeval_X]

/-- **The universal chain rule.**  Two jet families obeying the chain-rule recursion realise the
composition-jet polynomials as the iterated derivatives of the outer value. -/
theorem iterate_deriv_eq_aeval_compJetPoly (D : Derivation ℤ R R)
    (hK : ∀ c : K, D (algebraMap K R c) = 0) (a c : ℕ → R)
    (ha : ∀ j : ℕ, D (a j) = a (j + 1) * c 0) (hc : ∀ i : ℕ, D (c i) = c (i + 1)) (k : ℕ) :
    (⇑D)^[k] (a 0) = MvPolynomial.aeval (Sum.elim a c) (compJetPoly K k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [compJetPoly_succ]
      exact deriv_aeval_eq_aeval_compJetDerivation D hK (Sum.elim a c) ha hc (compJetPoly K k)

end

end GaloisForLFunctions.HTGeometry
