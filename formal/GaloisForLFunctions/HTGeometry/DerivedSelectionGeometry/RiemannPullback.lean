import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.DerivedPullback
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.FibreDichotomy

/-!
# The arithmetic specialisation of the universal monodromy line

A unit `b` of a `k`-algebra `A` determines a specialisation `k[q,q⁻¹] → A` sending `q` to `b`.
Under the arithmetic pullback `q = δ_n(ρ) = n^{2 Re ρ - 1}` the derived pullback of the source
orientation line is nonzero exactly on the critical line:

* `specializeHom`, `specializeHom_monodromyParam` — the specialisation homomorphism;
* `exists_riemann_specialization` — the arithmetic pullback is realised by an algebra structure;
* `riemann_pullback_nontrivial_iff` — its derived fibre is nonzero iff `Re ρ = 1/2`.

The second statement is the exact anti-circularity: asserting that the derived pullback survives at
every divisor point *is* the Riemann hypothesis, not a route to it.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

open CategoryTheory LaurentPolynomial

universe u

section Specialize

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- The specialisation of the universal monodromy line sending `q` to a chosen unit. -/
noncomputable def specializeHom (b : Aˣ) : MonodromyRing k →+* A :=
  eval₂ (algebraMap k A) b

@[simp] theorem specializeHom_monodromyParam (b : Aˣ) :
    specializeHom b (monodromyParam k) = (b : A) := by
  rw [specializeHom, monodromyParam, LaurentPolynomial.eval₂_T, zpow_one]

end Specialize

section Riemann

theorem riemannSpecial_pos {n : ℕ} (hn : 2 ≤ n) (ρ : ℂ) : 0 < riemannSpecial n ρ := by
  have hpos : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact Real.rpow_pos_of_pos hpos _

/-- The arithmetic pullback `q = δ_n(ρ)` is realised by an algebra structure on `ℂ` over the
universal monodromy line. -/
theorem exists_riemann_specialization {n : ℕ} (hn : 2 ≤ n) (ρ : ℂ) :
    ∃ alg : Algebra (MonodromyRing ℂ) ℂ,
      @algebraMap (MonodromyRing ℂ) ℂ _ _ alg (monodromyParam ℂ)
        = ((riemannSpecial n ρ : ℝ) : ℂ) := by
  have hne : ((riemannSpecial n ρ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (riemannSpecial_pos hn ρ).ne'
  refine ⟨(specializeHom (Units.mk0 _ hne)).toAlgebra, ?_⟩
  rw [RingHom.algebraMap_toAlgebra, specializeHom_monodromyParam]
  rfl

/-- **Corollary 8A.3.**  At the arithmetic specialisation the derived pullback of the source
orientation line is nonzero exactly on the critical line. -/
theorem riemann_pullback_nontrivial_iff {n : ℕ} (hn : 2 ≤ n) (ρ : ℂ)
    [Algebra (MonodromyRing ℂ) ℂ]
    (hspec : algebraMap (MonodromyRing ℂ) ℂ (monodromyParam ℂ)
      = ((riemannSpecial n ρ : ℝ) : ℂ)) :
    LinearMap.ker ((monodromyParam ℂ - 1) • LinearMap.id : ℂ →ₗ[MonodromyRing ℂ] ℂ) ≠ ⊥
      ↔ ρ.re = 1 / 2 := by
  rw [derivedPullback_nontrivial_iff (q := monodromyParam ℂ) ℂ, hspec,
    ← riemannSpecial_eq_one_iff hn ρ]
  exact_mod_cast Complex.ofReal_eq_one

end Riemann

end GaloisForLFunctions.HTGeometry.DerivedSelection
