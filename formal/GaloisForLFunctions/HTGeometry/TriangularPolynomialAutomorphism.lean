import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Order.OrderIsoNat
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Triangular automorphisms of polynomial rings

An endomorphism `φ` of `K[X_0, …, X_{M-1}]` (over a field) with
`φ(X_q) = u_q X_q + (a polynomial in X_0, …, X_{q-1})`, `u_q ≠ 0`, is an automorphism: every `X_q`
lies in the image by induction on `q`, and a surjective endomorphism of a Noetherian ring is
injective (the kernels of the iterates stabilize).

* `HTGeometry.injective_of_surjective_noetherian` : the Hopfian property of Noetherian rings.
* `HTGeometry.bijective_of_triangular`.
* `HTGeometry.triangularEquiv`.
-/

namespace HTGeometry

open MvPolynomial

/-- **A surjective endomorphism of a Noetherian ring is injective.** -/
theorem injective_of_surjective_noetherian {R : Type*} [CommRing R] [IsNoetherianRing R]
    (φ : R →+* R) (hφ : Function.Surjective φ) : Function.Injective φ := by
  let ker : ℕ →o Ideal R := ⟨fun n => RingHom.ker (φ ^ n), fun a b hab x hx => by
    rw [RingHom.mem_ker] at hx ⊢
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [add_comm, pow_add]
    change (φ ^ c) ((φ ^ a) x) = 0
    rw [hx, map_zero]⟩
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) ker
  have hsurj : ∀ k : ℕ, Function.Surjective ⇑(φ ^ k) := by
    intro k
    induction k with
    | zero =>
      intro x
      exact ⟨x, by rw [pow_zero]; rfl⟩
    | succ k ih =>
      rw [pow_succ]
      exact ih.comp hφ
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj n x
  have hy : y ∈ ker (n + 1) := by
    change (φ ^ (n + 1)) y = 0
    rw [pow_succ']
    exact hx
  rw [← hn (n + 1) (Nat.le_succ n)] at hy
  exact hy

variable {K : Type*} [Field K] {M : ℕ}

/-- The polynomials in the variables of index below `q`. -/
noncomputable def lowerVars (q : Fin M) : Subalgebra K (MvPolynomial (Fin M) K) :=
  Algebra.adjoin K (X '' {i | i < q})

/-- **Triangular endomorphisms are automorphisms.** -/
theorem bijective_of_triangular (φ : MvPolynomial (Fin M) K →ₐ[K] MvPolynomial (Fin M) K)
    (u : Fin M → K) (hu : ∀ q, u q ≠ 0)
    (hφ : ∀ q, φ (X q) - C (u q) * X q ∈ lowerVars (K := K) q) : Function.Bijective φ := by
  have hX : ∀ q, X q ∈ φ.range := by
    intro q
    induction q using WellFoundedLT.induction with
    | ind q ih =>
      have hlow : lowerVars (K := K) q ≤ φ.range := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨i, hi, rfl⟩
        exact ih i hi
      have h1 := hlow (hφ q)
      have h2 : X q = C (u q)⁻¹ * (φ (X q) - (φ (X q) - C (u q) * X q)) := by
        rw [sub_sub_cancel, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (hu q), C_1, one_mul]
      rw [h2]
      refine Subalgebra.mul_mem _ ?_ (Subalgebra.sub_mem _ ⟨X q, rfl⟩ h1)
      exact ⟨C (u q)⁻¹, φ.commutes (u q)⁻¹⟩
  have hsurj : Function.Surjective φ := by
    have htop : φ.range = ⊤ := by
      rw [eq_top_iff, ← MvPolynomial.adjoin_range_X, Algebra.adjoin_le_iff]
      rintro _ ⟨q, rfl⟩
      exact hX q
    intro y
    have hy : y ∈ φ.range := htop ▸ Algebra.mem_top
    exact hy
  exact ⟨injective_of_surjective_noetherian φ.toRingHom hsurj, hsurj⟩

/-- **The triangular automorphism.** -/
noncomputable def triangularEquiv (φ : MvPolynomial (Fin M) K →ₐ[K] MvPolynomial (Fin M) K)
    (u : Fin M → K) (hu : ∀ q, u q ≠ 0)
    (hφ : ∀ q, φ (X q) - C (u q) * X q ∈ lowerVars (K := K) q) :
    MvPolynomial (Fin M) K ≃ₐ[K] MvPolynomial (Fin M) K :=
  AlgEquiv.ofBijective φ (bijective_of_triangular φ u hu hφ)

end HTGeometry
