import Mathlib

/-!
# The quotient by a coordinate ideal

`MvPolynomial.killCompl` sends the variables outside the range of an injection to zero.  Its kernel
is exactly the coordinate ideal of that complement, and it is surjective because `rename` is a
section.  So the quotient by a coordinate ideal is the polynomial ring on the surviving variables,
and its Krull dimension is their number.

```text
killCompl_monomial_eq_zero            a monomial using a killed variable dies
ker_killCompl                         ** ker (killCompl) = span (X '' (range f)ᶜ) **
quotientSpanXImageEquiv               the quotient is a polynomial ring on the complement
ringKrullDim_quotient_span_X_image    ** dim = the number of surviving variables **
```

Together with `KrullDimInfPrimes.lean` and `stanleyReisnerIdeal_eq_inf_facetIdeal` this computes the
Krull dimension of a Stanley–Reisner ring as the size of its largest facet — for the Hankel
degeneration, `2r`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ τ : Type*} {R : Type u} [CommRing R]

theorem killCompl_monomial_eq_zero {f : σ → τ} (hf : Function.Injective f)
    {m : τ →₀ ℕ} (c : R) (h : ¬ ((↑m.support : Set τ) ⊆ Set.range f)) :
    killCompl hf (MvPolynomial.monomial m c) = 0 := by
  classical
  obtain ⟨i, hi, hir⟩ := Set.not_subset.mp h
  rw [killCompl, MvPolynomial.aeval_monomial]
  have hzero : (Finsupp.prod m fun j k =>
      (if hj : j ∈ Set.range f then X ((Equiv.ofInjective f hf).symm ⟨j, hj⟩)
        else (0 : MvPolynomial σ R)) ^ k) = 0 := by
    refine Finset.prod_eq_zero (i := i) hi ?_
    dsimp only
    rw [dif_neg hir, zero_pow]
    exact Finsupp.mem_support_iff.mp hi
  rw [hzero, mul_zero]

theorem killCompl_X_eq_zero {f : σ → τ} (hf : Function.Injective f) {i : τ}
    (hi : i ∉ Set.range f) : killCompl hf (X i : MvPolynomial τ R) = 0 := by
  classical
  rw [killCompl, MvPolynomial.aeval_X, dif_neg hi]

/-- **The kernel of `killCompl` is the coordinate ideal of the complement of the range.** -/
theorem ker_killCompl {f : σ → τ} (hf : Function.Injective f) :
    RingHom.ker ((killCompl hf : MvPolynomial τ R →ₐ[R] MvPolynomial σ R) :
        MvPolynomial τ R →+* MvPolynomial σ R)
      = Ideal.span (X '' (Set.range f)ᶜ) := by
  classical
  refine le_antisymm ?_ ?_
  · intro p hp
    rw [RingHom.mem_ker] at hp
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push Not at hcon
    have hsub : (↑m.support : Set τ) ⊆ Set.range f := by
      intro i hi
      by_contra hir
      exact (Finsupp.mem_support_iff.mp (by simpa using hi)) (hcon i hir)
    set m' : σ →₀ ℕ := Finsupp.comapDomain f m (hf.injOn) with hm'
    have hmap : Finsupp.mapDomain f m' = m := Finsupp.mapDomain_comapDomain f hf m hsub
    have hcoeff : MvPolynomial.coeff m' (killCompl hf p) = MvPolynomial.coeff m p := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum, MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single m]
      · rw [← hmap, MvPolynomial.killCompl_monomial_mapDomain hf, MvPolynomial.coeff_monomial,
          if_pos rfl]
      · intro n hn hne
        by_cases hns : (↑n.support : Set τ) ⊆ Set.range f
        · have hn' : Finsupp.mapDomain f (Finsupp.comapDomain f n (hf.injOn)) = n :=
            Finsupp.mapDomain_comapDomain f hf n hns
          rw [← hn', MvPolynomial.killCompl_monomial_mapDomain hf, MvPolynomial.coeff_monomial,
            if_neg]
          intro hcc
          apply hne
          rw [← hn', ← hmap, hcc]
        · rw [killCompl_monomial_eq_zero hf _ hns, MvPolynomial.coeff_zero]
      · intro hnm
        exact absurd hm hnm
    have hp' : killCompl hf p = 0 := hp
    rw [hp', MvPolynomial.coeff_zero] at hcoeff
    exact (MvPolynomial.mem_support_iff.mp hm) hcoeff.symm
  · rw [Ideal.span_le]
    rintro x ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    exact killCompl_X_eq_zero hf hi

/-- **The quotient by a coordinate ideal is a polynomial ring on the remaining variables.** -/
noncomputable def quotientSpanXImageEquiv (K : Type u) [Field K] {σ : Type*} (T : Set σ) :
    (MvPolynomial σ K ⧸ Ideal.span (X '' T : Set (MvPolynomial σ K)))
      ≃+* MvPolynomial ↑(Tᶜ) K := by
  classical
  have hinj : Function.Injective ((↑) : ↑(Tᶜ) → σ) := Subtype.val_injective
  have hrange : (Set.range ((↑) : ↑(Tᶜ) → σ))ᶜ = T := by
    rw [Subtype.range_coe, compl_compl]
  have hsurj : Function.Surjective
      ((killCompl hinj : MvPolynomial σ K →ₐ[K] MvPolynomial ↑(Tᶜ) K) :
        MvPolynomial σ K →+* MvPolynomial ↑(Tᶜ) K) := by
    intro q
    exact ⟨MvPolynomial.rename ((↑) : ↑(Tᶜ) → σ) q, MvPolynomial.killCompl_rename_app hinj q⟩
  refine RingEquiv.trans (RingEquiv.symm ?_) (RingHom.quotientKerEquivOfSurjective hsurj)
  exact Ideal.quotEquivOfEq (by rw [ker_killCompl hinj, hrange])

/-- **The dimension of a coordinate quotient is the number of surviving variables.** -/
theorem ringKrullDim_quotient_span_X_image (K : Type u) [Field K] {σ : Type*} [Finite σ]
    (T : Set σ) :
    ringKrullDim (MvPolynomial σ K ⧸ Ideal.span (X '' T : Set (MvPolynomial σ K)))
      = (Nat.card ↑(Tᶜ) : ℕ) := by
  classical
  rw [ringKrullDim_eq_of_ringEquiv (quotientSpanXImageEquiv K T),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field K]
  simp


end GaloisForLFunctions.HTGeometry
