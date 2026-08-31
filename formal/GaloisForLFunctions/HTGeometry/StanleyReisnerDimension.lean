import GaloisForLFunctions.HTGeometry.CoordinatePrimeRegular
import GaloisForLFunctions.HTGeometry.KrullDimInfPrimes
import GaloisForLFunctions.HTGeometry.CoordinateQuotient

/-!
# Dimension and regular elements of a Stanley–Reisner ring

The Hankel-specific arguments of `HankelChainStanleyReisner.lean` are really general facts about a
finite family of faces, so they are recorded here in that generality.

```text
faceFamilyIdeal K F                 ⋂ over the faces of the complementary coordinate ideal
ringKrullDim_faceFamilyIdeal        ** the dimension is the size of the largest face **
isRegularOn_faceFamilyIdeal         ** a form outside every facet prime is a nonzerodivisor **
```

Both rest on `isPrime_span_X_image`, `ringKrullDim_quotient_inf_primes` and
`ringKrullDim_quotient_span_X_image`, none of which is in mathlib.  They are the substrate a
shellability argument would build on: the remaining Cohen–Macaulay content for the Hankel card is
the regularity of the *later* terms of a linear system of parameters, where the quotients stop being
Stanley–Reisner rings.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type u} [Field K]

/-- The Stanley–Reisner ideal of a finite family of faces: the intersection over the faces of the
coordinate ideal of the complementary variables. -/
noncomputable def faceFamilyIdeal (K : Type u) [Field K] (F : Finset (Finset σ)) :
    Ideal (MvPolynomial σ K) :=
  F.inf fun S => Ideal.span (X '' (↑(Sᶜ) : Set σ))

theorem ringKrullDim_quotient_span_X_compl' (K : Type u) [Field K] (S : Finset σ) :
    ringKrullDim (MvPolynomial σ K ⧸
        Ideal.span (X '' (↑(Sᶜ) : Set σ) : Set (MvPolynomial σ K)))
      = (S.card : ℕ) := by
  classical
  rw [ringKrullDim_quotient_span_X_image K (↑(Sᶜ) : Set σ)]
  congr 1
  rw [Finset.coe_compl, compl_compl]
  simp

/-- **The dimension of a Stanley–Reisner ring is the size of its largest face.** -/
theorem ringKrullDim_faceFamilyIdeal (K : Type u) [Field K] {F : Finset (Finset σ)}
    {D : ℕ} (hle : ∀ S ∈ F, S.card ≤ D) {S₀ : Finset σ} (hS₀ : S₀ ∈ F) (hcard : S₀.card = D) :
    ringKrullDim (MvPolynomial σ K ⧸ faceFamilyIdeal K F) = ((D : ℕ) : ℕ∞) := by
  classical
  refine ringKrullDim_quotient_inf_primes (s := F)
    (P := fun S : Finset σ => Ideal.span (X '' (↑(Sᶜ) : Set σ)))
    (I := faceFamilyIdeal K F) (d := ((D : ℕ) : ℕ∞)) rfl ?_ (i₀ := S₀) hS₀ ?_
  · intro S hS
    rw [ringKrullDim_quotient_span_X_compl' K S]
    exact_mod_cast Nat.cast_le.mpr (hle S hS)
  · rw [ringKrullDim_quotient_span_X_compl' K S₀, hcard]
    norm_cast

/-- **A linear form whose support meets every face is a nonzerodivisor on the Stanley–Reisner
ring.** -/
theorem isRegularOn_faceFamilyIdeal (K : Type u) [Field K] {F : Finset (Finset σ)}
    {x : MvPolynomial σ K}
    (hx : ∀ S ∈ F, x ∉ Ideal.span (X '' (↑(Sᶜ) : Set σ) : Set (MvPolynomial σ K))) :
    IsRegularOn (faceFamilyIdeal K F) x :=
  isRegularOn_of_notMem_inf_primes (fun _S _ => isPrime_span_X_image _) rfl hx

end GaloisForLFunctions.HTGeometry
