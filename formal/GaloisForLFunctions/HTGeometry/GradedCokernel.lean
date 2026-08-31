import GaloisForLFunctions.HTGeometry.GradedMultiplication

/-!
# Adding a homogeneous element, degree by degree

```text
mem_sup_span_iff_of_homogeneous  ** a homogeneous element of `a + (l)` splits as α + l·β with both
                                    parts homogeneous **
degreePart_sup_span              ** so in each degree, `a + (l)` is the degree part of `a` plus the
                                    image of multiplication by `l` **
```

The splitting is the usual component argument: write the element as `α₀ + l·β₀` and take the
homogeneous component of the right degree, which keeps `α₀` inside the ideal and turns `l·β₀` into
`l` times a component of `β₀`.

This identifies the cokernel of multiplication: the degree-`(d+e)` piece of the ring modulo `a + (l)`
is the cokernel of `mulDegreeHom` on the pieces modulo `a`.  That is what lets the dimension
criterion `ker_eq_bot_of_finrank_quotient_range` be applied degree by degree.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Module

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- **A homogeneous element of `a + (l)` splits into homogeneous parts.** -/
theorem mem_sup_span_iff_of_homogeneous {a : Ideal (MvPolynomial σ K)} (ha : IsHomogIdeal a)
    {l : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d) {e : ℕ}
    {x : MvPolynomial σ K} (hx : x.IsHomogeneous (d + e)) :
    x ∈ a ⊔ Ideal.span {l} ↔
      ∃ α β : MvPolynomial σ K, α ∈ a ∧ α.IsHomogeneous (d + e) ∧ β.IsHomogeneous e
        ∧ x = α + l * β := by
  constructor
  · intro hmem
    obtain ⟨α₀, hα₀, y, hy, hxy⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨β₀, hβ₀⟩ := Ideal.mem_span_singleton.mp hy
    refine ⟨MvPolynomial.homogeneousComponent (d + e) α₀,
      MvPolynomial.homogeneousComponent e β₀,
      ha _ _ hα₀, MvPolynomial.homogeneousComponent_isHomogeneous (d + e) α₀,
      MvPolynomial.homogeneousComponent_isHomogeneous e β₀, ?_⟩
    have hxcomp : MvPolynomial.homogeneousComponent (d + e) x = x := by
      ext γ
      rw [MvPolynomial.coeff_homogeneousComponent]
      by_cases hγ : Finsupp.degree γ = d + e
      · rw [if_pos hγ]
      · rw [if_neg hγ]
        by_contra hcon
        refine hγ ?_
        have := hx (Ne.symm hcon)
        rwa [weight_one_eq_degree] at this
    have hsplit : x = MvPolynomial.homogeneousComponent (d + e) α₀
        + MvPolynomial.homogeneousComponent (d + e) (l * β₀) := by
      rw [← map_add, ← hβ₀, hxy, hxcomp]
    rw [hsplit, homogeneousComponent_mul_left hl β₀ e]
  · rintro ⟨α, β, hα, -, -, rfl⟩
    exact Submodule.mem_sup.mpr ⟨α, hα, l * β, Ideal.mem_span_singleton.mpr ⟨β, rfl⟩, rfl⟩

/-- **The degree part of `a + (l)` is the degree part of `a` plus the image of multiplication.** -/
theorem degreePart_sup_span {a : Ideal (MvPolynomial σ K)} (ha : IsHomogIdeal a)
    {l : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d) (e : ℕ) :
    degreePart ((a ⊔ Ideal.span {l}).restrictScalars K) (d + e)
      = degreePart (a.restrictScalars K) (d + e) ⊔ LinearMap.range (mulDegreeHom hl e) := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro x hx
    have hxmem : (x : MvPolynomial σ K) ∈ a ⊔ Ideal.span {l} := hx
    obtain ⟨α, β, hα, hαh, hβh, hsplit⟩ :=
      (mem_sup_span_iff_of_homogeneous ha hl x.2).mp hxmem
    refine Submodule.mem_sup.mpr ⟨⟨α, hαh⟩, hα, ⟨l * β, hl.mul hβh⟩, ⟨⟨β, hβh⟩, rfl⟩, ?_⟩
    exact Subtype.ext hsplit.symm
  · intro x hx
    exact Ideal.mem_sup_left hx
  · rintro x ⟨y, rfl⟩
    have : ((mulDegreeHom hl e y : homogeneousSubmodule σ K (d + e)) : MvPolynomial σ K)
        = l * (y : MvPolynomial σ K) := rfl
    show ((mulDegreeHom hl e y : homogeneousSubmodule σ K (d + e)) : MvPolynomial σ K)
      ∈ a ⊔ Ideal.span {l}
    rw [this]
    exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

end GaloisForLFunctions.HTGeometry
