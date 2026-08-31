import GaloisForLFunctions.HTGeometry.GradedCokernel
import GaloisForLFunctions.HTGeometry.DimensionInjectivity

/-!
# The Hilbert-function criterion for regularity

```text
mulQuotHom            multiplication by `l` between graded pieces of the quotient
range_mulQuotHom      its image
cokerMulQuotEquiv     ** the cokernel is the next graded piece of the ring modulo `a + (l)` **
forall_mem_of_hilbert ** if the dimensions add up in every degree, `l` is a nonzerodivisor **
```

In each degree, multiplication by a homogeneous element maps one graded piece of `R ⧸ a` to another,
and its cokernel is the corresponding piece of `R ⧸ (a + (l))`.  So the Hilbert-function equation

```text
dim (R/(a+l))_{d+e} + dim (R/a)_e = dim (R/a)_{d+e}
```

is exactly the rank-nullity count for an injective map, and
`ker_eq_bot_of_finrank_quotient_range` turns it into injectivity;
`forall_mem_of_forall_homogeneous` then assembles the degrees into regularity.

This is the criterion a Gröbner degeneration feeds: the initial ideal supplies the dimensions, the
degeneration transports them, and regularity upstairs follows without any homological algebra.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Module

universe u
variable {σ : Type*} {K : Type u} [Field K]

theorem degreePart_le_comap {a : Ideal (MvPolynomial σ K)} {l : MvPolynomial σ K} {d : ℕ}
    (hl : l.IsHomogeneous d) (e : ℕ) :
    degreePart (a.restrictScalars K) e
      ≤ Submodule.comap (mulDegreeHom hl e) (degreePart (a.restrictScalars K) (d + e)) := by
  intro x hx
  show l * (x : MvPolynomial σ K) ∈ a
  exact Ideal.mul_mem_left _ _ hx

/-- Multiplication by `l`, as a map between the graded pieces of the quotient. -/
noncomputable def mulQuotHom {a : Ideal (MvPolynomial σ K)} {l : MvPolynomial σ K} {d : ℕ}
    (hl : l.IsHomogeneous d) (e : ℕ) :
    quotDegreePart (a.restrictScalars K) e →ₗ[K] quotDegreePart (a.restrictScalars K) (d + e) :=
  Submodule.mapQ _ _ (mulDegreeHom hl e) (degreePart_le_comap hl e)

theorem range_mulQuotHom {a : Ideal (MvPolynomial σ K)} {l : MvPolynomial σ K} {d : ℕ}
    (hl : l.IsHomogeneous d) (e : ℕ) :
    LinearMap.range (mulQuotHom (a := a) hl e)
      = Submodule.map (degreePart (a.restrictScalars K) (d + e)).mkQ
        (LinearMap.range (mulDegreeHom hl e)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Submodule.Quotient.induction_on with
    | H z => exact ⟨mulDegreeHom hl e z, ⟨z, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨z, rfl⟩, rfl⟩
    exact ⟨Submodule.Quotient.mk z, rfl⟩

/-- The cokernel of multiplication is the next graded piece of the ring modulo `a + (l)`. -/
noncomputable def cokerMulQuotEquiv {a : Ideal (MvPolynomial σ K)} (ha : IsHomogIdeal a)
    {l : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d) (e : ℕ) :
    (quotDegreePart (a.restrictScalars K) (d + e) ⧸ LinearMap.range (mulQuotHom (a := a) hl e))
      ≃ₗ[K] quotDegreePart ((a ⊔ Ideal.span {l}).restrictScalars K) (d + e) := by
  have hmapsup : Submodule.map (degreePart (a.restrictScalars K) (d + e)).mkQ
      (degreePart (a.restrictScalars K) (d + e) ⊔ LinearMap.range (mulDegreeHom hl e))
      = Submodule.map (degreePart (a.restrictScalars K) (d + e)).mkQ
        (LinearMap.range (mulDegreeHom hl e)) := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self _, bot_sup_eq]
  refine (Submodule.quotEquivOfEq _ _ ?_).trans
    ((Submodule.quotientQuotientEquivQuotient (degreePart (a.restrictScalars K) (d + e))
      (degreePart (a.restrictScalars K) (d + e) ⊔ LinearMap.range (mulDegreeHom hl e))
      le_sup_left).trans
      (Submodule.quotEquivOfEq _ _ (degreePart_sup_span ha hl e).symm))
  rw [range_mulQuotHom, hmapsup]

/-- **The Hilbert-function criterion for regularity.**  If in every degree the dimensions add up the
way they do when multiplication is injective, the homogeneous element is a nonzerodivisor. -/
theorem forall_mem_of_hilbert {a : Ideal (MvPolynomial σ K)} (ha : IsHomogIdeal a)
    {l : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d)
    [∀ e : ℕ, FiniteDimensional K (homogeneousSubmodule σ K e)]
    (hdim : ∀ e : ℕ,
      finrank K (quotDegreePart ((a ⊔ Ideal.span {l}).restrictScalars K) (d + e))
        + finrank K (quotDegreePart (a.restrictScalars K) e)
      = finrank K (quotDegreePart (a.restrictScalars K) (d + e))) :
    ∀ f : MvPolynomial σ K, l * f ∈ a → f ∈ a := by
  refine forall_mem_of_forall_homogeneous ha hl ?_
  intro e f hfh hlf
  have hinj : Function.Injective (mulQuotHom (a := a) hl e) := by
    refine injective_of_finrank_quotient_range _ ?_
    rw [(cokerMulQuotEquiv ha hl e).finrank_eq]
    exact hdim e
  have hclass : mulQuotHom (a := a) hl e (Submodule.Quotient.mk ⟨f, hfh⟩) = 0 := by
    show Submodule.Quotient.mk (mulDegreeHom hl e ⟨f, hfh⟩) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hlf
  have hzero : (Submodule.Quotient.mk ⟨f, hfh⟩ : quotDegreePart (a.restrictScalars K) e) = 0 := by
    apply hinj
    rw [hclass, map_zero]
  rw [Submodule.Quotient.mk_eq_zero] at hzero
  exact hzero

end GaloisForLFunctions.HTGeometry
