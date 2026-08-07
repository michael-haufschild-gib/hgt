import Mathlib

/-!
# The conormal module of a principal ideal

For a nonzero `g` in an integral domain `R`, multiplication by `g` identifies `R / (g)` with the
conormal module `(g) / (g)^2`.  This is the algebraic content of "the conormal module of a
principal divisor is the free rank-one module over the structure sheaf of the divisor".

* `principalCotangentEquiv` — the `R`-linear equivalence.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R]

/-- Multiplication by `g`, landing in the principal ideal it generates. -/
def mulIntoSpan (g : R) : R →ₗ[R] ↥(Ideal.span ({g} : Set R)) where
  toFun r := ⟨r * g, Ideal.mem_span_singleton.mpr ⟨r, by ring⟩⟩
  map_add' r s := by ext; simp [add_mul]
  map_smul' c r := by ext; simp [smul_eq_mul, mul_assoc]

@[simp] theorem mulIntoSpan_coe (g r : R) : ((mulIntoSpan g r : ↥(Ideal.span ({g} : Set R))) : R)
    = r * g := rfl

/-- Multiplication by `g` composed with the conormal projection. -/
def toPrincipalCotangent (g : R) : R →ₗ[R] (Ideal.span ({g} : Set R)).Cotangent :=
  (Ideal.span ({g} : Set R)).toCotangent ∘ₗ mulIntoSpan g

theorem toPrincipalCotangent_surjective (g : R) :
    Function.Surjective (toPrincipalCotangent g) := by
  intro x
  obtain ⟨y, rfl⟩ := (Ideal.span ({g} : Set R)).toCotangent_surjective x
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp y.2
  refine ⟨c, ?_⟩
  simp only [toPrincipalCotangent, LinearMap.coe_comp, Function.comp_apply]
  congr 1
  exact Subtype.ext (by simpa [mul_comm] using hc.symm)

theorem ker_toPrincipalCotangent {g : R} (hg : ∀ a b : R, g * a = g * b → a = b) :
    LinearMap.ker (toPrincipalCotangent g) = Ideal.span ({g} : Set R) := by
  ext r
  simp only [LinearMap.mem_ker, toPrincipalCotangent, LinearMap.coe_comp, Function.comp_apply,
    Ideal.toCotangent_eq_zero, mulIntoSpan_coe]
  rw [sq, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hg r (g * c) (by linear_combination hc)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]; ring⟩

/-- **The conormal module of a principal ideal.**  Multiplication by a cancellable `g` identifies
`R / (g)` with `(g) / (g)^2`. -/
def principalCotangentEquiv {g : R} (hg : ∀ a b : R, g * a = g * b → a = b) :
    (R ⧸ Ideal.span ({g} : Set R)) ≃ₗ[R] (Ideal.span ({g} : Set R)).Cotangent :=
  (Submodule.quotEquivOfEq _ _ (ker_toPrincipalCotangent hg).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (toPrincipalCotangent_surjective g))

end

end GaloisForLFunctions.HTGeometry
