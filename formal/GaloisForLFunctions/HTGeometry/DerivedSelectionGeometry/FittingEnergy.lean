import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.FittingInvariance
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.SourceOrientation
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.ReflectionEnergy

/-!
# Fitting ideals of the incompatibility modules, and the Fitting-energy identity

The zeroth Fitting ideal is a module invariant, so it can be read off the standard presentations of
the cyclic quotient and its square:

* `fittingIdealZero_quotient` — `Fitt₀(R/I) = I` for any ideal `I`;
* `fittingIdealZero_quotient_sq` — `Fitt₀((R/(t))²) = (t)²`;
* `fittingIdealZero_incompatModule` — `Fitt₀(Q) = I²`;
* `fittingIdealZero_srcIncompatModule` — `Fitt₀(Q_src) = I`;
* `fittingIdealZero_incompatModule_eq_sq` — `Fitt₀(Q) = Fitt₀(Q_src)²`;
* `span_monodromyEnergy_eq_fittingIdealZero` — the reflected positive energy generates exactly the
  zeroth Fitting ideal of the physical two-leg incompatibility module.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

universe u v w

section Transport

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

theorem presDetIdeal_comp_equiv {n : ℕ} (π : (Fin n → R) →ₗ[R] M) (e : M ≃ₗ[R] N) :
    presDetIdeal ((e : M →ₗ[R] N) ∘ₗ π) = presDetIdeal π := by
  have hrel : ∀ A : Matrix (Fin n) (Fin n) R,
      IsRelMatrix ((e : M →ₗ[R] N) ∘ₗ π) A ↔ IsRelMatrix π A := by
    intro A
    constructor
    · intro hA j
      have := hA j
      simpa using (e.map_eq_zero_iff).1 this
    · intro hA j
      simp [hA j]
  refine le_antisymm (presDetIdeal_le fun A hA => det_mem_presDetIdeal ((hrel A).1 hA))
    (presDetIdeal_le fun A hA => det_mem_presDetIdeal ((hrel A).2 hA))

/-- The zeroth Fitting ideal is a module invariant. -/
theorem fittingIdealZero_congr (e : M ≃ₗ[R] N) :
    fittingIdealZero R M = fittingIdealZero R N := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun n => iSup_le fun π => iSup_le fun hπ => ?_
    have hs : Function.Surjective ((e : M →ₗ[R] N) ∘ₗ π) := e.surjective.comp hπ
    rw [← presDetIdeal_comp_equiv π e, ← fittingIdealZero_eq_presDetIdeal hs]
  · refine iSup_le fun n => iSup_le fun π => iSup_le fun hπ => ?_
    have hs : Function.Surjective ((e.symm : N →ₗ[R] M) ∘ₗ π) := e.symm.surjective.comp hπ
    rw [← presDetIdeal_comp_equiv π e.symm, ← fittingIdealZero_eq_presDetIdeal hs]

end Transport

section Cyclic

variable {R : Type u} [CommRing R]

/-- The standard one-generator family of the cyclic quotient `R/I`. -/
def cyclicGen (I : Ideal R) : (Fin 1 → R) →ₗ[R] (R ⧸ I) :=
  I.mkQ ∘ₗ (LinearMap.proj 0 : (Fin 1 → R) →ₗ[R] R)

theorem cyclicGen_surjective (I : Ideal R) : Function.Surjective (cyclicGen I) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨fun _ => x, rfl⟩

/-- **`Fitt₀(R/I) = I`.** -/
theorem fittingIdealZero_quotient (I : Ideal R) :
    fittingIdealZero R (R ⧸ I) = I := by
  rw [fittingIdealZero_eq_presDetIdeal (cyclicGen_surjective I)]
  refine le_antisymm (presDetIdeal_le fun A hA => ?_) fun a ha => ?_
  · have h0 := hA 0
    rw [Matrix.det_fin_one]
    simpa [cyclicGen, Ideal.Quotient.eq_zero_iff_mem] using h0
  · have hrel : IsRelMatrix (cyclicGen I) (Matrix.of fun _ _ => a) := by
      intro j
      simpa [cyclicGen, Ideal.Quotient.eq_zero_iff_mem] using ha
    have := det_mem_presDetIdeal hrel
    rwa [Matrix.det_fin_one] at this

/-- The standard two-generator family of `(R/I)²`. -/
def cyclicSqGen (I : Ideal R) : (Fin 2 → R) →ₗ[R] ((R ⧸ I) × (R ⧸ I)) :=
  LinearMap.prod (I.mkQ ∘ₗ (LinearMap.proj 0 : (Fin 2 → R) →ₗ[R] R))
    (I.mkQ ∘ₗ (LinearMap.proj 1 : (Fin 2 → R) →ₗ[R] R))

theorem cyclicSqGen_surjective (I : Ideal R) : Function.Surjective (cyclicSqGen I) := by
  rintro ⟨z, w⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
  exact ⟨![x, y], rfl⟩

theorem isRelMatrix_cyclicSqGen_iff (I : Ideal R) (A : Matrix (Fin 2) (Fin 2) R) :
    IsRelMatrix (cyclicSqGen I) A ↔ ∀ i j, A i j ∈ I := by
  constructor
  · intro hA i j
    have := hA j
    rw [cyclicSqGen] at this
    have h1 : Ideal.Quotient.mk I (A 0 j) = 0 := congrArg Prod.fst this
    have h2 : Ideal.Quotient.mk I (A 1 j) = 0 := congrArg Prod.snd this
    fin_cases i
    · simpa [Ideal.Quotient.eq_zero_iff_mem] using h1
    · simpa [Ideal.Quotient.eq_zero_iff_mem] using h2
  · intro hA j
    refine Prod.ext ?_ ?_ <;>
      simp [cyclicSqGen, Ideal.Quotient.eq_zero_iff_mem, hA _ j]

/-- **`Fitt₀((R/(t))²) = (t)²`.** -/
theorem fittingIdealZero_quotient_sq (t : R) :
    fittingIdealZero R ((R ⧸ Ideal.span {t}) × (R ⧸ Ideal.span {t}))
      = (Ideal.span {t} : Ideal R) ^ 2 := by
  rw [fittingIdealZero_eq_presDetIdeal (cyclicSqGen_surjective (Ideal.span {t})),
    Ideal.span_singleton_pow]
  refine le_antisymm (presDetIdeal_le fun A hA => ?_) ?_
  · rw [(isRelMatrix_cyclicSqGen_iff _ A)] at hA
    obtain ⟨a00, h00⟩ := Ideal.mem_span_singleton.1 (hA 0 0)
    obtain ⟨a01, h01⟩ := Ideal.mem_span_singleton.1 (hA 0 1)
    obtain ⟨a10, h10⟩ := Ideal.mem_span_singleton.1 (hA 1 0)
    obtain ⟨a11, h11⟩ := Ideal.mem_span_singleton.1 (hA 1 1)
    rw [Matrix.det_fin_two, h00, h01, h10, h11, Ideal.mem_span_singleton]
    exact ⟨a00 * a11 - a01 * a10, by ring⟩
  · rw [Ideal.span_le]
    rintro r rfl
    have hrel : IsRelMatrix (cyclicSqGen (Ideal.span {t})) (Matrix.of ![![t, 0], ![0, t]]) := by
      rw [isRelMatrix_cyclicSqGen_iff]
      intro i j
      fin_cases i <;> fin_cases j <;> simp
    have := det_mem_presDetIdeal hrel
    rw [Matrix.det_fin_two] at this
    simpa [pow_two] using this

end Cyclic

section Incompat

variable {R : Type u} [CommRing R] {q c : R}

/-- **Theorem 3.2, Fitting half.**  `Fitt₀(Q) = I²`. -/
theorem fittingIdealZero_incompatModule (hc : IsUnit c) :
    fittingIdealZero R (incompatModule q c) = (Ideal.span {q - 1} : Ideal R) ^ 2 := by
  rw [fittingIdealZero_congr (incompatEquiv q c hc), fittingIdealZero_quotient_sq]

variable {S : Type v} [AddCommGroup S] [Module R S] {tauS : S →ₗ[R] S} {eps : S →ₗ[R] R}

/-- **Theorem 4A.1 (4A.7), Fitting half.**  `Fitt₀(Q_src) = I`. -/
theorem fittingIdealZero_srcIncompatModule (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hq : IsUnit q) (hc : IsUnit c) :
    fittingIdealZero R (srcIncompatModule tauS eps q c) = Ideal.span {q - 1} := by
  rw [fittingIdealZero_congr (srcIncompatEquiv hinv heps hq hc), fittingIdealZero_quotient]

/-- **Corollary 4A.2 (4A.12).**  The physical Fitting ideal is the square of the source one. -/
theorem fittingIdealZero_incompatModule_eq_sq (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hq : IsUnit q) (hc : IsUnit c) :
    fittingIdealZero R (incompatModule q c)
      = (fittingIdealZero R (srcIncompatModule tauS eps q c)) ^ 2 := by
  rw [fittingIdealZero_incompatModule hc,
    fittingIdealZero_srcIncompatModule hinv heps hq hc]

end Incompat

section Monodromy

open LaurentPolynomial

variable {k : Type u} [Field k] {c : MonodromyRing k}

/-- **Theorem 5.1 (5.3).**  The reflected positive energy generates exactly the zeroth Fitting
ideal of the two-leg Cartier incompatibility module. -/
theorem span_monodromyEnergy_eq_fittingIdealZero (hc : IsUnit c) :
    (Ideal.span {monodromyEnergy} : Ideal (MonodromyRing k))
      = fittingIdealZero (MonodromyRing k) (incompatModule (monodromyParam k) c) := by
  rw [fittingIdealZero_incompatModule hc, span_monodromyEnergy_eq, identityIdeal, wallEquation]

end Monodromy

end GaloisForLFunctions.HTGeometry.DerivedSelection
