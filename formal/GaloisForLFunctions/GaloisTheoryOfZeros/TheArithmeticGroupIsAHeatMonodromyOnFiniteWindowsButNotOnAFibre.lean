import GaloisForLFunctions.GaloisTheoryOfZeros.TheDegreeOfTheResidueFieldOfAZeroIsTheSizeOfItsOrbit
import GaloisForLFunctions.GaloisTheoryOfZeros.TheForwardMonodromyGroupMovesFinitelyManyZerosInDistinctPairsAtWill

/-!
# The arithmetic group is a heat monodromy on finite windows but not on a fibre

The arithmetic group `G = Gal(E/B)` over the prime trace field acts on the zeros of ξ, the fibre
of the heat cover at the time `0`; the forward monodromy group `G₊(b)` acts on the zeros of `H_b`
at a forward time `b`. Both commute with the reflection (`ρ ↦ 1 − ρ`, resp. `z ↦ −z`). A
comparison is a map `φ` between the two fibres. This module says exactly what such a map can
carry.

* **Finite windows** (`exists_mem_forwardMonodromy_eq_on_window`). If `φ` is injective and carries
  the reflection to `z ↦ −z`, every `σ ∈ G` agrees, on every finite set of zeros in distinct
  reflection pairs, with an element of `G₊(b)`.
* **No fibre, heat side** (`not_exists_injective_intertwining_forwardMonodromy`). No injective map
  from the zeros of `H_b` to the zeros of ξ carries every element of `G₊(b)` to the action of an
  element of `G`: `G₊(b)` is transitive on an infinite fibre, every orbit of `G` is finite.
* **No fibre, arithmetic side** (`not_exists_injective_intertwining_of_infinite`). No injective
  map from the zeros of ξ to the zeros of `H_b` carries an element of `G` that moves infinitely
  many zeros, such as conjugation `ρ ↦ ρ̄`, to an element of `G₊(b)`: those move finitely many.

So generic heat monodromy and fixed-fibre automorphisms are compatible exactly at finite level.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local notation "B" => primeTraceField
local notation "E" => primeTraceExtension
local notation "G" => (E ≃ₐ[B] E)
local instance : IsGalois B E := ⟨⟩

/-! ## Finite windows -/

/-- **Finite windows.** Under an injective map of the zeros of ξ into the zeros of `H_b` that
carries the reflection to `z ↦ −z`, each arithmetic automorphism agrees with an element of the
forward monodromy group on any finitely many zeros in distinct reflection pairs. -/
theorem exists_mem_forwardMonodromy_eq_on_window {b : ℂ} (hb₀ : 0 < b.re) (hb : b ∉ branchTimes)
    (φ : XiDivisorSupport → {z : ℂ // complexHeat b z = 0}) (hφ : Function.Injective φ)
    (hr : ∀ ρ, φ (xiZeroReflectEquiv ρ) = fibreNeg b (φ ρ)) (σ : G) {ι : Type*} [Finite ι]
    (s : ι → XiDivisorSupport) (hs : ∀ i j, i ≠ j → s j ≠ s i ∧ s j ≠ xiZeroReflectEquiv (s i)) :
    ∃ g ∈ forwardMonodromy b hb₀ hb, ∀ i, g (φ (s i)) = φ (primeTraceZeroMap σ (s i)) := by
  have hσ : Function.Injective (primeTraceZeroMap σ) := (primeTraceZeroPermutation σ).injective
  refine exists_mem_forwardMonodromy_forall_apply_eq hb₀ hb (p := fun i => φ (s i))
    (q := fun i => φ (primeTraceZeroMap σ (s i))) (fun i j hij => ?_) (fun i j hij => ?_)
  · show φ (s j) ≠ φ (s i) ∧ φ (s j) ≠ fibreNeg b (φ (s i))
    rw [← hr]
    exact ⟨fun e => (hs i j hij).1 (hφ e), fun e => (hs i j hij).2 (hφ e)⟩
  · show φ (primeTraceZeroMap σ (s j)) ≠ φ (primeTraceZeroMap σ (s i)) ∧
      φ (primeTraceZeroMap σ (s j)) ≠ fibreNeg b (φ (primeTraceZeroMap σ (s i)))
    rw [← hr, ← primeTraceZeroMap_reflection]
    exact ⟨fun e => (hs i j hij).1 (hσ (hφ e)), fun e => (hs i j hij).2 (hσ (hφ e))⟩

/-! ## No fibre -/

/-- **No fibre, heat side.** No injective map from a forward fibre to the zeros of ξ carries each
element of the forward monodromy group to the action of an arithmetic automorphism. -/
theorem not_exists_injective_intertwining_forwardMonodromy {b : ℂ} (hb₀ : 0 < b.re)
    (hb : b ∉ branchTimes) :
    ¬ ∃ φ : {z : ℂ // complexHeat b z = 0} → XiDivisorSupport, Function.Injective φ ∧
      ∀ g ∈ forwardMonodromy b hb₀ hb, ∃ σ : G, ∀ x, φ (g x) = primeTraceZeroMap σ (φ x) := by
  rintro ⟨φ, hφ, hg⟩
  haveI := infinite_fibre hb₀ hb
  obtain ⟨x₀⟩ := (inferInstance : Nonempty {z : ℂ // complexHeat b z = 0})
  -- by transitivity the image of `φ` lies in one orbit of `G`, which is finite
  have hmem : ∀ y, φ y ∈ Set.range fun σ : G => primeTraceZeroMap σ (φ x₀) := by
    intro y
    obtain ⟨g, hgm, hgy⟩ := exists_mem_forwardMonodromy_apply_eq b hb₀ hb x₀ y
    obtain ⟨σ, hσ⟩ := hg g hgm
    exact ⟨σ, show primeTraceZeroMap σ (φ x₀) = φ y by rw [← hσ, hgy]⟩
  haveI : Finite (Set.range fun σ : G => primeTraceZeroMap σ (φ x₀)) :=
    (primeTraceZeroMap_range_finite (φ x₀)).to_subtype
  haveI := Finite.of_injective
    (fun y => (⟨φ y, hmem y⟩ : Set.range fun σ : G => primeTraceZeroMap σ (φ x₀)))
    fun y y' h => hφ (congrArg Subtype.val h)
  exact not_finite {z : ℂ // complexHeat b z = 0}

/-- **No fibre, arithmetic side.** An arithmetic automorphism that moves infinitely many zeros is
carried by no injective map of the zeros of ξ into a forward fibre to an element of the forward
monodromy group. -/
theorem not_exists_injective_intertwining_of_infinite {b : ℂ} (hb₀ : 0 < b.re)
    (hb : b ∉ branchTimes) (σ : G) (hσ : {ρ | primeTraceZeroMap σ ρ ≠ ρ}.Infinite) :
    ¬ ∃ φ : XiDivisorSupport → {z : ℂ // complexHeat b z = 0}, Function.Injective φ ∧
      ∃ g ∈ forwardMonodromy b hb₀ hb, ∀ ρ, φ (primeTraceZeroMap σ ρ) = g (φ ρ) := by
  rintro ⟨φ, hφ, g, hg, he⟩
  refine (hσ.image hφ.injOn).mono ?_ (finite_setOf_forwardMonodromy_ne hg)
  rintro _ ⟨ρ, hρ, rfl⟩
  change g (φ ρ) ≠ φ ρ
  rw [← he]
  exact fun e => hρ (hφ e)

/-- Conjugation `ρ ↦ ρ̄` moves every zero. -/
theorem setOf_primeTraceConjugation_ne_infinite :
    {ρ | primeTraceZeroMap primeTraceConjugation ρ ≠ ρ}.Infinite := by
  have h : {ρ | primeTraceZeroMap primeTraceConjugation ρ ≠ ρ} = Set.univ := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro e
    rw [primeTraceZeroMap_conjugation] at e
    have hi := congrArg (fun z : XiDivisorSupport => (z : ℂ).im) e
    change (starRingEnd ℂ (ρ : ℂ)).im = (ρ : ℂ).im at hi
    rw [Complex.conj_im] at hi
    exact xi_divisor_support_im_ne_zero ρ (by linarith only [hi])
  rw [h]
  exact Set.infinite_univ_iff.2 xiDivisorSupport_infinite.to_subtype

/-- In particular conjugation of the zeros of ξ is never an element of `G₊(b)` under an injective
identification of the fibres. -/
theorem not_exists_injective_intertwining_conjugation {b : ℂ} (hb₀ : 0 < b.re)
    (hb : b ∉ branchTimes) :
    ¬ ∃ φ : XiDivisorSupport → {z : ℂ // complexHeat b z = 0}, Function.Injective φ ∧
      ∃ g ∈ forwardMonodromy b hb₀ hb,
        ∀ ρ, φ (primeTraceZeroMap primeTraceConjugation ρ) = g (φ ρ) :=
  not_exists_injective_intertwining_of_infinite hb₀ hb _ setOf_primeTraceConjugation_ne_infinite

end GaloisForLFunctions.GaloisTheoryOfZeros
