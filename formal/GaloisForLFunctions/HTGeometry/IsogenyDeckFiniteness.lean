import GaloisForLFunctions.HTGeometry.DeckDegreeUpperBoundBridge
import GaloisForLFunctions.HTGeometry.IsogenyGeneral

/-!
# Isogenies supply finite prefix deck groups

The general commutative-group isogeny layer defines an isogeny by finite kernel and finite
cokernel.  Composition therefore makes every finite protocol prefix an isogeny.  Its kernel, and
the image of that kernel under any deck representation, are finite automatically.

This removes the separate finite-deck hypothesis from the numerical deck-closure theorem.  It does
not manufacture the geometric degree estimate: matching function-field degree with kernel order
remains the genuine quotient input.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {G : ℕ → Type*} [∀ i, CommGroup (G i)]

/-- Every finite prefix of a protocol of isogenies is an isogeny. -/
theorem isIsogeny_prefixHom
    (a : ∀ i, G i →* G (i + 1)) (ha : ∀ i, IsIsogeny (a i)) (i n : ℕ) :
    IsIsogeny (prefixHom a i n) := by
  induction n generalizing i with
  | zero => exact IsIsogeny.id_isogeny
  | succ n ih => exact (ih (i + 1)).comp (ha i)

/-- Prefix kernels of a protocol of isogenies are finite. -/
theorem finite_prefixKernel_of_isogenies
    (a : ∀ i, G i →* G (i + 1)) (ha : ∀ i, IsIsogeny (a i)) (i n : ℕ) :
    Finite (prefixKernel a i n) :=
  (isIsogeny_prefixHom a ha i n).finite_ker

/-- The represented deck group of an isogeny prefix is finite. -/
theorem finite_prefixKernel_map_of_isogenies
    (a : ∀ i, G i →* G (i + 1)) (ha : ∀ i, IsIsogeny (a i)) (i n : ℕ)
    {A : Type*} [Group A] (rho : G i →* A) :
    Finite ((prefixKernel a i n).map rho) := by
  letI : Finite (prefixKernel a i n) := finite_prefixKernel_of_isogenies a ha i n
  let f : prefixKernel a i n → (prefixKernel a i n).map rho := fun x =>
    ⟨rho x, ⟨x, x.2, rfl⟩⟩
  apply Finite.of_surjective f
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]

/-- **Deck-closure tail for an isogeny protocol.**  Isogeny hypotheses supply all finite-prefix
deck groups.  Deck invariance, finite-dimensionality, the one-sided function-field degree bound,
and closed stabilizers then identify the tail with the fixed field of the closed erased sector. -/
theorem nonautonomousTail_eq_fixedField_erasedClosure_of_isogenies_and_finrank_le
    (phi : ℕ → F →ₐ[K] F) (i : ℕ)
    (a : ∀ j, G j →* G (j + 1)) (ha : ∀ j, IsIsogeny (a j))
    (rho : G i →* (F ≃ₐ[K] F))
    (hfd : ∀ n, FiniteDimensional (IntermediateField.map (forwardPrefix phi i n) ⊤) F)
    (hfix : ∀ n, IntermediateField.map (forwardPrefix phi i n) ⊤ ≤
      IntermediateField.fixedField ((prefixKernel a i n).map rho))
    (hle : ∀ n, Module.finrank (IntermediateField.map (forwardPrefix phi i n) ⊤) F
      ≤ Nat.card ((prefixKernel a i n).map rho))
    (hclosed : ∀ x : F, IsClosed {g : G i | rho g x = x}) :
    nonautonomousTail phi i =
      IntermediateField.fixedField ((erasedClosure a i).map rho) := by
  apply nonautonomousTail_eq_fixedField_erasedClosure_of_finrank_le
    phi i a rho
      (fun n => finite_prefixKernel_map_of_isogenies a ha i n rho)
    hfd hfix hle hclosed

end


end GaloisForLFunctions.HTGeometry
