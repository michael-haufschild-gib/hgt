import GaloisForLFunctions.HTGeometry.PrincipalSymbolHypertranscendenceHorizon

/-!
# Principal-symbol law-space horizon

For a linear space of coefficient-field-preserving laws acting with a common algebraically free
source filtration, the complete failure-of-hypertranscendence locus is the kernel of the induced
principal raising symbol.  This is the affine-cone statement underlying the projective
characteristic horizon.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k K L g : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [AddCommMonoid g] [Module k g]

/-- The law-space principal symbol is forced by the law action and its algebraically free source
filtration.  In particular, two proposed linear symbols satisfying the same filtered law agree. -/
theorem principalSymbolLawSpace_unique
    (law : g →ₗ[k] Derivation k L L)
    (symbol₁ symbol₂ : g →ₗ[k] K) (u : ℕ → L)
    (hstep₁ : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol₁ A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (hstep₂ : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol₂ A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (hu : AlgebraicIndependent K u) :
    symbol₁ = symbol₂ := by
  ext A
  exact principalSymbol_unique (law A) u (symbol₁ A) (symbol₂ A)
    (hstep₁ A) (hstep₂ A) hu

/-- Exact law-space horizon: the directions whose complete jet tower fails to be algebraically
independent are precisely the characteristic directions in the kernel of the principal symbol. -/
theorem principalSymbolLawSpace_characteristicSet_eq_ker
    (law : g →ₗ[k] Derivation k L L)
    (coefficientLaw : g →ₗ[k] Derivation k K K)
    (symbol : g →ₗ[k] K) (u : ℕ → L)
    (hcompat : ∀ A : g, ∀ a : K,
      law A (algebraMap K L a) = algebraMap K L (coefficientLaw A a))
    (hstep : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (hu : AlgebraicIndependent K u) :
    {A : g | ¬ AlgebraicIndependent K
      (fun n : ℕ ↦ ((law A : L → L)^[n] (u 0)))} = (symbol.ker : Set g) := by
  ext A
  have hiff := principalJet_algebraicIndependent_iff
    (coefficientLaw A) (law A) u (symbol A) (hcompat A) (hstep A) hu
  simpa using not_congr hiff

/-- The complementary cone of hypertranscendental laws is exactly the complement of the
characteristic kernel. -/
theorem principalSymbolLawSpace_hypertranscendentalSet_eq_compl_ker
    (law : g →ₗ[k] Derivation k L L)
    (coefficientLaw : g →ₗ[k] Derivation k K K)
    (symbol : g →ₗ[k] K) (u : ℕ → L)
    (hcompat : ∀ A : g, ∀ a : K,
      law A (algebraMap K L a) = algebraMap K L (coefficientLaw A a))
    (hstep : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (hu : AlgebraicIndependent K u) :
    {A : g | AlgebraicIndependent K
      (fun n : ℕ ↦ ((law A : L → L)^[n] (u 0)))} = (symbol.ker : Set g)ᶜ := by
  ext A
  exact principalJet_algebraicIndependent_iff
    (coefficientLaw A) (law A) u (symbol A) (hcompat A) (hstep A) hu

end

end GaloisForLFunctions.HTGeometry
