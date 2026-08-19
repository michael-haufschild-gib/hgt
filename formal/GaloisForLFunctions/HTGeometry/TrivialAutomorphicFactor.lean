import GaloisForLFunctions.HTGeometry.QuasiAbelianCosetPoincareSeries
import GaloisForLFunctions.HTGeometry.LatticePeriodization

/-!
# The trivial automorphic factor, and periodization as a Poincaré series

Periodization along a lattice is the Poincaré series for the **trivial** factor: the term is
`1⁻¹ · f(x+γ) = f(x+γ)`, and the automorphy law it satisfies is plain invariance.  Introducing the
trivial factor therefore imports the corpus's whole coset-Poincaré apparatus — entireness from local
normal convergence, and the automorphy law — for the damping multiplier's profile, with no new
analysis.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The trivial automorphic factor. -/
def trivialAutomorphicFactor (d : ℕ) (Γ : AddSubgroup (Fin d → ℂ)) : AutomorphicFactor d Γ where
  factor := fun _ => mvPolynomialMultivariateEntire 1
  normalized := fun x => by simp [mvPolynomialMultivariateEntire]
  cocycle := fun γ δ x => by simp [mvPolynomialMultivariateEntire]
  nowhereZero := fun γ x => by simp [mvPolynomialMultivariateEntire]

@[simp] theorem trivialAutomorphicFactor_apply {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (γ : Γ) (x : Fin d → ℂ) :
    ((trivialAutomorphicFactor d Γ).factor γ).1 x = 1 := by
  simp [trivialAutomorphicFactor, mvPolynomialMultivariateEntire]

/-- A Poincaré term for the trivial factor is a plain translate. -/
theorem poincareTerm_trivialAutomorphicFactor {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (f : MultivariateEntire d) (γ : Γ) (x : Fin d → ℂ) :
    poincareTerm (trivialAutomorphicFactor d Γ) f γ x = f.1 (x + γ.1) := by
  rw [poincareTerm, trivialAutomorphicFactor_apply, inv_one, one_mul]

/-- **Membership in the forms of the trivial factor is invariance.** -/
theorem mem_forms_trivialAutomorphicFactor_iff {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (f : MultivariateEntire d) :
    f ∈ (trivialAutomorphicFactor d Γ).forms ↔ ∀ (γ : Γ) (x : Fin d → ℂ), f.1 (x + γ.1) = f.1 x := by
  constructor
  · intro hf γ x
    have := hf γ x
    rwa [trivialAutomorphicFactor_apply, one_mul] at this
  · intro hf γ x
    rw [trivialAutomorphicFactor_apply, one_mul]
    exact hf γ x

/-- The periodization of an entire source along a lattice, as an entire source. -/
def latticePeriodizationEntire {d k : ℕ} {ΓH : AddSubgroup (Fin d → ℂ)}
    (emb : (Fin k → ℤ) →+ (Fin d → ℂ)) (hemb : ∀ n, emb n ∈ ΓH) (f : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun n : Fin k → ℤ => poincareTerm (trivialAutomorphicFactor d ΓH) f
        (complementEmbedding emb hemb n)) Set.univ) :
    MultivariateEntire d :=
  cosetPoincareSeriesEntire (trivialAutomorphicFactor d ΓH) emb hemb f hnormal

/-- The entire periodization is the pointwise one. -/
theorem latticePeriodizationEntire_apply {d k : ℕ} {ΓH : AddSubgroup (Fin d → ℂ)}
    (emb : (Fin k → ℤ) →+ (Fin d → ℂ)) (hemb : ∀ n, emb n ∈ ΓH) (f : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun n : Fin k → ℤ => poincareTerm (trivialAutomorphicFactor d ΓH) f
        (complementEmbedding emb hemb n)) Set.univ)
    (x : Fin d → ℂ) :
    (latticePeriodizationEntire emb hemb f hnormal).1 x = latticePeriodizationFun emb f x := by
  rw [latticePeriodizationEntire, latticePeriodizationFun]
  show cosetPoincareSeries (trivialAutomorphicFactor d ΓH) emb hemb f x = _
  rw [cosetPoincareSeries]
  exact tsum_congr fun n => poincareTerm_trivialAutomorphicFactor f _ x

/-- **The entire periodization is invariant under the lattice.** -/
theorem latticePeriodizationEntire_invariant {d k : ℕ} {ΓH : AddSubgroup (Fin d → ℂ)}
    (emb : (Fin k → ℤ) →+ (Fin d → ℂ)) (hemb : ∀ n, emb n ∈ ΓH) (f : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun n : Fin k → ℤ => poincareTerm (trivialAutomorphicFactor d ΓH) f
        (complementEmbedding emb hemb n)) Set.univ)
    (hsurj : ∀ δ ∈ ΓH, ∃ n : Fin k → ℤ, δ = emb n) :
    ∀ η ∈ ΓH, ∀ x, (latticePeriodizationEntire emb hemb f hnormal).1 (x + η)
      = (latticePeriodizationEntire emb hemb f hnormal).1 x := by
  intro η hη x
  rw [latticePeriodizationEntire_apply, latticePeriodizationEntire_apply]
  exact latticePeriodizationFun_invariant emb f hsurj η hη x

end

end GaloisForLFunctions.HTGeometry
