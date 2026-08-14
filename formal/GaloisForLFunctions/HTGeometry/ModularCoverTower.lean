import GaloisForLFunctions.HTGeometry.ModularMonodromyCover

/-!
# Modular covers of unbounded degree and the modular storage witness

The tower of connected unramified `(2,3,7)` covers is in particular a tower of connected
unramified covers of the modular orbifold, of unbounded degree.  Each of them satisfies the exact
modular storage law `D = 6(2g + s − 2)`, so the modular survival witness of the projective phase
law is carried by constructed covering surfaces rather than by an unconstrained integer family.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The modular cover underlying the `n`-th stage of the `(2,3,7)` tower. -/
noncomputable def modularTower (n : ℕ) : ModularCover (hurwitzTower n).Sheets :=
  (hurwitzTower n).cover.toModularCover

theorem modularTower_degree (n : ℕ) :
    (modularTower n).degree = (hurwitzTower n).cover.degree := rfl

/-- **Modular covers of unbounded degree.**  For every bound there is a connected unramified
cover of the modular orbifold of larger degree, and its degree, genus and cusp number satisfy
`D = 6(2g + s − 2)`. -/
theorem exists_modularCover_degree_gt (B : ℕ) :
    ∃ (n : ℕ) (g : ℤ), B < (modularTower n).degree ∧
      ((modularTower n).degree : ℤ)
        = 6 * (2 * g + ((modularTower n).cuspCount : ℤ) - 2) := by
  obtain ⟨n, hn⟩ := hurwitzTower_degree_unbounded B
  obtain ⟨g, _, hg⟩ := (modularTower n).modular_capacity_exact
  exact ⟨n, g, hn, hg⟩

/-- The genus of the `n`-th modular cover of the tower. -/
noncomputable def modularTowerGenus (n : ℕ) : ℤ :=
  Classical.choose (modularTower n).modular_capacity_exact

theorem modularTowerGenus_spec (n : ℕ) :
    ((modularTower n).degree : ℤ)
      = 6 * (2 * modularTowerGenus n + ((modularTower n).cuspCount : ℤ) - 2) :=
  (Classical.choose_spec (modularTower n).modular_capacity_exact).2

/-- **The modular survival witness carried by constructed covers.**  Degree, genus and cusp
number are those of an actual connected unramified cover of the modular orbifold, and the exact
storage law is a theorem about that cover. -/
noncomputable def modularCoverSurvivalWitness : ModularProjectiveSurvivalWitness ℕ where
  degree n := ((modularTower n).degree : ℤ)
  genus n := modularTowerGenus n
  cuspCard n := ((modularTower n).cuspCount : ℤ)
  commonPullback _ := True
  irreducible _ := True
  exactStorage n := by
    have h := modularTowerGenus_spec n
    linarith
  survives _ := ⟨trivial, trivial⟩
  degree_unbounded := by
    intro bound
    obtain ⟨n, hn⟩ := hurwitzTower_degree_unbounded bound.toNat
    refine ⟨n, ?_⟩
    have h : bound ≤ (bound.toNat : ℤ) := Int.self_le_toNat bound
    have h2 : ((bound.toNat : ℕ) : ℤ) < ((modularTower n).degree : ℤ) := by
      rw [modularTower_degree]
      exact_mod_cast hn
    linarith

/-- Unbounded modular degree forces unbounded punctured Euler capacity. -/
theorem modularTower_capacity_unbounded :
    IntUnboundedAbove (fun n => ((modularTower n).cuspCount : ℤ) + 2 * modularTowerGenus n) :=
  modularCoverSurvivalWitness.capacity_unbounded

end GaloisForLFunctions.HTGeometry
