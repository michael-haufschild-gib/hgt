import GaloisForLFunctions.HTGeometry.FiniteAbelianCyclicQuotient
import GaloisForLFunctions.HTGeometry.TorusChartFundamentalGroup
import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Connected finite covers of the complex torus chart

Path connectedness of a covering space makes its monodromy action transitive.  For the chart
`(ℂˣ)² × ℂᵏ`, the monodromy image is abelian by Eckmann--Hilton.  A nontrivial finite
connected cover therefore has a nontrivial cyclic quotient of its monodromy group.
-/

namespace GaloisForLFunctions.HTGeometry

open Path

universe u

variable {E : Type u} [TopologicalSpace E] {k : ℕ}
  (p : E → ComplexTorusAffineChart k) (cov : IsCoveringMap p)

/-- The monodromy image of a path-connected covering acts transitively on every fibre. -/
theorem connectedCover_monodromy_orbit_eq_univ [PathConnectedSpace E]
    (e : p ⁻¹' {(1 : ComplexTorusAffineChart k)}) :
    MulAction.orbit (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range e = Set.univ := by
  ext e'
  simp only [Set.mem_univ, iff_true, MulAction.mem_orbit_iff]
  let Γ : Path.Homotopic.Quotient (e : E) (e' : E) :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (e : E) (e' : E))
  let γ : FundamentalGroup (ComplexTorusAffineChart k) 1 :=
    (Γ.map ⟨p, cov.continuous⟩).cast e.2.symm e'.2.symm
  refine ⟨⟨cov.monodromyPerm 1 γ, ⟨γ, rfl⟩⟩, ?_⟩
  change cov.monodromy γ e = e'
  apply cov.monodromy_eq_of_map_eq Γ
  simp [γ]

/-- A path-connected covering has pretransitive monodromy image on its fibre. -/
theorem connectedCover_monodromy_isPretransitive [PathConnectedSpace E]
    (e : p ⁻¹' {(1 : ComplexTorusAffineChart k)}) :
    MulAction.IsPretransitive
      (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range
      (p ⁻¹' {(1 : ComplexTorusAffineChart k)}) := by
  rw [MulAction.isPretransitive_iff_orbit_eq_univ e]
  exact connectedCover_monodromy_orbit_eq_univ p cov e

/-- A transitive permutation subgroup on a nontrivial set is itself nontrivial. -/
theorem nontrivial_monodromyRange_of_connectedCover [PathConnectedSpace E]
    [Nontrivial (p ⁻¹' {(1 : ComplexTorusAffineChart k)})] :
    Nontrivial (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range := by
  obtain ⟨e, e', he⟩ := exists_pair_ne (p ⁻¹' {(1 : ComplexTorusAffineChart k)})
  have hpre := connectedCover_monodromy_isPretransitive p cov e
  obtain ⟨g, hg⟩ := hpre.exists_smul_eq e e'
  refine ⟨⟨g, 1, ?_⟩⟩
  intro h
  apply he
  rw [← hg, h, one_smul]

/-- A monodromy subgroup cuts out a nontrivial cyclic quotient, using the canonical commutative
group structure on the torus-chart monodromy image. -/
def IsNontrivialCyclicTorusChartMonodromyQuotient
    (N : Subgroup (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range) : Prop :=
  letI : CommGroup (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range :=
    torusChartMonodromyRangeCommGroup p cov
  IsCyclic ((cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range ⧸ N) ∧
  Nontrivial ((cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range ⧸ N)

/-- A cyclic monodromy quotient together with its exact two coordinate-loop exponents. -/
def HasNontrivialCyclicTorusChartCharacter
    (N : Subgroup (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range) : Prop :=
  letI : CommGroup (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range :=
    torusChartMonodromyRangeCommGroup p cov
  ∃ z : (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range ⧸ N,
    ∃ a b : ℤ,
      Subgroup.zpowers z = ⊤ ∧
      QuotientGroup.mk' N
          ((cov.monodromyPerm (1 : ComplexTorusAffineChart k)).rangeRestrict
            (torusChartFirstFundamentalGenerator k)) = z ^ a ∧
      QuotientGroup.mk' N
          ((cov.monodromyPerm (1 : ComplexTorusAffineChart k)).rangeRestrict
            (torusChartSecondFundamentalGenerator k)) = z ^ b ∧
      ¬ ((Nat.card ((cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range ⧸ N) : ℤ) ∣ a ∧
        (Nat.card ((cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range ⧸ N) : ℤ) ∣ b)

/-- **Cyclic reduction for a connected finite topological cover of the torus chart.**  Every
nontrivial such cover has a maximal proper monodromy subgroup with nontrivial cyclic quotient. -/
theorem connectedFiniteTorusChartCover_exists_nontrivial_cyclic_quotient
    [PathConnectedSpace E]
    [Finite (p ⁻¹' {(1 : ComplexTorusAffineChart k)})]
    [Nontrivial (p ⁻¹' {(1 : ComplexTorusAffineChart k)})] :
    ∃ N : Subgroup (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range,
      IsCoatom N ∧
        IsNontrivialCyclicTorusChartMonodromyQuotient p cov N := by
  letI : CommGroup (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range :=
    torusChartMonodromyRangeCommGroup p cov
  letI : Nontrivial (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range :=
    nontrivial_monodromyRange_of_connectedCover p cov
  simpa [IsNontrivialCyclicTorusChartMonodromyQuotient] using
    (exists_nontrivial_cyclic_quotient
      (A := (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range))

/-- **Exact Kummer-character reduction for a finite connected torus-chart cover.**  Every
nontrivial connected finite cover supplies a nontrivial finite cyclic quotient and an exponent
pair for the two coordinate meridians which is nonzero modulo the quotient order. -/
theorem connectedFiniteTorusChartCover_exists_nontrivial_cyclic_character
    [PathConnectedSpace E]
    [Finite (p ⁻¹' {(1 : ComplexTorusAffineChart k)})]
    [Nontrivial (p ⁻¹' {(1 : ComplexTorusAffineChart k)})] :
    ∃ N : Subgroup (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range,
      IsCoatom N ∧ HasNontrivialCyclicTorusChartCharacter p cov N := by
  obtain ⟨N, hN, hcyc⟩ :=
    connectedFiniteTorusChartCover_exists_nontrivial_cyclic_quotient p cov
  letI : CommGroup (cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range :=
    torusChartMonodromyRangeCommGroup p cov
  have hcyc' :
      IsCyclic ((cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range ⧸ N) ∧
        Nontrivial ((cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range ⧸ N) := by
    simpa [IsNontrivialCyclicTorusChartMonodromyQuotient] using hcyc
  letI : IsCyclic ((cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range ⧸ N) := hcyc'.1
  letI : Nontrivial ((cov.monodromyPerm (1 : ComplexTorusAffineChart k)).range ⧸ N) := hcyc'.2
  let ρ := cov.monodromyPerm (1 : ComplexTorusAffineChart k)
  let φ : FundamentalGroup (ComplexTorusAffineChart k) 1 →*
      ρ.range ⧸ N := (QuotientGroup.mk' N).comp ρ.rangeRestrict
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective N).comp ρ.rangeRestrict_surjective
  obtain ⟨z, a, b, hz, ha, hb, hab⟩ :=
    exists_cyclicCharacterExponents_not_both_dvd k φ hφ
  refine ⟨N, hN, ?_⟩
  simpa [HasNontrivialCyclicTorusChartCharacter, ρ, φ] using
    (show ∃ z, ∃ a b, Subgroup.zpowers z = ⊤ ∧
        φ (torusChartFirstFundamentalGenerator k) = z ^ a ∧
        φ (torusChartSecondFundamentalGenerator k) = z ^ b ∧
        ¬ ((Nat.card (ρ.range ⧸ N) : ℤ) ∣ a ∧
          (Nat.card (ρ.range ⧸ N) : ℤ) ∣ b) from
      ⟨z, a, b, hz, ha, hb, hab⟩)

end GaloisForLFunctions.HTGeometry
