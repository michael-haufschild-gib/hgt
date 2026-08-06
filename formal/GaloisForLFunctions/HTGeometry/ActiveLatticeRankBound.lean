import GaloisForLFunctions.HTGeometry.IntegerToComplexIndependence
import GaloisForLFunctions.HTGeometry.PhaseRankLeAutonomousOrder

/-!
# The rank of the active lattice is at most the autonomous order

A bound on the size of every integrally independent family inside a set of
integer characters bounds the rank of the lattice it generates: a rational
basis extracted from the set is finite, and pulls back to an integrally
independent family of the same size.

Applied to the active support, this turns the bound on independent families
into the bound on the rank of the active lattice, which is the frequency rank.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
/-- **Bounding the rank of a character lattice by its independent families.** -/
theorem rank_span_int_le_of_independent_bound {S : Set (d → ℤ)} {n : ℕ}
    (h : ∀ (s : ℕ) (v : Fin s → (d → ℤ)), (∀ i, v i ∈ S) →
      LinearIndependent ℤ v → s ≤ n) :
    Module.rank ℤ (Submodule.span ℤ S) ≤ (n : Cardinal) := by
  classical
  set T : Set (d → ℚ) := intCharacterToRat '' S with hT
  obtain ⟨b, hbT, hspan, hind⟩ := exists_linearIndependent ℚ T
  have hbrank : Module.rank ℚ (Submodule.span ℚ T) = Cardinal.mk b := by
    rw [← hspan]
    exact rank_span_set hind
  have hfin : b.Finite := by
    rw [← Cardinal.lt_aleph0_iff_set_finite, ← hbrank]
    calc Module.rank ℚ (Submodule.span ℚ T)
        ≤ Module.rank ℚ (d → ℚ) := Submodule.rank_le _
      _ = (Fintype.card d : Cardinal) := rank_fun'
      _ < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  haveI : Fintype b := hfin.fintype
  let e : Fin (Fintype.card b) ≃ b := (Fintype.equivFin b).symm
  have hchoice : ∀ x : b, ∃ m : d → ℤ, m ∈ S ∧ intCharacterToRat m = (x : d → ℚ) := by
    intro x
    obtain ⟨m, hm, hmx⟩ := hbT x.2
    exact ⟨m, hm, hmx⟩
  choose mm hmmS hmmEq using hchoice
  set w : Fin (Fintype.card b) → (d → ℤ) := fun i => mm (e i) with hw
  have hwS : ∀ i, w i ∈ S := fun i => hmmS (e i)
  have hwQ : (fun i => intCharacterToRat (w i)) = fun i => ((e i : d → ℚ)) := by
    funext i
    exact hmmEq (e i)
  have hindQ : LinearIndependent ℚ (fun i => intCharacterToRat (w i)) := by
    rw [hwQ]
    exact hind.comp e e.injective
  have hindZ : LinearIndependent ℤ w :=
    LinearIndependent.of_comp intCharacterToRat
      ((LinearIndependent.iff_fractionRing ℤ ℚ).2 hindQ)
  have hcard := h _ w hwS hindZ
  have hZ : Module.rank ℤ (Submodule.span ℤ S)
      = Module.rank ℤ (Submodule.span ℤ T) := by
    rw [hT, ← Submodule.map_span]
    exact (Submodule.equivMapOfInjective _ injective_intCharacterToRat
      (Submodule.span ℤ S)).rank_eq
  rw [hZ, rank_span_int_eq_rank_span_rat, hbrank, Cardinal.mk_fintype]
  exact_mod_cast hcard

/-- **The rank of the active lattice is at most the autonomous order.** -/
theorem rank_activeLattice_le {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hindep : RationallyIndependentFrequency omega) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n : ℕ}
    (Q : MvPolynomial (Fin (n + 1)) ℂ)
    (hQ : ∀ z ∈ polyannulus ρ, jetRelationEval omega F Q z = 0) {z₀ : d → ℂ}
    (hz₀ : z₀ ∈ polyannulus ρ)
    (hsep : MvPolynomial.eval (fun i : Fin (n + 1) => phaseJet omega F (i : ℕ) z₀)
      (MvPolynomial.pderiv (Fin.last n) Q) ≠ 0) :
    Module.rank ℤ (activeLattice F) ≤ (n : Cardinal) := by
  refine rank_span_int_le_of_independent_bound fun s v hvS hvind => ?_
  exact card_le_of_autonomousRelation hρ hindep hF Q hQ hz₀ hsep v hvS
    (linearIndependent_complex_of_int hvind)

end

end GaloisForLFunctions.HTGeometry
