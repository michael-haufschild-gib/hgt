import GaloisForLFunctions.HTGeometry.PeriodicAutonomousDescent
import GaloisForLFunctions.HTGeometry.PeriodSubgroupCyclic

/-!
# What a nonzero period decides

For a meromorphic normal-form function with at least one nonzero period the period layer and the
autonomy descent combine into a single dichotomy: either the function satisfies a nonzero autonomous
algebraic differential equation, or it is hypertranscendental, its period group is infinite cyclic,
and it satisfies no autonomous equation at all.  Nothing else can happen.

Two consequences of independent interest fall out, both strengthening existing corpus theorems from
"differentially algebraic" to "autonomously differentially algebraic":

* `exists_autonomousJet_of_rankTwo_periods` — two rationally independent periods;
* `exists_autonomousJet_of_lattice_periodic` — an elliptic function.

The classical relation `℘'² = 4℘³ − g₂℘ − g₃` is the order-one instance of the latter.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- An autonomous algebraic differential equation for `f`. -/
def HasAutonomousJetRelation (f : ℂ → ℂ) : Prop :=
  ∃ (n : ℕ) (R : MvPolynomial (Fin (n + 1)) ℂ), R ≠ 0 ∧
    ∀ z, eval (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) R = 0

theorem ne_zero_of_linearIndependent_pair {p q : ℂ} (h : LinearIndependent ℚ ![p, q]) : p ≠ 0 := by
  rw [linearIndependent_fin2] at h
  have := h.2 0
  simpa using (Ne.symm (by simpa using this))

/-! ### Two rationally independent periods force an autonomous equation -/

/-- **Two rationally independent periods give an autonomous equation.**  The period-rank law makes
the function differentially algebraic, and periodicity then eliminates the point slot. -/
theorem exists_autonomousJet_of_rankTwo_periods {f : ℂ → ℂ}
    (hNF : MeromorphicNFOn f Set.univ) {p q : ℂ} (hindep : LinearIndependent ℚ ![p, q])
    (hp : Function.Periodic f p) (hq : Function.Periodic f q) :
    HasAutonomousJetRelation f :=
  exists_autonomousJet_of_periodic (ne_zero_of_linearIndependent_pair hindep) hp
    (differentiallyAlgebraic_of_two_periods hNF hindep hp hq)

/-- **An elliptic function satisfies an autonomous equation.**  This upgrades
`differentiallyAlgebraic_of_lattice_periodic_meromorphicNF`: the equation can be taken free of the
point slot, as the Weierstrass relation is. -/
theorem exists_autonomousJet_of_lattice_periodic (L : PeriodPair) {f : ℂ → ℂ}
    (hNF : MeromorphicNFOn f Set.univ) (hper : ∀ p ∈ L.lattice, Function.Periodic f p) :
    HasAutonomousJetRelation f := by
  have hω : L.ω₁ ≠ 0 := by
    have h := L.indep
    rw [linearIndependent_fin2] at h
    have := h.2 0
    simpa using (Ne.symm (by simpa using this))
  exact exists_autonomousJet_of_periodic hω (hper _ L.ω₁_mem_lattice)
    (differentiallyAlgebraic_of_lattice_periodic_meromorphicNF L hNF hper)

/-! ### The dichotomy -/

/-- **What a nonzero period decides.**  A meromorphic normal-form function with a nonzero period
either satisfies a nonzero autonomous algebraic differential equation, or is hypertranscendental with
infinite cyclic period group and no autonomous equation whatsoever.  The two cases are exclusive and
exhaust the possibilities. -/
theorem autonomous_or_cyclic_hypertranscendental {f : ℂ → ℂ}
    (hNF : MeromorphicNFOn f Set.univ) (hper : periodSubgroup f ≠ ⊥) :
    HasAutonomousJetRelation f ∨
      (Hypertranscendental f ∧ ¬ HasAutonomousJetRelation f ∧
        ∃ ω : ℂ, ω ≠ 0 ∧ periodSubgroup f = AddSubgroup.zmultiples ω) := by
  have hex : ∃ c ∈ periodSubgroup f, c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hper ((AddSubgroup.eq_bot_iff_forall _).mpr hcon)
  obtain ⟨c, hc, hc0⟩ := hex
  by_cases hDA : DifferentiallyAlgebraic f
  · exact Or.inl (exists_autonomousJet_of_periodic hc0 hc hDA)
  · refine Or.inr ⟨hDA, ?_, ?_⟩
    · rintro ⟨n, R, hR, hRz⟩
      exact hDA (differentiallyAlgebraic_of_autonomousJet hR hRz)
    · obtain ⟨ω, hω⟩ := periodSubgroup_eq_zmultiples hNF hDA
      refine ⟨ω, ?_, hω⟩
      intro hω0
      apply hper
      rw [hω, hω0]
      simp

/-- The two cases really are exclusive. -/
theorem not_and_autonomous_hypertranscendental {f : ℂ → ℂ} :
    ¬ (HasAutonomousJetRelation f ∧ Hypertranscendental f) := by
  rintro ⟨⟨n, R, hR, hRz⟩, hHT⟩
  exact hHT (differentiallyAlgebraic_of_autonomousJet hR hRz)

end GaloisForLFunctions.HTGeometry
