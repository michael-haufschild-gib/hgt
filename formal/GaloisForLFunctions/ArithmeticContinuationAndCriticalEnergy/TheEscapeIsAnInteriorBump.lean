import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampedMobiusCriticalEnergy
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedMoebiusFirstMomentAndChebyshevTangentBridge
import GaloisForLFunctions.BezoutValuationIncidence.DampedChebyshevTangentFormOfTheReceiver
import Mathlib.Analysis.Convex.Function

/-!
# The escape is an interior bump

Transport has been treated as a walk from one admitted end of the damping range towards a
forbidden one.  That picture is incomplete: *both* ends of the range are paid, uniformly in the
observation horizon.  At half damping the energy is bounded unconditionally, and at zero damping
the source collapses to the constant one, so for every horizon

`E_T(ε) → Σ_{n ≤ T} 1/(n(n+1)) ≤ 1`  as `ε ↓ 0`

(`tendsto_dampedMobiusEnergy_nhdsGT_zero`, `pronicMass_le_one`).  The escape that the Riemann
hypothesis forbids is therefore an **interior** phenomenon: a bump sitting strictly between two
paid ends, whose location drifts to zero as the horizon grows.

Two consequences.

* A horizon-wise *shape* hypothesis suffices: if no horizon's energy exceeds the larger of its two
  end values, every damping is admitted and RH follows
  (`riemannHypothesis_of_no_interior_bump`).  Convexity in the damping is one such hypothesis
  (`riemannHypothesis_of_convexOn_dampedMobiusEnergy`), and convexity is a statement about the
  second damping derivative of the energy — the pairing of the source with the *second* tangent
  against the tangent energy — not about any norm.
* Conversely, failure of RH forces interior bumps of unbounded height at a fixed interior damping
  (`exists_unbounded_interior_bump_of_not_riemannHypothesis`), while both ends stay bounded.  So an
  estimate that only improves the endpoint values cannot decide the question: what has to be
  excluded is a shape.
-/

open Set Filter Finset Topology RHTower GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The zero-damping end is paid, uniformly in the horizon -/

/-- The energy of the constant-one source to horizon `T`: the pronic mass, at most one. -/
theorem pronicMass_le_one (T : ℕ) :
    (∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ 1 := by
  rw [sum_Icc_pronic_mass]
  have h : (0 : ℝ) ≤ 1 / ((T : ℝ) + 1) := by positivity
  linarith

/-- **The zero-damping limit of the critical energy is the pronic mass.**  The damped Möbius
source collapses to the constant one, so each horizon's energy returns to a value below one. -/
theorem tendsto_dampedMobiusEnergy_nhdsGT_zero (T : ℕ) :
    Tendsto (fun ε => dampedMobiusEnergy ε T) (𝓝[>] 0)
      (𝓝 (∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1)))) := by
  unfold dampedMobiusEnergy pmPowerDampedDivisorDiscreteEnergy
  refine tendsto_finsetSum _ fun n hn => ?_
  have h := tendsto_pmPowerDampedCenteredDivisorPrefix_zero (mem_Icc.mp hn).1
  simpa using (h.pow 2).div_const ((n : ℝ) * ((n : ℝ) + 1))

/-! ## §2. A shape hypothesis closes the problem -/

/-- **No interior bump gives the Riemann hypothesis.**  If for every horizon the energy at an
interior damping never exceeds the larger of the value at a smaller damping and the value at half
damping, then both paid ends bound the whole range, every damping is admitted, and RH follows. -/
theorem riemannHypothesis_of_no_interior_bump
    (h : ∀ (T : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 → ∀ δ : ℝ, 0 < δ → δ < ε →
      dampedMobiusEnergy ε T ≤
        max (dampedMobiusEnergy δ T) (dampedMobiusEnergy (1 / 2) T)) :
    RiemannHypothesis := by
  obtain ⟨B, hB⟩ := admits_dampedMobiusEnergy_of_half_le (le_refl (1 / 2 : ℝ))
  have hadm : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Admits dampedMobiusEnergy ε := by
    intro ε hε hε2
    refine ⟨max 1 (max B 0), fun T => ?_⟩
    have hlim : Tendsto (fun δ => max (dampedMobiusEnergy δ T) (dampedMobiusEnergy (1 / 2) T))
        (𝓝[>] 0) (𝓝 (max (∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1)))
          (dampedMobiusEnergy (1 / 2) T))) :=
      (tendsto_dampedMobiusEnergy_nhdsGT_zero T).max tendsto_const_nhds
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        dampedMobiusEnergy ε T ≤
          max (dampedMobiusEnergy δ T) (dampedMobiusEnergy (1 / 2) T) := by
      filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ using h T ε hε hε2 δ hδ.1 hδ.2
    have hstep := ge_of_tendsto hlim hev
    refine hstep.trans (max_le_max (pronicMass_le_one T) ?_)
    exact (hB T).trans (le_max_left B 0)
  refine riemannHypothesis_iff_cofinallyAdmits.mpr fun δ hδ => ?_
  have hmin : 0 < min δ (1 / 2 : ℝ) := lt_min hδ (by norm_num)
  refine ⟨min δ (1 / 2) / 2, by positivity, by linarith [min_le_left δ (1 / 2 : ℝ)], ?_⟩
  exact hadm _ (by positivity) (by linarith [min_le_right δ (1 / 2 : ℝ)])

/-- **Convexity in the damping gives the Riemann hypothesis.**  A convex function on the damping
range is bounded by its end values, and both ends are paid. -/
theorem riemannHypothesis_of_convexOn_dampedMobiusEnergy
    (h : ∀ T : ℕ, ConvexOn ℝ (Ioc (0 : ℝ) (1 / 2)) (fun ε => dampedMobiusEnergy ε T)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_no_interior_bump fun T ε hε hε2 δ hδ hδε => ?_
  have hδ2 : δ ≤ 1 / 2 := le_of_lt (lt_of_lt_of_le hδε hε2)
  have hseg : ε ∈ segment ℝ δ (1 / 2 : ℝ) := by
    rw [segment_eq_Icc hδ2]
    exact ⟨le_of_lt hδε, hε2⟩
  exact ConvexOn.le_on_segment (h T) (mem_Ioc.mpr ⟨hδ, hδ2⟩)
    (mem_Ioc.mpr ⟨by norm_num, le_rfl⟩) hseg

/-! ## §3. Failure of the hypothesis is a bump, not an endpoint defect -/

/-- **Failure of the Riemann hypothesis is an interior bump of unbounded height.**  There is a
damping strictly inside `(0, ½)` whose energy exceeds every constant over the horizons, while half
damping stays below one fixed bound and zero damping returns below one at every horizon.  So no
improvement of the end values can decide the question. -/
theorem exists_unbounded_interior_bump_of_not_riemannHypothesis (h : ¬ RiemannHypothesis) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ∀ C : ℝ, ∃ T : ℕ, C < dampedMobiusEnergy ε T := by
  rw [riemannHypothesis_iff_cofinallyAdmits, CofinallyAdmits] at h
  push Not at h
  obtain ⟨δ, hδ, hno⟩ := h
  set ε : ℝ := min δ (1 / 2) / 2 with hεdef
  have hmin : 0 < min δ (1 / 2 : ℝ) := lt_min hδ (by norm_num)
  have hε0 : 0 < ε := by positivity
  have hεδ : ε < δ := by
    have := min_le_left δ (1 / 2 : ℝ)
    simp only [hεdef]
    linarith
  have hε2 : ε < 1 / 2 := by
    have := min_le_right δ (1 / 2 : ℝ)
    simp only [hεdef]
    linarith
  refine ⟨ε, hε0, hε2, fun C => ?_⟩
  have hnotadm : ¬ Admits dampedMobiusEnergy ε := hno ε hε0 hεδ
  rw [Admits] at hnotadm
  push Not at hnotadm
  obtain ⟨T, hT⟩ := hnotadm C
  exact ⟨T, hT⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
