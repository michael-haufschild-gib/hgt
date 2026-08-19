import GaloisForLFunctions.HTGeometry.GammaMonomialOrbitLimit

/-!
# The orbit limit as a function, and its periodicity

The orbit series of `GammaMonomialOrbitLimit` is absolutely summable, so its sum is the limit of
`M(s+n)`.  Because that limit only depends on the orbit, the resulting function is `1`-periodic —
which is one of the two hypotheses of `eq_zero_of_periodic_of_vertical_decay`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The orbit limit of a Gamma monomial. -/
def gammaMonomialOrbitLimit {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) (s : ℂ) : ℂ :=
  gammaMonomial lam g s + ∑' j : ℕ, orbitTerm lam g s j

/-- **The orbit limit really is the limit along the orbit.** -/
theorem tendsto_gammaMonomial_orbit {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ)
    (hdeg : ∑ k, g k = 0) (hmom : ∑ k, (g k : ℂ) * lam k = 0) :
    ∃ Rb : ℝ, 1 ≤ Rb ∧ ∀ s : ℂ, (∑ j, |(lam j).re|) < s.re → Rb ≤ ‖s‖ →
      Tendsto (fun n : ℕ => gammaMonomial lam g (s + (n : ℂ))) atTop
        (nhds (gammaMonomialOrbitLimit lam g s)) := by
  obtain ⟨Rb, hRb, hsum⟩ := summable_orbitTerm lam g hdeg hmom
  refine ⟨Rb, hRb, fun s hs hsn => ?_⟩
  have habs : Summable (orbitTerm lam g s) := Summable.of_norm (hsum s hs hsn)
  have htend := habs.hasSum.tendsto_sum_nat
  have hconst : Tendsto (fun _ : ℕ => gammaMonomial lam g s) atTop
      (nhds (gammaMonomial lam g s)) := tendsto_const_nhds
  have hadd := hconst.add htend
  rw [gammaMonomialOrbitLimit]
  refine hadd.congr fun n => ?_
  exact (gammaMonomial_orbit_telescope lam g hs n).symm

/-- **The orbit limit is `1`-periodic.** -/
theorem gammaMonomialOrbitLimit_shift {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ)
    (hdeg : ∑ k, g k = 0) (hmom : ∑ k, (g k : ℂ) * lam k = 0) :
    ∃ Rb : ℝ, 1 ≤ Rb ∧ ∀ s : ℂ, (∑ j, |(lam j).re|) < s.re → Rb ≤ ‖s‖ →
      gammaMonomialOrbitLimit lam g (s + 1) = gammaMonomialOrbitLimit lam g s := by
  obtain ⟨Rb, hRb, htend⟩ := tendsto_gammaMonomial_orbit lam g hdeg hmom
  refine ⟨Rb, hRb, fun s hs hsn => ?_⟩
  have hs1 : (∑ j, |(lam j).re|) < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hsn1 : Rb ≤ ‖s + 1‖ := by
    have hre : 0 < s.re := by
      have hnn : (0 : ℝ) ≤ ∑ j, |(lam j).re| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    have h1 : ‖s‖ ≤ ‖s + 1‖ := by
      have := norm_le_norm_add_natCast hre 1
      simpa using this
    linarith
  have h1 := htend (s + 1) hs1 hsn1
  have h2 := htend s hs hsn
  have h3 : Tendsto (fun n : ℕ => gammaMonomial lam g (s + ((n + 1 : ℕ) : ℂ))) atTop
      (nhds (gammaMonomialOrbitLimit lam g s)) :=
    (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => gammaMonomial lam g (s + (n : ℂ)))
      1).mpr h2
  have h4 : Tendsto (fun n : ℕ => gammaMonomial lam g (s + 1 + (n : ℂ))) atTop
      (nhds (gammaMonomialOrbitLimit lam g s)) := by
    refine h3.congr fun n => ?_
    congr 1
    push_cast
    ring
  exact tendsto_nhds_unique h1 h4

end

end GaloisForLFunctions.HTGeometry
