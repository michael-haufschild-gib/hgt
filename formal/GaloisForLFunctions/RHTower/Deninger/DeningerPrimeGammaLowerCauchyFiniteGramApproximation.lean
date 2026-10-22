import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeGammaLowerCauchyTotality

/-!
# Simultaneous finite lower prime--Gamma Cauchy approximation

Lower prime--Gamma Cauchy totality is strengthened here from one-vector reachability to a genuine
four-channel boundary carrier.  Any four regular Xi--Weil Cauchy-core vectors admit simultaneous
finite lower-source approximants, and every mixed Hermitian Gram entry converges with them.

This is deliberately not a positivity theorem: it preserves orientation and all cross terms rather
than replacing them with scalar or diagonal energy.  It supplies the finite-source input required
by a non-scalar P/C1 boundary construction.
-/

open Complex Metric Set Filter Topology

namespace RHTower

noncomputable section

/-- Four Xi--Weil Cauchy-core vectors can be approximated simultaneously by finite linear
combinations of literal lower prime--Gamma Cauchy atoms. -/
theorem exists_lowerCauchy_fourTuple_approx
    (v : Fin 4 → lp (fun _ : XiZeroCopy => ℂ) 2)
    (hv : ∀ i, v i ∈ xiWeilCauchyHilbertSubspace) :
    ∃ a : ℕ → Fin 4 → lp (fun _ : XiZeroCopy => ℂ) 2,
      (∀ n i, a n i ∈ deningerPrimeGammaLowerCauchyAlgebraicSubspace) ∧
      ∀ i, Tendsto (fun n => a n i) atTop (nhds (v i)) := by
  have hclosure : ∀ i, v i ∈ closure (deningerPrimeGammaLowerCauchyAlgebraicSubspace :
      Set (lp (fun _ : XiZeroCopy => ℂ) 2)) := by
    intro i
    change v i ∈ deningerPrimeGammaLowerCauchyAlgebraicSubspace.topologicalClosure
    rw [deningerPrimeGammaLowerCauchyHilbertSubspace_eq_xiWeilCauchyHilbertSubspace]
    exact hv i
  choose a haMem haDist using fun n i =>
    Metric.mem_closure_iff.mp (hclosure i) (1 / ((n + 1 : ℕ) : ℝ))
      (by positivity : 0 < 1 / ((n + 1 : ℕ) : ℝ))
  refine ⟨a, haMem, fun i => Metric.tendsto_atTop.2 ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn => ?_⟩
  calc
    dist (a n i) (v i) = dist (v i) (a n i) := dist_comm _ _
    _ < 1 / ((n + 1 : ℕ) : ℝ) := haDist n i
    _ ≤ 1 / ((N + 1 : ℕ) : ℝ) := by gcongr
    _ < ε := by simpa only [Nat.cast_add, Nat.cast_one] using hN

/-- The simultaneous lower-source carrier preserves every labelled mixed Gram term in the
limit.  Thus four-channel orientation is retained without a scalar boundary reader. -/
theorem exists_lowerCauchy_fourTuple_gramApprox
    (v : Fin 4 → lp (fun _ : XiZeroCopy => ℂ) 2)
    (hv : ∀ i, v i ∈ xiWeilCauchyHilbertSubspace) :
    ∃ a : ℕ → Fin 4 → lp (fun _ : XiZeroCopy => ℂ) 2,
      (∀ n i, a n i ∈ deningerPrimeGammaLowerCauchyAlgebraicSubspace) ∧
      (∀ i, Tendsto (fun n => a n i) atTop (nhds (v i))) ∧
      ∀ i j, Tendsto (fun n => inner ℂ (a n i) (a n j)) atTop
        (nhds (inner ℂ (v i) (v j))) := by
  obtain ⟨a, haMem, ha⟩ := exists_lowerCauchy_fourTuple_approx v hv
  refine ⟨a, haMem, ha, fun i j => ?_⟩
  have hpair : Tendsto (fun n => (a n i, a n j)) atTop (nhds (v i, v j)) :=
    (ha i).prodMk_nhds (ha j)
  exact (continuous_inner.tendsto _).comp hpair

end

end RHTower
