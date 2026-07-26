import GaloisForLFunctions.RHTower.MobiusCriticalFisherCutoffLimits
import GaloisForLFunctions.HTGeometry.HilbertSchmidt

/-!
# The conditional completed-source Ward budget

The squarefree source Ward law gives the closed critical commutator profile

```text
E_W(u) = 4[(2+u²)e^(-u) - 2(1+2u²)e^(-2u)] ,   E_W(u) ≤ 8(1 - e^(-u)) ,
```

with one-sided boundary density `E_W(u)/(2u) → 4`.  The completed-source consumer needs the same
budget for the anti-causal cutoff commutator itself.  Its two inputs are open — the direct
prime/Gamma--Sonin graph incidence and the nonexpansive source comparison — so they appear here as
explicit hypotheses; the implication they feed is proved unconditionally:

* entrywise (weak) convergence of Hilbert--Schmidt kernels is enough for lower semicontinuity of
  the Hilbert--Schmidt energy, `hsNormSq_le_of_tendsto_entries`;
* hence a completed family whose energies stay under the source Ward limit produces a limit kernel
  under the eight-unit window budget, `completedSourceWardBudget`;
* and any window profile under that budget has one-sided boundary density at most four,
  `eventually_div_two_mul_lt_of_le_eightMulCDF`.

Nothing here assumes the Riemann hypothesis or any property of `Xi`: the statements are about an
arbitrary family of kernels satisfying the two source hypotheses.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-! ### Weak lower semicontinuity of the Hilbert--Schmidt energy -/

/-- **Entrywise lower semicontinuity of the Hilbert--Schmidt energy.**  If the matrix entries of a
sequence of Hilbert--Schmidt kernels converge and their energies are eventually bounded by `B`,
then the limiting kernel has energy at most `B`.  Weak operator convergence on a total set gives
exactly this entrywise hypothesis. -/
theorem hsNormSq_le_of_tendsto_entries {ι : Type*} {K : ι × ι → ℂ} {A : ℕ → ι × ι → ℂ} {B : ℝ}
    (hK : HilbertSchmidt.IsHS K)
    (hentries : ∀ p, Tendsto (fun N => A N p) atTop (nhds (K p)))
    (hA : ∀ N, HilbertSchmidt.IsHS (A N))
    (hbound : ∀ᶠ N in atTop, HilbertSchmidt.hsNormSq (A N) ≤ B) :
    HilbertSchmidt.hsNormSq K ≤ B := by
  refine Summable.tsum_le_of_sum_le hK fun s => ?_
  -- every finite block of the limit is a limit of finite blocks
  have hfin : Tendsto (fun N => ∑ p ∈ s, ‖A N p‖ ^ 2) atTop
      (nhds (∑ p ∈ s, ‖K p‖ ^ 2)) := by
    refine tendsto_finsetSum s fun p _ => ?_
    exact ((hentries p).norm).pow 2
  refine le_of_tendsto hfin ?_
  filter_upwards [hbound] with N hN
  refine le_trans ?_ hN
  refine Summable.sum_le_tsum s (fun p _ => by positivity) ?_
  exact hA N

/-! ### The completed-source budget -/

/-- **Conditional completed-source Ward budget.**  A completed family of Hilbert--Schmidt kernels
whose entries converge to the anti-causal cutoff commutator kernel and whose energies do not exceed
the squarefree source Ward limit produces a limit kernel inside the eight-unit window budget.  The
two hypotheses are exactly the open inputs: graph incidence and nonexpansive source comparison. -/
theorem completedSourceWardBudget {ι : Type*} {u : ℝ} (hu : 0 ≤ u)
    {K : ι × ι → ℂ} {A : ℕ → ι × ι → ℂ}
    (hK : HilbertSchmidt.IsHS K)
    (hentries : ∀ p, Tendsto (fun N => A N p) atTop (nhds (K p)))
    (hA : ∀ N, HilbertSchmidt.IsHS (A N))
    (henergy : ∀ᶠ N in atTop,
      HilbertSchmidt.hsNormSq (A N) ≤ squarefreeMobiusCriticalFisherCutoffWardLimit u) :
    HilbertSchmidt.hsNormSq K ≤ 8 * (1 - Real.exp (-u)) :=
  le_trans (hsNormSq_le_of_tendsto_entries hK hentries hA henergy)
    (squarefreeMobiusCriticalFisherCutoffWardLimit_le_eight_mul_CDF hu)

/-! ### The four-unit boundary density -/

/-- The eight-unit window budget has one-sided boundary density exactly four after the native
factor two for the two commutator orientations. -/
theorem tendsto_eightMulCDF_div_two_mul :
    Tendsto (fun u : ℝ => 8 * (1 - Real.exp (-u)) / (2 * u))
      (nhdsWithin 0 (Ioi 0)) (nhds 4) := by
  have hbase := tendsto_mobiusCriticalExponentialCDF_div
  have h : Tendsto (fun u : ℝ => 4 * ((1 - Real.exp (-u)) / u))
      (nhdsWithin 0 (Ioi 0)) (nhds (4 * 1)) := hbase.const_mul 4
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : (0 : ℝ) < u := hu
  field_simp
  ring

/-- **Four-unit boundary density of the completed budget.**  Every window profile inside the
eight-unit budget has scaled boundary values eventually below `4 + ε`.  With
`completedSourceWardBudget` this is the conditional four-unit anti-causal statement. -/
theorem eventually_div_two_mul_lt_of_le_eightMulCDF {E : ℝ → ℝ}
    (hE : ∀ u : ℝ, 0 < u → E u ≤ 8 * (1 - Real.exp (-u))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u in nhdsWithin (0 : ℝ) (Ioi 0), E u / (2 * u) < 4 + ε := by
  have hlt : ∀ᶠ u in nhdsWithin (0 : ℝ) (Ioi 0),
      8 * (1 - Real.exp (-u)) / (2 * u) < 4 + ε :=
    tendsto_eightMulCDF_div_two_mul.eventually_lt_const (by linarith)
  filter_upwards [hlt, self_mem_nhdsWithin] with u hu hupos
  have hu' : (0 : ℝ) < u := hupos
  have hden : (0 : ℝ) < 2 * u := by linarith
  refine lt_of_le_of_lt ?_ hu
  exact div_le_div_of_nonneg_right (hE u hu') hden.le

end

end RHTower
