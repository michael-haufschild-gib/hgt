/-
# No finite atomic spectral trace represents the xi logarithmic derivative

A finite-dimensional spectral model has a logarithmic characteristic determinant whose
resolvent trace is a finite weighted sum of simple poles.  The actual completed-zeta
logarithmic derivative has a simple pole at every distinct xi zero, and the xi divisor is
infinite.  Hence no finite atomic resolvent trace can equal `xi'/xi` globally.

The theorem is intentionally exact.  It rules out only finite-dimensional / finite-atomic
realizations of the logarithmic derivative, not infinite-dimensional Hilbert--Polya, Connes,
or de Branges programs.
-/
import GaloisForLFunctions.RHTower.XiLogDerivNonholonomic

open Complex Set Filter Topology Finset

namespace RHTower

noncomputable section

/-- A finite atomic resolvent trace with arbitrary complex weights.  Repeated eigenvalues may
be encoded in the weights, as in the logarithmic derivative of a characteristic polynomial. -/
def finiteSpectralTrace (S : Finset ℂ) (weight : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∑ ρ ∈ S, weight ρ / (s - ρ)

/-- Every finite spectral support misses at least one of the chosen distinct actual xi zeros. -/
theorem exists_xiZeroPoint_not_mem (S : Finset ℂ) :
    ∃ n : ℕ, xiZeroPoint n ∉ S := by
  by_contra h
  push Not at h
  have hsub : Set.range xiZeroPoint ⊆ (S : Set ℂ) := by
    rintro z ⟨n, rfl⟩
    exact h n
  have hfinite : (Set.range xiZeroPoint).Finite := S.finite_toSet.subset hsub
  exact (Set.infinite_range_of_injective xiZeroPoint_injective) hfinite

/-- A finite atomic trace is analytic away from its finite support. -/
theorem analyticAt_finiteSpectralTrace_of_not_mem
    (S : Finset ℂ) (weight : ℂ → ℂ) {ρ : ℂ} (hρ : ρ ∉ S) :
    AnalyticAt ℂ (finiteSpectralTrace S weight) ρ := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa [finiteSpectralTrace] using! (analyticAt_const :
      AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) ρ)
  | @insert q S hq ih =>
      have hρq : ρ ≠ q := by
        intro h
        subst q
        exact hρ (Finset.mem_insert_self ρ S)
      have hρS : ρ ∉ S := by
        intro hmem
        exact hρ (Finset.mem_insert_of_mem hmem)
      have hterm : AnalyticAt ℂ (fun s : ℂ => weight q / (s - q)) ρ :=
        analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hρq)
      rw [show finiteSpectralTrace (insert q S) weight =
          fun s => weight q / (s - q) + finiteSpectralTrace S weight s by
        funext s
        simp [finiteSpectralTrace, hq]]
      exact hterm.add (ih hρS)

/-- **Finite spectral-trace no-go for the actual completed zeta.**  There is no finite set of
spectral points and no choice of complex weights for which the finite atomic resolvent trace is
globally equal to `xi'/xi`. -/
theorem xi_logDeriv_ne_finiteSpectralTrace (S : Finset ℂ) (weight : ℂ → ℂ) :
    ¬ ∀ s : ℂ, logDeriv xi s = finiteSpectralTrace S weight s := by
  intro heq
  obtain ⟨n, hn⟩ := exists_xiZeroPoint_not_mem S
  let ρ := xiZeroPoint n
  have hρ : ρ ∉ S := hn
  have han : AnalyticAt ℂ (finiteSpectralTrace S weight) ρ :=
    analyticAt_finiteSpectralTrace_of_not_mem S weight hρ
  have hnonneg : 0 ≤ meromorphicOrderAt (finiteSpectralTrace S weight) ρ :=
    han.meromorphicOrderAt_nonneg
  have hcongr : finiteSpectralTrace S weight =ᶠ[𝓝[≠] ρ] logDeriv xi := by
    filter_upwards with z
    exact (heq z).symm
  rw [meromorphicOrderAt_congr hcongr,
    meromorphicOrderAt_logDeriv_xi_eq_neg_one (xiZeroPoint_eq_zero n)] at hnonneg
  have hlt : (((-1 : ℤ) : WithTop ℤ)) < 0 := WithTop.coe_lt_coe.mpr (by omega)
  exact (not_le_of_gt hlt) hnonneg

end

end RHTower
