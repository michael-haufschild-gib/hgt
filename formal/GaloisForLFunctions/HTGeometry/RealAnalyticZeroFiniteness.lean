import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# A real-analytic function has finitely many zeros on a compact set

The corpus already owns the complex statement on a ball.  The real statement on a compact subset of
a preconnected open set is proved here directly from isolated zeros and compactness, with no
meromorphic machinery: each point of the compact set has a punctured neighbourhood free of zeros,
and a finite subcover leaves only the finitely many centres.

This is the one-dimensional finiteness that an o-minimality argument would otherwise be invoked
for, in the case where the constraint is an *equation*.  Inequalities are not covered: the zero set
of an analytic function is finite, but the set where it is nonnegative need not be.

`AnalyticNullPreimage` already proves that the zero set of a *globally* real-analytic function is
countable, deriving local finiteness inside that proof.  What is exported here is the finiteness
statement itself, on a compact subset of a preconnected open domain.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {f : ℝ → ℝ} {U : Set ℝ}

/-- On a preconnected open set, a single nonzero value forbids local vanishing anywhere. -/
theorem eventually_ne_zero_of_analyticOnNhd (hUconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℝ f U) {x₀ : ℝ} (hx₀ : x₀ ∈ U) (hfx₀ : f x₀ ≠ 0) {u : ℝ} (hu : u ∈ U) :
    ∀ᶠ z in nhdsWithin u {u}ᶜ, f z ≠ 0 := by
  rcases (hf u hu).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    have hEq : Set.EqOn f 0 U :=
      hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn hu hzero
    exact hfx₀ (hEq hx₀)
  · exact hne

/-- **Finiteness of the real zero set on a compact subset.** -/
theorem finite_zeros_of_analyticOnNhd (hUconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℝ f U) {x₀ : ℝ} (hx₀ : x₀ ∈ U) (hfx₀ : f x₀ ≠ 0)
    {K : Set ℝ} (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ f ⁻¹' {0}).Finite := by
  classical
  -- a punctured zero-free neighbourhood at every point of `K`
  have hpunct : ∀ u ∈ K, ∃ V : Set ℝ, IsOpen V ∧ u ∈ V ∧ ∀ z ∈ V, z ≠ u → f z ≠ 0 := by
    intro u hu
    have hev := eventually_ne_zero_of_analyticOnNhd hUconn hf hx₀ hfx₀ (hKU hu)
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.mp hev
    exact ⟨W, hWopen, hWmem, fun z hz hzu => hWsub hz hzu⟩
  choose V hVopen hVmem hVzero using hpunct
  obtain ⟨t, htK, htcover⟩ :=
    hK.elim_nhds_subcover (fun u => if hu : u ∈ K then V u hu else Set.univ) (by
      intro u hu
      rw [dif_pos hu]
      exact (hVopen u hu).mem_nhds (hVmem u hu))
  refine Set.Finite.subset t.finite_toSet ?_
  rintro z ⟨hzK, hzf⟩
  obtain ⟨u, hut, hzV⟩ := Set.mem_iUnion₂.mp (htcover hzK)
  rw [dif_pos (htK u hut)] at hzV
  by_cases hzu : z = u
  · rw [hzu]; exact hut
  · exact absurd hzf (by simpa using hVzero u (htK u hut) z hzV hzu)

end GaloisForLFunctions.HTGeometry
