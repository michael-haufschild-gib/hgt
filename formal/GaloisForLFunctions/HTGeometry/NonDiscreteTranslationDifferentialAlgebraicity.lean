import GaloisForLFunctions.HTGeometry.EllipticMeroFieldDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.SmallTranslationDerivInvariance
import GaloisForLFunctions.HTGeometry.RankTwoRealDependentPeriods

/-!
# A non-discrete period group forbids poles, and forces differential algebraicity

A meromorphic function in normal form whose periods form a non-discrete group has no poles at all:
a pole would be reproduced at every period, and periods accumulate at `0`, contradicting the
isolation of poles.  The function is therefore entire, and the corpus's small-translation law
applies verbatim.

Combined with the elliptic case this removes the last restriction from the two-shift law in the
global meromorphic differential field: `ℚ`-independence of the two shifts suffices, since two
`ℚ`-independent shifts are either `ℝ`-independent (elliptic branch) or `ℝ`-dependent
(non-discrete branch).

* **`analyticAt_of_meromorphicNFOn_periodic_of_not_discrete`**;
* **`differentiallyAlgebraic_of_meromorphicNFOn_periodic_of_not_discrete`**;
* **`differentialAlgebraicOver_of_translation_fixed_rat`** — the two-shift law for
  `ℚ`-independent shifts.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance nonDiscreteTranslationDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance nonDiscreteTranslationDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance nonDiscreteTranslationRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

/-! ## Non-discrete periods exclude poles -/

/-- **A non-discrete period group forbids poles.**  A pole is reproduced at every period, and a
non-discrete group has nonzero periods arbitrarily close to `0`, so the poles would accumulate —
impossible, since a meromorphic function is analytic on a punctured neighbourhood of each point. -/
theorem analyticAt_of_meromorphicNFOn_periodic_of_not_discrete {F : ℂ → ℂ}
    (hNF : MeromorphicNFOn F (Set.univ : Set ℂ)) {L : Submodule ℤ ℂ}
    (hper : ∀ p ∈ L, Function.Periodic F p) (hnd : ¬ DiscreteTopology L) (z : ℂ) :
    AnalyticAt ℂ F z := by
  by_contra hna
  have hNFz : MeromorphicNFAt F z := hNF (Set.mem_univ z)
  have hord : meromorphicOrderAt F z < 0 := by
    rcases lt_or_ge (meromorphicOrderAt F z) 0 with h | h
    · exact h
    · exact absurd (hNFz.meromorphicOrderAt_nonneg_iff_analyticAt.mp h) hna
  have hev : ∀ᶠ u in 𝓝[≠] z, AnalyticAt ℂ F u := hNFz.meromorphicAt.eventually_analyticAt
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  obtain ⟨p, hpL, hpne, hptend⟩ := exists_small_nonzero_of_not_discrete_intSubmodule L hnd
  obtain ⟨n, hn⟩ := (NormedAddGroup.tendsto_nhds_zero.mp hptend ε hε).exists
  have hdist : dist (z + p n) z < ε := by
    rw [dist_eq_norm]
    simpa using hn
  have hne : z + p n ∈ ({z}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    exact hpne n (by linear_combination hcon)
  have hzp : AnalyticAt ℂ F (z + p n) := hball hdist hne
  have hordp : 0 ≤ meromorphicOrderAt F (z + p n) :=
    hzp.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr hzp
  have hordeq : meromorphicOrderAt F (z + p n) = meromorphicOrderAt F z :=
    meromorphicOrderAt_add_eq_of_eventually_periodic
      (Filter.Eventually.of_forall fun u => hper (p n) (hpL n) u)
  rw [hordeq] at hordp
  exact absurd hord (not_lt.mpr hordp)

/-- **A normal-form meromorphic function with a non-discrete period group is differentially
algebraic.**  It is entire by pole exclusion, and the corpus's small-translation law then produces
a constant-coefficient annihilator. -/
theorem differentiallyAlgebraic_of_meromorphicNFOn_periodic_of_not_discrete {ι : Type*}
    {F : ℂ → ℂ} (hNF : MeromorphicNFOn F (Set.univ : Set ℂ)) (w : ι → ℂ)
    (hper : ∀ i, Function.Periodic F (w i))
    (hnd : ¬ DiscreteTopology (Submodule.span ℤ (Set.range w))) :
    DifferentiallyAlgebraic F := by
  have hspan : ∀ p ∈ Submodule.span ℤ (Set.range w), Function.Periodic F p :=
    periodic_of_mem_span_range w hper
  have han : ∀ z, AnalyticAt ℂ F z :=
    analyticAt_of_meromorphicNFOn_periodic_of_not_discrete hNF hspan hnd
  exact differentiallyAlgebraic_of_quasiperiods_of_not_discrete
    (fun z => (han z).differentiableAt) w (fun _ => 1)
    (fun i z => by rw [one_mul]; exact hper i z) hnd

/-! ## The two-shift law without the `ℝ`-independence restriction -/

/-- **The `ℝ`-dependent branch of the two-shift law in the meromorphic field.** -/
theorem differentialAlgebraicOver_of_translation_fixed_realDependent
    {α β : ℂ} (hQ : LinearIndependent ℚ ![α, β]) (hdep : ¬ LinearIndependent ℝ ![α, β])
    {x : meroField (Set.univ : Set ℂ)}
    (hα : addTranslationMeroEquiv α x = x) (hβ : addTranslationMeroEquiv β x = x) :
    DifferentialAlgebraicOver (RatFunc ℂ) x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (analyticSubring Set.univ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨A, hA, hAa⟩ := a.2
  obtain ⟨B, hB, hBb⟩ := b.2
  refine differentialAlgebraicOver_of_differentiallyAlgebraic_toMeromorphicNFOn
    hb0 hA hB hAa hBb ?_
  set H : ℂ → ℂ := fun z => A z / B z with hHdef
  have hHmer : MeromorphicOn H (Set.univ : Set ℂ) :=
    hA.meromorphicOn.div hB.meromorphicOn
  have hNF : MeromorphicNFOn (toMeromorphicNFOn H (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
    meromorphicNFOn_toMeromorphicNFOn _ _
  have hperα : Function.Periodic (toMeromorphicNFOn H (Set.univ : Set ℂ)) α :=
    periodic_toMeromorphicNFOn_of_eventually_punctured_meromorphic hHmer α
      (fun z => fraction_eventually_periodic_of_addTranslationMeroEquiv_fixed α hb0 hB hAa hBb hα z)
  have hperβ : Function.Periodic (toMeromorphicNFOn H (Set.univ : Set ℂ)) β :=
    periodic_toMeromorphicNFOn_of_eventually_punctured_meromorphic hHmer β
      (fun z => fraction_eventually_periodic_of_addTranslationMeroEquiv_fixed β hb0 hB hAa hBb hβ z)
  refine differentiallyAlgebraic_of_meromorphicNFOn_periodic_of_not_discrete hNF ![α, β] ?_ ?_
  · intro i
    fin_cases i
    · simpa using hperα
    · simpa using hperβ
  · exact not_discrete_intSpan_fin_two_of_not_linearIndependent_real ![α, β] hQ hdep

/-- **The two-shift law for `ℚ`-independent shifts.**  A meromorphic germ fixed by two
`ℚ`-independent translations is differentially algebraic over the rational coordinate field: the
`ℝ`-independent case is elliptic, the `ℝ`-dependent case has a non-discrete period group. -/
theorem differentialAlgebraicOver_of_translation_fixed_rat
    {α β : ℂ} (hQ : LinearIndependent ℚ ![α, β])
    {x : meroField (Set.univ : Set ℂ)}
    (hα : addTranslationMeroEquiv α x = x) (hβ : addTranslationMeroEquiv β x = x) :
    DifferentialAlgebraicOver (RatFunc ℂ) x := by
  by_cases hR : LinearIndependent ℝ ![α, β]
  · exact differentialAlgebraicOver_of_translation_fixed hR hα hβ
  · exact differentialAlgebraicOver_of_translation_fixed_realDependent hQ hR hα hβ

end

end GaloisForLFunctions.HTGeometry
