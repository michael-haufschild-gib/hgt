import GaloisForLFunctions.HTGeometry.RankTwoRealDependentPeriods
import GaloisForLFunctions.HTGeometry.EllipticHypertranscendenceFreeProof

/-!
# The period-rank law for meromorphic functions

Two `ℚ`-independent periods already force differential algebraicity.  The two configurations are
settled by different mechanisms and are collected here into one statement.

* the periods are `ℝ`-dependent: their integer span is a rank-two subgroup of a real line, hence not
  discrete, so arbitrarily small nonzero periods force the function to be constant;
* the periods are `ℝ`-independent: they span a lattice, the function is elliptic for it, and an
  elliptic function satisfies an algebraic differential equation of order one.

The contrapositive is the sharp form: **the period group of a hypertranscendental meromorphic
function on `ℂ` has `ℚ`-rank at most one** — any two of its periods are rationally dependent.  The
rank-three rigidity `meromorphicNF_constant_of_rankThree_periods` is the special case where a
rationally independent triple is available.

* **`differentiallyAlgebraic_of_rankTwo_periods`**, `differentiallyAlgebraic_of_two_periods`;
* **`rat_dependent_periods_of_hypertranscendental`** — the rank bound;
* `differentiallyAlgebraic_of_two_independent_periods` — the arbitrary-index form.
-/

namespace GaloisForLFunctions.HTGeometry

private theorem range_fin_two_pair {α : Type*} (v : Fin 2 → α) : Set.range v = {v 0, v 1} := by
  ext u
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

private theorem cons_fin_two_self {α : Type*} (v : Fin 2 → α) : ![v 0, v 1] = v := by
  funext i
  fin_cases i <;> rfl

/-- **The period-rank law.**  A meromorphic normal-form function invariant under the integer span of
two `ℚ`-independent complex numbers is differentially algebraic: if the two are `ℝ`-dependent the
period group is not discrete and the function is constant, and if they are `ℝ`-independent the
function is elliptic for the lattice they span. -/
theorem differentiallyAlgebraic_of_rankTwo_periods {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ) (v : Fin 2 → ℂ) (hv : LinearIndependent ℚ v)
    (hper : ∀ p ∈ Submodule.span ℤ (Set.range v), Function.Periodic f p) :
    DifferentiallyAlgebraic f := by
  by_cases hdep : LinearIndependent ℝ v
  · have hR : LinearIndependent ℝ ![v 0, v 1] := by rwa [cons_fin_two_self]
    have hlat : ∀ p ∈ (⟨v 0, v 1, hR⟩ : PeriodPair).lattice, Function.Periodic f p := by
      intro p hp
      refine hper p ?_
      rw [range_fin_two_pair]
      exact hp
    exact differentiallyAlgebraic_of_lattice_periodic_meromorphicNF ⟨v 0, v 1, hR⟩ hf hlat
  · exact differentiallyAlgebraic_of_const
      (meromorphicNF_constant_of_rankTwo_realDependent_periods f hf v hv hdep hper)

/-- The period-rank law for a pair of periods. -/
theorem differentiallyAlgebraic_of_two_periods {f : ℂ → ℂ} (hf : MeromorphicNFOn f Set.univ)
    {p q : ℂ} (hindep : LinearIndependent ℚ ![p, q])
    (hp : Function.Periodic f p) (hq : Function.Periodic f q) :
    DifferentiallyAlgebraic f := by
  refine differentiallyAlgebraic_of_rankTwo_periods hf ![p, q] hindep ?_
  refine periodic_of_mem_span_range ![p, q] (fun i => ?_)
  fin_cases i
  · exact hp
  · exact hq

/-- **The rank bound.**  Any two periods of a hypertranscendental meromorphic normal-form function
are rationally dependent: its period group has `ℚ`-rank at most one. -/
theorem rat_dependent_periods_of_hypertranscendental {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ) (hHT : Hypertranscendental f) {p q : ℂ}
    (hp : Function.Periodic f p) (hq : Function.Periodic f q) :
    ¬ LinearIndependent ℚ ![p, q] :=
  fun hindep => hHT (differentiallyAlgebraic_of_two_periods hf hindep hp hq)

/-- The period-rank law for an arbitrary rationally independent family with two distinct indices;
in particular a rationally independent triple of periods forces differential algebraicity, which is
the rank-three rigidity. -/
theorem differentiallyAlgebraic_of_two_independent_periods {ι : Type*} {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ) (w : ι → ℂ) (hw : LinearIndependent ℚ w)
    {i j : ι} (hij : i ≠ j)
    (hper : ∀ p ∈ Submodule.span ℤ (Set.range w), Function.Periodic f p) :
    DifferentiallyAlgebraic f := by
  refine differentiallyAlgebraic_of_rankTwo_periods hf (w ∘ ![i, j])
    (hw.comp _ (injective_cons_two hij)) (fun p hp => hper p ?_)
  refine Submodule.span_mono ?_ hp
  rintro _ ⟨k, rfl⟩
  exact ⟨![i, j] k, rfl⟩

/-- A hypertranscendental meromorphic normal-form function has no rationally independent family of
periods with two distinct indices. -/
theorem not_linearIndependent_periods_of_hypertranscendental {ι : Type*} {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ) (hHT : Hypertranscendental f) (w : ι → ℂ)
    {i j : ι} (hij : i ≠ j)
    (hper : ∀ p ∈ Submodule.span ℤ (Set.range w), Function.Periodic f p) :
    ¬ LinearIndependent ℚ w :=
  fun hw => hHT (differentiallyAlgebraic_of_two_independent_periods hf w hw hij hper)

end GaloisForLFunctions.HTGeometry
