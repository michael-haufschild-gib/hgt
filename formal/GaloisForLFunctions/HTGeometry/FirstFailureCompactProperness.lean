import GaloisForLFunctions.HTGeometry.FirstFailureSourceTomography

/-!
# Compact properness of permutation-averaged first-failure tomography

`Sym^k P([0,1])` is the quotient of `P([0,1])^k` by permutations of the sources, with
`P([0,1])` carrying the topology of weak convergence; it is compact.  Every observer coordinate
is a polynomial in finitely many continuous moment functionals.

**Theorem 8.1**: the observer `𝔚_k : Sym^k P([0,1]) → [0,1]^{ℕ_{≥1} × {1,…,k}}` is a closed
embedding — a homeomorphism onto its compact closed image — and a proper map; if the response
arrays of a sequence of source multisets converge coordinatewise, the limit array is the response
of a unique source multiset and the multisets converge weakly to it.
-/

open MeasureTheory Set Filter Topology Finset
open scoped unitInterval

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FirstFailure

variable {k : ℕ}

/-- Source tuples with the same multiset of laws. -/
def symSetoid (k : ℕ) : Setoid (Fin k → ProbabilityMeasure I) where
  r μ ν := univ.val.map μ = univ.val.map ν
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **`Sym^k P([0,1])`**: unordered `k`-tuples of probability laws on `[0, 1]`. -/
abbrev SymSource (k : ℕ) : Type := Quotient (symSetoid k)

theorem continuous_sourceMoment (n : ℕ) :
    Continuous fun μ : ProbabilityMeasure I => sourceMoment μ n :=
  ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact ⟨fun x : I => (x : ℝ) ^ n, by fun_prop⟩)

theorem continuous_observer :
    Continuous (observer : (Fin k → ProbabilityMeasure I) → ℕ × Fin k → ℝ) := by
  refine continuous_pi fun p => ?_
  have hs : ∀ i : Fin k, Continuous fun μ : Fin k → ProbabilityMeasure I =>
      survival (μ i) (p.1 + 1) := fun i =>
    ((continuous_sourceMoment _).comp (continuous_apply i)).pow 2
  change Continuous fun μ : Fin k → ProbabilityMeasure I =>
    ((k.factorial : ℕ) : ℝ)⁻¹ * ∑ τ, firstFailure (fun i => survival (μ i) (p.1 + 1)) τ p.2
  refine continuous_const.mul (continuous_finsetSum _ fun τ _ => ?_)
  exact (continuous_finsetProd _ fun j _ => hs (τ j)).mul (continuous_const.sub (hs (τ p.2)))

/-- The observer on unordered source multisets. -/
def symObserver : SymSource k → ℕ × Fin k → ℝ :=
  Quotient.lift observer fun μ ν (h : univ.val.map μ = univ.val.map ν) => by
    obtain ⟨τ, rfl⟩ := exists_perm_of_multiset_eq h
    exact observer_comp_perm ν τ

theorem continuous_symObserver : Continuous (symObserver (k := k)) := by
  unfold symObserver
  exact continuous_observer.quotient_lift _

theorem symObserver_injective : Function.Injective (symObserver (k := k)) := by
  intro a b hab
  induction a using Quotient.ind
  induction b using Quotient.ind
  exact Quotient.sound (observer_injective hab)

/-- **Theorem 8.1**: the observer is a closed embedding of the compact space
`Sym^k P([0,1])`. -/
theorem isClosedEmbedding_symObserver : IsClosedEmbedding (symObserver (k := k)) :=
  continuous_symObserver.isClosedEmbedding symObserver_injective

/-- **Theorem 8.1**: the observer is a homeomorphism onto its image, which is compact and
closed, and it is a proper map. -/
theorem symObserver_compact_properness :
    IsCompact (range (symObserver (k := k))) ∧ IsClosed (range (symObserver (k := k))) ∧
      IsProperMap (symObserver (k := k)) ∧
      Nonempty (SymSource k ≃ₜ range (symObserver (k := k))) :=
  ⟨isCompact_range continuous_symObserver, isClosedEmbedding_symObserver.isClosed_range,
    isClosedEmbedding_symObserver.isProperMap,
    ⟨isClosedEmbedding_symObserver.isEmbedding.toHomeomorph⟩⟩

/-- **Theorem 8.1** (stability): coordinatewise convergence of response arrays forces weak
convergence of the source multisets to the unique multiset producing the limit array. -/
theorem tendsto_of_symObserver_tendsto {m : ℕ → SymSource k} {w : ℕ × Fin k → ℝ}
    (h : Tendsto (fun j => symObserver (m j)) atTop (𝓝 w)) :
    ∃ m₀ : SymSource k, symObserver m₀ = w ∧ Tendsto m atTop (𝓝 m₀) ∧
      ∀ m' : SymSource k, symObserver m' = w → m' = m₀ := by
  have hw : w ∈ range (symObserver (k := k)) :=
    isClosedEmbedding_symObserver.isClosed_range.mem_of_tendsto h
      (Eventually.of_forall fun j => mem_range_self _)
  obtain ⟨m₀, rfl⟩ := hw
  refine ⟨m₀, rfl, ?_, fun m' hm' => symObserver_injective hm'⟩
  exact isClosedEmbedding_symObserver.isInducing.tendsto_nhds_iff.2 h

end GaloisForLFunctions.HTGeometry.FirstFailure
