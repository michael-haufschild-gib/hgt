import GaloisForLFunctions.SelbergClass.Primon.KestenTailGeometry
import GaloisForLFunctions.SelbergClass.Primon.KestenCharacterHardy

/-!
# A single prime generates the likelihood Hilbert space

Backward differences of one prime's normalized tails recover every even
character. Character truncations then recover every other prime likelihood.
Consequently the closed tail span is independent of the chosen prime and
coincides with both the even-character span and the full likelihood span.
-/

open Filter Topology
open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The algebraic span of all normalized tails at one fixed prime. -/
def kestenTailSpan (p : Nat.Primes) : Submodule ℝ SemicircleL2 :=
  Submodule.span ℝ (Set.range (kestenNormalizedTail p))

/-- The algebraic span of the even spectral characters. -/
def evenCharacterSpan : Submodule ℝ SemicircleL2 :=
  Submodule.span ℝ (Set.range (fun n => spectralCharacterVector (2 * n)))

/-- One prime's adjacent tails recover each even character by a finite linear combination. -/
theorem evenCharacter_mem_kestenTailSpan (p : Nat.Primes) (n : ℕ) :
    spectralCharacterVector (2 * n) ∈ kestenTailSpan p := by
  rw [← kestenNormalizedTail_innovation p n]
  exact (kestenTailSpan p).sub_mem
    (Submodule.subset_span (Set.mem_range_self n))
    ((kestenTailSpan p).smul_mem _ (Submodule.subset_span (Set.mem_range_self (n + 1))))

/-- Every prime likelihood is a limit of finite combinations of one fixed prime's tails. -/
theorem likelihood_mem_kestenTailClosure (p q : Nat.Primes) :
    kestenLikelihoodVector q ∈ (kestenTailSpan p).topologicalClosure := by
  apply isClosed_closure.mem_of_tendsto (tendsto_kestenCharacterTruncation q)
  apply Filter.Eventually.of_forall
  intro N
  apply subset_closure
  exact (kestenTailSpan p).sum_mem (fun n _ =>
    (kestenTailSpan p).smul_mem _ (evenCharacter_mem_kestenTailSpan p n))

/-- Every even character belongs to the closed prime-likelihood span. -/
theorem evenCharacter_mem_likelihoodHilbert (n : ℕ) :
    spectralCharacterVector (2 * n) ∈ KestenLikelihoodHilbert := by
  change spectralCharacterVector (2 * n) ∈
    closure (kestenLikelihoodMap.range : Set SemicircleL2)
  rw [← range_hardyLikelihoodEmbedding]
  exact ⟨lp.single 2 n (1 : ℝ), hardyLikelihoodEmbedding_single n⟩

private theorem likelihood_mem_likelihoodHilbert (p : Nat.Primes) :
    kestenLikelihoodVector p ∈ KestenLikelihoodHilbert := by
  apply subset_closure
  exact ⟨Finsupp.single p 1, by simp⟩

/-- Taking normalized character tails never leaves the likelihood Hilbert space. -/
theorem kestenNormalizedTail_mem_likelihoodHilbert (p : Nat.Primes) (N : ℕ) :
    kestenNormalizedTail p N ∈ KestenLikelihoodHilbert := by
  apply KestenLikelihoodHilbert.smul_mem
  apply KestenLikelihoodHilbert.sub_mem (likelihood_mem_likelihoodHilbert p)
  exact KestenLikelihoodHilbert.sum_mem (fun n _ =>
    KestenLikelihoodHilbert.smul_mem _ (evenCharacter_mem_likelihoodHilbert n))

/-- Every single prime's depth orbit is total in the entire likelihood Hilbert space. -/
theorem kestenTailSpan_closure (p : Nat.Primes) :
    (kestenTailSpan p).topologicalClosure = KestenLikelihoodHilbert := by
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    change kestenTailSpan p ≤ KestenLikelihoodHilbert
    apply Submodule.span_le.2
    rintro _ ⟨N, rfl⟩
    exact kestenNormalizedTail_mem_likelihoodHilbert p N
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨c, rfl⟩
    induction c using Finsupp.induction with
    | zero =>
        rw [map_zero]
        exact subset_closure (kestenTailSpan p).toAddSubmonoid.zero_mem
    | single_add q a c hq ha ih =>
        rw [map_add, kestenLikelihoodMap_single]
        exact (kestenTailSpan p).topologicalClosure.add_mem
          ((kestenTailSpan p).topologicalClosure.smul_mem a (likelihood_mem_kestenTailClosure p q)) ih

/-- The closed likelihood span is precisely the closed span of even characters. -/
theorem evenCharacterSpan_closure :
    evenCharacterSpan.topologicalClosure = KestenLikelihoodHilbert := by
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    change evenCharacterSpan ≤ KestenLikelihoodHilbert
    apply Submodule.span_le.2
    rintro _ ⟨n, rfl⟩
    exact evenCharacter_mem_likelihoodHilbert n
  · apply closure_minimal _ isClosed_closure
    have hlik (p : Nat.Primes) : kestenLikelihoodVector p ∈ evenCharacterSpan.topologicalClosure := by
      apply isClosed_closure.mem_of_tendsto (tendsto_kestenCharacterTruncation p)
      apply Filter.Eventually.of_forall
      intro N
      apply subset_closure
      exact evenCharacterSpan.sum_mem (fun n _ =>
        evenCharacterSpan.smul_mem _ (Submodule.subset_span (Set.mem_range_self n)))
    rintro _ ⟨c, rfl⟩
    induction c using Finsupp.induction with
    | zero =>
        rw [map_zero]
        exact subset_closure evenCharacterSpan.toAddSubmonoid.zero_mem
    | single_add p a c hp ha ih =>
        rw [map_add, kestenLikelihoodMap_single]
        exact evenCharacterSpan.topologicalClosure.add_mem
          (evenCharacterSpan.topologicalClosure.smul_mem a (hlik p)) ih

end
end GaloisForLFunctions.SelbergClass.Primon

