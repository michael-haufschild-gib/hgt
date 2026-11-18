import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.CoordinateArrangementCounts
import GaloisForLFunctions.HTGeometry.RydbergHardExclusionCumulants

/-!
# Finite-alphabet realization of blockade occupation laws

Mark an atom occupied when its letter is zero. Andrusov's face count then
weights each independent configuration by the number of ways to decorate
its unoccupied sites. A uniform law on admissible words induces a concrete
law on the corpus's Rydberg configurations.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open _root_.HTGeometry Finset
open scoped Classical
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Actual words realizing any specified family of independent configurations. -/
def blockadeWords (q : ℕ) (S : Finset (RydbergIndependentConfiguration G)) :=
  arrangementWords (fun _ : V => ({0} : Finset (Fin (q+2)))) (S.image (·.sites))

/-- Each unoccupied site has `q+1` possible decorations. -/
def decorationCount (q : ℕ) (C : RydbergIndependentConfiguration G) : ℕ :=
  (q+1) ^ (Fintype.card V - C.sites.card)

private theorem sites_injective :
    Function.Injective (fun C : RydbergIndependentConfiguration G => C.sites) := by
  rintro ⟨s, hs⟩ ⟨t, ht⟩ h
  cases h
  rfl

/-- Exact pushforward counts for arbitrary events of independent configurations. -/
theorem card_blockadeWords (q : ℕ) (S : Finset (RydbergIndependentConfiguration G)) :
    (blockadeWords G q S).card = ∑ C ∈ S, decorationCount G q C := by
  unfold blockadeWords
  rw [card_pointArrangement, sum_image (fun _ _ _ _ h => sites_injective G h)]
  simp [decorationCount]

private def oneOccupied (v : V) : RydbergIndependentConfiguration G :=
  ⟨{v}, by simp [SimpleGraph.IsIndepSet]⟩

private def vacant : RydbergIndependentConfiguration G := ⟨∅, by simp [SimpleGraph.IsIndepSet]⟩

private theorem partition_pos (q : ℕ) :
    0 < (blockadeWords G q univ).card := by
  rw [card_blockadeWords]
  exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨vacant G, mem_univ _, by dsimp [decorationCount]; positivity⟩

/-- Pushforward of uniform counting measure on allowed marked words. -/
def blockadeWordLaw (q : ℕ) : RydbergOutcomeLaw G where
  weight C := (decorationCount G q C : ℝ) / (blockadeWords G q univ).card
  nonnegative _ := by positivity
  normalized := by
    rw [← sum_div, card_blockadeWords, Nat.cast_sum]
    exact div_self (by exact_mod_cast (card_blockadeWords G q univ ▸ partition_pos G q).ne')

/-- Event probabilities are exact quotients of finite point counts. -/
theorem blockadeWordLaw_event (q : ℕ) (S : Finset (RydbergIndependentConfiguration G)) :
    ∑ C ∈ S, (blockadeWordLaw G q).weight C =
      (blockadeWords G q S).card / ((blockadeWords G q univ).card : ℝ) := by
  simp only [blockadeWordLaw, ← sum_div, card_blockadeWords, Nat.cast_sum]

/-- Binary words give a uniform law on all independent configurations. -/
theorem blockadeWordLaw_binary (C : RydbergIndependentConfiguration G) :
    (blockadeWordLaw G 0).weight C = (Fintype.card (RydbergIndependentConfiguration G) : ℝ)⁻¹ := by
  simp [blockadeWordLaw, card_blockadeWords, decorationCount]

/-- The one-site occupation probability is a face-stratum count divided by the full count. -/
theorem blockadeWordLaw_meanOccupation (q : ℕ) (v : V) :
    (blockadeWordLaw G q).meanOccupation v =
      (blockadeWords G q (univ.filter (fun C => v ∈ C.sites))).card /
        ((blockadeWords G q univ).card : ℝ) := by
  rw [← blockadeWordLaw_event, sum_filter]
  unfold RydbergOutcomeLaw.meanOccupation
  refine sum_congr rfl fun C _ => ?_
  by_cases h : v ∈ C.sites <;> simp [rydbergOccupationIndicator, h]

/-- Every site has positive occupancy because its singleton is admissible. -/
theorem blockadeWordLaw_meanOccupation_pos (q : ℕ) (v : V) :
    0 < (blockadeWordLaw G q).meanOccupation v := by
  rw [blockadeWordLaw_meanOccupation]
  apply div_pos _ (by exact_mod_cast partition_pos G q)
  rw [card_blockadeWords]
  exact_mod_cast (sum_pos' (fun _ _ => Nat.zero_le _)
    ⟨oneOccupied G v, by simp [oneOccupied], by dsimp [decorationCount]; positivity⟩ :
      0 < ∑ C ∈ univ.filter (fun C : RydbergIndependentConfiguration G => v ∈ C.sites),
        decorationCount G q C)

/-- Every blockaded edge has strictly negative connected spin correlation for this law. -/
theorem blockadeWordLaw_strict_anticorrelation (q : ℕ) (e : RydbergBlockedPair G) :
    (blockadeWordLaw G q).connectedSpinCorrelator e.left e.right < 0 := by
  rw [RydbergOutcomeLaw.connectedSpinCorrelator_blocked]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num)
    (blockadeWordLaw_meanOccupation_pos G q e.left)) (blockadeWordLaw_meanOccupation_pos G q e.right)

/-- The empty configuration gives every site positive vacancy probability. -/
theorem blockadeWordLaw_meanOccupation_lt_one (q : ℕ) (v : V) :
    (blockadeWordLaw G q).meanOccupation v < 1 := by
  rw [← (blockadeWordLaw G q).normalized]
  unfold RydbergOutcomeLaw.meanOccupation
  apply sum_lt_sum
  · intro C _
    by_cases hv : v ∈ C.sites <;> simp [rydbergOccupationIndicator,hv,(blockadeWordLaw G q).nonnegative]
  · refine ⟨vacant G,mem_univ _,?_⟩
    simp only [rydbergOccupationIndicator,vacant, notMem_empty,if_false,mul_zero]
    apply div_pos (by dsimp [decorationCount]; positivity) (by exact_mod_cast partition_pos G q)

/-- The entire clique cumulant hierarchy is a ratio of finite point counts. -/
theorem blockadeWordLaw_clique_cumulant (q : ℕ) (K : RydbergBlockedClique G) (s : Finset K.sites) :
    (blockadeWordLaw G q).blockedCliqueOccupationCumulant K s =
      (-1:ℝ)^(s.card-1) * (s.card-1).factorial *
        ((∏ i ∈ s, ((blockadeWords G q (univ.filter (fun C => (i:V) ∈ C.sites))).card : ℝ)) /
          ((blockadeWords G q univ).card : ℝ)^s.card) := by
  rw [RydbergOutcomeLaw.blockedCliqueOccupationCumulant_eq]
  simp only [blockadeWordLaw_meanOccupation,prod_div_distrib,prod_const]

/-- Every clique cumulant has its strict alternating sign at every order. -/
theorem blockadeWordLaw_clique_cumulant_sign (q : ℕ) (K : RydbergBlockedClique G)
    (s : Finset K.sites) :
    0 < (-1:ℝ)^(s.card-1) * (blockadeWordLaw G q).blockedCliqueOccupationCumulant K s := by
  rw [RydbergOutcomeLaw.blockedCliqueOccupationCumulant_eq]
  have hs : (-1:ℝ)^(s.card-1) * (-1:ℝ)^(s.card-1) = 1 := by rw [← mul_pow]; simp
  rw [← mul_assoc, ← mul_assoc,hs,one_mul]
  exact mul_pos (by exact_mod_cast Nat.factorial_pos _) (prod_pos fun i _ => blockadeWordLaw_meanOccupation_pos G q i)

#print axioms blockadeWordLaw_binary
#print axioms blockadeWordLaw_strict_anticorrelation
#print axioms blockadeWordLaw_meanOccupation_lt_one
#print axioms blockadeWordLaw_clique_cumulant_sign

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
