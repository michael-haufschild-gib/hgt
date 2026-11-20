import GaloisForLFunctions.SelbergClass.Primon.SquarefreeCardinality.TheColdRealActivityRoots
import GaloisForLFunctions.SelbergClass.Primon.SquarefreeCardinality.TheSplittingOfTheCoalescedActivityRoot
import GaloisForLFunctions.FiniteFreeProbability.ShiftRegimeGaussianCapacity

/-!
# The first positive temperature parameter with real activity roots

The set of inverse temperatures giving only real roots is closed.
For at least three primes it avoids an interval immediately to the
right of zero, and it contains every sufficiently large parameter.
Its first positive point has a repeated negative root: simple real
roots would persist to its left.
-/

noncomputable section
open Polynomial Finset Filter Topology Set
namespace GaloisForLFunctions.SelbergClass.Primon

private theorem coeff_continuous (P : Finset ℕ) (j : ℕ) :
    Continuous (fun t => (squarefreeCardinalityPolynomial P t).coeff j) := by
  simp only [squarefreeCardinality_coeff]
  fun_prop

private theorem partition_ne_zero (P : Finset ℕ) (β : ℝ) : squarefreeCardinalityPolynomial P β ≠ 0 := by
  intro he
  have h := squarefree_real_root_neg P β 0 (by rw [he]; simp)
  exact lt_irrefl _ h

private theorem splitting_closed (P : Finset ℕ) :
    IsClosed {t : ℝ | (squarefreeCardinalityPolynomial P t).Splits} := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  exact _root_.HTGeometry.eventually_not_splits_of_coeff_limit
    (fun u => (squarefreeCardinality_degree P u).le) (squarefreeCardinality_degree P t).le
    (partition_ne_zero P t) (fun j => (coeff_continuous P j).continuousAt) ht

private theorem stable_at_simple_splitting {P : Finset ℕ} {t : ℝ}
    (hs : (squarefreeCardinalityPolynomial P t).Splits)
    (hd : (squarefreeCardinalityPolynomial P t).roots.Nodup) :
    ∀ᶠ u in 𝓝 t, (squarefreeCardinalityPolynomial P u).Splits := by
  by_contra h
  obtain ⟨u,hu,hn⟩ := exists_seq_forall_of_frequently (not_eventually.mp h)
  have H := _root_.FiniteFreeProbability.eventually_splits_of_tendsto_coeff (partition_ne_zero P t)
    (squarefreeCardinality_degree P t).le hd ((splits_iff_card_roots.mp hs).trans (squarefreeCardinality_degree P t))
    (p:=fun n => squarefreeCardinalityPolynomial P (u n)) (fun n => (squarefreeCardinality_degree P _).le)
    (fun j => (coeff_continuous P j).continuousAt.tendsto.comp hu)
  obtain ⟨n,h⟩ := H.exists
  exact hn n h

/-- Every prime set of cardinality at least three has a first positive
inverse temperature with a split activity polynomial. It lies strictly
below 2 log 3 and contains a multiple root on the negative real axis. -/
theorem first_positive_activity_collision (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p) (hm : 3 ≤ P.card) :
    ∃ b : ℝ, 0 < b ∧ b < 2*Real.log 3 ∧ (squarefreeCardinalityPolynomial P b).Splits ∧
      (∀ u : ℝ, 0 < u → u < b → ¬(squarefreeCardinalityPolynomial P u).Splits) ∧
      ∃ x : ℝ, x < 0 ∧ 2 ≤ (squarefreeCardinalityPolynomial P b).rootMultiplicity x := by
  classical
  let F := squarefreeCardinalityPolynomial P
  let C := 2*Real.log 3
  have hC : 0 < C := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  obtain ⟨δ,hδ,hhot⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (squarefreeCardinality_eventually_not_splits hp hm)
  have hsep {u : ℝ} (hu : 0 < u) (hs : (F u).Splits) : δ ≤ u :=
    le_of_not_gt (fun h => hhot ⟨hu,h⟩ hs)
  let S := Ici δ ∩ {t : ℝ | (F t).Splits}
  have hclosed : IsClosed S := isClosed_Ici.inter (splitting_closed P)
  have hcold := squarefree_cold_roots_of_log_three (β:=C) le_rfl P hp
  have hCS : C ∈ S := ⟨hsep hC hcold.1,hcold.1⟩
  have hne : S.Nonempty := ⟨C,hCS⟩
  have hl : δ ∈ lowerBounds S := fun _ hs => hs.1
  let b := sInf S
  have hmem : b ∈ S := hclosed.csInf_mem hne ⟨δ,hl⟩
  have hb : 0 < b := lt_of_lt_of_le (show 0 < δ from hδ) hmem.1
  have hmin {u : ℝ} (hu : 0 < u) (hub : u < b) (hs : (F u).Splits) : False :=
    hub.not_ge (csInf_le (show BddBelow S from ⟨δ,hl⟩) (show u ∈ S from ⟨hsep hu hs,hs⟩))
  have hd : ¬ (F b).roots.Nodup := by
    intro hd
    have H := stable_at_simple_splitting hmem.2 hd
    have H' : ∀ᶠ t in 𝓝[<] b, (F t).Splits := H.filter_mono nhdsWithin_le_nhds
    obtain ⟨a,ha,hs⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp H'
    obtain ⟨u,hu,hub⟩ := exists_between (max_lt (show a < b from ha) hb)
    exact hmin ((le_max_right a 0).trans_lt hu) hub (hs ⟨(le_max_left a 0).trans_lt hu,hub⟩)
  have hbC : b < C := lt_of_le_of_ne (csInf_le (show BddBelow S from ⟨δ,hl⟩) hCS)
    (fun he => hd (he ▸ hcold.2.1))
  obtain ⟨x,hx⟩ : ∃ x : ℝ, 1 < (F b).roots.count x := by
    by_contra! h
    exact hd (Multiset.nodup_iff_count_le_one.mpr h)
  have hroot : (F b).IsRoot x := (mem_roots (partition_ne_zero P b : F b ≠ 0)).mp
    (Multiset.count_pos.mp (Nat.zero_lt_one.trans hx))
  refine ⟨b,hb,hbC,hmem.2,fun u hu hub => hmin hu hub,x,squarefree_real_root_neg P b x hroot,?_⟩
  rwa [count_roots] at hx


end GaloisForLFunctions.SelbergClass.Primon
