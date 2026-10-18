import GaloisForLFunctions.BiScaleUncertainty.PrimeMeasurementComplexity

/-!
# Adaptive literal-moment recovery for the prime family

Read every diagonal contrast first, then the row of the least nonzero diagonal.
Each contrast consists of 64 literal sixth moments. This discovers zero support
and recovers all coefficients up to common sign using at most `128M - 64`
indexed raw observations (natural subtraction gives zero when `M = 0`).

The selection uses only the diagonal observations. These are exact-data results;
noise bounds for the fixed full matrix remain in `PrimeRawMomentRecovery`.
-/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.PrimeRaw
open GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- First-stage pair indices, independent of the unknown coefficients. -/
def diagonalPairs (N : ℕ) : Finset (oddPrimeModes N × oddPrimeModes N) :=
  Finset.univ.image (fun p => (p,p))

/-- Second-stage row indices; the already observed diagonal is omitted. -/
def anchorPairs (N : ℕ) (r : oddPrimeModes N) : Finset (oddPrimeModes N × oddPrimeModes N) :=
  (Finset.univ.erase r).image (fun q => (r,q))

/-- Both stages, with the anchor determined by observed diagonal contrasts. -/
def adaptivePairs (N : ℕ) (a : ℕ → ℝ) : Finset (oddPrimeModes N × oddPrimeModes N) :=
  diagonalPairs N ∪
    if h : (anchorCandidates N (normalizedReadout N a)).Nonempty then
      anchorPairs N ((anchorCandidates N (normalizedReadout N a)).min' h)
    else ∅

private theorem diagonal_card (N : ℕ) : (diagonalPairs N).card = Fintype.card (oddPrimeModes N) := by
  rw [diagonalPairs, Finset.card_image_of_injective]
  · simp
  · intro p q h
    exact congrArg Prod.fst h

private theorem anchor_card (N : ℕ) (r : oddPrimeModes N) :
    (anchorPairs N r).card = Fintype.card (oddPrimeModes N)-1 := by
  rw [anchorPairs, Finset.card_image_of_injective]
  · rw [Finset.card_erase_of_mem (Finset.mem_univ r)]
    simp
  · intro p q h
    exact congrArg Prod.snd h

private theorem diagonal_anchor_disjoint (N : ℕ) (r : oddPrimeModes N) :
    Disjoint (diagonalPairs N) (anchorPairs N r) := by
  apply Finset.disjoint_left.mpr
  intro x hd hr
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hd
  obtain ⟨q,hq,hqx⟩ := Finset.mem_image.mp hr
  have he : (p,p) = (r,q) := hp.trans hqx.symm
  have hpr := congrArg Prod.fst he
  have hpq := congrArg Prod.snd he
  exact (Finset.mem_erase.mp hq).1 (hpq.symm.trans hpr)

/-- Exact pair count, including the all-zero and empty mode cases. -/
theorem adaptive_pair_count (N : ℕ) (a : ℕ → ℝ) :
    (adaptivePairs N a).card =
      if (anchorCandidates N (normalizedReadout N a)).Nonempty then
        2*Fintype.card (oddPrimeModes N)-1 else Fintype.card (oddPrimeModes N) := by
  unfold adaptivePairs
  split_ifs with h
  · rw [Finset.card_union_of_disjoint (diagonal_anchor_disjoint N _), diagonal_card, anchor_card]
    omega
  · simp [diagonal_card]

/-- Uniform upper bound for the indexed raw observations. -/
theorem adaptive_raw_count (N : ℕ) (a : ℕ → ℝ) :
    64*(adaptivePairs N a).card ≤ 128*Fintype.card (oddPrimeModes N)-64 := by
  rw [adaptive_pair_count]
  split_ifs <;> omega

private theorem diagonal_mem (N : ℕ) (a : ℕ → ℝ) (p : oddPrimeModes N) :
    (p,p) ∈ adaptivePairs N a := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩

private theorem selected_mem (N : ℕ) (a : ℕ → ℝ)
    (h : (anchorCandidates N (normalizedReadout N a)).Nonempty) (p : oddPrimeModes N) :
    ((anchorCandidates N (normalizedReadout N a)).min' h,p) ∈ adaptivePairs N a := by
  let r := (anchorCandidates N (normalizedReadout N a)).min' h
  by_cases hp : p = r
  · subst p
    exact diagonal_mem N a r
  · unfold adaptivePairs
    rw [dif_pos h]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨p,Finset.mem_erase.mpr ⟨hp,Finset.mem_univ _⟩,rfl⟩

private theorem normalized_eq_of_raw (N : ℕ) (a b : ℕ → ℝ) (p q : oddPrimeModes N)
    (h : ∀ v : Fin 6 → Fin 2, rawObservation N a p q v = rawObservation N b p q v) :
    normalizedReadout N a p q = normalizedReadout N b p q := by
  unfold normalizedReadout pairContrast momentContrast
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  exact congrArg (fun x : ℝ => cubeSign v*x) (h v)

/-- Equality on the selected raw observations is exactly common-sign ambiguity. -/
theorem adaptive_observations_iff_common_sign (N : ℕ) (a b : ℕ → ℝ) :
    (∀ z ∈ adaptivePairs N a, ∀ v : Fin 6 → Fin 2,
      rawObservation N a z.1 z.2 v = rawObservation N b z.1 z.2 v) ↔
      (∀ p : oddPrimeModes N, a p = b p) ∨ (∀ p : oddPrimeModes N, a p = -b p) := by
  constructor
  · intro hobs
    have hd (p : oddPrimeModes N) : normalizedReadout N a p p = normalizedReadout N b p p :=
      normalized_eq_of_raw N a b p p (hobs (p,p) (diagonal_mem N a p))
    by_cases h : (anchorCandidates N (normalizedReadout N a)).Nonempty
    · let r := (anchorCandidates N (normalizedReadout N a)).min' h
      have hr : normalizedReadout N a r r ≠ 0 :=
        (Finset.mem_filter.mp (Finset.min'_mem (anchorCandidates N (normalizedReadout N a)) h)).2
      have har : a r ≠ 0 := by
        intro hz
        apply hr
        rw [normalizedReadout_eq, hz]
        ring
      have hp (q : oddPrimeModes N) : a r*a q = b r*b q := by
        have he := normalized_eq_of_raw N a b r q (hobs (r,q) (selected_mem N a h q))
        have he' := congrArg inverseCube he
        simpa only [normalizedReadout_eq, inverseCube_cube] using he'
      have hf : (a r-b r)*(a r+b r) = 0 := by nlinarith [hp r]
      rcases mul_eq_zero.mp hf with he | he
      · left
        have heq : a r = b r := sub_eq_zero.mp he
        intro q
        have hq := hp q
        rw [← heq] at hq
        exact mul_left_cancel₀ har hq
      · right
        have heq : b r = -a r := by linarith
        intro q
        apply mul_left_cancel₀ har
        calc
          a r*a q = b r*b q := hp q
          _ = a r*(-b q) := by rw [heq]; ring
    · left
      intro p
      have ha : a p = 0 := by
        by_contra ha
        apply h
        exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [normalizedReadout_eq]
          exact pow_ne_zero 3 (mul_ne_zero ha ha)⟩⟩
      have he := congrArg inverseCube (hd p)
      simp only [normalizedReadout_eq, inverseCube_cube] at he
      rw [ha] at he
      nlinarith
  · intro h z _ v
    exact (rawObservations_iff_common_sign N a b).mpr h z.1 z.2 v

/-- Fill unobserved raw slots with zero; the anchor decoder uses only observed slots. -/
def selectedRaw (N : ℕ) (a : ℕ → ℝ) (p q : oddPrimeModes N) (v : Fin 6 → Fin 2) : ℝ :=
  if (p,q) ∈ adaptivePairs N a then rawObservation N a p q v else 0

private def selectedReadout (N : ℕ) (a : ℕ → ℝ) (p q : oddPrimeModes N) : ℝ :=
  if (p,q) ∈ adaptivePairs N a then normalizedReadout N a p q else 0

private theorem selected_candidates (N : ℕ) (a : ℕ → ℝ) :
    anchorCandidates N (selectedReadout N a) = anchorCandidates N (normalizedReadout N a) := by
  ext p
  simp only [anchorCandidates, Finset.mem_filter, Finset.mem_univ, true_and,
    selectedReadout, if_pos (diagonal_mem N a p)]

private theorem recover_selected (N : ℕ) (a : ℕ → ℝ) (p : oddPrimeModes N) :
    recover N (selectedReadout N a) p = recover N (normalizedReadout N a) p := by
  unfold recover
  rw [selected_candidates]
  split_ifs with h
  · let r := (anchorCandidates N (normalizedReadout N a)).min' h
    change inverseCube (selectedReadout N a r p) / Real.sqrt (inverseCube (selectedReadout N a r r)) = _
    rw [selectedReadout, if_pos (selected_mem N a h p), selectedReadout,
      if_pos (diagonal_mem N a r)]
  · rfl

/-- Zero filling needs no unobserved data and gives the same exact decoder output. -/
theorem decode_selected_eq (N : ℕ) (a : ℕ → ℝ) (p : oddPrimeModes N) :
    decodeRaw N (selectedRaw N a) p = decodeRaw N (rawObservation N a) p := by
  have he : (fun r s => (∑ v : Fin 6 → Fin 2, cubeSign v * selectedRaw N a r s v) /
      pairScale N r s) = selectedReadout N a := by
    funext r s
    by_cases h : (r,s) ∈ adaptivePairs N a
    · simp only [selectedRaw, selectedReadout, if_pos h]
      rfl
    · simp [selectedRaw, selectedReadout, h]
  unfold decodeRaw
  rw [he]
  exact recover_selected N a p

/-- The explicit raw decoder recovers every vector from the adaptive observations alone. -/
theorem decode_selected_actual (N : ℕ) (a : ℕ → ℝ) :
    (∀ p : oddPrimeModes N, decodeRaw N (selectedRaw N a) p = a p) ∨
      (∀ p : oddPrimeModes N, decodeRaw N (selectedRaw N a) p = -a p) := by
  simpa only [decode_selected_eq] using decodeRaw_actual N a

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.PrimeRaw
