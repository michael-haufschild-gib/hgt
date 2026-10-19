import GaloisForLFunctions.BiScaleUncertainty.SieveVisibilityPhaseSeparation
import GaloisForLFunctions.BiScaleUncertainty.SieveVisibilityRadialEstimates
import GaloisForLFunctions.BiScaleUncertainty.SieveParityNeighborhoodSharpness

/-! Sharp local inverse exponents on the nonzero highest-dyadic stratum. -/

open scoped BigOperators
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
open ValuationPhase ParityNeighborhood
set_option autoImplicit false

/-- The known top-mode estimate holds on a full physical neighborhood and at every noise size. -/
theorem normalized_local_cubic (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ)
    (hb : 2 ≤ |selbergMultiplesCoord N b (TopAnchor.topOrder N)|) :
    LocalPairwiseHolder N b (1/3) := by
  let W : ℝ := ∑ q ∈ Icc 1 N, (q.totient : ℝ)
  have hW : 0 ≤ W := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  refine ⟨1, by norm_num, 2+2*W, by positivity, ?_⟩
  intro c e ε hε hc he h5 h6
  have hanchor (a : ℕ → ℝ) (ha : ∀ n, |sieveSeq N a n-sieveSeq N b n| ≤ 1) :
      1 ≤ |selbergMultiplesCoord N a (TopAnchor.topOrder N)| := by
    have hnear := coordinate_sup_error N b a 1 ha _ (TopAnchor.topOrder_mem N hN)
    have htri : |selbergMultiplesCoord N b (TopAnchor.topOrder N)| ≤
        |selbergMultiplesCoord N a (TopAnchor.topOrder N)-
          selbergMultiplesCoord N b (TopAnchor.topOrder N)|+
        |selbergMultiplesCoord N a (TopAnchor.topOrder N)| := by
      simpa only [sub_zero, abs_sub_comm] using
        abs_sub_le (selbergMultiplesCoord N b (TopAnchor.topOrder N))
          (selbergMultiplesCoord N a (TopAnchor.topOrder N)) 0
    linarith
  by_cases hε1 : ε ≤ 1
  · obtain ⟨h, hh⟩ := TopAnchor.exists_translate_error_rpow N hN c e ε hε hε1
      (hanchor c hc) (hanchor e he) h5 h6
    refine ⟨h, fun n => (hh n).trans ?_⟩
    apply mul_le_mul_of_nonneg_right (show 2*W ≤ 2+2*W by linarith)
      (Real.rpow_nonneg hε _)
  · have hεge : 1 ≤ ε := le_of_lt (lt_of_not_ge hε1)
    have hp : 1 ≤ ε^(1/3 : ℝ) := Real.one_le_rpow hεge (by norm_num)
    refine ⟨0, fun n => ?_⟩
    have hc' : |sieveSeq N b n-sieveSeq N c n| ≤ 1 := by
      simpa only [abs_sub_comm] using hc n
    have htri := abs_sub_le (sieveSeq N e n) (sieveSeq N b n) (sieveSeq N c n)
    have hsmall : |sieveSeq N e n-sieveSeq N c n| ≤ 2 := by linarith [he n]
    calc
      _ ≤ 2 := by simpa only [Nat.add_zero] using hsmall
      _ ≤ 2+2*W := by linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hp

/-- Every nonzero highest dyadic coordinate has a local cube-root inverse modulus. -/
theorem local_cubic (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ)
    (hb : selbergMultiplesCoord N b (TopAnchor.topOrder N) ≠ 0) :
    LocalPairwiseHolder N b (1/3) := by
  obtain ⟨scl, hscl, ha⟩ := normalize_coordinate N b (TopAnchor.topOrder N) hb
  exact (local_holder_scale_iff N b (1/3) scl hscl.ne').mp
    (normalized_local_cubic N hN _ ha.ge)

/-- A nonzero normalized source rules out every exponent above one. -/
theorem normalized_not_above_one (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ)
    (hb : 2 ≤ |selbergMultiplesCoord N b (TopAnchor.topOrder N)|)
    (α : ℝ) (hα : 1 < α) : ¬LocalPairwiseHolder N b α := by
  let M : ℝ := coordinateBudget N b
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (coordinateBudget_one_le N b)
  let L : ℝ := (N.factorial : ℝ)^6*6*(2*M)^6*M
  let W : ℝ := (∑ q ∈ Icc 1 N, (q.totient : ℝ))*M
  apply not_holder_of_witnesses N 1 (by decide) b (fun _ => b)
    (fun t d => (1+t)*b d) L W 1 α (by dsimp [L]; positivity)
    (by dsimp [W]; positivity) (by simpa using hα)
  · intro t ht _ n
    constructor
    · simp only [sub_self, abs_zero]
      dsimp [W]
      positivity
    · exact radial_near_base N b t ht n
  · intro t ht ht1
    constructor
    · intro v
      simpa only [pow_one] using radial_raw_error N b t ht ht1 5 (by decide) v
    · intro v
      simpa only [pow_one] using radial_raw_error N b t ht ht1 6 (by decide) v
  · intro t ht _ h D herr
    simpa only [one_mul] using radial_separation N b _ (TopAnchor.topOrder_mem N hN) hb t ht h D herr

/-- The linear endpoint is an absolute ceiling on the nonzero highest-mode stratum. -/
theorem not_above_one (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ)
    (hb : selbergMultiplesCoord N b (TopAnchor.topOrder N) ≠ 0)
    (α : ℝ) (hα : 1 < α) : ¬LocalPairwiseHolder N b α := by
  obtain ⟨scl, hscl, ha⟩ := normalize_coordinate N b (TopAnchor.topOrder N) hb
  intro h
  exact normalized_not_above_one N hN _ ha.ge α hα
    ((local_holder_scale_iff N b α scl hscl.ne').mpr h)

/-- An invisible missing mode gives sharp cubic instability around the normalized source. -/
theorem normalized_not_holder_invisible (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ)
    (hA : 1 ≤ |selbergMultiplesCoord N b (TopAnchor.topOrder N)|)
    (q : ℕ) (hq : q ∈ Icc 1 N) (hmissing : q ∉ activeModes N b)
    (hv : ¬Visible N (activeModes N b) q) (α : ℝ) (hα : 1/3 < α) :
    ¬LocalPairwiseHolder N b α := by
  have hq0 := coordinate_zero_of_not_active N b q hmissing
  have hne : q ≠ TopAnchor.topOrder N := by
    intro heq
    rw [← heq, hq0, abs_zero] at hA
    linarith
  obtain ⟨p, u, hu, hphase⟩ := top_phase_relation N hN q hq hne
  let L : ℝ := 2*(N.factorial : ℝ)^6*(coordinateBudget N b)^6
  have hM : 0 ≤ coordinateBudget N b :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (coordinateBudget_one_le N b)
  apply not_holder_of_witnesses N 3 (by decide) b
    (spikeWeights N b q) (fun t => spikeWeights N b q (-t))
    L (q.totient : ℝ) ((p : ℝ)+u) α (by dsimp [L]; positivity) (by positivity) hα
  · intro t ht _ n
    constructor
    · simpa only [abs_of_nonneg ht] using spike_near_base N b q hq hq0 t n
    · simpa only [abs_neg, abs_of_nonneg ht] using spike_near_base N b q hq hq0 (-t) n
  · intro t ht ht1
    exact ⟨invisible_raw_error N b q hq hv t ht ht1 5 (Or.inl rfl),
      invisible_raw_error N b q hq hv t ht ht1 6 (Or.inr rfl)⟩
  · intro t ht ht1 h D herr
    exact spike_separation_of_relation N hN b q hq hne hA t ht ht1 h p u hu (hphase h) D herr

/-- Invisibility forces the cubic ceiling at every nonzero top-mode amplitude. -/
theorem not_holder_invisible (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ)
    (hb : selbergMultiplesCoord N b (TopAnchor.topOrder N) ≠ 0)
    (q : ℕ) (hq : q ∈ Icc 1 N) (hmissing : q ∉ activeModes N b)
    (hv : ¬Visible N (activeModes N b) q) (α : ℝ) (hα : 1/3 < α) :
    ¬LocalPairwiseHolder N b α := by
  obtain ⟨scl, hscl, ha⟩ := normalize_coordinate N b (TopAnchor.topOrder N) hb
  have hs := activeModes_scale N b scl hscl.ne'
  intro h
  exact normalized_not_holder_invisible N hN _ (by rw [ha]; norm_num) q hq
    (by simpa only [hs] using hmissing) (by simpa only [hs] using hv) α hα
    ((local_holder_scale_iff N b α scl hscl.ne').mpr h)

/-- Exact first-order arithmetic criterion for local physical Lipschitz recovery. -/
theorem local_lipschitz_iff_visible (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ)
    (hb : selbergMultiplesCoord N b (TopAnchor.topOrder N) ≠ 0) :
    LocalPairwiseHolder N b 1 ↔
      ∀ q ∈ Icc 1 N, q ∉ activeModes N b → Visible N (activeModes N b) q := by
  constructor
  · intro h q hq hmissing
    by_contra hv
    exact not_holder_invisible N hN b hb q hq hmissing hv 1 (by norm_num) h
  · exact local_lipschitz_of_visibility N b

open scoped Classical

/-- Complete local exponent classification on the highest dyadic stratum. -/
theorem highest_stratum_sharp_exponent (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ)
    (hb : selbergMultiplesCoord N b (TopAnchor.topOrder N) ≠ 0) :
    let α : ℝ := if ∀ q ∈ Icc 1 N, q ∉ activeModes N b → Visible N (activeModes N b) q
      then 1 else 1/3
    LocalPairwiseHolder N b α ∧ ∀ β : ℝ, α < β → ¬LocalPairwiseHolder N b β := by
  classical
  by_cases hv : ∀ q ∈ Icc 1 N, q ∉ activeModes N b → Visible N (activeModes N b) q
  · simp only [if_pos hv]
    exact ⟨local_lipschitz_of_visibility N b hv, not_above_one N hN b hb⟩
  · simp only [if_neg hv]
    have hex : ∃ q ∈ Icc 1 N, q ∉ activeModes N b ∧ ¬Visible N (activeModes N b) q := by
      by_contra hn
      apply hv
      intro q hq hmissing
      by_contra hnot
      exact hn ⟨q, hq, hmissing, hnot⟩
    obtain ⟨q, hq, hmissing, hnot⟩ := hex
    exact ⟨local_cubic N hN b hb, not_holder_invisible N hN b hb q hq hmissing hnot⟩

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
