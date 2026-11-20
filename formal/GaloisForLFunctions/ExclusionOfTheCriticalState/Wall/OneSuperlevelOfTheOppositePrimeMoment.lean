import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositePrimeExcursionsOnOneFixedBand
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.FiniteWeakMomentComparison

/-!
# One superlevel of the joint opposite-prime moment

Level-set testing, as in Chen et al., Lemma 2.1, has a finite counting
version. A nonnegative sum is at most its largest weak first moment times
the harmonic number of its support. Applied to the forced arithmetic
excursion this extracts one realized threshold at each late test.
-/

open Finset Filter
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

open GaloisForLFunctions.FiniteWeakMoment

/-- A realized threshold captures at least the reciprocal harmonic
fraction of any finite nonnegative sum. -/
theorem exists_harmonic_superlevel {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hn : S.Nonempty) (hf : ∀ i ∈ S, 0 ≤ f i) :
    ∃ i ∈ S, (∑ j ∈ S, f j) ≤ (harmonic S.card:ℝ)*(f i*((S.filter (fun j => f i ≤ f j)).card:ℝ)) := by
  obtain ⟨i,hi,h,_⟩ := exists_capturing_level hn f hf
  exact ⟨i,hi,h⟩

/-- Reciprocal rank counting all ties at the same observed height. -/
def reciprocalSuperlevelRank {ι : Type*} (S : Finset ι) (f : ι → ℝ) (i : ι) : ℝ :=
  ((S.filter (fun j => f i ≤ f j)).card:ℝ)⁻¹

private theorem reciprocal_rank_pos {ι : Type*} {S : Finset ι} (f : ι → ℝ) {i : ι} (hi : i ∈ S) :
    0 < ((S.filter (fun j => f i ≤ f j)).card:ℝ) :=
  Nat.cast_pos.mpr (card_pos.mpr ⟨i,mem_filter.mpr ⟨hi,le_rfl⟩⟩)

/-- Reciprocal superlevel ranks preserve both strict order and ties.
In particular each height of the new sample has weak first moment one. -/
theorem reciprocal_rank_order {ι : Type*} {S : Finset ι} (f : ι → ℝ) {i j : ι}
    (hi : i ∈ S) (hj : j ∈ S) :
    reciprocalSuperlevelRank S f i ≤ reciprocalSuperlevelRank S f j ↔ f i ≤ f j := by
  let U (k : ι) := S.filter fun l => f k ≤ f l
  have nest {u v : ι} (h : f u ≤ f v) : U v ⊆ U u := fun l hl =>
    mem_filter.mpr ⟨(mem_filter.mp hl).1,h.trans (mem_filter.mp hl).2⟩
  rw [reciprocalSuperlevelRank,reciprocalSuperlevelRank,
    inv_le_inv₀ (reciprocal_rank_pos f hi) (reciprocal_rank_pos f hj),Nat.cast_le]
  constructor
  · intro hc
    by_contra! h
    have proper : U i ⊂ U j := by
      refine ⟨nest h.le,fun sub => ?_⟩
      exact h.not_ge (mem_filter.mp (sub (show j ∈ U j from mem_filter.mpr ⟨hj,le_rfl⟩))).2
    exact (card_lt_card proper).not_ge hc
  · exact fun h => card_le_card (nest h)

theorem unit_weak_moment_of_reciprocal_ranks {ι : Type*} {S : Finset ι} (f : ι → ℝ)
    {i : ι} (hi : i ∈ S) : levelMass S (reciprocalSuperlevelRank S f) i=1 := by
  have eq : S.filter (fun j => reciprocalSuperlevelRank S f i ≤ reciprocalSuperlevelRank S f j) =
      S.filter (fun j => f i ≤ f j) := by
    ext j
    by_cases hj : j ∈ S
    · simp only [mem_filter,hj,true_and,reciprocal_rank_order f hi hj]
    · simp [hj]
  rw [levelMass,eq,reciprocalSuperlevelRank,inv_mul_cancel₀ (reciprocal_rank_pos f hi).ne']

/-- Once the weak order of the observed heights is known, its exact
weak-to-strong constant is the sum of reciprocal ranks. The reciprocal
rank profile realizes it and the harmonic number always bounds it. -/
theorem weak_moment_cost_of_tied_heights {ι : Type*} (S : Finset ι) (f : ι → ℝ) (C : ℝ)
    (cap : ∀ i ∈ S, levelMass S f i ≤ C) :
    (∑ i ∈ S, f i) ≤ (∑ i ∈ S, reciprocalSuperlevelRank S f i)*C ∧
    (∑ i ∈ S, reciprocalSuperlevelRank S f i) ≤ (harmonic S.card:ℝ) := by
  constructor
  · rw [sum_mul]
    apply sum_le_sum
    intro i hi
    have bound := (le_div_iff₀ (reciprocal_rank_pos f hi)).mpr (cap i hi)
    simpa only [reciprocalSuperlevelRank,div_eq_inv_mul] using bound
  · have h := sum_le_harmonic S (reciprocalSuperlevelRank S f) 1
      (fun i hi => (inv_pos.mpr (reciprocal_rank_pos f hi)).le)
      (fun i hi => (unit_weak_moment_of_reciprocal_ranks f hi).le)
    simpa only [mul_one] using h

/-- Eligible numerators whose positive-part product reaches the value at
the selected numerator. The orientation and flank stay fixed. -/
def oppositePrimeSuperlevel (left : Bool) (s a g d T : ℝ) (k L H : ℕ) : Finset ℕ :=
  (largeOppositePrimeNumerators left s a g d T k L).filter fun J =>
    oppositePrimeProduct left s k L H ≤ oppositePrimeProduct left s k L J

/-- The cutoff selected by the actual prime products pays only the sum
of reciprocal superlevel counts. Equal observations are grouped at their
full upper rank. -/
theorem opposite_prime_tied_height_level (left : Bool) (s a g d T : ℝ) (k L : ℕ) :
    let S := largeOppositePrimeNumerators left s a g d T k L
    let f := oppositePrimeProduct left s k L
    S.Nonempty → ∃ H ∈ S, (L:ℝ)*(∑ J ∈ S, f J) ≤
      (∑ J ∈ S, reciprocalSuperlevelRank S f J)*((L:ℝ)*f H)*
        (oppositePrimeSuperlevel left s a g d T k L H).card := by
  intro S f hn
  obtain ⟨i,hi,cap⟩ := S.exists_max_image (levelMass S f) hn
  refine ⟨i,hi,?_⟩
  have h := mul_le_mul_of_nonneg_left
    (weak_moment_cost_of_tied_heights S f (levelMass S f i) cap).1 (Nat.cast_nonneg (α:=ℝ) L)
  exact h.trans_eq (by unfold levelMass; dsimp only [oppositePrimeSuperlevel,S,f]; ring)

/-- The joint moment reduces to a single product threshold with loss at
most one plus twice the logarithm of the denominator endpoint. -/
theorem opposite_prime_single_superlevel (left : Bool) (s a g d T : ℝ) (k L : ℕ) :
    let S := largeOppositePrimeNumerators left s a g d T k L
    S.Nonempty → ∃ H ∈ S, (L:ℝ)*(∑ J ∈ S, oppositePrimeProduct left s k L J) ≤
      (1+2*Real.log L)*((L:ℝ)*oppositePrimeProduct left s k L H)*
        (oppositePrimeSuperlevel left s a g d T k L H).card := by
  intro S hn
  let f := oppositePrimeProduct left s k L
  have hf (j : ℕ) : 0 ≤ f j := div_nonneg (mul_nonneg (le_max_left ..) (le_max_left ..)) (sq_nonneg _)
  obtain ⟨H,hH,he⟩ := exists_harmonic_superlevel S f hn (fun j _ => hf j)
  refine ⟨H,hH,?_⟩
  have hcard : S.card ≤ L^2 := (card_le_card (show S ⊆ range (L^2) from
    (filter_subset ..).trans (filter_subset ..))).trans_eq (card_range _)
  have hlog := Real.log_le_log (Nat.cast_pos.mpr (card_pos.mpr hn)) (Nat.cast_le.mpr hcard : (S.card:ℝ) ≤ (L^2:ℕ))
  rw [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] at hlog
  have hh : (harmonic S.card:ℝ) ≤ 1+2*Real.log L :=
    (harmonic_le_one_add_log _).trans (add_le_add_left hlog _)
  let n : ℝ := (oppositePrimeSuperlevel left s a g d T k L H).card
  change (∑ j ∈ S, f j) ≤ (harmonic S.card:ℝ)*(f H*n) at he
  change (L:ℝ)*(∑ j ∈ S, f j) ≤ (1+2*Real.log L)*((L:ℝ)*f H)*n
  have h := mul_le_mul_of_nonneg_left (he.trans (mul_le_mul_of_nonneg_right hh
    (mul_nonneg (hf H) (Nat.cast_nonneg _)))) (Nat.cast_nonneg (α:=ℝ) L)
  linarith only [h]

/-- A failure of RH forces a single, arithmetically defined product
superlevel at each sufficiently late test. The original scales and both
sign thresholds survive, with the loss computed from the observed ties. -/
theorem rh_or_one_opposite_prime_superlevel : RiemannHypothesis ∨
    ∃ a c g d r : ℝ, 0<a ∧ 0<c ∧ 0<g ∧ 0<d ∧ d≤1/4 ∧ 0<r ∧
      ∀ η : ℝ, 0<η → η≤r → ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η)≤Real.log (k i) ∧ Real.log (k i)≤T i) ∧
        ∀ᶠ i in atTop,
          let L := ⌈Real.exp ((1+η)*T i)⌉₊
          ∃ (s : ℝ) (left : Bool) (H : ℕ), (s=1 ∨ s= -1) ∧
            H ∈ largeOppositePrimeNumerators left s a g d (T i) (k i) L ∧
            c*a^2*Real.exp ((1/2+3*g)*T i) <
              (∑ J ∈ largeOppositePrimeNumerators left s a g d (T i) (k i) L,
                reciprocalSuperlevelRank (largeOppositePrimeNumerators left s a g d (T i) (k i) L)
                  (oppositePrimeProduct left s (k i) L) J)*((L:ℝ)*oppositePrimeProduct left s (k i) L H)*
                (oppositePrimeSuperlevel left s a g d (T i) (k i) L H).card := by
  rcases riemannHypothesis_or_fixed_band_opposite_prime_moment with hh |
    ⟨_,_,_,a,c,g,d,r,_,_,_,_,_,ha,hc,hg,hd,hd',hr,seq⟩
  · exact Or.inl hh
  refine Or.inr ⟨a,c,g,d,r,ha,hc,hg,hd,hd',hr,fun η hη hηr => ?_⟩
  obtain ⟨T,k,ht,hk,_,ev⟩ := seq η hη hηr
  refine ⟨T,k,ht,hk,?_⟩
  filter_upwards [ev] with i hi
  let L := ⌈Real.exp ((1+η)*T i)⌉₊
  obtain ⟨_,_,s,left,_,_,hs,_,_,_,_,_,hlarge⟩ := hi
  let S := largeOppositePrimeNumerators left s a g d (T i) (k i) L
  have hn : S.Nonempty := by
    by_contra! he
    change c*a^2*Real.exp ((1/2+3*g)*T i) < (L:ℝ)*∑ j ∈ S, _ at hlarge
    rw [he,sum_empty,mul_zero] at hlarge
    exact hlarge.not_ge (by positivity)
  obtain ⟨H,hH,hu⟩ := opposite_prime_tied_height_level left s a g d (T i) (k i) L hn
  exact ⟨s,left,H,hs,hH,hlarge.trans_le hu⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
