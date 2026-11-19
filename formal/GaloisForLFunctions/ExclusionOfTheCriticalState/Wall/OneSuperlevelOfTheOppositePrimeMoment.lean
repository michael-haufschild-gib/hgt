import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositePrimeExcursionsOnOneFixedBand
import Mathlib.NumberTheory.Harmonic.Bounds

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

private def upperReading {ι : Type*} (S : Finset ι) (f : ι → ℝ) (i : ι) : ℝ :=
  f i * ((S.filter (fun j => f i ≤ f j)).card:ℝ)

private theorem harmonic_majorant {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℝ) (C : ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (hb : ∀ i ∈ S, upperReading S f i ≤ C) :
    (∑ i ∈ S, f i) ≤ (harmonic S.card:ℝ)*C := by
  classical
  induction S using Finset.strongInductionOn with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl|hn
    · simp
    obtain ⟨i,hi,hmin⟩ := S.exists_min_image f hn
    let T := S.erase i
    have ht := erase_subset i S
    have hsub (j : ι) : T.filter (fun q => f j ≤ f q) ⊆ S.filter (fun q => f j ≤ f q) :=
      filter_subset_filter _ ht
    have hT := ih T (erase_ssubset hi) (fun j hj => hf j (ht hj)) (fun j hj =>
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card (hsub j))) (hf j (ht hj))).trans
        (hb j (ht hj)))
    have hstep : T.card+1=S.card := card_erase_add_one hi
    have hcard : 0 < (S.card:ℝ) := Nat.cast_pos.mpr (card_pos.mpr hn)
    have low := hb i hi
    rw [upperReading,filter_true_of_mem hmin] at low
    have hlead := (le_div_iff₀ hcard).mpr low
    have hh : (harmonic S.card:ℝ) = (harmonic T.card:ℝ)+(S.card:ℝ)⁻¹ := by
      rw [←hstep,harmonic_succ]
      push_cast
      rfl
    rw [←sum_erase_add S f hi,hh,add_mul]
    exact add_le_add hT (by simpa only [div_eq_mul_inv,mul_comm C] using hlead)

/-- A realized threshold captures at least the reciprocal harmonic
fraction of any finite nonnegative sum. Ties are counted together. -/
theorem exists_harmonic_superlevel {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hn : S.Nonempty) (hf : ∀ i ∈ S, 0 ≤ f i) :
    ∃ i ∈ S, (∑ j ∈ S, f j) ≤ (harmonic S.card:ℝ)*(f i*((S.filter (fun j => f i ≤ f j)).card:ℝ)) := by
  classical
  obtain ⟨i,hi,hmax⟩ := S.exists_max_image (upperReading S f) hn
  exact ⟨i,hi,harmonic_majorant S f _ hf hmax⟩

/-- Eligible numerators whose positive-part product reaches the value at
the selected numerator. The orientation and flank stay fixed. -/
def oppositePrimeSuperlevel (left : Bool) (s a g d T : ℝ) (k L H : ℕ) : Finset ℕ :=
  (largeOppositePrimeNumerators left s a g d T k L).filter fun J =>
    oppositePrimeProduct left s k L H ≤ oppositePrimeProduct left s k L J

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
sign thresholds survive, with only logarithmic loss. -/
theorem rh_or_one_opposite_prime_superlevel : RiemannHypothesis ∨
    ∃ a c g d r : ℝ, 0<a ∧ 0<c ∧ 0<g ∧ 0<d ∧ d≤1/4 ∧ 0<r ∧
      ∀ η : ℝ, 0<η → η≤r → ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η)≤Real.log (k i) ∧ Real.log (k i)≤T i) ∧
        ∀ᶠ i in atTop,
          let L := ⌈Real.exp ((1+η)*T i)⌉₊
          ∃ (s : ℝ) (left : Bool) (H : ℕ), (s=1 ∨ s= -1) ∧
            H ∈ largeOppositePrimeNumerators left s a g d (T i) (k i) L ∧
            c*a^2*Real.exp ((1/2+3*g)*T i) <
              (1+2*Real.log L)*((L:ℝ)*oppositePrimeProduct left s (k i) L H)*
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
  obtain ⟨H,hH,hu⟩ := opposite_prime_single_superlevel left s a g d (T i) (k i) L hn
  exact ⟨s,left,H,hs,hH,hlarge.trans_le hu⟩

#print axioms exists_harmonic_superlevel
#print axioms opposite_prime_single_superlevel
#print axioms rh_or_one_opposite_prime_superlevel
end GaloisForLFunctions.ExclusionOfTheCriticalState
