import GaloisForLFunctions.RHTower.MobiusDivisorNonemptyEnergy
import GaloisForLFunctions.RHTower.RetainedPrimeSupportThreshold
import Mathlib.Data.Nat.Log

/-!
# Arity-weighted energy and accumulated prime interaction charge

Weighting each retained square by its remaining prime count gives an exact
balance: every merger consumes the complete copied-child square energy and
adds its arity-weighted signed overlap. The balance telescopes along every
finite prime history, including repeated insertions. Product support bounds
arity by the binary logarithm of the cutoff, so the initial cost is at most
`722 M² log₂ M`.

This energy ignores the empty head. Neither a sign bound for accumulated
charge nor a bound for the complete signed head is asserted. For arbitrary
signed fields on two remaining coordinates one next arity energy contracts;
on three coordinates the sharp universal next-step factor is four thirds.
-/

noncomputable section
open Finset
open scoped symmDiff
namespace RHTower

/-- Full retained square energy weighted by the number of unprocessed primes in each label. -/
def mobiusDivisorArityEnergy (M : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
    (R.card : ℝ)*(mobiusDivisorSelectionFibre M P R)^2

private theorem mobiusDivisorSelectionPrimeFactors_subset (M : ℕ) :
    ∀ d ∈ mobiusDivisorSelectionIndices M,
      d.primeFactors ⊆ mobiusDivisorSelectionPrimes M := by
  intro d hd p hp
  obtain ⟨hd,hds⟩ := mem_filter.mp hd
  obtain ⟨hd1,hdM⟩ := mem_Icc.mp hd
  have hpd := Nat.le_of_mem_primeFactors hp
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), (Nat.mem_primeFactors.mp hp).1⟩

/-- Literal all-source pair expansion of arity energy.  The factor is the
common unprocessed-prime arity of an interfering pair; no signed sector is
dropped. -/
theorem mobiusDivisorArityEnergy_eq_pairs (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorArityEnergy M P =
      ∑ d ∈ mobiusDivisorSelectionIndices M, ∑ e ∈ mobiusDivisorSelectionIndices M,
        if d.primeFactors ∆ e.primeFactors ⊆ P then
          ((d.primeFactors \ P).card : ℝ) * mobiusDivisorDilationChannel M d *
            mobiusDivisorDilationChannel M e
        else 0 := by
  change subsetLabelArityEnergy (mobiusDivisorSelectionPrimes M)
    (mobiusDivisorSelectionIndices M) Nat.primeFactors (mobiusDivisorDilationChannel M) P = _
  exact subsetLabelArityEnergy_eq_pairs _ _ _ _
    (mobiusDivisorSelectionPrimeFactors_subset M) P

/-- Complete signed overlap charge, with the exact parent-label arity retained. -/
def mobiusDivisorArityCharge (M : ℕ) (P : Finset ℕ) (p : ℕ) : ℝ :=
  2*∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset,
    (R.card : ℝ)*mobiusDivisorSelectionFibre M P R*
      mobiusDivisorSelectionFibre M P (insert p R)

/-- Arity energy is nonnegative for every actual source state. -/
theorem mobiusDivisorArityEnergy_nonneg (M : ℕ) (P : Finset ℕ) :
    0 ≤ mobiusDivisorArityEnergy M P :=
  sum_nonneg (fun R _ => mul_nonneg (Nat.cast_nonneg R.card) (sq_nonneg _))

/-- Arity energy controls every nonempty source coordinate, but assigns zero weight to the head. -/
theorem mobiusDivisorNonemptyEnergy_le_arity (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorNonemptyEnergy M P ≤ mobiusDivisorArityEnergy M P := by
  rw [mobiusDivisorNonemptyEnergy_eq_sum]
  unfold mobiusDivisorArityEnergy
  have hs := sum_erase_add (s := (mobiusDivisorSelectionPrimes M).powerset)
    (f := fun R => (R.card : ℝ)*(mobiusDivisorSelectionFibre M P R)^2)
    (a := ∅) (by simp)
  simp only [card_empty,Nat.cast_zero,zero_mul,add_zero] at hs
  rw [← hs]
  apply sum_le_sum
  intro R hR
  have hR0 : R.Nonempty := nonempty_iff_ne_empty.mpr (mem_erase.mp hR).1
  have hc : (1:ℝ) ≤ R.card := by exact_mod_cast hR0.card_pos
  nlinarith only [mul_le_mul_of_nonneg_right hc (sq_nonneg (mobiusDivisorSelectionFibre M P R))]

/-- A nonzero actual label has at most the binary logarithm of the cutoff many prime factors. -/
theorem mobiusDivisorSelectionLabel_card_le_log (M : ℕ) (P R : Finset ℕ)
    (hR : R ⊆ mobiusDivisorSelectionPrimes M)
    (hF : mobiusDivisorSelectionFibre M P R ≠ 0) : R.card ≤ Nat.log 2 M := by
  have hprod : (∏ p ∈ R,p) < M := by
    by_contra hn
    exact hF (mobiusDivisorSelectionFibre_eq_zero_of_le_product M P R (by omega))
  have hp : 2^R.card ≤ ∏ p ∈ R,p := by
    calc
      _ = ∏ _p ∈ R,(2:ℕ) := (prod_const 2).symm
      _ ≤ _ := prod_le_prod (fun _ _ => by omega)
        (fun p hp => (mem_filter.mp (hR hp)).2.two_le)
  exact Nat.le_log_of_pow_le (by omega) (hp.trans hprod.le)

/-- The complete arity cost is bounded by a single logarithmic factor times raw energy, uniformly in the processed core. -/
theorem mobiusDivisorArityEnergy_le_log_mul_energy (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorArityEnergy M P ≤ (Nat.log 2 M : ℝ)*mobiusDivisorSelectionEnergy M P := by
  unfold mobiusDivisorArityEnergy mobiusDivisorSelectionEnergy subsetLabelEnergy
  rw [mul_sum]
  apply sum_le_sum
  intro R hR
  change (R.card:ℝ)*(mobiusDivisorSelectionFibre M P R)^2 ≤
    (Nat.log 2 M:ℝ)*(mobiusDivisorSelectionFibre M P R)^2
  by_cases hF : mobiusDivisorSelectionFibre M P R=0
  · simp [hF]
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast
      mobiusDivisorSelectionLabel_card_le_log M P R (mem_powerset.mp hR) hF) (sq_nonneg _)

/-- The original actual arity budget has an unconditional quadratic-logarithmic ceiling. -/
theorem mobiusDivisorArityEnergy_initial_le (M : ℕ) :
    mobiusDivisorArityEnergy M ∅ ≤ 722*(Nat.log 2 M : ℝ)*(M:ℝ)^2 := by
  have h := mobiusDivisorArityEnergy_le_log_mul_energy M ∅
  rw [mobiusDivisorSelectionEnergy_empty] at h
  have hb := mul_le_mul_of_nonneg_left (sum_mobiusDivisorDilationChannel_sq_le_quadratic M)
    (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 M))
  nlinarith only [h,hb]

/-- Exact prime balance: signed arity charge minus the entire copied-child square energy. -/
theorem mobiusDivisorArityEnergy_insert (M : ℕ) (P : Finset ℕ) {p : ℕ}
    (hp : p ∈ mobiusDivisorSelectionPrimes M) :
    mobiusDivisorArityEnergy M (insert p P)-mobiusDivisorArityEnergy M P =
      mobiusDivisorArityCharge M P p-
        ∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset,
          (mobiusDivisorSelectionFibre M P (insert p R))^2 := by
  let U := mobiusDivisorSelectionPrimes M
  have split (f : Finset ℕ → ℝ) : (∑ R ∈ U.powerset,f R)=
      (∑ R ∈ (U.erase p).powerset,f R)+(∑ R ∈ (U.erase p).powerset,f (insert p R)) := by
    have hpU : p ∈ U := hp
    conv_lhs => rw [← insert_erase hpU]
    exact sum_powerset_insert (notMem_erase p U) f
  have hn (R : Finset ℕ) (hR : R ∈ (U.erase p).powerset) : p ∉ R := by
    intro h
    exact (mem_erase.mp (mem_powerset.mp hR h)).1 rfl
  unfold mobiusDivisorArityEnergy
  change (∑ R ∈ U.powerset, _)-(∑ R ∈ U.powerset, _)=_
  rw [split,split]
  have hz : (∑ R ∈ (U.erase p).powerset,
      ((insert p R).card:ℝ)*(mobiusDivisorSelectionFibre M (insert p P) (insert p R))^2)=0 := by
    apply sum_eq_zero
    intro R _
    simp [mobiusDivisorSelectionFibre_insert]
  rw [hz,add_zero,← sum_add_distrib,← sum_sub_distrib]
  unfold mobiusDivisorArityCharge
  rw [mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro R hR
  rw [mobiusDivisorSelectionFibre_insert,if_neg (hn R hR),card_insert_of_notMem (hn R hR)]
  push_cast
  ring

/-- Literal finite prime-insertion history; repeated primes are permitted. -/
def mobiusDivisorArityHistory (P : Finset ℕ) (q : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => P
  | n+1 => insert (q n) (mobiusDivisorArityHistory P q n)

/-- All copied-child square costs telescope into the two actual arity endpoints and the accumulated signed charge. -/
theorem mobiusDivisorArityEnergy_history_balance (M : ℕ) (P : Finset ℕ)
    (q : ℕ → ℕ) (n : ℕ) (hq : ∀ k<n,q k ∈ mobiusDivisorSelectionPrimes M) :
    (∑ k ∈ range n, ∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase (q k)).powerset,
      (mobiusDivisorSelectionFibre M (mobiusDivisorArityHistory P q k) (insert (q k) R))^2) =
      mobiusDivisorArityEnergy M P-mobiusDivisorArityEnergy M (mobiusDivisorArityHistory P q n)+
        ∑ k ∈ range n,mobiusDivisorArityCharge M (mobiusDivisorArityHistory P q k) (q k) := by
  have h := Finset.sum_range_sub (fun k => mobiusDivisorArityEnergy M (mobiusDivisorArityHistory P q k)) n
  have he : (∑ k ∈ range n, (mobiusDivisorArityEnergy M (mobiusDivisorArityHistory P q (k+1))-
      mobiusDivisorArityEnergy M (mobiusDivisorArityHistory P q k))) =
      (∑ k ∈ range n,mobiusDivisorArityCharge M (mobiusDivisorArityHistory P q k) (q k))-
      ∑ k ∈ range n, ∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase (q k)).powerset,
        (mobiusDivisorSelectionFibre M (mobiusDivisorArityHistory P q k) (insert (q k) R))^2 := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    exact mobiusDivisorArityEnergy_insert M _ (hq k (mem_range.mp hk))
  rw [he] at h
  change _ = _ - mobiusDivisorArityEnergy M P at h
  linarith only [h]

/-- Accumulated signed charge is the only extra term beyond initial arity energy in the total copied-square budget. -/
theorem mobiusDivisorArityEnergy_history_copied_budget (M : ℕ) (P : Finset ℕ)
    (q : ℕ → ℕ) (n : ℕ) (hq : ∀ k<n,q k ∈ mobiusDivisorSelectionPrimes M) :
    (∑ k ∈ range n, ∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase (q k)).powerset,
      (mobiusDivisorSelectionFibre M (mobiusDivisorArityHistory P q k) (insert (q k) R))^2) ≤
      mobiusDivisorArityEnergy M P+
        ∑ k ∈ range n,mobiusDivisorArityCharge M (mobiusDivisorArityHistory P q k) (q k) := by
  rw [mobiusDivisorArityEnergy_history_balance M P q n hq]
  have h := mobiusDivisorArityEnergy_nonneg M (mobiusDivisorArityHistory P q n)
  linarith only [h]

/-- Full prime processing leaves zero arity energy, irrespective of the final signed head. -/
theorem mobiusDivisorArityEnergy_of_complete (M : ℕ) (P : Finset ℕ)
    (hP : mobiusDivisorSelectionPrimes M ⊆ P) : mobiusDivisorArityEnergy M P=0 := by
  apply sum_eq_zero
  intro R _
  rw [mobiusDivisorSelectionFibre_of_all_source_primes_processed M P R hP]
  by_cases h : R=∅ <;> simp [h]

/-- Exact two-coordinate deficit from twice the current arity energy. -/
theorem twoCoordinateArity_next_sum (a b c : ℝ) :
    (a+c)^2+(b+c)^2=2*(a^2+b^2+2*c^2)-((a-c)^2+(b-c)^2) := by ring

/-- Every signed two-coordinate field admits a nonincreasing next arity energy. -/
theorem twoCoordinateArity_min_le (a b c : ℝ) :
    min ((a+c)^2) ((b+c)^2) ≤ a^2+b^2+2*c^2 := by
  have h := twoCoordinateArity_next_sum a b c
  have hl := min_le_left ((a+c)^2) ((b+c)^2)
  have hr := min_le_right ((a+c)^2) ((b+c)^2)
  nlinarith only [h,hl,hr,sq_nonneg (a-c),sq_nonneg (b-c)]

/-- Arity energy of three singleton, three pair, and one triple coefficient. -/
def threeCoordinateArityEnergy (a b c d e f g : ℝ) : ℝ :=
  a^2+b^2+c^2+2*(d^2+e^2+f^2)+3*g^2

/-- Least arity energy among the three literal next coordinate mergers. -/
def threeCoordinateArityNextMinimum (a b c d e f g : ℝ) : ℝ :=
  min ((b+d)^2+(c+e)^2+2*(f+g)^2)
    (min ((a+d)^2+(c+f)^2+2*(e+g)^2) ((a+e)^2+(b+f)^2+2*(d+g)^2))

/-- Exact three-coordinate deficit as weighted squares of adjacent-label differences. -/
theorem threeCoordinateArity_next_sum (a b c d e f g : ℝ) :
    ((b+d)^2+(c+e)^2+2*(f+g)^2)+
      ((a+d)^2+(c+f)^2+2*(e+g)^2)+
      ((a+e)^2+(b+f)^2+2*(d+g)^2) =
    4*threeCoordinateArityEnergy a b c d e f g-
      ((a-d)^2+(a-e)^2+(b-d)^2+(b-f)^2+(c-e)^2+(c-f)^2+
        2*((d-g)^2+(e-g)^2+(f-g)^2)) := by
  unfold threeCoordinateArityEnergy
  ring

/-- At least one of three coordinate mergers costs at most four thirds of current arity energy. -/
theorem threeCoordinateArity_min_le (a b c d e f g : ℝ) :
    threeCoordinateArityNextMinimum a b c d e f g ≤ (4/3)*threeCoordinateArityEnergy a b c d e f g := by
  have h := threeCoordinateArity_next_sum a b c d e f g
  have h1 := min_le_left ((b+d)^2+(c+e)^2+2*(f+g)^2)
    (min ((a+d)^2+(c+f)^2+2*(e+g)^2) ((a+e)^2+(b+f)^2+2*(d+g)^2))
  have h2 := (min_le_right ((b+d)^2+(c+e)^2+2*(f+g)^2)
    (min ((a+d)^2+(c+f)^2+2*(e+g)^2) ((a+e)^2+(b+f)^2+2*(d+g)^2))).trans (min_le_left _ _)
  have h3 := (min_le_right ((b+d)^2+(c+e)^2+2*(f+g)^2)
    (min ((a+d)^2+(c+f)^2+2*(e+g)^2) ((a+e)^2+(b+f)^2+2*(d+g)^2))).trans (min_le_right _ _)
  unfold threeCoordinateArityNextMinimum
  nlinarith only [h,h1,h2,h3,sq_nonneg (a-d),sq_nonneg (a-e),sq_nonneg (b-d),
    sq_nonneg (b-f),sq_nonneg (c-e),sq_nonneg (c-f),sq_nonneg (d-g),sq_nonneg (e-g),sq_nonneg (f-g)]

/-- Four thirds is the sharp universal factor; a constant nonempty field attains it in all three directions. -/
theorem threeCoordinateArity_factor_iff (C : ℝ) :
    (∀ a b c d e f g : ℝ, threeCoordinateArityNextMinimum a b c d e f g ≤
      C*threeCoordinateArityEnergy a b c d e f g) ↔ (4/3:ℝ)≤C := by
  constructor
  · intro h
    have hc := h 1 1 1 1 1 1 1
    norm_num [threeCoordinateArityNextMinimum,threeCoordinateArityEnergy] at hc
    linarith only [hc]
  · intro h a b c d e f g
    apply (threeCoordinateArity_min_le a b c d e f g).trans
    apply mul_le_mul_of_nonneg_right h
    unfold threeCoordinateArityEnergy
    positivity

end RHTower
