import GaloisForLFunctions.RHTower.MobiusDivisorParityDefectTransport
import GaloisForLFunctions.RHTower.TwoCoordinateMergerCeiling

/-!
# Sharp local control of two original prime mergers

The original oriented fibres are unsigned channels at their prime products.
Exact four-block decomposition and clipped clock interpolation localize any
two-prime ceiling failure to a factor-two unit-channel failure at a cutoff
no larger than the original one. Two is sharp for the nonnegative local
comparison class. The arithmetic unit-channel comparison remains unproved.
-/

noncomputable section
open Finset
namespace RHTower

/-- A factor-two parent bound controls the complete alternating square of a nonnegative two-coordinate block. -/
theorem nonnegative_two_coordinate_square_le_of_double
    {a b c e : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hba : b ≤ 2*a) (hca : c ≤ 2*a) (heb : e ≤ 2*b) (hec : e ≤ 2*c) :
    (a-b-c+e)^(2 : ℕ) ≤ a^(2 : ℕ)+b^(2 : ℕ)+c^(2 : ℕ)+e^(2 : ℕ) := by
  have hex : e ≤ b+c := by linarith only [heb,hec]
  have hbc : b*c ≤ a*(b+c) := by
    have h1 := mul_nonneg (sub_nonneg.mpr hba) hc
    have h2 := mul_nonneg (sub_nonneg.mpr hca) hb
    nlinarith only [h1,h2]
  by_cases hax : a ≤ b+c
  · have h := mul_nonneg he (sub_nonneg.mpr hax)
    nlinarith only [hbc,h]
  · have h := mul_nonneg (show 0 ≤ a-(b+c) by linarith)
      (sub_nonneg.mpr hex)
    have hprod := mul_nonneg hb hc
    nlinarith only [h,hprod,sq_nonneg b,sq_nonneg c]

/-- Two is the sharp uniform local dilation factor for nonnegative two-coordinate energy control. -/
theorem nonnegative_two_coordinate_factor_iff (κ : ℝ) :
    (∀ a b c e : ℝ,0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ e →
      b ≤ κ*a → c ≤ κ*a → e ≤ κ*b → e ≤ κ*c →
      (a-b-c+e)^(2 : ℕ) ≤ a^(2 : ℕ)+b^(2 : ℕ)+c^(2 : ℕ)+e^(2 : ℕ)) ↔ κ ≤ 2 := by
  constructor
  · intro h
    by_contra hn
    have hk : 2 < κ := lt_of_not_ge hn
    have hs := h 1 κ κ 0 (by norm_num) (by linarith) (by linarith) (by norm_num)
      (by simp) (by simp) (by nlinarith only [sq_nonneg κ]) (by nlinarith only [sq_nonneg κ])
    have hp := mul_pos (show 0 < κ by linarith) (show 0 < κ-2 by linarith)
    nlinarith only [hs,hp]
  · intro hk a b c e ha hb hc he hba hca heb hec
    exact nonnegative_two_coordinate_square_le_of_double ha hb hc he
      (hba.trans (mul_le_mul_of_nonneg_right hk ha))
      (hca.trans (mul_le_mul_of_nonneg_right hk ha))
      (heb.trans (mul_le_mul_of_nonneg_right hk hb))
      (hec.trans (mul_le_mul_of_nonneg_right hk hc))

/-- A comparison at the two adjacent unit-cofactor cutoffs survives every clipped dilation exactly. -/
theorem divisorUnsignedDilationChannel_le_mul_of_adjacent
    (M d p : ℕ) (κ : ℝ) (hd : 0 < d)
    (h0 : divisorUnsignedDilationChannel (M/d) p ≤ κ*divisorUnsignedDilationChannel (M/d) 1)
    (h1 : divisorUnsignedDilationChannel (M/d+1) p ≤ κ*divisorUnsignedDilationChannel (M/d+1) 1) :
    divisorUnsignedDilationChannel M (p*d) ≤ κ*divisorUnsignedDilationChannel M d := by
  have hleft := divisorUnsignedDilationChannel_prime_interpolation M d p hd
  have hright := divisorUnsignedDilationChannel_prime_interpolation M d 1 hd
  simp only [Nat.mul_one] at hright
  have hw0 := divisorPrimeClipWeight_nonneg M d hd
  have hw1 : 0 ≤ 1-divisorPrimeClipWeight M d := by
    have := divisorPrimeClipWeight_lt_one M d hd
    linarith
  have hsum := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left h0 hw1) (mul_le_mul_of_nonneg_left h1 hw0))
    (Real.sqrt_nonneg (d:ℝ))
  rw [Nat.mul_comm p d,hleft,hright]
  nlinarith only [hsum]

/-- All dilation comparisons are equivalent to their unit-cofactor restrictions; zero channels are included. -/
theorem divisorUnsignedDilation_comparison_iff_unit (p : ℕ) (κ : ℝ) :
    (∀ M d : ℕ,divisorUnsignedDilationChannel M (p*d) ≤ κ*divisorUnsignedDilationChannel M d) ↔
      ∀ N : ℕ,divisorUnsignedDilationChannel N p ≤ κ*divisorUnsignedDilationChannel N 1 := by
  constructor
  · intro h N
    simpa only [Nat.mul_one] using h N 1
  · intro h M d
    by_cases hd : d=0
    · subst d
      simp [divisorUnsignedDilationChannel,primeFreeDivisorDefect]
    · exact divisorUnsignedDilationChannel_le_mul_of_adjacent M d p κ (by omega) (h _) (h _)

/-- An original oriented prime label is exactly the unsigned channel at its prime product. -/
theorem mobiusDivisorOrientedFibre_empty_eq_unsigned_product
    (R : Finset ℕ) (hR : ∀ p ∈ R,p.Prime) (M : ℕ) :
    mobiusDivisorOrientedFibre M ∅ R = divisorUnsignedDilationChannel M (∏ p ∈ R,p) := by
  induction R using Finset.induction_on generalizing M with
  | empty =>
    simpa [mobiusDivisorOrientedFibre] using mobiusDivisorSelectionHead_empty_eq_unit_channel M
  | @insert p R hpR ih =>
    have hp := hR p (mem_insert_self p R)
    have hr : ∀ q ∈ R,q.Prime := fun q hq => hR q (mem_insert_of_mem hq)
    have hF := mobiusDivisorSelectionFibre_prime_interpolation hp M ∅ R (by simp) hpR
    have hA := ih hr (M/p)
    have hB := ih hr (M/p+1)
    have hscale := divisorUnsignedDilationChannel_prime_interpolation M p (∏ q ∈ R,q) hp.pos
    rw [prod_insert hpR,hscale]
    unfold mobiusDivisorOrientedFibre
    rw [card_insert_of_notMem hpR,pow_succ,hF,mobiusDivisorInterpolatedFibre]
    unfold mobiusDivisorOrientedFibre at hA hB
    rw [← hA,← hB]
    ring

private theorem two_label_split (U : Finset ℕ) (p q : ℕ)
    (hp : p ∈ U) (hq : q ∈ U) (hpq : p≠q) (f : Finset ℕ → ℝ) :
    (∑ R ∈ U.powerset,f R) =
      ∑ R ∈ ((U.erase p).erase q).powerset,(f R+f (insert p R)+f (insert q R)+f (insert p (insert q R))) := by
  let T := (U.erase p).erase q
  have hpT : p ∉ T := by simp [T]
  have hqT : q ∉ T := by simp [T]
  have hU : U=insert q (insert p T) := by
    ext x
    simp only [mem_insert,mem_erase,T]
    constructor
    · intro hx
      by_cases hxq : x=q
      · exact Or.inl hxq
      by_cases hxp : x=p
      · exact Or.inr (Or.inl hxp)
      exact Or.inr (Or.inr ⟨hxq,hxp,hx⟩)
    · rintro (rfl|rfl|hx)
      · exact hq
      · exact hp
      · exact hx.2.2
  conv_lhs => rw [hU]
  rw [sum_powerset_insert (by simp [hpq.symm,hqT]),sum_powerset_insert hpT,
    sum_powerset_insert hpT,← sum_add_distrib,← sum_add_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro R _
  rw [insert_comm q p R]
  ring

private theorem label_not_mem {U : Finset ℕ} {p q : ℕ} {R : Finset ℕ}
    (hR : R ∈ ((U.erase p).erase q).powerset) : p ∉ R ∧ q ∉ R := by
  constructor <;> intro h
  · have := mem_powerset.mp hR h
    simp at this
  · have := mem_powerset.mp hR h
    simp at this

/-- Exact decomposition of the original energy into every two-prime cofactor block. -/
theorem mobiusDivisorSelectionEnergy_empty_eq_two_prime_blocks
    (M : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpM : p<M) (hqM : q<M) (hpq : p≠q) :
    mobiusDivisorSelectionEnergy M ∅ =
      ∑ R ∈ (((mobiusDivisorSelectionPrimes M).erase p).erase q).powerset,
        ((mobiusDivisorOrientedFibre M ∅ R)^(2 : ℕ)+
        (mobiusDivisorOrientedFibre M ∅ (insert p R))^(2 : ℕ)+
        (mobiusDivisorOrientedFibre M ∅ (insert q R))^(2 : ℕ)+
        (mobiusDivisorOrientedFibre M ∅ (insert p (insert q R)))^(2 : ℕ)) := by
  have hpU : p ∈ mobiusDivisorSelectionPrimes M := mem_filter.mpr ⟨mem_range.mpr hpM,hp⟩
  have hqU : q ∈ mobiusDivisorSelectionPrimes M := mem_filter.mpr ⟨mem_range.mpr hqM,hq⟩
  simp_rw [mobiusDivisorOrientedFibre_sq]
  exact two_label_split _ p q hpU hqU hpq (fun R => (mobiusDivisorSelectionFibre M ∅ R)^(2 : ℕ))

/-- Processing two primes leaves the alternating sum in every original four-coefficient block. -/
theorem mobiusDivisorSelectionEnergy_two_primes_eq_blocks
    (M p q : ℕ) (hpq : p≠q) :
    mobiusDivisorSelectionEnergy M (insert q {p}) =
      ∑ R ∈ (((mobiusDivisorSelectionPrimes M).erase p).erase q).powerset,
        (mobiusDivisorOrientedFibre M ∅ R-
        mobiusDivisorOrientedFibre M ∅ (insert p R)-
        mobiusDivisorOrientedFibre M ∅ (insert q R)+
        mobiusDivisorOrientedFibre M ∅ (insert p (insert q R)))^(2 : ℕ) := by
  change subsetLabelEnergy _ _ _ _ _ = _
  rw [subsetLabelEnergy_remaining]
  have he : mobiusDivisorSelectionPrimes M \ insert q {p} =
      ((mobiusDivisorSelectionPrimes M).erase p).erase q := by
    ext x
    simp only [mem_sdiff,mem_insert,mem_singleton,mem_erase]
    tauto
  rw [he]
  apply sum_congr rfl
  intro R hR
  change (mobiusDivisorSelectionFibre M (insert q {p}) R)^(2 : ℕ) = _
  rw [← mobiusDivisorOrientedFibre_sq]
  obtain ⟨hpR,hqR⟩ := label_not_mem hR
  rw [mobiusDivisorOrientedFibre_insert M {p} R q hqR]
  rw [show ({p}:Finset ℕ)=insert p ∅ by rfl,
    mobiusDivisorOrientedFibre_insert M ∅ R p hpR,
    mobiusDivisorOrientedFibre_insert M ∅ (insert q R) p (by simp [hpq,hpR])]
  ring

private theorem two_prime_ceiling_of_bounded_unit_double
    (M : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpM : p<M) (hqM : q<M) (hpq : p≠q)
    (hunit : ∀ (N : ℕ),N ≤ M → ∀ r : ℕ,r=p ∨ r=q →
      divisorUnsignedDilationChannel N r ≤ 2*divisorUnsignedDilationChannel N 1) :
    mobiusDivisorSelectionEnergy M (insert q {p}) ≤ mobiusDivisorSelectionEnergy M ∅ := by
  have hdouble (R : Finset ℕ) (hR : ∀ r ∈ R,r.Prime) (r : ℕ) (hr : r.Prime) (hrR : r ∉ R) (hrpq : r=p ∨ r=q) :
      mobiusDivisorOrientedFibre M ∅ (insert r R) ≤ 2*mobiusDivisorOrientedFibre M ∅ R := by
    rw [mobiusDivisorOrientedFibre_empty_eq_unsigned_product _ (by simpa using And.intro hr hR),
      mobiusDivisorOrientedFibre_empty_eq_unsigned_product _ hR,prod_insert hrR]
    have hd : 0 < ∏ t ∈ R,t := Finset.prod_pos (fun t ht => (hR t ht).pos)
    by_cases hd1 : (∏ t ∈ R,t)=1
    · rw [hd1,Nat.mul_one]
      exact hunit M le_rfl r hrpq
    · have hN := Nat.div_lt_self (hp.pos.trans hpM) (show 1 < ∏ t ∈ R,t by omega)
      exact divisorUnsignedDilationChannel_le_mul_of_adjacent M _ r 2 hd
        (hunit _ (by omega) r hrpq) (hunit _ (by omega) r hrpq)
  rw [mobiusDivisorSelectionEnergy_two_primes_eq_blocks M p q hpq,
    mobiusDivisorSelectionEnergy_empty_eq_two_prime_blocks M hp hq hpM hqM hpq]
  apply sum_le_sum
  intro R hR
  obtain ⟨hpR,hqR⟩ := label_not_mem hR
  have hpr : ∀ r ∈ R,r.Prime := by
    intro r hr
    have h := mem_powerset.mp hR hr
    exact (mem_filter.mp (mem_erase.mp (mem_erase.mp h).2).2).2
  have hpi : ∀ r ∈ insert p R,r.Prime := by simpa using And.intro hp hpr
  have hqi : ∀ r ∈ insert q R,r.Prime := by simpa using And.intro hq hpr
  have hec := hdouble (insert q R) hqi p hp (by simp [hpq,hpR]) (Or.inl rfl)
  have heb := hdouble (insert p R) hpi q hq (by simp [hpq.symm,hqR]) (Or.inr rfl)
  rw [insert_comm q p R] at heb
  exact nonnegative_two_coordinate_square_le_of_double
    (mobiusDivisorSelectionFibre_empty_parity_nonneg M R)
    (mobiusDivisorSelectionFibre_empty_parity_nonneg M (insert p R))
    (mobiusDivisorSelectionFibre_empty_parity_nonneg M (insert q R))
    (mobiusDivisorSelectionFibre_empty_parity_nonneg M (insert p (insert q R)))
    (hdouble R hpr p hp hpR (Or.inl rfl)) (hdouble R hpr q hq hqR (Or.inr rfl)) heb hec

/-- Every two-prime ceiling failure exposes a unit-cofactor factor-two failure for one of those primes at a bounded cutoff. -/
theorem mobiusDivisorSelectionEnergy_two_primes_le_or_unit_failure
    (M : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpM : p<M) (hqM : q<M) (hpq : p≠q) :
    mobiusDivisorSelectionEnergy M (insert q {p}) ≤ mobiusDivisorSelectionEnergy M ∅ ∨
      ∃ (N r : ℕ),r < N ∧ N ≤ M ∧ (r=p ∨ r=q) ∧
        2*divisorUnsignedDilationChannel N 1 < divisorUnsignedDilationChannel N r := by
  by_cases hunit : ∀ (N : ℕ),N ≤ M → ∀ r : ℕ,r=p ∨ r=q →
      divisorUnsignedDilationChannel N r ≤ 2*divisorUnsignedDilationChannel N 1
  · exact Or.inl (two_prime_ceiling_of_bounded_unit_double M hp hq hpM hqM hpq hunit)
  · push Not at hunit
    obtain ⟨N,hN,r,hr,hfail⟩ := hunit
    have hrprime : r.Prime := hr.elim (fun h => h ▸ hp) (fun h => h ▸ hq)
    have hrN : r < N := by
      by_contra hn
      have hz : divisorUnsignedDilationChannel N r=0 := by
        simp [divisorUnsignedDilationChannel,Icc_eq_empty_of_lt (by have := hrprime.pos; omega : N-1<r)]
      have hnonneg := divisorUnsignedDilationChannel_nonneg N 1
      rw [hz] at hfail
      linarith only [hfail,hnonneg]
    exact Or.inr ⟨N,r,hrN,hN,hr,hfail⟩
end RHTower
