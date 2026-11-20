import GaloisForLFunctions.RestrictedFactorizationCalculus.TheTotalVariationOfTheFirstRoughPrimeBand
import GaloisForLFunctions.ArithmeticPositiveDuality.ARationalPrimeBeurlingOneOff

/-!
# The two sign boundaries of polynomial rough cofactor bands

The unit survives until the first allowed prime. The next prime ends the
zero interval. Bertrand's theorem places both changes before the first
possible composite, and the uniform negative-charge estimate prevents
any further return to zero in a fixed polynomial range.
-/
noncomputable section
open Finset Filter ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticPositiveDuality.RationalPrimeOneOff
open scoped Classical
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Least prime strictly greater than the integer wall. -/
def nextRoughPrime (y : ℕ) := nextPrime ((y+1 : ℕ) : ℝ)

private abbrev F (y m : ℕ) := coprimeMoebiusSum (primorial y) m
private abbrev primes := _root_.RHTower.Sieve.bigPrimeSet

private theorem next_spec (y : ℕ) : (nextRoughPrime y).Prime ∧ y < nextRoughPrime y := by
  refine ⟨nextPrime_prime _,?_⟩
  change y+1 ≤ _
  exact_mod_cast le_nextPrime ((y+1 : ℕ) : ℝ)

private theorem next_min {p y : ℕ} (hp : p.Prime) (above : y < p) : nextRoughPrime y ≤ p :=
  nextPrime_le hp (by exact_mod_cast above)

private theorem next_double {y : ℕ} (h : 0 < y) : nextRoughPrime y ≤ 2*y := by
  obtain ⟨p,hp,hy,hi⟩ := Nat.exists_prime_lt_and_le_two_mul y h.ne'
  exact (next_min hp hy).trans hi

private theorem second_before_square {y : ℕ} (hy : 4 ≤ y) :
    nextRoughPrime (nextRoughPrime y) ≤ y^2 := by
  have h := next_double (next_spec y).1.pos
  have h' := Nat.mul_le_mul_left 2 (next_double (show 0 < y by omega))
  have mul := Nat.mul_le_mul_right y hy
  calc _ ≤ 2*(2*y) := h.trans h'
       _ = 4*y := by ring
       _ ≤ _ := by simpa only [pow_two] using mul

private theorem prime_member {y m p : ℕ} :
    p ∈ primes y m ↔ y < p ∧ p ≤ m ∧ p.Prime := by
  simp only [primes,_root_.RHTower.Sieve.bigPrimeSet,mem_filter,mem_Icc]
  omega

private theorem before_first {y m : ℕ} (h : m < nextRoughPrime y) :
    primes y m = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p member
  obtain ⟨lo,hi,hp⟩ := prime_member.mp member
  exact h.not_ge ((next_min hp lo).trans hi)

private theorem between_first_two {y m : ℕ} (h₁ : nextRoughPrime y ≤ m)
    (h₂ : m < nextRoughPrime (nextRoughPrime y)) : primes y m = {nextRoughPrime y} := by
  ext p
  rw [mem_singleton]
  constructor
  · intro member
    obtain ⟨lo,hi,hp⟩ := prime_member.mp member
    apply le_antisymm _ (next_min hp lo)
    by_contra! larger
    exact h₂.not_ge ((next_min hp larger).trans hi)
  · rintro rfl
    exact prime_member.mpr ⟨(next_spec y).2,h₁,(next_spec y).1⟩

private theorem after_second {y m : ℕ} (h : nextRoughPrime (nextRoughPrime y) ≤ m) :
    2 ≤ (primes y m).card := by
  let p := nextRoughPrime y
  let q := nextRoughPrime p
  have hp := next_spec y
  have hq := next_spec p
  have smaller : p < q := hq.2
  have memp : p ∈ primes y m := prime_member.mpr ⟨hp.2,smaller.le.trans h,hp.1⟩
  have memq : q ∈ primes y m := prime_member.mpr ⟨hp.2.trans smaller,h,hq.1⟩
  have sub : ({p,q} : Finset ℕ) ⊆ primes y m := by
    intro n hn
    rcases mem_insert.mp hn with rfl|hn
    · exact memp
    · rw [mem_singleton.mp hn]; exact memq
  simpa only [card_pair smaller.ne] using card_le_card sub

/-- For all sufficiently large walls, the three signs are determined by
the first two allowed primes throughout the entire fixed polynomial band. -/
theorem sign_boundaries_of_polynomial_rough_prefix (j : ℕ) :
    ∀ᶠ y : ℕ in atTop, ∀ m : ℕ, 0 < m → m ≤ y^j →
      (0 < F y m ↔ m < nextRoughPrime y) ∧
      (F y m = 0 ↔ nextRoughPrime y ≤ m ∧ m < nextRoughPrime (nextRoughPrime y)) ∧
      (F y m < 0 ↔ nextRoughPrime (nextRoughPrime y) ≤ m) ∧
      (m < nextRoughPrime y → F y m = 1) := by
  filter_upwards [one_sided_rough_prefix_on_polynomial_ranges j,eventually_ge_atTop 4] with y hsign hy
  intro m hm hband
  let p := nextRoughPrime y
  let q := nextRoughPrime p
  have pq : p < q := (next_spec p).2
  have qy : q ≤ y^2 := second_before_square hy
  by_cases h₁ : m < p
  · have hz : F y m = 1 := by
      unfold F
      rw [rough_prefix_before_composites hm ((h₁.trans pq).le.trans qy),before_first h₁]
      simp
    exact ⟨iff_of_true (hz.symm ▸ zero_lt_one) h₁,
      iff_of_false (by rw [hz];exact one_ne_zero) (fun h => h₁.not_ge h.1),
      iff_of_false (by rw [hz];exact not_lt_of_ge zero_le_one) (not_le_of_gt (h₁.trans pq)),fun _ => hz⟩
  · have pm := le_of_not_gt h₁
    by_cases h₂ : m < q
    · have hz : F y m = 0 := by
        unfold F
        rw [rough_prefix_before_composites hm (h₂.le.trans qy),between_first_two pm h₂]; simp
      exact ⟨iff_of_false (by rw [hz];exact lt_irrefl _) h₁,iff_of_true hz ⟨pm,h₂⟩,
        iff_of_false (by rw [hz];exact lt_irrefl _) h₂.not_ge,fun hf => (h₁ hf).elim⟩
    · have qm := le_of_not_gt h₂
      have hn : F y m < 0 := by
        rcases le_or_gt m (y^2) with h|h
        · have two : (2:ℝ) ≤ (primes y m).card := by exact_mod_cast after_second qm
          unfold F
          rw [rough_prefix_before_composites hm h]
          change 1-((primes y m).card:ℝ) < 0
          linarith only [two]
        · exact (hsign m hm hband).2 h
      exact ⟨iff_of_false hn.asymm h₁,iff_of_false hn.ne (fun h => h₂ h.2),
        iff_of_true hn qm,fun hf => (h₁ hf).elim⟩

/-- Throughout a polynomial range, the whole positive row is an ordinary
arithmetic interval whose endpoint is set by the next prime after the wall. -/
theorem positive_band_is_an_exact_prime_cut (j : ℕ) :
    ∀ᶠ y : ℕ in atTop, ∀ Z X : ℕ, 0 < Z → Z ≤ y^j → ∀ a : ArithmeticFunction ℝ,
      positivePrimeBandMass a y X Z = ∑ q ∈ Ioc (X/min Z (nextRoughPrime y)) X,a q := by
  filter_upwards [sign_boundaries_of_polynomial_rough_prefix j] with y signs
  intro Z X hz hZ a
  let p := nextRoughPrime y
  let K := X/Z
  let J := X/(min Z p)
  have pp : 0 < p := (next_spec y).1.pos
  have kp : 0 < min Z p := lt_min hz pp
  have kj : K ≤ J := Nat.div_le_div_left (min_le_left ..) kp
  have sets : (Ioc K X).filter (fun q => J < q) = Ioc J X := by
    ext q
    simp only [mem_filter,mem_Ioc]
    omega
  rw [← sets, sum_filter]
  apply sum_congr rfl
  intro q hq
  obtain ⟨lo,hi⟩ := mem_Ioc.mp hq
  have qp := (Nat.zero_le K).trans_lt lo
  have fq : X/q < Z := (Nat.div_lt_iff_lt_mul qp).mpr (by simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hz).mp lo)
  have eq : J < q ↔ X/q < p := by
    change X/min Z p < q ↔ _
    rw [Nat.div_lt_iff_lt_mul kp, Nat.mul_comm q, ← Nat.div_lt_iff_lt_mul qp, lt_min_iff]
    exact ⟨And.right,fun h => ⟨fq,h⟩⟩
  have hs := signs (X/q) (Nat.div_pos hi qp) (fq.le.trans hZ)
  change a q*max (F y (X/q)) 0 = _
  by_cases h : J < q
  · rw [if_pos h,hs.2.2.2 (eq.mp h),max_eq_left zero_le_one,mul_one]
  · rw [if_neg h,max_eq_right (le_of_not_gt (fun pos => h (eq.mpr (hs.1.mp pos)))),mul_zero]

end GaloisForLFunctions.RestrictedFactorizationCalculus
