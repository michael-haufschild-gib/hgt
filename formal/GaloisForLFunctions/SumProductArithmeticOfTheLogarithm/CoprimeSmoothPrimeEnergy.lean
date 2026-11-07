import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.CumulativeSmoothPrimeEnergy
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic

/-!
# Coprime density in smooth-times-prime energy

For smooth rows `m,n` with gcd `g`, an actual prime-column collision at
difference `h` forces `h/g` to be coprime to `(m/g)*(n/g)`. The cumulative
fixed-row count through `H` is therefore at most `g` times the number of
these coprime integers through `H/g`, and never exceeds `H`.

Every positive divisor `d` of the reduced row product gives the finite bound
`g * (floor((H/g)/d)+1) * totient(d)`, by quotient and residue labels.
Summing actual row pairs and using the integer logarithmic cutoff retains
this arithmetic density in the full fine-energy envelope. No prime-pair
asymptotic or analytic positivity input is used.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open GaloisForLFunctions.Goldbach

/-- Positive integers through `H` coprime to a fixed modulus. -/
def coprimeDifferenceCount (N H : ℕ) : ℕ :=
  ((Icc 1 H).filter fun h => Nat.Coprime h N).card

/-- Quotient and residue labels retain the density of every divisor of the modulus. -/
theorem coprimeDifferenceCount_le_totient {N d : ℕ} (hd : 0 < d) (hdN : d ∣ N) (H : ℕ) :
    coprimeDifferenceCount N H ≤ (H / d + 1) * d.totient := by
  classical
  let F : Finset ℕ := (Icc 1 H).filter fun v => Nat.Coprime v N
  let R : Finset ℕ := (range d).filter fun r => Nat.Coprime d r
  let label : ↥F → Fin (H / d + 1) × ↥R := fun v =>
    (⟨v.val / d, by
      have hle : v.val / d ≤ H / d := Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp v.property).1).2
      omega⟩,
     ⟨v.val % d, mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt v.val hd),
       ((ZMod.coprime_mod_iff_coprime v.val d).mpr
         ((mem_filter.mp v.property).2.coprime_dvd_right hdN)).symm⟩⟩)
  have hinj : Function.Injective label := by
    intro v w he
    have hq : v.val / d = w.val / d := congrArg (fun p : Fin (H / d + 1) × ↥R => (p.1 : ℕ)) he
    have hr : v.val % d = w.val % d := congrArg (fun p : Fin (H / d + 1) × ↥R => p.2.val) he
    apply Subtype.ext
    rw [← Nat.mod_add_div v.val d, ← Nat.mod_add_div w.val d, hr, hq]
  simpa only [coprimeDifferenceCount, F, R, Fintype.card_coe,
    Fintype.card_prod, Fintype.card_fin, ← Nat.totient_eq_card_coprime] using
    Fintype.card_le_of_injective label hinj

/-- Discarding the coprimality restriction recovers the interval length. -/
theorem coprimeDifferenceCount_le (N H : ℕ) : coprimeDifferenceCount N H ≤ H := by
  unfold coprimeDifferenceCount
  exact ((Icc 1 H).card_filter_le _).trans_eq (by
    simp only [Nat.card_Icc, Nat.add_sub_cancel])

/-- Both determinant gcd identities force coprimality after removing the common row gcd. -/
theorem reduced_difference_coprime {m n h : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hleft : Nat.gcd m h = Nat.gcd m n) (hright : Nat.gcd n h = Nat.gcd m n) :
    Nat.Coprime (h / Nat.gcd m n) ((m / Nat.gcd m n) * (n / Nat.gcd m n)) := by
  have h1 := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left h hm)
  have h2 := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left h hn)
  rw [hleft] at h1
  rw [hright] at h2
  exact h1.symm.mul_right h2.symm

private theorem card_compatible_differences_le {m n H : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ((Icc 1 H).filter fun h => Nat.gcd m h = Nat.gcd m n ∧
      Nat.gcd n h = Nat.gcd m n).card ≤
      coprimeDifferenceCount ((m / Nat.gcd m n) * (n / Nat.gcd m n)) (H / Nat.gcd m n) := by
  let g := Nat.gcd m n
  have hg : 0 < g := Nat.gcd_pos_of_pos_left n hm
  apply card_le_card_of_injOn (fun h => h / g)
  · intro h hh
    obtain ⟨hH, hleft, hright⟩ := mem_filter.mp hh
    have hdiv : g ∣ h := by
      dsimp only [g]
      rw [← hleft]
      exact Nat.gcd_dvd_right m h
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_, Nat.div_le_div_right (mem_Icc.mp hH).2⟩,
      reduced_difference_coprime hm hn hleft hright⟩
    exact Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hH).1 hdiv) hg
  · intro h hh h' hh' he
    have hd : g ∣ h := by
      dsimp only [g]
      rw [← (mem_filter.mp hh).2.1]
      exact Nat.gcd_dvd_right m h
    have hd' : g ∣ h' := by
      dsimp only [g]
      rw [← (mem_filter.mp hh').2.1]
      exact Nat.gcd_dvd_right m h'
    calc
      h = g * (h / g) := (Nat.mul_div_cancel' hd).symm
      _ = g * (h' / g) := congrArg (g * ·) he
      _ = h' := Nat.mul_div_cancel' hd'

/-- Fixed smooth rows retain the coprime density of their reduced differences. -/
theorem cumulative_smooth_prime_fiber_le_coprime {X y : ℕ} (m n : Fin X)
    (hm : m ∈ smoothRows X y) (hn : n ∈ smoothRows X y) (H : ℕ) :
    (∑ h ∈ Icc 1 H, (smoothPrimeCollisionFiber y m n h).card) ≤
      let g := Nat.gcd (balancedIntervalValue m) (balancedIntervalValue n)
      g * coprimeDifferenceCount ((balancedIntervalValue m / g) * (balancedIntervalValue n / g)) (H / g) := by
  let a := balancedIntervalValue m
  let b := balancedIntervalValue n
  let g := Nat.gcd a b
  have hpoint (h : ℕ) : (smoothPrimeCollisionFiber y m n h).card ≤
      if Nat.gcd a h = g ∧ Nat.gcd b h = g then g else 0 := by
    by_cases hf : (smoothPrimeCollisionFiber y m n h).Nonempty
    · obtain ⟨p, hp⟩ := hf
      obtain ⟨hcols, he⟩ := mem_filter.mp hp
      have hp1 := (mem_filter.mp (mem_product.mp hcols).1).2
      have hp2 := (mem_filter.mp (mem_product.mp hcols).2).2
      have hgate := smooth_prime_determinant_gcd (mem_filter.mp hm).2 (mem_filter.mp hn).2
        hp1.1 hp2.1 hp1.2 hp2.2 he
      rw [if_pos hgate]
      apply le_trans _ (card_balancedProductCollisionFiber_le_gcd m n h)
      apply card_le_card
      intro p hp
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩
    · rw [not_nonempty_iff_eq_empty.mp hf, card_empty]
      exact Nat.zero_le _
  calc
    _ ≤ ∑ h ∈ Icc 1 H, if Nat.gcd a h = g ∧ Nat.gcd b h = g then g else 0 :=
      sum_le_sum fun h _ => hpoint h
    _ = g * ((Icc 1 H).filter fun h => Nat.gcd a h = g ∧ Nat.gcd b h = g).card := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, Nat.cast_id]
      ring
    _ ≤ _ := Nat.mul_le_mul_left g
      (card_compatible_differences_le (balancedIntervalValue_pos m) (balancedIntervalValue_pos n))

/-- Each small divisor of the reduced row product gives a finite density bound. -/
theorem cumulative_smooth_prime_fiber_le_totient {X y d : ℕ} (m n : Fin X)
    (hm : m ∈ smoothRows X y) (hn : n ∈ smoothRows X y) (H : ℕ)
    (hd : 0 < d)
    (hdN : d ∣ (balancedIntervalValue m / Nat.gcd (balancedIntervalValue m) (balancedIntervalValue n)) *
      (balancedIntervalValue n / Nat.gcd (balancedIntervalValue m) (balancedIntervalValue n))) :
    (∑ h ∈ Icc 1 H, (smoothPrimeCollisionFiber y m n h).card) ≤
      Nat.gcd (balancedIntervalValue m) (balancedIntervalValue n) *
        (H / Nat.gcd (balancedIntervalValue m) (balancedIntervalValue n) / d + 1) * d.totient := by
  apply (cumulative_smooth_prime_fiber_le_coprime m n hm hn H).trans
  calc
    _ ≤ Nat.gcd (balancedIntervalValue m) (balancedIntervalValue n) *
        ((H / Nat.gcd (balancedIntervalValue m) (balancedIntervalValue n) / d + 1) * d.totient) :=
      Nat.mul_le_mul_left _ (coprimeDifferenceCount_le_totient hd hdN _)
    _ = _ := by ring

/-- Row-pair cost retaining the coprime reduced differences. -/
def smoothCoprimeDifferenceCost (X y H : ℕ) : ℕ :=
  ∑ m ∈ smoothRows X y, ∑ n ∈ smoothRows X y,
    let g := Nat.gcd (balancedIntervalValue m) (balancedIntervalValue n)
    g * coprimeDifferenceCount ((balancedIntervalValue m / g) * (balancedIntervalValue n / g)) (H / g)

/-- The actual cumulative prime-column census retains the reduced-row arithmetic density. -/
theorem cumulative_smooth_prime_collision_le_coprime (X y H : ℕ) :
    (∑ h ∈ Icc 1 H, smoothPrimeCollisionCount X y h) ≤ smoothCoprimeDifferenceCost X y H := by
  calc
    _ = ∑ m ∈ smoothRows X y, ∑ n ∈ smoothRows X y,
        ∑ h ∈ Icc 1 H, (smoothPrimeCollisionFiber y m n h).card := by
      unfold smoothPrimeCollisionCount
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      rw [sum_comm]
    _ ≤ _ := sum_le_sum fun m hm => sum_le_sum fun n hn =>
      cumulative_smooth_prime_fiber_le_coprime m n hm hn H

/-- The retained arithmetic cost never exceeds the uniform cumulative envelope. -/
theorem smoothCoprimeDifferenceCost_le (X y H : ℕ) :
    smoothCoprimeDifferenceCost X y H ≤ H * (smoothRows X y).card ^ 2 := by
  have hrow (m n : Fin X) :
      let g := Nat.gcd (balancedIntervalValue m) (balancedIntervalValue n)
      g * coprimeDifferenceCount ((balancedIntervalValue m / g) * (balancedIntervalValue n / g)) (H / g) ≤ H := by
    dsimp only
    exact (Nat.mul_le_mul_left _ (coprimeDifferenceCount_le _ _)).trans (Nat.mul_div_le H _)
  calc
    _ ≤ ∑ m ∈ smoothRows X y, ∑ n ∈ smoothRows X y, H :=
      sum_le_sum fun m _ => sum_le_sum fun n _ => hrow m n
    _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]; ring

/-- Fine energy retains the coprime-density refinement at its exact integer cutoff. -/
theorem smoothPrimeLogEnergy_le_coprime_envelope (X y : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    smoothPrimeLogEnergy X y δ ≤ (smoothRows X y).card * (roughPrimeColumns X y).card +
      2 * smoothCoprimeDifferenceCost X y ⌊4 * (X : ℝ) ^ 2 * δ⌋₊ := by
  rw [smoothPrimeLogEnergy_eq_diagonal_add_twice X y hδ]
  have h := (smoothPrimeUpperLogCount_le_floor_sum X y hδ).trans
    (cumulative_smooth_prime_collision_le_coprime X y _)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 h) _


end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
