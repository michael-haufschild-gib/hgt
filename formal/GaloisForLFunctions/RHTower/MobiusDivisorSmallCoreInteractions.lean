import GaloisForLFunctions.RHTower.MobiusDivisorLocalizedInteractions
import GaloisForLFunctions.RHTower.MobiusDivisorQuotientWindowOrder

/-!
# Mixed interactions depend only on the active small-prime core

When two unprocessed primes have product at least the source cutoff, their
joint child vanishes. The exact mixed second energy difference then depends
only on the copied children, hence only on processed primes below their two
adjacent quotient cutoffs. This removes dependence on arbitrarily many other
processed primes, including states with arbitrary signed defects.

The resulting bound is uniform at fixed quotient depth. First energy gains
and overlapping pairs still need an arithmetic budget for complete extension.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

private lemma fibre_filter_cutoff (n N : ℕ) (P R : Finset ℕ) (hn : n≤N) :
    mobiusDivisorSelectionFibre n P R=
      mobiusDivisorSelectionFibre n (P.filter (fun r => r<N)) R := by
  have he : P=P.filter (fun r => r<N) ∪ P.filter (fun r => N≤r) := by
    ext r
    by_cases hr : r<N
    · simp [hr]
    · have hNr : N≤r := by omega
      simp [hr,hNr]
  calc
    _ = mobiusDivisorSelectionFibre n
        (P.filter (fun r => r<N) ∪ P.filter (fun r => N≤r)) R :=
      congrArg (fun S => mobiusDivisorSelectionFibre n S R) he
    _ = _ := mobiusDivisorSelectionFibre_union_inactive n _ _ R
      (fun r hr => hn.trans (mem_filter.mp hr).2)

/-- An unprocessed prime-containing fibre ignores processed primes outside
its two adjacent quotient cutoffs, with no retained-sign condition. -/
theorem mobiusDivisorSelectionFibre_partner_filter_cutoff (M N : ℕ) (P R : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hpP : p∉P) (hpR : p∉R) (hN : M/p+1≤N) :
    mobiusDivisorSelectionFibre M P (insert p R)=
      mobiusDivisorSelectionFibre M (P.filter (fun r => r<N)) (insert p R) := by
  rw [mobiusDivisorSelectionFibre_prime_interpolation hp M P R hpP hpR,
    mobiusDivisorSelectionFibre_prime_interpolation hp M _ R
      (fun h => hpP (mem_filter.mp h).1) hpR]
  unfold mobiusDivisorInterpolatedFibre
  rw [fibre_filter_cutoff (M/p) N P R (by omega),
    fibre_filter_cutoff (M/p+1) N P R hN]

private lemma joint_zero (M : ℕ) (P R : Finset ℕ) {p q : ℕ}
    (hpR : p∉R) (hqR : q∉R) (hpq : p≠q) (hprod : M≤p*q)
    (hR : ∀ r∈R,r.Prime) :
    mobiusDivisorSelectionFibre M P (insert p (insert q R))=0 := by
  apply mobiusDivisorSelectionFibre_eq_zero_of_le_product
  rw [prod_insert (by simp [hpq,hpR]),prod_insert hqR]
  have hRpos : 1≤∏ r∈R,r := prod_pos (fun r hr => (hR r hr).pos)
  calc
    M ≤ p*q := hprod
    _ = (p*q)*1 := by ring
    _ ≤ (p*q)*(∏ r∈R,r) := Nat.mul_le_mul_left _ hRpos
    _ = _ := by ring

/-- Above the joint-product threshold, the complete signed mixed interaction
is unchanged when all processed primes outside the quotient core are removed. -/
theorem mobiusDivisorSelectionEnergy_mixed_eq_filter_cutoff
    (M N : ℕ) (P : Finset ℕ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpM : p<M) (hqM : q<M)
    (hpP : p∉P) (hqP : q∉P) (hpq : p≠q) (hprod : M≤p*q)
    (hpN : M/p+1≤N) (hqN : M/q+1≤N) :
    mobiusDivisorSelectionEnergy M (insert q (insert p P))-
      mobiusDivisorSelectionEnergy M (insert p P)-
      mobiusDivisorSelectionEnergy M (insert q P)+mobiusDivisorSelectionEnergy M P =
    mobiusDivisorSelectionEnergy M (insert q (insert p (P.filter (fun r => r<N))))-
      mobiusDivisorSelectionEnergy M (insert p (P.filter (fun r => r<N)))-
      mobiusDivisorSelectionEnergy M (insert q (P.filter (fun r => r<N)))+
      mobiusDivisorSelectionEnergy M (P.filter (fun r => r<N)) := by
  rw [mobiusDivisorSelectionEnergy_mixed_eq M P hp hq hpM hqM hpP hqP hpq,
    mobiusDivisorSelectionEnergy_mixed_eq M _ hp hq hpM hqM
      (fun h => hpP (mem_filter.mp h).1) (fun h => hqP (mem_filter.mp h).1) hpq]
  congr 1
  apply sum_congr rfl
  intro R hR
  have hpR : p∉R := fun h => (mem_erase.mp (mem_powerset.mp hR h)).1 rfl
  have hqR : q∉R := fun h => (mem_erase.mp (mem_erase.mp (mem_powerset.mp hR h)).2).1 rfl
  have hprime : ∀ r∈R,r.Prime := by
    intro r hr
    exact (mem_filter.mp (mem_erase.mp (mem_erase.mp (mem_powerset.mp hR hr)).2).2).2
  rw [joint_zero M P R hpR hqR hpq hprod hprime,
    joint_zero M (P.filter (fun r => r<N)) R hpR hqR hpq hprod hprime,
    mul_zero,mul_zero,zero_add,zero_add,
    mobiusDivisorSelectionFibre_partner_filter_cutoff M N P R hp hpP hpR hpN,
    mobiusDivisorSelectionFibre_partner_filter_cutoff M N P R hq hqP hqR hqN]

/-- The mixed interaction costs only the active small-prime core, regardless
of the number and signs of all other already processed coordinates. -/
theorem abs_mobiusDivisorSelectionEnergy_mixed_le_small_core
    (M N : ℕ) (P : Finset ℕ) (hP : ∀ r∈P,r.Prime) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpM : p<M) (hqM : q<M)
    (hpP : p∉P) (hqP : q∉P) (hpq : p≠q) (hprod : M≤p*q)
    (hpN : M/p+1≤N) (hqN : M/q+1≤N) :
    |mobiusDivisorSelectionEnergy M (insert q (insert p P))-
      mobiusDivisorSelectionEnergy M (insert p P)-
      mobiusDivisorSelectionEnergy M (insert q P)+mobiusDivisorSelectionEnergy M P|≤
        (18/25:ℝ)*4^((P.filter (fun r => r<N)).card-1)*(M:ℝ)*
          ((M-1)/max p q:ℕ) := by
  rw [mobiusDivisorSelectionEnergy_mixed_eq_filter_cutoff M N P hp hq hpM hqM
    hpP hqP hpq hprod hpN hqN]
  have h := abs_mobiusDivisorSelectionEnergy_mixed_le_source_support M
    (P.filter (fun r => r<N)) (fun r hr => hP r (mem_filter.mp hr).1)
    hp hq hpM hqM (fun h => hpP (mem_filter.mp h).1)
    (fun h => hqP (mem_filter.mp h).1) hpq
  have hz : (M-1)/(p*q)=0 := Nat.div_eq_of_lt (by omega)
  simpa only [hz,CharP.cast_eq_zero,Nat.cast_zero,zero_add] using h

/-- At fixed quotient depth, every nonoverlapping mixed interaction is O(M)
with an explicit constant independent of the entire processed prime set. -/
theorem abs_mobiusDivisorSelectionEnergy_mixed_le_fixed_quotient
    (M L : ℕ) (P : Finset ℕ) (hP : ∀ r∈P,r.Prime) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpM : p<M) (hqM : q<M)
    (hpP : p∉P) (hqP : q∉P) (hpq : p≠q) (hprod : M≤p*q)
    (hpL : M/p≤L) (hqL : M/q≤L) :
    |mobiusDivisorSelectionEnergy M (insert q (insert p P))-
      mobiusDivisorSelectionEnergy M (insert p P)-
      mobiusDivisorSelectionEnergy M (insert q P)+mobiusDivisorSelectionEnergy M P|≤
        (18/25:ℝ)*4^L*(L:ℝ)*(M:ℝ) := by
  have hb := abs_mobiusDivisorSelectionEnergy_mixed_le_small_core M (L+1) P hP
    hp hq hpM hqM hpP hqP hpq hprod (by omega) (by omega)
  have hc : (P.filter (fun r => r<L+1)).card≤L+1 := by
    calc
      _ ≤ (range (L+1)).card := card_le_card
        (fun r hr => mem_range.mpr (mem_filter.mp hr).2)
      _ = _ := card_range _
  have hpow : (4:ℝ)^((P.filter (fun r => r<L+1)).card-1)≤4^L :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hdiv : (M-1)/max p q≤L :=
    (Nat.div_le_div_right (Nat.sub_le M 1)).trans
      ((Nat.div_le_div_left (le_max_right p q) hq.pos).trans hqL)
  calc
    _ ≤ (18/25:ℝ)*4^((P.filter (fun r => r<L+1)).card-1)*(M:ℝ)*
        ((M-1)/max p q:ℕ) := hb
    _ ≤ (18/25:ℝ)*4^L*(M:ℝ)*(L:ℝ) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by norm_num)) (Nat.cast_nonneg M))
        (by exact_mod_cast hdiv) (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end RHTower
