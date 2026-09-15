import GaloisForLFunctions.RHTower.EulerDeletionRamareDilationEnergy
import GaloisForLFunctions.RHTower.Sieve.RamareComplex
import GaloisForLFunctions.RHTower.Sieve.RamarePhaseBilinear

/-!
# Literal physical Ramaré packets for Euler deletion

This module keeps the complete finite source in the Báez--Duarte physical
coordinate.  It is deliberately distinct from the logarithmic Dirichlet
polynomial Ramaré form: the reciprocal generator has an affine dilation
correction, and that correction must remain visible in every packet.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace RHTower.DeletionRamarePhysical

open RHTower.Sieve
open RHTower.DeletionRamareDilation

/-- The literal finite Möbius source in the physical coordinate. -/
def source (M : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 M, ((μ n : ℤ) : ℝ) * bdGenReal (1 / (n : ℝ)) u

/-- The part of the physical source with no designated prime factor. -/
def rough (P : Finset ℕ) (M : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ {n ∈ Icc 1 M | primeFactorsIn P n = ∅},
    ((μ n : ℤ) : ℝ) * bdGenReal (1 / (n : ℝ)) u

/-- The p-free cofactor packet before the physical reciprocal dilation. -/
def cofactor (P : Finset ℕ) (M p : ℕ) (u : ℝ) : ℝ :=
  ∑ m ∈ {m ∈ ramareCofactorSet (Icc 1 M) p | ¬ p ∣ m},
    (((μ m : ℤ) : ℝ) / (((primeFactorsIn P m).card : ℝ) + 1)) *
      bdGenReal (1 / (m : ℝ)) u

/-- A finite p-free cofactor packet has no subunit physical contribution. -/
theorem cofactor_eq_zero_of_mem_Ioo_one (P : Finset ℕ) (M p : ℕ) (hp : 0 < p)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    cofactor P M p u = 0 := by
  classical
  unfold cofactor
  refine Finset.sum_eq_zero fun m hm => ?_
  have hmcof : m ∈ ramareCofactorSet (Icc 1 M) p := (Finset.mem_filter.mp hm).1
  rw [ramareCofactorSet, Finset.mem_image] at hmcof
  obtain ⟨n, hn, hnm⟩ := hmcof
  have hndvd : p ∣ n := (Finset.mem_filter.mp hn).2
  have hnpos : 0 < n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  have hmpos : 0 < m := by
    rw [← hnm]
    exact Nat.div_pos (Nat.le_of_dvd hnpos hndvd) hp
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have htheta0 : 0 ≤ 1 / (m : ℝ) := by positivity
  have htheta1 : 1 / (m : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hmR
  rw [bdGenReal_eq_zero_of_mem_Ioo_one htheta0 htheta1 hu, mul_zero]

/-- The forced affine correction coefficient of a physical Ramaré p-packet. -/
def harmonic (P : Finset ℕ) (M p : ℕ) : ℝ :=
  ∑ m ∈ {m ∈ ramareCofactorSet (Icc 1 M) p | ¬ p ∣ m},
    ((μ m : ℤ) : ℝ) /
      ((m : ℝ) * (((primeFactorsIn P m).card : ℝ) + 1))

/-- The exact physical p-packet: reciprocal dilation plus its affine correction. -/
def packet (P : Finset ℕ) (M p : ℕ) (u : ℝ) : ℝ :=
  dilate p (cofactor P M p) u + harmonic P M p * bdGenReal (1 / (p : ℝ)) u

/-- Every complete physical Ramaré packet vanishes below the unit boundary.
Both the reciprocal-dilated cofactor and its forced affine correction are
retained in this support statement. -/
theorem packet_eq_zero_of_mem_Ioo_one (P : Finset ℕ) (M p : ℕ) (hp : 0 < p)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    packet P M p u = 0 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpR1 : (1 : ℝ) ≤ p := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp.ne'
  have huDiv : u / (p : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos hu.1 hpR
    · apply (div_lt_one₀ hpR).2
      nlinarith [hu.2, hpR1]
  have htheta0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have htheta1 : 1 / (p : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hpR1
  unfold packet dilate
  rw [cofactor_eq_zero_of_mem_Ioo_one P M p hp huDiv, mul_zero, zero_add,
    bdGenReal_eq_zero_of_mem_Ioo_one htheta0 htheta1 hu, mul_zero]

/-- The p-incidence portion of the physical source, with its exact Ramaré weight. -/
def inner (P : Finset ℕ) (M p : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ {n ∈ Icc 1 M | p ∣ n},
    (((μ n : ℤ) : ℝ) * bdGenReal (1 / (n : ℝ)) u) /
      ((primeFactorsIn P n).card : ℝ)

/-- Ramaré's exact incidence identity applies directly to the literal physical source.
No norm inequality or spectral surrogate has been introduced. -/
theorem source_eq_ramare_add_rough (P : Finset ℕ) (M : ℕ) (u : ℝ) :
    source M u =
      (∑ p ∈ P, ∑ n ∈ {n ∈ Icc 1 M | p ∣ n},
        (((μ n : ℤ) : ℝ) * bdGenReal (1 / (n : ℝ)) u) /
          ((primeFactorsIn P n).card : ℝ)) + rough P M u := by
  exact sum_eq_ramare_add_rough P (Icc 1 M)
    (fun n => ((μ n : ℤ) : ℝ) * bdGenReal (1 / (n : ℝ)) u)

private theorem moebius_real_mul_eq_neg_of_prime_not_dvd {p m : ℕ}
    (hp : p.Prime) (hpm : ¬ p ∣ m) :
    ((μ (p * m) : ℤ) : ℝ) = -((μ m : ℤ) : ℝ) := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

private theorem moebius_real_mul_eq_zero_of_prime_dvd {p m : ℕ}
    (hp : p.Prime) (hpm : p ∣ m) :
    ((μ (p * m) : ℤ) : ℝ) = 0 := by
  have hpp : p * p ∣ p * m := Nat.mul_dvd_mul_left p hpm
  have hnonsq : ¬ Squarefree (p * m) := by
    intro hsq
    have hppsq : Squarefree (p * p) := hsq.squarefree_of_dvd hpp
    have hcop := Nat.coprime_of_squarefree_mul hppsq
    exact hp.ne_one (by simpa [Nat.coprime_self] using hcop)
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnonsq]
  norm_num

/-- A designated prime incidence is exactly the negative physical packet.
The square-multiple diagonal vanishes by Möbius, while every p-free cofactor
retains both pieces of the reciprocal-generator dilation law. -/
theorem inner_eq_neg_packet {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    (M : ℕ) {p : ℕ} (hpP : p ∈ P) (u : ℝ) :
    inner P M p u = -packet P M p u := by
  classical
  have hp : p.Prime := hPprime p hpP
  have hreindex : inner P M p u =
      ∑ m ∈ ramareCofactorSet (Icc 1 M) p,
        (((μ (p * m) : ℤ) : ℝ) * bdGenReal (1 / ((p * m : ℕ) : ℝ)) u) /
          ((primeFactorsIn P (p * m)).card : ℝ) := by
    unfold inner
    exact (sum_div_image p {n ∈ Icc 1 M | p ∣ n}
      (fun n hn => (Finset.mem_filter.mp hn).2)
      (fun n => (((μ n : ℤ) : ℝ) * bdGenReal (1 / (n : ℝ)) u) /
        ((primeFactorsIn P n).card : ℝ))).symm
  rw [hreindex]
  have hsplit :
      (∑ m ∈ ramareCofactorSet (Icc 1 M) p,
        (((μ (p * m) : ℤ) : ℝ) * bdGenReal (1 / ((p * m : ℕ) : ℝ)) u) /
          ((primeFactorsIn P (p * m)).card : ℝ)) =
        (∑ m ∈ {m ∈ ramareCofactorSet (Icc 1 M) p | ¬ p ∣ m},
          (((μ (p * m) : ℤ) : ℝ) * bdGenReal (1 / ((p * m : ℕ) : ℝ)) u) /
            ((primeFactorsIn P (p * m)).card : ℝ)) +
        ∑ m ∈ {m ∈ ramareCofactorSet (Icc 1 M) p | p ∣ m},
          (((μ (p * m) : ℤ) : ℝ) * bdGenReal (1 / ((p * m : ℕ) : ℝ)) u) /
            ((primeFactorsIn P (p * m)).card : ℝ) := by
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not
      (ramareCofactorSet (Icc 1 M) p) (fun m => p ∣ m) _).symm
  rw [hsplit]
  have hdiag : (∑ m ∈ {m ∈ ramareCofactorSet (Icc 1 M) p | p ∣ m},
      (((μ (p * m) : ℤ) : ℝ) * bdGenReal (1 / ((p * m : ℕ) : ℝ)) u) /
        ((primeFactorsIn P (p * m)).card : ℝ)) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [moebius_real_mul_eq_zero_of_prime_dvd hp (Finset.mem_filter.mp hm).2, zero_mul,
      zero_div]
  rw [hdiag, add_zero]
  unfold packet dilate cofactor harmonic
  rw [Finset.mul_sum]
  have hterm : ∀ m ∈ {m ∈ ramareCofactorSet (Icc 1 M) p | ¬ p ∣ m},
      (((μ (p * m) : ℤ) : ℝ) * bdGenReal (1 / ((p * m : ℕ) : ℝ)) u) /
          ((primeFactorsIn P (p * m)).card : ℝ) =
        -((1 / (p : ℝ)) *
            ((((μ m : ℤ) : ℝ) / (((primeFactorsIn P m).card : ℝ) + 1)) *
              bdGenReal (1 / (m : ℝ)) (u / (p : ℝ))) +
          (((μ m : ℤ) : ℝ) /
            ((m : ℝ) * (((primeFactorsIn P m).card : ℝ) + 1))) *
              bdGenReal (1 / (p : ℝ)) u) := by
    intro m hm
    have hpm : ¬ p ∣ m := (Finset.mem_filter.mp hm).2
    have hmpos : 0 < m := by
      have hmcof : m ∈ ramareCofactorSet (Icc 1 M) p := (Finset.mem_filter.mp hm).1
      rw [ramareCofactorSet, Finset.mem_image] at hmcof
      obtain ⟨n, hn, hnm⟩ := hmcof
      have hndvd : p ∣ n := (Finset.mem_filter.mp hn).2
      have hnpos : 0 < n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
      rw [← hnm]
      exact Nat.div_pos (Nat.le_of_dvd hnpos hndvd) hp.pos
    rw [moebius_real_mul_eq_neg_of_prime_not_dvd hp hpm,
      card_primeFactorsIn_mul_prime hPprime hp hpP hpm,
      bdGenReal_inv_mul_decompose hp.pos hmpos u]
    push_cast
    rw [dilate]
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hωR : (0 : ℝ) < ((primeFactorsIn P m).card : ℝ) + 1 := by positivity
    have hprod : (m : ℝ) + (m : ℝ) * ((primeFactorsIn P m).card : ℝ) ≠ 0 := by
      exact ne_of_gt (by positivity)
    field_simp [hpR.ne', hmR.ne', hωR.ne', hprod]
  rw [show
    (∑ m ∈ {m ∈ ramareCofactorSet (Icc 1 M) p | ¬ p ∣ m},
      (((μ (p * m) : ℤ) : ℝ) * bdGenReal (1 / ((p * m : ℕ) : ℝ)) u) /
        ((primeFactorsIn P (p * m)).card : ℝ)) =
      ∑ m ∈ {m ∈ ramareCofactorSet (Icc 1 M) p | ¬ p ∣ m},
        -((1 / (p : ℝ)) *
            ((((μ m : ℤ) : ℝ) / (((primeFactorsIn P m).card : ℝ) + 1)) *
              bdGenReal (1 / (m : ℝ)) (u / (p : ℝ))) +
          (((μ m : ℤ) : ℝ) /
            ((m : ℝ) * (((primeFactorsIn P m).card : ℝ) + 1))) *
              bdGenReal (1 / (p : ℝ)) u) from
      Finset.sum_congr rfl hterm]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_mul]

/-- The complete finite Möbius source is the rough remainder minus the exact
physical Ramaré packets.  This is the source identity whose signed physical
energy must be controlled to advance Euler deletion. -/
theorem source_eq_rough_sub_sum_packet {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) (u : ℝ) :
    source M u = rough P M u - ∑ p ∈ P, packet P M p u := by
  rw [source_eq_ramare_add_rough]
  change (∑ p ∈ P, inner P M p u) + rough P M u =
    rough P M u - ∑ p ∈ P, packet P M p u
  have hpackets : (∑ p ∈ P, inner P M p u) =
      -(∑ p ∈ P, packet P M p u) := by
    rw [Finset.sum_congr rfl (fun p hp => inner_eq_neg_packet hPprime M hp u),
      Finset.sum_neg_distrib]
  rw [hpackets]
  ring

end RHTower.DeletionRamarePhysical
