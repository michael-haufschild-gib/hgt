import GaloisForLFunctions.RHTower.EulerDeletionCenteredLcmIncidence
import GaloisForLFunctions.RHTower.Sieve.TotientMoebiusNormalisation

/-!
# Divisor-closed conservation of physical centered lcm fibres

The signed complete fibres over every divisor lattice reassemble into the square
of a literal coprime-window discrepancy. This holds at the physical starting
coordinate and every finite window length, without period averaging.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction

namespace RHTower

/-- All complete lcm fibres in one divisor lattice reassemble into the square
of the Möbius-weighted physical window discrepancy. -/
theorem physicalCenteredLcmFibre_divisorSum_eq_square
    (n t H : ℕ) (hn : 0 < n) :
    (∑ q ∈ n.divisors, physicalCenteredLcmFibre q t H t H) =
      (∑ d ∈ n.divisors,
        ((moebius d : ℤ) : ℝ) *
          DeletionResidueMartingale.divisorWindowDiscrepancy d t H) ^ (2 : ℕ) := by
  let a : ℕ → ℝ := fun d => ((moebius d : ℤ) : ℝ) *
    DeletionResidueMartingale.divisorWindowDiscrepancy d t H
  have hcarrier :
      (n.divisors ×ˢ n.divisors).image (fun de => Nat.lcm de.1 de.2) = n.divisors := by
    ext q
    constructor
    · intro h
      obtain ⟨de, hde, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hd, he⟩ := Finset.mem_product.mp hde
      exact Nat.mem_divisors.mpr ⟨Nat.lcm_dvd
        (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors he), hn.ne'⟩
    · intro hq
      exact Finset.mem_image.mpr ⟨(q, q), Finset.mem_product.mpr ⟨hq, hq⟩,
        by simp⟩
  have hfibre (q : ℕ) (hq : q ∈ n.divisors) :
      physicalCenteredLcmFibre q t H t H =
        finiteLcmPairCrossFibre n.divisors a a q := by
    have hqpos : 0 < q := Nat.pos_of_mem_divisors hq
    have hsets :
        ((q.divisors ×ˢ q.divisors).filter (fun de => Nat.lcm de.1 de.2 = q)) =
        ((n.divisors ×ˢ n.divisors).filter (fun de => Nat.lcm de.1 de.2 = q)) := by
      ext de
      constructor
      · intro hde
        obtain ⟨hprod, hlcm⟩ := Finset.mem_filter.mp hde
        obtain ⟨hd, he⟩ := Finset.mem_product.mp hprod
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨
          Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans
            (Nat.dvd_of_mem_divisors hq), hn.ne'⟩,
          Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors he).trans
            (Nat.dvd_of_mem_divisors hq), hn.ne'⟩⟩, hlcm⟩
      · intro hde
        obtain ⟨_, hlcm⟩ := Finset.mem_filter.mp hde
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨
          Nat.mem_divisors.mpr ⟨by simpa [hlcm] using Nat.dvd_lcm_left de.1 de.2,
            hqpos.ne'⟩,
          Nat.mem_divisors.mpr ⟨by simpa [hlcm] using Nat.dvd_lcm_right de.1 de.2,
            hqpos.ne'⟩⟩, hlcm⟩
    unfold physicalCenteredLcmFibre finiteLcmPairCrossFibre
    rw [hsets]
    apply Finset.sum_congr rfl
    intro de _
    dsimp [a]
    ring
  calc
    (∑ q ∈ n.divisors, physicalCenteredLcmFibre q t H t H) =
        ∑ q ∈ n.divisors, finiteLcmPairCrossFibre n.divisors a a q := by
          exact Finset.sum_congr rfl hfibre
    _ = (∑ d ∈ n.divisors, a d) ^ (2 : ℕ) := by
      have h := finite_sum_mul_eq_lcmPairCrossFibres n.divisors a a
      rw [hcarrier] at h
      simpa only [pow_two] using h.symm
    _ = _ := rfl

/-- The exact physical cancellation law: a complete divisor lattice of signed
lcm grades is one coprime-window discrepancy square, at every finite window. -/
theorem physicalCenteredLcmFibre_divisorSum_eq_coprimeDiscrepancy_sq
    (n t H : ℕ) (hn : 0 < n) :
    (∑ q ∈ n.divisors, physicalCenteredLcmFibre q t H t H) =
      ((H : ℝ) * ((Nat.totient n : ℝ) / (n : ℝ)) -
        ((Ioc t (t + H)).filter (n.Coprime ·)).card) ^ (2 : ℕ) := by
  rw [physicalCenteredLcmFibre_divisorSum_eq_square n t H hn]
  congr 1
  have hnIcc : n ∈ Icc 1 n := Finset.mem_Icc.mpr ⟨hn, le_refl n⟩
  have hdivisors : (Icc 1 n).filter (fun d => d ∣ n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, _⟩, hd⟩
      exact ⟨hd, hn.ne'⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn, Nat.le_of_dvd hn hd⟩, hd⟩
  have hβ := weighted_moebius_divisor_prefixDiscrepancy_filter_eq_coprime
    n n t H 1 1 hnIcc
  rw [hdivisors] at hβ
  simp only [Finset.sum_range_one, pow_zero, one_mul, zero_add, zero_mul] at hβ
  simpa [DeletionResidueMartingale.divisorWindowDiscrepancy,
    Sieve.sum_moebius_div_divisors_eq_totient_div hn] using hβ

/-- Every divisor-closed physical fibre sum is nonnegative, despite individual
composite grades having either sign. -/
theorem physicalCenteredLcmFibre_divisorSum_nonneg
    (n t H : ℕ) (hn : 0 < n) :
    0 ≤ ∑ q ∈ n.divisors, physicalCenteredLcmFibre q t H t H := by
  rw [physicalCenteredLcmFibre_divisorSum_eq_coprimeDiscrepancy_sq n t H hn]
  positivity

end RHTower
