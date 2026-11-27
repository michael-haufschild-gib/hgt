import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.StatementT

/-! A tuple of polynomials with no common proper divisor degree cannot arise
from more than one positive-rank isobaric block, or from a repeated block. -/

noncomputable section

open Polynomial

namespace WindowedLandauTheory.CyclotomicNorms

/-- The absence of a common divisor degree forces a positive-rank
factorization with prescribed block degrees to consist of just one factor. -/
theorem card_eq_one_of_common_divisor_degrees {K P J : Type*} [Field K] [Fintype J]
    {N : ℕ} (hn : 0 < N) (f : P → K[X]) (F : P → J → K[X]) (a d : J → ℕ)
    (ha : ∀ j, 0 < a j) (hd : ∀ j, 0 < d j)
    (hsum : ∑ j, a j * d j = N)
    (hprod : ∀ v, f v = ∏ j, F v j ^ d j) (hdeg : ∀ v j, (F v j).natDegree = a j)
    (havoid : ∀ s : ℕ, 1 ≤ s → 2 * s ≤ N → ∃ v, ¬ ∃ q : K[X], q ∣ f v ∧ q.natDegree = s) :
    Fintype.card J = 1 ∧ ∀ j, d j = 1 ∧ a j = N := by
  classical
  let w (j : J) := a j * d j
  have htotal : ∑ j, w j = N := hsum
  have hlarge (j : J) : N < 2 * a j := by
    by_contra! h
    obtain ⟨v, hv⟩ := havoid (a j) (ha j) h
    apply hv
    refine ⟨F v j, ?_, hdeg v j⟩
    rw [hprod]
    exact (dvd_pow_self _ (hd j).ne').trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
  have halew (j : J) : a j ≤ w j := by
    simpa only [w, mul_one] using Nat.mul_le_mul_left (a j) (show 1 ≤ d j from hd j)
  have hsingle (j : J) : d j = 1 := by
    have hw : w j ≤ N := htotal ▸ Finset.single_le_sum (f := w) (fun k _ => Nat.zero_le (w k))
      (Finset.mem_univ j)
    by_contra hne
    have htwo : 2 ≤ d j := by have := hd j; omega
    have hle := Nat.mul_le_mul_left (a j) htwo
    rw [Nat.mul_comm (a j) 2] at hle
    exact (Nat.not_le_of_gt (hlarge j)) (hle.trans hw)
  have hsub : Subsingleton J := by
    refine ⟨fun i j => ?_⟩
    by_contra hij
    have hm : j ∈ (Finset.univ.erase i) := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
    have hW := Finset.sum_erase_add (s := Finset.univ) w (Finset.mem_univ i)
    rw [htotal] at hW
    have hle := Finset.single_le_sum (f := w) (fun k _ => Nat.zero_le (w k)) hm
    have hi := halew i
    have hj := halew j
    have hli := hlarge i
    have hlj := hlarge j
    omega
  have hne : Nonempty J := by
    by_contra hh
    haveI : IsEmpty J := not_nonempty_iff.mp hh
    exact hn.ne' (by simpa using htotal.symm)
  letI := hsub
  have hc := Fintype.card_le_one_iff_subsingleton.mpr hsub
  refine ⟨le_antisymm hc (Fintype.card_pos_iff.mpr hne), fun j => ⟨hsingle j, ?_⟩⟩
  rwa [Fintype.sum_subsingleton _ j, hsingle j, mul_one] at hsum

end WindowedLandauTheory.CyclotomicNorms
