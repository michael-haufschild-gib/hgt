import GaloisForLFunctions.RHTower.Sieve.VinogradovBertrandReservoir
import Mathlib.Data.Nat.Dist

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- Directed Vandermonde product.  Each unordered difference appears twice;
the directed form makes the finite indexing canonical. -/
def vinogradovDifferenceProduct {N k : ℕ} (m : Fin k → Fin N) : ℕ :=
  ∏ ij ∈ Finset.offDiag Finset.univ,
    Nat.dist (m ij.1).val (m ij.2).val

theorem vinogradovDifferenceProduct_ne_zero
    {N k : ℕ} {m : Fin k → Fin N} (hm : Function.Injective m) :
    vinogradovDifferenceProduct m ≠ 0 := by
  rw [vinogradovDifferenceProduct, Finset.prod_ne_zero_iff]
  intro ij hij
  have hij' := Finset.mem_offDiag.mp hij
  exact (Nat.dist_pos_of_ne fun h => hij'.2.2 (hm (Fin.ext h))).ne'

theorem vinogradovDifferenceProduct_le
    {N k : ℕ} (m : Fin k → Fin N) :
    vinogradovDifferenceProduct m ≤ N ^ (k * k - k) := by
  unfold vinogradovDifferenceProduct
  calc
    (∏ ij ∈ Finset.offDiag Finset.univ,
        Nat.dist (m ij.1).val (m ij.2).val) ≤
        ∏ _ij ∈ Finset.offDiag Finset.univ, N := by
          apply Finset.prod_le_prod
          · intro _ _
            exact Nat.zero_le _
          · intro ij _
            unfold Nat.dist
            have hi := (m ij.1).isLt
            have hj := (m ij.2).isLt
            omega
    _ = N ^ (k * k - k) := by
      rw [Finset.prod_const, Finset.offDiag_card]
      simp

theorem dvd_vinogradovDifferenceProduct_of_cast_eq
    {N k p : ℕ} (m : Fin k → Fin N) {i j : Fin k} (hij : i ≠ j)
    (hcast : ((m i).val : ZMod p) = ((m j).val : ZMod p)) :
    p ∣ vinogradovDifferenceProduct m := by
  have hmod : (m i).val ≡ (m j).val [MOD p] := by
    exact (ZMod.natCast_eq_natCast_iff' (m i).val (m j).val p).mp hcast
  have hdist : p ∣ Nat.dist (m i).val (m j).val := by
    by_cases hle : (m i).val ≤ (m j).val
    · rw [Nat.dist_eq_sub_of_le hle]
      exact (Nat.modEq_iff_dvd' hle).mp hmod
    · have hle' : (m j).val ≤ (m i).val := by omega
      rw [Nat.dist_eq_sub_of_le_right hle']
      exact (Nat.modEq_iff_dvd' hle').mp hmod.symm
  apply hdist.trans
  have hmem : (i, j) ∈ Finset.offDiag (Finset.univ : Finset (Fin k)) :=
    Finset.mem_offDiag.mpr ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩
  exact Finset.dvd_prod_of_mem
    (fun ij : Fin k × Fin k => Nat.dist (m ij.1).val (m ij.2).val) hmem

/-- An injective tuple is separated modulo at least one prime in the fixed
Bertrand reservoir used by every tuple at this scale. -/
theorem exists_vinogradovAvoidingReservoirIndex
    {N k : ℕ} (hk : k ≠ 0) (hN : N ≠ 0)
    (m : Fin k → Fin N) (hm : Function.Injective m) :
    ∃ i : Fin (k * (k * k - k) + 1),
      Function.Injective (fun j =>
        ((m j).val : ZMod (vinogradovBertrandPrimeReservoir
          (vinogradovCeilRoot k N + k)
          (k * (k * k - k) + 1) i))) := by
  let y := vinogradovCeilRoot k N
  let d := k * k - k
  let M := k * d
  let A := vinogradovDifferenceProduct m
  have hy : 0 < y := vinogradovCeilRoot_pos hk hN
  have hA : A ≠ 0 := vinogradovDifferenceProduct_ne_zero hm
  have hA_N : A ≤ N ^ d := vinogradovDifferenceProduct_le m
  have hN_y : N ≤ y ^ k := le_vinogradovCeilRoot_pow hk
  have hA_y : A ≤ y ^ M := by
    calc
      A ≤ N ^ d := hA_N
      _ ≤ (y ^ k) ^ d := Nat.pow_le_pow_left hN_y d
      _ = y ^ M := by simp [M, d, pow_mul]
  have hA_start : A ≤ (y + k) ^ M :=
    hA_y.trans (Nat.pow_le_pow_left (Nat.le_add_right y k) M)
  obtain ⟨i, hi⟩ := exists_vinogradovBertrandPrimeReservoir_not_dvd
    (y := y + k) (M := M) (A := A) (by omega) hA hA_start
  refine ⟨i, ?_⟩
  intro a b hab
  by_contra hne
  exact hi (dvd_vinogradovDifferenceProduct_of_cast_eq m hne hab)

theorem vinogradovAvoidingReservoirPrime_gt_k
    {N k : ℕ} (i : Fin (k * (k * k - k) + 1)) :
    k < vinogradovBertrandPrimeReservoir
      (vinogradovCeilRoot k N + k) (k * (k * k - k) + 1) i := by
  have h := lt_vinogradovBertrandPrimeReservoir
    (vinogradovCeilRoot k N + k) (k * (k * k - k) + 1) i
  omega

theorem vinogradovAvoidingReservoirPrime_pow_gt
    {N k : ℕ} (hk : k ≠ 0)
    (i : Fin (k * (k * k - k) + 1)) :
    N < (vinogradovBertrandPrimeReservoir
      (vinogradovCeilRoot k N + k)
      (k * (k * k - k) + 1) i) ^ k := by
  have hcover := le_vinogradovCeilRoot_pow (k := k) (N := N) hk
  have hpgt := lt_vinogradovBertrandPrimeReservoir
    (vinogradovCeilRoot k N + k) (k * (k * k - k) + 1) i
  exact hcover.trans_lt (Nat.pow_lt_pow_left (by omega) hk)

/-- A prime selected from the Bertrand reservoir that avoids every
pairwise difference of an injective tuple. -/
theorem exists_vinogradovAvoidingPrime
    {N k : ℕ} (hk : k ≠ 0) (hN : N ≠ 0)
    (m : Fin k → Fin N) (hm : Function.Injective m) :
    ∃ p : ℕ,
      p.Prime ∧ k < p ∧ N < p ^ k ∧
      Function.Injective (fun i => ((m i).val : ZMod p)) ∧
      p + 2 ≤
        2 ^ (k * (k * k - k) + 1) * (vinogradovCeilRoot k N + k + 2) := by
  let y := vinogradovCeilRoot k N
  let d := k * k - k
  let M := k * d
  let A := vinogradovDifferenceProduct m
  have hy : 0 < y := vinogradovCeilRoot_pos hk hN
  have hA : A ≠ 0 := vinogradovDifferenceProduct_ne_zero hm
  have hA_N : A ≤ N ^ d := vinogradovDifferenceProduct_le m
  have hN_y : N ≤ y ^ k := le_vinogradovCeilRoot_pow hk
  have hA_y : A ≤ y ^ M := by
    calc
      A ≤ N ^ d := hA_N
      _ ≤ (y ^ k) ^ d := Nat.pow_le_pow_left hN_y d
      _ = y ^ M := by simp [M, d, pow_mul]
  have hA_start : A ≤ (y + k) ^ M :=
    hA_y.trans (Nat.pow_le_pow_left (Nat.le_add_right y k) M)
  obtain ⟨i, hi⟩ := exists_vinogradovBertrandPrimeReservoir_not_dvd
    (y := y + k) (M := M) (A := A) (by omega) hA hA_start
  let p := vinogradovBertrandPrimeReservoir (y + k) (M + 1) i
  have hp : p.Prime := vinogradovBertrandPrimeReservoir_prime (y + k) (M + 1) i
  have hpgt : y + k < p :=
    lt_vinogradovBertrandPrimeReservoir (y + k) (M + 1) i
  have hpk : k < p := by omega
  have hNp : N < p ^ k := by
    exact hN_y.trans_lt (Nat.pow_lt_pow_left (by omega) hk)
  have hinj : Function.Injective (fun j => ((m j).val : ZMod p)) := by
    intro a b hab
    by_contra hne
    exact hi (dvd_vinogradovDifferenceProduct_of_cast_eq m hne hab)
  exact ⟨p, hp, hpk, hNp, hinj, by
    simpa [p, M, d, y, add_assoc] using
      vinogradovBertrandPrimeReservoir_add_two_le (y + k) (M + 1) i⟩

end

end RHTower.Sieve
