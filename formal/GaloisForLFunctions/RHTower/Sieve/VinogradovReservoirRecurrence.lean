import GaloisForLFunctions.RHTower.Sieve.VinogradovResidueGoodEnergy
import GaloisForLFunctions.RHTower.Sieve.FiniteFiberCover
import GaloisForLFunctions.RHTower.Sieve.VinogradovAvoidingPrime

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovReservoirSize (k : ℕ) : ℕ :=
  k * (k * k - k) + 1

def vinogradovReservoirPrime (N k : ℕ)
    (i : Fin (vinogradovReservoirSize k)) : ℕ :=
  vinogradovBertrandPrimeReservoir
    (vinogradovCeilRoot k N + k) (vinogradovReservoirSize k) i

def vinogradovReservoirBound (N k : ℕ) : ℕ :=
  2 ^ (vinogradovReservoirSize k) *
    (vinogradovCeilRoot k N + k + 2)

def vinogradovPrimeMomentModulus (N k b : ℕ) : ℕ :=
  vinogradovBertrandNext
    (max (2 * (k + b) * N ^ k) (vinogradovReservoirBound N k))

theorem vinogradovPrimeMomentModulus_prime (N k b : ℕ) :
    (vinogradovPrimeMomentModulus N k b).Prime := by
  exact vinogradovBertrandNext_prime _

instance vinogradovPrimeMomentModulusNeZero (N k b : ℕ) :
    NeZero (vinogradovPrimeMomentModulus N k b) :=
  ⟨(vinogradovPrimeMomentModulus_prime N k b).ne_zero⟩

theorem vinogradovPrimeMomentModulus_large (N k b : ℕ) :
    2 * (k + b) * N ^ k < vinogradovPrimeMomentModulus N k b := by
  exact (le_max_left _ _).trans_lt (lt_vinogradovBertrandNext _)

theorem vinogradovReservoirPrime_prime
    {N k : ℕ} (i : Fin (vinogradovReservoirSize k)) :
    (vinogradovReservoirPrime N k i).Prime := by
  exact vinogradovBertrandPrimeReservoir_prime _ _ i

theorem vinogradovReservoirPrime_gt_k
    {N k : ℕ} (i : Fin (vinogradovReservoirSize k)) :
    k < vinogradovReservoirPrime N k i := by
  exact vinogradovAvoidingReservoirPrime_gt_k i

theorem vinogradovReservoirPrime_pow_gt
    {N k : ℕ} (hk : k ≠ 0) (i : Fin (vinogradovReservoirSize k)) :
    N < (vinogradovReservoirPrime N k i) ^ k := by
  exact vinogradovAvoidingReservoirPrime_pow_gt hk i

theorem vinogradovReservoirPrime_lt_momentModulus
    {N k b : ℕ} (i : Fin (vinogradovReservoirSize k)) :
    vinogradovReservoirPrime N k i < vinogradovPrimeMomentModulus N k b := by
  have hpbound := vinogradovBertrandPrimeReservoir_add_two_le
    (vinogradovCeilRoot k N + k) (vinogradovReservoirSize k) i
  have hpbound' : vinogradovReservoirPrime N k i + 2 ≤
      vinogradovReservoirBound N k := by
    simpa [vinogradovReservoirPrime, vinogradovReservoirBound] using hpbound
  have hq : vinogradovReservoirBound N k <
      vinogradovPrimeMomentModulus N k b := (le_max_right (2 * (k + b) * N ^ k)
    (vinogradovReservoirBound N k)).trans_lt
      (lt_vinogradovBertrandNext
        (max (2 * (k + b) * N ^ k) (vinogradovReservoirBound N k)))
  exact (show vinogradovReservoirPrime N k i <
    vinogradovReservoirBound N k by omega).trans hq

theorem vinogradovReservoirPrime_unit
    {N k b : ℕ} (i : Fin (vinogradovReservoirSize k)) :
    IsUnit ((vinogradovReservoirPrime N k i : ℕ) :
      ZMod (vinogradovPrimeMomentModulus N k b)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (Nat.coprime_primes
    (vinogradovReservoirPrime_prime i)
    (vinogradovPrimeMomentModulus_prime N k b)).2
      (by exact ne_of_lt (vinogradovReservoirPrime_lt_momentModulus i))

theorem ceilDiv_ne_zero_of_ne_zero
    {N p : ℕ} (hN : N ≠ 0) (hp : 0 < p) : N ⌈/⌉ p ≠ 0 := by
  intro h
  have hcover := le_smul_ceilDiv (α := ℕ) (β := ℕ) (b := N) hp
  rw [h] at hcover
  simp at hcover
  exact hN hcover

theorem ceilDiv_le_self_of_pos {N p : ℕ} (hp : 0 < p) :
    N ⌈/⌉ p ≤ N := by
  rw [ceilDiv_le_iff_le_mul hp]
  have hp1 : 1 ≤ p := hp
  calc
    N = 1 * N := by simp
    _ ≤ p * N := Nat.mul_le_mul_right N hp1

theorem vinogradovPrimeMomentModulus_large_tail
    {N k b p : ℕ} (hp : 0 < p) :
    2 * b * (N ⌈/⌉ p) ^ k < vinogradovPrimeMomentModulus N k b := by
  calc
    2 * b * (N ⌈/⌉ p) ^ k ≤ 2 * (k + b) * N ^ k := by
      exact Nat.mul_le_mul (by omega)
        (Nat.pow_le_pow_left (ceilDiv_le_self_of_pos hp) k)
    _ < vinogradovPrimeMomentModulus N k b :=
      vinogradovPrimeMomentModulus_large N k b

theorem vinogradov_injective_energy_le_reservoir_cover
    {q N k b : ℕ} [NeZero q] (hk : k ≠ 0) (hN : N ≠ 0) :
    finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
        (fun z => Function.Injective z.1) ≤
      vinogradovReservoirSize k *
        ∑ i : Fin (vinogradovReservoirSize k),
          finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
            (fun z => Function.Injective z.1 ∧
              Function.Injective (fun j =>
                ((z.1 j).val : ZMod (vinogradovReservoirPrime N k i)))) := by
  classical
  have hcover : ∀ z : (Fin k → Fin N) × (Fin b → Fin N),
      Function.Injective z.1 →
        ∃ i : Fin (vinogradovReservoirSize k),
          Function.Injective (fun j =>
            ((z.1 j).val : ZMod (vinogradovReservoirPrime N k i))) := by
    intro z hz
    obtain ⟨i, hi⟩ := exists_vinogradovAvoidingReservoirIndex hk hN z.1 hz
    exact ⟨i, hi⟩
  simpa only [Fintype.card_fin] using
    (finiteFiberEnergyWith_le_cover
      (ι := Fin (vinogradovReservoirSize k))
      (vinogradovSplitPowerSignature q N k b)
      (fun z => Function.Injective z.1)
      (fun i z => Function.Injective (fun j =>
        ((z.1 j).val : ZMod (vinogradovReservoirPrime N k i)))) hcover)

theorem vinogradov_injective_energy_reservoir_bound
    {N k b : ℕ} (hk : k ≠ 0) (hb : b ≠ 0) (hN : N ≠ 0) :
    finiteFiberEnergyWith
        (vinogradovSplitPowerSignature
          (vinogradovPrimeMomentModulus N k b) N k b)
        (fun z => Function.Injective z.1) ≤
      vinogradovReservoirSize k *
        ∑ i : Fin (vinogradovReservoirSize k),
          (vinogradovReservoirPrime N k i) ^ (2 * b) *
            (N ^ k * (k.factorial *
              (vinogradovReservoirPrime N k i) ^ (k * (k - 1) / 2) *
              Fintype.card (VinogradovDiagonalSolution
                (N ⌈/⌉ (vinogradovReservoirPrime N k i)) b k))) := by
  calc
    _ ≤ vinogradovReservoirSize k *
        ∑ i : Fin (vinogradovReservoirSize k),
          finiteFiberEnergyWith
            (vinogradovSplitPowerSignature
              (vinogradovPrimeMomentModulus N k b) N k b)
            (fun z => Function.Injective z.1 ∧
              Function.Injective (fun j =>
                ((z.1 j).val : ZMod (vinogradovReservoirPrime N k i)))) :=
      vinogradov_injective_energy_le_reservoir_cover hk hN
    _ ≤ vinogradovReservoirSize k *
        ∑ i : Fin (vinogradovReservoirSize k),
          (vinogradovReservoirPrime N k i) ^ (2 * b) *
            (N ^ k * (k.factorial *
              (vinogradovReservoirPrime N k i) ^ (k * (k - 1) / 2) *
              Fintype.card (VinogradovDiagonalSolution
                (N ⌈/⌉ (vinogradovReservoirPrime N k i)) b k))) := by
      gcongr
      letI : NeZero (vinogradovReservoirPrime N k i) :=
        ⟨(vinogradovReservoirPrime_prime i).ne_zero⟩
      exact finiteFiberEnergyWith_separated_le hb
        (vinogradovReservoirPrime_prime i)
        (vinogradovReservoirPrime_gt_k i)
        (vinogradovReservoirPrime_pow_gt hk i)
        hN
        (vinogradovPrimeMomentModulus_large N k b)
        (vinogradovReservoirPrime_unit i)
        (ceilDiv_ne_zero_of_ne_zero hN (vinogradovReservoirPrime_prime i).pos)
        (vinogradovPrimeMomentModulus_large_tail
          (vinogradovReservoirPrime_prime i).pos)

/-- PNT-free Linnik recurrence: a fixed Bertrand reservoir covers every
injective leading block, while colliding blocks lose two powers of `N`. -/
theorem vinogradov_moment_bertrand_recurrence
    {N k b : ℕ} (hk : k ≠ 0) (hb : b ≠ 0) (hN : N ≠ 0) :
    Fintype.card (VinogradovDiagonalSolution N (k + b) k) ≤
      2 * (vinogradovReservoirSize k *
          ∑ i : Fin (vinogradovReservoirSize k),
            (vinogradovReservoirPrime N k i) ^ (2 * b) *
              (N ^ k * (k.factorial *
                (vinogradovReservoirPrime N k i) ^ (k * (k - 1) / 2) *
                Fintype.card (VinogradovDiagonalSolution
                  (N ⌈/⌉ (vinogradovReservoirPrime N k i)) b k))) +
        ((k * k - k) * N ^ (k - 1)) ^ 2 *
          Fintype.card (VinogradovDiagonalSolution N b k)) := by
  let q := vinogradovPrimeMomentModulus N k b
  calc
    Fintype.card (VinogradovDiagonalSolution N (k + b) k) =
        finiteFiberEnergy
          (vinogradovPowerSignatureMod q k :
            (Fin (k + b) → Fin N) → Fin k → ZMod q) := by
      symm
      exact vinogradovModularMomentAt_eq_card_of_large hN
        (vinogradovPrimeMomentModulus_large N k b)
    _ ≤ 2 * (finiteFiberEnergyWith
          (vinogradovSplitPowerSignature q N k b)
          (fun z => Function.Injective z.1) +
        Fintype.card (VinogradovCollidingBlockCompletion q N k b)) :=
      vinogradov_moment_collision_partition
    _ ≤ 2 * (vinogradovReservoirSize k *
          ∑ i : Fin (vinogradovReservoirSize k),
            (vinogradovReservoirPrime N k i) ^ (2 * b) *
              (N ^ k * (k.factorial *
                (vinogradovReservoirPrime N k i) ^ (k * (k - 1) / 2) *
                Fintype.card (VinogradovDiagonalSolution
                  (N ⌈/⌉ (vinogradovReservoirPrime N k i)) b k))) +
        ((k * k - k) * N ^ (k - 1)) ^ 2 *
          Fintype.card (VinogradovDiagonalSolution N b k)) := by
      have hgood : finiteFiberEnergyWith
          (vinogradovSplitPowerSignature q N k b)
          (fun z => Function.Injective z.1) ≤
          vinogradovReservoirSize k *
            ∑ i : Fin (vinogradovReservoirSize k),
              (vinogradovReservoirPrime N k i) ^ (2 * b) *
                (N ^ k * (k.factorial *
                  (vinogradovReservoirPrime N k i) ^ (k * (k - 1) / 2) *
                  Fintype.card (VinogradovDiagonalSolution
                    (N ⌈/⌉ (vinogradovReservoirPrime N k i)) b k))) := by
        simpa [q] using vinogradov_injective_energy_reservoir_bound hk hb hN
      have hqtail : 2 * b * N ^ k < q := by
        calc
          2 * b * N ^ k ≤ 2 * (k + b) * N ^ k :=
            Nat.mul_le_mul_right (N ^ k) (by omega)
          _ < q := by simpa [q] using vinogradovPrimeMomentModulus_large N k b
      have hbad := card_vinogradovCollidingBlockCompletion_le_moment
        (q := q) (k := k) (b := b) hN hqtail
      exact Nat.mul_le_mul_left 2 (Nat.add_le_add hgood hbad)

end

end RHTower.Sieve
