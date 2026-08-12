import GaloisForLFunctions.RHTower.Sieve.VinogradovReservoirRecurrence

namespace RHTower.Sieve

noncomputable section

def vinogradovReservoirLinearConstant (k : ℕ) : ℕ :=
  2 ^ (vinogradovReservoirSize k) * (k + 3)

def vinogradovReservoirPrimePowerConstant (k : ℕ) : ℕ :=
  2 ^ (vinogradovReservoirSize k * k + k) * (k + 3) ^ k

def vinogradovReservoirSmallThreshold (k : ℕ) : ℕ :=
  (2 * vinogradovReservoirLinearConstant k) ^ k

theorem vinogradovReservoirBound_le_linear_root
    {N k : ℕ} (hk : k ≠ 0) (hN : N ≠ 0) :
    vinogradovReservoirBound N k ≤
      vinogradovReservoirLinearConstant k * vinogradovCeilRoot k N := by
  let y := vinogradovCeilRoot k N
  have hy : 1 ≤ y := vinogradovCeilRoot_pos hk hN
  have hk2 : k + 2 ≤ (k + 2) * y := by
    simpa only [mul_one] using Nat.mul_le_mul_left (k + 2) hy
  have hyk : y + k + 2 ≤ (k + 3) * y := by
    calc
      y + k + 2 = y + (k + 2) := by omega
      _ ≤ y + (k + 2) * y := Nat.add_le_add_left hk2 y
      _ = (k + 3) * y := by ring
  simpa [vinogradovReservoirBound, vinogradovReservoirLinearConstant,
    y, mul_assoc] using
      (Nat.mul_le_mul_left (2 ^ vinogradovReservoirSize k) hyk)

theorem vinogradovReservoirPrime_pow_le_scale
    {N k : ℕ} (hk : k ≠ 0) (hN : N ≠ 0)
    (i : Fin (vinogradovReservoirSize k)) :
    (vinogradovReservoirPrime N k i) ^ k ≤
      vinogradovReservoirPrimePowerConstant k * N := by
  let y := vinogradovCeilRoot k N
  let C := vinogradovReservoirLinearConstant k
  have hpB : vinogradovReservoirPrime N k i ≤ vinogradovReservoirBound N k := by
    have h := vinogradovBertrandPrimeReservoir_add_two_le
      (vinogradovCeilRoot k N + k) (vinogradovReservoirSize k) i
    simpa [vinogradovReservoirPrime, vinogradovReservoirBound] using
      (Nat.le_trans (Nat.le_add_right _ 2) h)
  have hBC : vinogradovReservoirBound N k ≤ C * y :=
    vinogradovReservoirBound_le_linear_root hk hN
  have hyN : y ^ k ≤ 2 ^ k * N := vinogradovCeilRoot_pow_le hk hN
  calc
    (vinogradovReservoirPrime N k i) ^ k ≤ (C * y) ^ k :=
      Nat.pow_le_pow_left (hpB.trans hBC) k
    _ = C ^ k * y ^ k := mul_pow C y k
    _ ≤ C ^ k * (2 ^ k * N) := Nat.mul_le_mul_left _ hyN
    _ = vinogradovReservoirPrimePowerConstant k * N := by
      simp [C, vinogradovReservoirLinearConstant,
        vinogradovReservoirPrimePowerConstant, mul_pow]
      ring

theorem vinogradovReservoirBound_failure_small
    {N k : ℕ} (hk2 : 2 ≤ k) (hN : N ≠ 0)
    (hfail : N < vinogradovReservoirBound N k) :
    N ≤ vinogradovReservoirSmallThreshold k := by
  let y := vinogradovCeilRoot k N
  let C := vinogradovReservoirLinearConstant k
  have hk : k ≠ 0 := by omega
  have hy : 1 ≤ y := vinogradovCeilRoot_pos hk hN
  have hC : 0 < C := by
    exact mul_pos (pow_pos (by omega) _) (by omega)
  have hNyk : N ≤ y ^ k := le_vinogradovCeilRoot_pow hk
  by_cases hyC : y ≤ 2 * C
  · simpa [vinogradovReservoirSmallThreshold, C] using
      hNyk.trans (Nat.pow_le_pow_left hyC k)
  · have hyC' : 2 * C ≤ y - 1 := by omega
    have hkpred : 0 < k - 1 := by omega
    have hlarge : 2 * C ≤ (y - 1) ^ (k - 1) :=
      hyC'.trans (Nat.le_pow hkpred)
    have hy2 : y ≤ 2 * (y - 1) := by omega
    have hBC := vinogradovReservoirBound_le_linear_root hk hN
    have hBN : vinogradovReservoirBound N k < N := by
      calc
        vinogradovReservoirBound N k ≤ C * y := hBC
        _ ≤ C * (2 * (y - 1)) := Nat.mul_le_mul_left C hy2
        _ = (2 * C) * (y - 1) := by ring
        _ ≤ (y - 1) ^ (k - 1) * (y - 1) :=
          Nat.mul_le_mul_right (y - 1) hlarge
        _ = (y - 1) ^ ((k - 1) + 1) := (pow_succ _ _).symm
        _ = (y - 1) ^ k := by congr 1; omega
        _ < N := pred_vinogradovCeilRoot_pow_lt hk hN
    omega

theorem vinogradovReservoirPrime_mul_ceilDiv_le_two_mul
    {N k : ℕ} (_hN : N ≠ 0)
    (i : Fin (vinogradovReservoirSize k))
    (hBN : vinogradovReservoirBound N k ≤ N) :
    vinogradovReservoirPrime N k i *
        (N ⌈/⌉ vinogradovReservoirPrime N k i) ≤ 2 * N := by
  let p := vinogradovReservoirPrime N k i
  have hpB : p ≤ vinogradovReservoirBound N k := by
    have h := vinogradovBertrandPrimeReservoir_add_two_le
      (vinogradovCeilRoot k N + k) (vinogradovReservoirSize k) i
    simpa [p, vinogradovReservoirPrime, vinogradovReservoirBound] using
      (Nat.le_trans (Nat.le_add_right _ 2) h)
  have hpN : p ≤ N := hpB.trans hBN
  rw [Nat.ceilDiv_eq_add_pred_div]
  calc
    p * ((N + p - 1) / p) ≤ N + p - 1 := Nat.mul_div_le _ _
    _ ≤ 2 * N := by omega

end

end RHTower.Sieve
