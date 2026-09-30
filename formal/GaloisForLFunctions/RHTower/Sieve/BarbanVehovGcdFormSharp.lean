import GaloisForLFunctions.RHTower.Sieve.LevinsonGcdFormBound
import GaloisForLFunctions.RHTower.Sieve.SelbergDiagonalUpperAsymptotic

/-!
# The Levinson gcd-power form against the Selberg diagonal

For squarefree `e` the gcd-power kernel `g_s(e) = ∏_{p ∣ e} (p^s − 1)` is at most `e^{2(s−1)} φ(e)`:
with `x = p^{s−1} ≥ 1`, `p^{2(s−1)}(p − 1) − (p^s − 1) = (x − 1)((p − 1)x − 1) ≥ 0`.  The
multiples-coordinates `Σ_{e ∣ m} w_m/m` of the Barban–Vehov weight vanish off the squarefree
integers, so

`Σ_{h,k ≤ N} w_h w_k (h,k)^s/(hk) ≤ N^{2(s−1)} · D(N)`,   `D(N) = Σ_{e ≤ N} φ(e) (Σ_{e ∣ m} w_m/m)²`,

and `D(N)/log N → 1` (`tendsto_barbanVehovSelbergDiagonal_div_log_one`).  For `s` close to `1` this
replaces the constant `64 C_L²` of `sum_barbanVehov_gcd_rpow_div_le` by `1 + o(1)`.
-/

open Finset ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

/-- `p^s − 1 ≤ p^{2(s−1)} (p − 1)` for a prime `p` and `s ≥ 1`. -/
theorem rpow_sub_one_le_rpow_mul_sub_one {p : ℕ} (hp : p.Prime) {s : ℝ} (hs : 1 ≤ s) :
    (p : ℝ) ^ s - 1 ≤ (p : ℝ) ^ (2 * (s - 1)) * ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (p : ℝ) ^ (s - 1) := ⟨_, rfl⟩
  have hx1 : 1 ≤ x := hx ▸ Real.one_le_rpow (by linarith) (by linarith)
  have hps : (p : ℝ) ^ s = p * x := by
    rw [hx, ← Real.rpow_one_add' hp0.le (by linarith)]
    ring_nf
  have hp2x : (p : ℝ) ^ (2 * (s - 1)) = x ^ 2 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    ring_nf
  rw [hps, hp2x]
  have h1 : 0 ≤ ((p : ℝ) - 1) * x - 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hx1) h1]

/-- **Jordan kernel against the totient.** `g_s(e) ≤ e^{2(s−1)} φ(e)` for squarefree `e`, `s ≥ 1`. -/
theorem gcdPowKernel_le_rpow_mul_totient {s : ℝ} (hs : 1 ≤ s) {e : ℕ} (he : Squarefree e) :
    gcdPowKernel s e ≤ (e : ℝ) ^ (2 * (s - 1)) * (Nat.totient e : ℝ) := by
  have he0 : e ≠ 0 := he.ne_zero
  have hprod : ∏ p ∈ e.primeFactors, p = e := Nat.prod_primeFactors_of_squarefree he
  have hg : gcdPowKernel s e = ∏ p ∈ e.primeFactors, ((p : ℝ) ^ s - 1) := by
    conv_lhs => rw [← hprod]
    rw [(isMultiplicative_gcdPowKernel s).map_prod_of_prime _
      (fun p hp => Nat.prime_of_mem_primeFactors hp)]
    refine Finset.prod_congr rfl fun p hp => ?_
    have := gcdPowKernel_prime_pow s (Nat.prime_of_mem_primeFactors hp) (le_refl 1)
    simpa using this
  have hφ : (Nat.totient e : ℝ) = ∏ p ∈ e.primeFactors, ((p : ℝ) - 1) := by
    have h := Nat.totient_mul_prod_primeFactors e
    rw [hprod, mul_comm] at h
    have h' : e.totient = ∏ p ∈ e.primeFactors, (p - 1) :=
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he0) h
    rw [h', Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hpow : (e : ℝ) ^ (2 * (s - 1)) = ∏ p ∈ e.primeFactors, (p : ℝ) ^ (2 * (s - 1)) := by
    conv_lhs => rw [← hprod]
    rw [Nat.cast_prod, Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
  rw [hg, hφ, hpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p hp => ?_)
    (fun p hp => rpow_sub_one_le_rpow_mul_sub_one (Nat.prime_of_mem_primeFactors hp) hs)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
  have : (1 : ℝ) ≤ (p : ℝ) ^ s := Real.one_le_rpow hp1 (by linarith)
  linarith

/-- **The Levinson gcd-power form against the Selberg diagonal.** For `s ≥ 1`,
`Σ_{h,k ≤ N} w_h w_k (h,k)^s/(hk) ≤ N^{2(s−1)} D(N)` with `w` the Barban–Vehov weight. -/
theorem sum_barbanVehov_gcd_rpow_div_le_diagonal (N : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N), barbanVehovWeight N p.1 * barbanVehovWeight N p.2
        * (Nat.gcd p.1 p.2 : ℝ) ^ s / ((p.1 : ℝ) * p.2)
      ≤ (N : ℝ) ^ (2 * (s - 1)) * barbanVehovSelbergDiagonal N := by
  classical
  let S := Icc 1 N
  have hSpos : ∀ m ∈ S, 0 < m := fun m hm => (Finset.mem_Icc.mp hm).1
  have hbi : S.biUnion Nat.divisors = S := by
    ext e
    constructor
    · intro he
      obtain ⟨m, hm, hem⟩ := Finset.mem_biUnion.mp he
      obtain ⟨hedvd, hm0⟩ := Nat.mem_divisors.mp hem
      have hepos : 0 < e := Nat.pos_of_dvd_of_pos hedvd (hSpos m hm)
      have hemle : e ≤ m := Nat.le_of_dvd (hSpos m hm) hedvd
      exact Finset.mem_Icc.mpr ⟨hepos, hemle.trans (Finset.mem_Icc.mp hm).2⟩
    · intro he
      exact Finset.mem_biUnion.mpr ⟨e, he,
        Nat.mem_divisors.mpr ⟨dvd_rfl, (Nat.ne_of_gt (Finset.mem_Icc.mp he).1)⟩⟩
  rw [sum_gcd_rpow_div_eq_kernel_diagonal S hSpos (barbanVehovWeight N) s, hbi]
  unfold barbanVehovSelbergDiagonal
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e he => ?_
  have he0 : 0 < e := hSpos e he
  have hinner : (∑ m ∈ S.filter (fun m => e ∣ m), barbanVehovWeight N m / (m : ℝ))
      = selbergMultiplesInner N (barbanVehovWeight N) e := rfl
  rw [hinner]
  by_cases hsq : Squarefree e
  · have hk := gcdPowKernel_le_rpow_mul_totient hs hsq
    have heN : (e : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp he).2
    have hpow : (e : ℝ) ^ (2 * (s - 1)) ≤ (N : ℝ) ^ (2 * (s - 1)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg e) heN (by linarith)
    have hφ0 : (0 : ℝ) ≤ Nat.totient e := Nat.cast_nonneg _
    calc gcdPowKernel s e * selbergMultiplesInner N (barbanVehovWeight N) e ^ 2
        ≤ ((e : ℝ) ^ (2 * (s - 1)) * (Nat.totient e : ℝ))
            * selbergMultiplesInner N (barbanVehovWeight N) e ^ 2 :=
          mul_le_mul_of_nonneg_right hk (sq_nonneg _)
      _ ≤ ((N : ℝ) ^ (2 * (s - 1)) * (Nat.totient e : ℝ))
            * selbergMultiplesInner N (barbanVehovWeight N) e ^ 2 := by gcongr
      _ = (N : ℝ) ^ (2 * (s - 1)) * ((Nat.totient e : ℝ)
            * selbergMultiplesInner N (barbanVehovWeight N) e ^ (2 : ℕ)) := by ring
  · have h0 : selbergMultiplesInner N (barbanVehovWeight N) e = 0 := by
      rw [selbergMultiplesInner_barbanVehov_eq N he0, moebius_eq_zero_of_not_squarefree hsq]
      simp
    rw [h0]
    simp

end

end RHTower.Sieve
