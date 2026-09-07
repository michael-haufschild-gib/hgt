import GaloisForLFunctions.RHTower.Sieve.GcdPowerDiagonalization
import GaloisForLFunctions.RHTower.Sieve.ReciprocalTotientLogBound
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusUniformBound
import GaloisForLFunctions.RHTower.Sieve.MoebiusScaledReindex
import GaloisForLFunctions.RHTower.Sieve.SelbergDiagonalLowerAsymptotic

/-!
# The Levinson gcd-power forms are `O(N^{s−1} log N)`

For the Barban–Vehov weight `w_m = μ(m) log(N/m)` (`m ≤ N`) the multiples-coordinates of the
Selberg diagonalisation are the corpus's coprime logarithmic Möbius sums:

`Σ_{m ≤ N, e ∣ m} w_m/m = (μ(e)/e) · T_e(N/e)`,   `|T_e(Y)| ≤ C · e/φ(e)`,

so `|Σ_{e∣m} w_m/m| ≤ C/φ(e)` on squarefree `e` and `0` elsewhere.  With the gcd-power kernel
`g_s(e) ≤ e^s` this gives, for every `s ≥ 1`,

`Σ_{h,k ≤ N} w_h w_k (h,k)^s/(hk) ≤ C² N^{s−1} · Σ_{e ≤ N} (e/φ(e))²/e ≤ C² N^{s−1} · 64(1 + log N)`.

The totient sum uses the divisor identity `e/φ(e) = Σ_{f∣e} μ²(f)/φ(f)`, super-multiplicativity
of `φ`, and the corpus bounds `Σ 1/φ ≤ 4(1+log N)`, `Σ μ²(d)/(dφ(d)) ≤ 4`.
-/

open Finset ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

/-! ## Totient sums -/

/-- `μ²(fj)/(fj φ(fj)) ≤ (μ²(f)/(fφ(f)))(μ²(j)/(jφ(j)))`. -/
theorem sqfreeTotientInv_mul_div_le (f j : ℕ) :
    sqfreeTotientInv (f * j) / ((f * j : ℕ) : ℝ)
      ≤ (sqfreeTotientInv f / f) * (sqfreeTotientInv j / j) := by
  by_cases hsq : Squarefree (f * j)
  · obtain ⟨hcop, hsf, hsj⟩ := Nat.squarefree_mul_iff.mp hsq
    rw [sqfreeTotientInv_apply, if_pos hsq, sqfreeTotientInv_apply, if_pos hsf,
      sqfreeTotientInv_apply, if_pos hsj, Nat.totient_mul hcop]
    push_cast
    apply le_of_eq
    ring
  · rw [sqfreeTotientInv_apply, if_neg hsq, zero_div]
    exact mul_nonneg (div_nonneg (sqfreeTotientInv_nonneg f) (Nat.cast_nonneg f))
      (div_nonneg (sqfreeTotientInv_nonneg j) (Nat.cast_nonneg j))

/-- `Σ_{d ≤ N} μ²(d)/φ(d)² ≤ 16`. -/
theorem sum_sqfreeTotientInv_div_totient_le (N : ℕ) :
    ∑ d ∈ Icc 1 N, sqfreeTotientInv d / (Nat.totient d : ℝ) ≤ 16 := by
  classical
  set G : ℕ → ℕ → ℝ := fun f k => sqfreeTotientInv (f * k) / ((f * k : ℕ) : ℝ) * sqfreeTotientInv f
    with hGdef
  have hpt : ∀ d ∈ Icc 1 N, sqfreeTotientInv d / (Nat.totient d : ℝ)
      = ∑ f ∈ d.divisors, G f (d / f) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hφ : (0 : ℝ) < Nat.totient d := by
      exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hd).1
    have h1 : ∀ f ∈ d.divisors, G f (d / f) = (sqfreeTotientInv d / (d : ℝ)) * sqfreeTotientInv f := by
      intro f hf
      simp only [hGdef]
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hf)]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, sum_divisors_sqfreeTotientInv' d]
    field_simp
  rw [Finset.sum_congr rfl hpt, sum_divisors_swap N G]
  have hinner : ∀ f ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / f), G f k ≤ 4 * (sqfreeTotientInv f / f) := by
    intro f hf
    have hf0 : 0 < f := (Finset.mem_Icc.mp hf).1
    calc ∑ k ∈ Icc 1 (N / f), G f k
        ≤ ∑ k ∈ Icc 1 (N / f), (sqfreeTotientInv f / f) * (sqfreeTotientInv k / k)
            * sqfreeTotientInv f := by
          refine Finset.sum_le_sum fun k _ => ?_
          simp only [hGdef]
          exact mul_le_mul_of_nonneg_right (sqfreeTotientInv_mul_div_le f k)
            (sqfreeTotientInv_nonneg f)
      _ = (sqfreeTotientInv f / f) * sqfreeTotientInv f * ∑ k ∈ Icc 1 (N / f), sqfreeTotientInv k / k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ ≤ (sqfreeTotientInv f / f) * 1 * 4 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (sqfreeTotientInv_le_one f)
            (div_nonneg (sqfreeTotientInv_nonneg f) (Nat.cast_nonneg f)))
            (sum_sqfreeTotientInv_div_le (N / f)) (Finset.sum_nonneg fun k _ =>
              div_nonneg (sqfreeTotientInv_nonneg k) (Nat.cast_nonneg k)) (by
                exact mul_nonneg (div_nonneg (sqfreeTotientInv_nonneg f) (Nat.cast_nonneg f))
                  zero_le_one)
      _ = 4 * (sqfreeTotientInv f / f) := by ring
  calc ∑ f ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / f), G f k
      ≤ ∑ f ∈ Icc 1 N, 4 * (sqfreeTotientInv f / f) := Finset.sum_le_sum hinner
    _ = 4 * ∑ f ∈ Icc 1 N, sqfreeTotientInv f / f := by rw [Finset.mul_sum]
    _ ≤ 4 * 4 := by
        apply mul_le_mul_of_nonneg_left (sum_sqfreeTotientInv_div_le N) (by norm_num)
    _ = 16 := by norm_num

/-- `Σ_{e ≤ N} (e/φ(e))²/e ≤ 64 (1 + log N)`. -/
theorem sum_totientRatio_sq_div_le (N : ℕ) :
    ∑ e ∈ Icc 1 N, ((e : ℝ) / (Nat.totient e : ℝ)) ^ 2 / (e : ℝ) ≤ 64 * (1 + Real.log N) := by
  classical
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
  set G : ℕ → ℕ → ℝ := fun f k => sqfreeTotientInv f * (1 / (Nat.totient (f * k) : ℝ)) with hGdef
  have hpt : ∀ e ∈ Icc 1 N, ((e : ℝ) / (Nat.totient e : ℝ)) ^ 2 / (e : ℝ)
      = ∑ f ∈ e.divisors, G f (e / f) := by
    intro e he
    have he0 : (0 : ℝ) < e := by exact_mod_cast (Finset.mem_Icc.mp he).1
    have hφ : (0 : ℝ) < Nat.totient e := by
      exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp he).1
    have h1 : ∀ f ∈ e.divisors, G f (e / f) = sqfreeTotientInv f * (1 / (Nat.totient e : ℝ)) := by
      intro f hf
      simp only [hGdef]
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hf)]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, sum_divisors_sqfreeTotientInv' e]
    field_simp
  rw [Finset.sum_congr rfl hpt, sum_divisors_swap N G]
  have hinner : ∀ f ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / f), G f k
      ≤ (sqfreeTotientInv f / (Nat.totient f : ℝ)) * (4 * (1 + Real.log N)) := by
    intro f hf
    have hf0 : 0 < f := (Finset.mem_Icc.mp hf).1
    have hφf : (0 : ℝ) < Nat.totient f := by exact_mod_cast Nat.totient_pos.mpr hf0
    have hsup : ∀ k ∈ Icc 1 (N / f), (1 : ℝ) / (Nat.totient (f * k) : ℝ)
        ≤ (1 / (Nat.totient f : ℝ)) * (1 / (Nat.totient k : ℝ)) := by
      intro k hk
      have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
      have hφk : (0 : ℝ) < Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr hk0
      have hsm : (Nat.totient f : ℝ) * Nat.totient k ≤ Nat.totient (f * k) := by
        exact_mod_cast Nat.totient_super_multiplicative f k
      rw [div_mul_div_comm, one_mul]
      exact one_div_le_one_div_of_le (by positivity) hsm
    have hlogdiv : Real.log ((N / f : ℕ) : ℝ) ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos (N / f) with h0 | hpos
      · rw [h0]; simp; exact hlogN
      · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.div_le_self N f)
    calc ∑ k ∈ Icc 1 (N / f), G f k
        ≤ ∑ k ∈ Icc 1 (N / f), sqfreeTotientInv f * ((1 / (Nat.totient f : ℝ)) * (1 / (Nat.totient k : ℝ))) := by
          refine Finset.sum_le_sum fun k hk => ?_
          simp only [hGdef]
          exact mul_le_mul_of_nonneg_left (hsup k hk) (sqfreeTotientInv_nonneg f)
      _ = (sqfreeTotientInv f / (Nat.totient f : ℝ)) * ∑ k ∈ Icc 1 (N / f), 1 / (Nat.totient k : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ ≤ (sqfreeTotientInv f / (Nat.totient f : ℝ)) * (4 * (1 + Real.log ((N / f : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left (sum_inv_totient_le (N / f))
            (div_nonneg (sqfreeTotientInv_nonneg f) hφf.le)
      _ ≤ (sqfreeTotientInv f / (Nat.totient f : ℝ)) * (4 * (1 + Real.log N)) := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg (sqfreeTotientInv_nonneg f) hφf.le)
          linarith
  calc ∑ f ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / f), G f k
      ≤ ∑ f ∈ Icc 1 N, (sqfreeTotientInv f / (Nat.totient f : ℝ)) * (4 * (1 + Real.log N)) :=
        Finset.sum_le_sum hinner
    _ = (∑ f ∈ Icc 1 N, sqfreeTotientInv f / (Nat.totient f : ℝ)) * (4 * (1 + Real.log N)) := by
        rw [Finset.sum_mul]
    _ ≤ 16 * (4 * (1 + Real.log N)) :=
        mul_le_mul_of_nonneg_right (sum_sqfreeTotientInv_div_totient_le N) (by positivity)
    _ = 64 * (1 + Real.log N) := by ring

/-! ## The multiples-coordinates of the Barban–Vehov weight -/

/-- `Σ_{m ≤ N, e ∣ m} w_m/m = (μ(e)/e) T_e(N/e)`. -/
theorem selbergMultiplesInner_barbanVehov_eq (N : ℕ) {e : ℕ} (he : 0 < e) :
    selbergMultiplesInner N (barbanVehovWeight N) e
      = ((moebius e : ℤ) : ℝ) / e * coprimeLogMoebius e ((N : ℝ) / e) := by
  classical
  unfold selbergMultiplesInner
  rw [sum_filter_dvd_eq_sum_scaled he, coprimeLogMoebius, Nat.floor_div_natCast, Nat.floor_natCast,
    Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : 0 < j := (Finset.mem_Icc.mp hj).1
  have hjN : e * j ≤ N := by
    have := (Finset.mem_Icc.mp hj).2
    calc e * j = j * e := mul_comm _ _
      _ ≤ N := Nat.mul_le_of_le_div e j N this
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
  rw [barbanVehovWeight, if_pos hjN]
  by_cases hcop : Nat.Coprime e j
  · rw [if_pos hcop, isMultiplicative_moebius.map_mul_of_coprime hcop]
    push_cast
    rw [div_div]
    field_simp
  · rw [if_neg hcop, moebius_mul_eq_zero_of_not_coprime hcop]
    simp

/-- `|Σ_{e ∣ m} w_m/m| ≤ C · μ²(e)/φ(e)`. -/
theorem abs_selbergMultiplesInner_barbanVehov_le (N : ℕ) {e : ℕ} (he : 0 < e) :
    |selbergMultiplesInner N (barbanVehovWeight N) e|
      ≤ coprimeLogMoebiusConst * sqfreeTotientInv e := by
  rw [selbergMultiplesInner_barbanVehov_eq N he, sqfreeTotientInv_apply]
  by_cases hsq : Squarefree e
  · rw [if_pos hsq, abs_mul, abs_div, Nat.abs_cast]
    have hT := abs_coprimeLogMoebius_le e hsq ((N : ℝ) / e)
    have hμ : |((moebius e : ℤ) : ℝ)| ≤ 1 := by
      have := abs_moebius_le_one (m := e)
      exact_mod_cast this
    have heR : (0 : ℝ) < e := by exact_mod_cast he
    have hφ : (0 : ℝ) < Nat.totient e := by exact_mod_cast Nat.totient_pos.mpr he
    calc |((moebius e : ℤ) : ℝ)| / e * |coprimeLogMoebius e ((N : ℝ) / e)|
        ≤ 1 / e * (coprimeLogMoebiusConst * ((e : ℝ) / Nat.totient e)) :=
          mul_le_mul (div_le_div_of_nonneg_right hμ heR.le) hT (abs_nonneg _) (by positivity)
      _ = coprimeLogMoebiusConst * (1 / (Nat.totient e : ℝ)) := by
          field_simp
  · rw [if_neg hsq, moebius_eq_zero_of_not_squarefree hsq]
    simp

/-! ## The gcd-power form of the Barban–Vehov weight -/

theorem gcdPowKernel_le_rpow {s : ℝ} (hs : 0 ≤ s) {e : ℕ} (he : 0 < e) :
    gcdPowKernel s e ≤ (e : ℝ) ^ s := by
  rw [← sum_gcdPowKernel_divisors s he]
  exact Finset.single_le_sum (fun f _ => gcdPowKernel_nonneg hs f) (Nat.mem_divisors_self e he.ne')

/-- **The Levinson gcd-power form is `O(N^{s−1} log N)`** for every `s ≥ 1`:
`Σ_{h,k ≤ N} w_h w_k (h,k)^s/(hk) ≤ C² N^{s−1} · 64(1+log N)` with `w = barbanVehovWeight N`. -/
theorem sum_barbanVehov_gcd_rpow_div_le (N : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N), barbanVehovWeight N p.1 * barbanVehovWeight N p.2
        * (Nat.gcd p.1 p.2 : ℝ) ^ s / ((p.1 : ℝ) * p.2)
      ≤ coprimeLogMoebiusConst ^ 2 * (N : ℝ) ^ (s - 1) * (64 * (1 + Real.log N)) := by
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
  have hC0 := coprimeLogMoebiusConst_nonneg
  have hterm : ∀ e ∈ S, gcdPowKernel s e
        * (∑ m ∈ S.filter (fun m => e ∣ m), barbanVehovWeight N m / (m : ℝ)) ^ 2
      ≤ coprimeLogMoebiusConst ^ 2 * (N : ℝ) ^ (s - 1)
          * (((e : ℝ) / (Nat.totient e : ℝ)) ^ 2 / (e : ℝ)) := by
    intro e he
    have he0 : 0 < e := hSpos e he
    have heR : (0 : ℝ) < e := by exact_mod_cast he0
    have heN : (e : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp he).2
    have hinner : (∑ m ∈ S.filter (fun m => e ∣ m), barbanVehovWeight N m / (m : ℝ)) ^ 2
        ≤ (coprimeLogMoebiusConst * sqfreeTotientInv e) ^ 2 := by
      have h := abs_selbergMultiplesInner_barbanVehov_le N he0
      have h' : |selbergMultiplesInner N (barbanVehovWeight N) e| ^ 2
          ≤ (coprimeLogMoebiusConst * sqfreeTotientInv e) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [sq_abs] at h'
      exact h'
    have hker : gcdPowKernel s e ≤ (N : ℝ) ^ (s - 1) * e := by
      calc gcdPowKernel s e ≤ (e : ℝ) ^ s := gcdPowKernel_le_rpow (by linarith) he0
        _ = (e : ℝ) ^ (s - 1) * e := by
            rw [Real.rpow_sub_one heR.ne']
            field_simp
        _ ≤ (N : ℝ) ^ (s - 1) * e :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow heR.le heN (by linarith)) heR.le
    have hsq : (sqfreeTotientInv e) ^ 2 * e ≤ ((e : ℝ) / (Nat.totient e : ℝ)) ^ 2 / (e : ℝ) := by
      rw [sqfreeTotientInv_apply]
      split_ifs
      · have hφ : (0 : ℝ) < Nat.totient e := by exact_mod_cast Nat.totient_pos.mpr he0
        apply le_of_eq
        field_simp
      · simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
        positivity
    calc gcdPowKernel s e * (∑ m ∈ S.filter (fun m => e ∣ m), barbanVehovWeight N m / (m : ℝ)) ^ 2
        ≤ ((N : ℝ) ^ (s - 1) * e) * (coprimeLogMoebiusConst * sqfreeTotientInv e) ^ 2 :=
          mul_le_mul hker hinner (sq_nonneg _) (by positivity)
      _ = coprimeLogMoebiusConst ^ 2 * (N : ℝ) ^ (s - 1) * ((sqfreeTotientInv e) ^ 2 * e) := by ring
      _ ≤ coprimeLogMoebiusConst ^ 2 * (N : ℝ) ^ (s - 1)
          * (((e : ℝ) / (Nat.totient e : ℝ)) ^ 2 / (e : ℝ)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
  calc ∑ e ∈ S, gcdPowKernel s e
        * (∑ m ∈ S.filter (fun m => e ∣ m), barbanVehovWeight N m / (m : ℝ)) ^ 2
      ≤ ∑ e ∈ S, coprimeLogMoebiusConst ^ 2 * (N : ℝ) ^ (s - 1)
          * (((e : ℝ) / (Nat.totient e : ℝ)) ^ 2 / (e : ℝ)) := Finset.sum_le_sum hterm
    _ = coprimeLogMoebiusConst ^ 2 * (N : ℝ) ^ (s - 1)
          * ∑ e ∈ S, ((e : ℝ) / (Nat.totient e : ℝ)) ^ 2 / (e : ℝ) := by rw [Finset.mul_sum]
    _ ≤ coprimeLogMoebiusConst ^ 2 * (N : ℝ) ^ (s - 1) * (64 * (1 + Real.log N)) :=
        mul_le_mul_of_nonneg_left (sum_totientRatio_sq_div_le N) (by positivity)

end

end RHTower.Sieve
