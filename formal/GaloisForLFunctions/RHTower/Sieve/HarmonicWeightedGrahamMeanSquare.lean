import GaloisForLFunctions.RHTower.Sieve.GrahamMeanSquare
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock

/-!
# The harmonic-weighted Graham mean square

The mollified second moment needs the divisor-sum mean square against the weight `1/k`, not against
the counting measure.  Expanding the square with the weight attached replaces the multiple count
`⌊N/d⌋` by the harmonic sum `(1/d)·H_{⌊N/d⌋}`, and

`0  ≤  (1 + log N)/d − ∑_{k ≤ N, d ∣ k} 1/k  ≤  (1 + log d)/d`

because `log(N/d) ≤ H_{⌊N/d⌋} ≤ 1 + log(N/d)`.  For coefficients supported on `m ≤ X` the lcm never
exceeds `X²`, so the whole defect is bounded by `(1 + 2 log X)` times the square of the `ℓ¹` mass —
a quantity that does not grow with the outer range `N`.  The main term is the same lcm quadratic
form that Graham's evaluation already bounds.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- **The weighted divisor-sum mean square as an lcm quadratic form.** -/
theorem sum_weighted_sq_divisorSum_eq_lcm_quadratic (N : ℕ) (a : ℕ → ℝ) (w : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 N, w k * (∑ m ∈ k.divisors, a m) ^ 2
      = ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
          a p.1 * a p.2 *
            (∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k), w k) := by
  classical
  have hexp : ∀ k ∈ Finset.Icc 1 N, w k * (∑ m ∈ k.divisors, a m) ^ 2
      = ∑ p ∈ k.divisors ×ˢ k.divisors, w k * (a p.1 * a p.2) := by
    intro k _
    rw [sq, Finset.sum_mul_sum, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl hexp]
  have hmem : ∀ (k : ℕ) (p : ℕ × ℕ),
      k ∈ Finset.Icc 1 N ∧ p ∈ k.divisors ×ˢ k.divisors
        ↔ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k)
            ∧ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) := by
    intro k p
    constructor
    · rintro ⟨hk, hp⟩
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
      have hd1 : p.1 ∣ k := Nat.dvd_of_mem_divisors hp1
      have hd2 : p.2 ∣ k := Nat.dvd_of_mem_divisors hp2
      have hk0 : 0 < k := hk1
      refine ⟨Finset.mem_filter.mpr ⟨hk, Nat.lcm_dvd hd1 hd2⟩, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hp1,
          le_trans (Nat.le_of_dvd hk0 hd1) hkN⟩
      · exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hp2,
          le_trans (Nat.le_of_dvd hk0 hd2) hkN⟩
    · rintro ⟨hkf, hp⟩
      obtain ⟨hk, hlcm⟩ := Finset.mem_filter.mp hkf
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
      have hk0 : k ≠ 0 := by omega
      refine ⟨hk, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_lcm_left _ _) hlcm, hk0⟩
      · exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_lcm_right _ _) hlcm, hk0⟩
  rw [Finset.sum_comm' hmem]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The harmonic mass of the multiples of `d`, from above. -/
theorem sum_dvd_inv_le {d N : ℕ} (hd : 0 < d) :
    ∑ k ∈ (Finset.Icc 1 N).filter (fun k => d ∣ k), 1 / (k : ℝ)
      ≤ (1 + Real.log N) / (d : ℝ) := by
  classical
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [sum_filter_dvd_eq_sum_scaled hd (fun k => 1 / (k : ℝ))]
  have hrw : ∑ j ∈ Finset.Icc 1 (N / d), 1 / ((d * j : ℕ) : ℝ)
      = (1 / (d : ℝ)) * ∑ j ∈ Finset.Icc 1 (N / d), 1 / (j : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ((d * j : ℕ) : ℝ) = (d : ℝ) * (j : ℝ) := by push_cast; ring
    rw [this]
    ring
  rw [hrw]
  have hharm := sum_Icc_one_div_le_one_add_log (N / d)
  have hlog : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos (N / d) with h0 | hpos
    · rw [h0]
      simpa using Real.log_natCast_nonneg N
    · refine Real.log_le_log (by exact_mod_cast hpos) ?_
      exact_mod_cast Nat.div_le_self N d
  have hinv : (0 : ℝ) < 1 / (d : ℝ) := by positivity
  calc (1 / (d : ℝ)) * ∑ j ∈ Finset.Icc 1 (N / d), 1 / (j : ℝ)
      ≤ (1 / (d : ℝ)) * (1 + Real.log N) := by
        refine mul_le_mul_of_nonneg_left ?_ hinv.le
        linarith
    _ = (1 + Real.log N) / (d : ℝ) := by ring

/-- The harmonic mass of the multiples of `d`, from below. -/
theorem sum_dvd_inv_ge {d N : ℕ} (hd : 0 < d) (hN : 1 ≤ N) :
    (Real.log N - Real.log d) / (d : ℝ)
      ≤ ∑ k ∈ (Finset.Icc 1 N).filter (fun k => d ∣ k), 1 / (k : ℝ) := by
  classical
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [sum_filter_dvd_eq_sum_scaled hd (fun k => 1 / (k : ℝ))]
  have hrw : ∑ j ∈ Finset.Icc 1 (N / d), 1 / ((d * j : ℕ) : ℝ)
      = (1 / (d : ℝ)) * ∑ j ∈ Finset.Icc 1 (N / d), 1 / (j : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ((d * j : ℕ) : ℝ) = (d : ℝ) * (j : ℝ) := by push_cast; ring
    rw [this]
    ring
  rw [hrw]
  have hlow := log_sub_le_sum_Icc_one_div (m := 1) (n := N / d) le_rfl
    (Nat.succ_le_succ (Nat.zero_le _))
  have hlow' : Real.log (((N / d : ℕ) : ℝ) + 1) ≤ ∑ j ∈ Finset.Icc 1 (N / d), 1 / (j : ℝ) := by
    simpa using hlow
  have hfloor : (N : ℝ) / (d : ℝ) ≤ ((N / d : ℕ) : ℝ) + 1 := by
    have hnat : N < d * (N / d + 1) := by
      have hmod : d * (N / d) + N % d = N := Nat.div_add_mod N d
      have hlt : N % d < d := Nat.mod_lt _ hd
      calc N = d * (N / d) + N % d := hmod.symm
        _ < d * (N / d) + d := by omega
        _ = d * (N / d + 1) := by ring
    have hcast : (N : ℝ) < (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := by
      have := (Nat.cast_lt (α := ℝ)).mpr hnat
      push_cast at this
      linarith
    rw [div_le_iff₀ hdR]
    linarith
  have hlogle : Real.log N - Real.log d ≤ Real.log (((N / d : ℕ) : ℝ) + 1) := by
    have hdiv : Real.log ((N : ℝ) / (d : ℝ)) = Real.log N - Real.log d :=
      Real.log_div (ne_of_gt hNR) (ne_of_gt hdR)
    rw [← hdiv]
    refine Real.log_le_log (by positivity) hfloor
  have hinv : (0 : ℝ) < 1 / (d : ℝ) := by positivity
  have hfin : (Real.log N - Real.log d) / (d : ℝ)
      = (1 / (d : ℝ)) * (Real.log N - Real.log d) := by ring
  rw [hfin]
  exact mul_le_mul_of_nonneg_left (le_trans hlogle hlow') hinv.le

/-- **The harmonic-weighted mean square of a divisor sum.**  For coefficients supported on `m ≤ X`
the harmonic weight costs only the square of the `ℓ¹` mass, times `1 + 2 log X`. -/
theorem sum_harmonic_sq_divisorSum_le {N X : ℕ} (hN : 1 ≤ N) (a : ℕ → ℝ)
    (hsupp : ∀ m, X < m → a m = 0) :
    ∑ k ∈ Finset.Icc 1 N, (∑ m ∈ k.divisors, a m) ^ 2 / (k : ℝ)
      ≤ (1 + Real.log N) * (∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
            a p.1 * a p.2 / (Nat.lcm p.1 p.2 : ℝ))
        + (1 + 2 * Real.log X) * (∑ m ∈ Finset.Icc 1 N, |a m|) ^ 2 := by
  classical
  have hlogX : (0 : ℝ) ≤ Real.log X := Real.log_natCast_nonneg X
  have hrw : ∑ k ∈ Finset.Icc 1 N, (∑ m ∈ k.divisors, a m) ^ 2 / (k : ℝ)
      = ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) * (∑ m ∈ k.divisors, a m) ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hrw, sum_weighted_sq_divisorSum_eq_lcm_quadratic N a (fun k => 1 / (k : ℝ))]
  have hterm : ∀ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      a p.1 * a p.2 * (∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k), 1 / (k : ℝ))
        ≤ (1 + Real.log N) * (a p.1 * a p.2 / (Nat.lcm p.1 p.2 : ℝ))
          + (1 + 2 * Real.log X) * (|a p.1| * |a p.2|) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hp11, -⟩ := Finset.mem_Icc.mp hp1
    obtain ⟨hp21, -⟩ := Finset.mem_Icc.mp hp2
    have hlcmpos : 0 < Nat.lcm p.1 p.2 := Nat.pos_of_ne_zero (by
      intro h
      rcases Nat.lcm_eq_zero_iff.mp h with h1 | h1 <;> omega)
    have hlcmR : (0 : ℝ) < (Nat.lcm p.1 p.2 : ℝ) := by exact_mod_cast hlcmpos
    have hupper := sum_dvd_inv_le (N := N) hlcmpos
    have hlower := sum_dvd_inv_ge hlcmpos hN
    by_cases hz : a p.1 * a p.2 = 0
    · have habs : |a p.1| * |a p.2| = 0 := by
        rw [← abs_mul, hz, abs_zero]
      rw [hz, habs]
      simp
    · have h1 : a p.1 ≠ 0 := fun h => hz (by rw [h]; ring)
      have h2 : a p.2 ≠ 0 := fun h => hz (by rw [h]; ring)
      have hx1 : p.1 ≤ X := by
        by_contra hcon
        exact h1 (hsupp p.1 (by omega))
      have hx2 : p.2 ≤ X := by
        by_contra hcon
        exact h2 (hsupp p.2 (by omega))
      have hlcmle : Nat.lcm p.1 p.2 ≤ p.1 * p.2 := Nat.le_of_dvd (by positivity)
        (Nat.lcm_dvd_mul p.1 p.2)
      have hloglcm : Real.log (Nat.lcm p.1 p.2 : ℝ) ≤ 2 * Real.log X := by
        have hb : (Nat.lcm p.1 p.2 : ℝ) ≤ (X : ℝ) * (X : ℝ) := by
          have : Nat.lcm p.1 p.2 ≤ X * X := le_trans hlcmle (Nat.mul_le_mul hx1 hx2)
          exact_mod_cast this
        have hXpos : (0 : ℝ) < (X : ℝ) := by
          have : 0 < X := by omega
          exact_mod_cast this
        calc Real.log (Nat.lcm p.1 p.2 : ℝ) ≤ Real.log ((X : ℝ) * (X : ℝ)) :=
              Real.log_le_log hlcmR hb
          _ = 2 * Real.log X := by
              rw [Real.log_mul (ne_of_gt hXpos) (ne_of_gt hXpos)]
              ring
      have hone : (1 : ℝ) ≤ (Nat.lcm p.1 p.2 : ℝ) := by exact_mod_cast hlcmpos
      have hdefect : (1 + Real.log N) / (Nat.lcm p.1 p.2 : ℝ)
          - (∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k), 1 / (k : ℝ))
          ≤ 1 + 2 * Real.log X := by
        have hstep : (1 + Real.log N) / (Nat.lcm p.1 p.2 : ℝ)
            - (Real.log N - Real.log (Nat.lcm p.1 p.2 : ℝ)) / (Nat.lcm p.1 p.2 : ℝ)
            = (1 + Real.log (Nat.lcm p.1 p.2 : ℝ)) / (Nat.lcm p.1 p.2 : ℝ) := by
          field_simp
          ring
        have hle : (1 + Real.log (Nat.lcm p.1 p.2 : ℝ)) / (Nat.lcm p.1 p.2 : ℝ)
            ≤ 1 + 2 * Real.log X := by
          have hnum : (0 : ℝ) ≤ 1 + Real.log (Nat.lcm p.1 p.2 : ℝ) := by
            have := Real.log_nonneg hone
            linarith
          calc (1 + Real.log (Nat.lcm p.1 p.2 : ℝ)) / (Nat.lcm p.1 p.2 : ℝ)
              ≤ (1 + Real.log (Nat.lcm p.1 p.2 : ℝ)) / 1 := by
                refine div_le_div_of_nonneg_left hnum ?_ hone
                norm_num
            _ = 1 + Real.log (Nat.lcm p.1 p.2 : ℝ) := by ring
            _ ≤ 1 + 2 * Real.log X := by linarith
        linarith
      have hdefect0 : (0 : ℝ) ≤ (1 + Real.log N) / (Nat.lcm p.1 p.2 : ℝ)
          - (∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k), 1 / (k : ℝ)) := by
        linarith
      have habsle : |a p.1 * a p.2| ≤ |a p.1| * |a p.2| := le_of_eq (abs_mul _ _)
      have hkey : a p.1 * a p.2 *
          (∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k), 1 / (k : ℝ))
          = (1 + Real.log N) * (a p.1 * a p.2 / (Nat.lcm p.1 p.2 : ℝ))
            - (a p.1 * a p.2) * ((1 + Real.log N) / (Nat.lcm p.1 p.2 : ℝ)
              - (∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k), 1 / (k : ℝ))) := by
        field_simp
        ring
      rw [hkey]
      have hbnd : - ((a p.1 * a p.2) * ((1 + Real.log N) / (Nat.lcm p.1 p.2 : ℝ)
          - (∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k), 1 / (k : ℝ))))
          ≤ (1 + 2 * Real.log X) * (|a p.1| * |a p.2|) := by
        have h1' : |(a p.1 * a p.2) * ((1 + Real.log N) / (Nat.lcm p.1 p.2 : ℝ)
            - (∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k), 1 / (k : ℝ)))|
            ≤ (|a p.1| * |a p.2|) * (1 + 2 * Real.log X) := by
          rw [abs_mul]
          refine mul_le_mul (le_of_eq (abs_mul _ _)) ?_ (abs_nonneg _) (by positivity)
          rw [abs_of_nonneg hdefect0]
          exact hdefect
        have h2' := neg_abs_le ((a p.1 * a p.2) * ((1 + Real.log N) / (Nat.lcm p.1 p.2 : ℝ)
            - (∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k), 1 / (k : ℝ))))
        nlinarith [h1', h2']
      linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hprod : ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N), |a p.1| * |a p.2|
      = (∑ m ∈ Finset.Icc 1 N, |a m|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  rw [hprod]

/-- **The harmonic-weighted Graham mean square.** -/
theorem sum_harmonic_sq_barbanVehovCoeff_le {X N : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (barbanVehovCoeff X k) ^ 2 / (k : ℝ)
      ≤ (1 + Real.log N) * (4 * coprimeLogMoebiusConst ^ 2 * (1 + Real.log X))
        + (1 + 2 * Real.log X) * ((X : ℝ) * Real.log X) ^ 2 := by
  classical
  have hN : 1 ≤ N := le_trans hX hXN
  have hsupp : ∀ m, X < m → barbanVehovWeight X m = 0 := by
    intro m hm
    rw [barbanVehovWeight, if_neg (by omega)]
  have hcoeff : ∀ k ∈ Finset.Icc 1 N,
      (∑ m ∈ k.divisors, barbanVehovWeight X m) ^ 2 / (k : ℝ)
        = (barbanVehovCoeff X k) ^ 2 / (k : ℝ) := by
    intro k _
    rw [barbanVehovCoeff]
  rw [← Finset.sum_congr rfl hcoeff]
  refine le_trans (sum_harmonic_sq_divisorSum_le hN (barbanVehovWeight X) hsupp) ?_
  have hform : ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      barbanVehovWeight X p.1 * barbanVehovWeight X p.2 / (Nat.lcm p.1 p.2 : ℝ)
      ≤ 4 * coprimeLogMoebiusConst ^ 2 * (1 + Real.log X) := by
    have hNpos : ∀ m ∈ Finset.Icc 1 N, 0 < m := by
      intro m hm
      obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hm
      omega
    rw [sum_div_lcm_eq_totient_diagonal (Finset.Icc 1 N) hNpos (barbanVehovWeight X)]
    have hbiUnion : (Finset.Icc 1 N).biUnion Nat.divisors ⊆ Finset.Icc 1 N := by
      intro e he
      obtain ⟨m, hm, hem⟩ := Finset.mem_biUnion.mp he
      obtain ⟨-, hmN⟩ := Finset.mem_Icc.mp hm
      obtain ⟨hdvd, hm0⟩ := Nat.mem_divisors.mp hem
      have hpos : 0 < e := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hm0)
      have hle : e ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
      exact Finset.mem_Icc.mpr ⟨hpos, le_trans hle hmN⟩
    have hnn : ∀ e ∈ Finset.Icc 1 N, e ∉ (Finset.Icc 1 N).biUnion Nat.divisors →
        (0 : ℝ) ≤ (Nat.totient e : ℝ) *
          (∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m),
            barbanVehovWeight X m / (m : ℝ)) ^ 2 := by
      intro e _ _
      positivity
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hbiUnion hnn) ?_
    exact barbanVehov_totient_diagonal_le hXN
  have hl1 := sum_abs_barbanVehovWeight_le hX hXN
  have hl1nn : (0 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 N, |barbanVehovWeight X m| :=
    Finset.sum_nonneg fun m _ => abs_nonneg _
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
  have hlogX : (0 : ℝ) ≤ Real.log X := Real.log_natCast_nonneg X
  have hsq : (∑ m ∈ Finset.Icc 1 N, |barbanVehovWeight X m|) ^ 2
      ≤ ((X : ℝ) * Real.log X) ^ 2 := by
    nlinarith [hl1, hl1nn]
  have h1 : (1 + Real.log N) * (∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      barbanVehovWeight X p.1 * barbanVehovWeight X p.2 / (Nat.lcm p.1 p.2 : ℝ))
      ≤ (1 + Real.log N) * (4 * coprimeLogMoebiusConst ^ 2 * (1 + Real.log X)) :=
    mul_le_mul_of_nonneg_left hform (by linarith)
  have h2 : (1 + 2 * Real.log X) * (∑ m ∈ Finset.Icc 1 N, |barbanVehovWeight X m|) ^ 2
      ≤ (1 + 2 * Real.log X) * ((X : ℝ) * Real.log X) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by linarith)
  linarith

end RHTower.Sieve
