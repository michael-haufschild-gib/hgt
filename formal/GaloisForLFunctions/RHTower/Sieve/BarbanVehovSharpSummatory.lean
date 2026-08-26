import GaloisForLFunctions.RHTower.Sieve.SelbergDiagonalUpperAsymptotic
import GaloisForLFunctions.RHTower.Sieve.GrahamMeanSquare
import GaloisForLFunctions.RHTower.BourgainPartialSummation

/-!
# Sharp summatory estimates for the Barban--Vehov coefficient

The sharp Selberg diagonal controls every longer square-sum prefix with a uniform floor-removal
error. Finite Abel summation then transports that estimate to any harmonic window whose left edge
lies beyond the mollifier length.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

noncomputable section

/-- The Selberg diagonal is exactly the smooth lcm quadratic form. -/
theorem barbanVehovSelbergDiagonal_eq_lcmQuadratic (X : ℕ) :
    barbanVehovSelbergDiagonal X =
      ∑ p ∈ (Finset.Icc 1 X) ×ˢ (Finset.Icc 1 X),
        barbanVehovWeight X p.1 * barbanVehovWeight X p.2 /
          (Nat.lcm p.1 p.2 : ℝ) := by
  let S := Finset.Icc 1 X
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact (Finset.mem_Icc.mp hm).1
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
  calc
    barbanVehovSelbergDiagonal X =
        ∑ e ∈ S.biUnion Nat.divisors, (Nat.totient e : ℝ) *
          (∑ m ∈ S.filter (fun m => e ∣ m), barbanVehovWeight X m / (m : ℝ)) ^ 2 := by
      rw [barbanVehovSelbergDiagonal]
      change (∑ e ∈ S, (Nat.totient e : ℝ) *
        (∑ m ∈ S.filter (fun m => e ∣ m), barbanVehovWeight X m / (m : ℝ)) ^ 2) = _
      rw [hbi]
    _ = ∑ p ∈ S ×ˢ S,
        barbanVehovWeight X p.1 * barbanVehovWeight X p.2 /
          (Nat.lcm p.1 p.2 : ℝ) :=
      (sum_div_lcm_eq_totient_diagonal S hSpos (barbanVehovWeight X)).symm

/-- Uniform sharp floor-removal estimate for the Barban--Vehov square sum. -/
theorem abs_sum_sq_barbanVehovCoeff_sub_mul_diagonal_le
    {X N : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N) :
    |(∑ k ∈ Finset.Icc 1 N, barbanVehovCoeff X k ^ 2) -
        (N : ℝ) * barbanVehovSelbergDiagonal X| ≤
      ((X : ℝ) * Real.log X) ^ 2 := by
  let SX := Finset.Icc 1 X
  let SN := Finset.Icc 1 N
  have hsub : SX ⊆ SN := by
    intro m hm
    obtain ⟨hm1, hmX⟩ := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨hm1, hmX.trans hXN⟩
  have hprod : SX ×ˢ SX ⊆ SN ×ˢ SN := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨hsub hp1, hsub hp2⟩
  have hvanish : ∀ p ∈ SN ×ˢ SN, p ∉ SX ×ˢ SX →
      barbanVehovWeight X p.1 * barbanVehovWeight X p.2 /
        (Nat.lcm p.1 p.2 : ℝ) = 0 := by
    intro p hp hpnot
    have hout : p.1 ∉ SX ∨ p.2 ∉ SX := by
      simpa only [Finset.mem_product, not_and_or] using hpnot
    rcases hout with hout | hout
    · have hpSN := (Finset.mem_product.mp hp).1
      have hgt : X < p.1 := by
        have hp1 := (Finset.mem_Icc.mp hpSN).1
        simpa [SX, Finset.mem_Icc, hp1, not_le] using hout
      rw [barbanVehovWeight, if_neg (not_le.mpr hgt), zero_mul, zero_div]
    · have hpSN := (Finset.mem_product.mp hp).2
      have hgt : X < p.2 := by
        have hp1 := (Finset.mem_Icc.mp hpSN).1
        simpa [SX, Finset.mem_Icc, hp1, not_le] using hout
      have hz : barbanVehovWeight X p.2 = 0 := by
        rw [barbanVehovWeight, if_neg (not_le.mpr hgt)]
      rw [hz, mul_zero, zero_div]
  have hlcm :
      (∑ p ∈ SN ×ˢ SN,
        barbanVehovWeight X p.1 * barbanVehovWeight X p.2 /
          (Nat.lcm p.1 p.2 : ℝ)) = barbanVehovSelbergDiagonal X := by
    rw [barbanVehovSelbergDiagonal_eq_lcmQuadratic X]
    simpa only [SX, SN] using (Finset.sum_subset hprod hvanish).symm
  have hmain :
      (∑ p ∈ SN ×ˢ SN,
        barbanVehovWeight X p.1 * barbanVehovWeight X p.2 *
          ((N : ℝ) / (Nat.lcm p.1 p.2 : ℝ))) =
        (N : ℝ) * barbanVehovSelbergDiagonal X := by
    rw [← hlcm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hcoeff : ∀ k ∈ SN,
      (∑ m ∈ k.divisors, barbanVehovWeight X m) ^ 2 =
        barbanVehovCoeff X k ^ 2 := by
    intro k hk
    rw [barbanVehovCoeff]
  have herr :
      (∑ p ∈ SN ×ˢ SN,
        |barbanVehovWeight X p.1| * |barbanVehovWeight X p.2|) =
        (∑ m ∈ SN, |barbanVehovWeight X m|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  have hfloor := abs_sum_sq_divisorSum_sub_lcm_main_le N (barbanVehovWeight X)
  change |(∑ k ∈ SN, (∑ m ∈ k.divisors, barbanVehovWeight X m) ^ 2) - _| ≤ _ at hfloor
  rw [Finset.sum_congr rfl hcoeff, hmain, herr] at hfloor
  have hl1 := sum_abs_barbanVehovWeight_le hX hXN
  have hl1nonneg : 0 ≤ ∑ m ∈ SN, |barbanVehovWeight X m| :=
    Finset.sum_nonneg fun m hm => abs_nonneg _
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hXR
  have hsquare : (∑ m ∈ SN, |barbanVehovWeight X m|) ^ 2 ≤
      ((X : ℝ) * Real.log X) ^ 2 := by
    nlinarith
  exact hfloor.trans hsquare

private theorem sum_Ioc_eq_sum_Icc_sub (f : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) :
    (∑ k ∈ Finset.Ioc L U, f k) =
      (∑ k ∈ Finset.Icc 1 U, f k) - ∑ k ∈ Finset.Icc 1 L, f k := by
  have hsub : Finset.Icc 1 L ⊆ Finset.Icc 1 U := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
      (Finset.mem_Icc.mp hk).2.trans hLU⟩
  have hdiff : Finset.Icc 1 U \ Finset.Icc 1 L = Finset.Ioc L U := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← hdiff, eq_sub_iff_add_eq]
  exact Finset.sum_sdiff hsub

/-- Harmonic window version of the sharp summatory estimate. -/
theorem abs_sum_Ioc_barbanVehovCoeff_sq_div_sub_diagonal_le
    {X L U : ℕ} (hX : 1 ≤ X) (hXL : X ≤ L) (hLU : L < U) :
    |(∑ k ∈ Finset.Ioc L U, barbanVehovCoeff X k ^ 2 / (k : ℝ)) -
        barbanVehovSelbergDiagonal X *
          (∑ k ∈ Finset.Ioc L U, 1 / (k : ℝ))| ≤
      2 * ((X : ℝ) * Real.log X) ^ 2 / ((L + 1 : ℕ) : ℝ) := by
  let D : ℝ := barbanVehovSelbergDiagonal X
  let E : ℝ := ((X : ℝ) * Real.log X) ^ 2
  have hE : 0 ≤ E := sq_nonneg _
  have hprefix : ∀ n ∈ Finset.Ioc L U,
      |∑ k ∈ Finset.Ioc L n, (barbanVehovCoeff X k ^ 2 - D)| ≤ 2 * E := by
    intro n hn
    have hLn : L ≤ n := (Finset.mem_Ioc.mp hn).1.le
    have hXn : X ≤ n := hXL.trans hLn
    have hnerr := abs_sum_sq_barbanVehovCoeff_sub_mul_diagonal_le hX hXn
    have hLerr := abs_sum_sq_barbanVehovCoeff_sub_mul_diagonal_le hX hXL
    have hidentity :
        (∑ k ∈ Finset.Ioc L n, (barbanVehovCoeff X k ^ 2 - D)) =
          ((∑ k ∈ Finset.Icc 1 n, barbanVehovCoeff X k ^ 2) - (n : ℝ) * D) -
            ((∑ k ∈ Finset.Icc 1 L, barbanVehovCoeff X k ^ 2) - (L : ℝ) * D) := by
      rw [sum_Ioc_eq_sum_Icc_sub _ hLn]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
      push_cast
      ring
    rw [hidentity]
    calc
      |((∑ k ∈ Finset.Icc 1 n, barbanVehovCoeff X k ^ 2) - (n : ℝ) * D) -
          ((∑ k ∈ Finset.Icc 1 L, barbanVehovCoeff X k ^ 2) - (L : ℝ) * D)|
          ≤ |(∑ k ∈ Finset.Icc 1 n, barbanVehovCoeff X k ^ 2) - (n : ℝ) * D| +
            |(∑ k ∈ Finset.Icc 1 L, barbanVehovCoeff X k ^ 2) - (L : ℝ) * D| :=
        abs_sub _ _
      _ ≤ E + E := add_le_add hnerr hLerr
      _ = 2 * E := by ring
  have habel := RHTower.norm_sum_Ioc_weight_mul_le
    (fun k : ℕ => (((barbanVehovCoeff X k ^ 2 - D : ℝ) : ℝ) : ℂ))
    (fun k : ℕ => 1 / (k : ℝ)) hLU
    (fun k => by positivity)
    (fun k hk => by
      have hkpos : (0 : ℝ) < (k : ℝ) := by
        have hkNat : 0 < k := by
          have hXpos : 0 < X := lt_of_lt_of_le Nat.zero_lt_one hX
          have hLpos : 0 < L := hXpos.trans_le hXL
          exact hLpos.trans (Finset.mem_Ioc.mp hk).1
        exact_mod_cast hkNat
      have hksucc : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
      exact one_div_le_one_div_of_le hkpos hksucc)
    (B := 2 * E) (fun n hn => by
      simpa only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
        using hprefix n hn)
  have hrewrite :
      (∑ k ∈ Finset.Ioc L U, barbanVehovCoeff X k ^ 2 / (k : ℝ)) -
          D * (∑ k ∈ Finset.Ioc L U, 1 / (k : ℝ)) =
        ∑ k ∈ Finset.Ioc L U, (1 / (k : ℝ)) *
          (barbanVehovCoeff X k ^ 2 - D) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hrewrite]
  have hleft :
      ‖∑ k ∈ Finset.Ioc L U, ((1 / (k : ℝ) : ℝ) : ℂ) *
          (((barbanVehovCoeff X k ^ 2 - D : ℝ) : ℝ) : ℂ)‖ =
        |∑ k ∈ Finset.Ioc L U, (1 / (k : ℝ)) *
          (barbanVehovCoeff X k ^ 2 - D)| := by
    have hcast :
        (∑ k ∈ Finset.Ioc L U, ((1 / (k : ℝ) : ℝ) : ℂ) *
            (((barbanVehovCoeff X k ^ 2 - D : ℝ) : ℝ) : ℂ)) =
          (((∑ k ∈ Finset.Ioc L U, (1 / (k : ℝ)) *
            (barbanVehovCoeff X k ^ 2 - D)) : ℝ) : ℂ) := by
      norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  rw [hleft] at habel
  simpa only [D, E, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
    mul_assoc, one_mul] using habel

end

end RHTower.Sieve
