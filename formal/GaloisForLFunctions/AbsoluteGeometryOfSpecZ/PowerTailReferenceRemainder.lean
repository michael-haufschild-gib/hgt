import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailArithmeticGrowth
import GaloisForLFunctions.HTGeometry.RpowPartialSumBound
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The reference convolution of two power tails

Integral comparison bounds the discrepancy of `∑_{n≤X} n⁻ᵃ` from its
power integral uniformly in the real cutoff. This controls the reference
convolution after subtraction of its pole term.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Finite power sum at a real cutoff. -/
def powerTailPrefix (a X : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊X⌋₊, powerTailWeight a n

/-- The pole coefficient is an absolutely convergent real Dirichlet series. -/
def powerTailPole (a : ℝ) : ℝ := ∑' n : ℕ, powerTailWeight (1 + a) n

/-- The power convolution after its leading polar coefficient is removed. -/
def powerTailReference (a : ℝ) : ArithmeticFunction ℝ :=
  powerTailZeta (2 * a) * powerTailZeta a - powerTailPole a • powerTailZeta a

theorem powerTailPole_nonneg (a : ℝ) : 0 ≤ powerTailPole a :=
  tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- Truncating the polar coefficient costs the tail of a convergent power series. -/
theorem powerTailPole_sub_sum_bounds {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ powerTailPole a - ∑ n ∈ Icc 1 N, powerTailWeight (1 + a) n ∧
      powerTailPole a - ∑ n ∈ Icc 1 N, powerTailWeight (1 + a) n ≤
        (N : ℝ) ^ (-a) / a := by
  have hs : Summable (powerTailWeight (1 + a)) :=
    Real.summable_nat_rpow.2 (by linarith only [ha])
  have hzero : powerTailWeight (1 + a) 0 = 0 := by
    simp only [powerTailWeight, Nat.cast_zero]
    exact Real.zero_rpow (by linarith only [ha])
  have hprefix : (∑ n ∈ range (N + 1), powerTailWeight (1 + a) n) =
      ∑ n ∈ Icc 1 N, powerTailWeight (1 + a) n := by
    rw [sum_range_succ', hzero, add_zero,
      RHTower.sum_range_succ_eq_sourcePartialSum]
    rfl
  have hsplit : powerTailPole a - ∑ n ∈ Icc 1 N, powerTailWeight (1 + a) n =
      ∑' j : ℕ, powerTailWeight (1 + a) (j + N + 1) := by
    have h := hs.sum_add_tsum_nat_add (N + 1)
    rw [hprefix] at h
    simpa only [powerTailPole, Nat.add_assoc] using (eq_sub_of_add_eq' h).symm
  rw [hsplit]
  refine ⟨tsum_nonneg (fun j => Real.rpow_nonneg (Nat.cast_nonneg _) _), ?_⟩
  simpa only [powerTailWeight, show 1 - (1 + a) = -a by ring,
    show 1 + a - 1 = a by ring] using
    RHTower.Sieve.tsum_tail_rpow_neg_le (show 1 < 1 + a by linarith only [ha]) hN

/-- For a subunit negative power, the finite sum lies within `1/(1-a)`
below its integral, uniformly at every nonnegative real cutoff. -/
theorem powerTailPrefix_sub_integral_bounds {a X : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hX : 0 ≤ X) :
    -(1 / (1 - a)) ≤ powerTailPrefix a X - X ^ (1 - a) / (1 - a) ∧
      powerTailPrefix a X - X ^ (1 - a) / (1 - a) ≤ 0 := by
  let N := ⌊X⌋₊
  have hden : 0 < 1 - a := by linarith only [ha1]
  have hreindex : powerTailPrefix a X =
      ∑ n ∈ range N, ((n : ℝ) + 1) ^ (-a) := by
    have h := RHTower.sum_range_succ_eq_sourcePartialSum (powerTailWeight a) N
    simpa only [RHTower.sourcePartialSum, powerTailPrefix, powerTailWeight,
      Nat.cast_add, Nat.cast_one, N] using h.symm
  have hupper : powerTailPrefix a X ≤ X ^ (1 - a) / (1 - a) := by
    have hu := HTGeometry.sum_rpow_sub_one_le hden
      (show 1 - a < 1 by linarith only [ha]) N
    rw [show 1 - a - 1 = -a by ring, ← hreindex] at hu
    exact hu.trans (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg N) (Nat.floor_le hX) hden.le) hden.le)
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-a)) (Set.Icc 1 (1 + (N : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith only [hx.1]) hxy (by linarith only [ha])
  have hlower := AntitoneOn.integral_le_sum (f := fun x : ℝ => x ^ (-a))
    (x₀ := 1) (a := N) hanti
  have hint : (∫ x in (1 : ℝ)..(1 + (N : ℝ)), x ^ (-a)) =
      ((1 + (N : ℝ)) ^ (1 - a) - 1) / (1 - a) := by
    rw [integral_rpow (Or.inl (by linarith only [ha1])),
      show -a + 1 = 1 - a by ring, Real.one_rpow]
  rw [hint] at hlower
  have hlower' : ((1 + (N : ℝ)) ^ (1 - a) - 1) / (1 - a) ≤ powerTailPrefix a X := by
    simpa only [hreindex, add_comm] using hlower
  have hp : X ^ (1 - a) ≤ (1 + (N : ℝ)) ^ (1 - a) :=
    Real.rpow_le_rpow hX (by simpa only [add_comm] using (Nat.lt_floor_add_one X).le) hden.le
  have hlo := (div_le_div_of_nonneg_right (sub_le_sub_right hp 1) hden.le).trans hlower'
  rw [sub_div] at hlo
  exact ⟨by linarith only [hlo], by linarith only [hupper]⟩

private theorem powerTailPrefix_nat (a : ℝ) (N : ℕ) :
    powerTailPrefix a N = ∑ n ∈ Icc 1 N, powerTailZeta a n := by
  simp only [powerTailPrefix, Nat.floor_natCast]
  exact sum_congr rfl fun n hn => (powerTailZeta_apply (by
    have := (mem_Icc.mp hn).1
    omega) a).symm

private theorem powerTailPrefix_div (a : ℝ) (N : ℕ) {d : ℕ} (hd : 0 < d) :
    powerTailPrefix a ((N : ℝ) / d) = ∑ n ∈ Icc 1 (N / d), powerTailZeta a n := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hfloor : ⌊(N : ℝ) / d⌋₊ = N / d := by
    rw [Nat.floor_eq_iff (by positivity)]
    refine ⟨Nat.cast_div_le, ?_⟩
    rw [div_lt_iff₀ hdR]
    have hlt : N < (N / d + 1) * d := by
      have hm := Nat.div_add_mod N d
      have hr := Nat.mod_lt N hd
      nlinarith only [hm, hr]
    exact_mod_cast hlt
  simp only [powerTailPrefix, hfloor]
  exact sum_congr rfl fun n hn => (powerTailZeta_apply (by
    have := (mem_Icc.mp hn).1
    omega) a).symm

private theorem powerTail_main_product (a : ℝ) (N : ℕ) {d : ℕ} (hd : 0 < d) :
    powerTailWeight (2 * a) d * (((N : ℝ) / d) ^ (1 - a) / (1 - a)) =
      ((N : ℝ) ^ (1 - a) / (1 - a)) * powerTailWeight (1 + a) d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [powerTailWeight]
  rw [Real.div_rpow (Nat.cast_nonneg N) hdR.le]
  calc
    _ = ((N : ℝ) ^ (1 - a) / (1 - a)) *
        ((d : ℝ) ^ (-(2 * a)) * ((d : ℝ) ^ (1 - a))⁻¹) := by ring
    _ = _ := by
      rw [← Real.rpow_neg hdR.le, ← Real.rpow_add hdR]
      congr 2
      ring

/-- The pole-subtracted reference convolution has summatory size `N^(1-2a)`. -/
theorem abs_sum_powerTailReference_le {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, powerTailReference a n| ≤
      ((1 / a + 1 / (1 - 2 * a) + powerTailPole a) / (1 - a)) *
        (N : ℝ) ^ (1 - 2 * a) := by
  have ha1 : a < 1 := by linarith only [ha2]
  have hb : 0 < 1 - a := by linarith only [ha1]
  have hc : 0 < 1 - 2 * a := by linarith only [ha2]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith only [hN1]
  let A := (N : ℝ) ^ (1 - a) / (1 - a)
  let F := (N : ℝ) ^ (1 - 2 * a)
  let T := ∑ d ∈ Icc 1 N, powerTailWeight (1 + a) d
  let S := ∑ d ∈ Icc 1 N, powerTailWeight (2 * a) d
  let D := ∑ d ∈ Icc 1 N, powerTailWeight (2 * a) d * powerTailPrefix a ((N : ℝ) / d)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hF : 1 ≤ F := Real.one_le_rpow hN1 hc.le
  have hZ := powerTailPole_nonneg a
  have htail := powerTailPole_sub_sum_bounds ha hN
  change 0 ≤ powerTailPole a - T ∧ powerTailPole a - T ≤ (N : ℝ) ^ (-a) / a at htail
  have hprefix := powerTailPrefix_sub_integral_bounds ha ha1 hNp.le
  change -(1 / (1 - a)) ≤ powerTailPrefix a N - A ∧ powerTailPrefix a N - A ≤ 0 at hprefix
  have hmain : (∑ d ∈ Icc 1 N,
      powerTailWeight (2 * a) d * (((N : ℝ) / d) ^ (1 - a) / (1 - a))) = A * T := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun d hd => powerTail_main_product a N (by
      have := (mem_Icc.mp hd).1
      omega)
  have hDupper : D ≤ A * T := by
    rw [← hmain]
    apply sum_le_sum
    intro d hd
    have h := (powerTailPrefix_sub_integral_bounds ha ha1
      (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg d))).2
    exact mul_le_mul_of_nonneg_left (by linarith only [h])
      (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hDlower : A * T - S / (1 - a) ≤ D := by
    have h := sum_le_sum (s := Icc 1 N) (fun d _ =>
      mul_le_mul_of_nonneg_left
        (show ((N : ℝ) / d) ^ (1 - a) / (1 - a) - 1 / (1 - a) ≤
            powerTailPrefix a ((N : ℝ) / d) from by
          have hp := (powerTailPrefix_sub_integral_bounds ha ha1
            (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg d))).1
          linarith only [hp])
        (Real.rpow_nonneg (Nat.cast_nonneg d) (-(2 * a))))
    change (∑ d ∈ Icc 1 N, powerTailWeight (2 * a) d *
      (((N : ℝ) / d) ^ (1 - a) / (1 - a) - 1 / (1 - a))) ≤ D at h
    simpa only [mul_sub, sum_sub_distrib, hmain, mul_one_div,
      ← sum_div, S] using h
  have hS : S ≤ F / (1 - 2 * a) := by
    have h := (powerTailPrefix_sub_integral_bounds
      (show 0 < 2 * a by linarith only [ha])
      (show 2 * a < 1 by linarith only [ha2]) hNp.le).2
    simp only [powerTailPrefix, Nat.floor_natCast] at h
    dsimp only [S, F]
    linarith only [h]
  have hAtail : A * (powerTailPole a - T) ≤ F / (a * (1 - a)) := by
    calc
      _ ≤ A * ((N : ℝ) ^ (-a) / a) := mul_le_mul_of_nonneg_left htail.2 hA
      _ = F / (a * (1 - a)) := by
        dsimp only [A, F]
        calc
          _ = ((N : ℝ) ^ (1 - a) * (N : ℝ) ^ (-a)) / (a * (1 - a)) := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
          _ = _ := by rw [← Real.rpow_add hNp]; congr 2; ring
  have hform : (∑ n ∈ Icc 1 N, powerTailReference a n) =
      D - powerTailPole a * powerTailPrefix a N := by
    change (∑ n ∈ Icc 1 N, ((powerTailZeta (2 * a) * powerTailZeta a) n -
      powerTailPole a * powerTailZeta a n)) = _
    rw [sum_sub_distrib, ← mul_sum]
    rw [← powerTailPrefix_nat, RHTower.sum_Icc_mul_apply]
    congr 1
    apply sum_congr rfl
    intro d hd
    have hd0 : 0 < d := by have := (mem_Icc.mp hd).1; omega
    rw [powerTailZeta_apply (by omega), ← powerTailPrefix_div a N hd0]
  rw [hform, abs_le]
  have hlo : -F / (a * (1 - a)) - F / ((1 - 2 * a) * (1 - a)) ≤
      D - powerTailPole a * powerTailPrefix a N := by
    have hZprefix := mul_le_mul_of_nonneg_left (show powerTailPrefix a N ≤ A by
      linarith only [hprefix.2]) hZ
    have hS' := div_le_div_of_nonneg_right hS hb.le
    rw [div_div] at hS'
    calc
      _ ≤ -(A * (powerTailPole a - T)) - S / (1 - a) := by
        simpa only [neg_div] using sub_le_sub (neg_le_neg hAtail) hS'
      _ = (A * T - S / (1 - a)) - powerTailPole a * A := by ring
      _ ≤ _ := sub_le_sub hDlower hZprefix
  have hhi : D - powerTailPole a * powerTailPrefix a N ≤ powerTailPole a / (1 - a) := by
    have hAT := mul_le_mul_of_nonneg_left (show T ≤ powerTailPole a by
      linarith only [htail.1]) hA
    have hZprefix := mul_le_mul_of_nonneg_left (show A - 1 / (1 - a) ≤ powerTailPrefix a N by
      linarith only [hprefix.1]) hZ
    calc
      _ ≤ A * powerTailPole a - powerTailPole a * (A - 1 / (1 - a)) :=
        sub_le_sub (hDupper.trans hAT) hZprefix
      _ = _ := by ring
  have hZF : powerTailPole a / (1 - a) ≤ powerTailPole a / (1 - a) * F :=
    le_mul_of_one_le_right (div_nonneg hZ hb.le) hF
  have hF0 : 0 ≤ F := zero_le_one.trans hF
  have hpositive : 0 ≤ (1 / a + 1 / (1 - 2 * a)) / (1 - a) * F := by positivity
  constructor
  · calc
      _ ≤ -F / (a * (1 - a)) - F / ((1 - 2 * a) * (1 - a)) := by
        have he : -(((1 / a + 1 / (1 - 2 * a) + powerTailPole a) / (1 - a)) * F) =
            -F / (a * (1 - a)) - F / ((1 - 2 * a) * (1 - a)) -
              (powerTailPole a / (1 - a)) * F := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        rw [he]
        exact sub_le_self _ (mul_nonneg (div_nonneg hZ hb.le) hF0)
      _ ≤ _ := hlo
  · calc
      _ ≤ powerTailPole a / (1 - a) * F := hhi.trans hZF
      _ ≤ _ := by
        have he : ((1 / a + 1 / (1 - 2 * a) + powerTailPole a) / (1 - a)) * F =
            ((1 / a + 1 / (1 - 2 * a)) / (1 - a)) * F +
              (powerTailPole a / (1 - a)) * F := by ring
        rw [he]
        exact le_add_of_nonneg_left hpositive

/-- The reference term lies in the strict growth class `1-2a`. -/
theorem partialSumPowerBound_powerTailReference {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    RHTower.PartialSumPowerBound (fun n => powerTailReference a (n + 1)) (1 - 2 * a) := by
  intro δ hδ
  let C := (1 / a + 1 / (1 - 2 * a) + powerTailPole a) / (1 - a)
  have hθ : 0 < 1 - 2 * a := by linarith only [ha2]
  have hden : 0 < 1 - a := by linarith only [ha2]
  have hC : 0 ≤ C := by
    have := powerTailPole_nonneg a
    dsimp only [C]
    positivity
  refine ⟨C, hC, fun N => ?_⟩
  rw [RHTower.sum_range_succ_eq_sourcePartialSum]
  change |∑ n ∈ Icc 1 N, powerTailReference a n| ≤ _
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty, abs_zero]
    positivity
  calc
    _ ≤ C * (N : ℝ) ^ (1 - 2 * a) := abs_sum_powerTailReference_le ha ha2 hN
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) hθ.le).trans
        (Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
          (by linarith only [hδ]))) hC

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
