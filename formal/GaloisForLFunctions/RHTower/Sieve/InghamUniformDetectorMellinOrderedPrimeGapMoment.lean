import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinOrderedPrimeGap
import GaloisForLFunctions.RHTower.XiHeatCassiniPrimeGapMomentBigOBridge

/-!
# Route T pointwise-supply prime-gap moment

The every-base Hoheisel theorem gives an eventual `p^0.71` bound for every ordered prime gap.
A weighted telescoping argument turns this into an unconditional prefix gap-square moment of order
`1.71`.  This is the exact moment consequence of the pointwise supply lane; its exponent remains
strictly above Route T's critical Abel threshold `3/2`.
-/

open Complex Filter Set Topology Asymptotics
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Ordered additive prime gaps telescope exactly. -/
theorem sum_range_xiHeatCassiniOrderedPrimeGap (M : ℕ) :
    ∑ N ∈ Finset.range M, xiHeatCassiniOrderedPrimeGap N =
      (nthPrimeSubtype M : ℝ) - (nthPrimeSubtype 0 : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      unfold xiHeatCassiniOrderedPrimeGap
      ring

/-- The unconditional every-base Route-T supply gives a `p_M^(171/100)` ordered-prefix
gap-square moment. -/
theorem xiHeatCassiniPrimeGapSquarePrefix_isBigO_routeTHoheisel :
    xiHeatCassiniPrimeGapSquarePrefix =O[atTop]
      fun M : ℕ => Real.exp ((171 / 100 : ℝ) * xiMassNthPrimeLogHeight M) := by
  rcases eventually_atTop.1
      Sieve.eventually_nthPrimeSubtype_succ_gap_le_routeTHoheiselEveryBase with
    ⟨N₀, hN₀⟩
  let r : ℝ := Sieve.routeTHoheiselEveryBaseExponent
  let C : ℝ := 1 + ∑ N ∈ Finset.range N₀,
    xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ) ^ r
  have hr : 0 ≤ r := by
    dsimp only [r, Sieve.routeTHoheiselEveryBaseExponent]
    norm_num
  have hp (N : ℕ) : 0 < (nthPrimeSubtype N : ℝ) := nthPrimeSubtype_pos N
  have hratio (N : ℕ) :
      0 ≤ xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ) ^ r :=
    div_nonneg (xiHeatCassiniOrderedPrimeGap_nonneg N)
      (Real.rpow_nonneg (hp N).le _)
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun N _ => hratio N)
  have hpoint (N : ℕ) :
      xiHeatCassiniOrderedPrimeGap N ≤ C * (nthPrimeSubtype N : ℝ) ^ r := by
    by_cases hlarge : N₀ ≤ N
    · have hgap := hN₀ N hlarge
      have hpow0 : 0 ≤ (nthPrimeSubtype N : ℝ) ^ r :=
        Real.rpow_nonneg (hp N).le _
      calc
        xiHeatCassiniOrderedPrimeGap N ≤
            (nthPrimeSubtype N : ℝ) ^ Sieve.routeTHoheiselEveryBaseExponent := by
          simpa [xiHeatCassiniOrderedPrimeGap] using hgap
        _ = (nthPrimeSubtype N : ℝ) ^ r := rfl
        _ ≤ C * (nthPrimeSubtype N : ℝ) ^ r := by
          exact (one_mul _).symm.le.trans
            (mul_le_mul_of_nonneg_right hC1 hpow0)
    · have hmem : N ∈ Finset.range N₀ :=
        Finset.mem_range.mpr (Nat.lt_of_not_ge hlarge)
      have hsum :
          xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ) ^ r ≤ C := by
        calc
          xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ) ^ r ≤
              ∑ j ∈ Finset.range N₀,
                xiHeatCassiniOrderedPrimeGap j / (nthPrimeSubtype j : ℝ) ^ r :=
            Finset.single_le_sum (fun j _ => hratio j) hmem
          _ ≤ C := by dsimp only [C]; linarith
      calc
        xiHeatCassiniOrderedPrimeGap N =
            (xiHeatCassiniOrderedPrimeGap N /
              (nthPrimeSubtype N : ℝ) ^ r) * (nthPrimeSubtype N : ℝ) ^ r := by
          have hpow : 0 < (nthPrimeSubtype N : ℝ) ^ r :=
            Real.rpow_pos_of_pos (hp N) r
          field_simp [hpow.ne']
        _ ≤ C * (nthPrimeSubtype N : ℝ) ^ r :=
          mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg (hp N).le _)
  have hglobal (M : ℕ) :
      xiHeatCassiniPrimeGapSquarePrefix M ≤
        C * Real.exp ((171 / 100 : ℝ) * xiMassNthPrimeLogHeight M) := by
    have hCM0 : 0 ≤ C * (nthPrimeSubtype M : ℝ) ^ r :=
      mul_nonneg (zero_le_one.trans hC1) (Real.rpow_nonneg (hp M).le _)
    calc
      xiHeatCassiniPrimeGapSquarePrefix M =
          ∑ N ∈ Finset.range M, xiHeatCassiniOrderedPrimeGap N ^ 2 := rfl
      _ ≤ ∑ N ∈ Finset.range M,
          (C * (nthPrimeSubtype N : ℝ) ^ r) * xiHeatCassiniOrderedPrimeGap N := by
        apply Finset.sum_le_sum
        intro N _hNM
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (hpoint N)
          (xiHeatCassiniOrderedPrimeGap_nonneg N)
      _ ≤ ∑ N ∈ Finset.range M,
          (C * (nthPrimeSubtype M : ℝ) ^ r) * xiHeatCassiniOrderedPrimeGap N := by
        apply Finset.sum_le_sum
        intro N hNM
        have hNM' : N ≤ M := (Finset.mem_range.mp hNM).le
        have hpmono : (nthPrimeSubtype N : ℝ) ≤ (nthPrimeSubtype M : ℝ) := by
          exact_mod_cast nthPrimeSubtype_strictMono.monotone hNM'
        have hrpow : (nthPrimeSubtype N : ℝ) ^ r ≤
            (nthPrimeSubtype M : ℝ) ^ r :=
          Real.rpow_le_rpow (hp N).le hpmono hr
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpow (zero_le_one.trans hC1))
          (xiHeatCassiniOrderedPrimeGap_nonneg N)
      _ = (C * (nthPrimeSubtype M : ℝ) ^ r) *
          ((nthPrimeSubtype M : ℝ) - (nthPrimeSubtype 0 : ℝ)) := by
        rw [← Finset.mul_sum, sum_range_xiHeatCassiniOrderedPrimeGap]
      _ ≤ (C * (nthPrimeSubtype M : ℝ) ^ r) * (nthPrimeSubtype M : ℝ) := by
        exact mul_le_mul_of_nonneg_left (by linarith [nthPrimeSubtype_pos 0]) hCM0
      _ = C * Real.exp ((171 / 100 : ℝ) * xiMassNthPrimeLogHeight M) := by
        unfold xiMassNthPrimeLogHeight
        calc
          C * (nthPrimeSubtype M : ℝ) ^ r * (nthPrimeSubtype M : ℝ) =
              C * ((nthPrimeSubtype M : ℝ) ^ r *
                (nthPrimeSubtype M : ℝ) ^ (1 : ℝ)) := by
            rw [Real.rpow_one]
            ring
          _ = C * (nthPrimeSubtype M : ℝ) ^ (r + 1) := by
            rw [← Real.rpow_add (hp M)]
          _ = C * Real.exp ((171 / 100 : ℝ) *
                Real.log (nthPrimeSubtype M : ℝ)) := by
            rw [Real.rpow_def_of_pos (hp M)]
            congr 2
            dsimp only [r, Sieve.routeTHoheiselEveryBaseExponent]
            norm_num
            ring
  refine (Asymptotics.IsBigOWith.of_bound (c := C) ?_).isBigO
  filter_upwards with M
  rw [Real.norm_eq_abs,
    abs_of_nonneg (xiHeatCassiniPrimeGapSquarePrefix_nonneg M),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hglobal M

end

end RHTower
