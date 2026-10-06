import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeCancellation

/-!
# Every equal-gap tie in the actual hyperbolic prime packet

Equal absolute gaps allow only the original prime or its reflection in the
anchor. The actual pair sieve pays the complete tie sector, including p=q.
-/

noncomputable section

namespace RHTower

open Finset Filter Topology
open GaloisForLFunctions.RHTower

/-- The complete actual equal-gap sector, with both orientations and p=q retained. -/
def chiCubicHyperbolicPrimeTiePacket (N : ℝ) (M : ℕ) : ℂ :=
  ∑ pr ∈ chiCubicHyperbolicPrimeHolePairs N M,
    ∑ q ∈ (primeProfileBand N).filter
      (fun q : ℕ => |(pr.1 : ℝ) - pr.2| = |(q : ℝ) - pr.2|),
        primeGaussianCubicMainEntry N pr.1 q pr.2

/-- The literal cubic-entry bound holds at every positive real band scale. -/
theorem primeGaussianCubicMainEntry_norm_le_real {N : ℝ} (hN : 0 < N) {p q r : ℕ}
    (hp : p ∈ primeProfileBand N) (hq : q ∈ primeProfileBand N)
    (hr : r ∈ primeProfileBand N) :
    ‖primeGaussianCubicMainEntry N p q r‖ ≤ 2 * Real.pi / N := by
  have hp0 := hN.trans (primeProfileBand_mem hN.le hp).2.1
  have hq0 := hN.trans (primeProfileBand_mem hN.le hq).2.1
  have hrN := (primeProfileBand_mem hN.le hr).2.1
  have hr0 := hN.trans hrN
  have hpV := norm_smoothAFECutoff_le_one (div_pos hp0 hN)
  have hqV := norm_smoothAFECutoff_le_one (div_pos hq0 hN)
  have hrV := norm_smoothAFECutoff_le_one (div_pos hr0 hN)
  have hw := bagPhysicalHeightWindow.le_one (x := (p : ℝ) * q / ((r : ℝ) * N))
  simp only [primeGaussianCubicMainEntry, norm_mul, norm_div, Complex.norm_conj,
    Complex.norm_natCast, norm_bourgainOscillation, mul_one]
  rw [Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg]
  calc
    _ ≤ (2 * Real.pi) * 1 * 1 * 1 / r * 1 := by
      gcongr
      exact bagPhysicalHeightWindow.nonneg
    _ = 2 * Real.pi / r := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hN hrN.le

private theorem tie_choices_card (N : ℝ) (p r : ℕ) :
    ((primeProfileBand N).filter
      (fun q : ℕ => |(p : ℝ) - r| = |(q : ℝ) - r|)).card ≤ 2 := by
  classical
  have hsub : (primeProfileBand N).filter
      (fun q : ℕ => |(p : ℝ) - r| = |(q : ℝ) - r|) ⊆ {p, 2 * r - p} := by
    intro q hq
    have h := (Finset.mem_filter.1 hq).2
    rcases abs_eq_abs.1 h with h | h
    · have he : q = p := by exact_mod_cast (show (q : ℝ) = p by linarith)
      simp [he]
    · have he : p + q = 2 * r := by exact_mod_cast (show (p : ℝ) + q = 2 * r by linarith)
      have hq' : q = 2 * r - p := by omega
      simp [hq']
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_insert_le _ _).trans (by simp))

private theorem tie_row_norm {N : ℝ} (hN : 0 < N) {p r : ℕ}
    (hp : p ∈ primeProfileBand N) (hr : r ∈ primeProfileBand N) :
    ‖∑ q ∈ (primeProfileBand N).filter
      (fun q : ℕ => |(p : ℝ) - r| = |(q : ℝ) - r|), primeGaussianCubicMainEntry N p q r‖ ≤
        4 * Real.pi / N := by
  calc
    _ ≤ ∑ q ∈ (primeProfileBand N).filter
        (fun q : ℕ => |(p : ℝ) - r| = |(q : ℝ) - r|), ‖primeGaussianCubicMainEntry N p q r‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _q ∈ (primeProfileBand N).filter
        (fun q : ℕ => |(p : ℝ) - r| = |(q : ℝ) - r|), 2 * Real.pi / N :=
      Finset.sum_le_sum (fun q hq => primeGaussianCubicMainEntry_norm_le_real hN hp
        (Finset.mem_filter.1 hq).1 hr)
    _ = (((primeProfileBand N).filter
        (fun q : ℕ => |(p : ℝ) - r| = |(q : ℝ) - r|)).card : ℝ) * (2 * Real.pi / N) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (2 * Real.pi / N) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast tie_choices_card N p r) (by positivity)
    _ = _ := by ring

private theorem gap_le_floor {p r : ℕ} {x : ℝ} (h : |(p : ℝ) - r| ≤ x) :
    |(p : ℝ) - r| ≤ (⌊x⌋₊ : ℝ) := by
  rcases le_total p r with hpr | hrp
  · have he : |(p : ℝ) - r| = ((r - p : ℕ) : ℝ) := by
      rw [Nat.cast_sub hpr, abs_of_nonpos (sub_nonpos.2 (by exact_mod_cast hpr))]
      ring
    rw [he] at h ⊢
    exact_mod_cast Nat.le_floor h
  · have he : |(p : ℝ) - r| = ((p - r : ℕ) : ℝ) := by
      rw [Nat.cast_sub hrp, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hrp))]
    rw [he] at h ⊢
    exact_mod_cast Nat.le_floor h

/-- The ENTIRE actual equal-gap sector is negligible at the cubic scale.
Both the allowed collision p=q and the reflected prime q=2r-p are paid. -/
theorem chiCubicHyperbolicPrimeTiePacket_tendsto (M : ℕ) :
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N * ‖chiCubicHyperbolicPrimeTiePacket N M‖)
      atTop (𝓝 0) := by
  obtain ⟨A, hA, hpre⟩ := exists_chiCubicPrimeGapCount_prefix_bound
  let C := 8 * Real.pi * A * Real.sqrt (2 * (M : ℝ))
  have hlim : Tendsto (fun N : ℝ => C / Real.sqrt N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    positivity
  · filter_upwards [hpre, eventually_gt_atTop (1 : ℝ)] with N hpreN hN
    have hN0 : 0 < N := by linarith
    have hL : 0 < Real.log N := Real.log_pos hN
    let D := ⌊Real.sqrt (2 * (M : ℝ) * N)⌋₊
    have hY : 0 ≤ 2 * (M : ℝ) * N := by positivity
    have hsub : chiCubicHyperbolicPrimeHolePairs N M ⊆ chiCubicPrimeGapPairs N D := by
      intro pr hpr
      obtain ⟨hmem, hne, hactive⟩ := Finset.mem_filter.1 hpr
      have hr := (Finset.mem_product.1 hmem).2
      have hrN := (primeProfileBand_mem hN0.le hr).2.2
      have hsquare : |(pr.1 : ℝ) - pr.2| ^ 2 ≤ 2 * M * N := by
        calc
          _ ≤ (M : ℝ) * pr.2 := hactive
          _ ≤ (M : ℝ) * (2 * N) := by gcongr
          _ = _ := by ring
      have hrad : |(pr.1 : ℝ) - pr.2| ≤ Real.sqrt (2 * (M : ℝ) * N) := by
        have hroot := Real.sq_sqrt hY
        have hroot0 := Real.sqrt_nonneg (2 * (M : ℝ) * N)
        nlinarith [abs_nonneg ((pr.1 : ℝ) - pr.2)]
      exact Finset.mem_filter.2 ⟨hmem, hne, gap_le_floor hrad⟩
    have hcard : ((chiCubicHyperbolicPrimeHolePairs N M).card : ℝ) ≤
        2 * A * D * N / Real.log N ^ 2 := by
      have hcardGap : ((chiCubicPrimeGapPairs N D).card : ℝ) =
          2 * ∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d := by
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
          chiCubicPrimeGapPairs_sum N D (fun _ => 1)
      calc
        _ ≤ ((chiCubicPrimeGapPairs N D).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        _ = _ := hcardGap
        _ ≤ 2 * (A * D * N / Real.log N ^ 2) :=
          mul_le_mul_of_nonneg_left (hpreN D) (by norm_num)
        _ = _ := by ring
    have hmass : ‖chiCubicHyperbolicPrimeTiePacket N M‖ ≤
        8 * Real.pi * A * D / Real.log N ^ 2 := by
      calc
        _ ≤ ∑ pr ∈ chiCubicHyperbolicPrimeHolePairs N M,
            ‖∑ q ∈ (primeProfileBand N).filter
              (fun q : ℕ => |(pr.1 : ℝ) - pr.2| = |(q : ℝ) - pr.2|),
                primeGaussianCubicMainEntry N pr.1 q pr.2‖ := norm_sum_le _ _
        _ ≤ ∑ _pr ∈ chiCubicHyperbolicPrimeHolePairs N M, 4 * Real.pi / N := by
          apply Finset.sum_le_sum
          intro pr hpr
          obtain ⟨hp, hr⟩ := Finset.mem_product.1 (Finset.mem_filter.1 hpr).1
          exact tie_row_norm hN0 hp hr
        _ = ((chiCubicHyperbolicPrimeHolePairs N M).card : ℝ) * (4 * Real.pi / N) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * A * D * N / Real.log N ^ 2) * (4 * Real.pi / N) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by
          field_simp
          ring
    have hD : (D : ℝ) ≤ Real.sqrt (2 * (M : ℝ)) * Real.sqrt N := by
      have hh : (D : ℝ) ≤ Real.sqrt (2 * (M : ℝ) * N) := Nat.floor_le (Real.sqrt_nonneg _)
      rwa [Real.sqrt_mul (by positivity)] at hh
    have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    calc
      _ ≤ (Real.log N ^ 2 / N) * (8 * Real.pi * A * D / Real.log N ^ 2) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = 8 * Real.pi * A * D / N := by field_simp
      _ ≤ 8 * Real.pi * A * (Real.sqrt (2 * (M : ℝ)) * Real.sqrt N) / N := by gcongr
      _ = C / Real.sqrt N := by
        dsimp [C]
        field_simp
        rw [Real.sq_sqrt hN0.le]

end RHTower
