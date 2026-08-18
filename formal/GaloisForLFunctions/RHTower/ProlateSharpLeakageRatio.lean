import GaloisForLFunctions.RHTower.ProlateSharpExponentPower
import GaloisForLFunctions.RHTower.ProlateLeakageRatioVanishing

/-!
# The leakage ratio at the sharp power

The crude ladder compares consecutive signed leakages with the factor `c^{-3/4}`, which suffices for
the envelope but not for the card's exponents.  Replacing the crude amplitude ratio with the sharp
one carries the exact power `c^{-2(n−m)}` through the two transfers that follow it: from the pair
anchor to the centre (via the Hermite quotients) and from the centre to the leakage (via the
two-sided sharp mass ratio).
-/

noncomputable section

open Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-- **The centre amplitude ratio at the sharp power.** -/
theorem exists_bound_centre_sq_ratio_power (m n : ℕ) (hmn : m < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ a : ℝ in atTop,
      (signedModeRadialData a n).R 0 ^ 2
        ≤ C / signedModeRadialBandwidth a ^ (2 * (n - m))
          * (signedModeRadialData a m).R 0 ^ 2 := by
  obtain ⟨C₀, hC₀, hC₀e⟩ := exists_bound_prolateBand_sq_ratio_power m n hmn
  have hqn : pairAnchorHermiteQuotient m n n ≠ 0 :=
    pairAnchorHermiteQuotient_ne_zero m n n (Or.inr rfl)
  have hqm : pairAnchorHermiteQuotient m n m ≠ 0 :=
    pairAnchorHermiteQuotient_ne_zero m n m (Or.inl rfl)
  have hqn2 : 0 < pairAnchorHermiteQuotient m n n ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hqn))
  have hqm2 : 0 < pairAnchorHermiteQuotient m n m ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hqm))
  refine ⟨16 * pairAnchorHermiteQuotient m n m ^ 2 / pairAnchorHermiteQuotient m n n ^ 2 * C₀,
    by positivity, ?_⟩
  filter_upwards [hC₀e, eventually_pairAnchor_quotient_bounds m n n (Or.inr rfl),
    eventually_pairAnchor_quotient_bounds m n m (Or.inl rfl),
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (1 : ℝ)]
    with a hratio hbn hbm hc1
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  have hc0 : (0 : ℝ) < c := by linarith
  set S : ℝ := c ^ (2 * (n - m)) with hSdef
  have hS : 0 < S := by rw [hSdef]; positivity
  set y₀ : ℝ := pairAnchorPoint m n a with hy₀def
  have hRn0 : (signedModeRadialData a n).R 0 ≠ 0 := by
    intro hzero
    have h := hbn.1
    rw [hzero, div_zero, abs_zero] at h
    have hpos : 0 < |pairAnchorHermiteQuotient m n n| := abs_pos.2 hqn
    linarith
  have hRm0 : (signedModeRadialData a m).R 0 ≠ 0 := by
    intro hzero
    have h := hbm.1
    rw [hzero, div_zero, abs_zero] at h
    have hpos : 0 < |pairAnchorHermiteQuotient m n m| := abs_pos.2 hqm
    linarith
  set ρn : ℝ := (signedModeRadialData a n).R y₀ / (signedModeRadialData a n).R 0 with hρn
  set ρm : ℝ := (signedModeRadialData a m).R y₀ / (signedModeRadialData a m).R 0 with hρm
  have hfn : (signedModeRadialData a n).R y₀ = ρn * (signedModeRadialData a n).R 0 := by
    rw [hρn]
    field_simp
  have hfm : (signedModeRadialData a m).R y₀ = ρm * (signedModeRadialData a m).R 0 := by
    rw [hρm]
    field_simp
  have hnsq : pairAnchorHermiteQuotient m n n ^ 2 / 4 * (signedModeRadialData a n).R 0 ^ 2
      ≤ (signedModeRadialData a n).R y₀ ^ 2 := by
    have h1 : |pairAnchorHermiteQuotient m n n| / 2 ≤ |ρn| := hbn.1
    have h2 : (|pairAnchorHermiteQuotient m n n| / 2) ^ 2 ≤ |ρn| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have habs1 : |ρn| ^ 2 = ρn ^ 2 := sq_abs ρn
    have habs2 : |pairAnchorHermiteQuotient m n n| ^ 2
        = pairAnchorHermiteQuotient m n n ^ 2 := sq_abs _
    have hkey : pairAnchorHermiteQuotient m n n ^ 2 / 4 ≤ ρn ^ 2 := by
      rw [div_pow, habs1, habs2] at h2
      norm_num at h2
      linarith [h2]
    rw [hfn]
    calc pairAnchorHermiteQuotient m n n ^ 2 / 4 * (signedModeRadialData a n).R 0 ^ 2
        ≤ ρn ^ 2 * (signedModeRadialData a n).R 0 ^ 2 :=
          mul_le_mul_of_nonneg_right hkey (sq_nonneg _)
      _ = (ρn * (signedModeRadialData a n).R 0) ^ 2 := by ring
  have hmsq : (signedModeRadialData a m).R y₀ ^ 2
      ≤ 4 * pairAnchorHermiteQuotient m n m ^ 2 * (signedModeRadialData a m).R 0 ^ 2 := by
    have h1 : |ρm| ≤ 2 * |pairAnchorHermiteQuotient m n m| := hbm.2
    have h2 : |ρm| ^ 2 ≤ (2 * |pairAnchorHermiteQuotient m n m|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    have habs1 : |ρm| ^ 2 = ρm ^ 2 := sq_abs ρm
    have habs2 : |pairAnchorHermiteQuotient m n m| ^ 2
        = pairAnchorHermiteQuotient m n m ^ 2 := sq_abs _
    have hkey : ρm ^ 2 ≤ 4 * pairAnchorHermiteQuotient m n m ^ 2 := by
      rw [mul_pow, habs1, habs2] at h2
      norm_num at h2
      linarith [h2]
    rw [hfm]
    calc (ρm * (signedModeRadialData a m).R 0) ^ 2
        = ρm ^ 2 * (signedModeRadialData a m).R 0 ^ 2 := by ring
      _ ≤ 4 * pairAnchorHermiteQuotient m n m ^ 2 * (signedModeRadialData a m).R 0 ^ 2 :=
          mul_le_mul_of_nonneg_right hkey (sq_nonneg _)
  have hchain : pairAnchorHermiteQuotient m n n ^ 2 / 4 * (signedModeRadialData a n).R 0 ^ 2
      ≤ C₀ / S * (4 * pairAnchorHermiteQuotient m n m ^ 2
        * (signedModeRadialData a m).R 0 ^ 2) := by
    refine le_trans hnsq (le_trans hratio ?_)
    refine mul_le_mul_of_nonneg_left hmsq ?_
    positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hS]
  have hfac : (0 : ℝ) < 4 * S / pairAnchorHermiteQuotient m n n ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hchain hfac.le
  have hL : 4 * S / pairAnchorHermiteQuotient m n n ^ 2
      * (pairAnchorHermiteQuotient m n n ^ 2 / 4 * (signedModeRadialData a n).R 0 ^ 2)
      = (signedModeRadialData a n).R 0 ^ 2 * S := by
    field_simp
  have hR : 4 * S / pairAnchorHermiteQuotient m n n ^ 2
      * (C₀ / S * (4 * pairAnchorHermiteQuotient m n m ^ 2
        * (signedModeRadialData a m).R 0 ^ 2))
      = 16 * pairAnchorHermiteQuotient m n m ^ 2 / pairAnchorHermiteQuotient m n n ^ 2 * C₀
        * (signedModeRadialData a m).R 0 ^ 2 := by
    field_simp
    ring
  rw [hL, hR] at hmul
  exact hmul


/-- **The signed leakage ratio at the sharp power.**  This replaces the crude `c^{-3/4}` comparison
of the step-one ladder by the exact inverse power `c^{-2(n−m)}`. -/
theorem exists_bound_signedLeakage_ratio_power (m n : ℕ) (hmn : m < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ a : ℝ in atTop,
      evenProlateSignedLeakage a m
        ≤ C / signedModeRadialBandwidth a ^ (2 * (n - m))
          * evenProlateSignedLeakage a n := by
  obtain ⟨C₁, hC₁, hC₁e⟩ := exists_bound_centre_sq_ratio_power m n hmn
  have hM : (0 : ℝ) ≤ radialProlateExteriorMassConstant := radialProlateExteriorMassConstant_nonneg
  have hLn : 0 < sharpInteriorLimit n := sharpInteriorLimit_pos n
  have hLm : 0 < sharpInteriorLimit m := sharpInteriorLimit_pos m
  have hF : 0 < besselEnergyFloor := besselEnergyFloor_pos
  refine ⟨4 * radialProlateExteriorMassConstant * C₁ * 1728 * sharpInteriorLimit n
    / (sharpInteriorLimit m * besselEnergyFloor) + 1, by positivity, ?_⟩
  filter_upwards [eventually_signedLeakage_sharp_two_sided m,
    eventually_signedLeakage_sharp_two_sided n, hC₁e,
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (1 : ℝ)]
    with a hm hn hcentre hc1
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  obtain ⟨hRm0, _, hmup⟩ := hm
  obtain ⟨hRn0, hnlow, _⟩ := hn
  have hc0 : (0 : ℝ) < signedModeRadialBandwidth a := by linarith
  set sc : ℝ := Real.sqrt (signedModeRadialBandwidth a) with hscdef
  have hsc : 0 < sc := Real.sqrt_pos.2 hc0
  set S : ℝ := c ^ (2 * (n - m)) with hSdef
  have hS : 0 < S := by rw [hSdef]; positivity
  set Rm : ℝ := (signedModeRadialData a m).R 0 with hRm
  set Rn : ℝ := (signedModeRadialData a n).R 0 with hRn
  have hRm2 : 0 < Rm ^ 2 := by positivity
  have hRn2 : 0 < Rn ^ 2 := by positivity
  have hCnn : 0 ≤ C₁ := hC₁.le
  -- the centre comparison, in reciprocal form
  have hrecip : 1 / Rm ^ 2 ≤ C₁ / S / Rn ^ 2 := by
    rcases eq_or_lt_of_le hCnn with hC0 | hCpos
    · exfalso
      rw [← hC0] at hcentre
      simp only [zero_div, zero_mul] at hcentre
      linarith [hRn2, hcentre]
    · rw [div_le_div_iff₀ hRm2 (by positivity)]
      have hstep : Rn ^ 2 * 1 ≤ C₁ / S * Rm ^ 2 := by simpa using hcentre
      nlinarith [hstep]
  -- the leakage of the higher rung, from below
  have hinv : 1 / (sc * Rn ^ 2)
      ≤ 1728 * sharpInteriorLimit n / besselEnergyFloor * evenProlateSignedLeakage a n := by
    have hval : besselEnergyFloor / 1728 / sharpInteriorLimit n / (sc * Rn ^ 2)
        = besselEnergyFloor / (1728 * sharpInteriorLimit n) * (1 / (sc * Rn ^ 2)) := by
      field_simp
    rw [hval] at hnlow
    have hcoef : (0 : ℝ) < besselEnergyFloor / (1728 * sharpInteriorLimit n) := by positivity
    rw [← le_div_iff₀' hcoef] at hnlow
    calc 1 / (sc * Rn ^ 2)
        ≤ evenProlateSignedLeakage a n / (besselEnergyFloor / (1728 * sharpInteriorLimit n)) :=
          hnlow
      _ = 1728 * sharpInteriorLimit n / besselEnergyFloor * evenProlateSignedLeakage a n := by
          field_simp
  -- chain the three estimates
  have hmup' : evenProlateSignedLeakage a m
      ≤ 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m
        * (1 / sc) * (1 / Rm ^ 2) := by
    refine le_trans hmup (le_of_eq ?_)
    field_simp
  have hcoefm : (0 : ℝ) ≤ 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m
      * (1 / sc) := by positivity
  have hstep1 : evenProlateSignedLeakage a m
      ≤ 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m * (1 / sc)
        * (C₁ / S / Rn ^ 2) :=
    le_trans hmup' (mul_le_mul_of_nonneg_left hrecip hcoefm)
  have hstep2 : 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m * (1 / sc)
        * (C₁ / S / Rn ^ 2)
      = 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m * C₁
        * (1 / S) * (1 / (sc * Rn ^ 2)) := by
    field_simp
  have hcoef2 : (0 : ℝ) ≤ 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m
      * C₁ * (1 / S) := by positivity
  have hstep3 : evenProlateSignedLeakage a m
      ≤ 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m * C₁
        * (1 / S)
        * (1728 * sharpInteriorLimit n / besselEnergyFloor * evenProlateSignedLeakage a n) := by
    rw [hstep2] at hstep1
    exact le_trans hstep1 (mul_le_mul_of_nonneg_left hinv hcoef2)
  refine le_trans hstep3 ?_
  have hid : 4 * radialProlateExteriorMassConstant / sharpInteriorLimit m * C₁
        * (1 / S)
        * (1728 * sharpInteriorLimit n / besselEnergyFloor * evenProlateSignedLeakage a n)
      = (4 * radialProlateExteriorMassConstant * C₁ * 1728 * sharpInteriorLimit n
          / (sharpInteriorLimit m * besselEnergyFloor)) / S * evenProlateSignedLeakage a n := by
    field_simp
  rw [hid]
  have hleak0 : 0 ≤ evenProlateSignedLeakage a n := evenProlateSignedLeakage_nonneg a n
  have hKle : 4 * radialProlateExteriorMassConstant * C₁ * 1728 * sharpInteriorLimit n
        / (sharpInteriorLimit m * besselEnergyFloor)
      ≤ 4 * radialProlateExteriorMassConstant * C₁ * 1728 * sharpInteriorLimit n
        / (sharpInteriorLimit m * besselEnergyFloor) + 1 := by linarith
  have hSpos : (0 : ℝ) < S := hS
  gcongr

end RHTower

end
