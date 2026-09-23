import GaloisForLFunctions.RHTower.Sieve.MultiHarmonic
import GaloisForLFunctions.RHTower.Sieve.MultiBadStart

/-!
# The device threshold of the marker family

The lift factor is a fixed multiple of `log M₀` in both directions, so the marker count, the pair
budget and the harmonic mass are all comparable to the number of starts.  Choosing the tolerance of
the Möbius mean square below an explicit constant then makes the Cauchy–Schwarz device discard at
most half the harmonic mass.
-/

namespace RHTower.Sieve

open Filter

noncomputable section

/-- **The lift factor is comparable to the logarithm of the base.** -/
theorem eventually_multiFactor_bounds (K₀ : ℕ) :
    ∀ᶠ v : ℕ in atTop,
      Real.log ((multiBase K₀ v : ℕ) : ℝ) / 2 ≤ ((multiFactor K₀ v : ℕ) : ℝ)
        ∧ ((multiFactor K₀ v : ℕ) : ℝ) ≤ 2 * Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
  have hlogm : ∀ᶠ v : ℕ in atTop, (1 : ℝ) ≤ Real.log ((multiScale K₀ v : ℕ) : ℝ) := by
    have hev : ∀ᶠ y : ℝ in atTop, (1 : ℝ) ≤ Real.log y :=
      Real.tendsto_log_atTop.eventually_ge_atTop 1
    exact (tendsto_multiScale K₀).eventually hev
  have hWm : ∀ᶠ v : ℕ in atTop, ((multiFactor K₀ v : ℕ) : ℝ) ≤ ((multiScale K₀ v : ℕ) : ℝ) := by
    have hlo : (fun y : ℝ => Real.log y ^ (1 : ℝ)) =o[atTop] fun y : ℝ => y ^ (1 : ℝ) :=
      isLittleO_log_rpow_rpow_atTop 1 (by norm_num)
    have hev : ∀ᶠ y : ℝ in atTop, 2 * Real.log y ≤ y := by
      filter_upwards [hlo.def (by norm_num : (0:ℝ) < 1/2), eventually_ge_atTop (1 : ℝ)]
        with y hy hy1
      have hy0 : (0 : ℝ) < y := by linarith
      have hlog0 : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy1
      rw [Real.rpow_one, Real.rpow_one, Real.norm_of_nonneg hlog0,
        Real.norm_of_nonneg hy0.le] at hy
      linarith
    filter_upwards [(tendsto_multiScale K₀).eventually hev,
      (tendsto_multiScale K₀).eventually_ge_atTop 1] with v hv hv1
    have hfl : ((multiFactor K₀ v : ℕ) : ℝ) ≤ 2 * Real.log ((multiScale K₀ v : ℕ) : ℝ) := by
      have h1 : ((multiFactor K₀ v : ℕ) : ℝ)
          ≤ Real.log (((multiScale K₀ v : ℕ) : ℝ) ^ 2) := by
        rw [multiFactor]
        exact Nat.floor_le (Real.log_nonneg (by nlinarith [hv1]))
      have h2 : Real.log (((multiScale K₀ v : ℕ) : ℝ) ^ 2)
          = 2 * Real.log ((multiScale K₀ v : ℕ) : ℝ) := by
        rw [Real.log_pow]
        push_cast
        ring
      linarith [h1, h2]
    linarith [hfl, hv]
  filter_upwards [hlogm, hWm, (tendsto_multiScale K₀).eventually_ge_atTop 1] with v hlog1 hWle hv1
  have hm0 : (0 : ℝ) < ((multiScale K₀ v : ℕ) : ℝ) := by linarith
  have hbaseR : ((multiBase K₀ v : ℕ) : ℝ)
      = ((multiScale K₀ v : ℕ) : ℝ) * ((multiFactor K₀ v : ℕ) : ℝ) := by
    rw [multiBase]
    push_cast
    ring
  have hW0 : (0 : ℝ) ≤ ((multiFactor K₀ v : ℕ) : ℝ) := Nat.cast_nonneg _
  have hW1 : (1 : ℝ) ≤ ((multiFactor K₀ v : ℕ) : ℝ) := by
    have hnat : 1 ≤ multiFactor K₀ v := by
      rw [multiFactor]
      refine Nat.le_floor ?_
      push_cast
      have h3 : Real.log (((multiScale K₀ v : ℕ) : ℝ) ^ 2)
          = 2 * Real.log ((multiScale K₀ v : ℕ) : ℝ) := by
        rw [Real.log_pow]
        push_cast
        ring
      rw [h3]
      linarith
    exact_mod_cast hnat
  -- the upper bound
  have hupper : ((multiFactor K₀ v : ℕ) : ℝ) ≤ 2 * Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
    have h1 : ((multiFactor K₀ v : ℕ) : ℝ) ≤ 2 * Real.log ((multiScale K₀ v : ℕ) : ℝ) := by
      have h2 : ((multiFactor K₀ v : ℕ) : ℝ)
          ≤ Real.log (((multiScale K₀ v : ℕ) : ℝ) ^ 2) := by
        rw [multiFactor]
        exact Nat.floor_le (Real.log_nonneg (by nlinarith [hv1]))
      have h3 : Real.log (((multiScale K₀ v : ℕ) : ℝ) ^ 2)
          = 2 * Real.log ((multiScale K₀ v : ℕ) : ℝ) := by
        rw [Real.log_pow]
        push_cast
        ring
      linarith [h2, h3]
    have hmono : Real.log ((multiScale K₀ v : ℕ) : ℝ)
        ≤ Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
      refine Real.log_le_log hm0 ?_
      rw [hbaseR]
      nlinarith [hm0, hW1]
    linarith
  refine ⟨?_, hupper⟩
  -- the lower bound
  have hMle : Real.log ((multiBase K₀ v : ℕ) : ℝ)
      ≤ 2 * Real.log ((multiScale K₀ v : ℕ) : ℝ) := by
    have hsq : ((multiBase K₀ v : ℕ) : ℝ) ≤ ((multiScale K₀ v : ℕ) : ℝ) ^ 2 := by
      rw [hbaseR, sq]
      exact mul_le_mul_of_nonneg_left hWle hm0.le
    have := Real.log_le_log (by rw [hbaseR]; nlinarith [hm0, hW1]) hsq
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hWge : Real.log ((multiScale K₀ v : ℕ) : ℝ) ≤ ((multiFactor K₀ v : ℕ) : ℝ) := by
    have hfl : Real.log (((multiScale K₀ v : ℕ) : ℝ) ^ 2) - 1
        ≤ ((multiFactor K₀ v : ℕ) : ℝ) := by
      rw [multiFactor]
      have := Nat.lt_floor_add_one (Real.log (((multiScale K₀ v : ℕ) : ℝ) ^ 2))
      linarith
    have h3 : Real.log (((multiScale K₀ v : ℕ) : ℝ) ^ 2)
        = 2 * Real.log ((multiScale K₀ v : ℕ) : ℝ) := by
      rw [Real.log_pow]
      push_cast
      ring
    rw [h3] at hfl
    linarith [hlog1]
  linarith [hMle, hWge]

/-- The Möbius tolerance the device can afford. -/
def multiEps (K₀ : ℕ) : ℝ :=
  multiHarmConst K₀ ^ 2 / (16 * (128 * 2 ^ (K₀ + 1) + 2 * multiPiConst K₀))

theorem multiEps_pos {K₀ : ℕ} (hH : 0 < multiHarmConst K₀) : 0 < multiEps K₀ := by
  rw [multiEps]
  have h1 : (0 : ℝ) < 128 * 2 ^ (K₀ + 1) + 2 * multiPiConst K₀ := by
    have := multiPiConst_pos K₀
    positivity
  positivity

/-- **The sign count of the physical window, eventually.** -/
theorem eventually_card_sign_window_ge {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (K₀ : ℕ)
    (hH : 0 < multiHarmConst K₀) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    ∀ᶠ v : ℕ in atTop,
      (squarefreeDensity / 256)
          * (((multiWindow β K₀ v : ℕ) : ℝ)
              * (multiHarmConst K₀ / (2 * Real.log ((multiBase K₀ v : ℕ) : ℝ)))
            - multiCount K₀ v)
        ≤ ((((Finset.Ioc (multiPhys K₀ v) (multiPhys K₀ v + multiWindow β K₀ v)).filter
            (fun n => ArithmeticFunction.moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  have hβ0' : (0 : ℝ) < β := by linarith
  filter_upwards [eventually_multi_basics β hβ0' hβ1 K₀,
    eventually_multiCell_le β hβ0' hβ1 K₀,
    eventually_multiPi_le K₀,
    eventually_multiHarm_ge K₀,
    eventually_multiCount_le K₀,
    eventually_card_badStartUnion_le hβ0 hβ1 K₀ (multiEps_pos hH),
    eventually_multiFactor_bounds K₀,
    eventually_log_multiBase_ge K₀ 1,
    eventually_log_multiBase_ge K₀ (288 * Real.log 2),
    eventually_log_multiBase_ge K₀ (288 * (20 * mertensFirstConst)),
    eventually_three_le_multiSift K₀,
    (tendsto_multiScale K₀).eventually_ge_atTop 1,
    (tendsto_multiBase K₀).eventually_ge_atTop 2,
    Filter.eventually_gt_atTop 0]
    with v hbasics hC hPi hharm hcount hbad hWb hlog1 hbig288 hbig20 hs3 hm1 hM2R hv0
  obtain ⟨hM0, hXH⟩ := hbasics
  obtain ⟨hWlow, hWup⟩ := hWb
  have hM2 : 2 ≤ multiBase K₀ v := by exact_mod_cast hM2R
  have hM0R : (0 : ℝ) < ((multiBase K₀ v : ℕ) : ℝ) := by exact_mod_cast hM0
  have hlogM : (0 : ℝ) < Real.log ((multiBase K₀ v : ℕ) : ℝ) := by linarith
  have hmR : (1 : ℝ) ≤ ((multiScale K₀ v : ℕ) : ℝ) := by exact_mod_cast hm1
  have hbaseR : ((multiBase K₀ v : ℕ) : ℝ)
      = ((multiScale K₀ v : ℕ) : ℝ) * ((multiFactor K₀ v : ℕ) : ℝ) := by
    rw [multiBase]
    push_cast
    ring
  -- the base against the number of starts
  have hupper : ((multiBase K₀ v : ℕ) : ℝ) / Real.log ((multiBase K₀ v : ℕ) : ℝ)
      ≤ 2 * ((multiScale K₀ v : ℕ) : ℝ) := by
    rw [div_le_iff₀ hlogM]
    calc ((multiBase K₀ v : ℕ) : ℝ)
        = ((multiScale K₀ v : ℕ) : ℝ) * ((multiFactor K₀ v : ℕ) : ℝ) := hbaseR
      _ ≤ ((multiScale K₀ v : ℕ) : ℝ) * (2 * Real.log ((multiBase K₀ v : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hWup (by linarith)
      _ = 2 * ((multiScale K₀ v : ℕ) : ℝ) * Real.log ((multiBase K₀ v : ℕ) : ℝ) := by ring
  have hlower : ((multiScale K₀ v : ℕ) : ℝ) / 2
      ≤ ((multiBase K₀ v : ℕ) : ℝ) / Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
    rw [le_div_iff₀ hlogM]
    calc ((multiScale K₀ v : ℕ) : ℝ) / 2 * Real.log ((multiBase K₀ v : ℕ) : ℝ)
        = ((multiScale K₀ v : ℕ) : ℝ) * (Real.log ((multiBase K₀ v : ℕ) : ℝ) / 2) := by ring
      _ ≤ ((multiScale K₀ v : ℕ) : ℝ) * ((multiFactor K₀ v : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hWlow (by linarith)
      _ = ((multiBase K₀ v : ℕ) : ℝ) := hbaseR.symm
  -- the device
  set b : ℝ := multiHarmConst K₀ * ((multiBase K₀ v : ℕ) : ℝ)
      / (2 * Real.log ((multiBase K₀ v : ℕ) : ℝ)) with hb
  have hb0 : (0 : ℝ) ≤ b := by
    rw [hb]
    positivity
  have hbge : multiHarmConst K₀ * ((multiScale K₀ v : ℕ) : ℝ) / 4 ≤ b := by
    rw [hb, mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hH.le
    rw [show ((multiBase K₀ v : ℕ) : ℝ) / (2 * Real.log ((multiBase K₀ v : ℕ) : ℝ))
        = (((multiBase K₀ v : ℕ) : ℝ) / Real.log ((multiBase K₀ v : ℕ) : ℝ)) / 2 by
      field_simp]
    linarith [hlower]
  have hPi0 : (0 : ℝ) ≤ multiPi K₀ v := by
    rw [multiPi]
    have hL : (0 : ℝ) ≤ (multiLevel K₀ v) ^ 3 := by
      rw [multiLevel]
      positivity
    positivity
  have hsum : (((bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v)).card : ℕ) : ℝ)
      + 2 * multiPi K₀ v
      ≤ (128 * 2 ^ (K₀ + 1) + 2 * multiPiConst K₀) * ((multiScale K₀ v : ℕ) : ℝ) := by
    have h1 : (((bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v)).card : ℕ) : ℝ)
        ≤ 128 * 2 ^ (K₀ + 1) * ((multiScale K₀ v : ℕ) : ℝ) := by
      refine hcount.trans ?_
      rw [multiCount, mul_div_assoc]
      have hp0 : (0 : ℝ) ≤ 64 * 2 ^ (K₀ + 1) := by positivity
      nlinarith [hupper, hp0]
    linarith [h1, hPi]
  have hbthr : (((badStartUnion β K₀ v).card : ℕ) : ℝ)
      * ((((bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v)).card : ℕ) : ℝ)
        + 2 * multiPi K₀ v) ≤ b ^ 2 := by
    have hcoef0 : (0 : ℝ) < 128 * 2 ^ (K₀ + 1) + 2 * multiPiConst K₀ := by
      have := multiPiConst_pos K₀
      positivity
    have hstep : (((badStartUnion β K₀ v).card : ℕ) : ℝ)
        * ((((bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v)).card : ℕ) : ℝ)
          + 2 * multiPi K₀ v)
        ≤ (multiEps K₀ * ((multiScale K₀ v : ℕ) : ℝ))
          * ((128 * 2 ^ (K₀ + 1) + 2 * multiPiConst K₀) * ((multiScale K₀ v : ℕ) : ℝ)) := by
      refine mul_le_mul hbad hsum ?_ (mul_nonneg (multiEps_pos hH).le (by linarith))
      have h0 : (0 : ℝ) ≤ (((bigPrimeSet (multiBase K₀ v)
          (2 ^ (K₀ + 1) * multiBase K₀ v)).card : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    refine hstep.trans ?_
    have hval : (multiEps K₀ * ((multiScale K₀ v : ℕ) : ℝ))
        * ((128 * 2 ^ (K₀ + 1) + 2 * multiPiConst K₀) * ((multiScale K₀ v : ℕ) : ℝ))
        = multiHarmConst K₀ ^ 2 * ((multiScale K₀ v : ℕ) : ℝ) ^ 2 / 16 := by
      rw [multiEps]
      field_simp
    rw [hval]
    have hsq : (multiHarmConst K₀ * ((multiScale K₀ v : ℕ) : ℝ) / 4) ^ 2 ≤ b ^ 2 :=
      pow_le_pow_left₀ (by positivity) hbge 2
    have hval2 : (multiHarmConst K₀ * ((multiScale K₀ v : ℕ) : ℝ) / 4) ^ 2
        = multiHarmConst K₀ ^ 2 * ((multiScale K₀ v : ℕ) : ℝ) ^ 2 / 16 := by ring
    linarith [hsq, hval2]
  -- the sieve hypotheses
  have hlogsift : 20 * mertensFirstConst ≤ Real.log (multiSift K₀ v) := by
    have hs2 : 2 ≤ multiSift K₀ v := by omega
    have := log_multiSift_ge hM2 hbig288 hs2
    linarith [hbig20]
  have hpairle := multi_pair_le (K₀ := K₀) (v := v) (by omega) hs3 hlogsift
  -- the harmonic mass of the good markers
  have hgood := sum_inv_goodMarkers_ge (β := β) (K := multiPairK K₀ v) (Pi := multiPi K₀ v)
    (b := b) hv0 hM0 le_rfl hpairle hbthr hb0
  refine card_sign_window_ge_multi hβ0' hv0 hσ hM0 hXH hC ?_ ?_
  · refine le_trans ?_ hgood
    have hbM : b / ((multiBase K₀ v : ℕ) : ℝ)
        = multiHarmConst K₀ / (2 * Real.log ((multiBase K₀ v : ℕ) : ℝ)) := by
      rw [hb]
      field_simp
    rw [hbM]
    have hhalf : multiHarmConst K₀ / (2 * Real.log ((multiBase K₀ v : ℕ) : ℝ))
        = multiHarmConst K₀ / Real.log ((multiBase K₀ v : ℕ) : ℝ)
          - multiHarmConst K₀ / (2 * Real.log ((multiBase K₀ v : ℕ) : ℝ)) := by
      field_simp
      ring
    rw [hhalf]
    linarith [hharm]
  · refine le_trans ?_ hcount
    exact Nat.cast_le.2 (Finset.card_le_card (Finset.filter_subset _ _))

/-- The cell parameter grows. -/
theorem tendsto_multiCell {β : ℝ} (hβ0 : 0 < β) (K₀ : ℕ) :
    Filter.Tendsto (fun v : ℕ => ((multiCell β K₀ v : ℕ) : ℝ)) atTop atTop := by
  have hev : ∀ C : ℝ, ∀ᶠ v : ℕ in atTop, C ≤ ((multiCell β K₀ v : ℕ) : ℝ) := by
    intro C
    have hgrow : ∀ᶠ y : ℝ in atTop, C ≤ cardLength β y :=
      (tendsto_cardLength hβ0).eventually_ge_atTop C
    filter_upwards [(tendsto_multiBlockScale K₀).eventually hgrow] with v hv
    have hbase : ((multiScale K₀ v : ℕ) : ℝ) ^ 2 = multiBlockScale K₀ v 0 := rfl
    have hceil : cardLength β (multiBlockScale K₀ v 0) ≤ ((multiCell β K₀ v : ℕ) : ℝ) := by
      rw [multiCell, ← hbase] at *
      push_cast
      have := Nat.le_ceil (cardLength β (((multiScale K₀ v : ℕ) : ℝ) ^ 2))
      rw [hbase] at this ⊢
      have hp : (0 : ℝ) ≤ (2 : ℝ) ^ K₀ := by positivity
      linarith
    linarith [hv, hceil]
  exact tendsto_atTop.2 hev

/-- **The sign count in the card's normalisation.** -/
theorem eventually_card_sign_window_ge_const {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (K₀ : ℕ)
    (hH : 0 < multiHarmConst K₀) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    ∀ᶠ v : ℕ in atTop,
      squarefreeDensity * multiHarmConst K₀ / 1024
          * (((multiWindow β K₀ v : ℕ) : ℝ) / Real.log ((multiPhys K₀ v : ℕ) : ℝ))
        ≤ ((((Finset.Ioc (multiPhys K₀ v) (multiPhys K₀ v + multiWindow β K₀ v)).filter
            (fun n => ArithmeticFunction.moebius n = σ)).card : ℕ) : ℝ) := by
  have hβ0' : (0 : ℝ) < β := by linarith
  have hcellbig : ∀ᶠ v : ℕ in atTop,
      128 * 2 ^ (K₀ + 1) / multiHarmConst K₀ ≤ ((multiCell β K₀ v : ℕ) : ℝ) :=
    (tendsto_multiCell hβ0' K₀).eventually_ge_atTop _
  filter_upwards [eventually_card_sign_window_ge hβ0 hβ1 K₀ hH hσ, hcellbig,
    eventually_log_multiBase_ge K₀ 1,
    (tendsto_multiBase K₀).eventually_ge_atTop 2,
    (tendsto_multiScale K₀).eventually_ge_atTop 1] with v hmain hcell hlog1 hM2R hm1
  have hM2 : 2 ≤ multiBase K₀ v := by exact_mod_cast hM2R
  have hM0R : (0 : ℝ) < ((multiBase K₀ v : ℕ) : ℝ) := by linarith
  have hlogM : (0 : ℝ) < Real.log ((multiBase K₀ v : ℕ) : ℝ) := by linarith
  have hmR : (1 : ℝ) ≤ ((multiScale K₀ v : ℕ) : ℝ) := by exact_mod_cast hm1
  have hmM : ((multiScale K₀ v : ℕ) : ℝ) ≤ ((multiBase K₀ v : ℕ) : ℝ) := by
    have hbaseR : ((multiBase K₀ v : ℕ) : ℝ)
        = ((multiScale K₀ v : ℕ) : ℝ) * ((multiFactor K₀ v : ℕ) : ℝ) := by
      rw [multiBase]; push_cast; ring
    have hW1 : (1 : ℝ) ≤ ((multiFactor K₀ v : ℕ) : ℝ) := by
      by_contra hc
      push Not at hc
      have hW0 : multiFactor K₀ v = 0 := by
        have : ((multiFactor K₀ v : ℕ) : ℝ) < 1 := hc
        have : multiFactor K₀ v < 1 := by exact_mod_cast this
        omega
      rw [multiBase, hW0, Nat.mul_zero] at hM2
      omega
    rw [hbaseR]
    nlinarith [hmR, hW1]
  -- the physical scale
  have hXR : ((multiPhys K₀ v : ℕ) : ℝ)
      = ((multiScale K₀ v : ℕ) : ℝ) * ((multiBase K₀ v : ℕ) : ℝ) := by
    rw [multiPhys]; push_cast; ring
  have hX0 : (0 : ℝ) < ((multiPhys K₀ v : ℕ) : ℝ) := by
    rw [hXR]; positivity
  have hlogX : Real.log ((multiPhys K₀ v : ℕ) : ℝ)
      ≤ 2 * Real.log ((multiBase K₀ v : ℕ) : ℝ) := by
    have hsq : ((multiPhys K₀ v : ℕ) : ℝ) ≤ ((multiBase K₀ v : ℕ) : ℝ) ^ 2 := by
      rw [hXR, sq]
      exact mul_le_mul_of_nonneg_right hmM (by linarith)
    have := Real.log_le_log hX0 hsq
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hlogX0 : (0 : ℝ) < Real.log ((multiPhys K₀ v : ℕ) : ℝ) := by
    refine Real.log_pos ?_
    rw [hXR]
    nlinarith [hmR, hM0R, hM2R]
  -- the count term is beaten by half the main term
  have hW0R : (0 : ℝ) ≤ ((multiWindow β K₀ v : ℕ) : ℝ) := Nat.cast_nonneg _
  have hwinR : ((multiWindow β K₀ v : ℕ) : ℝ)
      = 2 * ((multiCell β K₀ v : ℕ) : ℝ) * ((multiBase K₀ v : ℕ) : ℝ) := by
    rw [multiWindow]; push_cast; ring
  have hcnt : multiCount K₀ v
      ≤ ((multiWindow β K₀ v : ℕ) : ℝ) * multiHarmConst K₀
        / (4 * Real.log ((multiBase K₀ v : ℕ) : ℝ)) := by
    rw [multiCount, hwinR, div_le_div_iff₀ hlogM (by positivity)]
    have hcell' : 128 * 2 ^ (K₀ + 1) ≤ ((multiCell β K₀ v : ℕ) : ℝ) * multiHarmConst K₀ := by
      rw [div_le_iff₀ hH] at hcell
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hcell'
      (by positivity : (0:ℝ) ≤ 2 * ((multiBase K₀ v : ℕ) : ℝ)
        * Real.log ((multiBase K₀ v : ℕ) : ℝ))]
  -- assemble
  refine le_trans ?_ hmain
  have hstep : ((multiWindow β K₀ v : ℕ) : ℝ)
        * (multiHarmConst K₀ / (2 * Real.log ((multiBase K₀ v : ℕ) : ℝ))) - multiCount K₀ v
      ≥ ((multiWindow β K₀ v : ℕ) : ℝ) * multiHarmConst K₀
        / (4 * Real.log ((multiBase K₀ v : ℕ) : ℝ)) := by
    have hval : ((multiWindow β K₀ v : ℕ) : ℝ)
          * (multiHarmConst K₀ / (2 * Real.log ((multiBase K₀ v : ℕ) : ℝ)))
        = 2 * (((multiWindow β K₀ v : ℕ) : ℝ) * multiHarmConst K₀
          / (4 * Real.log ((multiBase K₀ v : ℕ) : ℝ))) := by
      field_simp
      ring
    rw [hval]
    linarith [hcnt]
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  have hlogXge : Real.log ((multiBase K₀ v : ℕ) : ℝ)
      ≤ Real.log ((multiPhys K₀ v : ℕ) : ℝ) := by
    refine Real.log_le_log hM0R ?_
    rw [hXR]
    nlinarith [hmR, hM0R]
  have hfinal : squarefreeDensity * multiHarmConst K₀ / 1024
        * (((multiWindow β K₀ v : ℕ) : ℝ) / Real.log ((multiPhys K₀ v : ℕ) : ℝ))
      ≤ squarefreeDensity / 256
        * (((multiWindow β K₀ v : ℕ) : ℝ) * multiHarmConst K₀
          / (4 * Real.log ((multiBase K₀ v : ℕ) : ℝ))) := by
    have hdiv : ((multiWindow β K₀ v : ℕ) : ℝ) / Real.log ((multiPhys K₀ v : ℕ) : ℝ)
        ≤ ((multiWindow β K₀ v : ℕ) : ℝ) / Real.log ((multiBase K₀ v : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hW0R hlogM hlogXge
    have hcoef : (0 : ℝ) ≤ squarefreeDensity * multiHarmConst K₀ / 1024 := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hdiv hcoef) (le_of_eq ?_)
    field_simp
    ring
  refine hfinal.trans ?_
  refine mul_le_mul_of_nonneg_left hstep (by positivity)

/-- The net harmonic constant grows with the number of blocks. -/
theorem tendsto_multiHarmConst : Filter.Tendsto multiHarmConst atTop atTop := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : Filter.Tendsto (fun K₀ : ℕ => ((K₀ : ℝ) + 1) * Real.log 2 / 2)
      atTop atTop := by
    have h1 : Filter.Tendsto (fun K₀ : ℕ => ((K₀ : ℝ) + 1)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have h2 := h1.atTop_mul_const hlog2
    exact h2.atTop_div_const (by norm_num)
  have := hbase.atTop_add (tendsto_const_nhds (x := -(2 * (2 * mertensFirstConst + 1 / 2))))
  refine this.congr fun K₀ => ?_
  rw [multiHarmConst]
  ring

theorem exists_multiHarmConst_ge_multiDevice (C : ℝ) : ∃ K₀ : ℕ, C ≤ multiHarmConst K₀ :=
  (tendsto_multiHarmConst.eventually_ge_atTop C).exists

/-- **For every constant there is a block count realising it.**  This is statement (3) of the
reciprocal-marker Hall card at the constructed scales: the window `(X, X+H]` contains at least
`C·H/log X` integers of either prescribed Möbius sign, for every fixed `C`. -/
theorem exists_eventually_card_sign_window_ge {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (C : ℝ) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ K₀ : ℕ, ∀ᶠ v : ℕ in atTop,
      C * (((multiWindow β K₀ v : ℕ) : ℝ) / Real.log ((multiPhys K₀ v : ℕ) : ℝ))
        ≤ ((((Finset.Ioc (multiPhys K₀ v) (multiPhys K₀ v + multiWindow β K₀ v)).filter
            (fun n => ArithmeticFunction.moebius n = σ)).card : ℕ) : ℝ) := by
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  obtain ⟨K₀, hK₀⟩ := exists_multiHarmConst_ge_multiDevice (max 1 (1024 * C / squarefreeDensity))
  have hH : 0 < multiHarmConst K₀ := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hK₀)
  refine ⟨K₀, ?_⟩
  filter_upwards [eventually_card_sign_window_ge_const hβ0 hβ1 K₀ hH hσ,
    (tendsto_multiScale K₀).eventually_ge_atTop 1,
    (tendsto_multiBase K₀).eventually_ge_atTop 2] with v hv hm1 hM2R
  refine le_trans ?_ hv
  have hmR : (1 : ℝ) ≤ ((multiScale K₀ v : ℕ) : ℝ) := by exact_mod_cast hm1
  have hM0R : (0 : ℝ) < ((multiBase K₀ v : ℕ) : ℝ) := by linarith
  have hXR : ((multiPhys K₀ v : ℕ) : ℝ)
      = ((multiScale K₀ v : ℕ) : ℝ) * ((multiBase K₀ v : ℕ) : ℝ) := by
    rw [multiPhys]; push_cast; ring
  have hX1 : (1 : ℝ) < ((multiPhys K₀ v : ℕ) : ℝ) := by
    rw [hXR]
    nlinarith [hmR, hM0R, hM2R]
  have hlogX0 : (0 : ℝ) < Real.log ((multiPhys K₀ v : ℕ) : ℝ) := Real.log_pos hX1
  have hW0R : (0 : ℝ) ≤ ((multiWindow β K₀ v : ℕ) : ℝ) := Nat.cast_nonneg _
  have hquot : (0 : ℝ) ≤ ((multiWindow β K₀ v : ℕ) : ℝ)
      / Real.log ((multiPhys K₀ v : ℕ) : ℝ) := by positivity
  have hCle : C ≤ squarefreeDensity * multiHarmConst K₀ / 1024 := by
    have hge : 1024 * C / squarefreeDensity ≤ multiHarmConst K₀ :=
      le_trans (le_max_right _ _) hK₀
    rw [div_le_iff₀ hD] at hge
    linarith
  exact mul_le_mul_of_nonneg_right hCle hquot

end

end RHTower.Sieve
