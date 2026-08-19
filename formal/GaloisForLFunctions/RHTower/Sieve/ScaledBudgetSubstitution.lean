import GaloisForLFunctions.RHTower.Sieve.ScaledBudgetGeometry

/-!
# The budget bound at a scaled window

`Sieve/OmegaBudgetMaster.exists_omegaBudget_master` is free in the window `h`, so the corpus's
parameter substitution can be repeated at `h = scaledLength c β x`.  The ladder itself — the sifting
bottom, the step ratio, the number of steps, the ladder top, the smoothing width and the annulus
threshold — keeps its corpus value; only the fibre index range, the Gallagher cut, the expiry height
and the shortest cofactor block move, and the last is taken at the ladder's own top so that the
block condition of the master theorem is inherited from `Sieve/LadderBlockFacts.le_floor_cofactor`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **The window is far below `√x · ladderEta`.**  This is the slack that lets the *unscaled*
shortest cofactor block serve at the scaled index range: shrinking `B₀` by `h` costs less than the
one step of the ladder's own ratio. -/
theorem eventually_cardLength_add_two_le_sqrt_mul_eta {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, cardLength β x + 2 ≤ Real.sqrt x * ladderEta β γ x := by
  have hlim := tendsto_rpow_log_mul_cardLength_div_sqrt (β := β) hβ0 hβ1 (β + 5 / 4 - γ * β)
  filter_upwards [Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1 / 2) hlim,
    (tendsto_cardLength hβ0).eventually_ge_atTop (4 : ℝ),
    Filter.eventually_gt_atTop (1 : ℝ)] with x hsm hh4 hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hpow : (0 : ℝ) < (Real.log x) ^ (β + 5 / 4 - γ * β) := Real.rpow_pos_of_pos hlogx _
  have hη0 : (0 : ℝ) < ladderEta β γ x := Real.rpow_pos_of_pos hlogx _
  have hinv : (Real.log x) ^ (-(β + 5 / 4 - γ * β)) = ladderEta β γ x := by
    rw [ladderEta]
    congr 1
    ring
  have hcomb : (Real.log x) ^ (β + 5 / 4 - γ * β) * (Real.log x) ^ (-(β + 5 / 4 - γ * β)) = 1 := by
    rw [← Real.rpow_add hlogx]
    simp
  have hpi : (0 : ℝ) < (Real.log x) ^ (-(β + 5 / 4 - γ * β)) := Real.rpow_pos_of_pos hlogx _
  have hmul := mul_le_mul_of_nonneg_right hsm hpi.le
  have hlhs : (Real.log x) ^ (β + 5 / 4 - γ * β) * (cardLength β x / Real.sqrt x)
      * (Real.log x) ^ (-(β + 5 / 4 - γ * β)) = cardLength β x / Real.sqrt x := by
    calc (Real.log x) ^ (β + 5 / 4 - γ * β) * (cardLength β x / Real.sqrt x)
          * (Real.log x) ^ (-(β + 5 / 4 - γ * β))
        = (cardLength β x / Real.sqrt x)
            * ((Real.log x) ^ (β + 5 / 4 - γ * β) * (Real.log x) ^ (-(β + 5 / 4 - γ * β))) := by
          ring
      _ = cardLength β x / Real.sqrt x := by rw [hcomb, mul_one]
  rw [hlhs, hinv] at hmul
  rw [div_le_iff₀ hsx] at hmul
  nlinarith [hmul, hh4, hη0, hsx]

/-- **The unscaled shortest block still fits every scaled ladder step.** -/
theorem budgetNmin_le_floor_cofactorS {c β γ x : ℝ} (hc0 : 0 < c)
    (hx1 : 1 < x) (hη1 : ladderEta β γ x ≤ 1)
    (hslack : cardLength β x + 2 ≤ Real.sqrt x * ladderEta β γ x)
    (hQ0 : (0 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ))
    (hple : ((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ (ladderSteps β γ x)
      ≤ cardLength β x)
    {j : ℕ} (hj : j < ladderSteps β γ x) :
    budgetNmin β x ≤ ((⌊((budgetBS c β x : ℕ) : ℝ)
      / (((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ j)⌋₊ : ℕ) : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hs0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
  have hη0 : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hr1 : (1 : ℝ) ≤ 1 + ladderEta β γ x := by linarith
  have hbase : (0 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ j := by
    positivity
  -- the step is below the window divided by the ratio
  have hstepj : ((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ j
      * (1 + ladderEta β γ x) ≤ cardLength β x := by
    have hmono : (1 + ladderEta β γ x) ^ (j + 1)
        ≤ (1 + ladderEta β γ x) ^ (ladderSteps β γ x) := pow_le_pow_right₀ hr1 hj
    have := mul_le_mul_of_nonneg_left hmono hQ0.le
    calc ((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ j
          * (1 + ladderEta β γ x)
        = ((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ (j + 1) := by ring
      _ ≤ ((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ (ladderSteps β γ x) := this
      _ ≤ cardLength β x := hple
  -- the scaled index range, enlarged by the ratio, dominates the unscaled one
  have hBS : Real.sqrt x - 1 ≤ ((budgetBS c β x : ℕ) : ℝ) := by
    have := budgetBS_ge c β x
    linarith [hs0.le]
  have hB : ((budgetB β x : ℕ) : ℝ) ≤ Real.sqrt x + cardLength β x := by
    rw [budgetB]
    exact Nat.floor_le (by positivity)
  have hkey : gallagherCut β x
      ≤ ((budgetBS c β x : ℕ) : ℝ)
        / (((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ j) := by
    have hlow : ((budgetBS c β x : ℕ) : ℝ) * (1 + ladderEta β γ x) / cardLength β x
        ≤ ((budgetBS c β x : ℕ) : ℝ)
          / (((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ j) := by
      rw [div_le_div_iff₀ hh0 hbase]
      have hBS0 : (0 : ℝ) ≤ ((budgetBS c β x : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hstepj, hBS0]
    refine le_trans ?_ hlow
    have ha : Real.sqrt x + cardLength β x
        ≤ (Real.sqrt x - 1) * (1 + ladderEta β γ x) := by nlinarith [hslack, hη1, hη0]
    have hb : (Real.sqrt x - 1) * (1 + ladderEta β γ x)
        ≤ ((budgetBS c β x : ℕ) : ℝ) * (1 + ladderEta β γ x) :=
      mul_le_mul_of_nonneg_right hBS (by linarith)
    have hstep2 : ((budgetB β x : ℕ) : ℝ)
        ≤ ((budgetBS c β x : ℕ) : ℝ) * (1 + ladderEta β γ x) := le_trans hB (le_trans ha hb)
    rw [gallagherCut, div_le_div_iff₀ hh0 hh0]
    have hid : ((⌊Real.sqrt x + cardLength β x⌋₊ : ℕ) : ℝ) = ((budgetB β x : ℕ) : ℝ) := rfl
    rw [hid]
    exact mul_le_mul_of_nonneg_right hstep2 hh0.le
  rw [budgetNmin]
  exact_mod_cast Nat.floor_mono hkey

/-- **Every side condition of the master budget theorem holds at the scaled window.** -/
theorem exists_eventually_omegaBudgetS_le {c β γ : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ : γ * β < 1) :
    ∃ (A delta Ctot : ℝ), 0 < delta ∧ 0 < Ctot ∧
      ∀ᶠ x : ℝ in atTop,
        omegaBudget x (scaledLength c β x) (siftStart (γ * β) x) (ladderTop β γ x)
          ≤ 16 * Real.sqrt x
              * (2 * (fibreWidth x (scaledLength c β x)) ^ 2
                  * (ladderAffineSlope (ladderSteps β γ x) (budgetBS c β x)
                        ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
                        (budgetRho A delta Ctot β γ x) * gallagherCutS c β x
                    + ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x)
                        (ladderSteps β γ x) (budgetBS c β x) ((siftStart (γ * β) x : ℕ) : ℝ)
                        (ladderEta β γ x) (budgetRho A delta Ctot β γ x) (budgetS β x)
                        (annulusStart β x))
                + (4 * (ladderAffineSlope (ladderSteps β γ x) (budgetBS c β x)
                          ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
                          (budgetRho A delta Ctot β γ x)
                        + 5 * Real.pi / 2
                          * (∑ n ∈ Finset.Icc 1 (budgetBS c β x),
                              ‖omegaCoeff (primesRange (siftStart (γ * β) x)
                                (ladderTop β γ x)) n‖ ^ 2)
                        + 5 * Real.exp 1 / 2 * ((budgetBS c β x : ℕ) : ℝ)
                          * (∑ n ∈ Finset.Icc 1 (budgetBS c β x),
                              ‖omegaCoeff (primesRange (siftStart (γ * β) x)
                                (ladderTop β γ x)) n‖ ^ 2) / budgetT β x)
                      / (Real.pi ^ 2 * gallagherCutS c β x)
                    + 4 * ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x)
                          (ladderSteps β γ x) (budgetBS c β x) ((siftStart (γ * β) x : ℕ) : ℝ)
                          (ladderEta β γ x) (budgetRho A delta Ctot β γ x) (budgetS β x)
                          (annulusStart β x)
                      / (3 * Real.pi ^ 2 * (gallagherCutS c β x) ^ 2)))
            + 204 * (((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ) + 1) ^ 2
                * (Real.sqrt x + 1)
            + 2 * (scaledLength c β x + 1) * (2 * scaledLength c β x + 1)
                * (4 * (Real.sqrt x / 2 + scaledLength c β x + 1) * mertensS (ladderTop β γ x)
                  + 4 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ)
                  + 8 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ^ 2) := by
  obtain ⟨A, delta, Ctot, τ₀, K₀, N₁, hdelta, hCtot, hτ₀, hmaster⟩ := exists_omegaBudget_master
  refine ⟨A, delta, Ctot, hdelta, hCtot, ?_⟩
  have hab : (0 : ℝ) < γ * β := mul_pos hγ0 hβ0
  have hzero := tendsto_ladderEta (β := β) (γ := γ) hβ0 hγβ
  have hpolylog : Tendsto (fun x : ℝ => 2 * Real.pi * annulusStart β x) atTop atTop := by
    have h : Tendsto (fun x : ℝ => annulusStart β x) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < (13:ℝ))).comp Real.tendsto_log_atTop
    exact Filter.Tendsto.const_mul_atTop (by positivity) h
  filter_upwards [one_le_gallagherCutS hc0 hc1 hβ0 hβ1, gallagherCutS_le_budgetT hc0 hc1 hβ0,
    annulusStart_le_gallagherCutS hc0 hc1 hβ0 hβ1,
    (tendsto_scaledLength hc0 hβ0).eventually_ge_atTop (1 : ℝ),
    scaledLength_le_sqrt hc1 hβ0 hβ1, Filter.eventually_gt_atTop (1 : ℝ),
    eventually_le_siftStart hab 2, one_le_ladderWidth hβ0,
    one_le_ladderSteps hβ0 hγ0 hγ1 hγβ,
    eventually_siftStart_lt_cardLength hβ0 hγ0 hγ1,
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) hzero,
    hpolylog.eventually_ge_atTop (max τ₀ (16 * Real.pi / 3)),
    eventually_contourParam_budgetNmin hβ0 hβ1 (K₀ : ℝ),
    (tendsto_budgetNmin hβ0 hβ1).eventually_ge_atTop N₁,
    eventually_annulus_admissible hβ0 hβ1,
    one_le_gallagherCut hβ0 hβ1,
    eventually_cardLength_add_two_le_sqrt_mul_eta (γ := γ) hβ0 hβ1]
    with x hG1 hGT hwG hh1 hhs hx1 hQ2 hD1 hL1 h2Q hη1 hw₀τ hCP hN₁ hadm hGu1 hslack
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hh0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
  have hcl0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hQR2 : (2 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ2
  have hQ0 : (0 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ) := by linarith
  have hQ1R : (1 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by linarith
  have hz₀1 : 1 ≤ siftStart (γ * β) x := by omega
  have hη0 : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hQh : ((siftStart (γ * β) x : ℕ) : ℝ) ≤ cardLength β x := by linarith
  have hple := ladderPow_le hQ1R hQh hη0
  have hδpos : 0 < fibreWidth x (scaledLength c β x) := by
    rw [fibreWidth]
    refine Real.log_pos ?_
    have : (0 : ℝ) < scaledLength c β x / Real.sqrt x := by positivity
    linarith
  have hB0 : (0 : ℝ) < ((budgetBS c β x : ℕ) : ℝ) := by
    have h1 : 1 ≤ budgetBS c β x := by
      rw [budgetBS]
      exact Nat.le_floor (by push_cast; linarith [hsx.le, hh1])
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
  have hlogh : Real.log (cardLength β x) = (Real.log x) ^ β := log_cardLength β x
  have hLxj : ∀ j ∈ Finset.range (ladderSteps β γ x),
      Real.log (max ((⌊((siftStart (γ * β) x : ℕ) : ℝ)
        * (1 + ladderEta β γ x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) ≤ (Real.log x) ^ β := by
    intro j hj
    have hjL : j + 1 ≤ ladderSteps β γ x := Finset.mem_range.1 hj
    have hb := max_ladderBlock_le hQ0 hη0.le hjL hple (by linarith)
    have hmax0 : (0 : ℝ) < max ((⌊((siftStart (γ * β) x : ℕ) : ℝ)
        * (1 + ladderEta β γ x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1 :=
      lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have := Real.log_le_log hmax0 hb
    rwa [hlogh] at this
  have hqj : ∀ j ∈ Finset.range (ladderSteps β γ x),
      Real.log ((siftStart (γ * β) x : ℕ) : ℝ)
        ≤ Real.log (max ((⌊((siftStart (γ * β) x : ℕ) : ℝ)
            * (1 + ladderEta β γ x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) := by
    intro j _
    exact Real.log_le_log hQ0 (le_max_ladderBlock rfl hη0.le hz₀1 j)
  have hxminj : ∀ j ∈ Finset.range (ladderSteps β γ x),
      ((siftStart (γ * β) x : ℕ) : ℝ)
        ≤ max ((⌊((siftStart (γ * β) x : ℕ) : ℝ)
            * (1 + ladderEta β γ x) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1 := fun j _ =>
    le_max_ladderBlock rfl hη0.le hz₀1 j
  have hNj : ∀ j ∈ Finset.range (ladderSteps β γ x),
      budgetNmin β x ≤ ((⌊((budgetBS c β x : ℕ) : ℝ)
        / (((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ j)⌋₊ : ℕ) : ℝ) := by
    intro j hj
    exact budgetNmin_le_floor_cofactorS hc0 hx1 hη1 hslack hQ0 hple (Finset.mem_range.1 hj)
  have hNmin1 : (1 : ℝ) ≤ budgetNmin β x := by
    rw [budgetNmin]
    have : 1 ≤ ⌊gallagherCut β x⌋₊ := Nat.le_floor (by exact_mod_cast hGu1)
    exact_mod_cast this
  have hK : K₀ ≤ contourParam (budgetNmin β x) := by exact_mod_cast hCP
  have hμ0 : (0 : ℝ) ≤ budgetMu A delta β x := by
    rw [budgetMu]
    have h1 : (0 : ℝ) < routeTWidthPolylogLower A (2 * Real.pi * budgetT β x) :=
      routeTWidthPolylogLower_pos _ _
    have : (0 : ℝ) ≤ min delta (routeTWidthPolylogLower A (2 * Real.pi * budgetT β x)) :=
      le_min hdelta.le h1.le
    linarith
  have hw₀0 : (0 : ℝ) ≤ annulusStart β x := by
    rw [annulusStart]
    exact Real.rpow_nonneg (Real.log_nonneg hx1.le) _
  exact hmaster x (scaledLength c β x) (siftStart (γ * β) x) (ladderTop β γ x)
    (ladderSteps β γ x) (budgetBS c β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
    (ladderWidth β x) (annulusStart β x) (budgetT β x) (gallagherCutS c β x)
    ((Real.log x) ^ β) (Real.log ((siftStart (γ * β) x : ℕ) : ℝ)) (budgetMu A delta β x)
    ((siftStart (γ * β) x : ℕ) : ℝ) (budgetHmaj A β x) (budgetNmin β x)
    hδpos rfl hB0 hz₀1 rfl (by linarith) hη0 hL1 rfl hG1 hGT hw₀0 hwG hD1 hw₀τ
    (Real.rpow_nonneg (Real.log_nonneg hx1.le) β) hLxj (Real.log_nonneg hQ1R) hqj hμ0 le_rfl
    hQ0 hxminj le_rfl
    hNmin1 hN₁ hNj hK hadm

end

end RHTower.Sieve
