import GaloisForLFunctions.RHTower.Sieve.SpectralParameters
import GaloisForLFunctions.RHTower.Sieve.OmegaSpectralFibre
import GaloisForLFunctions.RHTower.Sieve.SiftingDepth

/-!
# The non-spectral part of the Route E budget

Two of the three parts of the budget carry no Dirichlet polynomial: the rounding cost of the
rescaled fibre bridge and the Turán--Kubilius variance.  Both are `O(1/W²)` after normalisation, so
they vanish as soon as the harmonic mass of the designated range grows.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **The non-spectral part of the budget, normalised.** -/
theorem nonSpectral_div_le {h s W m P Z : ℝ}
    (hh1 : 1 ≤ h) (hhs : h ≤ s) (hs1 : 1 ≤ s) (hW1 : 1 ≤ W)
    (hP0 : 0 ≤ P) (hP : P ≤ 2 * h) (hZ0 : 0 ≤ Z) (hZ : Z ≤ 2 * h) (hm0 : 0 ≤ m) :
    (204 * (P + 1) ^ 2 * (s + 1) + 2 * (h + 1) * (2 * h + 1) * (4 * (s / 2 + h + 1) * m
        + 4 * Z + 8 * Z ^ 2)) / (W ^ 2 * h ^ 2 * s)
      ≤ 3672 / W ^ 2 + 120 * m / W ^ 2 + 480 * h ^ 2 / (W ^ 2 * s) := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hden : (0 : ℝ) < W ^ 2 * h ^ 2 * s := by positivity
  have hA : 204 * (P + 1) ^ 2 * (s + 1) ≤ 3672 * (h ^ 2 * s) := by
    have h1 : (P + 1) ^ 2 ≤ 9 * h ^ 2 := by nlinarith [hP, hP0, hh1]
    have h2 : s + 1 ≤ 2 * s := by linarith
    nlinarith [h1, h2, hs0, hh0]
  have hBfac : 2 * (h + 1) * (2 * h + 1) ≤ 12 * h ^ 2 := by nlinarith [hh1]
  have hBin : 4 * (s / 2 + h + 1) * m + 4 * Z + 8 * Z ^ 2 ≤ 10 * s * m + 40 * h ^ 2 := by
    have h1 : 4 * (s / 2 + h + 1) * m ≤ 10 * s * m := by nlinarith [hm0, hhs, hs1, hh1]
    have h2 : 4 * Z + 8 * Z ^ 2 ≤ 40 * h ^ 2 := by nlinarith [hZ, hZ0, hh1]
    linarith
  have hBin0 : (0 : ℝ) ≤ 4 * (s / 2 + h + 1) * m + 4 * Z + 8 * Z ^ 2 := by
    have h1 : (0 : ℝ) ≤ 4 * (s / 2 + h + 1) * m := by
      have : (0 : ℝ) ≤ 4 * (s / 2 + h + 1) := by linarith
      exact mul_nonneg this hm0
    nlinarith [h1, hZ0]
  have hB : 2 * (h + 1) * (2 * h + 1) * (4 * (s / 2 + h + 1) * m + 4 * Z + 8 * Z ^ 2)
      ≤ 12 * h ^ 2 * (10 * s * m + 40 * h ^ 2) := by
    have hf0 : (0 : ℝ) ≤ 2 * (h + 1) * (2 * h + 1) := by nlinarith [hh0]
    nlinarith [hBfac, hBin, hBin0, hf0]
  have hnum : 204 * (P + 1) ^ 2 * (s + 1) + 2 * (h + 1) * (2 * h + 1)
      * (4 * (s / 2 + h + 1) * m + 4 * Z + 8 * Z ^ 2)
      ≤ 3672 * (h ^ 2 * s) + 12 * h ^ 2 * (10 * s * m + 40 * h ^ 2) := by linarith
  have hstep : (204 * (P + 1) ^ 2 * (s + 1) + 2 * (h + 1) * (2 * h + 1)
        * (4 * (s / 2 + h + 1) * m + 4 * Z + 8 * Z ^ 2)) / (W ^ 2 * h ^ 2 * s)
      ≤ (3672 * (h ^ 2 * s) + 12 * h ^ 2 * (10 * s * m + 40 * h ^ 2)) / (W ^ 2 * h ^ 2 * s) :=
    (div_le_div_iff_of_pos_right hden).mpr hnum
  refine hstep.trans (le_of_eq ?_)
  field_simp
  ring

/-- The prime counting function is at most the cutoff. -/
theorem card_primesLE_le (z : ℕ) : ((Nat.primesLE z).card : ℝ) ≤ (z : ℝ) + 1 := by
  classical
  have hsub : Nat.primesLE z ⊆ Finset.range (z + 1) := by
    intro p hp
    rw [mem_primesLE] at hp
    exact Finset.mem_range.2 (by omega)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_range] at hc
  have : ((Nat.primesLE z).card : ℝ) ≤ ((z + 1 : ℕ) : ℝ) := by exact_mod_cast hc
  push_cast at this
  linarith

theorem card_primesRange_le (z₀ z : ℕ) : ((primesRange z₀ z).card : ℝ) ≤ (z : ℝ) + 1 := by
  classical
  have hsub : primesRange z₀ z ⊆ Nat.primesLE z := Finset.sdiff_subset
  have hc := Finset.card_le_card hsub
  have : ((primesRange z₀ z).card : ℝ) ≤ ((Nat.primesLE z).card : ℝ) := by exact_mod_cast hc
  linarith [card_primesLE_le z]

/-- **The window length squared is negligible against the outer scale.** -/
theorem tendsto_cardLength_sq_div_sqrt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ => (cardLength β x) ^ 2 / Real.sqrt x) atTop (𝓝 0) := by
  have hδ : (0 : ℝ) < 1 - β := by linarith
  have hsmall := tendsto_log_rpow_neg hδ
  have hmaj : Tendsto (fun x : ℝ => Real.exp (-(Real.log x / 4))) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun x : ℝ => Real.log x / 4) atTop atTop :=
      Real.tendsto_log_atTop.atTop_div_const (by norm_num)
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have := Real.sqrt_pos.2 hx
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1 / 8) hsmall] with x hx1 hsm
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hpow0 : (0 : ℝ) < (Real.log x) ^ β := Real.rpow_pos_of_pos hlogx _
    have hkey : 2 * (Real.log x) ^ β ≤ Real.log x / 4 := by
      have hid : (Real.log x) ^ (-(1 - β)) * Real.log x = (Real.log x) ^ β := by
        rw [show -(1 - β) = β + -1 by ring, Real.rpow_add hlogx, Real.rpow_neg_one]
        field_simp
      have h1 : (Real.log x) ^ (-(1 - β)) * Real.log x ≤ 1 / 8 * Real.log x :=
        mul_le_mul_of_nonneg_right hsm hlogx.le
      rw [hid] at h1
      linarith
    have hsq : (cardLength β x) ^ 2 = Real.exp (2 * (Real.log x) ^ β) := by
      rw [cardLength, ← Real.exp_nat_mul]
      norm_num
    have hsx : Real.sqrt x = Real.exp (Real.log x / 2) := by
      have hl : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
      rw [← hl, Real.exp_log (Real.sqrt_pos.2 hx0)]
    rw [hsq, hsx, ← Real.exp_sub]
    exact Real.exp_le_exp.2 (by linarith)

set_option maxHeartbeats 1000000 in
/-- **The non-spectral part of the Route E budget vanishes.** -/
theorem tendsto_nonSpectralBudget {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hγβ : γ * β < 1) :
    Tendsto (fun x : ℝ =>
        (204 * (((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ) + 1) ^ 2
              * (Real.sqrt x + 1)
            + 2 * (cardLength β x + 1) * (2 * cardLength β x + 1)
              * (4 * (Real.sqrt x / 2 + cardLength β x + 1) * mertensS (ladderTop β γ x)
                + 4 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ)
                + 8 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ^ 2))
          / ((mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2
            * (cardLength β x) ^ 2 * Real.sqrt x)) atTop (𝓝 0) := by
  set c : ℝ := (β - γ * β) / 2 with hc
  have hc0 : (0 : ℝ) < c := by
    rw [hc]
    nlinarith
  set Cabs : ℝ := |mertensUpperConst| with hCabs
  have hCabs0 : (0 : ℝ) ≤ Cabs := abs_nonneg _
  have hCle : mertensUpperConst ≤ Cabs := le_abs_self _
  have hLL : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hLLc : Tendsto (fun x : ℝ => c ^ 2 * Real.log (Real.log x)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hLL
  have hmaj : Tendsto (fun x : ℝ =>
      (3672 + 120 * (β + Cabs)) / (c ^ 2 * Real.log (Real.log x))
        + 480 * ((cardLength β x) ^ 2 / Real.sqrt x)) atTop (𝓝 0) := by
    have t1 := hLLc.const_div_atTop (3672 + 120 * (β + Cabs))
    have t2 := (tendsto_cardLength_sq_div_sqrt hβ0 hβ1).const_mul (480 : ℝ)
    have h := t1.add t2
    simpa using h
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [(tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
      Filter.eventually_gt_atTop (1 : ℝ)] with x hh1 hx1
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hm0 : (0 : ℝ) ≤ mertensS (ladderTop β γ x) := mertensS_nonneg _
    have hp0 : (0 : ℝ) ≤ ((Nat.primesLE (ladderTop β γ x)).card : ℝ) := Nat.cast_nonneg _
    have hnum : (0 : ℝ)
        ≤ 204 * (((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ) + 1) ^ 2
              * (Real.sqrt x + 1)
            + 2 * (cardLength β x + 1) * (2 * cardLength β x + 1)
              * (4 * (Real.sqrt x / 2 + cardLength β x + 1) * mertensS (ladderTop β γ x)
                + 4 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ)
                + 8 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ^ 2) := by
      have h1 : (0 : ℝ) ≤ 204 * (((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ)
            + 1) ^ 2 * (Real.sqrt x + 1) := by positivity
      have h2 : (0 : ℝ) ≤ 4 * (Real.sqrt x / 2 + cardLength β x + 1)
          * mertensS (ladderTop β γ x) := by positivity
      have h3 : (0 : ℝ) ≤ 2 * (cardLength β x + 1) * (2 * cardLength β x + 1) := by positivity
      nlinarith [h1, h2, h3, hp0]
    positivity
  · filter_upwards [(tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
      cardLength_le_sqrt hβ0 hβ1, Filter.eventually_gt_atTop (1 : ℝ),
      eventually_ladderTop_facts hβ0 hγ0 hγ1 hγβ,
      ladderMass_lower hβ0 hγ0 hγ1 hγβ,
      Tendsto.eventually_ge_atTop hLL (1 : ℝ),
      Tendsto.eventually_ge_atTop hLL ((2 * Real.log 2 - ladderMassConst + 1) / c)]
      with x hh1 hhs hx1 htop hmass hLL1 hLLbig
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hs1 : (1 : ℝ) ≤ Real.sqrt x := le_trans hh1 hhs
    set LL : ℝ := Real.log (Real.log x) with hLLdef
    set W : ℝ := mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x) with hWdef
    have hcLL : 2 * Real.log 2 - ladderMassConst + 1 ≤ c * LL := by
      rw [div_le_iff₀ hc0] at hLLbig
      linarith [hLLbig]
    have hWc : c * LL + 1 ≤ W := by
      have h2c : β - γ * β = 2 * c := by rw [hc]; ring
      rw [h2c] at hmass
      linarith [hmass, hcLL]
    have hcLL0 : (0 : ℝ) ≤ c * LL := by positivity
    have hW1 : (1 : ℝ) ≤ W := by linarith
    have hW0 : (0 : ℝ) < W := by linarith
    -- the two counting bounds
    have htoph : ((ladderTop β γ x : ℕ) : ℝ) ≤ cardLength β x := htop.2.1
    have hZ : ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ≤ 2 * cardLength β x := by
      have := card_primesLE_le (ladderTop β γ x)
      linarith
    have hP : (((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ))
        ≤ 2 * cardLength β x := by
      have := card_primesRange_le (siftStart (γ * β) x) (ladderTop β γ x)
      linarith
    have hm0 : (0 : ℝ) ≤ mertensS (ladderTop β γ x) := mertensS_nonneg _
    -- Mertens upper bound
    have htop2 : 2 ≤ ladderTop β γ x := htop.1
    have htopR : (2 : ℝ) ≤ ((ladderTop β γ x : ℕ) : ℝ) := by exact_mod_cast htop2
    have hlogtop : (0 : ℝ) < Real.log ((ladderTop β γ x : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hlogle : Real.log ((ladderTop β γ x : ℕ) : ℝ) ≤ (Real.log x) ^ β := by
      have := Real.log_le_log (by linarith) htoph
      rwa [log_cardLength] at this
    have hmm : mertensS (ladderTop β γ x) ≤ β * LL + Cabs := by
      have h1 := mertensS_le_logLog_add htop2
      rw [logLog] at h1
      have h2 : Real.log (Real.log ((ladderTop β γ x : ℕ) : ℝ)) ≤ Real.log ((Real.log x) ^ β) :=
        Real.log_le_log hlogtop hlogle
      rw [Real.log_rpow hlogx, ← hLLdef] at h2
      linarith [h1, h2, hCle]
    have hmLL : mertensS (ladderTop β γ x) ≤ (β + Cabs) * LL := by
      nlinarith [hmm, hLL1, hCabs0]
    -- the arithmetic bound
    have hbase := nonSpectral_div_le (h := cardLength β x) (s := Real.sqrt x) (W := W)
      (m := mertensS (ladderTop β γ x))
      (P := ((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ))
      (Z := ((Nat.primesLE (ladderTop β γ x)).card : ℝ))
      hh1 hhs hs1 hW1 (Nat.cast_nonneg _) hP (Nat.cast_nonneg _) hZ hm0
    refine hbase.trans ?_
    have hWsq2 : c ^ 2 * LL ^ 2 ≤ W ^ 2 := by nlinarith [hWc, hcLL0]
    have hWsq : c ^ 2 * LL ≤ W ^ 2 := by
      have h1 : c ^ 2 * LL ≤ c ^ 2 * LL ^ 2 := by
        have hkey : (0 : ℝ) ≤ c ^ 2 * LL * (LL - 1) :=
          mul_nonneg (mul_nonneg (sq_nonneg c) (by linarith)) (by linarith)
        nlinarith [hkey]
      linarith
    have hcLLpos : (0 : ℝ) < c ^ 2 * LL := by positivity
    have hcLLpos2 : (0 : ℝ) < c ^ 2 * LL ^ 2 := by positivity
    have hA : 3672 / W ^ 2 ≤ 3672 / (c ^ 2 * LL) :=
      div_le_div_of_nonneg_left (by norm_num) hcLLpos hWsq
    have hB : 120 * mertensS (ladderTop β γ x) / W ^ 2
        ≤ 120 * (β + Cabs) / (c ^ 2 * LL) := by
      have hnum : 120 * mertensS (ladderTop β γ x) ≤ 120 * ((β + Cabs) * LL) := by linarith [hmLL]
      have hstep : 120 * mertensS (ladderTop β γ x) / W ^ 2
          ≤ 120 * ((β + Cabs) * LL) / (c ^ 2 * LL ^ 2) :=
        div_le_div₀ (by
          have h0 : (0 : ℝ) ≤ (β + Cabs) * LL := mul_nonneg (by linarith) (by linarith)
          linarith) hnum hcLLpos2 hWsq2
      refine hstep.trans (le_of_eq ?_)
      have hLLne : LL ≠ 0 := by linarith
      field_simp
    have hC : 480 * (cardLength β x) ^ 2 / (W ^ 2 * Real.sqrt x)
        ≤ 480 * ((cardLength β x) ^ 2 / Real.sqrt x) := by
      have hW2 : (1 : ℝ) ≤ W ^ 2 := by nlinarith [hW1]
      have hden : (0 : ℝ) < W ^ 2 * Real.sqrt x := by positivity
      rw [div_le_iff₀ hden]
      have hq : (0 : ℝ) ≤ 480 * (cardLength β x) ^ 2 / Real.sqrt x := by positivity
      have hid : 480 * ((cardLength β x) ^ 2 / Real.sqrt x) * (W ^ 2 * Real.sqrt x)
          = 480 * (cardLength β x) ^ 2 * W ^ 2 := by
        field_simp
      rw [hid]
      nlinarith [hW2, sq_nonneg (cardLength β x)]
    have hsplit : (3672 + 120 * (β + Cabs)) / (c ^ 2 * LL)
        = 3672 / (c ^ 2 * LL) + 120 * (β + Cabs) / (c ^ 2 * LL) := by
      field_simp
    rw [hsplit]
    linarith [hA, hB, hC]

end

end RHTower.Sieve