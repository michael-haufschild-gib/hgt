import GaloisForLFunctions.RHTower.Sieve.RhoLimitPieces

/-!
# The annulus constant times the number of steps vanishes

This is the one condition the spectral limit needs from the analytic side.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The majorant of the annulus constant times the number of steps. -/
def rhoMajorant (A Ctot β γ x : ℝ) : ℝ :=
  (4 / Real.log 2)
    * (2 * (512 * Ctot / 36 * (Real.log x) ^ (12 * β + 5 / 4 - γ * β - 13)
        + 512 * Ctot * (1 + 40 * routeTZeroFreeDeltaEnvelopeConstant A) / 6
            * ((Real.log x) ^ (10 * β + 13 / 4 - γ * β)
              * Real.exp (-((Real.log x) ^ ((γ * β - 9 / 10) / 4))))
        + 512 * Ctot * (1 + 40 * routeTZeroFreeDeltaEnvelopeConstant A) / 216
            * (Real.log x) ^ (10 * β + 13 / 4 - γ * β - 26)
        + 4 * (Real.log x) ^ (5 / 4 - β - γ * β)
        + 4 * ((Real.log x) ^ (3 * β + 5 / 4 - γ * β)
            * Real.exp (-((Real.log x) ^ (γ * β) / 2))))
      + 14 * Real.exp 9
        * ((Real.log x) ^ (2 * β + 5 / 4 - γ * β) * Real.exp (-((Real.log x) ^ (γ * β)))))

/-- **The majorant vanishes.** -/
theorem tendsto_rhoMajorant {A Ctot β γ : ℝ} (hβ0 : 9 / 10 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγβ0 : 9 / 10 < γ * β) (hγβ1 : γ * β < 1) :
    Tendsto (fun x : ℝ => rhoMajorant A Ctot β γ x) atTop (𝓝 0) := by
  have ha1 : 12 * β + 5 / 4 - γ * β - 13 < 0 := by nlinarith
  have ha3 : 10 * β + 13 / 4 - γ * β - 26 < 0 := by nlinarith
  have ha4 : 5 / 4 - β - γ * β < 0 := by nlinarith
  have hε : (0 : ℝ) < (γ * β - 9 / 10) / 4 := by linarith
  have hγβpos : (0 : ℝ) < γ * β := by linarith
  have t1 := (tendsto_rpow_log_of_neg ha1).const_mul (512 * Ctot / 36)
  have t2 := (tendsto_rpow_log_mul_exp_neg (c := 10 * β + 13 / 4 - γ * β)
      (a := (γ * β - 9 / 10) / 4) hε).const_mul
    (512 * Ctot * (1 + 40 * routeTZeroFreeDeltaEnvelopeConstant A) / 6)
  have t3 := (tendsto_rpow_log_of_neg ha3).const_mul
    (512 * Ctot * (1 + 40 * routeTZeroFreeDeltaEnvelopeConstant A) / 216)
  have t4 := (tendsto_rpow_log_of_neg ha4).const_mul (4 : ℝ)
  have hhalf : Tendsto (fun x : ℝ => (Real.log x) ^ (3 * β + 5 / 4 - γ * β)
      * Real.exp (-((Real.log x) ^ (γ * β) / 2))) atTop (𝓝 0) := by
    have h := tendsto_rpow_log_mul_exp_neg (c := 3 * β + 5 / 4 - γ * β)
      (a := γ * β / 2) (by linarith)
    refine squeeze_zero' ?_ ?_ h
    · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
      have := Real.log_pos hx1
      positivity
    · have hpowbig : Tendsto (fun x : ℝ => (Real.log x) ^ (γ * β / 2)) atTop atTop :=
        (tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop
      filter_upwards [Filter.eventually_ge_atTop (Real.exp 1),
        hpowbig.eventually_ge_atTop (2 : ℝ)] with x hxe hbig2
      have hx1 : (1 : ℝ) < x := by
        have h1 : (1 : ℝ) < Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ)
          linarith
        linarith
      have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
      have hlog1 : (1 : ℝ) ≤ Real.log x := by
        have := Real.log_le_log (Real.exp_pos 1) hxe
        rwa [Real.log_exp] at this
      have hpow : (Real.log x) ^ (γ * β / 2) ≤ (Real.log x) ^ (γ * β) / 2 := by
        have hsplit : (Real.log x) ^ (γ * β) = (Real.log x) ^ (γ * β / 2)
            * (Real.log x) ^ (γ * β / 2) := by
          rw [← Real.rpow_add hlogx]
          congr 1
          ring
        nlinarith [hsplit, hbig2]
      have hexp : Real.exp (-((Real.log x) ^ (γ * β) / 2))
          ≤ Real.exp (-((Real.log x) ^ (γ * β / 2))) := Real.exp_le_exp.2 (by linarith)
      have hp0 : (0 : ℝ) ≤ (Real.log x) ^ (3 * β + 5 / 4 - γ * β) := Real.rpow_nonneg hlogx.le _
      exact mul_le_mul_of_nonneg_left hexp hp0
  have t5 := hhalf.const_mul (4 : ℝ)
  have t6 := (tendsto_rpow_log_mul_exp_neg (c := 2 * β + 5 / 4 - γ * β)
      (a := γ * β) hγβpos).const_mul (14 * Real.exp 9)
  have hsum := ((((t1.add t2).add t3).add t4).add t5)
  have hfin := (hsum.const_mul (2 : ℝ)).add t6
  have hlast := hfin.const_mul (4 / Real.log 2)
  simpa [rhoMajorant] using hlast

/-- Combining powers of a fixed positive base. -/
theorem rpow_comb {t a b c d : ℝ} (ht : 0 < t) :
    t ^ a * t ^ b * t ^ c / t ^ d = t ^ (a + b + c - d) := by
  rw [← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_sub ht]

/-- Combining three powers of a fixed positive base. -/
theorem rpow_comb3 {t a b c : ℝ} (ht : 0 < t) :
    t ^ a * t ^ b * t ^ c = t ^ (a + b + c) := by
  rw [← Real.rpow_add ht, ← Real.rpow_add ht]

set_option maxHeartbeats 1000000 in
/-- **The annulus constant times the number of steps is below the majorant.** -/
theorem eventually_rhoBound_mul_steps_le {A delta Ctot β γ : ℝ} (hβ0 : 9 / 10 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ0 : 9 / 10 < γ * β) (hγβ1 : γ * β < 1) (hCtot : 0 ≤ Ctot)
    (hdelta : 0 < delta) :
    ∀ᶠ x : ℝ in atTop,
      budgetRhoBound A delta Ctot β γ x * ((ladderSteps β γ x : ℕ) : ℝ)
        ≤ rhoMajorant A Ctot β γ x := by
  have hβpos : (0 : ℝ) < β := by linarith
  have hε : (0 : ℝ) < (γ * β - 9 / 10) / 2 := by linarith
  have hzero := tendsto_ladderEta (β := β) (γ := γ) hβpos hγβ1
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  filter_upwards [eventually_ladderWidth_le hβpos, eventually_ladderWidth_ge hβpos,
    eventually_budgetHmaj_poly (A := A) hβpos hγ0 hγβ0 hγβ1,
    eventually_ladderSteps_poly hβpos hγ0 hγ1 hγβ1,
    Filter.eventually_ge_atTop (Real.exp 1),
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) hzero,
    eventually_exp_mu_q_le (A := A) (delta := delta) hβpos hγ0 hγβ0 hdelta,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hDle hDge hH hLs hxe hη1 hexp hx1
  have ht1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have ht0 : (0 : ℝ) < Real.log x := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  -- the seven pointwise facts
  have hD0 : (0 : ℝ) ≤ ladderWidth β x := by
    have := Real.rpow_nonneg ht0.le (4 * β)
    linarith [hDge]
  have hDsq : (ladderWidth β x) ^ 2 ≤ 256 * (Real.log x) ^ (8 * β) := by
    have hpow : ((Real.log x) ^ (4 * β)) ^ 2 = (Real.log x) ^ (8 * β) := by
      rw [← Real.rpow_natCast ((Real.log x) ^ (4 * β)) 2, ← Real.rpow_mul ht0.le]
      congr 1
      push_cast
      ring
    have h := pow_le_pow_left₀ hD0 hDle 2
    rw [mul_pow, hpow] at h
    norm_num at h
    linarith [h]
  have hLx : (0 : ℝ) < (Real.log x) ^ β := Real.rpow_pos_of_pos ht0 β
  have hLx1 : (1 : ℝ) ≤ (Real.log x) ^ β := Real.one_le_rpow ht1 hβpos.le
  have hQge : Real.exp ((Real.log x) ^ (γ * β)) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) :=
    eventually_siftStart_ge x
  have hQ0 : (0 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos _) hQge
  have ht₀ : 2 * Real.pi * annulusStart β x = 2 * Real.pi * (Real.log x) ^ (13 : ℝ) := by
    rw [annulusStart]
  have ht₀0 : (0 : ℝ) < 2 * Real.pi * annulusStart β x := by
    rw [ht₀]
    have : (0 : ℝ) < (Real.log x) ^ (13 : ℝ) := Real.rpow_pos_of_pos ht0 _
    positivity
  set t : ℝ := Real.log x with htdef
  set Dx : ℝ := ladderWidth β x with hDxdef
  set Hx : ℝ := 1 + (1 + t) * budgetWinv A x with hHxdef
  set Ex : ℝ := Real.exp (-(min delta (1 / budgetWinv A x) / 2
    * Real.log ((siftStart (γ * β) x : ℕ) : ℝ))) with hExdef
  set T0 : ℝ := 2 * Real.pi * annulusStart β x with hT0def
  set Qx : ℝ := ((siftStart (γ * β) x : ℕ) : ℝ) with hQxdef
  set KA : ℝ := 1 + 40 * routeTZeroFreeDeltaEnvelopeConstant A with hKAdef
  set Lm : ℝ := 2 * t ^ (2 * β + 5 / 4 - γ * β) with hLmdef
  have hEx0 : (0 : ℝ) < Ex := Real.exp_pos _
  have hHx0 : (0 : ℝ) < Hx := by
    rw [hHxdef]
    have := (budgetWinv_pos (A := A) hx1.le).le
    nlinarith [this, ht1]
  have hKA0 : (0 : ℝ) < KA := by
    rw [hKAdef]
    positivity
  have hLm0 : (0 : ℝ) < Lm := by
    rw [hLmdef]
    have : (0 : ℝ) < t ^ (2 * β + 5 / 4 - γ * β) := Real.rpow_pos_of_pos ht0 _
    linarith
  have hT0ge : 6 * t ^ (13 : ℝ) ≤ T0 := by
    rw [ht₀]
    have hp : (0 : ℝ) < t ^ (13 : ℝ) := Real.rpow_pos_of_pos ht0 _
    nlinarith [hpi3, hp]
  have hT0sq : 36 * t ^ (26 : ℝ) ≤ T0 ^ 2 := by
    have hp : (0 : ℝ) < t ^ (13 : ℝ) := Real.rpow_pos_of_pos ht0 _
    have hid : t ^ (26 : ℝ) = t ^ (13 : ℝ) * t ^ (13 : ℝ) := by
      rw [← Real.rpow_add ht0]
      norm_num
    have h36 : (0 : ℝ) ≤ 6 * t ^ (13 : ℝ) := by positivity
    have hprod : (0 : ℝ) ≤ (T0 - 6 * t ^ (13 : ℝ)) * (T0 + 6 * t ^ (13 : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hid]
    nlinarith [hprod]
  -- the five pieces
  have hpowmul : ∀ a b : ℝ, t ^ a * t ^ b = t ^ (a + b) := fun a b =>
    (Real.rpow_add ht0 a b).symm
  have hLxsq : ((t : ℝ) ^ β) ^ 2 = t ^ (2 * β) := by
    rw [← Real.rpow_natCast (t ^ β) 2, ← Real.rpow_mul ht0.le]
    congr 1
    push_cast
    ring
  have hB1 : Ctot * Dx ^ 2 * (((t : ℝ) ^ β) ^ 2 / T0) / (2 * Real.pi) * Lm
      ≤ 512 * Ctot / 36 * t ^ (12 * β + 5 / 4 - γ * β - 13) := by
    have h1 : Ctot * Dx ^ 2 * (((t : ℝ) ^ β) ^ 2 / T0) / (2 * Real.pi) * Lm
        ≤ Ctot * (256 * t ^ (8 * β)) * (t ^ (2 * β) / (6 * t ^ (13 : ℝ))) / 6
          * (2 * t ^ (2 * β + 5 / 4 - γ * β)) := by
      have hp13 : (0 : ℝ) < t ^ (13 : ℝ) := Real.rpow_pos_of_pos ht0 _
      have hp2 : (0 : ℝ) < t ^ (2 * β) := Real.rpow_pos_of_pos ht0 _
      have hdiv : ((t : ℝ) ^ β) ^ 2 / T0 ≤ t ^ (2 * β) / (6 * t ^ (13 : ℝ)) := by
        rw [hLxsq]
        exact div_le_div_of_nonneg_left hp2.le (by positivity) hT0ge
      have hdiv0 : (0 : ℝ) ≤ ((t : ℝ) ^ β) ^ 2 / T0 := by positivity
      have hstep1 : Ctot * Dx ^ 2 * (((t : ℝ) ^ β) ^ 2 / T0)
          ≤ Ctot * (256 * t ^ (8 * β)) * (t ^ (2 * β) / (6 * t ^ (13 : ℝ))) := by
        have ha : Ctot * Dx ^ 2 ≤ Ctot * (256 * t ^ (8 * β)) :=
          mul_le_mul_of_nonneg_left hDsq hCtot
        have ha0 : (0 : ℝ) ≤ Ctot * Dx ^ 2 := by positivity
        exact mul_le_mul ha hdiv hdiv0 (by positivity)
      have hstep2 : Ctot * (256 * t ^ (8 * β)) * (t ^ (2 * β) / (6 * t ^ (13 : ℝ))) / (2 * Real.pi)
          ≤ Ctot * (256 * t ^ (8 * β)) * (t ^ (2 * β) / (6 * t ^ (13 : ℝ))) / 6 := by
        refine div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      have hstep0 : (0 : ℝ) ≤ Ctot * Dx ^ 2 * (((t : ℝ) ^ β) ^ 2 / T0) := by positivity
      have hdivmono : Ctot * Dx ^ 2 * (((t : ℝ) ^ β) ^ 2 / T0) / (2 * Real.pi)
          ≤ Ctot * (256 * t ^ (8 * β)) * (t ^ (2 * β) / (6 * t ^ (13 : ℝ))) / (2 * Real.pi) :=
        div_le_div_of_nonneg_right hstep1 (by positivity)
      have hfin := mul_le_mul_of_nonneg_right (le_trans hdivmono hstep2)
        (by positivity : (0:ℝ) ≤ 2 * t ^ (2 * β + 5 / 4 - γ * β))
      rw [hLmdef]
      exact hfin
    refine h1.trans (le_of_eq ?_)
    have hp13 : (0 : ℝ) < t ^ (13 : ℝ) := Real.rpow_pos_of_pos ht0 _
    have hcomb : t ^ (8 * β) * t ^ (2 * β) * t ^ (2 * β + 5 / 4 - γ * β) / t ^ (13 : ℝ)
        = t ^ (12 * β + 5 / 4 - γ * β - 13) := by
      rw [rpow_comb ht0]
      congr 1
      ring
    rw [← hcomb]
    field_simp
    ring
  have hB2 : Ctot * Dx ^ 2 * (Hx * Ex) / (2 * Real.pi) * Lm
      ≤ 512 * Ctot * KA / 6 * (t ^ (10 * β + 13 / 4 - γ * β)
        * Real.exp (-(t ^ ((γ * β - 9 / 10) / 4)))) := by
    have hHE : Hx * Ex ≤ (KA * t ^ (2 : ℝ)) * Real.exp (-(t ^ ((γ * β - 9 / 10) / 4))) :=
      mul_le_mul hH hexp hEx0.le (by positivity)
    have hHE0 : (0 : ℝ) ≤ Hx * Ex := by positivity
    have hstep1 : Ctot * Dx ^ 2 * (Hx * Ex)
        ≤ Ctot * (256 * t ^ (8 * β)) * ((KA * t ^ (2 : ℝ))
          * Real.exp (-(t ^ ((γ * β - 9 / 10) / 4)))) := by
      have ha : Ctot * Dx ^ 2 ≤ Ctot * (256 * t ^ (8 * β)) :=
        mul_le_mul_of_nonneg_left hDsq hCtot
      exact mul_le_mul ha hHE hHE0 (by positivity)
    have hstep2 : Ctot * (256 * t ^ (8 * β)) * ((KA * t ^ (2 : ℝ))
          * Real.exp (-(t ^ ((γ * β - 9 / 10) / 4)))) / (2 * Real.pi)
        ≤ Ctot * (256 * t ^ (8 * β)) * ((KA * t ^ (2 : ℝ))
          * Real.exp (-(t ^ ((γ * β - 9 / 10) / 4)))) / 6 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have hdivmono : Ctot * Dx ^ 2 * (Hx * Ex) / (2 * Real.pi)
        ≤ Ctot * (256 * t ^ (8 * β)) * ((KA * t ^ (2 : ℝ))
          * Real.exp (-(t ^ ((γ * β - 9 / 10) / 4)))) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right hstep1 (by positivity)
    have hfin := mul_le_mul_of_nonneg_right (le_trans hdivmono hstep2)
      (by positivity : (0:ℝ) ≤ 2 * t ^ (2 * β + 5 / 4 - γ * β))
    rw [hLmdef]
    refine hfin.trans (le_of_eq ?_)
    have hcomb : t ^ (8 * β) * t ^ (2 : ℝ) * t ^ (2 * β + 5 / 4 - γ * β)
        = t ^ (10 * β + 13 / 4 - γ * β) := by
      rw [rpow_comb3 ht0]
      congr 1
      ring
    rw [← hcomb]
    ring
  have hB3 : Ctot * Dx ^ 2 * (Hx * (1 / T0 ^ 2)) / (2 * Real.pi) * Lm
      ≤ 512 * Ctot * KA / 216 * t ^ (10 * β + 13 / 4 - γ * β - 26) := by
    have hp26 : (0 : ℝ) < t ^ (26 : ℝ) := Real.rpow_pos_of_pos ht0 _
    have hinv : 1 / T0 ^ 2 ≤ 1 / (36 * t ^ (26 : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hT0sq
    have hHE : Hx * (1 / T0 ^ 2) ≤ (KA * t ^ (2 : ℝ)) * (1 / (36 * t ^ (26 : ℝ))) :=
      mul_le_mul hH hinv (by positivity) (by positivity)
    have hHE0 : (0 : ℝ) ≤ Hx * (1 / T0 ^ 2) := by positivity
    have hstep1 : Ctot * Dx ^ 2 * (Hx * (1 / T0 ^ 2))
        ≤ Ctot * (256 * t ^ (8 * β)) * ((KA * t ^ (2 : ℝ)) * (1 / (36 * t ^ (26 : ℝ)))) := by
      have ha : Ctot * Dx ^ 2 ≤ Ctot * (256 * t ^ (8 * β)) :=
        mul_le_mul_of_nonneg_left hDsq hCtot
      exact mul_le_mul ha hHE hHE0 (by positivity)
    have hstep2 : Ctot * (256 * t ^ (8 * β)) * ((KA * t ^ (2 : ℝ))
          * (1 / (36 * t ^ (26 : ℝ)))) / (2 * Real.pi)
        ≤ Ctot * (256 * t ^ (8 * β)) * ((KA * t ^ (2 : ℝ))
          * (1 / (36 * t ^ (26 : ℝ)))) / 6 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have hdivmono : Ctot * Dx ^ 2 * (Hx * (1 / T0 ^ 2)) / (2 * Real.pi)
        ≤ Ctot * (256 * t ^ (8 * β)) * ((KA * t ^ (2 : ℝ))
          * (1 / (36 * t ^ (26 : ℝ)))) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right hstep1 (by positivity)
    have hfin := mul_le_mul_of_nonneg_right (le_trans hdivmono hstep2)
      (by positivity : (0:ℝ) ≤ 2 * t ^ (2 * β + 5 / 4 - γ * β))
    rw [hLmdef]
    refine hfin.trans (le_of_eq ?_)
    have hcomb : t ^ (8 * β) * t ^ (2 : ℝ) * t ^ (2 * β + 5 / 4 - γ * β) / t ^ (26 : ℝ)
        = t ^ (10 * β + 13 / 4 - γ * β - 26) := by
      rw [rpow_comb ht0]
      congr 1
      ring
    rw [← hcomb]
    field_simp
    ring
  have hB4 : (Real.log 2 + t ^ β) / Dx * Lm ≤ 4 * t ^ (5 / 4 - β - γ * β) := by
    have hnum : Real.log 2 + t ^ β ≤ 2 * t ^ β := by linarith
    have hnum0 : (0 : ℝ) ≤ Real.log 2 + t ^ β := by linarith
    have hDpos : (0 : ℝ) < t ^ (4 * β) := Real.rpow_pos_of_pos ht0 _
    have hdiv : (Real.log 2 + t ^ β) / Dx ≤ 2 * t ^ β / t ^ (4 * β) := by
      refine div_le_div₀ (by positivity) hnum hDpos hDge
    have hfin := mul_le_mul_of_nonneg_right hdiv
      (by positivity : (0:ℝ) ≤ 2 * t ^ (2 * β + 5 / 4 - γ * β))
    rw [hLmdef]
    refine hfin.trans (le_of_eq ?_)
    have hcomb : t ^ β * t ^ (2 * β + 5 / 4 - γ * β) / t ^ (4 * β) = t ^ (5 / 4 - β - γ * β) := by
      rw [← Real.rpow_add ht0, ← Real.rpow_sub ht0]
      congr 1
      ring
    rw [← hcomb]
    field_simp
    ring
  have hB5 : 2 * t ^ β / Real.sqrt Qx * Lm
      ≤ 4 * (t ^ (3 * β + 5 / 4 - γ * β) * Real.exp (-(t ^ (γ * β) / 2))) := by
    have hsq : Real.exp (t ^ (γ * β) / 2) ≤ Real.sqrt Qx := by
      have h1 : Real.sqrt (Real.exp (t ^ (γ * β))) ≤ Real.sqrt Qx := Real.sqrt_le_sqrt hQge
      rwa [← Real.exp_half] at h1
    have hinv : 1 / Real.sqrt Qx ≤ Real.exp (-(t ^ (γ * β) / 2)) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos _) hsq
    have hdiv : 2 * t ^ β / Real.sqrt Qx ≤ 2 * t ^ β * Real.exp (-(t ^ (γ * β) / 2)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    have hfin := mul_le_mul_of_nonneg_right hdiv
      (by positivity : (0:ℝ) ≤ 2 * t ^ (2 * β + 5 / 4 - γ * β))
    rw [hLmdef]
    refine hfin.trans (le_of_eq ?_)
    have hcomb : t ^ β * t ^ (2 * β + 5 / 4 - γ * β) = t ^ (3 * β + 5 / 4 - γ * β) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    rw [← hcomb]
    ring
  have hB6 : 7 * Real.exp 9 / Qx * Lm
      ≤ 14 * Real.exp 9 * (t ^ (2 * β + 5 / 4 - γ * β) * Real.exp (-(t ^ (γ * β)))) := by
    have hinv : 1 / Qx ≤ Real.exp (-(t ^ (γ * β))) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos _) hQge
    have hdiv : 7 * Real.exp 9 / Qx ≤ 7 * Real.exp 9 * Real.exp (-(t ^ (γ * β))) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    have hfin := mul_le_mul_of_nonneg_right hdiv
      (by positivity : (0:ℝ) ≤ 2 * t ^ (2 * β + 5 / 4 - γ * β))
    rw [hLmdef]
    refine hfin.trans (le_of_eq ?_)
    ring
  -- assemble
  have hDpos : (0 : ℝ) < Dx := lt_of_lt_of_le (Real.rpow_pos_of_pos ht0 (4 * β)) hDge
  have hLs0 : (0 : ℝ) ≤ ((ladderSteps β γ x : ℕ) : ℝ) := Nat.cast_nonneg _
  set μx : ℝ := min delta (1 / budgetWinv A x) / 2 with hμxdef
  set R : ℝ := relScaledMajorant Ctot Dx (t ^ β) Hx μx (Real.log Qx) T0 Qx with hRdef
  have hR0 : (0 : ℝ) ≤ R :=
    relScaledMajorant_nonneg hCtot hDpos (Real.rpow_nonneg ht0.le β) hHx0.le ht₀0 hQ0
  have hηpos : (0 : ℝ) < ladderEta β γ x := ladderEta_pos hx1
  have hexpand : R * Lm
      = Ctot * Dx ^ 2 * (((t : ℝ) ^ β) ^ 2 / T0) / (2 * Real.pi) * Lm
        + Ctot * Dx ^ 2 * (Hx * Ex) / (2 * Real.pi) * Lm
        + Ctot * Dx ^ 2 * (Hx * (1 / T0 ^ 2)) / (2 * Real.pi) * Lm
        + (Real.log 2 + t ^ β) / Dx * Lm
        + 2 * t ^ β / Real.sqrt Qx * Lm := by
    rw [hRdef, relScaledMajorant, hExdef, hμxdef]
    ring
  have hRLm : R * Lm
      ≤ 512 * Ctot / 36 * t ^ (12 * β + 5 / 4 - γ * β - 13)
        + 512 * Ctot * KA / 6 * (t ^ (10 * β + 13 / 4 - γ * β)
            * Real.exp (-(t ^ ((γ * β - 9 / 10) / 4))))
        + 512 * Ctot * KA / 216 * t ^ (10 * β + 13 / 4 - γ * β - 26)
        + 4 * t ^ (5 / 4 - β - γ * β)
        + 4 * (t ^ (3 * β + 5 / 4 - γ * β) * Real.exp (-(t ^ (γ * β) / 2))) := by
    rw [hexpand]
    linarith [hB1, hB2, hB3, hB4, hB5]
  simp only [budgetRhoBound, ladderRho, rhoMajorant]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ 4 / Real.log 2)
  have hstep : ((1 + ladderEta β γ x) * R + 7 * Real.exp 9 / Qx)
        * ((ladderSteps β γ x : ℕ) : ℝ)
      ≤ (2 * R + 7 * Real.exp 9 / Qx) * Lm := by
    have hA : (1 + ladderEta β γ x) * R ≤ 2 * R := by nlinarith [hR0, hη1, hηpos]
    have hB : (0 : ℝ) ≤ 7 * Real.exp 9 / Qx := by positivity
    have hsum0 : (0 : ℝ) ≤ (1 + ladderEta β γ x) * R + 7 * Real.exp 9 / Qx := by
      have h1 : (0 : ℝ) ≤ (1 + ladderEta β γ x) * R :=
        mul_nonneg (by linarith) hR0
      linarith
    exact mul_le_mul (by linarith) hLs hLs0 (by linarith)
  refine hstep.trans ?_
  have hsplit : (2 * R + 7 * Real.exp 9 / Qx) * Lm = 2 * (R * Lm) + 7 * Real.exp 9 / Qx * Lm := by
    ring
  rw [hsplit]
  linarith [hRLm, hB6]


/-- **The annulus constant times the number of steps vanishes.** -/
theorem tendsto_budgetRho_mul_steps {A delta Ctot β γ : ℝ} (hβ0 : 9 / 10 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ0 : 9 / 10 < γ * β) (hγβ1 : γ * β < 1) (hCtot : 0 ≤ Ctot)
    (hdelta : 0 < delta) :
    Tendsto (fun x : ℝ => budgetRhoBound A delta Ctot β γ x * ((ladderSteps β γ x : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hβpos : (0 : ℝ) < β := by linarith
  refine squeeze_zero' ?_ (eventually_rhoBound_mul_steps_le hβ0 hβ1 hγ0 hγ1 hγβ0 hγβ1 hCtot
    hdelta) (tendsto_rhoMajorant hβ0 hβ1 hγ0 hγβ0 hγβ1)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (Real.exp 1)] with x hx1 hxe
  have ht1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have ht0 : (0 : ℝ) < Real.log x := by linarith
  have hηpos : (0 : ℝ) < ladderEta β γ x := ladderEta_pos hx1
  have hDpos : (0 : ℝ) < ladderWidth β x := by
    have hge : (Real.log x) ^ (4 * β) ≤ ladderWidth β x := by
      have hval : Real.log (2 * cardLength β x) = Real.log 2 + (Real.log x) ^ β := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (cardLength_pos β x)), log_cardLength]
      have hge' : (Real.log x) ^ β ≤ Real.log (2 * cardLength β x) := by
        rw [hval]
        have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      have h0 : (0 : ℝ) ≤ (Real.log x) ^ β := Real.rpow_nonneg ht0.le _
      have hp4 : ((Real.log x) ^ β) ^ 4 ≤ (Real.log (2 * cardLength β x)) ^ 4 :=
        pow_le_pow_left₀ h0 hge' 4
      have hrpow : ((Real.log x) ^ β) ^ 4 = (Real.log x) ^ (4 * β) := by
        rw [← Real.rpow_natCast ((Real.log x) ^ β) 4, ← Real.rpow_mul ht0.le]
        congr 1
        push_cast
        ring
      rw [ladderWidth, ← hrpow]
      exact hp4
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos ht0 (4 * β)) hge
  have hQ0 : (0 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos _) (eventually_siftStart_ge x)
  have hH0 : (0 : ℝ) ≤ 1 + (1 + Real.log x) * budgetWinv A x := by
    have := (budgetWinv_pos (A := A) hx1.le).le
    nlinarith [this, ht1]
  have ht₀0 : (0 : ℝ) < 2 * Real.pi * annulusStart β x := by
    rw [annulusStart]
    have : (0 : ℝ) < (Real.log x) ^ (13 : ℝ) := Real.rpow_pos_of_pos ht0 _
    have := Real.pi_pos
    positivity
  have hR0 : (0 : ℝ) ≤ relScaledMajorant Ctot (ladderWidth β x) ((Real.log x) ^ β)
      (1 + (1 + Real.log x) * budgetWinv A x) (min delta (1 / budgetWinv A x) / 2)
      (Real.log ((siftStart (γ * β) x : ℕ) : ℝ)) (2 * Real.pi * annulusStart β x)
      ((siftStart (γ * β) x : ℕ) : ℝ) :=
    relScaledMajorant_nonneg hCtot hDpos (Real.rpow_nonneg ht0.le β) hH0 ht₀0 hQ0
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLs0 : (0 : ℝ) ≤ ((ladderSteps β γ x : ℕ) : ℝ) := Nat.cast_nonneg _
  have hρ0 : (0 : ℝ) ≤ budgetRhoBound A delta Ctot β γ x := by
    simp only [budgetRhoBound, ladderRho]
    have h1 : (0 : ℝ) ≤ (1 + ladderEta β γ x)
        * relScaledMajorant Ctot (ladderWidth β x) ((Real.log x) ^ β)
          (1 + (1 + Real.log x) * budgetWinv A x) (min delta (1 / budgetWinv A x) / 2)
          (Real.log ((siftStart (γ * β) x : ℕ) : ℝ)) (2 * Real.pi * annulusStart β x)
          ((siftStart (γ * β) x : ℕ) : ℝ) := mul_nonneg (by linarith) hR0
    have h2 : (0 : ℝ) ≤ 7 * Real.exp 9 / ((siftStart (γ * β) x : ℕ) : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ 4 / Real.log 2 := by positivity
    nlinarith [h1, h2, h3]
  exact mul_nonneg hρ0 hLs0

end

end RHTower.Sieve
