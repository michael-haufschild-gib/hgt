import GaloisForLFunctions.RHTower.Sieve.MaynardMultiscaleReferenceTelescope
import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceCountNormalization
import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceArbitraryOrderLocalization

set_option maxHeartbeats 800000

/-!
# Prime-free composition for the physical Route-T slice

This module supplies quantitative bounds needed to compose the dyadic prime-free defect producer
with arbitrary-order physical-slice localization.  The literal floor envelope and the number of
dyadic rungs each cost only one logarithm.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- The literal floor-truncated physical-slice envelope costs at most one logarithm. -/
theorem routeTPhysicalSliceEnvelope_le_six_log_three_mul
    {N R : ℝ} (hN : 2 ≤ N) (hR : 0 ≤ R) (hRN : R ≤ N) :
    routeTPhysicalSliceEnvelope N R ≤ 6 * Real.log (3 * N) := by
  let A : ℕ := ⌊N⌋₊
  let B : ℕ := ⌊N + 2 * R⌋₊
  have hN0 : 0 ≤ N := by linarith
  have hBarg0 : 0 ≤ N + 2 * R := by linarith
  have hAupper : (A : ℝ) ≤ N := by
    dsimp only [A]
    exact Nat.floor_le hN0
  have hAlower : N - 1 < (A : ℝ) := by
    have h := Nat.lt_floor_add_one N
    dsimp only [A]
    linarith
  have hAone : (1 : ℝ) ≤ A := by linarith
  have hApos : (0 : ℝ) < A := by linarith
  have hBupper : (B : ℝ) ≤ 3 * N := by
    calc
      (B : ℝ) ≤ N + 2 * R := by
        dsimp only [B]
        exact Nat.floor_le hBarg0
      _ ≤ 3 * N := by linarith
  have hBone : (1 : ℝ) ≤ B := by
    have hAB : A ≤ B := by
      dsimp only [A, B]
      exact Nat.floor_mono (by linarith)
    have hAoneNat : 1 ≤ A := by exact_mod_cast hAone
    exact_mod_cast hAoneNat.trans hAB
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hBone
  have hlogB : Real.log B ≤ Real.log (3 * N) :=
    Real.log_le_log (by positivity) hBupper
  have hratio : (B : ℝ) / A ≤ 6 := by
    rw [div_le_iff₀ hApos]
    nlinarith [hBupper, hAlower]
  change (B : ℝ) * (Real.log B / A) ≤ 6 * Real.log (3 * N)
  calc
    (B : ℝ) * (Real.log B / A) = ((B : ℝ) / A) * Real.log B := by ring
    _ ≤ 6 * Real.log B := mul_le_mul_of_nonneg_right hratio hlogB0
    _ ≤ 6 * Real.log (3 * N) := mul_le_mul_of_nonneg_left hlogB (by norm_num)

/-- The endpoint power bracket makes the dyadic telescope loss explicitly logarithmic. -/
theorem routeTComparableWidthLadder_index_le_log
    {H R : ℝ} (hH : 0 < H) (hHR : H ≤ R) {J : ℕ} (hJ : 0 < J)
    (hbelow : (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ R / H) :
    (J : ℝ) ≤ 1 + Real.log (R / H) / Real.log 2 := by
  have hratio : 1 ≤ R / H := by
    exact (le_div_iff₀ hH).2 (by simpa using hHR)
  have hpow0 : (0 : ℝ) < (((2 ^ (J - 1) : ℕ) : ℝ)) := by positivity
  have hlog := Real.log_le_log hpow0 hbelow
  have hJone : 1 ≤ J := by omega
  have hlogpow :
      Real.log (((2 ^ (J - 1) : ℕ) : ℝ)) =
        ((J - 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hlogpow] at hlog
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : ((J - 1 : ℕ) : ℝ) ≤ Real.log (R / H) / Real.log 2 := by
    exact (le_div_iff₀ hlogtwo).2 (by simpa [mul_comm] using hlog)
  have hJcast : (J : ℝ) = (J - 1 : ℕ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hJone).symm
  rw [hJcast]
  linarith

private theorem tendsto_routeT_logPacket_mul_rpow_neg_zero
    {mu a : ℝ} (ha : 0 < a) :
    Tendsto (fun T : ℝ =>
      (1 + Real.log T) * (1 + Real.log (3 * T ^ mu)) * T ^ (-a))
      atTop (nhds 0) := by
  have h0 := HTGeometry.tendsto_logPow_div_rpow ha 0
  have h1 := HTGeometry.tendsto_logPow_div_rpow ha 1
  have h2 := HTGeometry.tendsto_logPow_div_rpow ha 2
  have hsum :=
    ((h0.const_mul (1 + Real.log 3)).add
      (h1.const_mul (mu + 1 + Real.log 3))).add
      (h2.const_mul mu)
  have hsum0 : Tendsto (fun T : ℝ =>
      (1 + Real.log 3) * ((Real.log T) ^ 0 / T ^ a) +
        (mu + 1 + Real.log 3) * ((Real.log T) ^ 1 / T ^ a) +
        mu * ((Real.log T) ^ 2 / T ^ a)) atTop (nhds 0) := by
    simpa using hsum
  refine hsum0.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hT mu).ne', Real.log_rpow hT,
    Real.rpow_neg hT.le]
  simp only [pow_zero, pow_one]
  field_simp
  ring

theorem eventually_routeT_natOrder_surplus_gt_base_layers
    (j : ℕ) (hj : 1 ≤ j) {mu alpha v : ℝ} (hmu : 0 < mu)
    (hvLower : 1 + 1 / (j : ℝ) < v) (hvUpper : v < mu * (1 - alpha))
    (Cloc Ccell c K : ℝ) (hCloc : 1 ≤ Cloc) (hCcell : 1 ≤ Ccell)
    (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {J : ℕ} {D : ℝ}, 0 < J →
        (J : ℝ) ≤ K * (1 + Real.log T) → c / (J : ℝ) ≤ D →
        let N := T ^ mu
        let R := N / (2 * T)
        let V := T ^ v
        32 * (N / (2 * R) - 1) * N ^ (alpha - 1) <
            routeTPhysicalSliceNatOrderLocalizationSurplus
              j Cloc N R 1 V D ∧
          2080 * Ccell * (V - N / (2 * R)) * N ^ (alpha - 1) <
            routeTPhysicalSliceNatOrderLocalizationSurplus
              j Cloc N R 1 V D := by
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have htailExp : ((j + 1 : ℕ) : ℝ) - (j : ℝ) * v < 0 := by
    have hmul : (j : ℝ) + 1 < (j : ℝ) * v := by
      have hfrac : 1 / (j : ℝ) < v - 1 := by linarith
      have := (div_lt_iff₀ hjR).mp hfrac
      nlinarith
    norm_num
    linarith
  have houterExp : v - mu * (1 - alpha) < 0 := sub_neg.mpr hvUpper
  let aTail : ℝ := (j : ℝ) * v - ((j + 1 : ℕ) : ℝ)
  let aCentral : ℝ := mu * (1 - alpha) - 1
  let aOuter : ℝ := mu * (1 - alpha) - v
  have hvOne : 1 < v := by linarith [one_div_pos.mpr hjR]
  have haTail : 0 < aTail := by dsimp only [aTail]; linarith
  have haCentral : 0 < aCentral := by dsimp only [aCentral]; linarith
  have haOuter : 0 < aOuter := by dsimp only [aOuter]; linarith
  have hlimOne := tendsto_routeT_logPacket_mul_rpow_neg_zero
    (mu := mu) (a := (1 : ℝ)) (by norm_num)
  have hlimTail := tendsto_routeT_logPacket_mul_rpow_neg_zero
    (mu := mu) haTail
  have hlimCentral := tendsto_routeT_logPacket_mul_rpow_neg_zero
    (mu := mu) haCentral
  have hlimOuter := tendsto_routeT_logPacket_mul_rpow_neg_zero
    (mu := mu) haOuter
  let Ctail : ℝ := 6 * Cloc * (((2 ^ (j + 1) : ℕ) : ℝ))
  have hlim := ((((hlimOne.const_mul 48).add
      (hlimTail.const_mul Ctail)).add
      (hlimCentral.const_mul 32)).add
      (hlimOuter.const_mul (2080 * Ccell))).const_mul K
  have hlim' : Tendsto (fun T : ℝ =>
      K * (1 + Real.log T) *
        (48 * (1 + Real.log (3 * T ^ mu)) * T ^ (-(1 : ℝ)) +
          Ctail * (1 + Real.log (3 * T ^ mu)) * T ^ (-aTail) +
          32 * (1 + Real.log (3 * T ^ mu)) * T ^ (-aCentral) +
          (2080 * Ccell) * (1 + Real.log (3 * T ^ mu)) * T ^ (-aOuter)))
      atTop (nhds 0) := by
    have hlim0 : Tendsto (fun T : ℝ =>
        K * (48 * ((1 + Real.log T) * (1 + Real.log (3 * T ^ mu)) * T ^ (-(1 : ℝ))) +
          Ctail * ((1 + Real.log T) * (1 + Real.log (3 * T ^ mu)) * T ^ (-aTail)) +
          32 * ((1 + Real.log T) * (1 + Real.log (3 * T ^ mu)) * T ^ (-aCentral)) +
          (2080 * Ccell) *
            ((1 + Real.log T) * (1 + Real.log (3 * T ^ mu)) * T ^ (-aOuter))))
        atTop (nhds 0) := by
      simpa using hlim
    exact hlim0.congr' (Eventually.of_forall fun T => by ring)
  have hsmall : ∀ᶠ T : ℝ in atTop,
      K * (1 + Real.log T) *
        (48 * (1 + Real.log (3 * T ^ mu)) * T ^ (-(1 : ℝ)) +
          Ctail * (1 + Real.log (3 * T ^ mu)) * T ^ (-aTail) +
          32 * (1 + Real.log (3 * T ^ mu)) * T ^ (-aCentral) +
          (2080 * Ccell) * (1 + Real.log (3 * T ^ mu)) * T ^ (-aOuter)) < c :=
    hlim'.eventually (Iio_mem_nhds hc)
  have hNtop : Tendsto (fun T : ℝ => T ^ mu) atTop atTop :=
    tendsto_rpow_atTop hmu
  have hNtwoEv : ∀ᶠ T : ℝ in atTop, 2 ≤ T ^ mu :=
    (tendsto_atTop.1 hNtop) 2
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ), hNtwoEv]
    with T hsmallT hT hNtwo
  intro J D hJ hJlog hD
  let N : ℝ := T ^ mu
  let R : ℝ := N / (2 * T)
  let V : ℝ := T ^ v
  let E : ℝ := routeTPhysicalSliceEnvelope N R
  let Llow : ℝ := 16 * E * (R / N)
  let Ltail : ℝ := E * (Cloc * (N / R) ^ (j + 1) * V ^ (-(j : ℝ)))
  let Bcentral : ℝ := 32 * (N / (2 * R) - 1) * N ^ (alpha - 1)
  let Bouter : ℝ := 2080 * Ccell * (V - N / (2 * R)) * N ^ (alpha - 1)
  let U : ℝ :=
    48 * (1 + Real.log (3 * N)) * T ^ (-(1 : ℝ)) +
      Ctail * (1 + Real.log (3 * N)) * T ^ (-aTail) +
      32 * (1 + Real.log (3 * N)) * T ^ (-aCentral) +
      (2080 * Ccell) * (1 + Real.log (3 * N)) * T ^ (-aOuter)
  have hT0 : 0 < T := by linarith
  have hTone : 1 ≤ T := le_trans (by norm_num) hT
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hNtwo' : 2 ≤ N := by simpa only [N] using hNtwo
  have hNone : 1 ≤ N := by
    dsimp only [N]
    exact Real.one_le_rpow hTone hmu.le
  have hR0 : 0 < R := by dsimp only [R]; positivity
  have hRN : R ≤ N := by
    dsimp only [R]
    rw [div_le_iff₀ (by positivity : 0 < 2 * T)]
    nlinarith [hN0]
  have hE := routeTPhysicalSliceEnvelope_le_six_log_three_mul hNtwo' hR0.le hRN
  have hlogPacket : 1 ≤ 1 + Real.log (3 * N) := by
    have h3N : 1 ≤ 3 * N := by nlinarith
    linarith [Real.log_nonneg h3N]
  have hE0 : 0 ≤ E := by
    dsimp only [E, routeTPhysicalSliceEnvelope]
    positivity
  have hwidthRatio : R / N = 1 / (2 * T) := by
    dsimp only [R]
    field_simp
  have htransition : N / (2 * R) = T := by
    dsimp only [R]
    field_simp
  have hNR : N / R = 2 * T := by
    dsimp only [R]
    field_simp
  have hNamp : N ^ (alpha - 1) = T ^ (-(mu * (1 - alpha))) := by
    dsimp only [N]
    rw [← Real.rpow_mul hT0.le]
    congr 1
    ring
  have htailId :
      (N / R) ^ (j + 1) * V ^ (-(j : ℝ)) =
        (((2 ^ (j + 1) : ℕ) : ℝ)) * T ^ (-aTail) := by
    rw [hNR]
    dsimp only [V]
    rw [mul_pow]
    have hid := (routeT_natOrder_tail_base_phase_identities
      (T := T) (mu := mu) (alpha := alpha) (v := v) (j := j) hT0).1
    calc
      (2 : ℝ) ^ (j + 1) * T ^ (j + 1) * (T ^ v) ^ (-(j : ℝ)) =
          (((2 ^ (j + 1) : ℕ) : ℝ)) *
            (T ^ (j + 1) * (T ^ v) ^ (-(j : ℝ))) := by
        norm_num [Nat.cast_pow]
        ring
      _ = (((2 ^ (j + 1) : ℕ) : ℝ)) *
          T ^ (((j + 1 : ℕ) : ℝ) - (j : ℝ) * v) := by rw [hid]
      _ = (((2 ^ (j + 1) : ℕ) : ℝ)) * T ^ (-aTail) := by
        congr 2
        dsimp only [aTail]
        ring
  have hcentralId : T * N ^ (alpha - 1) = T ^ (-aCentral) := by
    calc
      T * N ^ (alpha - 1) = T * T ^ (-(mu * (1 - alpha))) := by rw [hNamp]
      _ = T ^ (1 : ℝ) * T ^ (-(mu * (1 - alpha))) := by rw [Real.rpow_one]
      _ = T ^ ((1 : ℝ) + (-(mu * (1 - alpha)))) := by rw [Real.rpow_add hT0]
      _ = T ^ (-aCentral) := by
        congr 1
        dsimp only [aCentral]
        ring
  have houterId : V * N ^ (alpha - 1) = T ^ (-aOuter) := by
    dsimp only [V]
    rw [hNamp, ← Real.rpow_add hT0]
    congr 1
    dsimp only [aOuter]
    ring
  have hLlow0 : 0 ≤ Llow := by dsimp only [Llow]; positivity
  have hLtail0 : 0 ≤ Ltail := by dsimp only [Ltail]; positivity
  have hBcentral0 : 0 ≤ Bcentral := by
    dsimp only [Bcentral]
    rw [htransition]
    positivity
  have hBouter0 : 0 ≤ Bouter := by
    dsimp only [Bouter]
    rw [htransition]
    have hTv : T ≤ V := by
      dsimp only [V]
      have hjR : 0 < (j : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hj)
      have : 1 < v := by linarith [one_div_pos.mpr hjR]
      have hTv' : T ^ (1 : ℝ) ≤ T ^ v :=
        Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
      simpa only [Real.rpow_one] using hTv'
    positivity
  have hLlow : Llow ≤
      48 * (1 + Real.log (3 * N)) * T ^ (-(1 : ℝ)) := by
    dsimp only [Llow]
    rw [hwidthRatio, Real.rpow_neg_one]
    have hlog0 : 0 ≤ Real.log (3 * N) := by linarith [hlogPacket]
    have hE' : E ≤ 6 * Real.log (3 * N) := by simpa only [E] using hE
    have hhalfInv : 1 / (2 * T) = (1 / 2 : ℝ) * T⁻¹ := by
      field_simp
    rw [hhalfInv]
    calc
      16 * E * ((1 / 2 : ℝ) * T⁻¹) ≤
          16 * (6 * Real.log (3 * N)) * (1 / (2 * T)) := by
        rw [hhalfInv]
        gcongr
      _ = 48 * Real.log (3 * N) * T⁻¹ := by ring
      _ ≤ 48 * (1 + Real.log (3 * N)) * T⁻¹ := by
        gcongr; linarith
  have hLtail : Ltail ≤
      Ctail * (1 + Real.log (3 * N)) * T ^ (-aTail) := by
    dsimp only [Ltail]
    have hregroup :
        Cloc * (N / R) ^ (j + 1) * V ^ (-(j : ℝ)) =
          Cloc * ((N / R) ^ (j + 1) * V ^ (-(j : ℝ))) := by ring
    rw [hregroup, htailId]
    have hpow0 : 0 ≤ T ^ (-aTail) := Real.rpow_nonneg hT0.le _
    have hcoef0 : 0 ≤ Cloc * (((2 ^ (j + 1) : ℕ) : ℝ)) * T ^ (-aTail) := by
      positivity
    have hE' : E ≤ 6 * Real.log (3 * N) := by simpa only [E] using hE
    dsimp only [Ctail]
    calc
      E * (Cloc * ((((2 ^ (j + 1) : ℕ) : ℝ)) * T ^ (-aTail))) =
          E * (Cloc * (((2 ^ (j + 1) : ℕ) : ℝ)) * T ^ (-aTail)) := by ring
      _ ≤
          (6 * Real.log (3 * N)) *
            (Cloc * (((2 ^ (j + 1) : ℕ) : ℝ)) * T ^ (-aTail)) :=
        mul_le_mul_of_nonneg_right hE' hcoef0
      _ ≤ 6 * Cloc * (((2 ^ (j + 1) : ℕ) : ℝ)) *
          (1 + Real.log (3 * N)) * T ^ (-aTail) := by
        nlinarith
  have hBcentral : Bcentral ≤
      32 * (1 + Real.log (3 * N)) * T ^ (-aCentral) := by
    dsimp only [Bcentral]
    rw [htransition]
    have hamp0 : 0 ≤ N ^ (alpha - 1) := Real.rpow_nonneg hN0.le _
    have hdiff : T - 1 ≤ T := by linarith
    calc
      32 * (T - 1) * N ^ (alpha - 1) ≤
          32 * T * N ^ (alpha - 1) := by gcongr
      _ = 32 * T ^ (-aCentral) := by
        rw [show 32 * T * N ^ (alpha - 1) =
          32 * (T * N ^ (alpha - 1)) by ring, hcentralId]
      _ ≤ 32 * (1 + Real.log (3 * N)) * T ^ (-aCentral) := by
        have hpow0 : 0 ≤ T ^ (-aCentral) := Real.rpow_nonneg hT0.le _
        have hcoef : (32 : ℝ) ≤ 32 * (1 + Real.log (3 * N)) := by
          nlinarith
        exact mul_le_mul_of_nonneg_right hcoef hpow0
  have hBouter : Bouter ≤
      (2080 * Ccell) * (1 + Real.log (3 * N)) * T ^ (-aOuter) := by
    dsimp only [Bouter]
    rw [htransition]
    have hamp0 : 0 ≤ N ^ (alpha - 1) := Real.rpow_nonneg hN0.le _
    have hcell0 : 0 ≤ 2080 * Ccell := by positivity
    calc
      2080 * Ccell * (V - T) * N ^ (alpha - 1) ≤
          2080 * Ccell * V * N ^ (alpha - 1) := by gcongr; linarith
      _ = (2080 * Ccell) * T ^ (-aOuter) := by
        rw [show 2080 * Ccell * V * N ^ (alpha - 1) =
          (2080 * Ccell) * (V * N ^ (alpha - 1)) by ring, houterId]
      _ ≤ (2080 * Ccell) * (1 + Real.log (3 * N)) * T ^ (-aOuter) := by
        have hpow0 : 0 ≤ T ^ (-aOuter) := Real.rpow_nonneg hT0.le _
        have hcoef : 2080 * Ccell ≤
            (2080 * Ccell) * (1 + Real.log (3 * N)) := by
          have hcellpos : 0 < 2080 * Ccell := by positivity
          exact (le_mul_iff_one_le_right hcellpos).2 hlogPacket
        exact mul_le_mul_of_nonneg_right hcoef hpow0
  have htotalU : Llow + Ltail + Bcentral + Bouter ≤ U := by
    dsimp only [U]
    linarith
  have hU0 : 0 ≤ U := by
    dsimp only [U, Ctail]
    positivity
  have hJtotal : (J : ℝ) * (Llow + Ltail + Bcentral + Bouter) < c := by
    calc
      (J : ℝ) * (Llow + Ltail + Bcentral + Bouter) ≤ (J : ℝ) * U := by
        gcongr
      _ ≤ (K * (1 + Real.log T)) * U := by gcongr
      _ < c := by
        dsimp only [U, N] at hsmallT ⊢
        simpa only [mul_assoc] using hsmallT
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have htotal : Llow + Ltail + Bcentral + Bouter < c / (J : ℝ) := by
    exact (lt_div_iff₀ hJR).2 (by simpa [mul_comm] using hJtotal)
  have hDtotal : Llow + Ltail + Bcentral + Bouter < D := htotal.trans_le hD
  have hcentralSurplus : Bcentral <
      routeTPhysicalSliceNatOrderLocalizationSurplus j Cloc N R 1 V D := by
    have hcore : Bcentral < D - Llow - Ltail := by linarith
    simpa only [routeTPhysicalSliceNatOrderLocalizationSurplus,
      Llow, Ltail, E, one_pow, mul_one] using hcore
  have houterSurplus : Bouter <
      routeTPhysicalSliceNatOrderLocalizationSurplus j Cloc N R 1 V D := by
    have hcore : Bouter < D - Llow - Ltail := by linarith
    simpa only [routeTPhysicalSliceNatOrderLocalizationSurplus,
      Llow, Ltail, E, one_pow, mul_one] using hcore
  simpa only [N, R, V, Bcentral, Bouter] using ⟨hcentralSurplus, houterSurplus⟩


/-- On every strict base-phase margin, an inverse-log adjacent defect forces the literal
physical von-Mangoldt slice into Route T's second large-value alternative.  Arbitrary-order
localization makes both central and outer base layers strictly smaller than the surviving defect. -/
theorem exists_eventually_physicalSlice_natOrder_secondAlternative_of_inverseLog_defect
    {mu alpha eta : ℝ} (hmu : 0 < mu) (halpha : 0 ≤ alpha)
    (hphase : 1 < mu * (1 - alpha)) (heta : 0 < eta)
    (hbudget : mu * (1 - routeTGapMomentNu) + eta ≤ 2)
    (c K : ℝ) (hc : 0 < c) :
    ∃ j : ℕ, 1 ≤ j ∧ ∃ v : ℝ,
      1 + 1 / (j : ℝ) < v ∧ v < mu * (1 - alpha) ∧
      ∃ Cloc Ccell : ℝ, 1 ≤ Cloc ∧ 1 ≤ Ccell ∧
        ∀ᶠ T : ℝ in atTop,
          ∀ {H D : ℝ} {J Q : ℕ}, 0 < J →
            (J : ℝ) ≤ K * (1 + Real.log T) → c / (J : ℝ) ≤ D →
            let N := T ^ mu
            let R := N / (2 * T)
            let V := T ^ v
            0 < H → H ≤ R → R ≤ 2 * H →
            D ≤ ‖∫ y : ℝ,
              dirPoly ⌊N + 2 * R⌋₊
                  (routeTVonMangoldtSliceCoeff ⌊N⌋₊ ⌊N + 2 * R⌋₊) (-y) *
                (routeTNormalizedSmoothWindowMellin N R
                    ((1 : ℂ) + (y : ℝ) * I) -
                  routeTNormalizedSmoothWindowMellin N H
                    ((1 : ℂ) + (y : ℝ) * I))‖ →
            routeTPhysicalSliceEnvelope N R ≤
              (((2 ^ Q : ℕ) : ℝ) * N ^ (alpha - 1)) →
            0 < Q →
            ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
              (∀ i, lam i + 1 ≤ lam (i + 1)) ∧ q < Q ∧
              (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * N ^ (alpha - 1)) ≤
                ‖dirPoly ⌊N + 2 * R⌋₊
                  (routeTVonMangoldtSliceCoeff ⌊N⌋₊ ⌊N + 2 * R⌋₊)
                    (lam r)‖) ∧
              routeTPhysicalSliceNatOrderLocalizationSurplus
                    j Cloc N R 1 V D /
                  (8320 * Ccell * (Q : ℝ)) ≤
                (((2 ^ q : ℕ) : ℝ) * N ^ (alpha - 1)) * (S.card : ℝ) ∧
              (S.card : ℝ) ≤ T * N ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  obtain ⟨j, hj, v, hvLower, hvUpper, _htail, _houter⟩ :=
    exists_routeT_natOrder_outer_phase_window hphase
  obtain ⟨Cloc, Ccell, hCloc, hCcell, hcap⟩ :=
    exists_eventually_physicalSlice_natOrder_annulus_base_or_secondAlternative
      j hj (mu := mu) (alpha := alpha) hmu heta hbudget
  have hdom := eventually_routeT_natOrder_surplus_gt_base_layers
    j hj hmu hvLower hvUpper Cloc Ccell c K hCloc hCcell hc
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hvOne : 1 < v := by linarith [one_div_pos.mpr hjR]
  have halphaOne : alpha < 1 := by
    by_contra h
    have hdelta : 1 - alpha ≤ 0 := by linarith
    have hprodNonpos := mul_nonpos_of_nonneg_of_nonpos hmu.le hdelta
    linarith
  have huLeMu : mu * (1 - alpha) ≤ mu := by
    have hdeltaLe : 1 - alpha ≤ 1 := by linarith
    simpa using mul_le_mul_of_nonneg_left hdeltaLe hmu.le
  have hmuOne : 1 < mu := hphase.trans_le huLeMu
  have hmuSub : 0 < mu - 1 := by linarith
  have hvSub : 0 < v - 1 := by linarith
  have hmuV : 0 < mu - v := by linarith
  have hRratio : ∀ᶠ T : ℝ in atTop, 2 ≤ T ^ (mu - 1) :=
    (tendsto_atTop.1 (tendsto_rpow_atTop hmuSub)) 2
  have hVratio : ∀ᶠ T : ℝ in atTop, 2 ≤ T ^ (v - 1) :=
    (tendsto_atTop.1 (tendsto_rpow_atTop hvSub)) 2
  have hNVratio : ∀ᶠ T : ℝ in atTop, 2 ≤ T ^ (mu - v) :=
    (tendsto_atTop.1 (tendsto_rpow_atTop hmuV)) 2
  refine ⟨j, hj, v, hvLower, hvUpper, Cloc, Ccell, hCloc, hCcell, ?_⟩
  filter_upwards [hcap, hdom, hRratio, hVratio, hNVratio,
    eventually_ge_atTop (3 : ℝ)] with T hcapT hdomT hRratioT hVratioT
      hNVratioT hT
  intro H D J Q hJ hJlog hD
  dsimp only
  intro hH hHR hRH hfull hP hQ
  let N : ℝ := T ^ mu
  let R : ℝ := N / (2 * T)
  let V : ℝ := T ^ v
  have hT0 : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hV0 : 0 < V := by dsimp only [V]; positivity
  have hNdecomp : N = T ^ (mu - 1) * T := by
    dsimp only [N]
    calc
      T ^ mu = T ^ ((mu - 1) + 1) := by congr 1; ring
      _ = T ^ (mu - 1) * T ^ (1 : ℝ) := Real.rpow_add hT0 _ _
      _ = T ^ (mu - 1) * T := by rw [Real.rpow_one]
  have hVdecomp : V = T ^ (v - 1) * T := by
    dsimp only [V]
    calc
      T ^ v = T ^ ((v - 1) + 1) := by congr 1; ring
      _ = T ^ (v - 1) * T ^ (1 : ℝ) := Real.rpow_add hT0 _ _
      _ = T ^ (v - 1) * T := by rw [Real.rpow_one]
  have hNVdecomp : N = T ^ (mu - v) * V := by
    dsimp only [N, V]
    calc
      T ^ mu = T ^ ((mu - v) + v) := by congr 1; ring
      _ = T ^ (mu - v) * T ^ v := Real.rpow_add hT0 _ _
  have hRone : 1 ≤ R := by
    dsimp only [R]
    rw [hNdecomp]
    have hTne : T ≠ 0 := hT0.ne'
    field_simp
    nlinarith
  have hwidth : R ≤ 2 * N / T := by
    dsimp only [R]
    field_simp
    nlinarith [hN0]
  have htransition : N / (2 * R) = T := by
    dsimp only [R]
    field_simp
  have hcentralLen : (1 : ℝ) + 2 ≤ N / (2 * R) := by
    rw [htransition]
    norm_num at hT ⊢
    exact hT
  have houterLen : N / (2 * R) + 2 ≤ V := by
    rw [htransition, hVdecomp]
    nlinarith [mul_le_mul_of_nonneg_right hVratioT hT0.le]
  have hTordTop : V + 1 ≤ N := by
    rw [hNVdecomp]
    have hVone : 1 ≤ V := by
      dsimp only [V]
      exact Real.one_le_rpow hTone (by linarith : 0 ≤ v)
    nlinarith [mul_le_mul_of_nonneg_right hNVratioT hV0.le]
  have hdomPair := hdomT hJ hJlog hD
  have hbaseCentral0 : 0 ≤ 32 * (N / (2 * R) - 1) * N ^ (alpha - 1) := by
    rw [htransition]
    positivity
  have hsurplus : 0 <
      routeTPhysicalSliceNatOrderLocalizationSurplus j Cloc N R 1 V D :=
    hbaseCentral0.trans_lt (by simpa only [N, R, V] using hdomPair.1)
  have hout := hcapT (H := H) (R := R) (U := 1) (V := V) (D := D)
    (Tord := N) (Q := Q) hH hRone hHR hRH hwidth (by norm_num)
    hcentralLen houterLen hTordTop hN0.le (le_refl N) hsurplus
    (by simpa only [N, R] using hfull) (by simpa only [N, R] using hP) hQ
  rcases hout with hbaseCentral | hbaseOuter | hhigh
  · exact False.elim ((not_le_of_gt (by simpa only [N, R, V] using hdomPair.1))
      hbaseCentral)
  · exact False.elim ((not_le_of_gt (by simpa only [N, R, V] using hdomPair.2))
      hbaseOuter)
  · simpa only [N, R, V] using hhigh

end RHTower.Sieve
