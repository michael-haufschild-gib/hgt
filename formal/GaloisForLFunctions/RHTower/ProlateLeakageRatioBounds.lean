import GaloisForLFunctions.RHTower.ProlateIndexedLeakageTwoSided
import GaloisForLFunctions.RHTower.BandEndpointPhaseTurning

/-!
# Reducing the two leakage bounds to a power of the bandwidth times the action

The two-sided leakage estimate is explicit but heavy.  For the ladder only its *shape* matters:

```text
prolateLeakageUpper c s  ≤  A · c · exp(−2c·Ξ_s(2√s)) ,
prolateLeakageLower c s  ≥  B · s · c⁻¹ · exp(−2c(1 + (s/4)·log s)) .
```

Every factor that is dropped is bounded once `c ≥ 8` and `s ≤ 1/64`: the collar phase by its sharp
endpoint bound, the transport loss across `[2√s, 2√s + c⁻¹]` because the width is one inverse
bandwidth, the collar logarithms because the collar is fixed, and the barrier factor because the
radial barrier is `c` times a bounded quantity, so the barrier term is `O(1)` after division by `c²`.
-/

noncomputable section

set_option maxHeartbeats 2000000

open Set Filter Topology

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- The constant absorbed into the upper leakage bound. -/
def leakageUpperConst : ℝ :=
  36 * Real.pi ^ (2 : ℕ) * radialProlateExteriorMassConstant
    * (2 * Real.sqrt (1 - prolateLeakageCollar)) * Real.exp 5
    * (1 / (1 - prolateLeakageCollar)) ^ (12 : ℕ)

theorem leakageUpperConst_nonneg : 0 ≤ leakageUpperConst := by
  rw [leakageUpperConst]
  have h1 : (0 : ℝ) ≤ radialProlateExteriorMassConstant :=
    radialProlateExteriorMassConstant_nonneg
  have h2 : (0 : ℝ) < 1 - prolateLeakageCollar := by
    rw [prolateLeakageCollar]; norm_num
  positivity

/-- **The upper leakage bound is a bandwidth times the action.** -/
theorem prolateLeakageUpper_le {c s : ℝ} (hc : 8 ≤ c) (hs0 : 0 < s) (hs : s ≤ 1 / 64) :
    prolateLeakageUpper c s
      ≤ leakageUpperConst * c * Real.exp (-(2 * c * bandEndpointPhase s (2 * Real.sqrt s))) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hα0 : (0 : ℝ) < 1 - prolateLeakageCollar := by
    rw [prolateLeakageCollar]; norm_num
  have hα1 : prolateLeakageCollar ≤ 1 := by rw [prolateLeakageCollar]; norm_num
  have hαpos : (0 : ℝ) ≤ prolateLeakageCollar := by rw [prolateLeakageCollar]; norm_num
  have hsq0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hsqle : Real.sqrt s ≤ 1 / 8 := by
    have h := Real.sqrt_le_sqrt hs
    have h8 : Real.sqrt ((1 : ℝ) / 64) = 1 / 8 := by
      rw [show (1 : ℝ) / 64 = (1 / 8) ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h8] at h
  have hcut : prolateLeakageCut c s = 2 * Real.sqrt s + 1 / c := rfl
  have hcinv : 1 / c ≤ 1 / 8 := by
    rw [div_le_div_iff₀ hc0 (by norm_num : (0 : ℝ) < 8)]
    linarith
  have hcinv0 : (0 : ℝ) < 1 / c := by positivity
  have hcutpos : 0 < prolateLeakageCut c s := by
    rw [hcut]; positivity
  have hcutle : prolateLeakageCut c s ≤ 3 / 8 := by
    rw [hcut]; linarith
  have hwidth : prolateLeakageCut c s - 2 * Real.sqrt s = 1 / c := by
    rw [hcut]; ring
  -- the collar phase
  have hphaseα : bandEndpointPhase s prolateLeakageCollar
      ≤ 2 * Real.sqrt (1 - prolateLeakageCollar) := by
    refine le_trans (bandEndpointPhase_le_sharp hαpos hα1) ?_
    have h1 : Real.sqrt (1 - s) ≤ 1 := by
      have h := Real.sqrt_le_sqrt (show (1 : ℝ) - s ≤ 1 by linarith)
      rwa [Real.sqrt_one] at h
    have h2 : (1 : ℝ) ≤ Real.sqrt (1 + prolateLeakageCollar) := by
      have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + prolateLeakageCollar by linarith)
      rwa [Real.sqrt_one] at h
    have h3 : 0 < Real.sqrt (1 + prolateLeakageCollar) := by linarith
    have h4 : 2 * Real.sqrt (1 - prolateLeakageCollar) / Real.sqrt (1 + prolateLeakageCollar)
        ≤ 2 * Real.sqrt (1 - prolateLeakageCollar) := by
      rw [div_le_iff₀ h3]
      nlinarith [Real.sqrt_nonneg (1 - prolateLeakageCollar), h2]
    nlinarith [Real.sqrt_nonneg (1 - s), Real.sqrt_nonneg (1 - prolateLeakageCollar), h1, h4,
      div_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt (1 - prolateLeakageCollar)) h3.le]
  have hphaseα0 : 0 ≤ bandEndpointPhase s prolateLeakageCollar :=
    bandEndpointPhase_nonneg _ _
  -- the transport loss
  have hloss : 2 * ((c * prolateLeakageCut c s + 12) * (1 / c)
      / (1 - prolateLeakageCut c s ^ (2 : ℕ))) ≤ 5 := by
    have hden : (55 : ℝ) / 64 ≤ 1 - prolateLeakageCut c s ^ (2 : ℕ) := by
      nlinarith [hcutle, hcutpos]
    have hdenpos : (0 : ℝ) < 1 - prolateLeakageCut c s ^ (2 : ℕ) := by linarith
    have hnum : c * prolateLeakageCut c s + 12 = 2 * c * Real.sqrt s + 13 := by
      rw [hcut]
      field_simp
      ring
    have hnumle : (c * prolateLeakageCut c s + 12) * (1 / c) ≤ 2 * Real.sqrt s + 13 / 8 := by
      rw [hnum]
      have : (2 * c * Real.sqrt s + 13) * (1 / c) = 2 * Real.sqrt s + 13 * (1 / c) := by
        field_simp
      rw [this]
      nlinarith [hcinv]
    have hbound : 2 * Real.sqrt s + 13 / 8 ≤ 2 := by linarith
    have hpos : (0 : ℝ) ≤ (c * prolateLeakageCut c s + 12) * (1 / c) := by
      rw [hnum]
      positivity
    have hX : (c * prolateLeakageCut c s + 12) * (1 / c) ≤ 2 := le_trans hnumle hbound
    have hratio : (c * prolateLeakageCut c s + 12) * (1 / c) / (1 - prolateLeakageCut c s ^ (2 : ℕ))
        ≤ 2 / (55 / 64) := div_le_div₀ (by norm_num) hX (by norm_num) hden
    linarith [hratio]
  -- the collar logarithms
  have hlogfac : Real.exp (-(2 * (6 * (Real.log (1 - prolateLeakageCollar)
      - Real.log (1 - 2 * Real.sqrt s))))) ≤ (1 / (1 - prolateLeakageCollar)) ^ (12 : ℕ) := by
    have hb : (0 : ℝ) < 1 - 2 * Real.sqrt s := by linarith
    have hexp : Real.exp (-(2 * (6 * (Real.log (1 - prolateLeakageCollar)
        - Real.log (1 - 2 * Real.sqrt s)))))
        = ((1 - 2 * Real.sqrt s) / (1 - prolateLeakageCollar)) ^ (12 : ℕ) := by
      have hlog : Real.log (((1 - 2 * Real.sqrt s) / (1 - prolateLeakageCollar)) ^ (12 : ℕ))
          = -(2 * (6 * (Real.log (1 - prolateLeakageCollar)
            - Real.log (1 - 2 * Real.sqrt s)))) := by
        rw [Real.log_pow, Real.log_div (ne_of_gt hb) (ne_of_gt hα0)]
        push_cast
        ring
      rw [← hlog, Real.exp_log (by positivity)]
    rw [hexp]
    have hle : (1 - 2 * Real.sqrt s) / (1 - prolateLeakageCollar)
        ≤ 1 / (1 - prolateLeakageCollar) := by
      rw [div_le_div_iff₀ hα0 hα0]
      nlinarith [hsq0, hα0]
    exact pow_le_pow_left₀ (by positivity) hle 12
  -- assemble
  have hEnn : (0 : ℝ) ≤ radialProlateExteriorMassConstant :=
    radialProlateExteriorMassConstant_nonneg
  have hsq : (6 * Real.pi * Real.sqrt (c * bandEndpointPhase s prolateLeakageCollar)) ^ (2 : ℕ)
      = 36 * Real.pi ^ (2 : ℕ) * (c * bandEndpointPhase s prolateLeakageCollar) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hsplit : Real.exp (-(2 * (c * bandEndpointPhase s (2 * Real.sqrt s)
        + 6 * (Real.log (1 - prolateLeakageCollar) - Real.log (1 - 2 * Real.sqrt s)))))
      = Real.exp (-(2 * c * bandEndpointPhase s (2 * Real.sqrt s)))
        * Real.exp (-(2 * (6 * (Real.log (1 - prolateLeakageCollar)
            - Real.log (1 - 2 * Real.sqrt s))))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [prolateLeakageUpper, hsq, hwidth, hsplit, leakageUpperConst]
  set Lloss : ℝ := 2 * ((c * prolateLeakageCut c s + 12) * (1 / c)
    / (1 - prolateLeakageCut c s ^ (2 : ℕ))) with hLlossdef
  set G : ℝ := Real.exp (-(2 * (6 * (Real.log (1 - prolateLeakageCollar)
    - Real.log (1 - 2 * Real.sqrt s))))) with hGdef
  set Ξ : ℝ := Real.exp (-(2 * c * bandEndpointPhase s (2 * Real.sqrt s))) with hΞdef
  have hΞ0 : 0 < Ξ := Real.exp_pos _
  have hG0 : 0 < G := Real.exp_pos _
  have hLHS : radialProlateExteriorMassConstant / c
      * (36 * Real.pi ^ (2 : ℕ) * (c * bandEndpointPhase s prolateLeakageCollar)
        * Real.exp Lloss / (1 / c)) * (Ξ * G)
      = (36 * Real.pi ^ (2 : ℕ) * radialProlateExteriorMassConstant
        * (bandEndpointPhase s prolateLeakageCollar * (Real.exp Lloss * G))) * (c * Ξ) := by
    field_simp
  have hRHS : 36 * Real.pi ^ (2 : ℕ) * radialProlateExteriorMassConstant
      * (2 * Real.sqrt (1 - prolateLeakageCollar)) * Real.exp 5
      * (1 / (1 - prolateLeakageCollar)) ^ (12 : ℕ) * c * Ξ
      = (36 * Real.pi ^ (2 : ℕ) * radialProlateExteriorMassConstant
        * ((2 * Real.sqrt (1 - prolateLeakageCollar))
          * (Real.exp 5 * (1 / (1 - prolateLeakageCollar)) ^ (12 : ℕ)))) * (c * Ξ) := by
    ring
  rw [hLHS, hRHS]
  have hcΞ : (0 : ℝ) ≤ c * Ξ := by positivity
  refine mul_le_mul_of_nonneg_right ?_ hcΞ
  have hfac : bandEndpointPhase s prolateLeakageCollar * (Real.exp Lloss * G)
      ≤ (2 * Real.sqrt (1 - prolateLeakageCollar))
        * (Real.exp 5 * (1 / (1 - prolateLeakageCollar)) ^ (12 : ℕ)) := by
    have hexpL : Real.exp Lloss ≤ Real.exp 5 := Real.exp_le_exp.2 hloss
    have hGle : G ≤ (1 / (1 - prolateLeakageCollar)) ^ (12 : ℕ) := hlogfac
    have hpow0 : (0 : ℝ) ≤ (1 / (1 - prolateLeakageCollar)) ^ (12 : ℕ) := by positivity
    have hexp0 : (0 : ℝ) ≤ Real.exp Lloss := (Real.exp_pos _).le
    have h1 : Real.exp Lloss * G ≤ Real.exp 5 * (1 / (1 - prolateLeakageCollar)) ^ (12 : ℕ) := by
      calc Real.exp Lloss * G ≤ Real.exp Lloss * (1 / (1 - prolateLeakageCollar)) ^ (12 : ℕ) :=
            mul_le_mul_of_nonneg_left hGle hexp0
        _ ≤ Real.exp 5 * (1 / (1 - prolateLeakageCollar)) ^ (12 : ℕ) :=
            mul_le_mul_of_nonneg_right hexpL hpow0
    have h2 : (0 : ℝ) ≤ Real.exp 5 * (1 / (1 - prolateLeakageCollar)) ^ (12 : ℕ) := by positivity
    calc bandEndpointPhase s prolateLeakageCollar * (Real.exp Lloss * G)
        ≤ bandEndpointPhase s prolateLeakageCollar
            * (Real.exp 5 * (1 / (1 - prolateLeakageCollar)) ^ (12 : ℕ)) :=
          mul_le_mul_of_nonneg_left h1 hphaseα0
      _ ≤ (2 * Real.sqrt (1 - prolateLeakageCollar))
            * (Real.exp 5 * (1 / (1 - prolateLeakageCollar)) ^ (12 : ℕ)) :=
          mul_le_mul_of_nonneg_right hphaseα h2
  exact mul_le_mul_of_nonneg_left hfac (by positivity)

/-! ## The lower bound -/

/-- A bound for the barrier factor of the lower leakage bound. -/
def leakageBarrierConst : ℝ := 4 + 5 / (1 - prolateLeakageCollar)

theorem leakageBarrierConst_nonneg : 0 ≤ leakageBarrierConst := by
  have h : (0 : ℝ) < 1 - prolateLeakageCollar := by rw [prolateLeakageCollar]; norm_num
  rw [leakageBarrierConst]
  positivity

/-- **The barrier factor is bounded.** -/
theorem barrierFactor_le {c s : ℝ} (hc : 8 ≤ c) (hs0 : 0 < s) (hs : s ≤ 1 / 64) :
    (1 - prolateLeakageCollar ^ (2 : ℕ))
        * (prolateRadialBarrier c s prolateLeakageCollar + 6 / (1 - prolateLeakageCollar)) ^ (2 : ℕ)
        / (c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - s))
      ≤ leakageBarrierConst := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hα0 : (0 : ℝ) < 1 - prolateLeakageCollar := by rw [prolateLeakageCollar]; norm_num
  have hαsq : (999 : ℝ) / 1000 ≤ prolateLeakageCollar ^ (2 : ℕ) := by
    rw [prolateLeakageCollar]; norm_num
  have hαsq1 : prolateLeakageCollar ^ (2 : ℕ) ≤ 1 := by rw [prolateLeakageCollar]; norm_num
  have hgap : (1 : ℝ) / 2 ≤ prolateLeakageCollar ^ (2 : ℕ) - s := by linarith
  have hgap0 : (0 : ℝ) < prolateLeakageCollar ^ (2 : ℕ) - s := by linarith
  have hone : (0 : ℝ) < 1 - prolateLeakageCollar ^ (2 : ℕ) := by
    have : prolateLeakageCollar ^ (2 : ℕ) < 1 := by rw [prolateLeakageCollar]; norm_num
    linarith
  have hs1 : (0 : ℝ) ≤ 1 - s := by linarith
  set A : ℝ := prolateRadialBarrier c s prolateLeakageCollar with hA
  set B : ℝ := 6 / (1 - prolateLeakageCollar) with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  have hA0 : 0 ≤ A := by
    rw [hA, prolateRadialBarrier]
    have hαpos : (0 : ℝ) ≤ prolateLeakageCollar := by rw [prolateLeakageCollar]; norm_num
    positivity
  have hAsq : A ^ (2 : ℕ) * (1 - prolateLeakageCollar ^ (2 : ℕ))
      = c ^ (2 : ℕ) * (1 - s) * prolateLeakageCollar ^ (2 : ℕ) := by
    rw [hA, prolateRadialBarrier, div_pow, mul_pow, mul_pow]
    rw [Real.sq_sqrt hs1, Real.sq_sqrt hone.le]
    field_simp
  have hsplit : (A + B) ^ (2 : ℕ) ≤ 2 * A ^ (2 : ℕ) + 2 * B ^ (2 : ℕ) := by nlinarith [sq_nonneg (A - B)]
  have hden0 : (0 : ℝ) < c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - s) := by positivity
  rw [div_le_iff₀ hden0, leakageBarrierConst]
  have hterm1 : 2 * (A ^ (2 : ℕ) * (1 - prolateLeakageCollar ^ (2 : ℕ)))
      ≤ 4 * (c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - s)) := by
    rw [hAsq]
    have h1 : (1 - s) * prolateLeakageCollar ^ (2 : ℕ) ≤ 1 := by nlinarith [hαsq1, hs1, hs0]
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg c),
      mul_le_mul_of_nonneg_left hgap (sq_nonneg c)]
  have hterm2 : 2 * (B ^ (2 : ℕ) * (1 - prolateLeakageCollar ^ (2 : ℕ)))
      ≤ 5 / (1 - prolateLeakageCollar) * (c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - s)) := by
    have hBsq : B ^ (2 : ℕ) = 36 / (1 - prolateLeakageCollar) ^ (2 : ℕ) := by
      rw [hB, div_pow]
      norm_num
    have hcs : (64 : ℝ) ≤ c ^ (2 : ℕ) := by nlinarith
    have hup : (1 : ℝ) - prolateLeakageCollar ^ (2 : ℕ) ≤ 2 * (1 - prolateLeakageCollar) := by
      have : prolateLeakageCollar ≤ 1 := by rw [prolateLeakageCollar]; norm_num
      nlinarith
    rw [hBsq]
    have hlhs : 2 * (36 / (1 - prolateLeakageCollar) ^ (2 : ℕ) * (1 - prolateLeakageCollar ^ (2 : ℕ)))
        ≤ 144 / (1 - prolateLeakageCollar) := by
      rw [le_div_iff₀ hα0]
      have hid : 2 * (36 / (1 - prolateLeakageCollar) ^ (2 : ℕ) * (1 - prolateLeakageCollar ^ (2 : ℕ)))
            * (1 - prolateLeakageCollar)
          = 72 * (1 - prolateLeakageCollar ^ (2 : ℕ)) / (1 - prolateLeakageCollar) := by
        field_simp
        ring
      rw [hid, div_le_iff₀ hα0]
      nlinarith [hup, hα0]
    have hrhs : (144 : ℝ) / (1 - prolateLeakageCollar)
        ≤ 5 / (1 - prolateLeakageCollar) * (c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - s)) := by
      have hfac : (144 : ℝ) ≤ 5 * (c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - s)) := by
        nlinarith [mul_le_mul_of_nonneg_left hgap (by positivity : (0:ℝ) ≤ c ^ (2 : ℕ)), hcs]
      have hid : 5 / (1 - prolateLeakageCollar) * (c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - s))
          = 5 * (c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - s)) / (1 - prolateLeakageCollar) := by
        ring
      rw [hid, div_le_div_iff₀ hα0 hα0]
      nlinarith [hfac, hα0]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hsplit hone.le, hterm1, hterm2]

/-- The constant of the lower leakage bound. -/
def leakageLowerConst : ℝ :=
  besselEnergyFloor * 3 * (1 - prolateLeakageCollar ^ (2 : ℕ))
    / (3456 * (3 * (1 + leakageBarrierConst) + 1))

theorem leakageLowerConst_pos : 0 < leakageLowerConst := by
  have hF : 0 < besselEnergyFloor := besselEnergyFloor_pos
  have hone : (0 : ℝ) < 1 - prolateLeakageCollar ^ (2 : ℕ) := by
    have : prolateLeakageCollar ^ (2 : ℕ) < 1 := by rw [prolateLeakageCollar]; norm_num
    linarith
  have hW : 0 ≤ leakageBarrierConst := leakageBarrierConst_nonneg
  rw [leakageLowerConst]
  positivity

/-- **The lower leakage bound is a separation over a bandwidth times the action.** -/
theorem prolateLeakageLower_ge {c s : ℝ} (hc : 8 ≤ c) (hs0 : 0 < s) (hs : s ≤ 1 / 64) :
    leakageLowerConst * (s / c)
        * Real.exp (-(2 * c * (1 + s / 4 * Real.log s) + 10 * (c * s)))
      ≤ prolateLeakageLower c s := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hF : 0 < besselEnergyFloor := besselEnergyFloor_pos
  have hαsq : (999 : ℝ) / 1000 ≤ prolateLeakageCollar ^ (2 : ℕ) := by
    rw [prolateLeakageCollar]; norm_num
  have hαsq1 : prolateLeakageCollar ^ (2 : ℕ) < 1 := by rw [prolateLeakageCollar]; norm_num
  have hone : (0 : ℝ) < 1 - prolateLeakageCollar ^ (2 : ℕ) := by linarith
  have hgap0 : (0 : ℝ) < prolateLeakageCollar ^ (2 : ℕ) - s := by linarith
  have hgap1 : prolateLeakageCollar ^ (2 : ℕ) - s ≤ 1 := by linarith
  have hfour : (0 : ℝ) < 1 - 4 * s := by linarith
  have hfour1 : (1 : ℝ) - 4 * s ≤ 1 := by linarith
  set Wfac : ℝ := (1 - prolateLeakageCollar ^ (2 : ℕ))
      * (prolateRadialBarrier c s prolateLeakageCollar + 6 / (1 - prolateLeakageCollar)) ^ (2 : ℕ)
      / (c ^ (2 : ℕ) * (prolateLeakageCollar ^ (2 : ℕ) - s)) with hWdef
  have hW0 : 0 ≤ Wfac := by
    rw [hWdef]
    positivity
  have hWle : Wfac ≤ leakageBarrierConst := barrierFactor_le hc hs0 hs
  set A : ℝ := 2 * c * (1 + s / 4 * Real.log s) + 10 * (c * s) with hAdef
  set Bexp : ℝ := (Real.log (prolateLeakageCollar ^ (2 : ℕ) - s) - Real.log (3 * s))
      + (Real.log (1 - 4 * s) - Real.log (1 - prolateLeakageCollar ^ (2 : ℕ))) with hBdef
  have hM : 2 * c * (1 + s / 4 * Real.log s)
      + ((Real.log (prolateLeakageCollar ^ (2 : ℕ) - s) - Real.log (3 * s))
        + (Real.log (1 - 4 * s) - Real.log (1 - prolateLeakageCollar ^ (2 : ℕ))))
      + 10 * (c * s) = A + Bexp := by
    rw [hAdef, hBdef]; ring
  have hBval : Real.exp Bexp
      = (prolateLeakageCollar ^ (2 : ℕ) - s) / (3 * s)
        * ((1 - 4 * s) / (1 - prolateLeakageCollar ^ (2 : ℕ))) := by
    rw [hBdef, ← Real.log_div (ne_of_gt hgap0) (by positivity),
      ← Real.log_div (ne_of_gt hfour) (ne_of_gt hone),
      ← Real.log_mul (by positivity) (by positivity), Real.exp_log (by positivity)]
  have hBle : Real.exp Bexp ≤ 1 / (3 * s * (1 - prolateLeakageCollar ^ (2 : ℕ))) := by
    rw [hBval]
    have h1 : (prolateLeakageCollar ^ (2 : ℕ) - s) / (3 * s) ≤ 1 / (3 * s) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hgap1, hs0]
    have h2 : (1 - 4 * s) / (1 - prolateLeakageCollar ^ (2 : ℕ)) ≤ 1 / (1 - prolateLeakageCollar ^ (2 : ℕ)) := by
      rw [div_le_div_iff₀ hone hone]
      nlinarith [hfour1, hone]
    have h3 : (0 : ℝ) ≤ (1 - 4 * s) / (1 - prolateLeakageCollar ^ (2 : ℕ)) := by positivity
    have h4 : (0 : ℝ) ≤ 1 / (3 * s) := by positivity
    have hid : 1 / (3 * s) * (1 / (1 - prolateLeakageCollar ^ (2 : ℕ)))
        = 1 / (3 * s * (1 - prolateLeakageCollar ^ (2 : ℕ))) := by
      field_simp
    calc (prolateLeakageCollar ^ (2 : ℕ) - s) / (3 * s) * ((1 - 4 * s) / (1 - prolateLeakageCollar ^ (2 : ℕ)))
        ≤ 1 / (3 * s) * ((1 - 4 * s) / (1 - prolateLeakageCollar ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_right h1 h3
      _ ≤ 1 / (3 * s) * (1 / (1 - prolateLeakageCollar ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_left h2 h4
      _ = 1 / (3 * s * (1 - prolateLeakageCollar ^ (2 : ℕ))) := hid
  -- the denominator
  set Wc : ℝ := 3 * (1 + leakageBarrierConst) + 1 with hWcdef
  have hWc0 : 0 < Wc := by
    have := leakageBarrierConst_nonneg
    rw [hWcdef]; linarith
  have hD0 : 0 < 2 * (2 * (3 * (1 + Wfac) + 1) * Real.exp (A + Bexp)) := by
    have : 0 < 3 * (1 + Wfac) + 1 := by linarith
    positivity
  have hDle : 2 * (2 * (3 * (1 + Wfac) + 1) * Real.exp (A + Bexp))
      ≤ 4 * Wc * (Real.exp A / (3 * s * (1 - prolateLeakageCollar ^ (2 : ℕ)))) := by
    have hfac : 3 * (1 + Wfac) + 1 ≤ Wc := by rw [hWcdef]; linarith
    have hexp : Real.exp (A + Bexp)
        ≤ Real.exp A / (3 * s * (1 - prolateLeakageCollar ^ (2 : ℕ))) := by
      rw [Real.exp_add]
      have hA0 : (0 : ℝ) < Real.exp A := Real.exp_pos _
      calc Real.exp A * Real.exp Bexp
          ≤ Real.exp A * (1 / (3 * s * (1 - prolateLeakageCollar ^ (2 : ℕ)))) :=
            mul_le_mul_of_nonneg_left hBle hA0.le
        _ = Real.exp A / (3 * s * (1 - prolateLeakageCollar ^ (2 : ℕ))) := by ring
    have hexp0 : (0 : ℝ) < Real.exp (A + Bexp) := Real.exp_pos _
    have hnn : (0 : ℝ) ≤ 3 * (1 + Wfac) + 1 := by linarith
    nlinarith [hfac, hexp, hexp0, hnn, hWc0]
  have hnum : (0 : ℝ) < besselEnergyFloor / 864 / c := by positivity
  have hlow : besselEnergyFloor / 864 / c
      / (4 * Wc * (Real.exp A / (3 * s * (1 - prolateLeakageCollar ^ (2 : ℕ)))))
      ≤ besselEnergyFloor / 864 / c / (2 * (2 * (3 * (1 + Wfac) + 1) * Real.exp (A + Bexp))) :=
    div_le_div_of_nonneg_left hnum.le hD0 hDle
  have hval : besselEnergyFloor / 864 / c
      / (4 * Wc * (Real.exp A / (3 * s * (1 - prolateLeakageCollar ^ (2 : ℕ)))))
      = leakageLowerConst * (s / c) * Real.exp (-A) := by
    rw [leakageLowerConst, hWcdef, Real.exp_neg]
    field_simp
    ring
  have hLowerEq : prolateLeakageLower c s
      = besselEnergyFloor / 864 / c
        / (2 * (2 * (3 * (1 + Wfac) + 1) * Real.exp (A + Bexp))) := by
    rw [hWdef, ← hM, prolateLeakageLower]
  rw [hLowerEq]
  refine le_trans (le_of_eq ?_) hlow
  exact hval.symm

/-! ## The action as a power of the bandwidth -/

/-- The bandwidth-free part of the upper action, a function of `T = c·s` alone. -/
def phaseTail (K T : ℝ) : ℝ :=
  8 * T + 2 * K ^ (2 : ℕ) * T + (T / Real.sqrt (1 - 1 / K ^ (2 : ℕ))) * (Real.log 2 - Real.log K)
    - (T / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ)))) * Real.log T

private theorem phaseTail_algebra (c s K r L2 LK Lcs Lc : ℝ) (hr : r ≠ 0) :
    2 * c * (4 * s + K ^ (2 : ℕ) * s + s / (2 * r) * (L2 - (LK + (Lcs - Lc) / 2)))
      = 8 * (c * s) + 2 * K ^ (2 : ℕ) * (c * s) + ((c * s) / r) * (L2 - LK)
        - ((c * s) / (2 * r)) * Lcs + ((c * s) / (2 * r)) * Lc := by
  field_simp
  ring

/-- **The upper action is a power of the bandwidth times `e^{−2c}`.**  The exponent of the
bandwidth is `c·s / (2√(1−K⁻²))`, which approaches half the separation constant. -/
theorem exp_neg_two_mul_phase_le {c s K : ℝ} (hc : 8 ≤ c) (hs0 : 0 < s)
    (hK : 2 ≤ K) (hKs : K * Real.sqrt s ≤ 1 / 2) :
    Real.exp (-(2 * c * bandEndpointPhase s (2 * Real.sqrt s)))
      ≤ Real.exp (-(2 * c)) * Real.exp (phaseTail K (c * s))
        * Real.exp ((c * s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ)))) * Real.log c) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hK0 : (0 : ℝ) < K := by linarith
  have hsq0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hfracpos : (0 : ℝ) < 1 - 1 / K ^ (2 : ℕ) := by
    have hK2 : (4 : ℝ) ≤ K ^ (2 : ℕ) := by nlinarith
    have hK2p : (0 : ℝ) < K ^ (2 : ℕ) := by positivity
    rw [sub_pos, div_lt_one hK2p]
    linarith
  have hrt : 0 < Real.sqrt (1 - 1 / K ^ (2 : ℕ)) := Real.sqrt_pos.2 hfracpos
  have hphase := one_sub_bandEndpointPhase_turning_le hs0 hK hKs
  -- the logarithmic identity
  have hlogKs : Real.log (K * Real.sqrt s) = Real.log K + (Real.log (c * s) - Real.log c) / 2 := by
    rw [Real.log_mul (ne_of_gt hK0) (ne_of_gt hsq0), Real.log_sqrt hs0.le]
    have hs : Real.log s = Real.log (c * s) - Real.log c := by
      rw [Real.log_mul (ne_of_gt hc0) (ne_of_gt hs0)]
      ring
    rw [hs]
  have hkey : 2 * c * (1 - bandEndpointPhase s (2 * Real.sqrt s))
      ≤ phaseTail K (c * s) + (c * s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ)))) * Real.log c := by
    have hmul := mul_le_mul_of_nonneg_left hphase (by positivity : (0 : ℝ) ≤ 2 * c)
    refine le_trans hmul ?_
    rw [phaseTail, hlogKs]
    exact le_of_eq (phaseTail_algebra c s K (Real.sqrt (1 - 1 / K ^ (2 : ℕ))) (Real.log 2)
      (Real.log K) (Real.log (c * s)) (Real.log c) (ne_of_gt hrt))
  have hexp : -(2 * c * bandEndpointPhase s (2 * Real.sqrt s))
      ≤ -(2 * c) + phaseTail K (c * s)
        + (c * s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ)))) * Real.log c := by
    nlinarith [hkey]
  calc Real.exp (-(2 * c * bandEndpointPhase s (2 * Real.sqrt s)))
      ≤ Real.exp (-(2 * c) + phaseTail K (c * s)
          + (c * s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ)))) * Real.log c) := Real.exp_le_exp.2 hexp
    _ = Real.exp (-(2 * c)) * Real.exp (phaseTail K (c * s))
          * Real.exp ((c * s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ)))) * Real.log c) := by
        rw [Real.exp_add, Real.exp_add]

/-- **The lower action, exactly.**  Its bandwidth exponent is half the separation constant. -/
theorem exp_lower_action_eq {c s : ℝ} (hc0 : 0 < c) (hs0 : 0 < s) :
    Real.exp (-(2 * c * (1 + s / 4 * Real.log s) + 10 * (c * s)))
      = Real.exp (-(2 * c)) * Real.exp (-(10 * (c * s)) - (c * s / 2) * Real.log (c * s))
        * Real.exp ((c * s / 2) * Real.log c) := by
  have hs : Real.log s = Real.log (c * s) - Real.log c := by
    rw [Real.log_mul (ne_of_gt hc0) (ne_of_gt hs0)]
    ring
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [hs]
  ring

end GaloisForLFunctions.RHTower

end
