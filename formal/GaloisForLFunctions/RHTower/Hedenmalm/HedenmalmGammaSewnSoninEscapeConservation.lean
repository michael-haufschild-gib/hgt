import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnXiKadisonReceiverNoGo
import GaloisForLFunctions.RHTower.GammaCoPoissonSoninActualZeroEscape
import GaloisForLFunctions.RHTower.BurnolSoninEvaluationNonvanishing

/-!
# Route N fracture is reciprocal Sonin conormal escape

The Route N projective/Kadison survival mass is not deleted by the Gamma/co-Poisson/Sonin
completion.  Its square root is exactly the inward-oriented Sonin ladder character.  The
reciprocal squared character is the complementary conormal escape amplification, so

`(1 - D_t(p)) * A_t(p) = 1`.

Equivalently, projective defect odds are precisely excess Sonin escape.  At an actual
right-half-strip zeta zero, the same identity converts contractivity of the forward co-Poisson
bonding map into an exact defect-weighted one-step norm-growth law.  This is a conservation
theorem, not an RH proof: off-line fracture survives by moving from the positive projective
reporter into the escaping conormal corona.
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

/-- Inward-oriented Sonin character attached to the absolute Route N radial grade. -/
def routeNGammaSewnInwardSoninCharacter
    (t : ℝ) (p : Nat.Primes) : ℂ :=
  soninLadderCharacter (((1 / 2 - |t| : ℝ) : ℂ)) (p : ℝ)

/-- The inward Sonin character has exactly the critical half-density amplitude. -/
theorem norm_routeNGammaSewnInwardSoninCharacter
    (t : ℝ) (p : Nat.Primes) :
    ‖routeNGammaSewnInwardSoninCharacter t p‖ =
      (p : ℝ) ^ (-|t|) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [routeNGammaSewnInwardSoninCharacter,
    norm_soninLadderCharacter hp0]
  norm_num

/-- **Projective/Sonin survival identity.**  Route N multiplicative-domain survival is the
squared inward Sonin ladder amplitude. -/
theorem normSq_routeNGammaSewnInwardSoninCharacter_eq_survival
    (t : ℝ) (p : Nat.Primes) :
    ‖routeNGammaSewnInwardSoninCharacter t p‖ ^ 2 =
      1 - routeNGammaSewnProjectiveKadisonDefect t p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [norm_routeNGammaSewnInwardSoninCharacter,
    one_sub_routeNGammaSewnProjectiveKadisonDefect,
    routeNGammaSewnTransverseModularCocycle,
    routeNGammaSewnTransverseModularClockCocycle,
    pow_two, ← Real.rpow_add hp0]
  congr 1
  ring

/-- Complementary co-Poisson/Sonin conormal escape forced by one Route N radial grade. -/
def routeNGammaSewnSoninEscapeAmplification
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  ‖routeNGammaSewnInwardSoninCharacter t p‖⁻¹ ^ 2

/-- Escape amplification is the outward radial character. -/
theorem routeNGammaSewnSoninEscapeAmplification_eq_rpow
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnSoninEscapeAmplification t p =
      (p : ℝ) ^ (2 * |t|) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [routeNGammaSewnSoninEscapeAmplification,
    norm_routeNGammaSewnInwardSoninCharacter,
    ← Real.rpow_neg hp0.le, pow_two, ← Real.rpow_add hp0]
  congr 1
  ring

/-- **Defect--escape conservation.**  Projective survival and complementary Sonin escape are
exact reciprocals. -/
theorem routeNGammaSewnKadisonSurvival_mul_soninEscape_eq_one
    (t : ℝ) (p : Nat.Primes) :
    (1 - routeNGammaSewnProjectiveKadisonDefect t p) *
      routeNGammaSewnSoninEscapeAmplification t p = 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [one_sub_routeNGammaSewnProjectiveKadisonDefect,
    routeNGammaSewnTransverseModularCocycle,
    routeNGammaSewnTransverseModularClockCocycle,
    routeNGammaSewnSoninEscapeAmplification_eq_rpow,
    ← Real.rpow_add hp0]
  norm_num

/-- Projective defect odds are exactly excess Sonin conormal escape. -/
theorem routeNGammaSewnKadisonDefect_odds_eq_soninEscape_sub_one
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnProjectiveKadisonDefect t p /
        (1 - routeNGammaSewnProjectiveKadisonDefect t p) =
      routeNGammaSewnSoninEscapeAmplification t p - 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hsurv0 : 1 - routeNGammaSewnProjectiveKadisonDefect t p ≠ 0 := by
    rw [one_sub_routeNGammaSewnProjectiveKadisonDefect,
      routeNGammaSewnTransverseModularCocycle,
      routeNGammaSewnTransverseModularClockCocycle]
    exact ne_of_gt (Real.rpow_pos_of_pos hp0 _)
  rw [div_eq_iff hsurv0]
  have hconserve :=
    routeNGammaSewnKadisonSurvival_mul_soninEscape_eq_one t p
  nlinarith

/-- The logarithmic Sonin escape grade is the opposite of the C20 projective survival grade. -/
theorem log_routeNGammaSewnSoninEscapeAmplification_div
    (t : ℝ) (p : Nat.Primes) :
    Real.log (routeNGammaSewnSoninEscapeAmplification t p) /
        (2 * Real.log (p : ℝ)) = |t| := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast p.2.one_lt))
  rw [routeNGammaSewnSoninEscapeAmplification_eq_rpow,
    Real.log_rpow hp0]
  field_simp [hlog]

/-- On the right half-strip, the actual outward Sonin character is reciprocal to Route N
projective survival. -/
theorem routeNGammaSewnKadisonSurvival_mul_rightSoninCharacter_sq
    {w : ℂ} (hw : 1 / 2 ≤ w.re) (p : Nat.Primes) :
    (1 - routeNGammaSewnProjectiveKadisonDefect
      (w.re - 1 / 2) p) *
        ‖soninLadderCharacter w (p : ℝ)‖ ^ 2 = 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have ht : 0 ≤ w.re - 1 / 2 := by linarith
  rw [one_sub_routeNGammaSewnProjectiveKadisonDefect,
    routeNGammaSewnTransverseModularCocycle,
    routeNGammaSewnTransverseModularClockCocycle,
    norm_soninLadderCharacter hp0, abs_of_nonneg ht,
    pow_two, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
  have hexp :
      -2 * (w.re - 1 / 2) +
          ((w.re - 1 / 2) + (w.re - 1 / 2)) = 0 := by
    ring
  rw [hexp, Real.rpow_zero]

/-- **Actual-zero defect/escape law.**  At every right-half-strip zeta zero, one co-Poisson
ladder step can absorb the Route N projective survival exactly: its previous squared conormal norm
is bounded by survival times the next squared norm.  Off the line survival is strictly below one,
so the complementary conormal carrier must inflate. -/
theorem normSq_coPoissonLadderKernel_le_routeNSurvival_mul_succ
    {w : ℂ} {a : ℝ} {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} (p : Nat.Primes) (hz : riemannZeta w = 0)
    (j : ℕ) :
    ‖coPoissonLadderKernel w hlo hhi a (p : ℝ) ha
        (by exact_mod_cast p.2.pos) j‖ ^ 2 ≤
      (1 - routeNGammaSewnProjectiveKadisonDefect
        (w.re - 1 / 2) p) *
        ‖coPoissonLadderKernel w hlo hhi a (p : ℝ) ha
          (by exact_mod_cast p.2.pos) (j + 1)‖ ^ 2 := by
  let hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  let hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
  let Y := ‖coPoissonLadderKernel w hlo hhi a (p : ℝ) ha hp0 j‖
  let Z := ‖coPoissonLadderKernel w hlo hhi a (p : ℝ) ha hp0 (j + 1)‖
  let L := ‖soninLadderCharacter w (p : ℝ)‖
  let S := 1 - routeNGammaSewnProjectiveKadisonDefect
    (w.re - 1 / 2) p
  have hstep : L * Y ≤ Z :=
    norm_coPoissonLadderKernel_forward_step hp1
      (coPoissonLadderAnnihilator_of_riemannZeta_eq_zero hz) j
  have hLY : 0 ≤ L * Y := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hZ : 0 ≤ Z := norm_nonneg _
  have hsqprod : 0 ≤ (Z - L * Y) * (Z + L * Y) :=
    mul_nonneg (sub_nonneg.mpr hstep) (add_nonneg hZ hLY)
  have hsq : L ^ 2 * Y ^ 2 ≤ Z ^ 2 := by
    nlinarith
  have hS : 0 ≤ S := by
    dsimp [S]
    have hmem := routeNGammaSewnProjectiveKadisonDefect_mem_Ico
      (w.re - 1 / 2) p
    exact sub_nonneg.mpr hmem.2.le
  have hconserve : S * L ^ 2 = 1 := by
    dsimp [S, L]
    exact routeNGammaSewnKadisonSurvival_mul_rightSoninCharacter_sq
      hlo.le p
  change Y ^ 2 ≤ S * Z ^ 2
  calc
    Y ^ 2 = (S * L ^ 2) * Y ^ 2 := by rw [hconserve, one_mul]
    _ = S * (L ^ 2 * Y ^ 2) := by ring
    _ ≤ S * Z ^ 2 := mul_le_mul_of_nonneg_left hsq hS

/-- **Strict-right conormal escape.**  At every actual zeta zero in the open right half-strip,
the co-Poisson ladder-kernel norms diverge to infinity along every aperture ladder with ratio
strictly above one.  This upgrades the geometric lower bound to genuine corona escape using
nonvanishing of the source evaluation vector. -/
theorem tendsto_norm_coPoissonLadderKernel_atTop_of_riemannZeta_eq_zero
    {w : ℂ} {a r : ℝ} {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (ha1 : a < 1) (hr1 : 1 < r)
    (hz : riemannZeta w = 0) :
    Tendsto (fun N =>
      ‖coPoissonLadderKernel w hlo hhi a r ha hr N‖)
      atTop atTop := by
  have hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr :=
    coPoissonLadderAnnihilator_of_riemannZeta_eq_zero hz
  have hL : 1 < ‖soninLadderCharacter w r‖ := by
    rw [norm_soninLadderCharacter hr]
    exact Real.one_lt_rpow hr1 (by linarith)
  have hkernel0 :
      coPoissonLadderKernel w hlo hhi a r ha hr 0 ≠ 0 := by
    have hb1 : soninAperture a r 0 < 1 := by
      simpa only [soninAperture_zero] using ha1
    have hambient := burnolExtendedSoninEvaluationVector_ne_zero
      hlo hhi (soninAperture_pos ha hr 0) hb1
    have hsonin : soninLadderKernel w hlo hhi a r ha hr 0 ≠ 0 := by
      intro hk
      apply hambient
      apply Subtype.ext
      exact hk
    rw [coPoissonLadderKernel_eq_soninLadderKernel hann 0]
    exact hsonin
  have hnorm0 :
      0 < ‖coPoissonLadderKernel w hlo hhi a r ha hr 0‖ :=
    norm_pos_iff.mpr hkernel0
  have hlower : Tendsto (fun N =>
      ‖soninLadderCharacter w r‖ ^ N *
        ‖coPoissonLadderKernel w hlo hhi a r ha hr 0‖)
      atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hL).atTop_mul_const hnorm0
  apply Filter.tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall fun N =>
      norm_coPoissonLadderKernel_geometric_forward hr1.le hann N)
    hlower

end

end RHTower
