import GaloisForLFunctions.RHTower.FZZCigarParityMellinCharacterCrossingReflection

/-!
# Source-metric reflection tilt of the FZZ parity carrier

The positive-scale FZZ parity source has unequal diagonal coefficients
`P(beta) > P(4 beta)`.  This file constructs the resulting canonical weighted conjugate swap and
proves that it is an involution preserving the source Hermitian pairing.

On centered dyadic Mellin carriers its projective action is functional-equation reflection times
the unavoidable factor `P(beta) / P(4 beta)`.  Its fixed locus is therefore the exact vertical line

`Re rho = 1/2 + log(P(beta) / P(4 beta)) / (2 log 2)`,

strictly to the right of the critical line.  Bare source-metric reflection is thus a sharp no-go for
the F8 critical-line matching mechanism.  The positive survivor is equally exact: the unique scalar
counterterm restoring functional-equation reflection is `P(4 beta) / P(beta)`.
-/

open Complex

namespace RHTower

noncomputable section

theorem fzzKreinPAt_gt_fzzKreinRAt
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzKreinRAt beta < fzzKreinPAt beta := by
  change fzzCigarParityDelay (4 * beta) < fzzCigarParityDelay beta
  rw [fzzCigarParityDelay_eq_fermi hbeta,
    fzzCigarParityDelay_eq_fermi (mul_pos (by norm_num) hbeta)]
  have hden : Real.exp beta + 1 < Real.exp (4 * beta) + 1 := by
    have hexp : Real.exp beta < Real.exp (4 * beta) := by
      apply Real.exp_lt_exp.mpr
      linarith
    linarith
  simpa [one_div] using
    (one_div_lt_one_div_of_lt (by positivity : 0 < Real.exp beta + 1) hden)

/-- Positive coordinate weight of source-metric reflection. -/
def fzzCigarParitySourceMetricReflectionScale (beta : ℝ) : ℝ :=
  Real.sqrt (fzzKreinRAt beta / fzzKreinPAt beta)

theorem fzzCigarParitySourceMetricReflectionScale_pos
    {beta : ℝ} (hbeta : 0 < beta) :
    0 < fzzCigarParitySourceMetricReflectionScale beta := by
  rw [fzzCigarParitySourceMetricReflectionScale]
  exact Real.sqrt_pos.2 (div_pos (fzzKreinRAt_pos hbeta) (fzzKreinPAt_pos hbeta))

theorem fzzCigarParitySourceMetricReflectionScale_sq
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParitySourceMetricReflectionScale beta ^ (2 : ℕ) =
      fzzKreinRAt beta / fzzKreinPAt beta := by
  rw [fzzCigarParitySourceMetricReflectionScale, Real.sq_sqrt]
  exact (div_pos (fzzKreinRAt_pos hbeta) (fzzKreinPAt_pos hbeta)).le

theorem fzzCigarParitySourceMetricReflectionScale_inv_sq
    {beta : ℝ} (hbeta : 0 < beta) :
    (fzzCigarParitySourceMetricReflectionScale beta)⁻¹ ^ (2 : ℕ) =
      fzzKreinPAt beta / fzzKreinRAt beta := by
  have ha := fzzCigarParitySourceMetricReflectionScale_sq hbeta
  have hp := (fzzKreinPAt_pos hbeta).ne'
  have hr := (fzzKreinRAt_pos hbeta).ne'
  rw [inv_pow, ha]
  field_simp

/-- Weighted conjugate coordinate swap selected by the source diagonal. -/
def fzzCigarParitySourceMetricReflection (beta : ℝ) (u : ℂ × ℂ) : ℂ × ℂ :=
  ((fzzCigarParitySourceMetricReflectionScale beta : ℂ) * star u.2,
    ((fzzCigarParitySourceMetricReflectionScale beta)⁻¹ : ℂ) * star u.1)

theorem fzzCigarParitySourceMetricReflection_involutive
    {beta : ℝ} (hbeta : 0 < beta) (u : ℂ × ℂ) :
    fzzCigarParitySourceMetricReflection beta
        (fzzCigarParitySourceMetricReflection beta u) = u := by
  rcases u with ⟨u₁, u₂⟩
  apply Prod.ext <;>
    simp [fzzCigarParitySourceMetricReflection,
      Complex.conj_ofReal,
      (fzzCigarParitySourceMetricReflectionScale_pos hbeta).ne']

theorem fzzCigarParitySourceMetricReflection_pairing
    {beta : ℝ} (hbeta : 0 < beta) (u v : ℂ × ℂ) :
    fzzCigarParityDilatedTwoScaleKreinPairing beta
        (fzzCigarParitySourceMetricReflection beta u)
        (fzzCigarParitySourceMetricReflection beta v) =
      star (fzzCigarParityDilatedTwoScaleKreinPairing beta u v) := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  have ha2 := fzzCigarParitySourceMetricReflectionScale_sq hbeta
  have hai2 := fzzCigarParitySourceMetricReflectionScale_inv_sq hbeta
  have hp := (fzzKreinPAt_pos hbeta).ne'
  have hr := (fzzKreinRAt_pos hbeta).ne'
  have hpa2 :
      fzzKreinPAt beta * fzzCigarParitySourceMetricReflectionScale beta ^ (2 : ℕ) =
        fzzKreinRAt beta := by
    rw [ha2]
    field_simp
  have hrai2 :
      fzzKreinRAt beta * (fzzCigarParitySourceMetricReflectionScale beta)⁻¹ ^ (2 : ℕ) =
        fzzKreinPAt beta := by
    rw [hai2]
    field_simp
  have hpa2c :
      (fzzKreinPAt beta : ℂ) *
          (fzzCigarParitySourceMetricReflectionScale beta : ℂ) ^ (2 : ℕ) =
        (fzzKreinRAt beta : ℂ) := by
    exact_mod_cast hpa2
  have hrai2c :
      (fzzKreinRAt beta : ℂ) *
          ((fzzCigarParitySourceMetricReflectionScale beta)⁻¹ : ℂ) ^ (2 : ℕ) =
        (fzzKreinPAt beta : ℂ) := by
    exact_mod_cast hrai2
  have haC : (fzzCigarParitySourceMetricReflectionScale beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzCigarParitySourceMetricReflectionScale_pos hbeta).ne'
  simp [fzzCigarParityDilatedTwoScaleKreinPairing,
    fzzCigarParitySourceMetricReflection, Complex.conj_ofReal]
  field_simp [haC]
  ring_nf at hpa2c hrai2c ⊢
  rw [← hpa2c]
  ring

/-- Affine-chart ratio on the source block. -/
def fzzCigarParitySourceProjectiveRatio (u : ℂ × ℂ) : ℂ := u.2 / u.1

/-- Exact projective action: source-metric reflection adds the diagonal source ratio to
functional-equation reflection. -/
theorem fzzCigarParitySourceMetricReflection_mellin_ratio
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    fzzCigarParitySourceProjectiveRatio
        (fzzCigarParitySourceMetricReflection beta
          (fzzCigarParityMellinCharacterCarrier rho)) =
      ((fzzKreinPAt beta / fzzKreinRAt beta : ℝ) : ℂ) *
        fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho) := by
  have haC : (fzzCigarParitySourceMetricReflectionScale beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzCigarParitySourceMetricReflectionScale_pos hbeta).ne'
  have hz : star (fzzCigarParityDyadicMellinCharacter rho) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2
      (fzzCigarParityDyadicMellinCharacter_ne_zero rho)
  have ha2 := fzzCigarParitySourceMetricReflectionScale_sq hbeta
  have hpa2 :
      fzzKreinPAt beta * fzzCigarParitySourceMetricReflectionScale beta ^ (2 : ℕ) =
        fzzKreinRAt beta := by
    rw [ha2]
    field_simp [(fzzKreinPAt_pos hbeta).ne']
  have hpa2c :
      (fzzKreinPAt beta : ℂ) *
          (fzzCigarParitySourceMetricReflectionScale beta : ℂ) ^ (2 : ℕ) =
        (fzzKreinRAt beta : ℂ) := by
    exact_mod_cast hpa2
  have hrC : (fzzKreinRAt beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzKreinRAt_pos hbeta).ne'
  rw [fzzCigarParityDyadicMellinCharacter_reflection]
  simp [fzzCigarParitySourceProjectiveRatio,
    fzzCigarParitySourceMetricReflection,
    fzzCigarParityMellinCharacterCarrier]
  field_simp [haC, hz, hrC]
  ring_nf at hpa2c ⊢
  rw [hpa2c]

/-- Bare source reflection never realizes functional-equation reflection at positive scale. -/
theorem fzzCigarParitySourceMetricReflection_mellin_ratio_ne_reflection
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    fzzCigarParitySourceProjectiveRatio
        (fzzCigarParitySourceMetricReflection beta
          (fzzCigarParityMellinCharacterCarrier rho)) ≠
      fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho) := by
  rw [fzzCigarParitySourceMetricReflection_mellin_ratio hbeta]
  intro h
  have hz := fzzCigarParityDyadicMellinCharacter_ne_zero
    (criticalLineReflectionPoint rho)
  have hk : ((fzzKreinPAt beta / fzzKreinRAt beta : ℝ) : ℂ) = 1 := by
    apply mul_right_cancel₀ hz
    simpa using h
  have hkR : fzzKreinPAt beta / fzzKreinRAt beta = 1 := by
    exact_mod_cast hk
  have hr := (fzzKreinRAt_pos hbeta).ne'
  have hpr : fzzKreinPAt beta = fzzKreinRAt beta := by
    field_simp at hkR
    exact hkR
  exact (ne_of_gt (fzzKreinPAt_gt_fzzKreinRAt hbeta)) hpr

/-- Real fixed axis selected by bare source-metric reflection. -/
def fzzCigarParitySourceMetricReflectionFixedAxis (beta : ℝ) : ℝ :=
  1 / 2 +
    Real.log (fzzKreinPAt beta / fzzKreinRAt beta) / (2 * Real.log 2)

theorem fzzCigarParitySourceDiagonalRatio_gt_one
    {beta : ℝ} (hbeta : 0 < beta) :
    1 < fzzKreinPAt beta / fzzKreinRAt beta := by
  rw [one_lt_div₀ (fzzKreinRAt_pos hbeta)]
  exact fzzKreinPAt_gt_fzzKreinRAt hbeta

/-- Source-metric fixed axis is strictly to the right of the critical line at every positive
physical scale. -/
theorem fzzCigarParitySourceMetricReflectionFixedAxis_gt_half
    {beta : ℝ} (hbeta : 0 < beta) :
    1 / 2 < fzzCigarParitySourceMetricReflectionFixedAxis beta := by
  rw [fzzCigarParitySourceMetricReflectionFixedAxis]
  have hklog : 0 < Real.log (fzzKreinPAt beta / fzzKreinRAt beta) :=
    Real.log_pos (fzzCigarParitySourceDiagonalRatio_gt_one hbeta)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquot :
      0 < Real.log (fzzKreinPAt beta / fzzKreinRAt beta) /
        (2 * Real.log 2) := div_pos hklog (mul_pos (by norm_num) hlog2)
  linarith

/-- **Tilted-axis classification.** Projective fixed carriers of bare source-metric reflection
occupy exactly one scale-dependent vertical line. -/
theorem fzzCigarParitySourceMetricReflection_mellin_fixed_iff
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    fzzCigarParitySourceProjectiveRatio
        (fzzCigarParitySourceMetricReflection beta
          (fzzCigarParityMellinCharacterCarrier rho)) =
        fzzCigarParityDyadicMellinCharacter rho ↔
      rho.re = fzzCigarParitySourceMetricReflectionFixedAxis beta := by
  rw [fzzCigarParitySourceMetricReflection_mellin_ratio hbeta]
  let k : ℝ := fzzKreinPAt beta / fzzKreinRAt beta
  let z : ℂ := fzzCigarParityDyadicMellinCharacter rho
  let zr : ℂ :=
    fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho)
  let n : ℝ := ‖z‖
  let nr : ℝ := ‖zr‖
  have hkpos : 0 < k := div_pos (fzzKreinPAt_pos hbeta) (fzzKreinRAt_pos hbeta)
  have hnpos : 0 < n := by
    dsimp only [n, z]
    exact norm_fzzCigarParityDyadicMellinCharacter_pos rho
  have hnrpos : 0 < nr := by
    dsimp only [nr, zr]
    exact norm_fzzCigarParityDyadicMellinCharacter_pos
      (criticalLineReflectionPoint rho)
  have hrefnorm : nr * n = 1 := by
    dsimp only [nr, n, zr, z]
    exact norm_fzzCigarParityDyadicMellinCharacter_reflection_mul rho
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < 2 * Real.log 2 := mul_pos (by norm_num) hlog2
  change (k : ℂ) * zr = z ↔ _
  constructor
  · intro hfixed
    have hnorm := congrArg norm hfixed
    have hknorm : k * nr = n := by
      simpa [Real.norm_eq_abs, abs_of_pos hkpos, n, nr, z, zr] using hnorm
    have hnsq : n ^ (2 : ℕ) = k := by
      calc
        n ^ (2 : ℕ) = (k * nr) * n := by simp [pow_two, hknorm]
        _ = k * (nr * n) := by ring
        _ = k := by rw [hrefnorm, mul_one]
    have hexp :
        Real.exp (2 * (Real.log 2 * (rho.re - 1 / 2))) = k := by
      rw [show 2 * (Real.log 2 * (rho.re - 1 / 2)) =
        Real.log 2 * (rho.re - 1 / 2) +
          Real.log 2 * (rho.re - 1 / 2) by ring, Real.exp_add]
      simpa [n, z, norm_fzzCigarParityDyadicMellinCharacter, pow_two] using hnsq
    have hkexp : Real.exp (Real.log k) = k := Real.exp_log hkpos
    have harg :
        2 * (Real.log 2 * (rho.re - 1 / 2)) = Real.log k :=
      Real.exp_injective (hexp.trans hkexp.symm)
    rw [fzzCigarParitySourceMetricReflectionFixedAxis]
    change rho.re = 1 / 2 + Real.log k / (2 * Real.log 2)
    have hx : rho.re - 1 / 2 = Real.log k / (2 * Real.log 2) := by
      apply (eq_div_iff hden.ne').2
      nlinarith
    linarith
  · intro hre
    have harg :
        2 * (Real.log 2 * (rho.re - 1 / 2)) = Real.log k := by
      rw [hre, fzzCigarParitySourceMetricReflectionFixedAxis]
      change 2 * (Real.log 2 *
        (1 / 2 + Real.log k / (2 * Real.log 2) - 1 / 2)) = Real.log k
      field_simp [hlog2.ne']
      ring
    have hnsq : n ^ (2 : ℕ) = k := by
      dsimp only [n, z]
      rw [norm_fzzCigarParityDyadicMellinCharacter]
      rw [show Real.exp (Real.log 2 * (rho.re - 1 / 2)) ^ (2 : ℕ) =
        Real.exp (2 * (Real.log 2 * (rho.re - 1 / 2))) by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring]
      rw [harg, Real.exp_log hkpos]
    have hphase :=
      fzzCigarParityDyadicMellinCharacter_normalizedPhase_reflection rho
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have hnrC : (nr : ℂ) ≠ 0 := by exact_mod_cast hnrpos.ne'
    change zr / (nr : ℂ) = z / (n : ℂ) at hphase
    field_simp [hnC, hnrC] at hphase
    have hphaseMul : zr * (n : ℂ) = z * (nr : ℂ) := by
      simpa [mul_comm] using hphase
    have hnsqC : (n : ℂ) ^ (2 : ℕ) = (k : ℂ) := by exact_mod_cast hnsq
    have hrefnormC : (nr : ℂ) * (n : ℂ) = 1 := by exact_mod_cast hrefnorm
    calc
      (k : ℂ) * zr = (n : ℂ) ^ (2 : ℕ) * zr := by rw [hnsqC]
      _ = (n : ℂ) * (zr * (n : ℂ)) := by ring
      _ = (n : ℂ) * (z * (nr : ℂ)) := by rw [hphaseMul]
      _ = z * ((nr : ℂ) * (n : ℂ)) := by ring
      _ = z := by rw [hrefnormC, mul_one]

/-- Critical-line carriers are never projectively fixed by the bare source-metric reflection. -/
theorem fzzCigarParitySourceMetricReflection_criticalLine_not_fixed
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) (hrho : rho.re = 1 / 2) :
    fzzCigarParitySourceProjectiveRatio
        (fzzCigarParitySourceMetricReflection beta
          (fzzCigarParityMellinCharacterCarrier rho)) ≠
      fzzCigarParityDyadicMellinCharacter rho := by
  intro hfixed
  have haxis :=
    (fzzCigarParitySourceMetricReflection_mellin_fixed_iff hbeta rho).mp hfixed
  have htilt := fzzCigarParitySourceMetricReflectionFixedAxis_gt_half hbeta
  rw [hrho] at haxis
  linarith

/-- Unique scalar correction that removes source-diagonal tilt. -/
def fzzCigarParitySourceMetricReflectionCounterterm (beta : ℝ) : ℝ :=
  fzzKreinRAt beta / fzzKreinPAt beta

theorem fzzCigarParitySourceMetricReflection_counterterm_exact
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) :
    (fzzCigarParitySourceMetricReflectionCounterterm beta : ℂ) *
        fzzCigarParitySourceProjectiveRatio
          (fzzCigarParitySourceMetricReflection beta
            (fzzCigarParityMellinCharacterCarrier rho)) =
      fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho) := by
  rw [fzzCigarParitySourceMetricReflection_mellin_ratio hbeta]
  have hpC : (fzzKreinPAt beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzKreinPAt_pos hbeta).ne'
  have hrC : (fzzKreinRAt beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzKreinRAt_pos hbeta).ne'
  rw [fzzCigarParitySourceMetricReflectionCounterterm]
  push_cast
  field_simp [hpC, hrC]

/-- The diagonal inverse ratio is the only scalar correction realizing functional-equation
reflection on even one Mellin carrier. -/
theorem fzzCigarParitySourceMetricReflection_counterterm_unique
    {beta : ℝ} (hbeta : 0 < beta) (rho : ℂ) (c : ℂ) :
    c * fzzCigarParitySourceProjectiveRatio
          (fzzCigarParitySourceMetricReflection beta
            (fzzCigarParityMellinCharacterCarrier rho)) =
        fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho) ↔
      c = (fzzCigarParitySourceMetricReflectionCounterterm beta : ℂ) := by
  rw [fzzCigarParitySourceMetricReflection_mellin_ratio hbeta]
  let zr := fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho)
  have hzr : zr ≠ 0 :=
    fzzCigarParityDyadicMellinCharacter_ne_zero (criticalLineReflectionPoint rho)
  have hpC : (fzzKreinPAt beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzKreinPAt_pos hbeta).ne'
  have hrC : (fzzKreinRAt beta : ℂ) ≠ 0 := by
    exact_mod_cast (fzzKreinRAt_pos hbeta).ne'
  change c * (((fzzKreinPAt beta / fzzKreinRAt beta : ℝ) : ℂ) * zr) = zr ↔ _
  constructor
  · intro h
    have hcoeff : c * ((fzzKreinPAt beta / fzzKreinRAt beta : ℝ) : ℂ) = 1 := by
      apply mul_right_cancel₀ hzr
      simpa [mul_assoc] using h
    have hcoeff' :
        c * ((fzzKreinPAt beta : ℂ) / (fzzKreinRAt beta : ℂ)) = 1 := by
      simpa only [Complex.ofReal_div] using hcoeff
    rw [fzzCigarParitySourceMetricReflectionCounterterm]
    push_cast
    calc
      c = c * 1 := by ring
      _ = c * ((fzzKreinPAt beta : ℂ) / (fzzKreinRAt beta : ℂ) *
          ((fzzKreinRAt beta : ℂ) / (fzzKreinPAt beta : ℂ))) := by
            congr 1
            field_simp [hpC, hrC]
      _ = (c * ((fzzKreinPAt beta : ℂ) / (fzzKreinRAt beta : ℂ))) *
          ((fzzKreinRAt beta : ℂ) / (fzzKreinPAt beta : ℂ)) := by ring
      _ = 1 * ((fzzKreinRAt beta : ℂ) / (fzzKreinPAt beta : ℂ)) := by
        rw [hcoeff']
      _ = (fzzKreinRAt beta : ℂ) / (fzzKreinPAt beta : ℂ) := by ring
  · intro hc
    rw [hc]
    rw [fzzCigarParitySourceMetricReflectionCounterterm]
    push_cast
    field_simp [hpC, hrC]

end


end RHTower
