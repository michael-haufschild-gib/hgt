import GaloisForLFunctions.RHTower.LevinsonDetectorFE
import GaloisForLFunctions.RHTower.ZetaChiHardyPhase
import GaloisForLFunctions.PNTPlus.ZetaConj
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly
import GaloisForLFunctions.HTGeometry.DigammaAsymptotic

/-!
# Levinson's detector on the critical line

On the critical line `1 − s = s̄`, and for **real** `λ` both `Γ_ℝ` and `G = ζ + λζ'` are
Schwarz-symmetric, so the detector's functional equation collapses to

```text
Y(½+iτ)·Λ(½+iτ) = 2·Re[Γ_ℝ(½+iτ)·G(½+iτ)].
```

The weight is the explicit real number `Y(½+iτ) = 2 − λ·(Re ψ(¼+iτ/2) − log π)`, and for `λ ≤ 0` it
is at least `2` once `Re ψ(¼+iτ/2) > log π`, which the corpus's vertical digamma bound gives from
height `20` on.  Hence, unconditionally,

```text
Re[Γ_ℝ(½+iτ)·(ζ + λζ')(½+iτ)] = 0   ⟺   ζ(½+iτ) = 0        (λ ≤ 0 real, τ ≥ 20).
```

At `λ = 0` this is Hardy's `Z`; for `λ ≠ 0` it is the deformed detector whose off-line zeros
Levinson's method counts with Littlewood's lemma.
-/

open Complex


noncomputable section

namespace RHTower

theorem levinsonG_conj (lam : ℝ) (s : ℂ) :
    levinsonG (lam : ℂ) ((starRingEnd ℂ) s) = (starRingEnd ℂ) (levinsonG (lam : ℂ) s) := by
  rw [levinsonG, levinsonG, map_add, map_mul, riemannZeta_conj, deriv_riemannZeta_conj,
    Complex.conj_ofReal]

/-- **The detector on the critical line.**  Because `1 − (½+iτ) = conj(½+iτ)` and both `Γ_ℝ` and
`G` (for real `λ`) are Schwarz-symmetric, the functional equation collapses to a real statement:
the completed zeta, weighted by `Y`, is twice the real part of `Γ_ℝ·G`. -/
theorem levinsonY_mul_completed_line (lam : ℝ) (τ : ℝ) :
    levinsonY (lam : ℂ) (linePt τ) * completedRiemannZeta (linePt τ)
      = 2 * (((Complex.Gammaℝ (linePt τ) * levinsonG (lam : ℂ) (linePt τ)).re : ℝ) : ℂ) := by
  have hstrip0 : 0 < (linePt τ).re := by rw [linePt_re]; norm_num
  have hstrip1 : (linePt τ).re < 1 := by rw [linePt_re]; norm_num
  have h := levinsonY_mul_completedRiemannZeta (lam : ℂ) hstrip0 hstrip1
  rw [h, one_sub_linePt, Gammaℝ_conj, levinsonG_conj, ← map_mul, Complex.add_conj]
  push_cast
  ring

/-- **Levinson's detection lemma.**  Where the archimedean weight `Y` does not vanish, the real
function `τ ↦ Re[Γ_ℝ(½+iτ)·G(½+iτ)]` vanishes exactly at the critical-line zeros of `ζ`. -/
theorem re_Gammaℝ_mul_levinsonG_eq_zero_iff (lam : ℝ) {τ : ℝ}
    (hY : levinsonY (lam : ℂ) (linePt τ) ≠ 0) :
    (Complex.Gammaℝ (linePt τ) * levinsonG (lam : ℂ) (linePt τ)).re = 0
      ↔ riemannZeta (linePt τ) = 0 := by
  have hstrip0 : 0 < (linePt τ).re := by rw [linePt_re]; norm_num
  have hG : Complex.Gammaℝ (linePt τ) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hstrip0
  have hΛ : completedRiemannZeta (linePt τ)
      = Complex.Gammaℝ (linePt τ) * riemannZeta (linePt τ) :=
    completedRiemannZeta_eq_Gammaℝ_mul_levinsonDetectorFE hstrip0
  have hkey := levinsonY_mul_completed_line lam τ
  constructor
  · intro h0
    rw [h0] at hkey
    simp only [Complex.ofReal_zero, mul_zero] at hkey
    have hΛ0 : completedRiemannZeta (linePt τ) = 0 := by
      rcases mul_eq_zero.mp hkey with h | h
      · exact absurd h hY
      · exact h
    rw [hΛ] at hΛ0
    rcases mul_eq_zero.mp hΛ0 with h | h
    · exact absurd h hG
    · exact h
  · intro h0
    have hΛ0 : completedRiemannZeta (linePt τ) = 0 := by rw [hΛ, h0, mul_zero]
    rw [hΛ0, mul_zero] at hkey
    have h2 : (((Complex.Gammaℝ (linePt τ) * levinsonG (lam : ℂ) (linePt τ)).re : ℝ) : ℂ) = 0 := by
      rcases mul_eq_zero.mp hkey.symm with h | h
      · exact absurd h (by norm_num)
      · exact h
    exact_mod_cast h2

/-! ## The archimedean weight does not vanish -/

theorem levinsonY_line_eq (lam : ℝ) (τ : ℝ) :
    levinsonY (lam : ℂ) (linePt τ)
      = ((2 - lam * ((Complex.digamma (((1 / 4 : ℝ) : ℂ)
            + ((τ / 2 : ℝ) : ℂ) * Complex.I)).re - Real.log Real.pi) : ℝ) : ℂ) := by
  have hpos : 0 < (linePt τ).re := by rw [linePt_re]; norm_num
  have hpos' : 0 < ((starRingEnd ℂ) (linePt τ)).re := by
    rw [Complex.conj_re, linePt_re]; norm_num
  have hhalf : linePt τ / 2 = ((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * Complex.I := by
    unfold linePt
    push_cast
    ring
  have hconjhalf : ((starRingEnd ℂ) (linePt τ)) / 2 = (starRingEnd ℂ) (linePt τ / 2) := by
    rw [map_div₀, map_ofNat]
  rw [levinsonY, one_sub_linePt,
    logDeriv_Gammaℝ_of_re_pos hpos, logDeriv_Gammaℝ_of_re_pos hpos',
    hconjhalf, ReflectedDigammaAnomaly.digamma_conj, hhalf]
  have hz : ∀ z : ℂ, z + (starRingEnd ℂ) z = ((2 * z.re : ℝ) : ℂ) := by
    intro z
    rw [Complex.add_conj]
  set w : ℂ := Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * Complex.I) with hw
  have hsplit : (lam : ℂ) * (w / 2 - (Real.log Real.pi : ℂ) / 2)
      + (lam : ℂ) * ((starRingEnd ℂ) w / 2 - (Real.log Real.pi : ℂ) / 2)
      = (lam : ℂ) * ((w + (starRingEnd ℂ) w) / 2 - (Real.log Real.pi : ℂ)) := by ring
  rw [show (2 : ℂ) - (lam : ℂ) * (w / 2 - (Real.log Real.pi : ℂ) / 2)
      - (lam : ℂ) * ((starRingEnd ℂ) w / 2 - (Real.log Real.pi : ℂ) / 2)
      = 2 - ((lam : ℂ) * (w / 2 - (Real.log Real.pi : ℂ) / 2)
        + (lam : ℂ) * ((starRingEnd ℂ) w / 2 - (Real.log Real.pi : ℂ) / 2)) by ring,
    hsplit, hz w]
  push_cast
  ring

theorem log_pi_lt_re_digamma_quarter {τ : ℝ} (hτ : 20 ≤ τ) :
    Real.log Real.pi
      < (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * Complex.I)).re := by
  have hτ0 : (0 : ℝ) < τ := by linarith
  have hb := re_digamma_vertical_bound_uncond (σ := 1 / 4) (t := τ / 2)
    (by norm_num) (by linarith)
  have hlow : (1 / 2 : ℝ) * Real.log ((1 / 4 : ℝ) ^ (2 : ℕ) + (τ / 2) ^ (2 : ℕ))
        - (1 / (τ / 2) ^ (2 : ℕ) + Real.pi / (2 * (τ / 2)))
      ≤ (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * Complex.I)).re := by
    have := (abs_le.mp hb).1
    linarith
  -- the logarithm is at least `log 10`
  have hmono : Real.log ((τ / 2) ^ (2 : ℕ)) ≤ Real.log ((1 / 4 : ℝ) ^ (2 : ℕ) + (τ / 2) ^ (2 : ℕ)) := by
    refine Real.log_le_log (by positivity) (by nlinarith)
  have hsq : Real.log ((τ / 2) ^ (2 : ℕ)) = 2 * Real.log (τ / 2) := by
    rw [Real.log_pow]; push_cast; ring
  have hten : Real.log 10 ≤ Real.log (τ / 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hten' : (3 : ℝ) * Real.log 2 ≤ Real.log 10 := by
    have h8 : Real.log 8 ≤ Real.log 10 := Real.log_le_log (by norm_num) (by norm_num)
    have h8' : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    linarith
  -- the error terms are small
  have herr1 : 1 / (τ / 2) ^ (2 : ℕ) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have herr2 : Real.pi / (2 * (τ / 2)) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_lt_d2]
  -- and `log π ≤ 2 log 2`
  have hpi : Real.log Real.pi ≤ 2 * Real.log 2 := by
    have h4 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_d2])
    have h4' : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    linarith
  linarith

/-- **The archimedean weight of Levinson's detector never vanishes for `λ ≤ 0`.**  Above height
`20` the real part of the digamma factor already exceeds `log π`, so `Y(½+iτ) ≥ 2 > 0`. -/
theorem levinsonY_line_ne_zero {lam : ℝ} (hlam : lam ≤ 0) {τ : ℝ} (hτ : 20 ≤ τ) :
    levinsonY (lam : ℂ) (linePt τ) ≠ 0 := by
  rw [levinsonY_line_eq]
  refine Complex.ofReal_ne_zero.mpr ?_
  have hd := log_pi_lt_re_digamma_quarter hτ
  have hpos : (0 : ℝ) < 2 - lam * ((Complex.digamma (((1 / 4 : ℝ) : ℂ)
      + ((τ / 2 : ℝ) : ℂ) * Complex.I)).re - Real.log Real.pi) := by
    nlinarith
  exact ne_of_gt hpos

/-- **Levinson's detector, unconditionally.**  For real `λ ≤ 0` and heights above `20`, the real
function `τ ↦ Re[Γ_ℝ(½+iτ)·(ζ + λζ')(½+iτ)]` vanishes exactly at the critical-line zeros of `ζ`. -/
theorem re_Gammaℝ_mul_levinsonG_eq_zero_iff_of_nonpos {lam : ℝ} (hlam : lam ≤ 0)
    {τ : ℝ} (hτ : 20 ≤ τ) :
    (Complex.Gammaℝ (linePt τ) * levinsonG (lam : ℂ) (linePt τ)).re = 0
      ↔ riemannZeta (linePt τ) = 0 :=
  re_Gammaℝ_mul_levinsonG_eq_zero_iff lam (levinsonY_line_ne_zero hlam hτ)

/-- **On the critical line the detector is the completed zeta up to a nonvanishing real factor.**
Consequently `Re[Γ_ℝ·G]` has exactly the zeros of `Λ` on the line, with the same orders: the
deformation `λ ≠ 0` buys nothing *on* the line — its whole effect is off the line, where `G` has
fewer zeros than `ζ`.  In particular a sign change of the detector is a sign change of `Ξ`, so it
produces a critical zero of **odd** order. -/
theorem re_Gammaℝ_mul_levinsonG_eq_half_Y_mul_completed (lam : ℝ) (τ : ℝ) :
    (((Complex.Gammaℝ (linePt τ) * levinsonG (lam : ℂ) (linePt τ)).re : ℝ) : ℂ)
      = levinsonY (lam : ℂ) (linePt τ) * completedRiemannZeta (linePt τ) / 2 := by
  rw [levinsonY_mul_completed_line]
  ring

end RHTower

end
