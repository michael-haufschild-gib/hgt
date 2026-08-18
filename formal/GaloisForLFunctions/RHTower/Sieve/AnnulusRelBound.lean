import GaloisForLFunctions.RHTower.Sieve.RouteTWidthAntitone
import GaloisForLFunctions.RHTower.Sieve.GeomBlockPrimeRho

/-!
# The relative scaled envelope, bounded uniformly on an annulus

Every input of the relative scaled envelope — the logarithm of the cutoff, the Route-T width, the
height cost and the desmoothing term — is monotone in the cutoff or in the frequency, so on a range
`t₀ ≤ |τ| ≤ |σ|` and `xmin ≤ x` with `log x ≤ Lx` the envelope is bounded by one explicit constant.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- The uniform majorant of the relative scaled envelope. -/
def relScaledMajorant (Ctot D Lx Hmaj μ q t₀ xmin : ℝ) : ℝ :=
  Ctot * D ^ 2 * (Lx ^ 2 / t₀ + Hmaj * (Real.exp (-(μ * q)) + 1 / t₀ ^ 2)) / (2 * Real.pi)
    + (Real.log 2 + Lx) / D + 2 * Lx / Real.sqrt xmin

theorem relScaledMajorant_nonneg {Ctot D Lx Hmaj μ q t₀ xmin : ℝ} (hCtot : 0 ≤ Ctot)
    (hD : 0 < D) (hLx : 0 ≤ Lx) (hHmaj : 0 ≤ Hmaj) (ht0 : 0 < t₀) (hxmin : 0 < xmin) :
    0 ≤ relScaledMajorant Ctot D Lx Hmaj μ q t₀ xmin := by
  have h1 : (0 : ℝ) ≤ Lx ^ 2 / t₀ := by positivity
  have h2 : (0 : ℝ) ≤ Real.exp (-(μ * q)) + 1 / t₀ ^ 2 := by positivity
  have h3 : (0 : ℝ) ≤ Hmaj * (Real.exp (-(μ * q)) + 1 / t₀ ^ 2) := mul_nonneg hHmaj h2
  have hA : (0 : ℝ) ≤ Ctot * D ^ 2
      * (Lx ^ 2 / t₀ + Hmaj * (Real.exp (-(μ * q)) + 1 / t₀ ^ 2)) / (2 * Real.pi) := by
    refine div_nonneg (mul_nonneg (mul_nonneg hCtot (by positivity)) (by linarith)) (by positivity)
  have hB : (0 : ℝ) ≤ (Real.log 2 + Lx) / D := by
    have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hC : (0 : ℝ) ≤ 2 * Lx / Real.sqrt xmin := by positivity
  rw [relScaledMajorant]
  linarith

/-- **The relative scaled envelope, bounded uniformly on an annulus.** -/
theorem relScaledEnvelope_le_uniform {A delta Ctot D τ x : ℝ}
    (hCtot : 0 ≤ Ctot) (hD : 0 < D) (hτ : 16 * Real.pi / 3 ≤ |τ|) (hx : 1 ≤ x)
    {Lx q μ t₀ σ xmin Hmaj : ℝ}
    (ht0 : 0 < t₀) (hlo : t₀ ≤ |τ|) (hhi : |τ| ≤ |σ|)
    (hLx : Real.log x ≤ Lx) (hq0 : 0 ≤ q) (hq : q ≤ Real.log x)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ min delta (routeTWidthPolylogLower A τ) / 2)
    (hxmin : 0 < xmin) (hxminx : xmin ≤ x)
    (hHmaj : 1 / t₀ + Real.log (3 * |σ| / 2) / routeTWidthPolylogLower A σ ≤ Hmaj) :
    relScaledEnvelope A delta Ctot D τ x
      ≤ relScaledMajorant Ctot D Lx Hmaj μ q t₀ xmin := by
  have hpi := Real.pi_gt_three
  have hτ1 : (1 : ℝ) ≤ |τ| := by linarith
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hLx0 : (0 : ℝ) ≤ Lx := le_trans hlogx hLx
  have hbase := relScaledEnvelope_le (A := A) (delta := delta) (Ctot := Ctot) (D := D)
    (τ := τ) (x := x) hCtot hD hτ hx hLx hq0 hq hμ0 hμ
  refine hbase.trans ?_
  have hHm := le_trans (scaledHeightMajorant_le_of_le (A := A) ht0 hlo hhi hτ1) hHmaj
  have hHm0 : (0 : ℝ) ≤ Hmaj := by
    have h0 := scaledHeightMajorant_nonneg (A := A) (τ := τ) hτ1
    linarith
  have hA1 : Lx ^ 2 / |τ| ≤ Lx ^ 2 / t₀ :=
    div_le_div_of_nonneg_left (by positivity) ht0 hlo
  have hA2 : 1 / |τ| ^ 2 ≤ 1 / t₀ ^ 2 := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [hlo, ht0]
  have hA3 : scaledHeightMajorant A τ * (Real.exp (-(μ * q)) + 1 / |τ| ^ 2)
      ≤ Hmaj * (Real.exp (-(μ * q)) + 1 / t₀ ^ 2) := by
    refine mul_le_mul hHm (by linarith) (by positivity)
      (by linarith [scaledHeightMajorant_nonneg (A := A) (τ := τ) hτ1])
  have hAtot : Ctot * D ^ 2
        * (Lx ^ 2 / |τ| + scaledHeightMajorant A τ * (Real.exp (-(μ * q)) + 1 / |τ| ^ 2))
        / (2 * Real.pi)
      ≤ Ctot * D ^ 2 * (Lx ^ 2 / t₀ + Hmaj * (Real.exp (-(μ * q)) + 1 / t₀ ^ 2))
        / (2 * Real.pi) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hB : Real.log (2 * x) / D ≤ (Real.log 2 + Lx) / D := by
    refine div_le_div_of_nonneg_right ?_ hD.le
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0)]
    linarith
  have hC : 2 * Real.log x / Real.sqrt x ≤ 2 * Lx / Real.sqrt xmin := by
    have hsx : (0 : ℝ) < Real.sqrt xmin := Real.sqrt_pos.2 hxmin
    have hsq : Real.sqrt xmin ≤ Real.sqrt x := Real.sqrt_le_sqrt hxminx
    have hinv : 1 / Real.sqrt x ≤ 1 / Real.sqrt xmin := one_div_le_one_div_of_le hsx hsq
    have hnum : 2 * Real.log x ≤ 2 * Lx := by linarith
    calc 2 * Real.log x / Real.sqrt x = (2 * Real.log x) * (1 / Real.sqrt x) := by ring
      _ ≤ (2 * Lx) * (1 / Real.sqrt xmin) :=
          mul_le_mul hnum hinv (by positivity) (by linarith)
      _ = 2 * Lx / Real.sqrt xmin := by ring
  rw [relScaledMajorant]
  linarith

/-- **The annulus bound on a ladder step, with an explicit relative constant.**  This is the form
`Sieve/LadderPrimeMajorant.primeStepMajorant_sq_ge` consumes. -/
theorem exists_norm_primeBlockPoly_geomBlock_rho_le :
    ∃ A delta Ctot τ₀ : ℝ, 0 < delta ∧ 0 < Ctot ∧ 2 ≤ τ₀ ∧
      ∀ (z₀ z L j : ℕ) (Q η D w t₀ σ Lx q μ xmin Hmaj : ℝ),
        1 ≤ z₀ → Q = (z₀ : ℝ) → 0 ≤ η → j + 1 ≤ L → z = ⌊Q * (1 + η) ^ L⌋₊ → 1 ≤ D →
        τ₀ ≤ |(-(2 * Real.pi * w))| → 16 * Real.pi / 3 ≤ |(-(2 * Real.pi * w))| →
        0 < t₀ → t₀ ≤ |(-(2 * Real.pi * w))| → |(-(2 * Real.pi * w))| ≤ |σ| →
        Real.log (max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) ≤ Lx →
        0 ≤ q → q ≤ Real.log (max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) →
        0 ≤ μ → μ ≤ min delta (routeTWidthPolylogLower A (-(2 * Real.pi * w))) / 2 →
        0 < xmin → xmin ≤ max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1 →
        1 / t₀ + Real.log (3 * |σ| / 2) / routeTWidthPolylogLower A σ ≤ Hmaj →
        ‖primeBlockPoly (geomBlock (primesRange z₀ z) Q (1 + η) j) w‖
          ≤ (4 / Real.log 2)
              * ((1 + η) * relScaledMajorant Ctot D Lx Hmaj μ q t₀ xmin
                + 7 * Real.exp 9 / Q) * (Q * (1 + η) ^ j) := by
  obtain ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, hbound⟩ :=
    exists_norm_primeBlockPoly_geomBlock_le
  refine ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, ?_⟩
  intro z₀ z L j Q η D w t₀ σ Lx q μ xmin Hmaj hz₀ hQ hη hj hz hD hτ₀le hτ ht0 hlo hhi
    hLx hq0 hq hμ0 hμ hxmin hxminx hHmaj
  have hpi := Real.pi_gt_three
  have hτ1 : (1 : ℝ) ≤ |(-(2 * Real.pi * w))| := by linarith
  have hmax1 : (1 : ℝ) ≤ max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1 := le_max_right _ _
  have hlogmax : (0 : ℝ) ≤ Real.log (max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) :=
    Real.log_nonneg hmax1
  have hLx0 : (0 : ℝ) ≤ Lx := le_trans hlogmax hLx
  have hHm0 : (0 : ℝ) ≤ Hmaj := by
    have h1 : (0 : ℝ) < 1 / t₀ := by positivity
    have h2 : (0 : ℝ) ≤ Real.log (3 * |σ| / 2) / routeTWidthPolylogLower A σ := by
      have hσ : (1 : ℝ) ≤ |σ| := le_trans hτ1 hhi
      exact div_nonneg (Real.log_nonneg (by linarith)) (routeTWidthPolylogLower_pos A σ).le
    linarith
  have hR0 : (0 : ℝ) ≤ relScaledMajorant Ctot D Lx Hmaj μ q t₀ xmin :=
    relScaledMajorant_nonneg hCtot.le (by linarith) hLx0 hHm0 ht0 hxmin
  have hRle := relScaledEnvelope_le_uniform (A := A) (delta := delta) (Ctot := Ctot) (D := D)
    (τ := -(2 * Real.pi * w)) (x := max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1)
    hCtot.le (by linarith) hτ hmax1 ht0 hlo hhi hLx hq0 hq hμ0 hμ hxmin hxminx hHmaj
  exact hbound z₀ z L j Q η D w (relScaledMajorant Ctot D Lx Hmaj μ q t₀ xmin)
    hz₀ hQ hη hj hz hD hτ₀le hR0 hRle

end

end RHTower.Sieve
