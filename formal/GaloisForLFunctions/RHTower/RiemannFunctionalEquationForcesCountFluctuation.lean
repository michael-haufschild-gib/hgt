import GaloisForLFunctions.RHTower.ZetaShiftRatioMeanSquareLimit
import GaloisForLFunctions.HTGeometry.GaussianWeightedLaplacePlancherel
import GaloisForLFunctions.RHTower.BeurlingOverRegularIntegersOffLineZeros

/-!
# The functional equation forces an order-one fluctuation of the integer count

A generalized-integer system with count `N(x) = ρx + C + E(x)` has, for `Re s > 1`,
`ζ(s) = ρ s/(s-1) + C + s ∫_1^∞ E(u) u^{-s-1} du`.  If `E(u) = O(u^{-p})` with `p > 0`, the right
side continues `ζ` to `Re s > -p`; in the coordinate `u = e^v` it is
`countContinuation ρ C g s = ρ s/(s-1) + C + s ∫_{v>0} g(v) e^{-sv} dv`, `g(v) = E(e^v)`.

**Theorem** (`false_of_functionalEquation_of_decaying_count`).  Let `-1/2 < σ < 0`, `p > -σ`,
`|g(v)| ≤ K e^{-pv}`, and let `Z` be bounded below by `c > 0` on the line `Re = 1 - σ`.  Then the
Riemann functional equation `Γ_ℝ(s) (countContinuation ρ C g s) = Γ_ℝ(1-s) Z(1-s)` cannot hold for
all `s = σ + it`, `t ≥ 4`.

**Proof.**
* *Growth forced by the functional equation.*  `‖Γ_ℝ(1-s)/Γ_ℝ(s)‖ ≥ κ t^{1/2-σ}`
  (`norm_Gammaℝ_one_sub_ge`, from the vertical Gamma ratio bound), so `‖ζ(σ+it)‖ ≥ cκ t^{1/2-σ}`
  and `∫_{3T/2}^{5T/2} ‖ζ(σ+it)‖² dt ≫ T^{2-2σ}`.
* *Growth allowed by a decaying count.*  `ρ s/(s-1) + C` is bounded on the line, and the Laplace
  transform of `h(v) = g(v)e^{-σv} ∈ L¹ ∩ L²` has window mean square `≤ 2π e^{1/4} ‖h‖₂²`
  (`HTGeometry.GaussianLaplace.integral_gaussW_mul_normSq_lapI_le`), so the same integral is
  `O(T²)`.  Since `2 - 2σ > 2` this is a contradiction.

**Corollary** (`overRegularZeta_not_functionalEquation`).  The over-regular Beurling zetas of
`BeurlingOverRegularIntegersOffLineZeros`, whose count error decays like `x^{-p₁}`, satisfy the
Riemann functional equation on no line `max(-p₁, -1/2) < σ < 0`.

So a decaying integer-count error is incompatible with the functional equation of `ζ`.  The
countermodels that keep the count error small are exactly those that give up the functional
equation; under the functional equation the count error must fluctuate at least as much as the
sawtooth of `⌊x⌋`, at every scale.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate
open HTGeometry.GaussianLaplace

namespace RHTower.FunctionalEquationCountFluctuation

noncomputable section

/-! ## The functional-equation factor -/

theorem norm_cpi_cpow (w : ℂ) : ‖(Real.pi : ℂ) ^ w‖ = Real.pi ^ w.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos w

/-- **The functional-equation factor grows like `t^{1/2-σ}` on a line `-1/2 < σ < 0`.**
`‖Γ_ℝ(1 - s)‖ ≥ ½ π^{σ-1/2} e^{-3(σ+1/2)/2} t^{1/2-σ} ‖Γ_ℝ(s)‖` for `s = σ + it`, `t ≥ 4`. -/
theorem norm_Gammaℝ_one_sub_ge {σ t : ℝ} (h1 : -1 / 2 < σ) (h2 : σ < 0) (ht : 4 ≤ t) :
    1 / 2 * Real.pi ^ (σ - 1 / 2) * Real.exp (-(3 * (σ + 1 / 2) / 2)) * t ^ (1 / 2 - σ) *
        ‖Gammaℝ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      ‖Gammaℝ (1 - ((σ : ℂ) + (t : ℂ) * I))‖ := by
  set τ : ℝ := t / 2 with hτ
  have hτ2 : 2 ≤ τ := by rw [hτ]; linarith
  have hτ0 : 0 < τ := by linarith
  have ht0 : 0 < t := by linarith
  set a : ℝ := (1 - σ) / 2 with ha
  set δ : ℝ := σ + 1 / 2 with hδ
  have ha0 : 0 < a := by rw [ha]; linarith
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  -- the two Gamma factors
  have hs2 : ((σ : ℂ) + (t : ℂ) * I) / 2 = ((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I := by
    rw [hτ]; push_cast; ring
  have hs1 : (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2 = conj ((a : ℂ) + (τ : ℂ) * I) := by
    rw [ha, hτ, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hnorm_s : ‖Gammaℝ ((σ : ℂ) + (t : ℂ) * I)‖ =
      Real.pi ^ (-σ / 2) * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
    rw [Gammaℝ, norm_mul, norm_cpi_cpow, hs2]
    congr 2
    simp
  have hnorm_1s : ‖Gammaℝ (1 - ((σ : ℂ) + (t : ℂ) * I))‖ =
      Real.pi ^ (-(1 - σ) / 2) * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := by
    rw [Gammaℝ, norm_mul, norm_cpi_cpow, hs1, Complex.Gamma_conj, Complex.norm_conj]
    congr 2
    simp
  -- `Γ(b + iτ) = (σ/2 + iτ) Γ(σ/2 + iτ)` with `b = a + δ = 1 + σ/2`
  have hz0 : ((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hshift : (((a + δ : ℝ)) : ℂ) + (τ : ℂ) * I = (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I) + 1 := by
    rw [ha, hδ]; push_cast; ring
  have hstep := RHTower.norm_Gamma_add_le_rpow_mul ha0 hδ0 hτ2
  rw [hshift, Complex.Gamma_add_one _ hz0, norm_mul] at hstep
  have hzn : τ ≤ ‖((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)
    simpa [abs_of_pos hτ0] using this
  have hGpos : 0 ≤ ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := norm_nonneg _
  have hbt : a + δ + τ ≤ t := by rw [ha, hδ, hτ]; linarith
  have hpow : (a + δ + τ) ^ δ ≤ t ^ δ :=
    Real.rpow_le_rpow (by rw [ha, hδ]; linarith) hbt hδ0
  -- `τ ‖Γ(σ/2 + iτ)‖ ≤ e^{3δ/2} t^δ ‖Γ(a + iτ)‖`
  have hkey : τ * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤
      Real.exp (3 * δ / 2) * t ^ δ * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := by
    calc τ * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖
        ≤ ‖((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I‖ *
            ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ :=
          mul_le_mul_of_nonneg_right hzn hGpos
      _ ≤ Real.exp (3 * δ / 2) * (a + δ + τ) ^ δ * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ :=
          hstep
      _ ≤ Real.exp (3 * δ / 2) * t ^ δ * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := by
          gcongr
  rw [hnorm_s, hnorm_1s]
  -- assemble: `t^{1/2-σ} t^δ = t` and `π^{σ-1/2} π^{-σ/2} = π^{-(1-σ)/2}`
  have htt : t ^ (1 / 2 - σ) * t ^ δ = t := by
    rw [← Real.rpow_add ht0, hδ, show (1 / 2 - σ + (σ + 1 / 2) : ℝ) = 1 by ring, Real.rpow_one]
  have hpp : Real.pi ^ (σ - 1 / 2) * Real.pi ^ (-σ / 2) = Real.pi ^ (-(1 - σ) / 2) := by
    rw [← Real.rpow_add Real.pi_pos]; congr 1; ring
  have hee : Real.exp (-(3 * (σ + 1 / 2) / 2)) * Real.exp (3 * δ / 2) = 1 := by
    rw [← Real.exp_add, hδ]; simp
  have hA : 0 ≤ 1 / 2 * Real.pi ^ (σ - 1 / 2) * Real.exp (-(3 * (σ + 1 / 2) / 2)) *
      t ^ (1 / 2 - σ) * Real.pi ^ (-σ / 2) := by positivity
  calc 1 / 2 * Real.pi ^ (σ - 1 / 2) * Real.exp (-(3 * (σ + 1 / 2) / 2)) * t ^ (1 / 2 - σ) *
        (Real.pi ^ (-σ / 2) * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖)
      = (1 / 2 * Real.pi ^ (σ - 1 / 2) * Real.exp (-(3 * (σ + 1 / 2) / 2)) * t ^ (1 / 2 - σ) *
          Real.pi ^ (-σ / 2) / τ) * (τ * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖) := by
        field_simp
    _ ≤ (1 / 2 * Real.pi ^ (σ - 1 / 2) * Real.exp (-(3 * (σ + 1 / 2) / 2)) * t ^ (1 / 2 - σ) *
          Real.pi ^ (-σ / 2) / τ) *
          (Real.exp (3 * δ / 2) * t ^ δ * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖) :=
        mul_le_mul_of_nonneg_left hkey (div_nonneg hA hτ0.le)
    _ = (Real.pi ^ (σ - 1 / 2) * Real.pi ^ (-σ / 2)) *
          (Real.exp (-(3 * (σ + 1 / 2) / 2)) * Real.exp (3 * δ / 2)) *
          (t ^ (1 / 2 - σ) * t ^ δ) / (2 * τ) * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := by
        field_simp
    _ = Real.pi ^ (-(1 - σ) / 2) * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := by
        rw [hpp, hee, htt, hτ]
        field_simp


/-! ## The main theorem -/

/-- The continuation `ρ s/(s-1) + C + s ∫_{v>0} g(v) e^{-sv} dv` given by a count error `g(v)`. -/
def countContinuation (ρ C : ℂ) (g : ℝ → ℝ) (s : ℂ) : ℂ :=
  ρ * s / (s - 1) + C + s * ∫ v in Ioi (0 : ℝ), (g v : ℂ) * cexp (-(s * v))

theorem Gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : Gammaℝ s ≠ 0 := by
  rw [Gammaℝ]
  refine mul_ne_zero ?_ (Complex.Gamma_ne_zero fun m h => ?_)
  · intro h0
    have := congrArg norm h0
    rw [norm_cpi_cpow, norm_zero] at this
    exact (Real.rpow_pos_of_pos Real.pi_pos _).ne' this
  · have := congrArg Complex.im h
    simp at this
    exact hs (by linarith)

/-- `‖s/(s-1)‖ ≤ 2` when `Re s ≤ 0`. -/
theorem norm_div_sub_one_le {s : ℂ} (hs : s.re ≤ 0) : ‖s / (s - 1)‖ ≤ 2 := by
  have h1 : 1 ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    simp only [Complex.sub_re, Complex.one_re] at this
    rw [abs_of_neg (by linarith)] at this
    linarith
  have hpos : 0 < ‖s - 1‖ := by linarith
  rw [norm_div, div_le_iff₀ hpos]
  have := norm_add_le (s - 1) 1
  rw [sub_add_cancel, norm_one] at this
  linarith

/-- The count error damped to the line `σ`: `h(v) = g(v) e^{-σv}`. -/
def dampedError (g : ℝ → ℝ) (σ v : ℝ) : ℝ := g v * Real.exp (-(σ * v))

theorem countContinuation_eq (ρ C : ℂ) (g : ℝ → ℝ) (σ t : ℝ) :
    countContinuation ρ C g ((σ : ℂ) + (t : ℂ) * I) =
      ρ * ((σ : ℂ) + (t : ℂ) * I) / (((σ : ℂ) + (t : ℂ) * I) - 1) + C +
        ((σ : ℂ) + (t : ℂ) * I) * lapI (dampedError g σ) t := by
  rw [countContinuation, lapI]
  congr 2
  congr 1
  funext v
  rw [dampedError]
  push_cast
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Decay `|g(v)| ≤ K e^{-pv}` with `p > -σ` puts the damped error in `L¹ ∩ L²` of `(0, ∞)`. -/
theorem dampedError_integrable {g : ℝ → ℝ} {σ p K : ℝ} (hgm : Measurable g) (hp : -σ < p)
    (hg : ∀ v, 0 < v → |g v| ≤ K * Real.exp (-p * v)) :
    Measurable (dampedError g σ) ∧ IntegrableOn (dampedError g σ) (Ioi 0) ∧
      IntegrableOn (fun v => dampedError g σ v ^ 2) (Ioi 0) := by
  have hκ0 : 0 < p + σ := by linarith
  have hmeas : Measurable (dampedError g σ) := by unfold dampedError; fun_prop
  have hbound : ∀ v, 0 < v → |dampedError g σ v| ≤ K * Real.exp (-(p + σ) * v) := by
    intro v hv
    rw [dampedError, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |g v| * Real.exp (-(σ * v)) ≤ K * Real.exp (-p * v) * Real.exp (-(σ * v)) :=
          mul_le_mul_of_nonneg_right (hg v hv) (Real.exp_pos _).le
      _ = K * Real.exp (-(p + σ) * v) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  refine ⟨hmeas, ?_, ?_⟩
  · exact ((integrableOn_exp_mul_Ioi (by linarith : -(p + σ) < 0) 0).const_mul K).mono'
      hmeas.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioi
        fun v hv => by rw [Real.norm_eq_abs]; exact hbound v hv)
  · refine ((integrableOn_exp_mul_Ioi (by linarith : -(2 * (p + σ)) < 0) 0).const_mul
      (K ^ 2)).mono' (hmeas.pow_const 2).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc |dampedError g σ v| ^ 2 ≤ (K * Real.exp (-(p + σ) * v)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (hbound v hv) 2
      _ = K ^ 2 * Real.exp (-(2 * (p + σ)) * v) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring

/-- `‖ρ s/(s-1) + C + sM‖² ≤ 2(2‖ρ‖ + ‖C‖)² + 2(σ² + t²)‖M‖²` on a line `Re s = σ ≤ 0`. -/
theorem normSq_continuation_le (ρ C M : ℂ) {σ : ℝ} (hσ : σ ≤ 0) (t : ℝ) :
    ‖ρ * ((σ : ℂ) + (t : ℂ) * I) / (((σ : ℂ) + (t : ℂ) * I) - 1) + C +
        ((σ : ℂ) + (t : ℂ) * I) * M‖ ^ 2 ≤
      2 * (2 * ‖ρ‖ + ‖C‖) ^ 2 + 2 * (σ ^ 2 + t ^ 2) * ‖M‖ ^ 2 := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re ≤ 0 := by rw [hs]; simp; linarith
  have h1 : ‖ρ * s / (s - 1)‖ ≤ 2 * ‖ρ‖ := by
    rw [mul_div_assoc, norm_mul]
    have := norm_div_sub_one_le hsre
    nlinarith [norm_nonneg ρ]
  have hns : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [hs, Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h2 : ‖ρ * s / (s - 1) + C + s * M‖ ≤ (2 * ‖ρ‖ + ‖C‖) + ‖s‖ * ‖M‖ := by
    calc ‖ρ * s / (s - 1) + C + s * M‖ ≤ ‖ρ * s / (s - 1) + C‖ + ‖s * M‖ := norm_add_le _ _
      _ ≤ (‖ρ * s / (s - 1)‖ + ‖C‖) + ‖s‖ * ‖M‖ :=
          add_le_add (norm_add_le _ _) (norm_mul _ _).le
      _ ≤ (2 * ‖ρ‖ + ‖C‖) + ‖s‖ * ‖M‖ := by linarith
  have hx : 0 ≤ ‖s‖ * ‖M‖ := by positivity
  have hm : 0 ≤ 2 * ‖ρ‖ + ‖C‖ := by positivity
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hexp : (‖s‖ * ‖M‖) ^ 2 = (σ ^ 2 + t ^ 2) * ‖M‖ ^ 2 := by rw [mul_pow, hns]
  nlinarith [sq_nonneg ((2 * ‖ρ‖ + ‖C‖) - ‖s‖ * ‖M‖)]

theorem volume_real_window {T : ℝ} (hT : 0 ≤ T) :
    volume.real (Icc (3 * T / 2) (5 * T / 2)) = T := by
  rw [Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- **Window lower bound.**  A continuous `L` with `‖L(t)‖ ≥ A t^{1/2-σ}` for `t ≥ 4` has
`∫_{3T/2}^{5T/2} ‖L‖² ≥ T · A² (3T/2)^{1-2σ}` for `T ≥ 8`. -/
theorem window_lower {L : ℝ → ℂ} (hL : Continuous L) {A σ : ℝ} (hA : 0 ≤ A) (hσ : σ < 1 / 2)
    (hlow : ∀ t : ℝ, 4 ≤ t → A * t ^ (1 / 2 - σ) ≤ ‖L t‖) {T : ℝ} (hT : 8 ≤ T) :
    T * (A ^ 2 * (3 * T / 2) ^ (1 - 2 * σ)) ≤ ∫ t in Icc (3 * T / 2) (5 * T / 2), ‖L t‖ ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hconst : ∫ t in Icc (3 * T / 2) (5 * T / 2), A ^ 2 * (3 * T / 2) ^ (1 - 2 * σ) =
      T * (A ^ 2 * (3 * T / 2) ^ (1 - 2 * σ)) := by
    rw [setIntegral_const, smul_eq_mul, volume_real_window hT0.le]
  rw [← hconst]
  refine setIntegral_mono_on continuous_const.integrableOn_Icc
    (hL.norm.pow 2).integrableOn_Icc measurableSet_Icc fun t ht => ?_
  have ht4 : 4 ≤ t := by linarith [ht.1]
  have hmono : (3 * T / 2) ^ (1 / 2 - σ) ≤ t ^ (1 / 2 - σ) :=
    Real.rpow_le_rpow (by positivity) ht.1 (by linarith)
  have hcl : A * (3 * T / 2) ^ (1 / 2 - σ) ≤ ‖L t‖ :=
    le_trans (mul_le_mul_of_nonneg_left hmono hA) (hlow t ht4)
  have hpow : ((3 * T / 2) ^ (1 / 2 - σ)) ^ 2 = (3 * T / 2) ^ (1 - 2 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  calc A ^ 2 * (3 * T / 2) ^ (1 - 2 * σ) = (A * (3 * T / 2) ^ (1 / 2 - σ)) ^ 2 := by
        rw [mul_pow, hpow]
    _ ≤ ‖L t‖ ^ 2 := pow_le_pow_left₀ (by positivity) hcl 2

/-- **Window upper bound.**  If `‖L(t)‖² ≤ 2m² + 2(σ² + t²)‖M(t)‖²` with `M` the Laplace transform
of `h ∈ L¹ ∩ L²`, then `∫_{3T/2}^{5T/2} ‖L‖² ≤ 2m²T + 14T² e^{1/4} 2π ∫h²` for `T ≥ 8`. -/
theorem window_upper {L : ℝ → ℂ} (hL : Continuous L) {h : ℝ → ℝ} (hmeas : Measurable h)
    (hh : IntegrableOn h (Ioi 0)) (hh2 : IntegrableOn (fun v => h v ^ 2) (Ioi 0)) {m σ : ℝ}
    (hσ : σ ^ 2 ≤ 1) (hLle : ∀ t : ℝ, ‖L t‖ ^ 2 ≤ 2 * m ^ 2 + 2 * (σ ^ 2 + t ^ 2) * ‖lapI h t‖ ^ 2)
    {T : ℝ} (hT : 8 ≤ T) :
    ∫ t in Icc (3 * T / 2) (5 * T / 2), ‖L t‖ ^ 2 ≤
      2 * m ^ 2 * T + 14 * T ^ 2 * Real.exp (1 / 4) *
        (2 * Real.pi * ∫ v in Ioi (0 : ℝ), h v ^ 2) := by
  have hT0 : 0 < T := by linarith
  have hlap_cont : Continuous (lapI h) := continuous_lapI hmeas hh
  have hgauss_int : Integrable (fun t => gaussW (2 * T) T t * ‖lapI h t‖ ^ 2) := by
    refine ((integrable_gaussW (2 * T) hT0).mul_const ((∫ v in Ioi (0 : ℝ), |h v|) ^ 2)).mono'
      ((continuous_gaussW _ _).mul (hlap_cont.norm.pow 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    have hw0 : 0 ≤ gaussW (2 * T) T t := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_lapI_le h t) 2) hw0
  have hplanch := integral_gaussW_mul_normSq_lapI_le hmeas hh hh2 (2 * T) hT0
  have hptw : ∀ t ∈ Icc (3 * T / 2) (5 * T / 2), ‖L t‖ ^ 2 ≤
      2 * m ^ 2 + 14 * T ^ 2 * Real.exp (1 / 4) * (gaussW (2 * T) T t * ‖lapI h t‖ ^ 2) := by
    intro t ht
    have hst : 2 * (σ ^ 2 + t ^ 2) ≤ 14 * T ^ 2 := by nlinarith [ht.1, ht.2]
    have hw : 1 ≤ Real.exp (1 / 4) * gaussW (2 * T) T t := by
      rw [gaussW, ← Real.exp_add]
      apply Real.one_le_exp
      have : ((t - 2 * T) / T) ^ 2 ≤ 1 / 4 := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        nlinarith [ht.1, ht.2]
      linarith
    have hM := sq_nonneg ‖lapI h t‖
    have h1 : 2 * (σ ^ 2 + t ^ 2) * ‖lapI h t‖ ^ 2 ≤ 14 * T ^ 2 * ‖lapI h t‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hst hM
    have h2 : 14 * T ^ 2 * ‖lapI h t‖ ^ 2 ≤
        14 * T ^ 2 * (Real.exp (1 / 4) * gaussW (2 * T) T t * ‖lapI h t‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc ‖lapI h t‖ ^ 2 = 1 * ‖lapI h t‖ ^ 2 := (one_mul _).symm
        _ ≤ Real.exp (1 / 4) * gaussW (2 * T) T t * ‖lapI h t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hw hM
    calc ‖L t‖ ^ 2 ≤ 2 * m ^ 2 + 2 * (σ ^ 2 + t ^ 2) * ‖lapI h t‖ ^ 2 := hLle t
      _ ≤ 2 * m ^ 2 + 14 * T ^ 2 * (Real.exp (1 / 4) * gaussW (2 * T) T t * ‖lapI h t‖ ^ 2) := by
          linarith
      _ = 2 * m ^ 2 + 14 * T ^ 2 * Real.exp (1 / 4) * (gaussW (2 * T) T t * ‖lapI h t‖ ^ 2) := by
          ring
  calc ∫ t in Icc (3 * T / 2) (5 * T / 2), ‖L t‖ ^ 2
      ≤ ∫ t in Icc (3 * T / 2) (5 * T / 2), (2 * m ^ 2 + 14 * T ^ 2 * Real.exp (1 / 4) *
          (gaussW (2 * T) T t * ‖lapI h t‖ ^ 2)) :=
        setIntegral_mono_on (hL.norm.pow 2).integrableOn_Icc
          (continuous_const.integrableOn_Icc.add (hgauss_int.integrableOn.const_mul _))
          measurableSet_Icc hptw
    _ = 2 * m ^ 2 * T + 14 * T ^ 2 * Real.exp (1 / 4) *
          ∫ t in Icc (3 * T / 2) (5 * T / 2), gaussW (2 * T) T t * ‖lapI h t‖ ^ 2 := by
        rw [integral_add continuous_const.integrableOn_Icc (hgauss_int.integrableOn.const_mul _),
          integral_const_mul (14 * T ^ 2 * Real.exp (1 / 4)), setIntegral_const, smul_eq_mul,
          volume_real_window hT0.le]
        ring
    _ ≤ 2 * m ^ 2 * T + 14 * T ^ 2 * Real.exp (1 / 4) *
          (2 * Real.pi * ∫ v in Ioi (0 : ℝ), h v ^ 2) := by
        gcongr
        exact (setIntegral_le_integral hgauss_int (Filter.Eventually.of_forall fun t =>
          mul_nonneg (Real.exp_pos _).le (sq_nonneg _))).trans hplanch

/-- A polynomial bound `D T^{2+E} ≤ B T²` with `E > 0` fails for large `T`. -/
theorem false_of_window_bounds {D B E : ℝ} (hD : 0 < D) (hE : 0 < E)
    (h : ∀ T : ℝ, 8 ≤ T → D * T ^ E * T ^ 2 ≤ B * T ^ 2) : False := by
  have hlim : Tendsto (fun T : ℝ => T ^ E) atTop atTop := tendsto_rpow_atTop hE
  obtain ⟨T, hT8, hTbig⟩ := ((eventually_ge_atTop 8).and (hlim.eventually_gt_atTop (B / D))).exists
  have hT2 : 0 < T ^ 2 := by positivity
  have := le_of_mul_le_mul_right (h T hT8) hT2
  rw [div_lt_iff₀ hD] at hTbig
  linarith

/-- **The Riemann functional equation is incompatible with a decaying count error.** -/
theorem false_of_functionalEquation_of_decaying_count {σ p K c : ℝ} (hσ1 : -1 / 2 < σ)
    (hσ2 : σ < 0) (hp : -σ < p) (hc : 0 < c) {g : ℝ → ℝ} (hgm : Measurable g)
    (hg : ∀ v, 0 < v → |g v| ≤ K * Real.exp (-p * v)) (ρ C : ℂ) (Z : ℂ → ℂ)
    (hZ : ∀ t : ℝ, 4 ≤ t → c ≤ ‖Z (1 - ((σ : ℂ) + (t : ℂ) * I))‖)
    (hFE : ∀ t : ℝ, 4 ≤ t →
      Gammaℝ ((σ : ℂ) + (t : ℂ) * I) * countContinuation ρ C g ((σ : ℂ) + (t : ℂ) * I) =
        Gammaℝ (1 - ((σ : ℂ) + (t : ℂ) * I)) * Z (1 - ((σ : ℂ) + (t : ℂ) * I))) : False := by
  obtain ⟨hmeas, hhint, hhint2⟩ := dampedError_integrable (σ := σ) hgm hp hg
  have hχc0 : 0 < 1 / 2 * Real.pi ^ (σ - 1 / 2) * Real.exp (-(3 * (σ + 1 / 2) / 2)) := by
    positivity
  -- the functional equation forces `‖ζ(σ + it)‖ ≥ cκ t^{1/2-σ}`
  have hlow : ∀ t : ℝ, 4 ≤ t →
      c * (1 / 2 * Real.pi ^ (σ - 1 / 2) * Real.exp (-(3 * (σ + 1 / 2) / 2))) *
        t ^ (1 / 2 - σ) ≤ ‖countContinuation ρ C g ((σ : ℂ) + (t : ℂ) * I)‖ := by
    intro t ht
    have hG : 0 < ‖Gammaℝ ((σ : ℂ) + (t : ℂ) * I)‖ :=
      norm_pos_iff.mpr (Gammaℝ_ne_zero_of_im_ne_zero (by simp; linarith))
    have hfe := congrArg norm (hFE t ht)
    rw [norm_mul, norm_mul] at hfe
    have hχ := norm_Gammaℝ_one_sub_ge hσ1 hσ2 ht
    have key : (c * (1 / 2 * Real.pi ^ (σ - 1 / 2) * Real.exp (-(3 * (σ + 1 / 2) / 2))) *
          t ^ (1 / 2 - σ)) * ‖Gammaℝ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        ‖countContinuation ρ C g ((σ : ℂ) + (t : ℂ) * I)‖ * ‖Gammaℝ ((σ : ℂ) + (t : ℂ) * I)‖ := by
      rw [mul_comm (‖countContinuation ρ C g _‖), hfe, mul_comm (‖Gammaℝ (1 - _)‖)]
      calc c * (1 / 2 * Real.pi ^ (σ - 1 / 2) * Real.exp (-(3 * (σ + 1 / 2) / 2))) *
            t ^ (1 / 2 - σ) * ‖Gammaℝ ((σ : ℂ) + (t : ℂ) * I)‖
          = c * (1 / 2 * Real.pi ^ (σ - 1 / 2) * Real.exp (-(3 * (σ + 1 / 2) / 2)) *
              t ^ (1 / 2 - σ) * ‖Gammaℝ ((σ : ℂ) + (t : ℂ) * I)‖) := by ring
        _ ≤ ‖Z (1 - ((σ : ℂ) + (t : ℂ) * I))‖ * ‖Gammaℝ (1 - ((σ : ℂ) + (t : ℂ) * I))‖ :=
            mul_le_mul (hZ t ht) hχ (by positivity) (norm_nonneg _)
    exact le_of_mul_le_mul_right key hG
  -- continuity of the continuation on the line
  have hs_cont : Continuous fun t : ℝ => ((σ : ℂ) + (t : ℂ) * I) := by fun_prop
  have hsne : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I) - 1 ≠ 0 := by
    intro t h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hLcont : Continuous fun t : ℝ => countContinuation ρ C g ((σ : ℂ) + (t : ℂ) * I) := by
    simp_rw [countContinuation_eq]
    exact (((continuous_const.mul hs_cont).div (hs_cont.sub continuous_const) hsne).add
      continuous_const).add (hs_cont.mul (continuous_lapI hmeas hhint))
  have hLle : ∀ t : ℝ, ‖countContinuation ρ C g ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      2 * (2 * ‖ρ‖ + ‖C‖) ^ 2 + 2 * (σ ^ 2 + t ^ 2) * ‖lapI (dampedError g σ) t‖ ^ 2 := by
    intro t
    rw [countContinuation_eq]
    exact normSq_continuation_le ρ C _ hσ2.le t
  -- compare the two window bounds
  set A : ℝ := c * (1 / 2 * Real.pi ^ (σ - 1 / 2) * Real.exp (-(3 * (σ + 1 / 2) / 2)))
  set H : ℝ := ∫ v in Ioi (0 : ℝ), dampedError g σ v ^ 2
  have hσsq : σ ^ 2 ≤ 1 := by nlinarith
  refine false_of_window_bounds (D := A ^ 2 * (3 / 2) ^ (1 - 2 * σ))
    (B := 2 * (2 * ‖ρ‖ + ‖C‖) ^ 2 + 14 * Real.exp (1 / 4) * (2 * Real.pi * H)) (E := -2 * σ)
    (by positivity) (by linarith) fun T hT => ?_
  have hT0 : 0 < T := by linarith
  have hlo := window_lower hLcont (by positivity) (by linarith) hlow hT
  have hup := window_upper hLcont hmeas hhint hhint2 hσsq hLle hT
  have hsplit : T * (A ^ 2 * (3 * T / 2) ^ (1 - 2 * σ)) =
      A ^ 2 * (3 / 2) ^ (1 - 2 * σ) * T ^ (-2 * σ) * T ^ 2 := by
    rw [show 3 * T / 2 = (3 / 2) * T by ring, Real.mul_rpow (by norm_num) hT0.le,
      show (1 - 2 * σ) = (-2 * σ) + 1 by ring, Real.rpow_add hT0, Real.rpow_one]
    ring
  have hH0 : 0 ≤ H := setIntegral_nonneg measurableSet_Ioi fun v _ => sq_nonneg _
  have hTT : T ≤ T ^ 2 := by nlinarith
  have hm0 : 0 ≤ 2 * (2 * ‖ρ‖ + ‖C‖) ^ 2 := by positivity
  rw [← hsplit]
  calc T * (A ^ 2 * (3 * T / 2) ^ (1 - 2 * σ))
      ≤ 2 * (2 * ‖ρ‖ + ‖C‖) ^ 2 * T + 14 * T ^ 2 * Real.exp (1 / 4) * (2 * Real.pi * H) :=
        hlo.trans hup
    _ ≤ (2 * (2 * ‖ρ‖ + ‖C‖) ^ 2 + 14 * Real.exp (1 / 4) * (2 * Real.pi * H)) * T ^ 2 := by
        have := mul_le_mul_of_nonneg_left hTT hm0
        nlinarith

end

end RHTower.FunctionalEquationCountFluctuation
