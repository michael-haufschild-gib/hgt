import GaloisForLFunctions.RHTower.ModularArcLogEdgeWitness
import GaloisForLFunctions.RHTower.BesselIZeroODE

/-!
# Arc measures blind to the decaying first mode are positive on the growing first mode

Parametrize the bottom arc of the standard fundamental domain by `u ∈ [−½, ½]`, `y = √(1 − u²)`.
Let `ν` be a nonzero finite measure on the arc which annihilates the first two decaying Whittaker
cosine modes `√y K₀(2πmy) cos(2πmu)`, `m = 1, 2`.  Then `ν` is strictly positive on the growing first
mode:

  `∫ √y I₀(2πy) cos(2πu) dν > 0`.

**Mechanism (cosine rearrangement).**  Both factors of
`(I₀(2πy) − λ K₀(2πy)) · cos(2πu)`, with `λ = I₀/K₀` evaluated at the height over `u = ¼`, change sign
exactly at `|u| = ¼`: the height `y` decreases in `|u|` and `I₀/K₀` increases in `y`.  So this
integrand is nonnegative, and strictly positive away from `|u| = ¼`.  Integrating against `ν` and using
the blindness to `√y K₀(2πy) cos(2πu)` gives the claim.  Blindness to the second mode only excludes
the degenerate case of `ν` concentrated on `|u| = ¼`.

The cusp harmonic measure of the fundamental domain annihilates every decaying Whittaker mode, so it
satisfies the hypotheses.  In that case the theorem says that the solution of `(y²Δ + ¼)V = 0`
vanishing on the arc and growing like `√y I₀(2πy) cos 2πx` at the cusp has a strictly negative `√y`
coefficient.

The module also proves the general form `integral_mul_cos_pos_of_ratio`, which replaces `(I₀, K₀)` by
any pair `(F, G)` with `G > 0` and `F/G` decreasing in `|u|`.
-/

open MeasureTheory Set Filter
open RHTower.BesselKZero
open GaloisForLFunctions.RHTower (besselI0 continuous_besselI0 monotoneOn_besselI0 besselI0_pos)

namespace RHTower

noncomputable section

/-! ### Positivity and strict monotonicity of `K₀` -/

theorem kMoment_pos_of_pos (j : ℕ) {r : ℝ} (hr : 0 < r) : 0 < kMoment j r := by
  rw [kMoment_eq]
  have hint := integrableOn_kIntegrand j hr
  rw [integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall (kIntegrand_nonneg j r)) hint]
  have hsupp : Function.support (kIntegrand j r) = univ := by
    ext t
    simp only [Function.mem_support, mem_univ, iff_true]
    unfold kIntegrand
    exact (mul_pos (pow_pos (Real.cosh_pos t) j) (Real.exp_pos _)).ne'
  rw [hsupp, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

theorem strictAntiOn_kMoment_zero : StrictAntiOn (kMoment 0) (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) (continuousOn_kMoment 0) fun r hr => ?_
  rw [interior_Ioi] at hr
  rw [deriv_kMoment 0 hr]
  exact neg_neg_of_pos (kMoment_pos_of_pos 1 hr)

/-! ### Geometry of the arc -/

/-- The point `u = ¼` of the arc. -/
def arcQuarter : ArcParam := ⟨1 / 4, by constructor <;> norm_num⟩

theorem modularArcHeight_lt_of_abs_lt {u v : ℝ} (hv : |v| ≤ 1) (h : |u| < |v|) :
    modularArcHeight v < modularArcHeight u := by
  unfold modularArcHeight
  have h1 : u ^ 2 < v ^ 2 := by
    rw [← sq_abs u, ← sq_abs v]
    exact pow_lt_pow_left₀ h (abs_nonneg u) two_ne_zero
  have h2 : v ^ 2 ≤ 1 := by
    rw [← sq_abs v]
    nlinarith [abs_nonneg v]
  exact Real.sqrt_lt_sqrt (by linarith) (by linarith)

theorem abs_le_half_of_arc (u : ArcParam) : |(u : ℝ)| ≤ 1 / 2 :=
  abs_le.mpr ⟨by linarith [u.2.1], u.2.2⟩

theorem cos_two_pi_mul_pos_of_abs_lt {u : ℝ} (h : |u| < 1 / 4) :
    0 < Real.cos (2 * Real.pi * u) := by
  rw [← Real.cos_abs, abs_mul, abs_of_pos Real.two_pi_pos]
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
  · have := abs_nonneg u
    nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

theorem cos_two_pi_mul_neg_of_abs_gt {u : ℝ} (h : 1 / 4 < |u|) (h' : |u| ≤ 1 / 2) :
    Real.cos (2 * Real.pi * u) < 0 := by
  rw [← Real.cos_abs, abs_mul, abs_of_pos Real.two_pi_pos]
  refine Real.cos_neg_of_pi_div_two_lt_of_lt ?_ ?_
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-! ### The general cosine rearrangement inequality -/

/-- **Cosine rearrangement on the arc.**  If `G > 0`, the ratio `F/G` is larger than its value at
`|u| = ¼` for `|u| < ¼` and smaller for `|u| > ¼`, and the finite measure `ν` annihilates
`G cos(2πu)` without being concentrated on `|u| = ¼`, then `∫ F cos(2πu) dν > 0`. -/
theorem integral_mul_cos_pos_of_ratio {ν : Measure ArcParam} [IsFiniteMeasure ν]
    {F G : ArcParam → ℝ} (hF : Continuous F) (hG : Continuous G) (hGpos : ∀ u, 0 < G u)
    (hlt : ∀ u : ArcParam, |(u : ℝ)| < 1 / 4 → F arcQuarter / G arcQuarter < F u / G u)
    (hgt : ∀ u : ArcParam, 1 / 4 < |(u : ℝ)| → F u / G u < F arcQuarter / G arcQuarter)
    (hblind : ∫ u, G u * Real.cos (2 * Real.pi * u) ∂ν = 0)
    (hsupp : ν {u : ArcParam | |(u : ℝ)| ≠ 1 / 4} ≠ 0) :
    0 < ∫ u, F u * Real.cos (2 * Real.pi * u) ∂ν := by
  set c := F arcQuarter / G arcQuarter with hc
  set H : ArcParam → ℝ := fun u => (F u - c * G u) * Real.cos (2 * Real.pi * u) with hH
  have hcos : Continuous fun u : ArcParam => Real.cos (2 * Real.pi * u) := by fun_prop
  have hHcont : Continuous H := ((hF.sub (continuous_const.mul hG)).mul hcos)
  have hfactor : ∀ u, F u - c * G u = G u * (F u / G u - c) := by
    intro u
    field_simp [(hGpos u).ne']
  have hHpos : ∀ u : ArcParam, |(u : ℝ)| ≠ 1 / 4 → 0 < H u := by
    intro u hu
    rw [hH]
    dsimp only
    rw [hfactor]
    rcases lt_or_gt_of_ne hu with h | h
    · exact mul_pos (mul_pos (hGpos u) (sub_pos.mpr (hlt u h)))
        (cos_two_pi_mul_pos_of_abs_lt h)
    · exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (hGpos u) (sub_neg.mpr (hgt u h)))
        (cos_two_pi_mul_neg_of_abs_gt h (abs_le_half_of_arc u))
  have hHnonneg : ∀ u, 0 ≤ H u := by
    intro u
    by_cases hu : |(u : ℝ)| = 1 / 4
    · rw [hH]
      dsimp only
      have hcos0 : Real.cos (2 * Real.pi * u) = 0 := by
        rw [← Real.cos_abs, abs_mul, abs_of_pos Real.two_pi_pos, hu]
        rw [show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two]
      rw [hcos0, mul_zero]
    · exact (hHpos u hu).le
  have hsplit : ∫ u, F u * Real.cos (2 * Real.pi * u) ∂ν =
      ∫ u, H u ∂ν + c * ∫ u, G u * Real.cos (2 * Real.pi * u) ∂ν := by
    have hI2 : Integrable (fun u : ArcParam => c * (G u * Real.cos (2 * Real.pi * u))) ν :=
      (integrable_of_continuous_arc (hG.mul hcos)).const_mul c
    have hadd := integral_add (integrable_of_continuous_arc hHcont) hI2
    rw [← integral_const_mul, ← hadd]
    congr 1
    funext u
    rw [hH]
    ring
  rw [hsplit, hblind, mul_zero, add_zero,
    integral_pos_iff_support_of_nonneg hHnonneg (integrable_of_continuous_arc hHcont)]
  refine lt_of_lt_of_le (pos_iff_ne_zero.mpr hsupp) (measure_mono fun u hu => ?_)
  exact (hHpos u hu).ne'

/-! ### The growing first Whittaker mode -/

theorem arcWhittakerCos_zero_apply (u : ArcParam) :
    arcWhittakerCos 0 u = Real.sqrt (modularArcHeight u) *
      kMoment 0 (2 * Real.pi * modularArcHeight u) * Real.cos (2 * Real.pi * u) := by
  simp [arcWhittakerCos, arcCosMode_apply, arcFreq, mul_assoc]

theorem continuous_modularArcHeight_arc : Continuous fun u : ArcParam => modularArcHeight u := by
  unfold modularArcHeight; fun_prop

/-- A nonzero finite arc measure blind to the second decaying cosine mode is not concentrated on
`|u| = ¼`. -/
theorem measure_abs_ne_quarter_ne_zero {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (h2 : ∫ u, arcWhittakerCos 1 u ∂ν = 0) : ν {u : ArcParam | |(u : ℝ)| ≠ 1 / 4} ≠ 0 := by
  intro h0
  have hae : ∀ᵐ u : ArcParam ∂ν, |(u : ℝ)| = 1 / 4 := by
    rw [ae_iff]
    simpa using h0
  set y₀ := modularArcHeight (1 / 4) with hy₀
  have hval : ∀ u : ArcParam, |(u : ℝ)| = 1 / 4 →
      arcWhittakerCos 1 u = -(Real.sqrt y₀ * kMoment 0 (arcFreq 1 * y₀)) := by
    intro u hu
    have hsq : (u : ℝ) ^ 2 = (1 / 4) ^ 2 := by rw [← sq_abs, hu]
    have hy : modularArcHeight u = y₀ := by
      rw [hy₀]; unfold modularArcHeight; rw [hsq]
    have hcos : Real.cos (arcFreq 1 * u) = -1 := by
      rw [← Real.cos_abs, abs_mul, abs_of_pos (arcFreq_pos 1), hu]
      unfold arcFreq
      rw [show 2 * Real.pi * ((((1 : ℕ) : ℝ)) + 1) * (1 / 4) = Real.pi by push_cast; ring,
        Real.cos_pi]
    rw [arcWhittakerCos, arcCosMode_apply, hy, hcos]
    ring
  have hcongr : ∫ u, arcWhittakerCos 1 u ∂ν =
      ∫ _u, -(Real.sqrt y₀ * kMoment 0 (arcFreq 1 * y₀)) ∂ν :=
    integral_congr_ae (hae.mono fun u hu => hval u hu)
  rw [hcongr, integral_const, smul_eq_mul] at h2
  have hy₀pos : 0 < y₀ := modularArcHeight_pos ⟨by norm_num, by norm_num⟩
  have hK : 0 < kMoment 0 (arcFreq 1 * y₀) := kMoment_pos_of_pos 0 (mul_pos (arcFreq_pos 1) hy₀pos)
  have hmass : 0 < ν.real univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (by simpa using hν) (measure_ne_top ν univ)
  have : ν.real univ * -(Real.sqrt y₀ * kMoment 0 (arcFreq 1 * y₀)) < 0 :=
    mul_neg_of_pos_of_neg hmass (neg_neg_of_pos (mul_pos (Real.sqrt_pos.mpr hy₀pos) hK))
  linarith

/-- **The growing first mode is strictly positive on every arc measure blind to the first two decaying
modes.**  For a nonzero finite measure `ν` on the arc with `∫ √y K₀(2πmy) cos(2πmu) dν = 0` for
`m = 1, 2`:  `∫ √y I₀(2πy) cos(2πu) dν > 0`. -/
theorem integral_growingWhittakerCos_pos {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (h1 : ∫ u, arcWhittakerCos 0 u ∂ν = 0) (h2 : ∫ u, arcWhittakerCos 1 u ∂ν = 0) :
    0 < ∫ u, Real.sqrt (modularArcHeight u) * besselI0 (2 * Real.pi * modularArcHeight u) *
        Real.cos (2 * Real.pi * u) ∂ν := by
  set G : ArcParam → ℝ := fun u =>
    Real.sqrt (modularArcHeight u) * kMoment 0 (2 * Real.pi * modularArcHeight u) with hGdef
  set F : ArcParam → ℝ := fun u =>
    Real.sqrt (modularArcHeight u) * besselI0 (2 * Real.pi * modularArcHeight u) with hFdef
  have hy : ∀ u : ArcParam, 0 < modularArcHeight u := fun u => modularArcHeight_pos u.2
  have hGpos : ∀ u, 0 < G u := fun u =>
    mul_pos (Real.sqrt_pos.mpr (hy u)) (kMoment_pos_of_pos 0 (mul_pos Real.two_pi_pos (hy u)))
  have hGcont : Continuous G := by
    refine (Real.continuous_sqrt.comp continuous_modularArcHeight_arc).mul ?_
    exact (continuousOn_kMoment 0).comp_continuous
      (continuous_const.mul continuous_modularArcHeight_arc)
      fun u => mul_pos Real.two_pi_pos (hy u)
  have hFcont : Continuous F :=
    (Real.continuous_sqrt.comp continuous_modularArcHeight_arc).mul
      (continuous_besselI0.comp (continuous_const.mul continuous_modularArcHeight_arc))
  have hratio : ∀ u, F u / G u =
      besselI0 (2 * Real.pi * modularArcHeight u) / kMoment 0 (2 * Real.pi * modularArcHeight u) := by
    intro u
    rw [hFdef, hGdef]
    dsimp only
    rw [mul_div_mul_left _ _ (Real.sqrt_pos.mpr (hy u)).ne']
  -- the ratio `I₀/K₀` is strictly increasing in the height
  have hmono : ∀ u v : ArcParam, modularArcHeight u < modularArcHeight v → F u / G u < F v / G v := by
    intro u v huv
    rw [hratio, hratio]
    have hu' := mul_pos Real.two_pi_pos (hy u)
    have hv' := mul_pos Real.two_pi_pos (hy v)
    have hlt : 2 * Real.pi * modularArcHeight u < 2 * Real.pi * modularArcHeight v :=
      mul_lt_mul_of_pos_left huv Real.two_pi_pos
    have hI : besselI0 (2 * Real.pi * modularArcHeight u) ≤
        besselI0 (2 * Real.pi * modularArcHeight v) :=
      monotoneOn_besselI0 (mem_Ici.mpr hu'.le) (mem_Ici.mpr hv'.le) hlt.le
    have hK : kMoment 0 (2 * Real.pi * modularArcHeight v) <
        kMoment 0 (2 * Real.pi * modularArcHeight u) :=
      strictAntiOn_kMoment_zero hu' hv' hlt
    have hKv := kMoment_pos_of_pos 0 hv'
    calc besselI0 (2 * Real.pi * modularArcHeight u) / kMoment 0 (2 * Real.pi * modularArcHeight u)
        ≤ besselI0 (2 * Real.pi * modularArcHeight v) /
            kMoment 0 (2 * Real.pi * modularArcHeight u) :=
          div_le_div_of_nonneg_right hI (kMoment_pos_of_pos 0 hu').le
      _ < besselI0 (2 * Real.pi * modularArcHeight v) /
            kMoment 0 (2 * Real.pi * modularArcHeight v) :=
          div_lt_div_of_pos_left (besselI0_pos _) hKv hK
  have hquarter : |((arcQuarter : ArcParam) : ℝ)| = 1 / 4 := by
    simp [arcQuarter, abs_of_pos]
  have hblind : ∫ u, G u * Real.cos (2 * Real.pi * u) ∂ν = 0 := by
    rw [← h1]
    congr 1
    funext u
    rw [arcWhittakerCos_zero_apply]
  have h := integral_mul_cos_pos_of_ratio (ν := ν) hFcont hGcont hGpos
    (fun u hu => hmono _ _ (modularArcHeight_lt_of_abs_lt (by rw [hquarter]; norm_num)
      (by rw [hquarter]; exact hu)))
    (fun u hu => hmono _ _ (modularArcHeight_lt_of_abs_lt
      ((abs_le_half_of_arc u).trans (by norm_num)) (by rw [hquarter]; exact hu)))
    hblind (measure_abs_ne_quarter_ne_zero hν h2)
  simpa [hFdef] using h

/-- The positive, self-dual, Whittaker-blind arc measure of `exists_arcWitness` (the cusp harmonic
measure of the fundamental domain) is strictly positive on the growing first Whittaker mode. -/
theorem exists_arcWitness_growingWhittakerCos_pos :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ n : ℕ, ∫ u, arcWhittakerCos n u ∂ν = 0 ∧ ∫ u, arcWhittakerSin n u ∂ν = 0) ∧
      0 < ∫ u, Real.sqrt (modularArcHeight u) * besselI0 (2 * Real.pi * modularArcHeight u) *
        Real.cos (2 * Real.pi * u) ∂ν := by
  obtain ⟨ν, hfin, hne, hsym, hblind, -⟩ := exists_arcWitness
  exact ⟨ν, hfin, hne, hsym, hblind,
    integral_growingWhittakerCos_pos hne (hblind 0).1 (hblind 1).1⟩

end

end RHTower
