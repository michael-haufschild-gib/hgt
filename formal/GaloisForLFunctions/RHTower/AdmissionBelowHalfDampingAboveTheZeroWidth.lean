import GaloisForLFunctions.RHTower.TheDampedMoebiusMellinQuotientIsHardyRightOfTheZeroAbscissa
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusMellin
import GaloisForLFunctions.RHTower.ReceiverDampingsAccumulateAboveTheZeros
import GaloisForLFunctions.RHTower.ArchimedeanMellinFourier
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw
import GaloisForLFunctions.HTGeometry.HalfLineLaplaceFourier
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1

/-!
# Admission below half damping above the zero width

Let `Θ = zetaZeroAbscissa`. For every damping `ε > Θ − ½` the power-damped Möbius Fermi source is
square-integrable, i.e. the damped Möbius receiver has a horizon-uniform budget
(`mem_receiverDampings_of_zetaZeroAbscissa_lt`). This is the converse of
`zetaZeroAbscissa_le_of_accPt_receiverDampings`, and together they give the exact exponent law

`receiverDampingRate = zetaZeroAbscissa − ½`   (`receiverDampingRate_eq_zetaZeroAbscissa_sub_half`),

so that RH is `receiverDampingRate = 0`, the accumulation of admissible dampings at `0`, and the
cofinal budget criterion is an equivalence (`riemannHypothesis_iff_cofinal_budget`).

**Mechanism.** The source `f_ε` lives on `(0, 1]`; inversion `g(u) = u⁻¹ f_ε(1/u)` turns it into a
tail datum on `(1, ∞)` with the same `L²` mass and with right Mellin transform
`∫_1^∞ u^{−s} g(u) du = mellin f_ε s = (1 − 2^{1−s}) ζ(s)/(s ζ(s+ε))` on the strip
`max(½, 1 − ε) < Re s < 1` (`mellinTail_invertedFermiSource`). The quotient is Mellin–Hardy right of
`½` when `Θ < ½ + ε`, so Paley–Wiener gives a datum `h ∈ L²(1, ∞)` with the same right Mellin
transform on `Re s > ½`. In the logarithmic chart both data have the same half-line Laplace
transform on a vertical line inside the strip, so the damped difference has vanishing Fourier
transform and is zero almost everywhere (`ae_eq_zero_of_fourierIntegral_eq_zero`). Hence `g = h`
almost everywhere, `g` is square-integrable, and so is `f_ε`.
-/

open Complex Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped FourierTransform

noncomputable section
set_option autoImplicit false

namespace RHTower

open Sieve

/-! ### The inverted source -/

/-- The inverted Fermi source, a tail datum on `(1, ∞)`: `g(u) = u⁻¹ f_ε(1/u)`. -/
def invertedFermiSource (ε : ℝ) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator fun u => ((u⁻¹ : ℝ) : ℂ) * pmPowerDampedFermiSource ε u⁻¹

theorem measurable_invertedFermiSource (ε : ℝ) : Measurable (invertedFermiSource ε) :=
  ((Complex.measurable_ofReal.comp measurable_inv).mul
    ((measurable_pmPowerDampedFermiSource ε).comp measurable_inv)).indicator measurableSet_Ioi

/-- The pointwise form of the inversion: for `v > 0`,
`v^{−2} · (v⁻¹)^{s−1} · z = v^{−s} · (v⁻¹ · z)`. -/
theorem inv_sq_smul_cpow_smul {v : ℝ} (hv : 0 < v) (s : ℂ) (z : ℂ) :
    (v ^ 2)⁻¹ • (((v⁻¹ : ℝ) : ℂ) ^ (s - 1) • z) = (v : ℂ) ^ (-s) * (((v⁻¹ : ℝ) : ℂ) * z) := by
  have hv0 : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [ofReal_inv_cpow hv, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv,
    Complex.ofReal_inv, Complex.ofReal_pow, show -(s - 1) = -s + 1 by ring,
    Complex.cpow_add _ _ hv0, Complex.cpow_one]
  field_simp

/-- Almost every real is not `1`. -/
theorem ae_ne_one : ∀ᵐ v : ℝ ∂volume, v ≠ 1 := by
  rw [ae_iff]
  simp only [not_not, setOf_eq_eq_singleton, Real.volume_singleton]

/-- Off the point `1`, the pulled-back Mellin integrand of the source is the tail integrand of the
inverted source. -/
theorem pullback_eq_invertedFermiSource (ε : ℝ) (s : ℂ) {v : ℝ} (hv : 0 < v) (hv1 : v ≠ 1) :
    (v ^ 2)⁻¹ • (((v⁻¹ : ℝ) : ℂ) ^ (s - 1) • pmPowerDampedFermiSource ε v⁻¹) =
      ((v : ℝ) : ℂ) ^ (-s) * invertedFermiSource ε v := by
  rw [inv_sq_smul_cpow_smul hv, invertedFermiSource]
  rcases lt_or_gt_of_ne hv1 with h | h
  · have hinv : 1 < v⁻¹ := one_lt_inv_iff₀.mpr ⟨hv, h⟩
    rw [pmPowerDampedFermiSource_eq_zero_of_one_lt ε hinv,
      indicator_of_notMem (show v ∉ Ioi (1 : ℝ) by simpa using h.le)]
    simp
  · rw [indicator_of_mem (mem_Ioi.mpr h)]

/-- The Mellin transform of the source over `(0, ∞)` is the right Mellin transform of the
inverted source over `(1, ∞)`. -/
theorem mellinTail_invertedFermiSource (ε : ℝ) (s : ℂ) :
    (∫ t in Ioi (1 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * invertedFermiSource ε t) =
      mellin (pmPowerDampedFermiSource ε) s := by
  rw [mellin, integral_Ioi_comp_inv (fun t : ℝ => (t : ℂ) ^ (s - 1) • pmPowerDampedFermiSource ε t)]
  have hcongr : ∫ v in Ioi (0 : ℝ),
      (v ^ 2)⁻¹ • (((v⁻¹ : ℝ) : ℂ) ^ (s - 1) • pmPowerDampedFermiSource ε v⁻¹) =
      ∫ v in Ioi (0 : ℝ), ((v : ℝ) : ℂ) ^ (-s) * invertedFermiSource ε v := by
    refine integral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
    filter_upwards [ae_ne_one] with v hv1 hv0
    exact pullback_eq_invertedFermiSource ε s hv0 hv1
  rw [hcongr]
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi zero_le_one) fun v hv => ?_
  simp only [invertedFermiSource, indicator_of_notMem hv.2, mul_zero]

/-- The tail integrand of the inverted source is integrable on `(1, ∞)` on the Mellin strip. -/
theorem integrableOn_cpow_mul_invertedFermiSource (ε : ℝ) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) (hsε : 1 < s.re + ε) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * invertedFermiSource ε t) (Ioi 1) := by
  have hM : MellinConvergent (pmPowerDampedFermiSource ε) s :=
    (hasMellin_pmPowerDampedFermiSource ε hs0 hs1 hsε).1
  have hderiv : ∀ v ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => u⁻¹) (-(v ^ 2)⁻¹) (Ioi 0) v := fun v hv =>
    (hasDerivAt_inv (ne_of_gt (mem_Ioi.mp hv))).hasDerivWithinAt
  have hJ := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv
    injOn_inv_Ioi (fun t : ℝ => (t : ℂ) ^ (s - 1) • pmPowerDampedFermiSource ε t)
  rw [image_inv_Ioi] at hJ
  have h0 : IntegrableOn (fun v : ℝ => ((v : ℝ) : ℂ) ^ (-s) * invertedFermiSource ε v)
      (Ioi 0) := by
    refine (hJ.mp hM).congr_fun_ae ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
    filter_upwards [ae_ne_one] with v hv1 hv0
    have hv : 0 < v := hv0
    rw [abs_neg, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < v ^ 2)]
    exact pullback_eq_invertedFermiSource ε s hv hv1
  exact h0.mono_set (Ioi_subset_Ioi zero_le_one)

/-- The square mass of the source on `(0, ∞)` is the square mass of the inverted source on
`(1, ∞)`, so square-integrability transfers back. -/
theorem memLp_source_of_memLp_inverted {ε : ℝ}
    (hg : MemLp (invertedFermiSource ε) 2 (volume.restrict (Ioi 1))) :
    MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi 0)) := by
  rw [memLp_two_iff_integrable_sq_norm
    (measurable_pmPowerDampedFermiSource ε).aestronglyMeasurable]
  have hderiv : ∀ v ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => u⁻¹) (-(v ^ 2)⁻¹) (Ioi 0) v := fun v hv =>
    (hasDerivAt_inv (ne_of_gt (mem_Ioi.mp hv))).hasDerivWithinAt
  have hJ := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv
    injOn_inv_Ioi (fun t : ℝ => ‖pmPowerDampedFermiSource ε t‖ ^ (2 : ℕ))
  rw [image_inv_Ioi] at hJ
  change IntegrableOn _ (Ioi (0 : ℝ)) volume
  rw [hJ]
  have hsq : ∀ v : ℝ, 0 < v → v ≠ 1 →
      |-(v ^ 2)⁻¹| • ‖pmPowerDampedFermiSource ε v⁻¹‖ ^ (2 : ℕ) =
        ‖invertedFermiSource ε v‖ ^ (2 : ℕ) := by
    intro v hv hv1
    rw [abs_neg, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < v ^ 2), smul_eq_mul,
      invertedFermiSource]
    rcases lt_or_gt_of_ne hv1 with h | h
    · have hinv : 1 < v⁻¹ := one_lt_inv_iff₀.mpr ⟨hv, h⟩
      rw [pmPowerDampedFermiSource_eq_zero_of_one_lt ε hinv,
        indicator_of_notMem (show v ∉ Ioi (1 : ℝ) by simpa using h.le)]
      simp
    · rw [indicator_of_mem (mem_Ioi.mpr h), norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_inv, abs_of_pos hv, mul_pow, inv_pow]
  have hint : IntegrableOn (fun v : ℝ => ‖invertedFermiSource ε v‖ ^ (2 : ℕ)) (Ioi 0) := by
    have h1 : IntegrableOn (fun v : ℝ => ‖invertedFermiSource ε v‖ ^ (2 : ℕ)) (Ioi 1) :=
      (memLp_two_iff_integrable_sq_norm
        (measurable_invertedFermiSource ε).aestronglyMeasurable).mp hg
    have h0 : IntegrableOn (fun v : ℝ => ‖invertedFermiSource ε v‖ ^ (2 : ℕ)) (Ioc (0 : ℝ) 1) := by
      refine (integrable_zero ℝ ℝ volume).integrableOn.congr_fun ?_
        (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1))
      intro v hv
      simp [invertedFermiSource, indicator_of_notMem (show v ∉ Ioi (1 : ℝ) by
        simpa using hv.2)]
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact h0.union h1
  refine hint.congr_fun_ae ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
  filter_upwards [ae_ne_one] with v hv1 hv0
  exact (hsq v hv0 hv1).symm

/-! ### The logarithmic chart of the inverted source -/

/-- The chart and its inverse are mutually inverse at aperture `1`. -/
theorem logChartInv_logChart_one (g : ℝ → ℂ) {t : ℝ} (ht : 0 < t) :
    logChartInv 1 (logChart 1 g) t = g t := by
  have hsqrt : Real.exp (Real.log t / 2) = Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    congr 1
    ring
  have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  simp only [logChartInv, logChart, div_one, one_mul, Real.sqrt_one, Real.exp_log ht, hsqrt]
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hs0, Complex.ofReal_one, one_mul]

/-- In the chart at aperture `1`, the Laplace integrand at `w` is the exponential-scale pullback
of the tail Mellin integrand at `w + ½`. -/
theorem logChart_one_mul_expRay (g : ℝ → ℂ) (w : ℂ) (x : ℝ) :
    logChart 1 g x * expRay w x =
      (1 * Real.exp x) • ((((1 * Real.exp x : ℝ)) : ℂ) ^ (-(w + 1 / 2)) * g (1 * Real.exp x)) := by
  have hex : Complex.exp (x : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have hcpow : Complex.exp (x : ℂ) ^ (-(w + 1 / 2)) = Complex.exp (-(w + 1 / 2) * x) := by
    rw [Complex.cpow_def_of_ne_zero hex, Complex.log_exp
      (by rw [Complex.ofReal_im]; linarith [Real.pi_pos])
      (by rw [Complex.ofReal_im]; linarith [Real.pi_pos])]
    ring_nf
  simp only [one_mul, logChart, expRay, Real.sqrt_one, Complex.real_smul,
    Complex.ofReal_exp, Complex.ofReal_div]
  rw [hcpow]
  have hkey : Complex.exp ((x : ℂ) / 2) * Complex.exp (-(w * x)) =
      Complex.exp (x : ℂ) * Complex.exp (-(w + 1 / 2) * x) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  linear_combination (g (Real.exp x)) * hkey

/-- Integrability of the chart of the inverted source against `e^{−wx}` on the ray, for `Re w`
inside the Mellin strip. -/
theorem integrableOn_logChart_invertedFermiSource_mul_expRay (ε : ℝ) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1 / 2) (hwε : 1 / 2 < w.re + ε) :
    IntegrableOn (fun x : ℝ => logChart 1 (invertedFermiSource ε) x * expRay w x) (Ioi 0) := by
  have hs0 : 0 < (w + 1 / 2).re := by simp; linarith
  have hs1 : (w + 1 / 2).re < 1 := by simp; linarith
  have hsε : 1 < (w + 1 / 2).re + ε := by simp; linarith
  have htail := integrableOn_cpow_mul_invertedFermiSource ε hs0 hs1 hsε
  rw [integrableOn_Ioi_expScale one_pos] at htail
  exact htail.congr_fun (fun x _ => (logChart_one_mul_expRay _ w x).symm) measurableSet_Ioi

/-! ### The identification -/

/-- **Admission above the zero width.** For `Θ < ½ + ε` the Fermi source at damping `ε` is
square-integrable, i.e. `ε` is an admissible damping. -/
theorem mem_receiverDampings_of_zetaZeroAbscissa_lt {ε : ℝ}
    (hΘ : zetaZeroAbscissa < 1 / 2 + ε) : ε ∈ receiverDampings := by
  have hε : 0 < ε := by linarith [half_le_zetaZeroAbscissa]
  rw [mem_receiverDampings_iff_memLp hε]
  -- the Paley–Wiener datum
  obtain ⟨h, hh, hhF⟩ :=
    exists_memLp_of_isMellinTailHardy one_pos (isMellinTailHardy_etaZetaQuotient hΘ)
  -- a vertical line inside the strip: `Re w = τ`, `τ := (max 0 (½ − ε) + ½)/2`
  set τ : ℝ := (max 0 (1 / 2 - ε) + 1 / 2) / 2 with hτdef
  have hτ0 : 0 < τ := by
    have := le_max_left 0 (1 / 2 - ε); rw [hτdef]; linarith
  have hτ1 : τ < 1 / 2 := by
    have : max 0 (1 / 2 - ε) < 1 / 2 := max_lt (by norm_num) (by linarith)
    rw [hτdef]; linarith
  have hτε : 1 / 2 < τ + ε := by
    have := le_max_right 0 (1 / 2 - ε); rw [hτdef]; linarith
  -- the two Laplace transforms agree on the line
  have hlap : ∀ ξ : ℝ, laplaceRay (logChart 1 h) (rayLine τ ξ) = laplaceRay (logChart 1 (invertedFermiSource ε)) (rayLine τ ξ) := by
    intro ξ
    set s : ℂ := rayLine τ ξ + 1 / 2 with hsdef
    have hs_re : s.re = τ + 1 / 2 := by simp [hsdef, rayLine]
    have hs_half : 1 / 2 < s.re := by rw [hs_re]; linarith
    have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by rw [hs_re]; linarith
    have hsε : 1 < s.re + ε := by rw [hs_re]; linarith
    have hs_ne1 : s ≠ 1 := fun h1 => by rw [h1, one_re] at hs1; linarith
    have hsε_ne1 : s + (ε : ℂ) ≠ 1 := fun h1 => by
      have := congrArg Complex.re h1
      simp only [add_re, ofReal_re, one_re] at this
      linarith
    -- both tail Mellin transforms equal the quotient
    have h1 : (∫ t in Ioi (1 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * h t) = etaZetaQuotient ε s := hhF s hs_half
    have h2 : (∫ t in Ioi (1 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * invertedFermiSource ε t) =
        etaZetaQuotient ε s := by
      rw [mellinTail_invertedFermiSource,
        (hasMellin_pmPowerDampedFermiSource ε hs0 hs1 hsε).2, etaZetaQuotient_eq hs_ne1 hsε_ne1]
    -- convert to Laplace transforms in the chart
    have e1 := mellinTail_eq_laplaceRay one_pos h s
    have e2 := mellinTail_eq_laplaceRay one_pos (invertedFermiSource ε) s
    have hone : (((1 : ℝ)) : ℂ) ^ ((1 : ℂ) / 2 - s) = 1 := by
      rw [Complex.ofReal_one, Complex.one_cpow]
    have hsw : s - 1 / 2 = rayLine τ ξ := by rw [hsdef]; ring
    rw [hone, one_mul, hsw] at e1 e2
    rw [← e1, ← e2, h1, h2]
  -- integrability of the damped data on the line
  have hφ₁L : MemLp (logChart 1 h) 2 (volume.restrict (Ioi 0)) := memLp_two_logChart one_pos hh
  have hint1 : ∀ ξ : ℝ,
      IntegrableOn (fun x : ℝ => logChart 1 h x * expRay (rayLine τ ξ) x) (Ioi 0) :=
    fun ξ => integrableOn_laplaceRay hφ₁L (by rw [rayLine_re]; exact hτ0)
  have hint2 : ∀ ξ : ℝ, IntegrableOn
      (fun x : ℝ => logChart 1 (invertedFermiSource ε) x * expRay (rayLine τ ξ) x) (Ioi 0) :=
    fun ξ => integrableOn_logChart_invertedFermiSource_mul_expRay ε
      (by rw [rayLine_re]; exact hτ0) (by rw [rayLine_re]; exact hτ1) (by rw [rayLine_re]; exact hτε)
  -- the difference has vanishing Fourier transform
  have hdamp : rayDamp (logChart 1 h - logChart 1 (invertedFermiSource ε)) τ =
      rayDamp (logChart 1 h) τ - rayDamp (logChart 1 (invertedFermiSource ε)) τ := by
    funext x
    simp only [rayDamp, Pi.sub_apply, indicator_apply, sub_mul]
    split_ifs <;> simp
  have hintdiff : Integrable (rayDamp (logChart 1 h - logChart 1 (invertedFermiSource ε)) τ) := by
    rw [hdamp]
    have i1 : Integrable (rayDamp (logChart 1 h) τ) := integrable_rayDamp hφ₁L hτ0
    have i2 : Integrable (rayDamp (logChart 1 (invertedFermiSource ε)) τ) := by
      rw [rayDamp, integrable_indicator_iff measurableSet_Ioi]
      have := hint2 0
      simpa [rayLine] using this
    exact i1.sub i2
  have hfour : ∀ ξ : ℝ,
      𝓕 (rayDamp (logChart 1 h - logChart 1 (invertedFermiSource ε)) τ) ξ = 0 := by
    intro ξ
    rw [fourierIntegral_rayDamp]
    have hsub : laplaceRay (logChart 1 h - logChart 1 (invertedFermiSource ε)) (rayLine τ ξ) =
        laplaceRay (logChart 1 h) (rayLine τ ξ) -
          laplaceRay (logChart 1 (invertedFermiSource ε)) (rayLine τ ξ) := by
      simp only [laplaceRay, Pi.sub_apply, sub_mul]
      exact integral_sub (hint1 ξ) (hint2 ξ)
    rw [hsub, hlap ξ, sub_self]
  have hae := HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hintdiff hfour
  -- hence the charts agree almost everywhere on the ray
  have hφ : logChart 1 h =ᵐ[volume.restrict (Ioi 0)] logChart 1 (invertedFermiSource ε) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    filter_upwards [hae] with x hx hx0
    simp only [rayDamp, indicator_of_mem hx0, Pi.sub_apply, Pi.zero_apply, sub_mul] at hx
    have hexp : expRay ((τ : ℝ) : ℂ) x ≠ 0 := Complex.exp_ne_zero _
    have h2 : (logChart 1 h x - logChart 1 (invertedFermiSource ε) x) *
        expRay ((τ : ℝ) : ℂ) x = 0 := by rw [sub_mul]; exact hx
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hexp)
  have hφ₂L : MemLp (logChart 1 (invertedFermiSource ε)) 2 (volume.restrict (Ioi 0)) :=
    hφ₁L.ae_eq hφ
  -- back to the inverted source and to the source
  have hgL : MemLp (invertedFermiSource ε) 2 (volume.restrict (Ioi 1)) := by
    refine (memLp_two_logChartInv one_pos hφ₂L).ae_eq ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    exact Eventually.of_forall fun t ht =>
      logChartInv_logChart_one (invertedFermiSource ε) (by linarith [mem_Ioi.mp ht])
  exact memLp_source_of_memLp_inverted hgL

/-! ### The exact exponent law -/

/-- Every damping above the zero width `Θ − ½` is admissible. -/
theorem Ioi_zetaZeroAbscissa_sub_half_subset_receiverDampings :
    Ioi (zetaZeroAbscissa - 1 / 2) ⊆ receiverDampings := fun ε hε =>
  mem_receiverDampings_of_zetaZeroAbscissa_lt (by linarith [mem_Ioi.mp hε])

/-- The receiver damping rate is at most the zero width. -/
theorem receiverDampingRate_le_zetaZeroAbscissa_sub_half :
    receiverDampingRate ≤ zetaZeroAbscissa - 1 / 2 :=
  csInf_le bddBelow_derivedSet_receiverDampings (mem_derivedSet.mpr
    (accPt_of_Ioo_subset (lt_add_one _) fun _ hx =>
      Ioi_zetaZeroAbscissa_sub_half_subset_receiverDampings hx.1))

/-- **The receiver damping rate is the zero width.** -/
theorem receiverDampingRate_eq_zetaZeroAbscissa_sub_half :
    receiverDampingRate = zetaZeroAbscissa - 1 / 2 :=
  le_antisymm receiverDampingRate_le_zetaZeroAbscissa_sub_half
    (by linarith [zetaZeroAbscissa_le_half_add_receiverDampingRate])

/-- RH is the vanishing of the receiver damping rate. -/
theorem riemannHypothesis_iff_receiverDampingRate_eq_zero :
    RiemannHypothesis ↔ receiverDampingRate = 0 := by
  rw [receiverDampingRate_eq_zetaZeroAbscissa_sub_half, sub_eq_zero,
    zetaZeroAbscissa_eq_half_iff_riemannHypothesis]

/-- RH is the accumulation of admissible dampings at `0`. -/
theorem riemannHypothesis_iff_accPt_zero_receiverDampings :
    RiemannHypothesis ↔ AccPt (0 : ℝ) (𝓟 receiverDampings) :=
  riemannHypothesis_iff_receiverDampingRate_eq_zero.trans receiverDampingRate_eq_zero_iff_accPt_zero

/-- **The cofinal budget criterion is an equivalence.** -/
theorem riemannHypothesis_iff_cofinal_budget :
    RiemannHypothesis ↔
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
        ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B :=
  riemannHypothesis_iff_receiverDampingRate_eq_zero.trans
    receiverDampingRate_eq_zero_iff_cofinal_budget

/-- Under RH every positive damping is admissible. -/
theorem Ioi_zero_subset_receiverDampings_of_riemannHypothesis (h : RiemannHypothesis) :
    Ioi (0 : ℝ) ⊆ receiverDampings := by
  have hΘ : zetaZeroAbscissa = 1 / 2 := zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr h
  intro ε hε
  exact mem_receiverDampings_of_zetaZeroAbscissa_lt (by rw [hΘ]; linarith [mem_Ioi.mp hε])

end RHTower
