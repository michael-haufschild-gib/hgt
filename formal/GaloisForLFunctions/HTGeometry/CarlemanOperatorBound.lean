import GaloisForLFunctions.HTGeometry.CarlemanSchurWeight
import GaloisForLFunctions.HTGeometry.YoungConvolutionL2

/-!
# Schur's test for the Carleman kernel

The Carleman kernel `1/(s+t)` on the half line has `t^{-1/2}` as a Schur weight with constant `π`,
in both variables by symmetry.  Splitting the kernel against that weight and integrating gives the
sharp `L²` bound

`∫_0^∞ (∫_0^∞ f(t)/(s+t) dt)² ds ≤ π² ∫_0^∞ f(t)² dt`,

i.e. `‖S‖ ≤ π` for the Carleman transform.  Everything runs in `ℝ≥0∞`, where the Tonelli swap is
what proves joint integrability rather than what assumes it.
-/

open MeasureTheory Set Filter Topology ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Schur integrand is integrable on the ray. -/
theorem integrableOn_carlemanSchurWeight {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t => 1 / ((s + t) * Real.sqrt t)) (Ioi 0) volume := by
  refine integrableOn_Ioi_deriv_of_nonneg (g := carlemanSchurPrimitive s)
    (l := 2 / Real.sqrt s * (Real.pi / 2))
    (continuous_carlemanSchurPrimitive s).continuousWithinAt
    (fun t ht => hasDerivAt_carlemanSchurPrimitive hs ht) ?_
    (tendsto_carlemanSchurPrimitive hs)
  intro t ht
  have htt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hst : 0 < s + t := by linarith [mem_Ioi.mp ht]
  positivity

/-- **The Schur weight identity in `ℝ≥0∞`.** -/
theorem lintegral_carlemanSchurWeight {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / ((s + t) * Real.sqrt t)))
      = ENNReal.ofReal (Real.pi / Real.sqrt s) := by
  have hint := integrableOn_carlemanSchurWeight hs
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] fun t => 1 / ((s + t) * Real.sqrt t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hst : 0 < s + t := by linarith [mem_Ioi.mp ht]
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_carlemanSchurWeight hs]

/-- The pointwise Schur step for the Carleman kernel. -/
theorem sq_lintegral_carleman_le {F : ℝ → ℝ≥0∞} (hF : Measurable F) {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2
      ≤ ENNReal.ofReal (Real.pi / Real.sqrt s)
          * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (Real.sqrt t / (s + t)) * F t ^ 2 := by
  have hK : Measurable fun t : ℝ => ENNReal.ofReal (1 / ((s + t) * Real.sqrt t)) := by
    apply ENNReal.measurable_ofReal.comp
    fun_prop
  have hG : Measurable fun t : ℝ => F t * ENNReal.ofReal (Real.sqrt t) := by
    apply hF.mul
    apply ENNReal.measurable_ofReal.comp
    fun_prop
  have hbase := lintegral_weighted_sq_le (volume.restrict (Ioi (0:ℝ))) hK hG
  have hLHS : (∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (1 / ((s + t) * Real.sqrt t)) * (F t * ENNReal.ofReal (Real.sqrt t)))
      = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : (0:ℝ) < t := ht
    have htt : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
    have hst : 0 < s + t := by linarith
    have hmul : ENNReal.ofReal (1 / ((s + t) * Real.sqrt t)) * ENNReal.ofReal (Real.sqrt t)
        = ENNReal.ofReal (1 / (s + t)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    calc ENNReal.ofReal (1 / ((s + t) * Real.sqrt t)) * (F t * ENNReal.ofReal (Real.sqrt t))
        = (ENNReal.ofReal (1 / ((s + t) * Real.sqrt t)) * ENNReal.ofReal (Real.sqrt t)) * F t := by
          ring
      _ = ENNReal.ofReal (1 / (s + t)) * F t := by rw [hmul]
  have hRHS : (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / ((s + t) * Real.sqrt t))
        * (F t * ENNReal.ofReal (Real.sqrt t)) ^ 2)
      = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (Real.sqrt t / (s + t)) * F t ^ 2 := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : (0:ℝ) < t := ht
    have htt : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
    have hst : 0 < s + t := by linarith
    have hsq : ENNReal.ofReal (Real.sqrt t) ^ 2 = ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg t), Real.sq_sqrt htpos.le]
    have hts : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt htpos.le
    have hval : (1 / ((s + t) * Real.sqrt t)) * t = Real.sqrt t / (s + t) := by
      field_simp
      nlinarith [hts]
    have hmul : ENNReal.ofReal (1 / ((s + t) * Real.sqrt t)) * ENNReal.ofReal t
        = ENNReal.ofReal (Real.sqrt t / (s + t)) := by
      rw [← ENNReal.ofReal_mul (by positivity), hval]
    calc ENNReal.ofReal (1 / ((s + t) * Real.sqrt t)) * (F t * ENNReal.ofReal (Real.sqrt t)) ^ 2
        = (ENNReal.ofReal (1 / ((s + t) * Real.sqrt t)) * ENNReal.ofReal (Real.sqrt t) ^ 2)
            * F t ^ 2 := by ring
      _ = (ENNReal.ofReal (1 / ((s + t) * Real.sqrt t)) * ENNReal.ofReal t) * F t ^ 2 := by
          rw [hsq]
      _ = ENNReal.ofReal (Real.sqrt t / (s + t)) * F t ^ 2 := by rw [hmul]
  rw [hLHS, hRHS, lintegral_carlemanSchurWeight hs] at hbase
  exact hbase

/-- **Schur's test for the Carleman kernel**: the transform is bounded on `L²` with norm at most
`π`. -/
theorem lintegral_carleman_sq_le {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ s in Ioi (0:ℝ), (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2)
      ≤ ENNReal.ofReal (Real.pi ^ 2) * ∫⁻ t in Ioi (0:ℝ), F t ^ 2 := by
  set g : ℝ → ℝ → ℝ≥0∞ := fun s t =>
    ENNReal.ofReal (Real.pi / Real.sqrt s) * (ENNReal.ofReal (Real.sqrt t / (s + t)) * F t ^ 2)
    with hg
  have hprodmeas : Measurable fun p : ℝ × ℝ => g p.1 p.2 := by
    rw [hg]
    apply Measurable.mul
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul
        ((hF.comp measurable_snd).pow_const 2)
  have hstep : ∀ s ∈ Ioi (0:ℝ),
      (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2
        ≤ ∫⁻ t in Ioi (0:ℝ), g s t := by
    intro s hs
    have hmeas : Measurable fun t : ℝ =>
        ENNReal.ofReal (Real.sqrt t / (s + t)) * F t ^ 2 := by
      apply Measurable.mul _ (hF.pow_const 2)
      exact ENNReal.measurable_ofReal.comp (by fun_prop)
    simp only [hg]
    rw [lintegral_const_mul _ hmeas]
    exact sq_lintegral_carleman_le hF hs
  have houter : (∫⁻ s in Ioi (0:ℝ), (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2)
      ≤ ∫⁻ s in Ioi (0:ℝ), ∫⁻ t in Ioi (0:ℝ), g s t :=
    setLIntegral_mono' measurableSet_Ioi hstep
  have hswap : (∫⁻ s in Ioi (0:ℝ), ∫⁻ t in Ioi (0:ℝ), g s t)
      = ∫⁻ t in Ioi (0:ℝ), ∫⁻ s in Ioi (0:ℝ), g s t :=
    lintegral_lintegral_swap hprodmeas.aemeasurable
  have hinner : ∀ t ∈ Ioi (0:ℝ),
      (∫⁻ s in Ioi (0:ℝ), g s t) = ENNReal.ofReal (Real.pi ^ 2) * F t ^ 2 := by
    intro t ht
    have htpos : (0:ℝ) < t := ht
    have hts : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
    have hfac : ∀ s ∈ Ioi (0:ℝ), g s t
        = (ENNReal.ofReal (Real.pi * Real.sqrt t) * F t ^ 2)
            * ENNReal.ofReal (1 / ((t + s) * Real.sqrt s)) := by
      intro s hs
      have hspos : (0:ℝ) < s := hs
      have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
      have hst : 0 < s + t := by linarith
      have hval : (Real.pi / Real.sqrt s) * (Real.sqrt t / (s + t))
          = (Real.pi * Real.sqrt t) * (1 / ((t + s) * Real.sqrt s)) := by
        field_simp
        ring
      simp only [hg]
      calc ENNReal.ofReal (Real.pi / Real.sqrt s)
            * (ENNReal.ofReal (Real.sqrt t / (s + t)) * F t ^ 2)
          = (ENNReal.ofReal (Real.pi / Real.sqrt s)
              * ENNReal.ofReal (Real.sqrt t / (s + t))) * F t ^ 2 := by ring
        _ = ENNReal.ofReal ((Real.pi / Real.sqrt s) * (Real.sqrt t / (s + t))) * F t ^ 2 := by
            rw [← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal ((Real.pi * Real.sqrt t) * (1 / ((t + s) * Real.sqrt s)))
              * F t ^ 2 := by rw [hval]
        _ = (ENNReal.ofReal (Real.pi * Real.sqrt t) * F t ^ 2)
              * ENNReal.ofReal (1 / ((t + s) * Real.sqrt s)) := by
            rw [ENNReal.ofReal_mul (by positivity)]
            ring
    have hkermeas : Measurable fun x : ℝ => ENNReal.ofReal (1 / ((t + x) * Real.sqrt x)) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    rw [setLIntegral_congr_fun measurableSet_Ioi hfac,
      lintegral_const_mul _ hkermeas, lintegral_carlemanSchurWeight htpos]
    have hval2 : ENNReal.ofReal (Real.pi * Real.sqrt t) * ENNReal.ofReal (Real.pi / Real.sqrt t)
        = ENNReal.ofReal (Real.pi ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    calc ENNReal.ofReal (Real.pi * Real.sqrt t) * F t ^ 2
          * ENNReal.ofReal (Real.pi / Real.sqrt t)
        = (ENNReal.ofReal (Real.pi * Real.sqrt t) * ENNReal.ofReal (Real.pi / Real.sqrt t))
            * F t ^ 2 := by ring
      _ = ENNReal.ofReal (Real.pi ^ 2) * F t ^ 2 := by rw [hval2]
  calc (∫⁻ s in Ioi (0:ℝ), (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 / (s + t)) * F t) ^ 2)
      ≤ ∫⁻ s in Ioi (0:ℝ), ∫⁻ t in Ioi (0:ℝ), g s t := houter
    _ = ∫⁻ t in Ioi (0:ℝ), ∫⁻ s in Ioi (0:ℝ), g s t := hswap
    _ = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (Real.pi ^ 2) * F t ^ 2 :=
        setLIntegral_congr_fun measurableSet_Ioi hinner
    _ = ENNReal.ofReal (Real.pi ^ 2) * ∫⁻ t in Ioi (0:ℝ), F t ^ 2 :=
        lintegral_const_mul _ (hF.pow_const 2)

end

end GaloisForLFunctions.HTGeometry
