import Mathlib
import GaloisForLFunctions.RHTower.SuzukiWienerNeumannMajorant
import GaloisForLFunctions.RHTower.SuzukiWienerMixedNormCarrier
import GaloisForLFunctions.HTGeometry.PhysicalLogChart

/-!
# The Wiener carrier is nuclear in position, and the physical log measure is not free

The word-majorant theorem: applying the high-pass Neumann inverse to a single-root source gives a
coefficient family dominated by the translated fixed kernel, so the valuation sum of `L²` norms
pays exactly `(L₀ - C - M)⁻¹` — the exact inverse of the widened margin.  Two oriented roots pay
it twice.  In the boundary-log chart, the half-weight `e^{-L/2}` is precisely the conjugation
making `r = e^{-L}` an `L²` isometry of the whole ray.

The obstruction half: a unit frequency band arbitrarily far out has an inverse transform that is
continuous and nonzero at the origin, so its squared modulus against `dr/r` diverges — no
free-standing high-tail `dr/r` upgrade exists, and only the coupled low/high boundary-moment lock
can supply the physical measure.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set GaloisForLFunctions.HTGeometry
open scoped ENNReal FourierTransform RealInnerProductSpace

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Convolution against a single-atom source evaluates the kernel at the shifted coefficient. -/
theorem discreteConv_single_atom (x : G → ℂ) (B : ℂ) (ρ ν : G) :
    discreteConv x (fun σ => if σ = ρ then B else 0) ν = x (ν - ρ) * B := by
  rw [discreteConv, tsum_eq_single (ν - ρ) (fun μ hμ => by
    have hne : ν - μ ≠ ρ := fun h => hμ (by rw [← h, sub_sub_cancel])
    rw [if_neg hne, mul_zero])]
  rw [if_pos (sub_sub_cancel ν ρ)]

/-- **The exact inverse-margin mass** — `L₀⁻¹ (1 - (C+M)/L₀)⁻¹ = (L₀ - (C+M))⁻¹`. -/
theorem wienerInverseMass_eq {x l : ℝ≥0∞} (hx : x < l) (hl : l ≠ ⊤) :
    l⁻¹ * (1 - x / l)⁻¹ = (l - x)⁻¹ := by
  have hl0 : l ≠ 0 := (lt_of_le_of_lt (by simp : (0 : ℝ≥0∞) ≤ x) hx).ne'
  have hxtop : x ≠ ⊤ := ne_top_of_lt hx
  have hdiv : x / l < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl hl0) (Or.inl hl)]
    simpa using hx
  have hsub0 : (1 : ℝ≥0∞) - x / l ≠ 0 := (tsub_pos_of_lt hdiv).ne'
  have hlx0 : l - x ≠ 0 := (tsub_pos_of_lt hx).ne'
  have hLHS : l⁻¹ * (1 - x / l)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hl0) (ENNReal.inv_ne_top.mpr hsub0)
  have hRHS : (l - x)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hlx0
  rw [← ENNReal.toReal_eq_toReal_iff' hLHS hRHS]
  have hxl : x / l ≤ 1 := le_of_lt hdiv
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_inv,
    ENNReal.toReal_sub_of_le hxl (by norm_num), ENNReal.toReal_sub_of_le hx.le hl,
    ENNReal.toReal_div, ENNReal.toReal_one]
  have hlr : (0 : ℝ) < l.toReal := ENNReal.toReal_pos hl0 hl
  have hxr : x.toReal < l.toReal := by
    exact (ENNReal.toReal_lt_toReal hxtop hl).mpr hx
  field_simp

/-- **The single-root nuclear bound** — the card's `(3)`: the valuation sum of `L²` norms of the
Neumann-inverse carrier pays exactly the inverse widened margin `(L₀ - (C+M))⁻¹`. -/
theorem tsum_eLpNorm_wienerSingleRoot_le {μ : Measure ℝ}
    {L q : ℝ → ℂ} {t : G → ℂ} {C L0 : ℝ} {B : ℝ → ℂ} {ρ : G}
    (hq : ∀ ξ, ‖q ξ‖ₑ ≤ ENNReal.ofReal C) (hL : ∀ ξ, ENNReal.ofReal L0 ≤ ‖L ξ‖ₑ)
    (hB : AEStronglyMeasurable B μ)
    (hth : ENNReal.ofReal C + (discreteMass fun ν => ‖t ν‖ₑ) < ENNReal.ofReal L0) :
    (∑' ν : G, eLpNorm
        (fun ξ => wienerNeumannInverse (L ξ) (q ξ) t (ν - ρ) * B ξ) 2 μ)
      ≤ (ENNReal.ofReal L0 - (ENNReal.ofReal C + discreteMass fun ν => ‖t ν‖ₑ))⁻¹
          * eLpNorm B 2 μ := by
  set K : G → ℝ≥0∞ := fun ν =>
    (ENNReal.ofReal L0)⁻¹ * discreteNeumannKernel (wienerStarKernel C L0 t) ν with hK
  have hmassK : discreteMass K
      = (ENNReal.ofReal L0)⁻¹
          * (1 - (ENNReal.ofReal C + discreteMass fun ν => ‖t ν‖ₑ)
              / ENNReal.ofReal L0)⁻¹ := discreteMass_wienerInverseKernel C L0 t
  have hmassK' : discreteMass K
      = (ENNReal.ofReal L0 - (ENNReal.ofReal C + discreteMass fun ν => ‖t ν‖ₑ))⁻¹ := by
    rw [hmassK, wienerInverseMass_eq hth ENNReal.ofReal_ne_top]
  have hmassKt : discreteMass (fun ν => K (ν - ρ)) ≠ ⊤ := by
    rw [discreteMass_comp_sub, hmassK']
    exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hth).ne'
  have hdom : ∀ ν : G, ∀ᵐ ξ ∂μ,
      ‖wienerNeumannInverse (L ξ) (q ξ) t (ν - ρ) * B ξ‖ₑ
        ≤ K (ν - ρ) * ‖B ξ‖ₑ + 0 * ‖B ξ‖ₑ := by
    intro ν
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [enorm_mul, zero_mul, add_zero]
    exact mul_le_mul' (enorm_wienerNeumannInverse_le (hq ξ) (hL ξ) (ν - ρ)) le_rfl
  have h := tsum_eLpNorm_le_twoKernel (Km := fun ν => K (ν - ρ)) (Kp := fun _ => 0)
    hB hB hmassKt (by simp [discreteMass]) hdom
  calc (∑' ν : G, eLpNorm
      (fun ξ => wienerNeumannInverse (L ξ) (q ξ) t (ν - ρ) * B ξ) 2 μ)
      ≤ discreteMass (fun ν => K (ν - ρ)) * eLpNorm B 2 μ
          + discreteMass (fun _ : G => (0 : ℝ≥0∞)) * eLpNorm B 2 μ := h
    _ = (ENNReal.ofReal L0 - (ENNReal.ofReal C + discreteMass fun ν => ‖t ν‖ₑ))⁻¹
          * eLpNorm B 2 μ := by
        rw [discreteMass_comp_sub, hmassK']
        have h0 : discreteMass (fun _ : G => (0 : ℝ≥0∞)) = 0 := by
          simp [discreteMass]
        rw [h0, zero_mul, add_zero]

/-- **The two-root nuclear bound** — the card's `(4)`: any coefficient family dominated by the
two translated Neumann kernels against the two Hardy amplitudes pays the inverse margin once for
each root. -/
theorem tsum_eLpNorm_wienerTwoRoot_le {μ : Measure ℝ}
    {t : G → ℂ} {C L0 : ℝ} {Bm Bp : ℝ → ℂ} {ρm ρp : G} {chat : G → ℝ → ℂ}
    (hBm : AEStronglyMeasurable Bm μ) (hBp : AEStronglyMeasurable Bp μ)
    (hth : ENNReal.ofReal C + (discreteMass fun ν => ‖t ν‖ₑ) < ENNReal.ofReal L0)
    (hdom : ∀ ν, ∀ᵐ ξ ∂μ, ‖chat ν ξ‖ₑ
      ≤ ((ENNReal.ofReal L0)⁻¹
            * discreteNeumannKernel (wienerStarKernel C L0 t) (ν - ρm)) * ‖Bm ξ‖ₑ
        + ((ENNReal.ofReal L0)⁻¹
            * discreteNeumannKernel (wienerStarKernel C L0 t) (ν - ρp)) * ‖Bp ξ‖ₑ) :
    (∑' ν : G, eLpNorm (chat ν) 2 μ)
      ≤ (ENNReal.ofReal L0 - (ENNReal.ofReal C + discreteMass fun ν => ‖t ν‖ₑ))⁻¹
          * (eLpNorm Bm 2 μ + eLpNorm Bp 2 μ) := by
  set K : G → ℝ≥0∞ := fun ν =>
    (ENNReal.ofReal L0)⁻¹ * discreteNeumannKernel (wienerStarKernel C L0 t) ν with hK
  have hmassK' : discreteMass K
      = (ENNReal.ofReal L0 - (ENNReal.ofReal C + discreteMass fun ν => ‖t ν‖ₑ))⁻¹ := by
    rw [discreteMass_wienerInverseKernel C L0 t,
      wienerInverseMass_eq hth ENNReal.ofReal_ne_top]
  have hne : discreteMass K ≠ ⊤ := by
    rw [hmassK']
    exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hth).ne'
  have hmassm : discreteMass (fun ν => K (ν - ρm)) ≠ ⊤ := by
    rw [discreteMass_comp_sub]
    exact hne
  have hmassp : discreteMass (fun ν => K (ν - ρp)) ≠ ⊤ := by
    rw [discreteMass_comp_sub]
    exact hne
  have h := tsum_eLpNorm_le_twoKernel (Km := fun ν => K (ν - ρm))
    (Kp := fun ν => K (ν - ρp)) hBm hBp hmassm hmassp hdom
  calc (∑' ν : G, eLpNorm (chat ν) 2 μ)
      ≤ discreteMass (fun ν => K (ν - ρm)) * eLpNorm Bm 2 μ
          + discreteMass (fun ν => K (ν - ρp)) * eLpNorm Bp 2 μ := h
    _ = (ENNReal.ofReal L0 - (ENNReal.ofReal C + discreteMass fun ν => ‖t ν‖ₑ))⁻¹
          * (eLpNorm Bm 2 μ + eLpNorm Bp 2 μ) := by
        rw [discreteMass_comp_sub, discreteMass_comp_sub, hmassK', mul_add]

/-! ## The unitarily weighted boundary-log chart -/

/-- The chart `L ↦ e^{-L}` carries the whole line onto the positive axis. -/
theorem image_logChart_univ : logChart '' univ = Ioi (0 : ℝ) := by
  ext r
  constructor
  · rintro ⟨L, _, rfl⟩
    exact Real.exp_pos _
  · intro hr
    exact ⟨-Real.log r, trivial, by
      rw [logChart, neg_neg, Real.exp_log hr]⟩

theorem injOn_logChart_univ : InjOn logChart (univ : Set ℝ) := by
  intro a _ b _ hab
  have := Real.exp_injective hab
  linarith

/-- **The half weight makes the whole-ray chart an `L²` isometry** — the card's `(14)`:
`‖e^{-L/2} g(e^{-L})‖_{L²(dL)} = ‖g‖_{L²((0,∞))}`. -/
theorem integral_sq_fullLogChart (g : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), g r ^ 2)
      = ∫ L : ℝ, (Real.exp (-L / 2) * g (Real.exp (-L))) ^ 2 := by
  have hderiv : ∀ L ∈ (univ : Set ℝ),
      HasDerivWithinAt logChart (-Real.exp (-L)) univ L :=
    fun L _ => (hasDerivAt_logChart L).hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv
    injOn_logChart_univ (fun r => g r ^ 2)
  rw [image_logChart_univ] at h
  rw [h, Measure.restrict_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
  show |(-Real.exp (-L))| • g (logChart L) ^ 2
      = (Real.exp (-L / 2) * g (Real.exp (-L))) ^ 2
  rw [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul, logChart, mul_pow]
  have hsq : (Real.exp (-L / 2)) ^ 2 = Real.exp (-L) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hsq]

/-! ## No free-standing high-tail `dr/r` upgrade -/

/-- The unit frequency band at height `Ξ`. -/
def highBandProfile (Ξ : ℝ) : ℝ → ℂ := indicator (Icc Ξ (Ξ + 1)) fun _ => 1

/-- Its inverse Fourier transform — the position-space band profile. -/
def highBandPosition (Ξ : ℝ) : ℝ → ℂ := 𝓕⁻ (highBandProfile Ξ)

theorem integrable_highBandProfile (Ξ : ℝ) : Integrable (highBandProfile Ξ) volume := by
  rw [highBandProfile, integrable_indicator_iff measurableSet_Icc]
  exact continuousOn_const.integrableOn_compact isCompact_Icc

/-- The band profile evaluates to one at the origin: no oscillation, mass one. -/
theorem highBandPosition_zero (Ξ : ℝ) : highBandPosition Ξ 0 = 1 := by
  rw [highBandPosition, Real.fourierInv_eq]
  have h1 : ∀ v : ℝ, 𝐞 ⟪v, (0 : ℝ)⟫ • highBandProfile Ξ v = highBandProfile Ξ v := by
    intro v
    rw [inner_zero_right, AddChar.map_zero_eq_one, one_smul]
  rw [integral_congr_ae (Filter.Eventually.of_forall h1), highBandProfile,
    integral_indicator_const _ measurableSet_Icc]
  simp

/-- The band profile is continuous in position. -/
theorem continuous_highBandPosition (Ξ : ℝ) : Continuous (highBandPosition Ξ) := by
  have h1 : Continuous fun x : ℝ => 𝓕 (highBandProfile Ξ) x :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) (integrable_highBandProfile Ξ)
  have heq : highBandPosition Ξ = fun w => 𝓕 (highBandProfile Ξ) (-w) := by
    funext w
    rw [highBandPosition, Real.fourierInv_eq_fourier_neg]
  rw [heq]
  exact h1.comp continuous_neg

/-- **The sharp obstruction** — the card's `(17b)`: the band profile has divergent `dr/r`
energy at the origin, however far out the band sits.  The physical log measure cannot be
supplied by any high-frequency estimate alone. -/
theorem lintegral_div_highBandPosition_eq_top (Ξ : ℝ) :
    ∃ ε > (0 : ℝ), (∫⁻ r in Ioo (0 : ℝ) ε,
      ‖highBandPosition Ξ r‖ₑ ^ 2 * (ENNReal.ofReal r)⁻¹) = ⊤ := by
  have hcont := (continuous_highBandPosition Ξ).continuousAt (x := 0)
  have h1 : ∀ᶠ r in nhds (0 : ℝ), ‖highBandPosition Ξ r - 1‖ < 1 / 2 := by
    have h2 := Metric.tendsto_nhds.mp hcont.tendsto (1 / 2) (by norm_num)
    filter_upwards [h2] with r hr
    rw [highBandPosition_zero] at hr
    simpa [dist_eq_norm] using hr
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h1
  refine ⟨ε, hε, ?_⟩
  have hlow : ∀ r ∈ Ioo (0 : ℝ) ε, ENNReal.ofReal (1 / 4) * (ENNReal.ofReal r)⁻¹
      ≤ ‖highBandPosition Ξ r‖ₑ ^ 2 * (ENNReal.ofReal r)⁻¹ := by
    intro r hr
    refine mul_le_mul' ?_ le_rfl
    have hmem : r ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr.1]
      exact hr.2
    have h3 := hball r hmem
    have h4 : (1 : ℝ) / 2 ≤ ‖highBandPosition Ξ r‖ := by
      have h5 := norm_sub_norm_le (1 : ℂ) (1 - highBandPosition Ξ r)
      have h6 : (1 : ℂ) - (1 - highBandPosition Ξ r) = highBandPosition Ξ r := by ring
      rw [h6, norm_one] at h5
      have h7 : ‖(1 : ℂ) - highBandPosition Ξ r‖ < 1 / 2 := by
        rw [← norm_neg]
        simpa [neg_sub] using h3
      linarith
    calc ENNReal.ofReal (1 / 4) = ENNReal.ofReal ((1 / 2) ^ 2) := by norm_num
      _ ≤ ENNReal.ofReal (‖highBandPosition Ξ r‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (highBandPosition Ξ r)])
      _ = ‖highBandPosition Ξ r‖ₑ ^ 2 := by
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hinner : (∫⁻ r in Ioo (0 : ℝ) ε, (ENNReal.ofReal r)⁻¹) = ⊤ := by
    by_contra hfin
    have hfin' : (∫⁻ r in Ioo (0 : ℝ) ε, (ENNReal.ofReal r)⁻¹) < ⊤ :=
      lt_top_iff_ne_top.mpr hfin
    have hni : ¬ IntegrableOn (fun r : ℝ => r ^ (-1 : ℝ)) (Ioo (0 : ℝ) ε) := by
      rw [intervalIntegral.integrableOn_Ioo_rpow_iff hε]
      norm_num
    refine hni ⟨(Measurable.aestronglyMeasurable (by fun_prop)).restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (le_of_eq ?_) hfin'
    refine lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall fun r hr => ?_))
    show ‖r ^ (-1 : ℝ)‖ₑ = (ENNReal.ofReal r)⁻¹
    have hrpos : (0 : ℝ) < r := hr.1
    rw [Real.rpow_neg_one, Real.enorm_eq_ofReal (by positivity),
      ENNReal.ofReal_inv_of_pos hrpos]
  have hdiv : (∫⁻ r in Ioo (0 : ℝ) ε, ENNReal.ofReal (1 / 4) * (ENNReal.ofReal r)⁻¹) = ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hinner,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by norm_num : (0:ℝ) < 1/4)).ne']
  refine eq_top_iff.mpr (le_trans (le_of_eq hdiv.symm) ?_)
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
    (Filter.Eventually.of_forall fun r hr => hlow r hr))

end GaloisForLFunctions.RHTower
