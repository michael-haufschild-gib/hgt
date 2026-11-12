import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRenormalizedThetaSquareIsBounded
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheConstantTermContinuesAcrossFourThirds

/-!
# The renormalized theta square unfolds

For `4 < Re s < 13/3` the renormalized square `G = θ_s² − H` pairs with the cubic Eisenstein series
as (`integral_renormalized_mul_eisenstein`)

`∫_{D_Γ} G · E(s) = |P| M(s) D(s) + |P| c² 2^{s−2/3}/(s − 2/3) − c² Φ(s) 2^{4/3−s}/(s − 4/3)`,

with `D(s) = Σ_{h≠0} T_s(h)² (4π|ξ_h|)^{−s}`, `M(s) = ∫ t^{s−1} K_{1/3}(t)² dt` and `Φ` the scattering
coefficient of the rational cusp subtraction. The three pieces of the constant term
`a₀(G) = |P| R + |P| c² v^{4/3} 1_{v<2} − (a₀(H) − |P| c² f)` are Mellin-transformed separately:
the first by the Mellin link, the second explicitly, the third by `integral_scatterPart`.

* `renormalized_strip_lintegral_lt_top`: `∫_{strip} |G| v^σ < ∞` for `2 < σ < 13/3` (`G` bounded,
  `O(v^{−7/3})` high in the cusp); hence `G` pairs with every incomplete Eisenstein series of a profile
  bounded by `v^σ` (`renormalized_integrableOn_mul_incomplete`).
* `sub_mul_scatterTotal`: `(s − 4/3) Φ(s) = Φ₀(s)`,
  `Φ₀(s) = (π/(s−1)) |P| (s − 4/3)φ(s) (3·3^{3s−3} − 1)/2` (`clearedScatterTotal`), holomorphic on
  `Re s > 1` with `Φ₀(4/3) = 12π |P| r` (`clearedScatterTotal_four_thirds`): the opposite cusps carry
  `U(s) = (3^{3s−3} − 1)|P| φ(s)/2`, and at `4/3` the four rational cusps contribute `1 + 3 = 4`.
-/

noncomputable section

open MeasureTheory Filter Function
open scoped BigOperators Classical MatrixGroups ComplexConjugate ENNReal Topology

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-! ### The strip bound -/

/-- `∫_{strip} |G| v^σ dμ < ∞` for `2 < σ < 13/3`. -/
theorem renormalized_strip_lintegral_lt_top {σ : ℝ} (hσ2 : 2 < σ) (hσ : σ < 13 / 3) :
    ∫⁻ w in cuspStripSet, ‖renormalizedThetaSq w‖ₑ * ENNReal.ofReal (hyperbolicHeight w ^ σ)
      ∂hyperbolicVolume < ⊤ := by
  obtain ⟨B, hB⟩ := renormalizedThetaSq_bounded
  obtain ⟨C, hC, hhigh⟩ := norm_renormalizedThetaSq_high
  set B' := max B 0
  have hB' : ∀ w, ‖renormalizedThetaSq w‖ ≤ B' := fun w => (hB w).trans (le_max_left _ _)
  have hm : Measurable (fun w => ‖renormalizedThetaSq w‖ₑ * ENNReal.ofReal (hyperbolicHeight w ^ σ)) :=
    renormalizedThetaSq_measurable.enorm.mul
      (ENNReal.measurable_ofReal.comp (hyperbolicHeight_continuous.measurable.pow_const σ))
  rw [cuspStrip_lintegral _ hm]
  set g : ℝ → ℝ := fun v => (Set.Ioc 0 2).indicator (fun v => B' * periodAreaReal * v ^ (σ - 3)) v +
    (Set.Ioi 2).indicator (fun v => C * periodAreaReal * v ^ (σ - 3 - 7 / 3)) v with hgdef
  have hg1 : IntegrableOn (fun v : ℝ => B' * periodAreaReal * v ^ (σ - 3)) (Set.Ioc 0 2) := by
    have := intervalIntegral.intervalIntegrable_rpow' (r := σ - 3) (by linarith) (a := 0) (b := 2)
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp this).const_mul _
  have hg2 : IntegrableOn (fun v : ℝ => C * periodAreaReal * v ^ (σ - 3 - 7 / 3)) (Set.Ioi 2) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul _
  have hg : IntegrableOn g (Set.Ioi 0) :=
    (((integrable_indicator_iff measurableSet_Ioc).mpr hg1).add
      ((integrable_indicator_iff measurableSet_Ioi).mpr hg2)).integrableOn
  have hg0 : ∀ v, 0 ≤ g v := by
    intro v
    simp only [hgdef]
    refine add_nonneg (Set.indicator_nonneg (fun v hv => ?_) _) (Set.indicator_nonneg (fun v hv => ?_) _)
    · have : (0 : ℝ) < v := hv.1
      positivity
    · have : (0 : ℝ) < v := lt_trans (by norm_num) hv
      positivity
  have hP : volume periodDomain = ENNReal.ofReal periodAreaReal := periodDomain_volume
  calc ∫⁻ v in Set.Ioi (0 : ℝ), ∫⁻ z in periodDomain,
        ‖renormalizedThetaSq (cuspCoordinateLift (v, z))‖ₑ *
          ENNReal.ofReal (hyperbolicHeight (cuspCoordinateLift (v, z)) ^ σ) * ENNReal.ofReal ((v ^ 3)⁻¹)
      ≤ ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (g v) := by
        refine setLIntegral_mono' measurableSet_Ioi fun v (hv : 0 < v) => ?_
        have hlift : ∀ z, cuspCoordinateLift (v, z) = upperPoint z v hv := fun z =>
          cuspCoordinateLift_positive v z hv
        simp only [hlift, hyperbolicHeight_upperPoint]
        have hpow : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x * ENNReal.ofReal (v ^ σ) * ENNReal.ofReal ((v ^ 3)⁻¹) =
            ENNReal.ofReal (x * v ^ (σ - 3)) := by
          intro x hx
          rw [← ENNReal.ofReal_mul hx, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [Real.rpow_sub hv, mul_assoc, div_eq_mul_inv]
          norm_cast
        by_cases hv2 : v ≤ 2
        · have hgv : g v = B' * periodAreaReal * v ^ (σ - 3) := by
            simp only [hgdef, Set.indicator_of_mem (show v ∈ Set.Ioc 0 2 from ⟨hv, hv2⟩),
              Set.indicator_of_notMem (show v ∉ Set.Ioi 2 from fun h => absurd hv2 (not_le.mpr h)), add_zero]
          calc ∫⁻ z in periodDomain, ‖renormalizedThetaSq (upperPoint z v hv)‖ₑ * ENNReal.ofReal (v ^ σ) *
                ENNReal.ofReal ((v ^ 3)⁻¹)
              ≤ ∫⁻ _z in periodDomain, ENNReal.ofReal (B' * v ^ (σ - 3)) := by
                refine lintegral_mono fun z => ?_
                rw [← hpow B' (le_max_right _ _)]
                gcongr
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hB' _)
            _ = ENNReal.ofReal (g v) := by
                rw [setLIntegral_const, hP, ← ENNReal.ofReal_mul (by positivity), hgv]
                ring_nf
        · have hv2' : 2 < v := not_le.mp hv2
          have hgv : g v = C * periodAreaReal * v ^ (σ - 3 - 7 / 3) := by
            simp only [hgdef, Set.indicator_of_notMem (show v ∉ Set.Ioc 0 2 from fun h => hv2 h.2),
              Set.indicator_of_mem (show v ∈ Set.Ioi 2 from hv2'), zero_add]
          calc ∫⁻ z in periodDomain, ‖renormalizedThetaSq (upperPoint z v hv)‖ₑ * ENNReal.ofReal (v ^ σ) *
                ENNReal.ofReal ((v ^ 3)⁻¹)
              ≤ ∫⁻ _z in periodDomain, ENNReal.ofReal (C * v ^ (-(7 : ℝ) / 3) * v ^ (σ - 3)) := by
                refine lintegral_mono fun z => ?_
                rw [← hpow (C * v ^ (-(7 : ℝ) / 3)) (by positivity)]
                gcongr
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hhigh z v hv hv2'.le)
            _ = ENNReal.ofReal (g v) := by
                rw [setLIntegral_const, hP, ← ENNReal.ofReal_mul (by positivity), hgv]
                congr 1
                rw [show σ - 3 - 7 / 3 = -(7 : ℝ) / 3 + (σ - 3) by ring, Real.rpow_add hv]
                ring
    _ = ENNReal.ofReal (∫ v in Set.Ioi (0 : ℝ), g v) :=
        (ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hg0)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem renormalized_integrableOn_unfolded (ψ : ℝ → ℂ) (hψm : Measurable ψ) {σ : ℝ} (hσ2 : 2 < σ)
    (hσ : σ < 13 / 3) (hψ : ∀ v : ℝ, 0 < v → ‖ψ v‖ ≤ v ^ σ) :
    IntegrableOn (unfolded renormalizedThetaSq ψ) cuspStripSet hyperbolicVolume := by
  refine ⟨(renormalizedThetaSq_measurable.mul
    (hψm.comp hyperbolicHeight_continuous.measurable)).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_) (renormalized_strip_lintegral_lt_top hσ2 hσ)
  rw [unfolded, enorm_mul]
  gcongr
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hψ _ (hyperbolicHeight_pos w))

theorem incompleteEisenstein_measurable (ψ : ℝ → ℂ) (hψ : Measurable ψ) :
    Measurable (incompleteEisenstein ψ) := by
  unfold incompleteEisenstein
  exact Measurable.tsum fun x => measurable_const.mul (hψ.comp (cosetHeight_continuous x).measurable)

theorem renormalized_integrableOn_mul_incomplete (ψ : ℝ → ℂ) (hψm : Measurable ψ) {σ : ℝ}
    (hσ2 : 2 < σ) (hσ : σ < 13 / 3) (hψ : ∀ v : ℝ, 0 < v → ‖ψ v‖ ≤ v ^ σ) :
    IntegrableOn (fun w => renormalizedThetaSq w * incompleteEisenstein ψ w) levelSet hyperbolicVolume := by
  have hun := renormalized_integrableOn_unfolded ψ hψm hσ2 hσ hψ
  refine ⟨(renormalizedThetaSq_measurable.mul
    (incompleteEisenstein_measurable ψ hψm)).aestronglyMeasurable, ?_⟩
  have heq := lintegral_norm_mul_incompleteEisenstein CuspDomain.strip renormalizedThetaSq
    renormalizedThetaSq_automorphy ψ
    (renormalizedThetaSq_measurable.mul (hψm.comp hyperbolicHeight_continuous.measurable)).enorm.aemeasurable
  change ∫⁻ w in levelSet, ‖renormalizedThetaSq w * incompleteEisenstein ψ w‖ₑ ∂hyperbolicVolume < ⊤
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_) (heq.trans_lt hun.2)
  rw [enorm_mul, ENNReal.tsum_mul_left, incompleteEisenstein]
  gcongr
  refine enorm_tsum_le_tsum_enorm.trans (le_of_eq (tsum_congr fun x => ?_))
  rw [enorm_mul, ← ofReal_norm ((cosetCharacter x)⁻¹), norm_inv, norm_cosetCharacter, inv_one,
    ENNReal.ofReal_one, one_mul]

/-! ### Explicit Mellin integrals -/

theorem cpow_mul_rpow_div (s : ℂ) (a : ℝ) (v : ℝ) (hv : 0 < v) :
    (v : ℂ) ^ s * ((v ^ a : ℝ) : ℂ) / (v : ℂ) ^ 3 = (v : ℂ) ^ (s + a - 3) := by
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [Complex.ofReal_cpow hv.le, Complex.cpow_sub _ _ hv0, Complex.cpow_add _ _ hv0]
  norm_cast

/-- `∫_0^2 v^s v^{4/3} v^{−3} dv = 2^{s−2/3}/(s − 2/3)` for `Re s > 2/3`. -/
theorem integral_low_power (s : ℂ) (hs : 2 / 3 < s.re) :
    ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
      (Set.Iio 2).indicator (fun v => ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ)) v / (v : ℂ) ^ 3 =
        (2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3) := by
  have hr : -1 < (s + ((4 : ℝ) / 3 : ℝ) - 3).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.re_ofNat]
    linarith
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
      (Set.Iio 2).indicator (fun v => ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ)) v / (v : ℂ) ^ 3 =
        (Set.Iio 2).indicator (fun v => (v : ℂ) ^ (s + ((4 : ℝ) / 3 : ℝ) - 3)) v := by
    intro v (hv : 0 < v)
    by_cases h2 : v < 2
    · rw [Set.indicator_of_mem h2, Set.indicator_of_mem h2, cpow_mul_rpow_div s _ v hv]
    · rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem h2, mul_zero, zero_div]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, setIntegral_indicator measurableSet_Iio,
    show Set.Ioi (0 : ℝ) ∩ Set.Iio 2 = Set.Ioo 0 2 from Set.Ioi_inter_Iio, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num), integral_cpow (Or.inl hr)]
  have hne : s + ((4 : ℝ) / 3 : ℝ) - 3 + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofNat, Complex.one_re,
      Complex.zero_re] at this
    linarith
  rw [Complex.ofReal_zero, Complex.zero_cpow hne, sub_zero]
  push_cast
  congr 1 <;> ring_nf

theorem integrableOn_low_power (s : ℂ) (hs : 2 / 3 < s.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ s *
      (Set.Iio 2).indicator (fun v => ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ)) v / (v : ℂ) ^ 3) (Set.Ioi 0) := by
  have hr : -1 < (s + ((4 : ℝ) / 3 : ℝ) - 3).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.re_ofNat]
    linarith
  have hI : IntegrableOn (fun v : ℝ => (v : ℂ) ^ (s + ((4 : ℝ) / 3 : ℝ) - 3)) (Set.Ioc 0 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (intervalIntegral.intervalIntegrable_cpow' hr)
  refine (hI.of_forall_sdiff_eq_zero measurableSet_Ioi fun v hv => ?_).congr_fun (fun v hv => ?_)
    measurableSet_Ioi
  · sorry
  · sorry

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
