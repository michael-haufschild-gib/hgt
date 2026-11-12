import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheThetaSquareHasARationalCuspSubtraction

/-!
# The rational cusp subtraction scatters through the Gauss series

Let `H = H_{[2,∞)}` be the rational cusp subtraction with profile `f = 1_{[2,∞)} v^{4/3}` and
`a₀(H)(v) = ∫_P H(z + jv) dz` its constant term. Above height `1/2` it is `|P| c² f(v)`; below, it is
the scattering of the four rational cusps into `∞`. Its Mellin transform is
(`integral_cuspConstant_cuspSubtraction`, `Re s > 10/3`)

`∫_0^∞ v^s (a₀(H)(v) − |P| c² f(v)) v^{−3} dv = c² Φ(s) ∫_0^∞ f(v) v^{2−s} v^{−3} dv`,

`Φ(s) = |P| (π/(s−1)) φ(s) + 3 (π/(s−1)) U(s)` (`scatterTotal`), with `φ` the scattering coefficient of
the cubic Eisenstein series at `∞` and `U` the unramified Gauss series of the opposite cusp.

* For the truncated profile `1_{[2,T]} v^{4/3}` both sides of `∫_{D_Γ} H_T E(s)` unfold: through `E(s)`
  to the constant term of `H_T`, and through each rational translate `r_q` (moved onto `E(s)` by
  `setIntegral_levelSet_translate`, `E(s)(r_q⁻¹ w) = E(s)(S w)` for `q ≠ 1`) to the constant terms of
  `E(s)` and `E(s) ∘ S` (`cuspConstant_eisenstein`, `cuspConstant_eisensteinS`).
* `T → ∞`: at height `v ∈ [1/T, 1/2]` the truncation is invisible (`cuspSubtraction_truncate`), and
  below `1/2` both are `O(v^{−4/3})` (`norm_cuspSubtraction_small`), so the error is
  `O(T^{10/3 − Re s}) + O(T^{4/3 − Re s})`.
* `integrableOn_mul_eisenstein_of_strip`: a function of multiplier `κ⁻¹` that is bounded on the
  standard strip and vanishes there above a fixed height is integrable against `E(s)` on `D_Γ`
  (absolute unfolding).
-/

noncomputable section

open MeasureTheory Filter Function
open scoped BigOperators Classical MatrixGroups ComplexConjugate ENNReal Topology

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-! ### The cutoff series -/

theorem cuspCutoffCorrection_norm_le_of (F : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (w : HyperbolicSpace)
    (hF : ∀ r : CuspCosets, 1 < cosetHeight r w → ‖F (cosetHeight r w)‖ ≤ C) :
    ‖cuspCutoffCorrection 1 F w‖ ≤ C := by
  by_cases hh : ∃ r : CuspCosets, 1 < cosetHeight r w
  · obtain ⟨r, hr⟩ := hh
    rw [cuspCutoffCorrection_eq 1 le_rfl F w r hr, norm_mul, norm_inv, norm_cosetCharacter, inv_one,
      one_mul]
    exact hF r hr
  · have hz : cuspCutoffCorrection 1 F w = 0 := by
      unfold cuspCutoffCorrection
      refine (tsum_congr fun r => ?_).trans tsum_zero
      simp [cuspCutoffTerm, show ¬1 < cosetHeight r w from fun h => hh ⟨r, h⟩]
    rw [hz, norm_zero]
    exact hC

theorem cuspCutoffCorrection_congr (F G : ℝ → ℂ) (w : HyperbolicSpace)
    (h : ∀ r : CuspCosets, 1 < cosetHeight r w → F (cosetHeight r w) = G (cosetHeight r w)) :
    cuspCutoffCorrection 1 F w = cuspCutoffCorrection 1 G w := by
  unfold cuspCutoffCorrection
  refine tsum_congr fun r => ?_
  rw [cuspCutoffTerm, cuspCutoffTerm]
  split_ifs with hr
  · rw [h r hr]
  · rfl

theorem growthProfile_measurable (S : Set ℝ) (hS : MeasurableSet S) : Measurable (growthProfile S) :=
  (Complex.measurable_ofReal.comp (measurable_id.pow_const _)).indicator hS

theorem norm_growthProfile_le (S : Set ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖growthProfile S t‖ ≤ t ^ ((4 : ℝ) / 3) := by
  rw [growthProfile]
  by_cases h : t ∈ S
  · rw [Set.indicator_of_mem h, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht _)]
  · rw [Set.indicator_of_notMem h, norm_zero]
    exact Real.rpow_nonneg ht _

theorem cuspSubtraction_measurable (c : ℂ) (S : Set ℝ) (hS : MeasurableSet S) :
    Measurable (cuspSubtraction c S) := by
  unfold cuspSubtraction
  refine measurable_const.mul (Finset.measurable_sum _ fun q _ => ?_)
  exact Complex.continuous_conj.measurable.comp
    ((cuspCutoffCorrection_measurable 1 _ (growthProfile_measurable S hS)).comp
      (continuous_hyperbolic_action _).measurable)

theorem card_rationalFourCusp : Fintype.card RationalFourCusp = 4 := rfl

/-- `|Σ_q a_q| ≤ 4 B` when every `|a_q| ≤ B`. -/
theorem norm_cuspSubtraction_le_of (c : ℂ) (S : Set ℝ) (w : HyperbolicSpace) (B : ℝ)
    (hB : ∀ q : RationalFourCusp,
      ‖cuspCutoffCorrection 1 (growthProfile S) (rationalComplex (rationalRep q) • w)‖ ≤ B) :
    ‖cuspSubtraction c S w‖ ≤ ‖c‖ ^ 2 * (4 * B) := by
  rw [cuspSubtraction, norm_mul, norm_pow]
  gcongr
  calc ‖∑ q : RationalFourCusp, conj (cuspCutoffCorrection 1 (growthProfile S)
        (rationalComplex (rationalRep q) • w))‖
      ≤ ∑ q : RationalFourCusp, ‖conj (cuspCutoffCorrection 1 (growthProfile S)
        (rationalComplex (rationalRep q) • w))‖ := norm_sum_le _ _
    _ ≤ ∑ _q : RationalFourCusp, B := Finset.sum_le_sum fun q _ => by rw [RCLike.norm_conj]; exact hB q
    _ = 4 * B := by rw [Finset.sum_const, Finset.card_univ, card_rationalFourCusp, nsmul_eq_mul]; norm_num

/-- For `S ⊆ [2, T]`: `|H_S| ≤ 4|c|² T^{4/3}` everywhere. -/
theorem norm_cuspSubtraction_le (c : ℂ) {T : ℝ} (hT : 2 ≤ T) (S : Set ℝ) (hS : S ⊆ Set.Icc 2 T)
    (w : HyperbolicSpace) : ‖cuspSubtraction c S w‖ ≤ ‖c‖ ^ 2 * (4 * T ^ ((4 : ℝ) / 3)) := by
  refine norm_cuspSubtraction_le_of c S w _ fun q => cuspCutoffCorrection_norm_le _ _ (by positivity)
    (fun t => ?_) _
  rw [growthProfile]
  by_cases h : t ∈ S
  · rw [Set.indicator_of_mem h, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (by
      linarith [(hS h).1]) _)]
    exact Real.rpow_le_rpow (by linarith [(hS h).1]) (hS h).2 (by norm_num)
  · rw [Set.indicator_of_notMem h, norm_zero]
    positivity

/-- At height `v ≤ 1/2`, every coset that lifts a rational translate of `z + jv` above `1` lifts it
to height `≤ 1/v`. -/
theorem cosetHeight_rationalRep_le (q : RationalFourCusp) (r : CuspCosets) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (hv2 : v ≤ 1 / 2) (h1 : 1 < cosetHeight r (rationalComplex (rationalRep q) • upperPoint z v hv)) :
    cosetHeight r (rationalComplex (rationalRep q) • upperPoint z v hv) ≤ 1 / v := by
  by_cases hq : q = .inl ()
  · subst hq
    have hp : rationalComplex (rationalRep (.inl ())) • upperPoint z v hv = upperPoint z v hv := by
      simp [rationalRep, rationalFourCuspRep]
    rw [hp] at h1 ⊢
    by_cases hr : r = cosetOf 1
    · subst hr
      rw [cosetHeight_cosetOf, map_one, one_smul, hyperbolicHeight_upperPoint] at h1
      linarith
    · refine (cosetHeight_upper_le r hr z v hv).trans ?_
      apply div_le_div_of_nonneg_left zero_le_one hv
      linarith
  · obtain ⟨h0, h1'⟩ := rationalRep_column q hq
    exact cosetHeight_rational_le _ h0 h1' r z v hv

/-- Below height `1/2`: `|H_S(z + jv)| ≤ 4|c|² v^{−4/3}`. -/
theorem norm_cuspSubtraction_small (c : ℂ) (S : Set ℝ) (z : ℂ) (v : ℝ) (hv : 0 < v) (hv2 : v ≤ 1 / 2) :
    ‖cuspSubtraction c S (upperPoint z v hv)‖ ≤ ‖c‖ ^ 2 * (4 * (1 / v) ^ ((4 : ℝ) / 3)) := by
  refine norm_cuspSubtraction_le_of c S _ _ fun q =>
    cuspCutoffCorrection_norm_le_of _ _ (by positivity) _ fun r hr => ?_
  have hh := cosetHeight_rationalRep_le q r z v hv hv2 hr
  refine (norm_growthProfile_le S (by linarith)).trans ?_
  exact Real.rpow_le_rpow (by linarith) hh (by norm_num)

/-- Between heights `1/T` and `1/2` the truncation at `T` is invisible. -/
theorem cuspSubtraction_truncate (c : ℂ) {T : ℝ} (hT : 2 ≤ T) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (hv2 : v ≤ 1 / 2) (hvT : 1 / T ≤ v) :
    cuspSubtraction c (Set.Icc 2 T) (upperPoint z v hv) =
      cuspSubtraction c (Set.Ici 2) (upperPoint z v hv) := by
  unfold cuspSubtraction
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  refine cuspCutoffCorrection_congr _ _ _ fun r hr => ?_
  have hh := cosetHeight_rationalRep_le q r z v hv hv2 hr
  have hT' : cosetHeight r (rationalComplex (rationalRep q) • upperPoint z v hv) ≤ T := by
    refine hh.trans ?_
    rw [div_le_iff₀ hv]
    rw [div_le_iff₀ (by linarith)] at hvT
    linarith
  simp only [growthProfile, Set.indicator, Set.mem_Icc, Set.mem_Ici, hT', and_true]

/-! ### Integrability against the Eisenstein series -/

theorem strip_lintegral_lt_top (G : HyperbolicSpace → ℂ) (hGm : Measurable G) (B V : ℝ)
    (hV : 0 < V) (hB : ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), ‖G (upperPoint z v hv)‖ ≤ B)
    (hV' : ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), V < v → G (upperPoint z v hv) = 0) (σ : ℝ) (hσ : 2 < σ) :
    ∫⁻ w in cuspStripSet, ‖G w‖ₑ * ENNReal.ofReal (hyperbolicHeight w ^ σ) ∂hyperbolicVolume < ⊤ := by
  have hm : Measurable (fun w => ‖G w‖ₑ * ENNReal.ofReal (hyperbolicHeight w ^ σ)) :=
    hGm.enorm.mul (ENNReal.measurable_ofReal.comp (hyperbolicHeight_continuous.measurable.pow_const σ))
  rw [cuspStrip_lintegral _ hm]
  have hP : volume periodDomain = ENNReal.ofReal periodAreaReal := periodDomain_volume
  have hI : IntegrableOn (fun v : ℝ => v ^ (σ - 3)) (Set.Ioc 0 V) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (r := σ - 3) (by linarith) (a := 0) (b := V))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hV.le).mp this
  calc ∫⁻ v in Set.Ioi (0 : ℝ), ∫⁻ z in periodDomain,
        ‖G (cuspCoordinateLift (v, z))‖ₑ * ENNReal.ofReal (hyperbolicHeight (cuspCoordinateLift (v, z)) ^ σ) *
          ENNReal.ofReal ((v ^ 3)⁻¹)
      ≤ ∫⁻ v in Set.Ioi (0 : ℝ), (Set.Ioc 0 V).indicator
          (fun v => ENNReal.ofReal B * ENNReal.ofReal periodAreaReal * ENNReal.ofReal (v ^ (σ - 3))) v := by
        refine setLIntegral_mono' measurableSet_Ioi fun v (hv : 0 < v) => ?_
        have hlift : ∀ z, cuspCoordinateLift (v, z) = upperPoint z v hv := fun z =>
          cuspCoordinateLift_positive v z hv
        simp only [hlift, hyperbolicHeight_upperPoint]
        by_cases hvV : v ≤ V
        · rw [Set.indicator_of_mem (show v ∈ Set.Ioc 0 V from ⟨hv, hvV⟩)]
          have hpow : ENNReal.ofReal (v ^ σ) * ENNReal.ofReal ((v ^ 3)⁻¹) = ENNReal.ofReal (v ^ (σ - 3)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [Real.rpow_sub hv, div_eq_mul_inv]
            norm_cast
          calc ∫⁻ z in periodDomain, ‖G (upperPoint z v hv)‖ₑ * ENNReal.ofReal (v ^ σ) * ENNReal.ofReal ((v ^ 3)⁻¹)
              ≤ ∫⁻ _z in periodDomain, ENNReal.ofReal B * ENNReal.ofReal (v ^ (σ - 3)) := by
                refine lintegral_mono fun z => ?_
                rw [mul_assoc, hpow]
                gcongr
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hB z v hv)
            _ = _ := by
                rw [setLIntegral_const, hP]
                ring
        · rw [Set.indicator_of_notMem fun h => hvV h.2]
          have : ∀ z, G (upperPoint z v hv) = 0 := fun z => hV' z v hv (not_le.mp hvV)
          simp [this]
    _ = ∫⁻ v in Set.Ioc 0 V, ENNReal.ofReal B * ENNReal.ofReal periodAreaReal *
          ENNReal.ofReal (v ^ (σ - 3)) := by
        rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
          Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self]
    _ = ENNReal.ofReal B * ENNReal.ofReal periodAreaReal *
          ∫⁻ v in Set.Ioc 0 V, ENNReal.ofReal (v ^ (σ - 3)) := lintegral_const_mul' _ _ (by finiteness)
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (by finiteness) ?_
        rw [← ofReal_integral_eq_lintegral_ofReal hI
          (ae_restrict_of_forall_mem measurableSet_Ioc fun v hv => Real.rpow_nonneg hv.1.le _)]
        exact ENNReal.ofReal_lt_top

theorem integrableOn_unfolded_of_strip (G : HyperbolicSpace → ℂ) (hGm : Measurable G) (B V : ℝ)
    (hV : 0 < V) (hB : ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), ‖G (upperPoint z v hv)‖ ≤ B)
    (hV' : ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), V < v → G (upperPoint z v hv) = 0) (s : ℂ) (hs : 2 < s.re) :
    IntegrableOn (unfolded G fun t => (t : ℂ) ^ s) cuspStripSet hyperbolicVolume := by
  have hcm : Measurable (fun w => (hyperbolicHeight w : ℂ) ^ s) :=
    (Complex.measurable_ofReal.comp hyperbolicHeight_continuous.measurable).pow_const s
  refine ⟨(hGm.mul hcm).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_) (strip_lintegral_lt_top G hGm B V hV hB hV' s.re hs)
  rw [unfolded, enorm_mul, ← ofReal_norm (_ ^ s),
    Complex.norm_cpow_eq_rpow_re_of_pos (hyperbolicHeight_pos w)]

/-- **Strip-bounded functions pair with `E(s)`.** -/
theorem integrableOn_mul_eisenstein_of_strip (G : HyperbolicSpace → ℂ)
    (hG : ∀ (M : levelThree) (w : HyperbolicSpace), G (complexMatrix M • w) = (complexCharacter M)⁻¹ * G w)
    (hGm : Measurable G) (B V : ℝ) (hV : 0 < V)
    (hB : ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), ‖G (upperPoint z v hv)‖ ≤ B)
    (hV' : ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), V < v → G (upperPoint z v hv) = 0) (s : ℂ) (hs : 2 < s.re) :
    IntegrableOn (fun w => G w * hyperbolicEisenstein s w) levelSet hyperbolicVolume := by
  have hun := integrableOn_unfolded_of_strip G hGm B V hV hB hV' s hs
  refine ⟨(hGm.mul (hyperbolicEisenstein_continuous s hs).measurable).aestronglyMeasurable, ?_⟩
  have hcm : Measurable (fun t : ℝ => (t : ℂ) ^ s) := Complex.measurable_ofReal.pow_const s
  have heq := lintegral_norm_mul_incompleteEisenstein CuspDomain.strip G hG (fun t => (t : ℂ) ^ s)
    (hGm.mul (hcm.comp hyperbolicHeight_continuous.measurable)).enorm.aemeasurable
  change ∫⁻ w in levelSet, ‖G w * hyperbolicEisenstein s w‖ₑ ∂hyperbolicVolume < ⊤
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_) (heq.trans_lt hun.2)
  rw [enorm_mul, ENNReal.tsum_mul_left, hyperbolicEisenstein_eq_height_series]
  gcongr
  refine enorm_tsum_le_tsum_enorm.trans (le_of_eq (tsum_congr fun x => ?_))
  rw [enorm_mul, ← ofReal_norm ((cosetCharacter x)⁻¹), norm_inv, norm_cosetCharacter, inv_one,
    ENNReal.ofReal_one, one_mul]

/-! ### Unfolding the conjugate cutoff series -/

/-- A real profile vanishing below `2` gives the incomplete series. -/
theorem cuspCutoffCorrection_eq_incomplete (F : ℝ → ℂ) (hF : ∀ t, t < 2 → F t = 0) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 F w = incompleteEisenstein F w := by
  rw [cuspCutoffCorrection, incompleteEisenstein]
  refine tsum_congr fun x => ?_
  rw [cuspCutoffTerm]
  split_ifs with h
  · rfl
  · rw [hF _ (by linarith [not_lt.mp h]), mul_zero]

/-- **Unfolding `conj E(· ∣ f)`.** For `B` of multiplier `κ`, continuous, and `f = f_{[2,T]}`:
`∫_{D_Γ} conj(E_1(w ∣ f)) B(w) dμ = ∫_0^∞ f(v) (∫_P B(z + jv) dz) v^{−3} dv`. -/
theorem integral_conj_cutoff_mul (T : ℝ) (B : HyperbolicSpace → ℂ) (hBc : Continuous B)
    (hB : ∀ (M : levelThree) (w : HyperbolicSpace), B (complexMatrix M • w) = complexCharacter M * B w) :
    ∫ w in levelSet, conj (cuspCutoffCorrection 1 (growthProfile (Set.Icc 2 T)) w) * B w
        ∂hyperbolicVolume =
      ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v *
        (∫ z in periodDomain, B (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 := by
  have hzero : ∀ t, t < 2 → growthProfile (Set.Icc 2 T) t = 0 := fun t ht =>
    Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr ht)) _
  have hBc' : ∀ (M : levelThree) (w : HyperbolicSpace),
      conj (B (complexMatrix M • w)) = (complexCharacter M)⁻¹ * conj (B w) := by
    intro M w
    rw [hB, map_mul, conj_complexCharacter]
  have hint : IntegrableOn (unfolded (fun w => conj (B w)) (growthProfile (Set.Icc 2 T))) cuspStripSet
      hyperbolicVolume := by
    have hc : Continuous (fun w => conj (B w) *
        ((hyperbolicHeight w ^ ((4 : ℝ) / 3) : ℝ) : ℂ)) :=
      (Complex.continuous_conj.comp hBc).mul (Complex.continuous_ofReal.comp
        (hyperbolicHeight_continuous.rpow_const fun _ => Or.inr (by norm_num)))
    have h1 : IntegrableOn (unfolded (fun w => conj (B w)) (growthProfile (Set.Icc 2 T)))
        (cuspPeriodStrip 2 T) hyperbolicVolume := by
      refine (cuspStrip_integrable_continuous 2 T (by norm_num) _ hc).congr_fun (fun w hw => ?_)
        (cuspPeriodStrip_measurable 2 T)
      rw [unfolded, growthProfile, Set.indicator_of_mem hw.2]
    refine h1.of_forall_sdiff_eq_zero cuspStripSet_measurable fun w hw => ?_
    have hv : hyperbolicHeight w ∉ Set.Icc 2 T := fun h => hw.2 ⟨hw.1, h⟩
    rw [unfolded, growthProfile, Set.indicator_of_notMem hv, mul_zero]
  have hcut : ∀ w, cuspCutoffCorrection 1 (growthProfile (Set.Icc 2 T)) w =
      incompleteEisenstein (growthProfile (Set.Icc 2 T)) w :=
    cuspCutoffCorrection_eq_incomplete _ hzero
  have hunf := integral_mul_incompleteEisenstein_eq_constantTerm (fun w => conj (B w)) hBc'
    (growthProfile (Set.Icc 2 T)) hint
  calc ∫ w in levelSet, conj (cuspCutoffCorrection 1 (growthProfile (Set.Icc 2 T)) w) * B w
        ∂hyperbolicVolume
      = conj (∫ w in levelSet, conj (B w) * incompleteEisenstein (growthProfile (Set.Icc 2 T)) w
          ∂hyperbolicVolume) := by
        rw [← integral_conj]
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp only [hcut, map_mul, Complex.conj_conj]
        ring
    _ = conj (∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v *
          (∫ z in periodDomain, conj (B (cuspCoordinateLift (v, z)))) / (v : ℂ) ^ 3) := by rw [hunf]
    _ = _ := by
        rw [← integral_conj]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        simp only [map_div₀, map_mul, map_pow, Complex.conj_ofReal, conj_growthProfile]
        rw [← integral_conj]
        simp only [Complex.conj_conj]

/-! ### The constant terms of `E(s)` and `E(s) ∘ S` -/

theorem tracePhase_zero_freq (z : ℂ) : tracePhase (-cuspFrequency 0 * z) = 1 := by
  simp [cuspFrequency]

/-- `∫_P E(s)(z + jv) dz = |P| (v^s + v^{2−s} (π/(s−1)) φ(s))`. -/
theorem cuspConstant_eisenstein (s : ℂ) (hs : 2 < s.re) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, hyperbolicEisenstein s (cuspCoordinateLift (v, z)) =
      periodArea * ((v : ℂ) ^ s + (v : ℂ) ^ (2 - s) * ((Real.pi : ℂ) / (s - 1) * scatteringCoefficient s 0)) := by
  have h := eisensteinFourierCoefficient_formula v hv s hs 0
  rw [eisensteinFourierCoefficient, if_pos rfl] at h
  simp only [tracePhase_zero_freq, mul_one] at h
  have hK : sourceFourierKernel s (cuspFrequency 0 * v) = (Real.pi : ℂ) / (s - 1) := by
    rw [show cuspFrequency 0 = 0 by simp [cuspFrequency], zero_mul]
    exact sourceFourierKernel_zero s (by linarith)
  rw [hK] at h
  have hP : periodArea ≠ 0 := Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne'
  have hlift : ∀ z, hyperbolicEisenstein s (cuspCoordinateLift (v, z)) = upperEisenstein z v hv s := by
    intro z
    rw [cuspCoordinateLift_positive v z hv]
    rfl
  simp_rw [hlift]
  rw [div_eq_iff hP] at h
  rw [h]
  ring

/-- `∫_P E(s)(S(z + jv)) dz = v^{2−s} (π/(s−1)) U(s)`. -/
theorem cuspConstant_eisensteinS (s : ℂ) (hs : 2 < s.re) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, hyperbolicEisenstein s (rationalComplex ModularGroup.S • cuspCoordinateLift (v, z)) =
      (v : ℂ) ^ (2 - s) * ((Real.pi : ℂ) / (s - 1) * unramifiedCubicGaussSeries s 0) := by
  have h := oppositeEisenstein_fourier v hv s hs 0
  simp only [tracePhase_zero_freq, mul_one, mul_zero] at h
  have hK : sourceFourierKernel s (cuspFrequency 0 * v) = (Real.pi : ℂ) / (s - 1) := by
    rw [show cuspFrequency 0 = 0 by simp [cuspFrequency], zero_mul]
    exact sourceFourierKernel_zero s (by linarith)
  rw [hK] at h
  have hlift : ∀ z, hyperbolicEisenstein s (rationalComplex ModularGroup.S • cuspCoordinateLift (v, z)) =
      oppositeEisenstein z v hv s := by
    intro z
    rw [cuspCoordinateLift_positive v z hv, ← hyperbolicEisenstein_opposite_upper]
    rfl
  simp_rw [hlift]
  rw [h]
  ring

/-- Through a rational representative `r_q ≠ 1`, `E(s)(r_q⁻¹ w) = E(s)(S w)`. -/
theorem eisenstein_rationalRep_inv (s : ℂ) (q : RationalFourCusp) (hq : q ≠ .inl ())
    (w : HyperbolicSpace) :
    hyperbolicEisenstein s ((rationalComplex (rationalRep q))⁻¹ • w) =
      hyperbolicEisenstein s (rationalComplex ModularGroup.S • w) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, rationalRep q = ModularGroup.S * ModularGroup.T ^ k := by
    rcases q with _ | _ | _ | _
    · exact absurd rfl hq
    · exact ⟨0, by simp [rationalRep, rationalFourCuspRep]⟩
    · exact ⟨1, by simp [rationalRep, rationalFourCuspRep]⟩
    · exact ⟨2, rfl⟩
  set u := (rationalComplex (rationalRep q))⁻¹ • w
  have hw : w = rationalComplex (rationalRep q) • u := by simp [u]
  rw [hw, hk, ← mul_smul, ← map_mul, ← mul_assoc, show ModularGroup.S * ModularGroup.S =
    ModularGroup.S ^ 2 from (sq _).symm, map_mul, mul_smul, hyperbolicEisenstein_S_sq,
    hyperbolicEisenstein_T_pow]

/-! ### The truncated identity -/

/-- `E(s) ∘ S` has the multiplier `κ`. -/
theorem eisensteinS_automorphy (s : ℂ) (hs : 2 < s.re) (M : levelThree) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex ModularGroup.S • (complexMatrix M • w)) =
      complexCharacter M * hyperbolicEisenstein s (rationalComplex ModularGroup.S • w) := by
  have hmove : rationalComplex ModularGroup.S • (complexMatrix M • w) =
      complexMatrix (levelThreeConjugate (rationalEmbedding ModularGroup.S) M) •
        (rationalComplex ModularGroup.S • w) := by
    rw [← mul_smul, ← mul_smul]
    congr 1
    change integralComplexMatrix (rationalEmbedding ModularGroup.S) * integralComplexMatrix (M : SL(2, O)) =
      integralComplexMatrix ((rationalEmbedding ModularGroup.S) * (M : SL(2, O)) *
        (rationalEmbedding ModularGroup.S)⁻¹) * integralComplexMatrix (rationalEmbedding ModularGroup.S)
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [hmove, hyperbolicEisenstein_automorphy _ s hs, complexCharacter_conjugate_rational]

/-- The truncated subtraction vanishes on the standard strip above height `T`. -/
theorem cutoff_rationalRep_high (T : ℝ) (hT : 2 ≤ T) (q : RationalFourCusp) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (hvT : T < v) :
    cuspCutoffCorrection 1 (growthProfile (Set.Icc 2 T))
      (rationalComplex (rationalRep q) • upperPoint z v hv) = 0 := by
  have hzero : ∀ t, t < 2 → growthProfile (Set.Icc 2 T) t = 0 := fun t ht =>
    Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr ht)) _
  have hsmall : 1 / v < 2 := by
    rw [div_lt_iff₀ hv]
    linarith
  by_cases hq : q = .inl ()
  · subst hq
    have hp : rationalComplex (rationalRep (.inl ())) • upperPoint z v hv = upperPoint z v hv := by
      simp [rationalRep, rationalFourCuspRep]
    rw [hp, cuspCutoffCorrection_upper _ z v hv fun t _ ht => hzero t (by
      have : 1 / (9 * v) ≤ 1 / v := by
        apply div_le_div_of_nonneg_left zero_le_one hv
        linarith
      linarith)]
    rw [if_pos (by linarith), growthProfile, Set.indicator_of_notMem fun h => absurd h.2 (not_le.mpr hvT)]
  · obtain ⟨h0, h1⟩ := rationalRep_column q hq
    exact cuspCutoffCorrection_rational _ _ h0 h1 z v hv fun t _ ht => hzero t (by linarith)

theorem cutoff_rationalRep_integrable (T : ℝ) (hT : 2 ≤ T) (q : RationalFourCusp) (s : ℂ) (hs : 2 < s.re) :
    IntegrableOn (fun w => conj (cuspCutoffCorrection 1 (growthProfile (Set.Icc 2 T))
      (rationalComplex (rationalRep q) • w)) * hyperbolicEisenstein s w) levelSet hyperbolicVolume := by
  refine integrableOn_mul_eisenstein_of_strip (fun w => conj (cuspCutoffCorrection 1
    (growthProfile (Set.Icc 2 T)) (rationalComplex (rationalRep q) • w)))
    (fun M w => conj_cutoff_rational_automorphy _ _ M w)
    (Complex.continuous_conj.measurable.comp
      ((cuspCutoffCorrection_measurable 1 _ (growthProfile_measurable _ measurableSet_Icc)).comp
        (continuous_hyperbolic_action _).measurable)) (T ^ ((4 : ℝ) / 3)) T (by linarith)
    (fun z v hv => ?_) (fun z v hv hvT => ?_) s hs
  · rw [RCLike.norm_conj]
    refine cuspCutoffCorrection_norm_le _ _ (by positivity) (fun t => ?_) _
    rw [growthProfile]
    by_cases h : t ∈ Set.Icc 2 T
    · rw [Set.indicator_of_mem h, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (by
        linarith [h.1]) _)]
      exact Real.rpow_le_rpow (by linarith [h.1]) h.2 (by norm_num)
    · rw [Set.indicator_of_notMem h, norm_zero]
      positivity
  · rw [cutoff_rationalRep_high T hT q z v hv hvT, map_zero]

theorem growthProfile_mul_integrableOn (T : ℝ) (g : ℝ → ℂ) (hg : ContinuousOn g (Set.Icc 2 T)) :
    IntegrableOn (fun v => growthProfile (Set.Icc 2 T) v * g v) (Set.Ioi 0) := by
  have h : (fun v => growthProfile (Set.Icc 2 T) v * g v) =
      (Set.Icc 2 T).indicator (fun v => ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ) * g v) := by
    funext v
    rw [growthProfile, Set.indicator_mul_left]
  rw [h]
  refine ((integrable_indicator_iff measurableSet_Icc).mpr ?_).integrableOn
  refine ContinuousOn.integrableOn_Icc (ContinuousOn.mul ?_ hg)
  exact (Complex.continuous_ofReal.comp_continuousOn
    ((continuous_id.rpow_const fun _ => Or.inr (by norm_num)).continuousOn))

/-- The scattering coefficient `Φ(s) = |P| (π/(s−1)) φ(s) + 3 (π/(s−1)) U(s)`. -/
def scatterTotal (s : ℂ) : ℂ :=
  periodArea * ((Real.pi : ℂ) / (s - 1) * scatteringCoefficient s 0) +
    3 * ((Real.pi : ℂ) / (s - 1) * unramifiedCubicGaussSeries s 0)

/-- **The truncated identity.** For `T ≥ 2`, `Re s > 2`:
`∫_{D_Γ} H_T E(s) = c² ∫_0^∞ f_T(v) (|P| v^s + Φ(s) v^{2−s}) v^{−3} dv`. -/
theorem integral_cuspSubtraction_trunc_mul_eisenstein (c : ℂ) {T : ℝ} (hT : 2 ≤ T) (s : ℂ)
    (hs : 2 < s.re) :
    ∫ w in levelSet, cuspSubtraction c (Set.Icc 2 T) w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      c ^ 2 * ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v *
        (periodArea * (v : ℂ) ^ s + scatterTotal s * (v : ℂ) ^ (2 - s)) / (v : ℂ) ^ 3 := by
  set f := growthProfile (Set.Icc 2 T)
  set Fq : RationalFourCusp → HyperbolicSpace → ℂ := fun q w =>
    conj (cuspCutoffCorrection 1 f (rationalComplex (rationalRep q) • w)) * hyperbolicEisenstein s w
  have hsplit : ∀ w, cuspSubtraction c (Set.Icc 2 T) w * hyperbolicEisenstein s w =
      c ^ 2 * ∑ q : RationalFourCusp, Fq q w := by
    intro w
    rw [cuspSubtraction, mul_assoc, Finset.sum_mul]
  have hcont : Continuous (hyperbolicEisenstein s) := hyperbolicEisenstein_continuous s hs
  have hcontS : Continuous (fun w => hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)) :=
    hcont.comp (continuous_hyperbolic_action _)
  -- the identity representative
  have h1 : ∫ w in levelSet, Fq (.inl ()) w ∂hyperbolicVolume =
      ∫ v in Set.Ioi (0 : ℝ), f v * (periodArea * ((v : ℂ) ^ s + (v : ℂ) ^ (2 - s) *
        ((Real.pi : ℂ) / (s - 1) * scatteringCoefficient s 0)) / (v : ℂ) ^ 3) := by
    have hp : ∀ w : HyperbolicSpace, rationalComplex (rationalRep (.inl ())) • w = w := fun w => by
      simp [rationalRep, rationalFourCuspRep]
    simp only [Fq, hp]
    rw [integral_conj_cutoff_mul T _ hcont (fun M w => hyperbolicEisenstein_automorphy M s hs w)]
    refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
    rw [cuspConstant_eisenstein s hs v hv, mul_div_assoc]
  -- the other three representatives
  have h2 : ∀ q : RationalFourCusp, q ≠ .inl () → ∫ w in levelSet, Fq q w ∂hyperbolicVolume =
      ∫ v in Set.Ioi (0 : ℝ), f v * ((v : ℂ) ^ (2 - s) *
        ((Real.pi : ℂ) / (s - 1) * unramifiedCubicGaussSeries s 0) / (v : ℂ) ^ 3) := by
    intro q hq
    set r := rationalRep q
    let F' : HyperbolicSpace → ℂ := fun u =>
      conj (cuspCutoffCorrection 1 f u) * hyperbolicEisenstein s ((rationalComplex r)⁻¹ • u)
    have hF' : ∀ (M : levelThree) (u : HyperbolicSpace), F' (complexMatrix M • u) = F' u := by
      intro M u
      have hmove : (rationalComplex r)⁻¹ • (complexMatrix M • u) =
          complexMatrix (levelThreeConjugate (rationalEmbedding r⁻¹) M) • ((rationalComplex r)⁻¹ • u) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        change (integralComplexMatrix (rationalEmbedding r))⁻¹ * integralComplexMatrix (M : SL(2, O)) =
          integralComplexMatrix ((rationalEmbedding r⁻¹) * (M : SL(2, O)) * (rationalEmbedding r⁻¹)⁻¹) *
            (integralComplexMatrix (rationalEmbedding r))⁻¹
        simp only [map_mul, map_inv, inv_inv]
        group
      have hc := cuspCutoffCorrection_automorphy 1 le_rfl f M u
      simp only [F', hmove, hc, hyperbolicEisenstein_automorphy _ s hs, complexCharacter_conjugate_rational,
        map_mul, conj_complexCharacter]
      have hne : complexCharacter M ≠ 0 := by
        intro h0
        have := norm_complexCharacter M
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      field_simp
    have htr := setIntegral_levelSet_translate (rationalEmbedding r) F' hF'
    have hback : ∀ w, F' (integralComplexMatrix (rationalEmbedding r) • w) = Fq q w := by
      intro w
      change conj (cuspCutoffCorrection 1 f (rationalComplex r • w)) *
        hyperbolicEisenstein s ((rationalComplex r)⁻¹ • (rationalComplex r • w)) = _
      rw [inv_smul_smul]
    simp_rw [hback] at htr
    rw [htr]
    have hS : ∀ u, F' u = conj (cuspCutoffCorrection 1 f u) *
        hyperbolicEisenstein s (rationalComplex ModularGroup.S • u) := fun u =>
      congrArg (fun t => conj (cuspCutoffCorrection 1 f u) * t) (eisenstein_rationalRep_inv s q hq u)
    simp_rw [hS]
    rw [integral_conj_cutoff_mul T _ hcontS (eisensteinS_automorphy s hs)]
    refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
    rw [cuspConstant_eisensteinS s hs v hv, mul_div_assoc]
  -- assemble
  have hint : ∀ q, IntegrableOn (Fq q) levelSet hyperbolicVolume := fun q =>
    cutoff_rationalRep_integrable T hT q s hs
  simp_rw [hsplit]
  rw [integral_const_mul, integral_finsetSum _ fun q _ => hint q]
  congr 1
  have hcompl : ({.inl ()} : Finset RationalFourCusp)ᶜ.card = 3 := by
    rw [Finset.card_compl, card_rationalFourCusp, Finset.card_singleton]
  rw [Fintype.sum_eq_add_sum_compl (.inl ()), h1,
    Finset.sum_congr rfl fun q hq => h2 q (by simpa using hq), Finset.sum_const, hcompl, nsmul_eq_mul]
  have hcpow : ∀ a : ℂ, ContinuousOn (fun v : ℝ => (v : ℂ) ^ a) (Set.Icc 2 T) := fun a v hv =>
    ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr (by linarith [hv.1]))).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hden : ContinuousOn (fun v : ℝ => (v : ℂ) ^ 3) (Set.Icc 2 T) :=
    (Complex.continuous_ofReal.pow 3).continuousOn
  have hne : ∀ v ∈ Set.Icc 2 T, (v : ℂ) ^ 3 ≠ 0 := fun v hv =>
    pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (by linarith [hv.1]))
  have hA := growthProfile_mul_integrableOn T (fun v => periodArea * ((v : ℂ) ^ s + (v : ℂ) ^ (2 - s) *
      ((Real.pi : ℂ) / (s - 1) * scatteringCoefficient s 0)) / (v : ℂ) ^ 3)
    ((continuousOn_const.mul ((hcpow s).add ((hcpow (2 - s)).mul continuousOn_const))).div hden hne)
  have hB := growthProfile_mul_integrableOn T (fun v => (v : ℂ) ^ (2 - s) *
      ((Real.pi : ℂ) / (s - 1) * unramifiedCubicGaussSeries s 0) / (v : ℂ) ^ 3)
    (((hcpow (2 - s)).mul continuousOn_const).div hden hne)
  rw [Nat.cast_ofNat, ← integral_const_mul, ← integral_add hA (hB.const_mul 3)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [scatterTotal, f]
  ring

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
