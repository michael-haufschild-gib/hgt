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

/-! ### Removing the truncation -/

/-- The constant term `a₀(F)(v) = ∫_P F(z + jv) dz`. -/
def cuspConstantTerm (F : HyperbolicSpace → ℂ) (v : ℝ) : ℂ :=
  ∫ z in periodDomain, F (cuspCoordinateLift (v, z))

theorem cuspConstantTerm_measurable (F : HyperbolicSpace → ℂ) (hF : Measurable F) :
    StronglyMeasurable (cuspConstantTerm F) :=
  StronglyMeasurable.integral_prod_right'
    (f := fun p : ℝ × ℂ => F (cuspCoordinateLift p)) (hF.comp cuspCoordinateLift_measurable).stronglyMeasurable

theorem norm_cuspConstantTerm_le (F : HyperbolicSpace → ℂ) (v : ℝ) (hv : 0 < v) (C : ℝ)
    (hC : ∀ z : ℂ, ‖F (upperPoint z v hv)‖ ≤ C) : ‖cuspConstantTerm F v‖ ≤ C * periodAreaReal := by
  have hP : volume.real periodDomain = periodAreaReal := by
    rw [Measure.real, periodDomain_volume, ENNReal.toReal_ofReal periodAreaReal_pos.le]
  rw [cuspConstantTerm, ← hP]
  refine norm_setIntegral_le_of_norm_le_const (by rw [periodDomain_volume]; exact ENNReal.ofReal_lt_top)
    fun z _ => ?_
  rw [cuspCoordinateLift_positive v z hv]
  exact hC z

/-- The scattering part `a₀(H_S)(v) − |P| c² f_S(v)` of the constant term. -/
def scatterPart (c : ℂ) (S : Set ℝ) (v : ℝ) : ℂ :=
  cuspConstantTerm (cuspSubtraction c S) v - periodArea * c ^ 2 * growthProfile S v

theorem scatterPart_measurable (c : ℂ) (S : Set ℝ) (hS : MeasurableSet S) :
    StronglyMeasurable (scatterPart c S) :=
  (cuspConstantTerm_measurable _ (cuspSubtraction_measurable c S hS)).sub
    (stronglyMeasurable_const.mul (growthProfile_measurable S hS).stronglyMeasurable)

theorem scatterPart_high (c : ℂ) (S : Set ℝ) (hS : S ⊆ Set.Ici 2) (v : ℝ) (hv2 : 1 / 2 < v) :
    scatterPart c S v = 0 := by
  have hv : 0 < v := by linarith
  have hP : volume.real periodDomain = periodAreaReal := by
    rw [Measure.real, periodDomain_volume, ENNReal.toReal_ofReal periodAreaReal_pos.le]
  rw [scatterPart, cuspConstantTerm]
  have hc : ∀ z, cuspSubtraction c S (cuspCoordinateLift (v, z)) = c ^ 2 * growthProfile S v := fun z => by
    rw [cuspCoordinateLift_positive v z hv, cuspSubtraction_upper c S hS z v hv hv2]
  simp_rw [hc]
  rw [setIntegral_const, hP, Complex.real_smul]
  ring

theorem norm_scatterPart_small (c : ℂ) (S : Set ℝ) (hS : S ⊆ Set.Ici 2) (v : ℝ) (hv : 0 < v)
    (hv2 : v ≤ 1 / 2) :
    ‖scatterPart c S v‖ ≤ ‖c‖ ^ 2 * (4 * (1 / v) ^ ((4 : ℝ) / 3)) * periodAreaReal := by
  have hf : growthProfile S v = 0 :=
    Set.indicator_of_notMem (fun h => by linarith [Set.mem_Ici.mp (hS h)]) _
  rw [scatterPart, hf, mul_zero, sub_zero]
  exact norm_cuspConstantTerm_le _ v hv _ fun z => norm_cuspSubtraction_small c S z v hv hv2

theorem scatterPart_truncate (c : ℂ) {T : ℝ} (hT : 2 ≤ T) (v : ℝ) (hv : 0 < v) (hvT : 1 / T ≤ v) :
    scatterPart c (Set.Icc 2 T) v = scatterPart c (Set.Ici 2) v := by
  by_cases hv2 : v ≤ 1 / 2
  · have hf : ∀ S : Set ℝ, S ⊆ Set.Ici 2 → growthProfile S v = 0 := fun S hS =>
      Set.indicator_of_notMem (fun h => by linarith [Set.mem_Ici.mp (hS h)]) _
    rw [scatterPart, scatterPart, hf _ (fun t ht => ht.1), hf _ le_rfl, cuspConstantTerm, cuspConstantTerm]
    congr 1
    refine setIntegral_congr_fun periodDomain_measurable fun z _ => ?_
    rw [cuspCoordinateLift_positive v z hv, cuspSubtraction_truncate c hT z v hv hv2 hvT]
  · rw [scatterPart_high c _ (fun t ht => ht.1) v (not_le.mp hv2),
      scatterPart_high c _ le_rfl v (not_le.mp hv2)]

/-- The Mellin integrand of the scattering part is integrable for `Re s > 10/3`. -/
theorem integrableOn_scatterPart (c : ℂ) (S : Set ℝ) (hS : S ⊆ Set.Ici 2) (hSm : MeasurableSet S)
    (s : ℂ) (hs : 10 / 3 < s.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ s * scatterPart c S v / (v : ℂ) ^ 3) (Set.Ioi 0) := by
  set C := ‖c‖ ^ 2 * 4 * periodAreaReal
  have hg : IntegrableOn (fun v : ℝ => C * v ^ (s.re - 13 / 3)) (Set.Ioc 0 (1 / 2)) := by
    have := intervalIntegral.intervalIntegrable_rpow' (r := s.re - 13 / 3) (by linarith)
      (a := 0) (b := 1 / 2)
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp this).const_mul C
  have hm : AEStronglyMeasurable (fun v : ℝ => (v : ℂ) ^ s * scatterPart c S v / (v : ℂ) ^ 3)
      (volume.restrict (Set.Ioc 0 (1 / 2))) :=
    (((Complex.measurable_ofReal.pow_const s).mul (scatterPart_measurable c S hSm).measurable).div
      (Complex.measurable_ofReal.pow_const 3)).aestronglyMeasurable
  have h1 : IntegrableOn (fun v : ℝ => (v : ℂ) ^ s * scatterPart c S v / (v : ℂ) ^ 3)
      (Set.Ioc 0 (1 / 2)) := by
    refine hg.mono' hm (ae_restrict_of_forall_mem measurableSet_Ioc fun v hv => ?_)
    have hv0 := hv.1
    have hb := norm_scatterPart_small c S hS v hv0 hv.2
    rw [norm_div, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hv0, Complex.norm_real,
      Real.norm_of_nonneg hv0.le]
    have hpow : (1 / v) ^ ((4 : ℝ) / 3) = v ^ (-((4 : ℝ) / 3)) := by
      rw [one_div, Real.inv_rpow hv0.le, Real.rpow_neg hv0.le]
    rw [hpow] at hb
    have he : v ^ s.re * (‖c‖ ^ 2 * (4 * v ^ (-((4 : ℝ) / 3))) * periodAreaReal) / v ^ 3 =
        C * v ^ (s.re - 13 / 3) := by
      rw [show s.re - 13 / 3 = s.re + (-((4 : ℝ) / 3)) - 3 by ring, Real.rpow_sub hv0,
        Real.rpow_add hv0]
      norm_cast
      ring
    calc v ^ s.re * ‖scatterPart c S v‖ / v ^ 3
        ≤ v ^ s.re * (‖c‖ ^ 2 * (4 * v ^ (-((4 : ℝ) / 3))) * periodAreaReal) / v ^ 3 := by
          gcongr
      _ = C * v ^ (s.re - 13 / 3) := he
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun v hv => ?_
  have hv2 : 1 / 2 < v := by
    by_contra h
    exact hv.2 ⟨hv.1, not_lt.mp h⟩
  rw [scatterPart_high c S hS v hv2, mul_zero, zero_div]

/-- The Mellin integrand of the full profile is integrable for `Re s > 4/3`. -/
theorem integrableOn_growthProfile_full (s : ℂ) (hs : 4 / 3 < s.re) :
    IntegrableOn (fun v : ℝ => growthProfile (Set.Ici 2) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3)
      (Set.Ioi 0) := by
  have hg : IntegrableOn (fun v : ℝ => v ^ ((1 : ℝ) / 3 - s.re)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hm : AEStronglyMeasurable (fun v : ℝ => growthProfile (Set.Ici 2) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3)
      (volume.restrict (Set.Ioi 1)) :=
    (((growthProfile_measurable _ measurableSet_Ici).mul (Complex.measurable_ofReal.pow_const _)).div
      (Complex.measurable_ofReal.pow_const 3)).aestronglyMeasurable
  have h1 : IntegrableOn (fun v : ℝ => growthProfile (Set.Ici 2) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3)
      (Set.Ioi 1) := by
    refine hg.mono' hm (ae_restrict_of_forall_mem measurableSet_Ioi fun v (hv : 1 < v) => ?_)
    have hv0 : 0 < v := by linarith
    rw [norm_div, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hv0, Complex.norm_real,
      Real.norm_of_nonneg hv0.le]
    have hf := norm_growthProfile_le (Set.Ici 2) hv0.le
    have he : v ^ ((4 : ℝ) / 3) * v ^ (2 - s).re / v ^ 3 = v ^ ((1 : ℝ) / 3 - s.re) := by
      rw [Complex.sub_re, Complex.re_ofNat, show (1 : ℝ) / 3 - s.re = (4 : ℝ) / 3 + (2 - s.re) - 3 by ring]
      conv_rhs => rw [Real.rpow_sub hv0, Real.rpow_add hv0]
      norm_cast
    calc ‖growthProfile (Set.Ici 2) v‖ * v ^ (2 - s).re / v ^ 3
        ≤ v ^ ((4 : ℝ) / 3) * v ^ (2 - s).re / v ^ 3 := by gcongr
      _ = _ := he
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun v hv => ?_
  have hv1 : v ≤ 1 := not_lt.mp hv.2
  rw [growthProfile, Set.indicator_of_notMem (fun h => by linarith [show (2 : ℝ) ≤ v from h]),
    zero_mul, zero_div]

/-- **The scattering of the rational cusp subtraction.** For `Re s > 10/3`:
`∫_0^∞ v^s (a₀(H)(v) − |P| c² f(v)) v^{−3} dv = c² Φ(s) ∫_0^∞ f(v) v^{2−s} v^{−3} dv`. -/
theorem integral_scatterPart (c : ℂ) (s : ℂ) (hs : 10 / 3 < s.re) :
    ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * scatterPart c (Set.Ici 2) v / (v : ℂ) ^ 3 =
      c ^ 2 * scatterTotal s * ∫ v in Set.Ioi (0 : ℝ),
        growthProfile (Set.Ici 2) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
  have hs2 : 2 < s.re := by linarith
  set X := (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * scatterPart c (Set.Ici 2) v / (v : ℂ) ^ 3) -
    c ^ 2 * scatterTotal s * ∫ v in Set.Ioi (0 : ℝ),
      growthProfile (Set.Ici 2) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 with hX
  suffices hX0 : X = 0 from sub_eq_zero.mp hX0
  set A := 2 * (‖c‖ ^ 2 * 4 * periodAreaReal) / (s.re - 10 / 3)
  set B := ‖c ^ 2 * scatterTotal s‖ / (s.re - 4 / 3)
  -- the truncated identity in Mellin form
  have htrunc : ∀ T : ℝ, 2 ≤ T →
      ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * scatterPart c (Set.Icc 2 T) v / (v : ℂ) ^ 3 =
        c ^ 2 * scatterTotal s * ∫ v in Set.Ioi (0 : ℝ),
          growthProfile (Set.Icc 2 T) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
    intro T hT
    have hcpow : ∀ a : ℂ, ContinuousOn (fun v : ℝ => (v : ℂ) ^ a) (Set.Icc 2 T) := fun a v hv =>
      ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr (by linarith [hv.1]))).comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
    have hden : ContinuousOn (fun v : ℝ => (v : ℂ) ^ 3) (Set.Icc 2 T) :=
      (Complex.continuous_ofReal.pow 3).continuousOn
    have hne : ∀ v ∈ Set.Icc 2 T, (v : ℂ) ^ 3 ≠ 0 := fun v hv =>
      pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (by linarith [hv.1]))
    have I1 := integrableOn_scatterPart c (Set.Icc 2 T) (fun t ht => ht.1) measurableSet_Icc s hs
    have I2 := growthProfile_mul_integrableOn T (fun v => periodArea * c ^ 2 * (v : ℂ) ^ s / (v : ℂ) ^ 3)
      ((continuousOn_const.mul (hcpow s)).div hden hne)
    have I3 := growthProfile_mul_integrableOn T (fun v => (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3)
      ((hcpow (2 - s)).div hden hne)
    have hint := integrableOn_unfolded_of_strip (cuspSubtraction c (Set.Icc 2 T))
      (cuspSubtraction_measurable c _ measurableSet_Icc) (‖c‖ ^ 2 * (4 * T ^ ((4 : ℝ) / 3))) T
      (by linarith) (fun z v hv => norm_cuspSubtraction_le c hT _ subset_rfl _) (fun z v hv hvT => by
        rw [cuspSubtraction_upper c _ (fun t ht => ht.1) z v hv (by linarith), growthProfile,
          Set.indicator_of_notMem (fun h => absurd h.2 (not_le.mpr hvT)), mul_zero]) s hs2
    have hunf := integral_mul_hyperbolicEisenstein_eq_constantTerm (cuspSubtraction c (Set.Icc 2 T))
      (cuspSubtraction_automorphy c _) s hint
    rw [integral_cuspSubtraction_trunc_mul_eisenstein c hT s hs2] at hunf
    have hsplit : ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
          (∫ z in periodDomain, cuspSubtraction c (Set.Icc 2 T) (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 =
        (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * scatterPart c (Set.Icc 2 T) v / (v : ℂ) ^ 3) +
          ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v *
            (periodArea * c ^ 2 * (v : ℂ) ^ s / (v : ℂ) ^ 3) := by
      rw [← integral_add I1 I2]
      refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
      simp only [scatterPart, cuspConstantTerm]
      ring
    have hright : c ^ 2 * ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v *
          (periodArea * (v : ℂ) ^ s + scatterTotal s * (v : ℂ) ^ (2 - s)) / (v : ℂ) ^ 3 =
        (∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v *
            (periodArea * c ^ 2 * (v : ℂ) ^ s / (v : ℂ) ^ 3)) +
          c ^ 2 * scatterTotal s * ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v *
            ((v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3) := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add I2 (I3.const_mul _)]
      refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
      ring
    rw [hsplit, hright] at hunf
    have hfin : ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 =
        ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v * ((v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3) :=
      setIntegral_congr_fun measurableSet_Ioi fun v _ => mul_div_assoc _ _ _
    rw [hfin]
    linear_combination -hunf
  -- the two error terms
  have hσ1 : 0 < s.re - 10 / 3 := by linarith
  have hσ2 : 0 < s.re - 4 / 3 := by linarith
  set C' := ‖c‖ ^ 2 * 4 * periodAreaReal
  have hbound : ∀ T : ℝ, 2 ≤ T → ‖X‖ ≤ 2 * C' / (s.re - 10 / 3) * T ^ (-(s.re - 10 / 3)) +
      ‖c ^ 2 * scatterTotal s‖ / (s.re - 4 / 3) * T ^ (-(s.re - 4 / 3)) := by
    intro T hT
    have hT0 : 0 < T := by linarith
    have hX : X = (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
          (scatterPart c (Set.Ici 2) v - scatterPart c (Set.Icc 2 T) v) / (v : ℂ) ^ 3) -
        c ^ 2 * scatterTotal s * ∫ v in Set.Ioi (0 : ℝ),
          (growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
      have J1 := integrableOn_scatterPart c (Set.Ici 2) le_rfl measurableSet_Ici s hs
      have J2 := integrableOn_scatterPart c (Set.Icc 2 T) (fun t ht => ht.1) measurableSet_Icc s hs
      have J3 := integrableOn_growthProfile_full s (by linarith)
      have J4 : IntegrableOn (fun v : ℝ => growthProfile (Set.Icc 2 T) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3)
          (Set.Ioi 0) := by
        have := growthProfile_mul_integrableOn T (fun v => (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3)
          ((ContinuousOn.div (fun v hv => ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr
            (by linarith [hv.1]))).comp Complex.continuous_ofReal.continuousAt).continuousWithinAt)
            (Complex.continuous_ofReal.pow 3).continuousOn fun v hv =>
              pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (by linarith [hv.1]))))
        exact this.congr_fun (fun v _ => (mul_div_assoc _ _ _).symm) measurableSet_Ioi
      have e1 : ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
          (scatterPart c (Set.Ici 2) v - scatterPart c (Set.Icc 2 T) v) / (v : ℂ) ^ 3 =
          (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * scatterPart c (Set.Ici 2) v / (v : ℂ) ^ 3) -
            ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * scatterPart c (Set.Icc 2 T) v / (v : ℂ) ^ 3 := by
        rw [← integral_sub J1 J2]
        refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
        ring
      have e2 : ∫ v in Set.Ioi (0 : ℝ),
          (growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 =
          (∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Ici 2) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3) -
            ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
        rw [← integral_sub J3 J4]
        refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
        ring
      rw [e1, e2, htrunc T hT, hX]
      ring
    -- first error term: supported on `(0, 1/T)`
    have hb1 : ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
        (scatterPart c (Set.Ici 2) v - scatterPart c (Set.Icc 2 T) v) / (v : ℂ) ^ 3‖ ≤
        2 * C' / (s.re - 10 / 3) * T ^ (-(s.re - 10 / 3)) := by
      have hsub : ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
          (scatterPart c (Set.Ici 2) v - scatterPart c (Set.Icc 2 T) v) / (v : ℂ) ^ 3 =
          ∫ v in Set.Ioc 0 (1 / T), (v : ℂ) ^ s *
            (scatterPart c (Set.Ici 2) v - scatterPart c (Set.Icc 2 T) v) / (v : ℂ) ^ 3 := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self
          fun v hv => ?_
        have hv0 : 0 < v := hv.1
        have hvT : 1 / T ≤ v := by
          by_contra h
          exact hv.2 ⟨hv0, (not_le.mp h).le⟩
        rw [scatterPart_truncate c hT v hv0 hvT, sub_self, mul_zero, zero_div]
      rw [hsub]
      have hT2 : 1 / T ≤ 1 / 2 := by
        apply div_le_div_of_nonneg_left zero_le_one (by norm_num) hT
      have hgi : IntegrableOn (fun v : ℝ => 2 * C' * v ^ (s.re - 13 / 3)) (Set.Ioc 0 (1 / T)) := by
        have := intervalIntegral.intervalIntegrable_rpow' (r := s.re - 13 / 3) (by linarith)
          (a := 0) (b := 1 / T)
        exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp this).const_mul _
      refine (norm_integral_le_of_norm_le hgi (ae_restrict_of_forall_mem measurableSet_Ioc
        fun v hv => ?_)).trans (le_of_eq ?_)
      · have hv0 := hv.1
        have hv2 : v ≤ 1 / 2 := hv.2.trans hT2
        have hb1' := norm_scatterPart_small c (Set.Ici 2) le_rfl v hv0 hv2
        have hb2' := norm_scatterPart_small c (Set.Icc 2 T) (fun t ht => ht.1) v hv0 hv2
        have hpow : (1 / v) ^ ((4 : ℝ) / 3) = v ^ (-((4 : ℝ) / 3)) := by
          rw [one_div, Real.inv_rpow hv0.le, Real.rpow_neg hv0.le]
        rw [hpow] at hb1' hb2'
        rw [norm_div, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hv0, Complex.norm_real,
          Real.norm_of_nonneg hv0.le]
        have htri := norm_sub_le (scatterPart c (Set.Ici 2) v) (scatterPart c (Set.Icc 2 T) v)
        have he : v ^ s.re * (2 * (‖c‖ ^ 2 * (4 * v ^ (-((4 : ℝ) / 3))) * periodAreaReal)) / v ^ 3 =
            2 * C' * v ^ (s.re - 13 / 3) := by
          rw [show s.re - 13 / 3 = s.re + (-((4 : ℝ) / 3)) - 3 by ring, Real.rpow_sub hv0,
            Real.rpow_add hv0]
          norm_cast
          ring
        calc v ^ s.re * ‖scatterPart c (Set.Ici 2) v - scatterPart c (Set.Icc 2 T) v‖ / v ^ 3
            ≤ v ^ s.re * (2 * (‖c‖ ^ 2 * (4 * v ^ (-((4 : ℝ) / 3))) * periodAreaReal)) / v ^ 3 := by
              gcongr
              linarith
          _ = 2 * C' * v ^ (s.re - 13 / 3) := he
      · rw [integral_const_mul, ← intervalIntegral.integral_of_le (by positivity),
          integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith), sub_zero,
          show s.re - 13 / 3 + 1 = s.re - 10 / 3 by ring, one_div, Real.inv_rpow hT0.le,
          ← Real.rpow_neg hT0.le]
        field_simp
    -- second error term: supported on `(T, ∞)`
    have hb2 : ‖∫ v in Set.Ioi (0 : ℝ),
        (growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3‖ ≤
        1 / (s.re - 4 / 3) * T ^ (-(s.re - 4 / 3)) := by
      have hdiff : ∀ v, growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v =
          (Set.Ioi T).indicator (fun v => ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ)) v := by
        intro v
        by_cases h2 : 2 ≤ v
        · by_cases hT' : v ≤ T
          · simp [growthProfile, Set.indicator, h2, hT', not_lt.mpr hT']
          · simp [growthProfile, Set.indicator, h2, hT', lt_of_not_ge hT']
        · have hnT : ¬T < v := fun h => h2 (by linarith)
          simp [growthProfile, Set.indicator, h2, hnT]
      have hsub : ∫ v in Set.Ioi (0 : ℝ),
          (growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 =
          ∫ v in Set.Ioi T,
            (growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          (Set.Ioi_subset_Ioi hT0.le) fun v hv => ?_
        rw [hdiff, Set.indicator_of_notMem hv.2, zero_mul, zero_div]
      rw [hsub]
      have hgi : IntegrableOn (fun v : ℝ => v ^ ((1 : ℝ) / 3 - s.re)) (Set.Ioi T) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) hT0
      refine (norm_integral_le_of_norm_le hgi (ae_restrict_of_forall_mem measurableSet_Ioi
        fun v (hv : T < v) => ?_)).trans (le_of_eq ?_)
      · have hv0 : 0 < v := by linarith
        rw [hdiff, Set.indicator_of_mem (show v ∈ Set.Ioi T from hv), norm_div, norm_mul, norm_pow,
          Complex.norm_cpow_eq_rpow_re_of_pos hv0, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hv0.le, Real.norm_of_nonneg (Real.rpow_nonneg hv0.le _), Complex.sub_re,
          Complex.re_ofNat, show (1 : ℝ) / 3 - s.re = (4 : ℝ) / 3 + (2 - s.re) - 3 by ring]
        conv_rhs => rw [Real.rpow_sub hv0, Real.rpow_add hv0]
        norm_cast
      · rw [integral_Ioi_rpow_of_lt (by linarith) hT0, show (1 : ℝ) / 3 - s.re + 1 = -(s.re - 4 / 3) by ring]
        field_simp
    rw [hX]
    calc ‖_ - _‖ ≤ ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
          (scatterPart c (Set.Ici 2) v - scatterPart c (Set.Icc 2 T) v) / (v : ℂ) ^ 3‖ +
        ‖c ^ 2 * scatterTotal s‖ * ‖∫ v in Set.Ioi (0 : ℝ),
          (growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3‖ := by
          rw [← norm_mul]
          exact norm_sub_le _ _
      _ ≤ 2 * C' / (s.re - 10 / 3) * T ^ (-(s.re - 10 / 3)) +
          ‖c ^ 2 * scatterTotal s‖ * (1 / (s.re - 4 / 3) * T ^ (-(s.re - 4 / 3))) := by gcongr
      _ = _ := by ring
  have hlim : Tendsto (fun T : ℝ => 2 * C' / (s.re - 10 / 3) * T ^ (-(s.re - 10 / 3)) +
      ‖c ^ 2 * scatterTotal s‖ / (s.re - 4 / 3) * T ^ (-(s.re - 4 / 3))) atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_atTop hσ1).const_mul (2 * C' / (s.re - 10 / 3))
    have h2 := (tendsto_rpow_neg_atTop hσ2).const_mul (‖c ^ 2 * scatterTotal s‖ / (s.re - 4 / 3))
    simpa using h1.add h2
  have hle : ‖X‖ ≤ 0 := ge_of_tendsto hlim ((eventually_ge_atTop 2).mono hbound)
  exact norm_le_zero_iff.mp hle

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
