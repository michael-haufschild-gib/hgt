import GaloisForLFunctions.RHTower.InfiniteMobiusShiftAnalysis
import GaloisForLFunctions.RHTower.ZetaTwoShiftContraction
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.SeamRealAxisGrowth
import GaloisForLFunctions.RHTower.CCMRectangularAutocorrelation

/-!
# Critical escape of the normalized Möbius shift channel

This leaf records the exact obstruction behind the compensated-cancellation pivot.

* The zero-mean adjacent rectangular Haar window pairs with a complementary cutoff only when the
  divisor logarithm lies in one finite shell.
* The paper-normalized Möbius shift channel has exact squared norm `ζ(2σ)⁻¹ ‖f‖²`, is a strict
  contraction for every `σ > 1`, and loses every fixed finite divisor window as `σ → 1+`.
* The full channel is weakly null but not strongly null on nonzero inputs. Every fixed compact
  synthesis therefore annihilates it at criticality.

These are unconditional source-side results. They do not estimate the RH-bearing localized
commutator; they prove why that commutator must move mass from cofinally remote Möbius channels into
the near-aperture prime--polar shell before the critical limit.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace RHTower

/-- Pairing of the adjacent rectangular Haar window with the constant boundary mode cut off at
`a`. -/
def rectangularHaarBoundaryIncidence (c L a : ℝ) : ℝ :=
  (volume (Ioc c (c + L) ∩ Iic a)).toReal -
    (volume (Ioc (c - L) c ∩ Iic a)).toReal

theorem Ioc_inter_Iic (u v a : ℝ) :
    Ioc u v ∩ Iic a = Ioc u (min v a) := by
  ext x
  simp only [mem_inter_iff, mem_Ioc, mem_Iic]
  constructor
  · rintro ⟨⟨hu, hv⟩, ha⟩
    exact ⟨hu, le_min hv ha⟩
  · rintro ⟨hu, hmin⟩
    exact ⟨⟨hu, hmin.trans (min_le_left _ _)⟩,
      hmin.trans (min_le_right _ _)⟩

theorem rectangularHaarBoundaryIncidence_eq
    (c L a : ℝ) :
    rectangularHaarBoundaryIncidence c L a =
      max 0 (min (c + L) a - c) -
        max 0 (min c a - (c - L)) := by
  rw [rectangularHaarBoundaryIncidence, Ioc_inter_Iic, Ioc_inter_Iic,
    Real.volume_Ioc, Real.volume_Ioc, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rw [max_comm (min (c + L) a - c) 0,
    max_comm (min c a - (c - L)) 0]

theorem rectangularHaarBoundaryIncidence_eq_zero_of_le_left
    {c L a : ℝ} (hL : 0 ≤ L) (ha : a ≤ c - L) :
    rectangularHaarBoundaryIncidence c L a = 0 := by
  rw [rectangularHaarBoundaryIncidence_eq]
  have ha1 : min (c + L) a = a := min_eq_right (by linarith)
  have ha2 : min c a = a := min_eq_right (by linarith)
  rw [ha1, ha2, max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

theorem rectangularHaarBoundaryIncidence_eq_zero_of_right_le
    {c L a : ℝ} (hL : 0 ≤ L) (ha : c + L ≤ a) :
    rectangularHaarBoundaryIncidence c L a = 0 := by
  rw [rectangularHaarBoundaryIncidence_eq]
  have ha1 : min (c + L) a = c + L := min_eq_left ha
  have ha2 : min c a = c := min_eq_left (by linarith)
  rw [ha1, ha2]
  have hright : c + L - c = L := by ring
  have hleft : c - (c - L) = L := by ring
  rw [hright, hleft]
  ring

/-- The zero-mean Haar readout annihilates every complementary cutoff whose boundary is outside the
open shell `(c-L,c+L)`. -/
theorem rectangularHaarBoundaryIncidence_eq_zero_off_shell
    {c L a : ℝ} (hL : 0 ≤ L)
    (ha : a ≤ c - L ∨ c + L ≤ a) :
    rectangularHaarBoundaryIncidence c L a = 0 := by
  rcases ha with ha | ha
  · exact rectangularHaarBoundaryIncidence_eq_zero_of_le_left hL ha
  · exact rectangularHaarBoundaryIncidence_eq_zero_of_right_le hL ha

def rectangularHaarWindow (c L t : ℝ) : ℝ :=
  rectangularIntervalIndicator c L t -
    rectangularIntervalIndicator (c - L) L t

theorem integrable_rectangularIntervalIndicator (u L : ℝ) :
    Integrable (rectangularIntervalIndicator u L) := by
  rw [show rectangularIntervalIndicator u L =
      (Ioc u (u + L)).indicator (1 : ℝ → ℝ) by
    funext t
    rfl]
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (ne_of_lt measure_Ioc_lt_top)

theorem integral_rectangularIntervalIndicator_Iic (u L a : ℝ) :
    (∫ t in Iic a, rectangularIntervalIndicator u L t) =
      (volume (Ioc u (u + L) ∩ Iic a)).toReal := by
  rw [← integral_indicator measurableSet_Iic]
  rw [show (Iic a).indicator (rectangularIntervalIndicator u L) =
      (Ioc u (u + L) ∩ Iic a).indicator (1 : ℝ → ℝ) by
    rw [show rectangularIntervalIndicator u L =
        (Ioc u (u + L)).indicator (1 : ℝ → ℝ) by rfl,
      Set.indicator_indicator, inter_comm]]
  rw [integral_indicator_one (measurableSet_Ioc.inter measurableSet_Iic),
    Measure.real]

theorem rectangularHaarBoundaryIncidence_eq_integral
    (c L a : ℝ) :
    rectangularHaarBoundaryIncidence c L a =
      ∫ t in Iic a, rectangularHaarWindow c L t := by
  change rectangularHaarBoundaryIncidence c L a =
    ∫ t in Iic a, (rectangularIntervalIndicator c L t -
      rectangularIntervalIndicator (c - L) L t)
  rw [rectangularHaarBoundaryIncidence,
    integral_sub
      (integrable_rectangularIntervalIndicator c L).integrableOn
      (integrable_rectangularIntervalIndicator (c - L) L).integrableOn,
    integral_rectangularIntervalIndicator_Iic,
    integral_rectangularIntervalIndicator_Iic]
  rw [show c - L + L = c by ring]

theorem rectangularHaarBoundaryIncidence_log_eq_zero_of_not_mem_shell
    {c L : ℝ} (hL : 0 ≤ L) (d : ℕ)
    (hd : Real.log d ∉ Ioo (c - L) (c + L)) :
    rectangularHaarBoundaryIncidence c L (Real.log d) = 0 := by
  apply rectangularHaarBoundaryIncidence_eq_zero_off_shell hL
  simpa only [mem_Ioo, not_and_or, not_lt] using hd

theorem one_lt_zetaTwoShiftTotal
    {sigma : ℝ} (hsigma : 1 < sigma) :
    1 < zetaTwoShiftTotal sigma := by
  have hs := summable_zetaTwoShiftMass hsigma
  have hsplit := hs.sum_add_tsum_nat_add 1
  have htailSummable : Summable (fun n : ℕ => zetaTwoShiftMass sigma (n + 1)) :=
    (summable_nat_add_iff 1).2 hs
  have htailPos : 0 < ∑' n : ℕ, zetaTwoShiftMass sigma (n + 1) :=
    htailSummable.tsum_pos
      (fun n => (zetaTwoShiftMass_pos sigma (n + 1)).le) 0
      (zetaTwoShiftMass_pos sigma 1)
  rw [show zetaTwoShiftTotal sigma = ∑' n : ℕ, zetaTwoShiftMass sigma n by rfl]
  rw [← hsplit]
  have hzero : zetaTwoShiftMass sigma 0 = 1 := by
    simp [zetaTwoShiftMass]
  rw [Finset.sum_range_one, hzero]
  linarith

/-- Paper normalization of the unit Möbius shift analysis: `ζ(2σ)⁻¹/²`. -/
def mobiusCriticalContractionScale (sigma : ℝ) : ℝ :=
  (Real.sqrt (zetaTwoShiftTotal sigma))⁻¹

theorem mobiusCriticalContractionScale_nonneg (sigma : ℝ) :
    0 ≤ mobiusCriticalContractionScale sigma := by
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem mobiusCriticalContractionScale_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    mobiusCriticalContractionScale sigma ^ 2 =
      (zetaTwoShiftTotal sigma)⁻¹ := by
  rw [mobiusCriticalContractionScale, inv_pow, Real.sq_sqrt]
  exact (zetaTwoShiftTotal_pos hsigma).le

theorem mobiusCriticalContractionScale_lt_one
    {sigma : ℝ} (hsigma : 1 < sigma) :
    mobiusCriticalContractionScale sigma < 1 := by
  rw [mobiusCriticalContractionScale,
    inv_lt_one₀ (Real.sqrt_pos.2 (zetaTwoShiftTotal_pos hsigma))]
  exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2
    (by simpa using one_lt_zetaTwoShiftTotal hsigma)

/-- The divisor-resolved Möbius shift channel with the paper normalization. -/
def mobiusCriticalShiftChannelValue
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : InfiniteMobiusShiftChannel :=
  (mobiusCriticalContractionScale sigma : ℂ) •
    infiniteMobiusShiftAnalysisValue sigma hsigma f

theorem mobiusCriticalShiftChannelValue_apply
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) :
    mobiusCriticalShiftChannelValue sigma hsigma f n =
      (mobiusCriticalContractionScale sigma : ℂ) •
        (infiniteMobiusSignedWeight sigma n •
          MellinL2.additiveTranslationUnitary (-Real.log n) f) := by
  rfl

/-- Exact norm law `‖C_σ f‖² = ζ(2σ)⁻¹ ‖f‖²`. -/
theorem norm_mobiusCriticalShiftChannelValue_sq
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖mobiusCriticalShiftChannelValue sigma hsigma f‖ ^ 2 =
      (zetaTwoShiftTotal sigma)⁻¹ * ‖f‖ ^ 2 := by
  rw [mobiusCriticalShiftChannelValue, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (mobiusCriticalContractionScale_nonneg sigma),
    mul_pow, norm_infiniteMobiusShiftAnalysisValue_sq,
    mobiusCriticalContractionScale_sq hsigma]

theorem norm_mobiusCriticalShiftChannelValue_lt
    (sigma : ℝ) (hsigma : 1 < sigma)
    {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ≠ 0) :
    ‖mobiusCriticalShiftChannelValue sigma hsigma f‖ < ‖f‖ := by
  rw [mobiusCriticalShiftChannelValue, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (mobiusCriticalContractionScale_nonneg sigma),
    norm_infiniteMobiusShiftAnalysisValue]
  exact (mul_lt_iff_lt_one_left (norm_pos_iff.mpr hf)).mpr
    (mobiusCriticalContractionScale_lt_one hsigma)

def mobiusCriticalShiftChannel
    (sigma : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    InfiniteMobiusShiftChannel :=
  if hsigma : 1 < sigma then mobiusCriticalShiftChannelValue sigma hsigma f else 0

theorem mobiusCriticalShiftChannel_eq
    {sigma : ℝ} (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    mobiusCriticalShiftChannel sigma f =
      mobiusCriticalShiftChannelValue sigma hsigma f := by
  simp only [mobiusCriticalShiftChannel, dif_pos hsigma]

theorem tendsto_inv_squarefreeMobiusTotal_zero :
    Tendsto (fun sigma : ℝ => (squarefreeMobiusTotal sigma)⁻¹)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hsigma : Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have htwoArg : Tendsto (fun sigma : ℝ => 2 * (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) := by
    simpa using (tendsto_const_nhds.mul hsigma :
      Tendsto (fun sigma : ℝ => (2 : ℂ) * (sigma : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 ((2 : ℂ) * 1)))
  have hnum : Tendsto (fun sigma : ℝ => riemannZeta (2 * (sigma : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) :=
    (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto.comp htwoArg
  have hunit : Tendsto (fun sigma : ℝ => zetaResidueUnit (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using! zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hsigma
  have hsub : Tendsto (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa using hsigma.sub_const (1 : ℂ)
  have hcomplex : Tendsto
      (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ) *
        riemannZeta (2 * (sigma : ℂ)) / zetaResidueUnit (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa using! (hsub.mul hnum).div hunit (by norm_num : (1 : ℂ) ≠ 0)
  have heq :
      (fun sigma : ℝ => (((squarefreeMobiusTotal sigma)⁻¹ : ℝ) : ℂ)) =ᶠ[𝓝[>] (1 : ℝ)]
        fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ) *
          riemannZeta (2 * (sigma : ℂ)) / zetaResidueUnit (sigma : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigmaGt
    change 1 < sigma at hsigmaGt
    have hsigmaOne : (sigma : ℂ) ≠ 1 := by exact_mod_cast ne_of_gt hsigmaGt
    have hzetaSigma : riemannZeta (sigma : ℂ) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigmaGt)
    have hzetaTwo : riemannZeta (2 * (sigma : ℂ)) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
    rw [Complex.ofReal_inv, ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigmaGt]
    rw [show zetaResidueUnit (sigma : ℂ) =
        ((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ) by
      simp only [zetaResidueUnit, Function.update_of_ne hsigmaOne]]
    push_cast
    field_simp [hzetaSigma, hzetaTwo, hsigmaOne,
      sub_ne_zero.mpr hsigmaOne]
  have hcast : Tendsto
      (fun sigma : ℝ => (((squarefreeMobiusTotal sigma)⁻¹ : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := hcomplex.congr' heq.symm
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hcast
  simpa [Function.comp_def] using hre

theorem tendsto_squarefreeMobiusProbability_zero (n : ℕ) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusProbability sigma n)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hmass : Tendsto (fun sigma : ℝ => squarefreeMobiusMass sigma n)
      (𝓝[>] (1 : ℝ)) (𝓝 (squarefreeMobiusMass 1 n)) := by
    have hcont : ContinuousAt (fun sigma : ℝ => squarefreeMobiusMass sigma n) 1 := by
      unfold squarefreeMobiusMass
      split_ifs with hn
      · have hn0 : n ≠ 0 := by
          intro hn0
          subst n
          exact not_squarefree_zero hn
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have hnreal : (n : ℝ) ≠ 0 := ne_of_gt hnpos
        simpa using! ((Real.continuous_const_rpow hnreal).comp continuous_neg).continuousAt
      · fun_prop
    exact hcont.tendsto.mono_left inf_le_left
  simpa only [squarefreeMobiusProbability, div_eq_mul_inv, mul_zero] using
    hmass.mul tendsto_inv_squarefreeMobiusTotal_zero

theorem tendsto_inv_zetaTwoShiftTotal :
    Tendsto (fun sigma : ℝ => (zetaTwoShiftTotal sigma)⁻¹)
      (𝓝[>] (1 : ℝ)) (𝓝 ((riemannZeta (2 : ℂ)).re)⁻¹) := by
  have hsigma : Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have htwoArg : Tendsto (fun sigma : ℝ => 2 * (sigma : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (2 : ℂ)) := by
    simpa using (tendsto_const_nhds.mul hsigma :
      Tendsto (fun sigma : ℝ => (2 : ℂ) * (sigma : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 ((2 : ℂ) * 1)))
  have hzeta : Tendsto (fun sigma : ℝ => riemannZeta (2 * (sigma : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) :=
    (differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.tendsto.comp htwoArg
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hzeta
  have heq :
      (fun sigma : ℝ => zetaTwoShiftTotal sigma) =ᶠ[𝓝[>] (1 : ℝ)]
        fun sigma : ℝ => (riemannZeta (2 * (sigma : ℂ))).re := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigmaGt
    change 1 < sigma at hsigmaGt
    exact congrArg Complex.re (ofReal_zetaTwoShiftTotal_eq_riemannZeta hsigmaGt)
  have htotal : Tendsto (fun sigma : ℝ => zetaTwoShiftTotal sigma)
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ)).re) := hre.congr' heq.symm
  exact htotal.inv₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one
    (one_le_re_riemannZeta_ofReal 2 (by norm_num))))

theorem tendsto_norm_mobiusCriticalShiftChannel_sq
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun sigma : ℝ => ‖mobiusCriticalShiftChannel sigma f‖ ^ 2)
      (𝓝[>] (1 : ℝ))
      (𝓝 (((riemannZeta (2 : ℂ)).re)⁻¹ * ‖f‖ ^ 2)) := by
  have h := tendsto_inv_zetaTwoShiftTotal.mul_const (‖f‖ ^ 2)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  rw [mobiusCriticalShiftChannel_eq hsigma,
    norm_mobiusCriticalShiftChannelValue_sq]

def mobiusCriticalShiftChannelFiniteRestriction
    (F : Finset ℕ) (x : InfiniteMobiusShiftChannel) : InfiniteMobiusShiftChannel :=
  ∑ n ∈ F, lp.single 2 n (x n)

theorem norm_mobiusCriticalShiftChannelFiniteRestriction_sq
    (F : Finset ℕ) (x : InfiniteMobiusShiftChannel) :
    ‖mobiusCriticalShiftChannelFiniteRestriction F x‖ ^ 2 =
      ∑ n ∈ F, ‖x n‖ ^ 2 := by
  have h := lp.norm_sum_single (p := (2 : ENNReal))
    (by norm_num) (fun n => x n) F
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  simpa only [mobiusCriticalShiftChannelFiniteRestriction] using h

theorem norm_mobiusCriticalShiftChannel_apply_sq
    {sigma : ℝ} (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) :
    ‖mobiusCriticalShiftChannel sigma f n‖ ^ 2 =
      (zetaTwoShiftTotal sigma)⁻¹ *
        squarefreeMobiusProbability sigma n * ‖f‖ ^ 2 := by
  rw [mobiusCriticalShiftChannel_eq hsigma,
    mobiusCriticalShiftChannelValue_apply, norm_smul, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mobiusCriticalContractionScale_nonneg sigma),
    LinearIsometryEquiv.norm_map, mul_pow, mul_pow,
    norm_infiniteMobiusSignedWeight_sq hsigma,
    mobiusCriticalContractionScale_sq hsigma]
  ring

theorem tendsto_norm_mobiusCriticalShiftChannelFiniteRestriction_sq
    (F : Finset ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto
      (fun sigma : ℝ =>
        ‖mobiusCriticalShiftChannelFiniteRestriction F
          (mobiusCriticalShiftChannel sigma f)‖ ^ 2)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  rw [show (fun sigma : ℝ =>
      ‖mobiusCriticalShiftChannelFiniteRestriction F
        (mobiusCriticalShiftChannel sigma f)‖ ^ 2) =
      fun sigma : ℝ => ∑ n ∈ F, ‖mobiusCriticalShiftChannel sigma f n‖ ^ 2 by
    funext sigma
    exact norm_mobiusCriticalShiftChannelFiniteRestriction_sq F _]
  have hterm : ∀ n ∈ F,
      Tendsto (fun sigma : ℝ => ‖mobiusCriticalShiftChannel sigma f n‖ ^ 2)
        (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    intro n hn
    have hprod := tendsto_inv_zetaTwoShiftTotal.mul
      (tendsto_squarefreeMobiusProbability_zero n)
    have hzero : Tendsto
        (fun sigma : ℝ => (zetaTwoShiftTotal sigma)⁻¹ *
          squarefreeMobiusProbability sigma n * ‖f‖ ^ 2)
        (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      simpa using hprod.mul_const (‖f‖ ^ 2)
    apply hzero.congr'
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    change 1 < sigma at hsigma
    exact (norm_mobiusCriticalShiftChannel_apply_sq hsigma f n).symm
  simpa using tendsto_finsetSum F hterm

/-- Every fixed finite divisor window loses all channel norm at the critical boundary. -/
theorem tendsto_norm_mobiusCriticalShiftChannelFiniteRestriction
    (F : Finset ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto
      (fun sigma : ℝ =>
        ‖mobiusCriticalShiftChannelFiniteRestriction F
          (mobiusCriticalShiftChannel sigma f)‖)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp
    (tendsto_norm_mobiusCriticalShiftChannelFiniteRestriction_sq F f)
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using hsqrt

/-- The complement of every fixed finite window retains the entire nonzero limiting energy. -/
theorem tendsto_mobiusCriticalShiftChannel_tail_energy
    (F : Finset ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto
      (fun sigma : ℝ => ‖mobiusCriticalShiftChannel sigma f‖ ^ 2 -
        ‖mobiusCriticalShiftChannelFiniteRestriction F
          (mobiusCriticalShiftChannel sigma f)‖ ^ 2)
      (𝓝[>] (1 : ℝ))
      (𝓝 (((riemannZeta (2 : ℂ)).re)⁻¹ * ‖f‖ ^ 2)) := by
  simpa using (tendsto_norm_mobiusCriticalShiftChannel_sq f).sub
    (tendsto_norm_mobiusCriticalShiftChannelFiniteRestriction_sq F f)

theorem norm_mobiusCriticalShiftChannel_le
    (sigma : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖mobiusCriticalShiftChannel sigma f‖ ≤ ‖f‖ := by
  by_cases hsigma : 1 < sigma
  · rw [mobiusCriticalShiftChannel_eq hsigma,
      mobiusCriticalShiftChannelValue, norm_smul, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (mobiusCriticalContractionScale_nonneg sigma),
      norm_infiniteMobiusShiftAnalysisValue]
    calc
      mobiusCriticalContractionScale sigma * ‖f‖ ≤ 1 * ‖f‖ :=
        mul_le_mul_of_nonneg_right
          (mobiusCriticalContractionScale_lt_one hsigma).le (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  · simp [mobiusCriticalShiftChannel, hsigma]

theorem tendsto_norm_mobiusCriticalShiftChannel_apply_sq
    (n : ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun sigma : ℝ => ‖mobiusCriticalShiftChannel sigma f n‖ ^ 2)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hprod := tendsto_inv_zetaTwoShiftTotal.mul
    (tendsto_squarefreeMobiusProbability_zero n)
  have hzero : Tendsto
      (fun sigma : ℝ => (zetaTwoShiftTotal sigma)⁻¹ *
        squarefreeMobiusProbability sigma n * ‖f‖ ^ 2)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa using hprod.mul_const (‖f‖ ^ 2)
  apply hzero.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  exact (norm_mobiusCriticalShiftChannel_apply_sq hsigma f n).symm

theorem tendsto_mobiusCriticalShiftChannel_apply_zero
    (n : ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun sigma : ℝ => mobiusCriticalShiftChannel sigma f n)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp
    (tendsto_norm_mobiusCriticalShiftChannel_apply_sq n f)
  have hnorm : Tendsto (fun sigma : ℝ => ‖mobiusCriticalShiftChannel sigma f n‖)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- The critical Möbius channel is weakly null: every fixed continuous linear observation tends to
zero. -/
theorem mobiusCriticalShiftChannel_weakly_tendsto_zero
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ ell : InfiniteMobiusShiftChannel →L[ℂ] ℂ,
      Tendsto (fun sigma : ℝ => ell (mobiusCriticalShiftChannel sigma f))
        (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  intro ell
  let y : InfiniteMobiusShiftChannel :=
    (InnerProductSpace.toDual ℂ InfiniteMobiusShiftChannel).symm ell
  have hyApprox : Tendsto
      (fun N : ℕ => mobiusCriticalShiftChannelFiniteRestriction (Finset.range N) y)
      atTop (𝓝 y) := by
    simpa only [mobiusCriticalShiftChannelFiniteRestriction] using
      (lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) y).tendsto_sum_nat
  have hyTail : Tendsto
      (fun N : ℕ => ‖y - mobiusCriticalShiftChannelFiniteRestriction (Finset.range N) y‖)
      atTop (𝓝 0) := by
    have hyConst : Tendsto (fun _ : ℕ => y) atTop (𝓝 y) := tendsto_const_nhds
    have hsub := hyConst.sub hyApprox
    have hnorm := continuous_norm.continuousAt.tendsto.comp hsub
    simpa [Function.comp_def] using hnorm
  have hinner : Tendsto
      (fun sigma : ℝ => inner ℂ y (mobiusCriticalShiftChannel sigma f))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro epsilon hepsilon
    let R : ℝ := ‖f‖
    let delta : ℝ := epsilon / (2 * (R + 1))
    have hR : 0 ≤ R := norm_nonneg f
    have hdelta : 0 < delta := by
      dsimp only [delta]
      positivity
    have hyEventually := (Metric.tendsto_nhds.1 hyTail) delta hdelta
    obtain ⟨N, hN⟩ := hyEventually.exists
    let yN := mobiusCriticalShiftChannelFiniteRestriction (Finset.range N) y
    have hfinite : Tendsto
        (fun sigma : ℝ => inner ℂ yN (mobiusCriticalShiftChannel sigma f))
        (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have hterm : ∀ n ∈ Finset.range N,
          Tendsto
            (fun sigma : ℝ => inner ℂ (y n)
              (mobiusCriticalShiftChannel sigma f n))
            (𝓝[>] (1 : ℝ)) (𝓝 0) := by
        intro n hn
        simpa only [innerSL_apply_apply, map_zero] using!
          (innerSL ℂ (y n)).continuous.continuousAt.tendsto.comp
            (tendsto_mobiusCriticalShiftChannel_apply_zero n f)
      have hsum := tendsto_finsetSum (Finset.range N) hterm
      simpa only [yN, mobiusCriticalShiftChannelFiniteRestriction,
        sum_inner, lp.inner_single_left, Finset.sum_const_zero] using hsum
    have hfiniteEventually :=
      (Metric.tendsto_nhds.1 hfinite) (epsilon / 2) (by positivity)
    filter_upwards [hfiniteEventually] with sigma hsigma
    have hchannelBound : ‖mobiusCriticalShiftChannel sigma f‖ ≤ R := by
      simpa only [R] using norm_mobiusCriticalShiftChannel_le sigma f
    have htailBound :
        ‖inner ℂ (y - yN) (mobiusCriticalShiftChannel sigma f)‖ < epsilon / 2 := by
      calc
        ‖inner ℂ (y - yN) (mobiusCriticalShiftChannel sigma f)‖
            ≤ ‖y - yN‖ * ‖mobiusCriticalShiftChannel sigma f‖ :=
              norm_inner_le_norm _ _
        _ ≤ ‖y - yN‖ * R :=
          mul_le_mul_of_nonneg_left hchannelBound (norm_nonneg _)
        _ ≤ delta * R := by
          exact mul_le_mul_of_nonneg_right
            (by simpa only [yN, dist_zero_right, Real.norm_eq_abs,
              abs_of_nonneg (norm_nonneg _)] using hN.le) hR
        _ < delta * (R + 1) := by
          exact mul_lt_mul_of_pos_left (by linarith) hdelta
        _ = epsilon / 2 := by
          dsimp only [delta]
          field_simp
    have hdecomp :
        inner ℂ y (mobiusCriticalShiftChannel sigma f) =
          inner ℂ yN (mobiusCriticalShiftChannel sigma f) +
            inner ℂ (y - yN) (mobiusCriticalShiftChannel sigma f) := by
      rw [← inner_add_left]
      congr 1
      abel
    rw [dist_zero_right, hdecomp]
    calc
      ‖inner ℂ yN (mobiusCriticalShiftChannel sigma f) +
          inner ℂ (y - yN) (mobiusCriticalShiftChannel sigma f)‖
          ≤ ‖inner ℂ yN (mobiusCriticalShiftChannel sigma f)‖ +
            ‖inner ℂ (y - yN) (mobiusCriticalShiftChannel sigma f)‖ :=
              norm_add_le _ _
      _ < epsilon / 2 + epsilon / 2 := add_lt_add (by simpa [dist_zero_right] using hsigma) htailBound
      _ = epsilon := by ring
  simpa [y, InnerProductSpace.toDual_symm_apply] using hinner

/-- A nonzero input prevents strong convergence because the total limiting norm is positive. -/
theorem mobiusCriticalShiftChannel_not_strongly_tendsto_zero
    {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ≠ 0) :
    ¬ Tendsto (fun sigma : ℝ => mobiusCriticalShiftChannel sigma f)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  intro hstrong
  have hnorm : Tendsto (fun sigma : ℝ => ‖mobiusCriticalShiftChannel sigma f‖)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa only [norm_zero] using! continuous_norm.continuousAt.tendsto.comp hstrong
  have hsq : Tendsto (fun sigma : ℝ => ‖mobiusCriticalShiftChannel sigma f‖ ^ 2)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa using hnorm.pow 2
  have hzero := tendsto_nhds_unique
    (tendsto_norm_mobiusCriticalShiftChannel_sq f) hsq
  have hzetaPos : 0 < (riemannZeta (2 : ℂ)).re :=
    lt_of_lt_of_le zero_lt_one (one_le_re_riemannZeta_ofReal 2 (by norm_num))
  have htargetPos :
      0 < ((riemannZeta (2 : ℂ)).re)⁻¹ * ‖f‖ ^ 2 :=
    mul_pos (inv_pos.mpr hzetaPos) (sq_pos_of_pos (norm_pos_iff.mpr hf))
  rw [hzero] at htargetPos
  exact lt_irrefl 0 htargetPos

theorem IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weaklyNullSequence
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (K : E →L[ℂ] F) (hK : IsCompactOperator K) (x : ℕ → E) (R : ℝ)
    (hxBound : ∀ n, ‖x n‖ ≤ R)
    (hxWeak : ∀ ell : E →L[ℂ] ℂ,
      Tendsto (fun n => ell (x n)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖K (x n)‖) atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    exact Eventually.of_forall fun n => hb.trans_le (norm_nonneg (K (x n)))
  · intro b hb
    by_contra hsmall
    have hfreq : ∃ᶠ n in atTop, b ≤ ‖K (x n)‖ :=
      (not_eventually.mp hsmall).mono fun _ hn => le_of_not_gt hn
    obtain ⟨phi, hphi, hphiLower⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨C, hCcompact, hKC⟩ := hK.image_closedBall_subset_compact R
    have hxMem : ∀ n, K (x (phi n)) ∈ C := fun n =>
      hKC ⟨x (phi n), by simpa using hxBound (phi n), rfl⟩
    obtain ⟨y, hyC, psi, hpsi, hpsiY⟩ :=
      hCcompact.tendsto_subseq (x := fun n => K (x (phi n))) hxMem
    have hyZero : y = 0 := by
      have hweakSub :
          Tendsto (fun n => ((innerSL ℂ y) ∘L K) (x (phi (psi n))))
            atTop (𝓝 0) :=
        (hxWeak ((innerSL ℂ y) ∘L K)).comp
          (hphi.tendsto_atTop.comp hpsi.tendsto_atTop)
      have hstrongInner :
          Tendsto (fun n => (innerSL ℂ y) (K (x (phi (psi n)))))
            atTop (𝓝 ((innerSL ℂ y) y)) := by
        simpa [Function.comp_def] using
          (innerSL ℂ y).continuous.continuousAt.tendsto.comp hpsiY
      have hinner : (innerSL ℂ y) y = 0 := by
        apply tendsto_nhds_unique hstrongInner
        simpa using hweakSub
      change inner ℂ y y = 0 at hinner
      exact inner_self_eq_zero.mp hinner
    rw [hyZero] at hpsiY
    rw [NormedAddGroup.tendsto_nhds_zero] at hpsiY
    obtain ⟨n, hn⟩ := (hpsiY b hb).exists
    exact (not_lt_of_ge (hphiLower (psi n)))
      (by simpa [Function.comp_def] using hn)

/-- Every fixed compact synthesis kills the critical Möbius mass that escapes through the divisor
index. -/
theorem IsCompactOperator.tendsto_norm_apply_mobiusCriticalShiftChannel_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : InfiniteMobiusShiftChannel →L[ℂ] H) (hK : IsCompactOperator K)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun sigma : ℝ => ‖K (mobiusCriticalShiftChannel sigma f)‖)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  rw [tendsto_iff_seq_tendsto]
  intro sigma hsigma
  apply IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weaklyNullSequence
    K hK (fun n => mobiusCriticalShiftChannel (sigma n) f) ‖f‖
  · intro n
    exact norm_mobiusCriticalShiftChannel_le (sigma n) f
  · intro ell
    simpa [Function.comp_def] using
      (mobiusCriticalShiftChannel_weakly_tendsto_zero f ell).comp hsigma

end RHTower
