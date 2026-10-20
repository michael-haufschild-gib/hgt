import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalRationalDilationLaw
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPolarCutoff
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeKernelNegativeDefinite
import GaloisForLFunctions.BiScaleUncertainty.LogarithmicIncrementEnergy
import GaloisForLFunctions.BiScaleUncertainty.IntegratedOriginCollarLeverage

/-!
# The complete critical form of translated factorial patterns

The complete energy of the translated critical source is written in Gamma–Lévy form:
the Lévy jump energy `∫_{x>0} (ac(0) - ac(x)) ω(x) dx` plus the Gamma constant `Ω(0) ac(0)`,
the polar channel `2 ĝ(-i/2) ĝ(i/2)` and the subtracted prime channel. As the scale grows:

* both polar readouts are `O(1/n)` (the upper one by integration by parts against the bounded
  lattice primitive), so the polar channel vanishes;
* the mass `ac(0)` converges to the positive diagonal dilation limit, and the prime channel to
  `P∞`, which is uniformly negative definite;
* by the rational dilation law the autocorrelation vanishes at every shift with irrational
  exponential, hence almost everywhere, and Fatou's lemma with `ω(x) ≥ e^{-1/2}/x` forces the
  Lévy energy to `+∞`.

Hence the complete critical energy of every nonzero translated pattern tends to `+∞`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- The upper polar readout `∫_{v>1} v⁻² F(v) dv` of a critical source. -/
def criticalFactorialPolarReadout (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re

/-- Integration by parts against the bounded primitive bounds the upper polar readout. -/
theorem abs_criticalFactorialPolarReadout_le (S : Finset ℕ) (b : ℕ → ℝ) :
    |criticalFactorialPolarReadout S b| ≤ 24 * ∑ n ∈ S, |b n| / ((n+1 : ℕ) : ℝ) := by
  set G := criticalFactorialPhasePrimitive S b
  set P := 12 * ∑ n ∈ S, |b n| / ((n+1 : ℕ) : ℝ)
  have hGb (v : ℝ) : |G v| ≤ P := criticalFactorialPhasePrimitive_bound S b v
  have hP : 0 ≤ P := (abs_nonneg _).trans (hGb 0)
  set F : ℝ → ℝ := fun v => (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re
  have hFc : Continuous F := Complex.continuous_re.comp (continuous_factorialPhaseCombination _ _)
  have hFb (v : ℝ) : |F v| ≤ 2 * ∑ n ∈ S, |b n| := by
    have h := (Complex.abs_re_le_norm _).trans (norm_factorialPhaseCombination_le S (fun n => (b n : ℂ)) v)
    simpa [Complex.norm_real] using h
  have hu (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) : HasDerivAt (fun v : ℝ => v ^ (-2 : ℝ))
      (-2 * x ^ (-3 : ℝ)) x := by
    have hx0 : 0 < x := zero_lt_one.trans hx
    have := Real.hasDerivAt_rpow_const (p := (-2 : ℝ)) (Or.inl hx0.ne')
    convert this using 1; norm_num
  have hv (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) : HasDerivAt G (F x) x :=
    criticalFactorialPhasePrimitive_hasDerivAt S b (zero_lt_one.trans hx)
  have hw2 : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hw3 : IntegrableOn (fun v : ℝ => v ^ (-3 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hGc : ContinuousOn G (Ioi 0) := fun x hx =>
    (criticalFactorialPhasePrimitive_hasDerivAt S b hx).continuousAt.continuousWithinAt
  have hint1 : IntegrableOn ((fun v : ℝ => v ^ (-2 : ℝ)) * F) (Ioi 1) :=
    hw2.mul_bdd hFc.aestronglyMeasurable (Eventually.of_forall fun v => by
      simpa only [Real.norm_eq_abs] using hFb v)
  have hint2 : IntegrableOn ((fun v : ℝ => -2 * v ^ (-3 : ℝ)) * G) (Ioi 1) :=
    (hw3.const_mul (-2)).mul_bdd ((hGc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) (Eventually.of_forall fun v => by simpa only [Real.norm_eq_abs] using hGb v)
  have hlim1 : Tendsto ((fun v : ℝ => v ^ (-2 : ℝ)) * G) (𝓝[>] 1) (𝓝 (G 1)) := by
    have h1 : ContinuousAt (fun v : ℝ => v ^ (-2 : ℝ)) 1 :=
      Real.continuousAt_rpow_const _ _ (Or.inl one_ne_zero)
    have h2 : ContinuousAt G 1 := (criticalFactorialPhasePrimitive_hasDerivAt S b one_pos).continuousAt
    have := (h1.mul h2).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    simpa using this
  have hlim2 : Tendsto ((fun v : ℝ => v ^ (-2 : ℝ)) * G) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).mul_const P |>.trans
      (by simp))
    filter_upwards [eventually_gt_atTop 0] with v hv
    simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hv.le _)]
    exact mul_le_mul_of_nonneg_left (hGb v) (Real.rpow_nonneg hv.le _)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hint1 hint2 hlim1 hlim2
  unfold criticalFactorialPolarReadout
  rw [show 24 * ∑ n ∈ S, |b n| / ((n+1 : ℕ) : ℝ) = 2 * P by simp only [P]; ring]
  change |∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * F v| ≤ 2 * P
  rw [hibp]
  have hb2 : |∫ v in Ioi (1 : ℝ), -2 * v ^ (-3 : ℝ) * G v| ≤ P := by
    have hmass : (∫ v in Ioi (1 : ℝ), v ^ (-3 : ℝ)) = 1 / 2 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) zero_lt_one]; norm_num
    calc |∫ v in Ioi (1 : ℝ), -2 * v ^ (-3 : ℝ) * G v| ≤ ∫ v in Ioi (1 : ℝ), 2 * P * v ^ (-3 : ℝ) := by
          rw [← Real.norm_eq_abs]
          refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on hint2.norm
            (hw3.const_mul _) measurableSet_Ioi fun v hv => ?_)
          have hv0 : 0 ≤ v ^ (-3 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hv.le) _
          simp only [norm_mul, Real.norm_eq_abs, abs_neg, abs_two, abs_of_nonneg hv0]
          nlinarith [hGb v]
      _ = P := by rw [integral_const_mul, hmass]; ring
  calc |0 - G 1 - ∫ v in Ioi (1 : ℝ), -2 * v ^ (-3 : ℝ) * G v| ≤
      |G 1| + |∫ v in Ioi (1 : ℝ), -2 * v ^ (-3 : ℝ) * G v| := by
        rw [zero_sub, ← neg_add', abs_neg]; exact abs_add_le _ _
    _ ≤ 2 * P := by linarith [hGb 1]

/-- The critical source of a finite pattern translated to scale `n`. -/
def criticalTranslatedSource (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ → ℝ :=
  criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n))

/-- Autocorrelation of the translated critical source at shift `x`. -/
def criticalTranslatedAutocorrelation (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, criticalTranslatedSource S b n y * criticalTranslatedSource S b n (y - x)

/-- Lévy jump energy of the translated critical source, `∫_{x>0} (ac(0) - ac(x)) ω(x) dx`,
as an extended nonnegative quantity. -/
def criticalTranslatedLevyEnergy (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in Ioi 0, ENNReal.ofReal ((criticalTranslatedAutocorrelation S b n 0 -
    criticalTranslatedAutocorrelation S b n x) * BiScaleUncertainty.archLevySinhWeight x)

/-- **Critical mass floor.** The limiting physical mass of a translated pattern dominates
`Σ b_j² / (12π⁴)`: the diagonal dilation sum is bounded below by its first harmonic term. -/
theorem factorialCriticalDilationLimit_one_ge (S : Finset ℕ) (b : ℕ → ℝ) :
    (∑ j ∈ S, b j ^ 2) / (12 * Real.pi ^ 4) ≤ factorialCriticalDilationLimit S b 1 := by
  set f : ℕ × ℕ → ℝ := fun p => if (p.1 : ℝ) = 1 * p.2 then dyadicHarmonicWeight p.1 *
    dyadicHarmonicWeight p.2 * factorialCriticalPatternHarmonicMass S b p.1 else 0
  have hJle (m : ℕ) : factorialCriticalPatternHarmonicMass S b m ≤ 4 * ∑ i ∈ S, b i ^ 2 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : factorialCriticalPatternHarmonicMass S b 0 = 0 := by
        simp [factorialCriticalPatternHarmonicMass]
      rw [this]; positivity
    · exact factorialCriticalPatternHarmonicMass_le S b hm
  have hfs : Summable f := by
    refine ((summable_abs_dyadicHarmonicWeight.mul_of_nonneg summable_abs_dyadicHarmonicWeight
      (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)).mul_right (4 * ∑ i ∈ S, b i ^ 2)).of_norm_bounded
      fun p => ?_
    simp only [f]
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (factorialCriticalPatternHarmonicMass_nonneg S b _)]
      exact mul_le_mul_of_nonneg_left (hJle _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · simp only [norm_zero]; positivity
  have hf0 (p : ℕ × ℕ) : 0 ≤ f p := by
    simp only [f]
    split_ifs with hp
    · have : p.1 = p.2 := by exact_mod_cast (by simpa using hp)
      rw [this, ← sq]
      exact mul_nonneg (sq_nonneg _) (factorialCriticalPatternHarmonicMass_nonneg S b _)
    · exact le_rfl
  have h11 : f (1, 1) = factorialCriticalPatternHarmonicMass S b 1 := by
    simp [f, dyadicHarmonicWeight, dyadicHarmonicChi]
  have hJ1 := factorialCriticalPatternHarmonicMass_ge S b (m := 1) one_pos
  have hle := hfs.le_tsum (1, 1) (fun q _ => hf0 q)
  rw [h11] at hle
  unfold factorialCriticalDilationLimit
  have hpi : 0 < Real.pi ^ 4 := by positivity
  calc (∑ j ∈ S, b j ^ 2) / (12 * Real.pi ^ 4) = 4 / Real.pi ^ 4 * ((∑ j ∈ S, b j ^ 2) / 48) := by
        field_simp; ring
    _ ≤ 4 / Real.pi ^ 4 * ∑' p : ℕ × ℕ, f p := by gcongr; linarith

/-- The physical mass of a nonzero translated pattern has a strictly positive critical limit. -/
theorem factorialCriticalDilationLimit_one_pos {S : Finset ℕ} {b : ℕ → ℝ}
    (h : ∃ j ∈ S, b j ≠ 0) : 0 < factorialCriticalDilationLimit S b 1 := by
  obtain ⟨j, hj, hb⟩ := h
  have hE : 0 < ∑ i ∈ S, b i ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  exact lt_of_lt_of_le (by positivity) (factorialCriticalDilationLimit_one_ge S b)

/-- Outside a countable set every shift has irrational exponential. -/
theorem ae_irrational_exp : ∀ᵐ x : ℝ, Irrational (Real.exp x) := by
  have hc : {x : ℝ | ¬ Irrational (Real.exp x)} ⊆ Set.range fun q : ℚ => Real.log q := by
    intro x hx
    simp only [Set.mem_setOf_eq, Irrational, not_not, Set.mem_range] at hx
    obtain ⟨q, hq⟩ := hx
    exact ⟨q, show Real.log q = x by rw [hq, Real.log_exp]⟩
  have h0 := ((Set.countable_range _).mono hc).measure_zero volume
  exact measure_eq_zero_iff_ae_notMem.mp h0 |>.mono fun x hx => by simpa using hx

private theorem measurable_criticalTranslatedSource (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) :
    Measurable (criticalTranslatedSource S b n) := by
  unfold criticalTranslatedSource criticalFactorialSource
  refine Measurable.indicator ?_ measurableSet_Iic
  have := continuous_factorialPhaseCombination (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ))
  exact (by fun_prop : Continuous fun x : ℝ => Real.exp (x / 2) *
    (factorialPhaseCombination (S.image (fun j => n+j)) (fun q => (b (q-n) : ℂ)) (Real.exp (-x))).re).measurable

private theorem measurable_criticalTranslatedAutocorrelation (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) :
    Measurable (criticalTranslatedAutocorrelation S b n) := by
  have hs := measurable_criticalTranslatedSource S b n
  have hm : StronglyMeasurable fun p : ℝ × ℝ =>
      criticalTranslatedSource S b n p.2 * criticalTranslatedSource S b n (p.2 - p.1) :=
    ((hs.comp measurable_snd).mul (hs.comp (measurable_snd.sub measurable_fst))).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := volume)).measurable

/-- The Lévy weight `ω(x) = e^{x/2}/sinh x` has a non-integrable `1/x` singularity at the
origin: every positive multiple has infinite lower integral over `x > 0`. -/
theorem lintegral_ofReal_mul_archLevySinhWeight_eq_top {c : ℝ} (hc : 0 < c) :
    ∫⁻ x in Ioi 0, ENNReal.ofReal (c * BiScaleUncertainty.archLevySinhWeight x) = ⊤ := by
  have hinv : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal x⁻¹ = ⊤ := by
    by_contra hne
    have hfin : HasFiniteIntegral (fun x : ℝ => x⁻¹) (volume.restrict (Ioc 0 1)) :=
      (hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem measurableSet_Ioc
        fun x hx => (inv_pos.mpr hx.1).le)).mpr (lt_top_iff_ne_top.mpr hne)
    have hint : IntegrableOn (fun x : ℝ => x⁻¹) (Ioc 0 1) :=
      ⟨measurable_inv.aestronglyMeasurable, hfin⟩
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hint
    rw [intervalIntegrable_inv_iff] at this
    rcases this with h01 | h01
    · norm_num at h01
    · exact h01 (by simp)
  have hlow : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (c * Real.exp (-(1 / 2 : ℝ))) * ENNReal.ofReal x⁻¹ ≤
      ∫⁻ x in Ioi 0, ENNReal.ofReal (c * BiScaleUncertainty.archLevySinhWeight x) := by
    calc ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (c * Real.exp (-(1 / 2 : ℝ))) * ENNReal.ofReal x⁻¹ ≤
        ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (c * BiScaleUncertainty.archLevySinhWeight x) := by
          refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have := BiScaleUncertainty.exp_neg_half_div_le_archLevySinhWeight hx.1 hx.2
          rw [mul_assoc, ← div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left this hc.le
      _ ≤ _ := lintegral_mono_set Ioc_subset_Ioi_self
  rw [lintegral_const_mul _ measurable_inv.ennreal_ofReal, hinv,
    ENNReal.mul_top (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)] at hlow
  exact top_le_iff.mp hlow

/-- **Archimedean divergence at the critical scale.** For every nonzero finite pattern, the
Lévy jump energy of the translated critical source tends to `+∞`: the mass converges to a
positive limit while the autocorrelation decorrelates at almost every shift. -/
theorem tendsto_criticalTranslatedLevyEnergy_top {S : Finset ℕ} {b : ℕ → ℝ}
    (h : ∃ j ∈ S, b j ≠ 0) :
    Tendsto (criticalTranslatedLevyEnergy S b) atTop (𝓝 ⊤) := by
  set μ := factorialCriticalDilationLimit S b 1 with hμ
  have hμpos : 0 < μ := factorialCriticalDilationLimit_one_pos h
  have hac (x : ℝ) (hx : 0 ≤ x) : Tendsto (fun n => criticalTranslatedAutocorrelation S b n x) atTop
      (𝓝 (Real.exp (-(x / 2)) * factorialCriticalDilationLimit S b (Real.exp x))) :=
    criticalFactorialSource_translated_autocorrelation_tendsto S b hx
  have hac0 : Tendsto (fun n => criticalTranslatedAutocorrelation S b n 0) atTop (𝓝 μ) := by
    simpa using hac 0 le_rfl
  set ω := BiScaleUncertainty.archLevySinhWeight
  set f : ℕ → ℝ → ℝ≥0∞ := fun n x => ENNReal.ofReal ((criticalTranslatedAutocorrelation S b n 0 -
    criticalTranslatedAutocorrelation S b n x) * ω x)
  have hmeas (n : ℕ) : AEMeasurable (f n) (volume.restrict (Ioi 0)) := by
    have := measurable_criticalTranslatedAutocorrelation S b n
    exact (ENNReal.measurable_ofReal.comp ((measurable_const.sub this).mul
      BiScaleUncertainty.measurable_archLevySinhWeight)).aemeasurable
  have hlim : ∀ᵐ x ∂(volume.restrict (Ioi 0)), Tendsto (fun n => f n x) atTop
      (𝓝 (ENNReal.ofReal (μ * ω x))) := by
    filter_upwards [ae_restrict_of_ae ae_irrational_exp, ae_restrict_mem measurableSet_Ioi] with x hirr hx
    have hx0 := hac x (le_of_lt hx)
    rw [factorialCriticalDilationLimit_eq_zero_of_irrational S b hirr, mul_zero] at hx0
    have := ((hac0.sub hx0).mul_const (ω x))
    rw [sub_zero] at this
    exact (ENNReal.continuous_ofReal.tendsto _).comp this
  have hfatou := lintegral_liminf_le' (μ := volume.restrict (Ioi 0)) (u := atTop) hmeas
  have hliminf : ∫⁻ x in Ioi 0, Filter.liminf (fun n => f n x) atTop =
      ∫⁻ x in Ioi 0, ENNReal.ofReal (μ * ω x) :=
    lintegral_congr_ae (hlim.mono fun x hx => hx.liminf_eq)
  have htop : ∫⁻ x in Ioi 0, ENNReal.ofReal (μ * ω x) = ⊤ :=
    lintegral_ofReal_mul_archLevySinhWeight_eq_top hμpos
  rw [hliminf, htop] at hfatou
  apply ENNReal.tendsto_nhds_top
  intro k
  exact Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le (ENNReal.natCast_lt_top k) hfatou)

private theorem translated_inverse_mass_le (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) :
    ∑ q ∈ S.image (fun j => n+j), |b (q-n)| / ((q+1 : ℕ) : ℝ) ≤
      (∑ j ∈ S, |b j|) / ((n+1 : ℕ) : ℝ) := by
  classical
  rw [Finset.sum_image (fun i _ j _ h => Nat.add_left_cancel h), Finset.sum_div]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [Nat.add_sub_cancel_left]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])

/-- The polar channel `ĝ(-i/2) ĝ(i/2)` of the translated critical source. -/
def criticalTranslatedPolarProduct (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  criticalFactorialPolarReadout (S.image (fun j => n+j)) (fun q => b (q-n)) *
    criticalFactorialPolarEndpoint (S.image (fun j => n+j)) (fun q => b (q-n))

/-- Both polar readouts are `O(1/n)`: the polar channel is bounded by `(24 Σ|b_j|)²/(n+1)`. -/
theorem abs_criticalTranslatedPolarProduct_le (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) :
    |criticalTranslatedPolarProduct S b n| ≤ (24 * ∑ j ∈ S, |b j|) ^ 2 / ((n+1 : ℕ) : ℝ) := by
  set A := ∑ j ∈ S, |b j|
  have hA : 0 ≤ A := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h1 := (abs_criticalFactorialPolarReadout_le (S.image (fun j => n+j)) (fun q => b (q-n))).trans
    (mul_le_mul_of_nonneg_left (translated_inverse_mass_le S b n) (by norm_num))
  have h2 := (criticalFactorialPolarEndpoint_bound (S.image (fun j => n+j)) (fun q => b (q-n))).trans
    (mul_le_mul_of_nonneg_left (translated_inverse_mass_le S b n) (by norm_num))
  have hn1 : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hq : (24 * (A / ((n+1 : ℕ) : ℝ))) ≤ 24 * A := by
    gcongr; exact div_le_self hA hn1
  unfold criticalTranslatedPolarProduct
  rw [abs_mul]
  calc _ ≤ (24 * (A / ((n+1 : ℕ) : ℝ))) * (24 * A) :=
        mul_le_mul h1 (h2.trans hq) (abs_nonneg _) (by positivity)
    _ = (24 * A) ^ 2 / ((n+1 : ℕ) : ℝ) := by ring

/-- The polar channel vanishes in the translated limit. -/
theorem tendsto_criticalTranslatedPolarProduct (S : Finset ℕ) (b : ℕ → ℝ) :
    Tendsto (criticalTranslatedPolarProduct S b) atTop (𝓝 0) := by
  set A := ∑ j ∈ S, |b j|
  have hlim : Tendsto (fun n : ℕ => (24 * A) ^ 2 / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((24 * A) ^ 2)
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    push_cast; ring
  exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact abs_criticalTranslatedPolarProduct_le S b n) hlim

open _root_.Zeta23 in
/-- Gamma constant, polar and prime channels of the translated critical source. -/
def criticalTranslatedArithmeticChannels (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  EF.gammaBracket 0 * criticalTranslatedAutocorrelation S b n 0 +
    2 * criticalTranslatedPolarProduct S b n - 2 * factorialCriticalTranslatedPrimeEnergy S b n

open _root_.Zeta23 in
/-- **Arithmetic channels of the complete critical form.** The Gamma constant term, the polar
channel and the complete prime channel converge together; the prime channel enters with the
uniformly positive weight `-2 P∞ ≥ (8/(7000π⁴)) Σ b_j²`. -/
theorem tendsto_criticalTranslatedArithmeticChannels (S : Finset ℕ) (b : ℕ → ℝ) :
    Tendsto (criticalTranslatedArithmeticChannels S b) atTop
      (𝓝 (EF.gammaBracket 0 * factorialCriticalDilationLimit S b 1 -
        2 * factorialCriticalTranslatedPrimeLimit S b)) := by
  have h0 : Tendsto (fun n => criticalTranslatedAutocorrelation S b n 0) atTop
      (𝓝 (Real.exp (-((0 : ℝ) / 2)) * factorialCriticalDilationLimit S b (Real.exp 0))) :=
    criticalFactorialSource_translated_autocorrelation_tendsto S b le_rfl
  have hac0 : Tendsto (fun n => criticalTranslatedAutocorrelation S b n 0) atTop
      (𝓝 (factorialCriticalDilationLimit S b 1)) := by simpa using h0
  have h := ((hac0.const_mul (EF.gammaBracket 0)).add
    ((tendsto_criticalTranslatedPolarProduct S b).const_mul 2)).sub
    ((factorialCriticalTranslatedPrimeEnergy_tendsto S b).const_mul 2)
  rw [mul_zero, add_zero] at h
  exact h

/-- The prime part of the limiting arithmetic channels is uniformly coercive. -/
theorem neg_two_factorialCriticalTranslatedPrimeLimit_ge (S : Finset ℕ) (b : ℕ → ℝ) :
    (8 / (7000 * Real.pi ^ 4)) * ∑ j ∈ S, b j ^ 2 ≤ -2 * factorialCriticalTranslatedPrimeLimit S b := by
  have := factorialCriticalTranslatedPrimeLimit_le_neg_energy S b
  have e : -2 * (-(4 / (7000 * Real.pi ^ 4)) * ∑ j ∈ S, b j ^ 2) =
      (8 / (7000 * Real.pi ^ 4)) * ∑ j ∈ S, b j ^ 2 := by ring
  linarith

/-- The complete critical energy of the translated source in Gamma–Lévy form:
Lévy jump energy plus Gamma constant, polar and prime channels. -/
def criticalTranslatedCompleteEnergy (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) : EReal :=
  (criticalTranslatedLevyEnergy S b n : EReal) + (criticalTranslatedArithmeticChannels S b n : EReal)

open _root_.Zeta23 in
/-- **Eventual positivity of the complete critical form.** For every nonzero finite pattern the
complete critical energy of its translates tends to `+∞`. -/
theorem tendsto_criticalTranslatedCompleteEnergy_top {S : Finset ℕ} {b : ℕ → ℝ}
    (h : ∃ j ∈ S, b j ≠ 0) :
    Tendsto (criticalTranslatedCompleteEnergy S b) atTop (𝓝 ⊤) := by
  rw [EReal.tendsto_nhds_top_iff_real]
  intro M
  set L := EF.gammaBracket 0 * factorialCriticalDilationLimit S b 1 -
    2 * factorialCriticalTranslatedPrimeLimit S b
  have hA := (tendsto_criticalTranslatedArithmeticChannels S b).eventually (eventually_gt_nhds
    (show L - 1 < L by linarith))
  have hB := (ENNReal.tendsto_nhds_top_iff_nnreal.mp (tendsto_criticalTranslatedLevyEnergy_top h))
    (Real.toNNReal (M - L + 1))
  filter_upwards [hA, hB] with n hn hl
  unfold criticalTranslatedCompleteEnergy
  set lev := criticalTranslatedLevyEnergy S b n
  rcases eq_or_ne lev ⊤ with htop | hfin
  · rw [htop]; simp
  · have hlev : (M - L + 1 : ℝ) < lev.toReal := by
      have h1 : ((Real.toNNReal (M - L + 1) : ℝ≥0∞)) < lev := hl
      have h2 := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hfin).mpr h1
      simp only [ENNReal.coe_toReal, Real.coe_toNNReal'] at h2
      exact lt_of_le_of_lt (le_max_left _ _) h2
    have hc : (lev : EReal) = ((lev.toReal : ℝ) : EReal) := by
      rw [← EReal.coe_ennreal_toReal hfin]
    rw [hc, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    linarith

end GaloisForLFunctions.ArithmeticPositivityTheory
