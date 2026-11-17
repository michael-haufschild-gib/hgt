import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroSeriesIsTheStateLeftOfTheWallAndThePrimeSideBeyond
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheBeyondTheWallPrimeBalanceExcludesTheState

/-!
# The profile beyond the wall in prime form

For a profile `F` of the energy domain the profile beyond the wall `F⁺` (`beyondWallProfile`) is defined
as an `L²` class through damped Hardy data. Pointwise, for almost every `x > 0`,

  `−a F⁺(x) = J⁺(x) + Σ_n Λ(n) n^{−½} F(x − log n) − L F(½) e^{−x/2} − L F(−½) e^{x/2}`

(`beyondWallProfile_primeForm`), where `J⁺` is the archimedean Hankel profile and the series is absolutely
convergent almost everywhere; only `n > eˣ` contribute, since `F` vanishes on `u ≥ 0`. The polar term is
the continuum main term of the prime number theorem, `L F(−½) e^{x/2} = ∫_{y>x} F(x − y) e^{y/2} dy`, so
the prime part of `−a F⁺` is the remainder of the prime number theorem averaged against `F`
(`beyondWallProfile_pntForm`):

  `−a F⁺(x) = J⁺(x) − L F(½) e^{−x/2} + (Σ_n Λ(n) n^{−½} F(x − log n) − ∫_{y>x} F(x − y) e^{y/2} dy)`.

The general step is `coeFn_tsum_ae_eq`: an `L²` series whose terms are square-summable in norm is almost
everywhere its pointwise sum (`ae_summable_of_summable_eLpNorm`).
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23 Complex
open scoped ENNReal

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Series in `L²` and pointwise sums -/

theorem coeFn_sum_range_ae {μ : Measure ℝ} (f : ℕ → Lp ℂ 2 μ) (N : ℕ) :
    ∀ᵐ x ∂μ, (↑(∑ n ∈ Finset.range N, f n) : ℝ → ℂ) x = ∑ n ∈ Finset.range N, (f n : ℝ → ℂ) x := by
  induction N with
  | zero =>
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    simpa using hx
  | succ N ih =>
    filter_upwards [ih, Lp.coeFn_add (∑ n ∈ Finset.range N, f n) (f N)] with x h1 h2
    rw [Finset.sum_range_succ, h2, Pi.add_apply, h1, Finset.sum_range_succ]

/-- **An `L²` series is almost everywhere its pointwise sum**, where the pointwise series converges. -/
theorem coeFn_tsum_ae_eq {μ : Measure ℝ} {f : ℕ → Lp ℂ 2 μ} (hf : Summable f) {g : ℕ → ℝ → ℂ}
    (hfg : ∀ n, (f n : ℝ → ℂ) =ᵐ[μ] g n) (hs : ∀ᵐ x ∂μ, Summable fun n => g n x) :
    (↑(∑' n, f n) : ℝ → ℂ) =ᵐ[μ] fun x => ∑' n, g n x := by
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (𝓝 (∑' n, f n)) :=
    hf.hasSum.tendsto_sum_nat
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hpart : ∀ᵐ x ∂μ, ∀ N, (↑(∑ n ∈ Finset.range N, f n) : ℝ → ℂ) x =
      ∑ n ∈ Finset.range N, g n x := by
    rw [ae_all_iff]
    intro N
    filter_upwards [coeFn_sum_range_ae f N, ae_all_iff.2 hfg] with x h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun n _ => h2 n
  filter_upwards [hae, hpart, hs] with x h1 h2 h3
  have h4 : Tendsto (fun i => ∑ n ∈ Finset.range (ns i), g n x) atTop (𝓝 (∑' n, g n x)) :=
    h3.hasSum.tendsto_sum_nat.comp hns.tendsto_atTop
  simp only [h2] at h1
  exact tendsto_nhds_unique h1 h4

/-- **Norm-summable square-integrable terms are almost everywhere summable** on `(0, ∞)`: on each
`(0, X)` the `L¹` norms are at most `√X` times the `L²` norms. -/
theorem ae_summable_of_summable_eLpNorm {g : ℕ → ℝ → ℂ}
    (hg : ∀ n, MemLp (g n) 2 (volume.restrict (Ioi (0 : ℝ))))
    (hsum : Summable fun n => (eLpNorm (g n) 2 (volume.restrict (Ioi (0 : ℝ)))).toReal) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), Summable fun n => g n x := by
  have hX : ∀ X : ℕ, ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) X)), Summable fun n => g n x := by
    intro X
    set ν : Measure ℝ := volume.restrict (Ioo (0 : ℝ) X)
    have hν : ν ≤ volume.restrict (Ioi 0) := Measure.restrict_mono Ioo_subset_Ioi_self le_rfl
    have hgν : ∀ n, AEStronglyMeasurable (g n) ν :=
      fun n => (hg n).aestronglyMeasurable.mono_measure hν
    have hνuniv : ν univ = ENNReal.ofReal X := by
      simp only [ν, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
    have hbound : ∀ n, ∫⁻ x, ‖g n x‖ₑ ∂ν ≤
        ENNReal.ofReal (eLpNorm (g n) 2 (volume.restrict (Ioi 0))).toReal *
          ENNReal.ofReal X ^ (1 / 2 : ℝ) := by
      intro n
      have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) (hgν n)
      rw [eLpNorm_one_eq_lintegral_enorm, hνuniv] at h1
      have h2 : eLpNorm (g n) 2 ν ≤ eLpNorm (g n) 2 (volume.restrict (Ioi 0)) :=
        eLpNorm_mono_measure _ hν
      rw [ENNReal.ofReal_toReal (hg n).2.ne]
      refine h1.trans ?_
      norm_num
      exact mul_le_mul' h2 le_rfl
    have hfin : ∫⁻ x, ∑' n, ‖g n x‖ₑ ∂ν ≠ ⊤ := by
      rw [lintegral_tsum fun n => (hgν n).enorm]
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
      rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg
        (f := fun n => (eLpNorm (g n) 2 (volume.restrict (Ioi (0 : ℝ)))).toReal)
        (fun n => ENNReal.toReal_nonneg) hsum]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) ENNReal.ofReal_ne_top)
    filter_upwards [ae_lt_top' (AEMeasurable.tsum fun n => (hgν n).enorm) hfin] with x hx
    refine Summable.of_norm ?_
    have hx' : (∑' n, ((‖g n x‖₊ : NNReal) : ℝ≥0∞)) ≠ ⊤ := by
      simpa only [enorm] using hx.ne
    exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hx')
  have hall : ∀ᵐ x, ∀ X : ℕ, x ∈ Ioo (0 : ℝ) X → Summable fun n => g n x := by
    rw [ae_all_iff]
    intro X
    exact (ae_restrict_iff' measurableSet_Ioo).1 (hX X)
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hall] with x hx hx0
  obtain ⟨X, hX⟩ := exists_nat_gt x
  exact hx X ⟨hx0, hX⟩

/-! ### The prime form -/

/-- The prime atom `Λ(n)/√n` (`0` for `n < 2`). -/
def primeAtom (n : ℕ) : ℝ := if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0

/-- The damped prime datum at ratio `c = 1` is `e^{−x} Λ(n) n^{−½} F(x − log n)`. -/
theorem primeHeadDatumTerm_one (F : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    primeHeadDatumTerm F 1 n x =
      (Real.exp (-x) : ℂ) * ((primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)) := by
  unfold primeHeadDatumTerm dampedNegativeProfile
  change ((primeAtom n * Real.exp (-1 * Real.log n) : ℝ) : ℂ) *
      ((Real.exp (-1 * (x - Real.log n)) : ℂ) * (F (x - Real.log n) : ℂ)) = _
  have he : Real.exp (-1 * Real.log n) * Real.exp (-1 * (x - Real.log n)) = Real.exp (-x) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← he]
  simp only [Complex.ofReal_mul]
  ring

/-- **The profile beyond the wall in prime form.** For almost every `x > 0` the prime series converges
absolutely and `−a F⁺(x) = J⁺(x) + Σ_n Λ(n) n^{−½} F(x − log n) − L F(½) e^{−x/2} − L F(−½) e^{x/2}`. -/
theorem beyondWallProfile_primeForm {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      Summable (fun n : ℕ => (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)) ∧
      -(criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hF x =
        levyHeadProfile F x + ∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ) -
          negativeHalfLineLaplace (cx F) (1 / 2) * (Real.exp (-(x / 2)) : ℂ) -
          negativeHalfLineLaplace (cx F) (-(1 / 2)) * (Real.exp (x / 2) : ℂ) := by
  have hc : (1 : ℝ) ≤ 4 := by norm_num
  have hc0 : (1 / 2 : ℝ) < 1 := by norm_num
  have h0 : (0 : ℝ) ≤ 1 := by norm_num
  have hA0 : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hW).ne'
  set A : ℂ := (criticalAliasCoefficient W₀ : ℂ)
  set C₁ := negativeHalfLineLaplace (cx F) (1 / 2)
  set C₂ := negativeHalfLineLaplace (cx F) (-(1 / 2))
  -- the prime datum is a.e. its pointwise sum
  have hsumLp := summable_primeHeadDatumLp hF hc hc0
  have hnorms : Summable fun n =>
      (eLpNorm (primeHeadDatumTerm F 1 n) 2 (volume.restrict (Ioi (0 : ℝ)))).toReal := by
    refine Summable.of_nonneg_of_le (fun n => ENNReal.toReal_nonneg) (fun n => ?_)
      ((summable_primeHead_damping hc0).mul_right (eLpNorm (dampedNegativeProfile F 1) 2 volume).toReal)
    have h := norm_primeHeadDatumLp_le hF hc n
    rwa [primeHeadDatumLp, Lp.norm_toLp] at h
  have hsAE := ae_summable_of_summable_eLpNorm (memLp_primeHeadDatumTerm hF hc) hnorms
  -- the prime datum as an element of the half-line Hardy space
  let P : Lp ℂ 2 halfLineLaplaceMeasure := primeHeadProfileLp hF hc
  have hprime : (P : ℝ → ℂ) =ᵐ[halfLineLaplaceMeasure]
      fun x => ∑' n, primeHeadDatumTerm F 1 n x :=
    coeFn_tsum_ae_eq hsumLp (fun n => (memLp_primeHeadDatumTerm hF hc n).coeFn_toLp) hsAE
  have hsAE' : ∀ᵐ x ∂halfLineLaplaceMeasure, Summable fun n => primeHeadDatumTerm F 1 n x := hsAE
  show ∀ᵐ x ∂halfLineLaplaceMeasure, _
  have hw₁ : 0 < (((1 + 1 / 2 : ℝ)) : ℂ).re := by simp only [ofReal_re]; norm_num
  have hw₂ : 0 < (((1 - 1 / 2 : ℝ)) : ℂ).re := by simp only [ofReal_re]; norm_num
  have hdef : unitLeftDatum W₀ hF = (-(1 : ℂ) / A) •
      (dampedLevyHeadDatumLp hF h0 + P -
        C₁ • halfLineLaplaceFeature ((1 + 1 / 2 : ℝ) : ℂ) hw₁ -
        C₂ • halfLineLaplaceFeature ((1 - 1 / 2 : ℝ) : ℂ) hw₂) := rfl
  filter_upwards [hprime, hsAE',
    Lp.coeFn_smul (-(1 : ℂ) / A) (dampedLevyHeadDatumLp hF h0 + P -
        C₁ • halfLineLaplaceFeature ((1 + 1 / 2 : ℝ) : ℂ) hw₁ -
        C₂ • halfLineLaplaceFeature ((1 - 1 / 2 : ℝ) : ℂ) hw₂),
    Lp.coeFn_sub (dampedLevyHeadDatumLp hF h0 + P -
        C₁ • halfLineLaplaceFeature ((1 + 1 / 2 : ℝ) : ℂ) hw₁)
      (C₂ • halfLineLaplaceFeature ((1 - 1 / 2 : ℝ) : ℂ) hw₂),
    Lp.coeFn_sub (dampedLevyHeadDatumLp hF h0 + P)
      (C₁ • halfLineLaplaceFeature ((1 + 1 / 2 : ℝ) : ℂ) hw₁),
    Lp.coeFn_add (dampedLevyHeadDatumLp hF h0) P,
    Lp.coeFn_smul C₁ (halfLineLaplaceFeature ((1 + 1 / 2 : ℝ) : ℂ) hw₁),
    Lp.coeFn_smul C₂ (halfLineLaplaceFeature ((1 - 1 / 2 : ℝ) : ℂ) hw₂),
    (memLp_dampedLevyHeadProfile hF h0).coeFn_toLp,
    (halfLineLaplaceFeatureRaw_memLp hw₁).coeFn_toLp,
    (halfLineLaplaceFeatureRaw_memLp hw₂).coeFn_toLp] with x hpx hsx e1 e2 e3 e4 e5 e6 e7 f1 f2
  have e7' : (dampedLevyHeadDatumLp hF h0 : ℝ → ℂ) x =
      levyHeadProfile F x * expRay ((1 : ℝ) : ℂ) x := e7
  have f1' : (halfLineLaplaceFeature ((1 + 1 / 2 : ℝ) : ℂ) hw₁ : ℝ → ℂ) x =
      halfLineLaplaceFeatureRaw ((1 + 1 / 2 : ℝ) : ℂ) x := f1
  have f2' : (halfLineLaplaceFeature ((1 - 1 / 2 : ℝ) : ℂ) hw₂ : ℝ → ℂ) x =
      halfLineLaplaceFeatureRaw ((1 - 1 / 2 : ℝ) : ℂ) x := f2
  have hterm : ∀ n, primeHeadDatumTerm F 1 n x =
      (Real.exp (-x) : ℂ) * ((primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)) :=
    fun n => primeHeadDatumTerm_one F n x
  have hsx' : Summable fun n : ℕ => (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ) := by
    have h := hsx.mul_left (Real.exp x : ℂ)
    refine h.congr fun n => ?_
    rw [hterm n, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      Complex.ofReal_one, one_mul]
  refine ⟨hsx', ?_⟩
  set T := ∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)
  have hT : (∑' n, primeHeadDatumTerm F 1 n x) = (Real.exp (-x) : ℂ) * T := by
    rw [tsum_congr hterm, tsum_mul_left]
  have hU : (unitLeftDatum W₀ hF : ℝ → ℂ) x = (-(1 : ℂ) / A) *
      (levyHeadProfile F x * expRay ((1 : ℝ) : ℂ) x + (Real.exp (-x) : ℂ) * T -
        C₁ * halfLineLaplaceFeatureRaw ((1 + 1 / 2 : ℝ) : ℂ) x -
        C₂ * halfLineLaplaceFeatureRaw ((1 - 1 / 2 : ℝ) : ℂ) x) := by
    rw [hdef, e1, Pi.smul_apply, smul_eq_mul, e2, Pi.sub_apply, e3, Pi.sub_apply, e4, Pi.add_apply,
      e5, e6, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, e7', f1', f2', hpx, hT]
  have E1 : Complex.exp (x : ℂ) * expRay ((1 : ℝ) : ℂ) x = 1 := by
    rw [expRay, ← Complex.exp_add]; simp
  have E4 : Complex.exp (x : ℂ) * (Real.exp (-x) : ℂ) = 1 := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; push_cast; simp
  have E2 : Complex.exp (x : ℂ) * halfLineLaplaceFeatureRaw ((1 + 1 / 2 : ℝ) : ℂ) x =
      (Real.exp (-(x / 2)) : ℂ) := by
    rw [halfLineLaplaceFeatureRaw, ← Complex.exp_add, Complex.ofReal_exp]
    congr 1; simp only [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
  have E3 : Complex.exp (x : ℂ) * halfLineLaplaceFeatureRaw ((1 - 1 / 2 : ℝ) : ℂ) x =
      (Real.exp (x / 2) : ℂ) := by
    rw [halfLineLaplaceFeatureRaw, ← Complex.exp_add, Complex.ofReal_exp]
    congr 1; simp only [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
  have key : ∀ X : ℂ, -A * (Complex.exp (x : ℂ) * (-(1 : ℂ) / A * X)) = Complex.exp (x : ℂ) * X :=
    fun X => by field_simp
  rw [beyondWallProfile, hU, key]
  linear_combination levyHeadProfile F x * E1 + T * E4 - C₁ * E2 - C₂ * E3

/-- **The prime part beyond the wall is the averaged remainder of the prime number theorem.** For almost
every `x > 0`, `−a F⁺(x) = J⁺(x) − L F(½) e^{−x/2} + (Σ_n Λ(n) n^{−½} F(x − log n) − ∫_{y>x} F(x − y)
e^{y/2} dy)`. -/
theorem beyondWallProfile_pntForm {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      -(criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hF x =
        levyHeadProfile F x - negativeHalfLineLaplace (cx F) (1 / 2) * (Real.exp (-(x / 2)) : ℂ) +
          ((∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)) -
            ∫ y in Ioi x, (F (x - y) : ℂ) * (Real.exp (y / 2) : ℂ)) := by
  filter_upwards [beyondWallProfile_primeForm hW hF] with x hx
  rw [hx.2, ← polarWallTerm_eq_continuumMainTerm hF x]
  ring

end GaloisForLFunctions.ExclusionOfTheCriticalState
