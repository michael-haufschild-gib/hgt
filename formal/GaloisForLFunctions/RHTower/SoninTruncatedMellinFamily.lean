import GaloisForLFunctions.HTGeometry.TruncatedMellinEntire
import GaloisForLFunctions.RHTower.SoninTruncatedMellinCauchy

/-!
# The truncated Mellin family of a Sonine vector

`soninTruncMellin f a T s = ∫_a^T t^{-s} f(t) dt` is entire in `s` for every finite truncation `T`,
its increments are exactly the integrals estimated in `SoninTruncatedMellinCauchy`, and therefore
the family is uniformly Cauchy on every set of the form `{σ₀ ≤ Re s} ∩ {‖s‖ ≤ R}` with `σ₀ > 0`.

## Main results

* `differentiable_soninTruncMellin`
* `soninTruncMellin_sub`
* `norm_soninTruncMellin_sub_le`
-/

noncomputable section

open MeasureTheory Set Complex Real

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The truncated right Mellin transform of an `L²` vector. -/
def soninTruncMellin (f : SoninL2) (a T : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioo a T, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t

theorem integrableOn_soninL2_Ioo (f : SoninL2) (a T : ℝ) :
    IntegrableOn (f : ℝ → ℂ) (Set.Ioo a T) volume := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioo a T)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  exact ((Lp.memLp f).restrict (Set.Ioo a T)).integrable (by norm_num)

theorem differentiable_soninTruncMellin {a T : ℝ} (ha : 0 < a) (haT : a ≤ T) (f : SoninL2) :
    Differentiable ℂ (soninTruncMellin f a T) := by
  have hcong : soninTruncMellin f a T
      = fun s : ℂ => ∫ t in Set.Ioo a T, (f : ℝ → ℂ) t * ((t : ℝ) : ℂ) ^ (-s) := by
    funext s
    rw [soninTruncMellin]
    refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    ring
  rw [hcong]
  exact differentiable_truncatedMellin ha haT (integrableOn_soninL2_Ioo f a T)

theorem integrableOn_cpow_mul_Icc {b c : ℝ} (hb : 0 < b) (f : SoninL2) (s : ℂ) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t) (Set.Icc b c) volume := by
  refine IntegrableOn.continuousOn_mul ?_ ?_ isCompact_Icc
  · exact (continuousOn_ofReal_cpow_neg_Ici hb s).mono (fun t ht => ht.1)
  · haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Icc b c)) := by
      constructor
      rw [Measure.restrict_apply_univ]
      exact measure_Icc_lt_top
    exact ((Lp.memLp f).restrict (Set.Icc b c)).integrable (by norm_num)

theorem integrableOn_cpow_mul_Ioc {b c : ℝ} (hb : 0 < b) (f : SoninL2) (s : ℂ) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t) (Set.Ioc b c) volume :=
  (integrableOn_cpow_mul_Icc hb f s).mono_set Set.Ioc_subset_Icc_self

/-- Increments of the truncated Mellin family are integrals over the intervening window. -/
theorem soninTruncMellin_sub {a T T' : ℝ} (ha : 0 < a) (haT : a ≤ T) (hTT' : T ≤ T')
    (f : SoninL2) (s : ℂ) :
    soninTruncMellin f a T' s - soninTruncMellin f a T s
      = ∫ t in Set.Ioo T T', ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
  have hsplit : Set.Ioc a T ∪ Set.Ioc T T' = Set.Ioc a T' := Set.Ioc_union_Ioc_eq_Ioc haT hTT'
  have hdisj : Disjoint (Set.Ioc a T) (Set.Ioc T T') := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx'.1 (not_lt.2 hx.2)
  have hun := MeasureTheory.setIntegral_union hdisj measurableSet_Ioc
    (integrableOn_cpow_mul_Ioc ha f s) (integrableOn_cpow_mul_Ioc (lt_of_lt_of_le ha haT) f s)
  rw [hsplit] at hun
  rw [soninTruncMellin, soninTruncMellin, ← integral_Ioc_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo, hun]
  ring

/-- **The uniform Cauchy estimate for the truncated Mellin family of a Sonine vector.** -/
theorem norm_soninTruncMellin_sub_le {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hf : f ∈ centralSoninCarrier a) {T T' : ℝ} (haT : a ≤ T) (hTT' : T ≤ T') {s : ℂ}
    (hs : 0 < s.re) :
    ‖soninTruncMellin f a T' s - soninTruncMellin f a T s‖
      ≤ ((2 * T ^ (-s.re) + ‖s‖ * T ^ (-s.re) / s.re) / (2 * Real.pi)) *
          invAbsTailNorm a * ‖f‖ := by
  rw [soninTruncMellin_sub ha haT hTT' f s]
  exact norm_truncMellin_le ha hf haT hTT' hs

end RHTower
