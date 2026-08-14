import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The weighted Hardy inequality on `(1, ∞)`

For `p > 1/2` the weighted Hardy averaging operator

`(K h)(x) = x^{-p} ∫₁^x t^{p-1} h(t) dt`

is bounded on `L²((1,∞))` with operator norm at most `(p - 1/2)⁻¹`.  The proof is Cauchy–Schwarz
against the weight `t^{p-1/2}`, which converts the inner integral into

`(x^{p-1/2}/(p-1/2)) ∫₁^x t^{p-1/2}|h|²`,

followed by Tonelli: the resulting outer weight `x^{-(p+1/2)}` integrates over `[t,∞)` to
`t^{-(p-1/2)}/(p-1/2)`, which cancels the inner weight exactly and leaves the square of the
constant.

Everything is stated for `ℝ≥0∞`-valued densities, so no integrability hypothesis is needed, and
then transported to Bochner integrals of functions valued in a normed space.

The exponent restriction is sharp at both ends: for `p ≤ 1/2` the indicator of `(1,2]` is square
integrable while its Hardy average is not.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Two-power form of the square in `ℝ≥0∞`. -/
private theorem enn_rpow_two (a : ℝ≥0∞) : a ^ (2 : ℝ) = a ^ 2 := by
  rw [← ENNReal.rpow_natCast a 2]
  norm_num

private theorem enn_sqrt_mul_sq (A B : ℝ≥0∞) :
    (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) ^ 2 = A * B := by
  rw [mul_pow, ← ENNReal.rpow_natCast (A ^ ((1 : ℝ) / 2)) 2,
    ← ENNReal.rpow_natCast (B ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num

/-- **Weighted Cauchy–Schwarz on a finite window.**  Against the weight `t^{p-1/2}` the square of
the Hardy numerator is controlled by the weighted energy, with the elementary constant
`x^{p-1/2}/(p-1/2)` coming from `∫₁^x t^{p-3/2} dt`. -/
private theorem sq_hardyKernel_le {p : ℝ} (hp : 1 / 2 < p) {H : ℝ → ℝ≥0∞}
    (hH : Measurable H) {x : ℝ} (hx : 1 ≤ x) :
    (∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2
      ≤ ENNReal.ofReal (x ^ (p - 1 / 2) / (p - 1 / 2))
          * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1 / 2)) * H t ^ 2 := by
  have hq : 0 < p - 1 / 2 := by linarith
  have hconj : Real.HolderConjugate 2 2 := by constructor <;> norm_num
  have hs : MeasurableSet (Ioc (1 : ℝ) x) := measurableSet_Ioc
  set f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p / 2 - 3 / 4)) with hfdef
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p / 2 - 1 / 4)) * H t with hgdef
  have hfmeas : Measurable f := by fun_prop
  have hgmeas : Measurable g :=
    (by fun_prop : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (p / 2 - 1 / 4))).mul hH
  have hprod : EqOn (f * g) (fun t => ENNReal.ofReal (t ^ (p - 1)) * H t) (Ioc (1 : ℝ) x) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht.1
    have hexp : p / 2 - 3 / 4 + (p / 2 - 1 / 4) = p - 1 := by ring
    simp only [Pi.mul_apply, hfdef, hgdef]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _), ← Real.rpow_add ht0, hexp]
  have hf2 : EqOn (fun t => f t ^ (2 : ℝ)) (fun t => ENNReal.ofReal (t ^ (p - 3 / 2)))
      (Ioc (1 : ℝ) x) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht.1
    have hexp : (p / 2 - 3 / 4) * 2 = p - 3 / 2 := by ring
    simp only [hfdef]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht0.le _) (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul ht0.le, hexp]
  have hg2 : EqOn (fun t => g t ^ (2 : ℝ))
      (fun t => ENNReal.ofReal (t ^ (p - 1 / 2)) * H t ^ 2) (Ioc (1 : ℝ) x) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht.1
    have hexp : (p / 2 - 1 / 4) * 2 = p - 1 / 2 := by ring
    simp only [hgdef]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht0.le _) (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul ht0.le, hexp, enn_rpow_two]
  have hpow : ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 3 / 2))
      = ENNReal.ofReal ((x ^ (p - 1 / 2) - 1) / (p - 1 / 2)) := by
    have hint : IntegrableOn (fun t : ℝ => t ^ (p - 3 / 2)) (Ioc (1 : ℝ) x) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp
        (intervalIntegral.intervalIntegrable_rpow' (a := (1 : ℝ)) (b := x) (r := p - 3 / 2)
          (by linarith))
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc (1 : ℝ) x)] fun t : ℝ => t ^ (p - 3 / 2) := by
      filter_upwards [ae_restrict_mem hs] with t ht
      exact Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht.1)) _
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    rw [← intervalIntegral.integral_of_le hx, integral_rpow (Or.inl (by linarith))]
    rw [show p - 3 / 2 + 1 = p - 1 / 2 by ring, Real.one_rpow]
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc (1 : ℝ) x)) hconj
    hfmeas.aemeasurable hgmeas.aemeasurable
  rw [setLIntegral_congr_fun hs hprod] at hCS
  calc (∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2
      ≤ ((∫⁻ t in Ioc (1 : ℝ) x, f t ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
          * (∫⁻ t in Ioc (1 : ℝ) x, g t ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ 2 := pow_le_pow_left' hCS 2
    _ = (∫⁻ t in Ioc (1 : ℝ) x, f t ^ (2 : ℝ)) * ∫⁻ t in Ioc (1 : ℝ) x, g t ^ (2 : ℝ) :=
        enn_sqrt_mul_sq _ _
    _ = ENNReal.ofReal ((x ^ (p - 1 / 2) - 1) / (p - 1 / 2))
          * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1 / 2)) * H t ^ 2 := by
        rw [setLIntegral_congr_fun hs hf2, setLIntegral_congr_fun hs hg2, hpow]
    _ ≤ ENNReal.ofReal (x ^ (p - 1 / 2) / (p - 1 / 2))
          * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1 / 2)) * H t ^ 2 := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        rw [sub_div]
        have : 0 ≤ 1 / (p - 1 / 2) := by positivity
        linarith

/-- **The Tonelli step.**  Integrating the tail weight `x^{-(q+1)}` against the moving window
`(1,x]` replaces it by the exact one-sided tail mass `t^{-q}/q`. -/
private theorem lintegral_tail_weight {q : ℝ} (hq : 0 < q) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (x ^ (-(q + 1))) * ∫⁻ t in Ioc (1 : ℝ) x, F t
      = ENNReal.ofReal q⁻¹ * ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-q)) * F t := by
  classical
  set S : Set (ℝ × ℝ) := {r : ℝ × ℝ | 1 < r.2 ∧ r.2 ≤ r.1} with hSdef
  have hSmeas : MeasurableSet S := by
    have h1 : MeasurableSet {r : ℝ × ℝ | 1 < r.2} :=
      measurableSet_lt measurable_const measurable_snd
    have h2 : MeasurableSet {r : ℝ × ℝ | r.2 ≤ r.1} :=
      measurableSet_le measurable_snd measurable_fst
    exact h1.inter h2
  set Φ : ℝ → ℝ → ℝ≥0∞ := fun x t =>
    ENNReal.ofReal (x ^ (-(q + 1))) * S.indicator (fun r : ℝ × ℝ => F r.2) (x, t) with hΦdef
  have hΦmeas : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable fun r : ℝ × ℝ => ENNReal.ofReal (r.1 ^ (-(q + 1))) := by fun_prop
    have h2 : Measurable (S.indicator fun r : ℝ × ℝ => F r.2) :=
      (hF.comp measurable_snd).indicator hSmeas
    exact h1.mul h2
  have hinner : EqOn (fun x => ∫⁻ t in Ioi (1 : ℝ), Φ x t)
      (fun x => ENNReal.ofReal (x ^ (-(q + 1))) * ∫⁻ t in Ioc (1 : ℝ) x, F t) (Ioi (1 : ℝ)) := by
    intro x hx
    have hslice : (fun t => S.indicator (fun r : ℝ × ℝ => F r.2) (x, t))
        = (Ioc (1 : ℝ) x).indicator F := by
      funext t
      by_cases ht : t ∈ Ioc (1 : ℝ) x
      · rw [Set.indicator_of_mem ht,
          Set.indicator_of_mem (show (x, t) ∈ S from ⟨ht.1, ht.2⟩)]
      · rw [Set.indicator_of_notMem ht,
          Set.indicator_of_notMem (show (x, t) ∉ S from fun h => ht ⟨h.1, h.2⟩)]
    simp only [hΦdef]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hslice,
      lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_self_of_subset_left
        (show Ioc (1 : ℝ) x ⊆ Ioi (1 : ℝ) from fun y hy => hy.1)]
  have houter : EqOn (fun t => ∫⁻ x in Ioi (1 : ℝ), Φ x t)
      (fun t => ENNReal.ofReal q⁻¹ * (ENNReal.ofReal (t ^ (-q)) * F t)) (Ioi (1 : ℝ)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have hslice : (fun x => Φ x t)
        = (Ici t).indicator (fun x => ENNReal.ofReal (x ^ (-(q + 1))) * F t) := by
      funext x
      by_cases hx : t ≤ x
      · rw [Set.indicator_of_mem (show x ∈ Ici t from hx)]
        simp only [hΦdef]
        rw [Set.indicator_of_mem (show (x, t) ∈ S from ⟨ht, hx⟩)]
      · rw [Set.indicator_of_notMem (show x ∉ Ici t from hx)]
        simp only [hΦdef]
        rw [Set.indicator_of_notMem (show (x, t) ∉ S from fun h => hx h.2), mul_zero]
    have hIci : ∫⁻ x in Ici t, ENNReal.ofReal (x ^ (-(q + 1)))
        = ENNReal.ofReal (t ^ (-q) / q) := by
      rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
      have hint : IntegrableOn (fun x : ℝ => x ^ (-(q + 1))) (Ioi t) volume :=
        (integrableOn_Ioi_rpow_iff ht0).mpr (by linarith)
      have hnn : 0 ≤ᵐ[volume.restrict (Ioi t)] fun x : ℝ => x ^ (-(q + 1)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact Real.rpow_nonneg (le_of_lt (lt_trans ht0 hx)) _
      rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
      congr 1
      rw [integral_Ioi_rpow_of_lt (by linarith) ht0, show -(q + 1) + 1 = -q by ring]
      exact neg_div_neg_eq _ _
    show ∫⁻ x in Ioi (1 : ℝ), Φ x t
        = ENNReal.ofReal q⁻¹ * (ENNReal.ofReal (t ^ (-q)) * F t)
    rw [hslice, lintegral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici,
      Set.inter_eq_self_of_subset_left
        (show Ici t ⊆ Ioi (1 : ℝ) from fun y hy =>
          Set.mem_Ioi.mpr (lt_of_lt_of_le ht (Set.mem_Ici.mp hy))),
      lintegral_mul_const _ (by fun_prop), hIci, ← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hq))]
    congr 1
    field_simp
  calc ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (x ^ (-(q + 1))) * ∫⁻ t in Ioc (1 : ℝ) x, F t
      = ∫⁻ x in Ioi (1 : ℝ), ∫⁻ t in Ioi (1 : ℝ), Φ x t :=
        (setLIntegral_congr_fun measurableSet_Ioi hinner).symm
    _ = ∫⁻ t in Ioi (1 : ℝ), ∫⁻ x in Ioi (1 : ℝ), Φ x t :=
        lintegral_lintegral_swap hΦmeas.aemeasurable
    _ = ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal q⁻¹ * (ENNReal.ofReal (t ^ (-q)) * F t) :=
        setLIntegral_congr_fun measurableSet_Ioi houter
    _ = ENNReal.ofReal q⁻¹ * ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-q)) * F t :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **The weighted Hardy inequality for nonnegative densities.**  For `p > 1/2` the Hardy average
`x^{-p}∫₁^x t^{p-1}H(t)dt` has `L²((1,∞))` norm at most `(p-1/2)⁻¹‖H‖₂`. -/
theorem lintegral_hardyAverage_sq_le_of_measurable {p : ℝ} (hp : 1 / 2 < p) {H : ℝ → ℝ≥0∞}
    (hH : Measurable H) :
    (∫⁻ x in Ioi (1 : ℝ),
        (ENNReal.ofReal (x ^ (-p)) * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2)
      ≤ ENNReal.ofReal ((p - 1 / 2)⁻¹ ^ 2) * ∫⁻ t in Ioi (1 : ℝ), H t ^ 2 := by
  have hq : 0 < p - 1 / 2 := by linarith
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p - 1 / 2)) * H t ^ 2 with hFdef
  have hFmeas : Measurable F :=
    (by fun_prop : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (p - 1 / 2))).mul (hH.pow_const 2)
  have hpt : EqOn (fun x =>
      (ENNReal.ofReal (x ^ (-p)) * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2)
      (fun x => ENNReal.ofReal (x ^ (-p)) ^ 2
        * (∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2) (Ioi (1 : ℝ)) := by
    intro x _
    exact mul_pow _ _ 2
  have hbound : ∀ x ∈ Ioi (1 : ℝ),
      ENNReal.ofReal (x ^ (-p)) ^ 2
          * (∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2
        ≤ ENNReal.ofReal (p - 1 / 2)⁻¹
            * (ENNReal.ofReal (x ^ (-(p - 1 / 2 + 1))) * ∫⁻ t in Ioc (1 : ℝ) x, F t) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hreal : (x ^ (-p)) ^ 2 * (x ^ (p - 1 / 2) / (p - 1 / 2))
        = (p - 1 / 2)⁻¹ * x ^ (-(p - 1 / 2 + 1)) := by
      rw [← Real.rpow_natCast (x ^ (-p)) 2, ← Real.rpow_mul hx0.le, div_eq_mul_inv, ← mul_assoc,
        ← Real.rpow_add hx0, show -p * ((2 : ℕ) : ℝ) + (p - 1 / 2) = -(p - 1 / 2 + 1) by
          push_cast; ring]
      ring
    have hennreal : ENNReal.ofReal (x ^ (-p)) ^ 2
        * ENNReal.ofReal (x ^ (p - 1 / 2) / (p - 1 / 2))
        = ENNReal.ofReal (p - 1 / 2)⁻¹ * ENNReal.ofReal (x ^ (-(p - 1 / 2 + 1))) := by
      rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hx0.le _),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hreal]
    calc ENNReal.ofReal (x ^ (-p)) ^ 2
          * (∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2
        ≤ ENNReal.ofReal (x ^ (-p)) ^ 2
            * (ENNReal.ofReal (x ^ (p - 1 / 2) / (p - 1 / 2)) * ∫⁻ t in Ioc (1 : ℝ) x, F t) :=
          mul_le_mul' le_rfl (sq_hardyKernel_le hp hH (le_of_lt hx))
      _ = ENNReal.ofReal (p - 1 / 2)⁻¹
            * (ENNReal.ofReal (x ^ (-(p - 1 / 2 + 1))) * ∫⁻ t in Ioc (1 : ℝ) x, F t) := by
          rw [← mul_assoc, hennreal, mul_assoc]
  have hFsimp : EqOn (fun t => ENNReal.ofReal (t ^ (-(p - 1 / 2))) * F t) (fun t => H t ^ 2)
      (Ioi (1 : ℝ)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    simp only [hFdef]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _), ← Real.rpow_add ht0,
      neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  calc (∫⁻ x in Ioi (1 : ℝ),
        (ENNReal.ofReal (x ^ (-p)) * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2)
      = ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (x ^ (-p)) ^ 2
          * (∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2 :=
        setLIntegral_congr_fun measurableSet_Ioi hpt
    _ ≤ ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (p - 1 / 2)⁻¹
          * (ENNReal.ofReal (x ^ (-(p - 1 / 2 + 1))) * ∫⁻ t in Ioc (1 : ℝ) x, F t) := by
        refine setLIntegral_mono' measurableSet_Ioi ?_
        intro x hx
        exact hbound x hx
    _ = ENNReal.ofReal (p - 1 / 2)⁻¹ * ∫⁻ x in Ioi (1 : ℝ),
          ENNReal.ofReal (x ^ (-(p - 1 / 2 + 1))) * ∫⁻ t in Ioc (1 : ℝ) x, F t :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (p - 1 / 2)⁻¹
          * (ENNReal.ofReal (p - 1 / 2)⁻¹
            * ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-(p - 1 / 2))) * F t) := by
        rw [lintegral_tail_weight hq hFmeas]
    _ = ENNReal.ofReal ((p - 1 / 2)⁻¹ ^ 2) * ∫⁻ t in Ioi (1 : ℝ), H t ^ 2 := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hq)), ← sq,
          setLIntegral_congr_fun measurableSet_Ioi hFsimp]

/-- The weighted Hardy inequality for an almost everywhere measurable density. -/
theorem lintegral_hardyAverage_sq_le {p : ℝ} (hp : 1 / 2 < p) {H : ℝ → ℝ≥0∞}
    (hH : AEMeasurable H (volume.restrict (Ioi (1 : ℝ)))) :
    (∫⁻ x in Ioi (1 : ℝ),
        (ENNReal.ofReal (x ^ (-p)) * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2)
      ≤ ENNReal.ofReal ((p - 1 / 2)⁻¹ ^ 2) * ∫⁻ t in Ioi (1 : ℝ), H t ^ 2 := by
  have hmk : H =ᵐ[volume.restrict (Ioi (1 : ℝ))] hH.mk H := hH.ae_eq_mk
  have hwindow : ∀ x : ℝ, H =ᵐ[volume.restrict (Ioc (1 : ℝ) x)] hH.mk H := by
    intro x
    exact ae_mono (Measure.restrict_mono (fun y hy => hy.1) le_rfl) hmk
  have hleft : EqOn (fun x =>
      (ENNReal.ofReal (x ^ (-p)) * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * H t) ^ 2)
      (fun x => (ENNReal.ofReal (x ^ (-p))
        * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * hH.mk H t) ^ 2)
      (Ioi (1 : ℝ)) := by
    intro x _
    refine congrArg (· ^ 2) (congrArg _ (lintegral_congr_ae ?_))
    filter_upwards [hwindow x] with t ht
    rw [ht]
  rw [setLIntegral_congr_fun measurableSet_Ioi hleft,
    lintegral_congr_ae (by filter_upwards [hmk] with t ht; rw [ht] :
      (fun t => H t ^ 2) =ᵐ[volume.restrict (Ioi (1 : ℝ))] fun t => hH.mk H t ^ 2)]
  exact lintegral_hardyAverage_sq_le_of_measurable hp hH.measurable_mk

section Vector

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **The Hilbert-valued weighted Hardy inequality.**  For `p > 1/2` the Bochner Hardy average of a
square integrable `X`-valued function is square integrable, with constant `(p-1/2)⁻¹`. -/
theorem lintegral_enorm_hardyAverage_sq_le {p : ℝ} (hp : 1 / 2 < p) {h : ℝ → X}
    (hh : AEStronglyMeasurable h (volume.restrict (Ioi (1 : ℝ)))) :
    (∫⁻ x in Ioi (1 : ℝ),
        ‖x ^ (-p) • ∫ t in Ioc (1 : ℝ) x, t ^ (p - 1) • h t‖ₑ ^ 2)
      ≤ ENNReal.ofReal ((p - 1 / 2)⁻¹ ^ 2) * ∫⁻ t in Ioi (1 : ℝ), ‖h t‖ₑ ^ 2 := by
  have hmeas : AEMeasurable (fun t => ‖h t‖ₑ) (volume.restrict (Ioi (1 : ℝ))) :=
    hh.enorm
  refine le_trans ?_ (lintegral_hardyAverage_sq_le hp hmeas)
  refine setLIntegral_mono' measurableSet_Ioi ?_
  intro x hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  refine pow_le_pow_left' ?_ 2
  have hstep : ‖∫ t in Ioc (1 : ℝ) x, t ^ (p - 1) • h t‖ₑ
      ≤ ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ := by
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht.1
    rw [enorm_smul]
    exact mul_le_mul' (le_of_eq (by
      rw [Real.enorm_eq_ofReal (Real.rpow_nonneg ht0.le _)])) le_rfl
  calc ‖x ^ (-p) • ∫ t in Ioc (1 : ℝ) x, t ^ (p - 1) • h t‖ₑ
      = ENNReal.ofReal (x ^ (-p)) * ‖∫ t in Ioc (1 : ℝ) x, t ^ (p - 1) • h t‖ₑ := by
        rw [enorm_smul, Real.enorm_eq_ofReal (Real.rpow_nonneg hx0.le _)]
    _ ≤ ENNReal.ofReal (x ^ (-p))
          * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ :=
        mul_le_mul' le_rfl hstep

end Vector

section Sharpness

/-- The test density used to certify sharpness: the indicator of the unit window `(1,2]`. -/
def hardySharpDensity : ℝ → ℝ≥0∞ := (Ioc (1 : ℝ) 2).indicator (fun _ => (1 : ℝ≥0∞))

theorem lintegral_hardySharpDensity_sq :
    ∫⁻ t in Ioi (1 : ℝ), hardySharpDensity t ^ 2 = 1 := by
  have hrw : (fun t : ℝ => hardySharpDensity t ^ 2) = hardySharpDensity := by
    funext t
    simp only [hardySharpDensity]
    by_cases ht : t ∈ Ioc (1 : ℝ) 2
    · rw [Set.indicator_of_mem ht, one_pow]
    · rw [Set.indicator_of_notMem ht, zero_pow (by norm_num)]
  rw [hrw, hardySharpDensity, lintegral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left
      (show Ioc (1 : ℝ) 2 ⊆ Ioi (1 : ℝ) from fun y hy => hy.1),
    setLIntegral_const, one_mul, Real.volume_Ioc]
  norm_num

private theorem hardySharpWindow {p x : ℝ} (hx : 2 ≤ x) :
    ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * hardySharpDensity t
      = ∫⁻ t in Ioc (1 : ℝ) 2, ENNReal.ofReal (t ^ (p - 1)) := by
  have hrw : (fun t : ℝ => ENNReal.ofReal (t ^ (p - 1)) * hardySharpDensity t)
      = (Ioc (1 : ℝ) 2).indicator (fun t => ENNReal.ofReal (t ^ (p - 1))) := by
    funext t
    simp only [hardySharpDensity]
    by_cases ht : t ∈ Ioc (1 : ℝ) 2
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, mul_one]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
  rw [hrw, lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left
      (show Ioc (1 : ℝ) 2 ⊆ Ioc (1 : ℝ) x from fun y hy => ⟨hy.1, le_trans hy.2 hx⟩)]

private theorem hardySharpConst_pos {p : ℝ} (hp : p ≤ 1 / 2) :
    0 < ∫⁻ t in Ioc (1 : ℝ) 2, ENNReal.ofReal (t ^ (p - 1)) := by
  have hconst : (0 : ℝ≥0∞) < ∫⁻ _t in Ioc (1 : ℝ) 2, ENNReal.ofReal ((2 : ℝ) ^ (p - 1)) := by
    rw [setLIntegral_const, Real.volume_Ioc]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
      (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  refine lt_of_lt_of_le hconst (setLIntegral_mono' measurableSet_Ioc ?_)
  intro t ht
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_nonpos (lt_trans zero_lt_one ht.1) ht.2 (by linarith))

private theorem hardySharpConst_lt_top {p : ℝ} (hp : p ≤ 1 / 2) :
    (∫⁻ t in Ioc (1 : ℝ) 2, ENNReal.ofReal (t ^ (p - 1))) < ⊤ := by
  calc ∫⁻ t in Ioc (1 : ℝ) 2, ENNReal.ofReal (t ^ (p - 1))
      ≤ ∫⁻ _t in Ioc (1 : ℝ) 2, (1 : ℝ≥0∞) := by
        refine setLIntegral_mono' measurableSet_Ioc ?_
        intro t ht
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal
          (Real.rpow_le_one_of_one_le_of_nonpos ht.1.le (by linarith))
    _ < ⊤ := by
        rw [setLIntegral_const, one_mul, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top

private theorem lintegral_Ioi_two_rpow_eq_top {a : ℝ} (ha : -1 ≤ a) :
    ∫⁻ x in Ioi (2 : ℝ), ENNReal.ofReal (x ^ a) = ⊤ := by
  by_contra hcon
  have hne : ∫⁻ x in Ioi (2 : ℝ), ENNReal.ofReal (x ^ a) < ⊤ := lt_top_iff_ne_top.mpr hcon
  have hfi : HasFiniteIntegral (fun x : ℝ => x ^ a) (volume.restrict (Ioi (2 : ℝ))) := by
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr_ae ?_)) hne
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.enorm_eq_ofReal (Real.rpow_nonneg (le_of_lt (lt_trans (by norm_num) hx)) _)
  have hint : IntegrableOn (fun x : ℝ => x ^ a) (Ioi (2 : ℝ)) volume :=
    ⟨(by fun_prop : Measurable fun x : ℝ => x ^ a).aestronglyMeasurable, hfi⟩
  have := (integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp hint
  linarith

/-- **Sharpness of the exponent.**  At `p ≤ 1/2` the Hardy average of the unit-energy window
density `hardySharpDensity` is no longer square integrable, so the range `p > 1/2` in the weighted
Hardy inequality cannot be enlarged. -/
theorem lintegral_hardyAverage_sq_eq_top_of_le_half {p : ℝ} (hp : p ≤ 1 / 2) :
    (∫⁻ x in Ioi (1 : ℝ),
        (ENNReal.ofReal (x ^ (-p))
          * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * hardySharpDensity t) ^ 2)
      = ⊤ := by
  by_contra hcon
  have hne : (∫⁻ x in Ioi (1 : ℝ),
      (ENNReal.ofReal (x ^ (-p))
        * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * hardySharpDensity t) ^ 2) < ⊤ :=
    lt_top_iff_ne_top.mpr hcon
  set c : ℝ≥0∞ := ∫⁻ t in Ioc (1 : ℝ) 2, ENNReal.ofReal (t ^ (p - 1)) with hcdef
  have hcpos : 0 < c := hardySharpConst_pos hp
  have hctop : c < ⊤ := hardySharpConst_lt_top hp
  have hlow : ∀ x ∈ Ioi (2 : ℝ),
      ENNReal.ofReal (x ^ (-(2 * p))) * c ^ 2
        ≤ (ENNReal.ofReal (x ^ (-p))
            * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * hardySharpDensity t) ^ 2 := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans (by norm_num) hx
    rw [hardySharpWindow (le_of_lt hx), ← hcdef, mul_pow,
      ← ENNReal.ofReal_pow (Real.rpow_nonneg hx0.le _),
      ← Real.rpow_natCast (x ^ (-p)) 2, ← Real.rpow_mul hx0.le,
      show -p * ((2 : ℕ) : ℝ) = -(2 * p) by push_cast; ring]
  have htail : (∫⁻ x in Ioi (2 : ℝ), ENNReal.ofReal (x ^ (-(2 * p)))) * c ^ 2 < ⊤ := by
    rw [← lintegral_mul_const _ (by fun_prop)]
    refine lt_of_le_of_lt (le_trans (setLIntegral_mono' measurableSet_Ioi hlow) ?_) hne
    exact lintegral_mono' (Measure.restrict_mono
      (show Ioi (2 : ℝ) ⊆ Ioi (1 : ℝ) from fun y hy =>
        Set.mem_Ioi.mpr (lt_trans one_lt_two (Set.mem_Ioi.mp hy))) le_rfl) le_rfl
  rw [lintegral_Ioi_two_rpow_eq_top (by linarith : (-1 : ℝ) ≤ -(2 * p)),
    ENNReal.top_mul (pow_ne_zero 2 hcpos.ne')] at htail
  exact absurd htail (lt_irrefl ⊤)

end Sharpness

section Transfer

private theorem enn_sq_add_le (A B : ℝ≥0∞) : (A + B) ^ 2 ≤ 4 * A ^ 2 + 4 * B ^ 2 := by
  have h1 : A + B ≤ 2 * max A B := by
    rw [two_mul]
    exact add_le_add (le_max_left _ _) (le_max_right _ _)
  have h2 : max A B ^ 2 ≤ A ^ 2 + B ^ 2 := by
    rcases max_choice A B with h | h <;> rw [h]
    · exact le_self_add
    · exact le_add_self
  calc (A + B) ^ 2 ≤ (2 * max A B) ^ 2 := pow_le_pow_left' h1 2
    _ = 4 * max A B ^ 2 := by ring
    _ ≤ 4 * (A ^ 2 + B ^ 2) := mul_le_mul' le_rfl h2
    _ = 4 * A ^ 2 + 4 * B ^ 2 := by ring

private theorem lintegral_Ioi_one_rpow_lt_top {a : ℝ} (ha : a < -1) :
    ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (x ^ a) < ⊤ := by
  have hint : IntegrableOn (fun x : ℝ => x ^ a) (Ioi (1 : ℝ)) volume :=
    (integrableOn_Ioi_rpow_iff one_pos).mpr ha
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun x : ℝ => x ^ a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hx)) _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact ENNReal.ofReal_lt_top

variable {X : Type*} [NormedAddCommGroup X]

/-- **Weighted Hardy transfer for a propagated forced solution.**  A function obeying the
variation-of-constants bound with propagator decay `x^{-p}`, `p > 1/2`, and whose forcing carries a
square integrable first moment, is itself square integrable on the ray.  The homogeneous part is
square integrable because `2p > 1`, and the forced part is controlled by the weighted Hardy
inequality. -/
theorem lintegral_enorm_sq_lt_top_of_hardyBound {p : ℝ} (hp : 1 / 2 < p)
    {f h : ℝ → X} {K κ : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hbound : ∀ x : ℝ, 1 < x →
      ‖f x‖ₑ ≤ ENNReal.ofReal (K * x ^ (-p))
        * (ENNReal.ofReal κ + ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ))
    (hmeas : AEMeasurable (fun t => ‖h t‖ₑ) (volume.restrict (Ioi (1 : ℝ))))
    (hfin : ∫⁻ t in Ioi (1 : ℝ), ‖h t‖ₑ ^ 2 < ⊤) :
    ∫⁻ x in Ioi (1 : ℝ), ‖f x‖ₑ ^ 2 < ⊤ := by
  have hq : 0 < p - 1 / 2 := by linarith
  -- pointwise splitting of the propagated bound
  have hpt : ∀ x ∈ Ioi (1 : ℝ), ‖f x‖ₑ ^ 2
      ≤ 4 * ENNReal.ofReal ((K * κ) ^ 2 * x ^ (-(2 * p)))
        + 4 * (ENNReal.ofReal (K ^ 2)
          * (ENNReal.ofReal (x ^ (-p))
            * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ) ^ 2) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hsplitK : ENNReal.ofReal (K * x ^ (-p))
        = ENNReal.ofReal K * ENNReal.ofReal (x ^ (-p)) := ENNReal.ofReal_mul hK
    have hhom : (ENNReal.ofReal K * ENNReal.ofReal (x ^ (-p)) * ENNReal.ofReal κ) ^ 2
        = ENNReal.ofReal ((K * κ) ^ 2 * x ^ (-(2 * p))) := by
      rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [mul_pow, mul_pow, ← Real.rpow_natCast (x ^ (-p)) 2, ← Real.rpow_mul hx0.le,
        show -p * ((2 : ℕ) : ℝ) = -(2 * p) by push_cast; ring]
      ring
    have hforced : (ENNReal.ofReal K * (ENNReal.ofReal (x ^ (-p))
        * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ)) ^ 2
        = ENNReal.ofReal (K ^ 2)
          * (ENNReal.ofReal (x ^ (-p))
            * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ) ^ 2 := by
      rw [mul_pow, ← ENNReal.ofReal_pow hK]
    calc ‖f x‖ₑ ^ 2
        ≤ (ENNReal.ofReal (K * x ^ (-p))
            * (ENNReal.ofReal κ
              + ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ)) ^ 2 :=
          pow_le_pow_left' (hbound x hx) 2
      _ = (ENNReal.ofReal K * ENNReal.ofReal (x ^ (-p)) * ENNReal.ofReal κ
            + ENNReal.ofReal K * (ENNReal.ofReal (x ^ (-p))
              * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ)) ^ 2 := by
          rw [hsplitK]
          ring
      _ ≤ 4 * (ENNReal.ofReal K * ENNReal.ofReal (x ^ (-p)) * ENNReal.ofReal κ) ^ 2
            + 4 * (ENNReal.ofReal K * (ENNReal.ofReal (x ^ (-p))
              * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ)) ^ 2 :=
          enn_sq_add_le _ _
      _ = 4 * ENNReal.ofReal ((K * κ) ^ 2 * x ^ (-(2 * p)))
            + 4 * (ENNReal.ofReal (K ^ 2)
              * (ENNReal.ofReal (x ^ (-p))
                * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ) ^ 2) := by
          rw [hhom, hforced]
  -- the homogeneous ray integral
  have hhomfin : (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal ((K * κ) ^ 2 * x ^ (-(2 * p)))) < ⊤ := by
    have hrw : ∀ x ∈ Ioi (1 : ℝ), ENNReal.ofReal ((K * κ) ^ 2 * x ^ (-(2 * p)))
        = ENNReal.ofReal ((K * κ) ^ 2) * ENNReal.ofReal (x ^ (-(2 * p))) := by
      intro x _
      exact ENNReal.ofReal_mul (by positivity)
    rw [setLIntegral_congr_fun measurableSet_Ioi hrw,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lintegral_Ioi_one_rpow_lt_top (by linarith))
  -- the forced ray integral
  have hforcedfin : (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (K ^ 2)
      * (ENNReal.ofReal (x ^ (-p))
        * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ) ^ 2) < ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    refine lt_of_le_of_lt (lintegral_hardyAverage_sq_le hp hmeas) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  calc ∫⁻ x in Ioi (1 : ℝ), ‖f x‖ₑ ^ 2
      ≤ ∫⁻ x in Ioi (1 : ℝ), (4 * ENNReal.ofReal ((K * κ) ^ 2 * x ^ (-(2 * p)))
          + 4 * (ENNReal.ofReal (K ^ 2)
            * (ENNReal.ofReal (x ^ (-p))
              * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ) ^ 2)) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = 4 * (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal ((K * κ) ^ 2 * x ^ (-(2 * p))))
          + 4 * ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (K ^ 2)
            * (ENNReal.ofReal (x ^ (-p))
              * ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ) ^ 2 := by
        rw [lintegral_add_left' (by
          refine AEMeasurable.const_mul ?_ _
          exact ENNReal.measurable_ofReal.comp_aemeasurable
            (((by fun_prop : Measurable fun x : ℝ => (K * κ) ^ 2 * x ^ (-(2 * p)))).aemeasurable))
          _, lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
    _ < ⊤ :=
        ENNReal.add_lt_top.mpr
          ⟨ENNReal.mul_lt_top (by norm_num) hhomfin, ENNReal.mul_lt_top (by norm_num) hforcedfin⟩

end Transfer

end GaloisForLFunctions.HTGeometry
