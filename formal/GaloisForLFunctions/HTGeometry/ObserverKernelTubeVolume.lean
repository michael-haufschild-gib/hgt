import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Annular tubes over an invisible carrier, and the exponent they force

An invisible coefficient carrier `F` of a Hamiltonian dictionary contributes a
tube: an annular shell in `F` thickened by a fixed transverse radius.  Its Haar
volume scales as the `dim F`-th power of the shell radius, which is the source of
the annular lower bound on the shortcut locus.  A power lower bound of that shape
dominated by a power upper bound forces the ceiling on the upper exponent.
-/

open MeasureTheory Metric Filter Topology

namespace GaloisForLFunctions.HTGeometry

section ExponentComparison

/-- **Exponent ceiling.**  If a positive multiple of `t ^ (-v)` is dominated by
`K * t ^ (-κ)` for all large `t`, then `κ ≤ v`. -/
theorem exponent_le_of_forall_rpow_le {c K v κ T : ℝ} (hc : 0 < c)
    (h : ∀ t : ℝ, T ≤ t → 1 ≤ t → c * t ^ (-v) ≤ K * t ^ (-κ)) : κ ≤ v := by
  by_contra hcon
  have hpos : 0 < κ - v := sub_pos.mpr (lt_of_not_ge hcon)
  have hev : ∀ᶠ t : ℝ in atTop, c ≤ K * (t ^ (κ - v))⁻¹ := by
    filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (1 : ℝ)] with t htT ht1
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hkey := h t htT ht1
    have hvpos : (0 : ℝ) < t ^ v := Real.rpow_pos_of_pos ht0 v
    have := mul_le_mul_of_nonneg_right hkey (le_of_lt hvpos)
    rw [mul_assoc, mul_assoc, ← Real.rpow_add ht0, ← Real.rpow_add ht0,
      neg_add_cancel] at this
    rw [Real.rpow_zero, mul_one] at this
    have hrw : t ^ (-κ + v) = (t ^ (κ - v))⁻¹ := by
      rw [show -κ + v = -(κ - v) by ring, Real.rpow_neg (le_of_lt ht0)]
    rwa [hrw] at this
  have hlim : Tendsto (fun t : ℝ => K * (t ^ (κ - v))⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ (κ - v)) atTop atTop := tendsto_rpow_atTop hpos
    simpa using (h1.inv_tendsto_atTop).const_mul K
  exact absurd (ge_of_tendsto hlim hev) (not_le.mpr hc)

/-- Natural-exponent form of the exponent ceiling: a shortcut mass bounded below
by `c t^{-v}` and above by `K t^{-κ}` forces `κ ≤ v`. -/
theorem exponent_le_natCast_of_forall_le {c K κ T : ℝ} {v : ℕ} (hc : 0 < c)
    (h : ∀ t : ℝ, T ≤ t → 1 ≤ t → c * (t ^ v)⁻¹ ≤ K * t ^ (-κ)) : κ ≤ (v : ℝ) := by
  refine exponent_le_of_forall_rpow_le (K := K) (T := T) hc fun t htT ht1 => ?_
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have hrw : t ^ (-(v : ℝ)) = (t ^ v)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt ht0), Real.rpow_natCast]
  rw [hrw]
  exact h t htT ht1

end ExponentComparison

section TubeVolume

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ F]

/-- The Haar volume of a closed annulus scales as the shell radius to the
dimension. -/
theorem measure_annulus (μ : Measure E) [μ.IsAddHaarMeasure] {R : ℝ} (hR : 0 ≤ R) :
    μ (closedBall (0 : E) (2 * R) \ closedBall (0 : E) R)
      = ENNReal.ofReal ((2 ^ Module.finrank ℝ E - 1) * R ^ Module.finrank ℝ E)
        * μ (ball 0 1) := by
  have hsub : closedBall (0 : E) R ⊆ closedBall (0 : E) (2 * R) :=
    closedBall_subset_closedBall (by linarith)
  have hfin : μ (closedBall (0 : E) R) ≠ ⊤ := (measure_closedBall_lt_top).ne
  rw [measure_sdiff hsub measurableSet_closedBall.nullMeasurableSet hfin,
    Measure.addHaar_closedBall μ 0 (by linarith : (0 : ℝ) ≤ 2 * R),
    Measure.addHaar_closedBall μ 0 hR, ← ENNReal.sub_mul, ← ENNReal.ofReal_sub _ (by positivity)]
  · congr 2
    rw [mul_pow]
    ring
  · intro _ _
    exact (measure_ball_lt_top).ne

/-- **Annular tube volume.**  The tube over an annular shell in the invisible
carrier, thickened by a fixed transverse radius, has volume the product of the
annular volume and the transverse ball volume. -/
theorem measure_annulusTube (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure] [SFinite ν] {R δ : ℝ} (hR : 0 ≤ R)
    (hδ : 0 ≤ δ) :
    (μ.prod ν)
        ((closedBall (0 : E) (2 * R) \ closedBall (0 : E) R) ×ˢ closedBall (0 : F) δ)
      = ENNReal.ofReal ((2 ^ Module.finrank ℝ E - 1) * R ^ Module.finrank ℝ E)
          * μ (ball 0 1)
          * (ENNReal.ofReal (δ ^ Module.finrank ℝ F) * ν (ball 0 1)) := by
  rw [Measure.prod_prod, measure_annulus μ hR, Measure.addHaar_closedBall ν 0 hδ]

/-- The annular tube has strictly positive volume whenever the shell and the
transverse radius are nondegenerate. -/
theorem measure_annulusTube_pos (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure] [SFinite ν] {R δ : ℝ} (hR : 0 < R)
    (hδ : 0 < δ) (hE : 0 < Module.finrank ℝ E) :
    0 < (μ.prod ν)
        ((closedBall (0 : E) (2 * R) \ closedBall (0 : E) R) ×ˢ closedBall (0 : F) δ) := by
  rw [measure_annulusTube μ ν (le_of_lt hR) (le_of_lt hδ)]
  have h2 : (1 : ℝ) < 2 ^ Module.finrank ℝ E := by
    exact one_lt_pow₀ (by norm_num) hE.ne'
  have hfac : 0 < (2 ^ Module.finrank ℝ E - 1) * R ^ Module.finrank ℝ E := by
    have : 0 < R ^ Module.finrank ℝ E := pow_pos hR _
    nlinarith
  refine ENNReal.mul_pos (ENNReal.mul_pos ?_ ?_).ne' (ENNReal.mul_pos ?_ ?_).ne'
  · exact (ENNReal.ofReal_pos.mpr hfac).ne'
  · exact (measure_ball_pos μ (0 : E) one_pos).ne'
  · exact (ENNReal.ofReal_pos.mpr (pow_pos hδ _)).ne'
  · exact (measure_ball_pos ν (0 : F) one_pos).ne'

end TubeVolume

end GaloisForLFunctions.HTGeometry
