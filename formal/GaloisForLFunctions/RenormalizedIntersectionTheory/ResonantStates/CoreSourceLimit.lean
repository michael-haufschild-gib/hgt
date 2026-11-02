import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.CoreSourceSquare
import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.CoreSourceDephasing

/-!
# Weak limit of the normalized compact-core Hecke residual

The two Weyl-source masses survive, while their interference dephases. The
limiting density retains the real resonance parameter.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

-- Extend the positive-height formulas continuously away from the integration rectangle.
private def sourceY (p : ℝ × ℝ) : ℝ := max 1 p.2
private def sourceH (p : ℝ × ℝ) : ℝ := 2 * sourceY p / (p.1 ^ 2 + sourceY p ^ 2)
private def sourceG (p : ℝ × ℝ) : ℝ := 4 / (p.1 ^ 2 + sourceY p ^ 2)

private theorem sourceY_pos (p : ℝ × ℝ) : 0 < sourceY p :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

private theorem sourceDen_pos (p : ℝ × ℝ) : 0 < p.1 ^ 2 + sourceY p ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (sourceY_pos p))

private theorem sourceH_pos (p : ℝ × ℝ) : 0 < sourceH p :=
  div_pos (mul_pos (by norm_num) (sourceY_pos p)) (sourceDen_pos p)

private theorem sourceG_pos (p : ℝ × ℝ) : 0 < sourceG p :=
  div_pos (by norm_num) (sourceDen_pos p)

private theorem sourceY_continuous : Continuous sourceY := continuous_const.max continuous_snd

private theorem sourceH_continuous : Continuous sourceH :=
  (continuous_const.mul sourceY_continuous).div
    ((continuous_fst.pow 2).add (sourceY_continuous.pow 2)) (fun p => (sourceDen_pos p).ne')

private theorem sourceG_continuous : Continuous sourceG :=
  continuous_const.div ((continuous_fst.pow 2).add (sourceY_continuous.pow 2))
    (fun p => (sourceDen_pos p).ne')

private def sourceDiagonal (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  (-2 * a) / 2 * (sourceH p ^ (1 / 2 - a)) ^ 2 *
    ((2 * sourceG p ^ (a - 1 / 2)) ^ 2 + 1) / sourceY p ^ 2

private def sourceCross (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  (-2 * a) / 2 * (sourceH p ^ (1 / 2 - a)) ^ 2 *
    (4 * sourceG p ^ (a - 1 / 2)) / sourceY p ^ 2

private theorem sourceDiagonal_continuous : Continuous (Function.uncurry sourceDiagonal) := by
  have hh : Continuous (fun q : ℝ × (ℝ × ℝ) => sourceH q.2 ^ (1 / 2 - q.1)) :=
    (sourceH_continuous.comp continuous_snd).rpow (by fun_prop)
      (fun q => Or.inl (sourceH_pos q.2).ne')
  have hg : Continuous (fun q : ℝ × (ℝ × ℝ) => sourceG q.2 ^ (q.1 - 1 / 2)) :=
    (sourceG_continuous.comp continuous_snd).rpow (by fun_prop)
      (fun q => Or.inl (sourceG_pos q.2).ne')
  exact ((((continuous_const.mul continuous_fst).div_const 2).mul (hh.pow 2)).mul
    ((continuous_const.mul hg).pow 2 |>.add continuous_const)).div
      ((sourceY_continuous.comp continuous_snd).pow 2)
      (fun q => (sq_pos_of_pos (sourceY_pos q.2)).ne')

private theorem sourceCross_continuous : Continuous (Function.uncurry sourceCross) := by
  have hh : Continuous (fun q : ℝ × (ℝ × ℝ) => sourceH q.2 ^ (1 / 2 - q.1)) :=
    (sourceH_continuous.comp continuous_snd).rpow (by fun_prop)
      (fun q => Or.inl (sourceH_pos q.2).ne')
  have hg : Continuous (fun q : ℝ × (ℝ × ℝ) => sourceG q.2 ^ (q.1 - 1 / 2)) :=
    (sourceG_continuous.comp continuous_snd).rpow (by fun_prop)
      (fun q => Or.inl (sourceG_pos q.2).ne')
  exact ((((continuous_const.mul continuous_fst).div_const 2).mul (hh.pow 2)).mul
    (continuous_const.mul hg)).div ((sourceY_continuous.comp continuous_snd).pow 2)
      (fun q => (sq_pos_of_pos (sourceY_pos q.2)).ne')

private theorem sourceDiagonal_eq (a : ℝ) (p : ℝ × ℝ) :
    sourceDiagonal a p = (-2 * a) *
      ((2 : ℝ) ^ (2 * a) * sourceY p ^ (1 - 2 * a) +
        sourceH p ^ (1 - 2 * a) / 2) / sourceY p ^ 2 := by
  have hsq (x : ℝ) (hx : 0 < x) : (x ^ (1 / 2 - a)) ^ 2 = x ^ (1 - 2 * a) := by
    simpa only [half_sub_re, Complex.ofReal_re] using rpow_half_sub_sq hx (a : ℂ)
  have hscale : sourceH p = (sourceY p / 2) * sourceG p := by
    unfold sourceH sourceG
    ring
  have hm : sourceH p ^ (1 / 2 - a) * sourceG p ^ (a - 1 / 2) =
      (sourceY p / 2) ^ (1 / 2 - a) := by
    rw [hscale, Real.mul_rpow (half_pos (sourceY_pos p)).le (sourceG_pos p).le,
      show a - 1 / 2 = -(1 / 2 - a) by ring, Real.rpow_neg (sourceG_pos p).le,
      mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos (sourceG_pos p) _).ne', mul_one]
  have htwo : (2 : ℝ) ^ (2 * a) * (2 : ℝ) ^ (1 - 2 * a) = 2 := by
    rw [← Real.rpow_add (by norm_num), show 2 * a + (1 - 2 * a) = (1 : ℝ) by ring,
      Real.rpow_one]
  have hfirst : (sourceH p ^ (1 / 2 - a)) ^ 2 / 2 *
      (2 * sourceG p ^ (a - 1 / 2)) ^ 2 =
      (2 : ℝ) ^ (2 * a) * sourceY p ^ (1 - 2 * a) := by
    calc
      _ = 2 * (sourceH p ^ (1 / 2 - a) * sourceG p ^ (a - 1 / 2)) ^ 2 := by ring
      _ = 2 * (sourceY p / 2) ^ (1 - 2 * a) := by
        rw [hm, hsq _ (half_pos (sourceY_pos p))]
      _ = (2 / (2 : ℝ) ^ (1 - 2 * a)) * sourceY p ^ (1 - 2 * a) := by
        rw [Real.div_rpow (sourceY_pos p).le (by norm_num)]
        ring
      _ = _ := by
        rw [(div_eq_iff (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne').mpr
          htwo.symm]
  calc
    sourceDiagonal a p = (-2 * a) *
        ((sourceH p ^ (1 / 2 - a)) ^ 2 / 2 * (2 * sourceG p ^ (a - 1 / 2)) ^ 2 +
          (sourceH p ^ (1 / 2 - a)) ^ 2 / 2) / sourceY p ^ 2 := by
      unfold sourceDiagonal
      ring
    _ = _ := by rw [hfirst, hsq _ (sourceH_pos p)]

/-- Density in Euclidean coordinates; the factor `y⁻²` is hyperbolic area. -/
def coreSourceLimitDensity (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  (-2 * a) * ((2 : ℝ) ^ (2 * a) * p.2 ^ (1 - 2 * a) +
    (2 * p.2 / (p.1 ^ 2 + p.2 ^ 2)) ^ (1 - 2 * a) / 2) / p.2 ^ 2

/-- Every negative limiting real parameter leaves a strictly positive source density. -/
theorem coreSourceLimitDensity_pos {a : ℝ} (ha : a < 0)
    {p : ℝ × ℝ} (hp : p ∈ coreSourceRect) : 0 < coreSourceLimitDensity a p := by
  have hy := coreSourceRect_height_pos hp
  have hd : 0 < p.1 ^ 2 + p.2 ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hy)
  have hh : 0 < 2 * p.2 / (p.1 ^ 2 + p.2 ^ 2) :=
    div_pos (mul_pos (by norm_num) hy) hd
  unfold coreSourceLimitDensity
  exact div_pos (mul_pos (by linarith) (add_pos
    (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hy _))
    (div_pos (Real.rpow_pos_of_pos hh _) (by norm_num)))) (sq_pos_of_pos hy)

private theorem sourceY_eq {p : ℝ × ℝ} (hp : p ∈ coreSourceRect) : sourceY p = p.2 :=
  max_eq_right (by linarith [hp.2.1])

private theorem sourceDiagonal_eq_density (a : ℝ) {p : ℝ × ℝ} (hp : p ∈ coreSourceRect) :
    sourceDiagonal a p = coreSourceLimitDensity a p := by
  rw [sourceDiagonal_eq]
  simp only [sourceH, sourceY_eq hp, coreSourceLimitDensity]

private theorem normalized_residual_eq {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hur : u.re < 0) (hAu : msA u = 0)
    {p : ℝ × ℝ} (hp : p ∈ coreSourceRect) :
    (‖dyadicEigenResidual u (ofComplex ⟨p.1, p.2⟩)‖ ^ 2 /
      (∫ w in fd, ‖truncatedLineModel u 1 w‖ ^ 2)) / p.2 ^ 2 =
      sourceDiagonal u.re p - sourceCross u.re p * Real.cos (u.im * coreSourcePhase p) := by
  let z : ℍ := ⟨⟨p.1, p.2⟩, coreSourceRect_height_pos hp⟩
  have he : ofComplex (⟨p.1, p.2⟩ : ℂ) = z := by
    rw [ofComplex_apply_of_im_pos (coreSourceRect_height_pos hp)]
  have hz : z ∈ coreRectangle := ⟨abs_le.mpr hp.1, hp.2⟩
  rw [he, dyadicEigenResidual_normalized_expansion hu hur hAu hz]
  simp only [sourceDiagonal, sourceCross, sourceH, sourceG, sourceY_eq hp,
    returnHeight, returnRatio, coreSourcePhase, z, Int.cast_zero, add_zero]
  ring

/-- Weak convergence of the actual normalized residual on the complete single-return rectangle. -/
theorem dyadicEigenResidual_core_weak_limit
    {u : ℕ → ℂ} (hu : ∀ n, u n ∈ eisensteinLineDomain)
    (hur : ∀ n, (u n).re < 0) (hAu : ∀ n, msA (u n) = 0)
    {a : ℝ} (ha : Tendsto (fun n => (u n).re) atTop (𝓝 a))
    (ht : Tendsto (fun n => (u n).im) atTop atTop)
    (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun n => ∫ p in coreSourceRect,
      f p * (‖dyadicEigenResidual (u n) (ofComplex ⟨p.1, p.2⟩)‖ ^ 2 /
        (∫ w in fd, ‖truncatedLineModel (u n) 1 w‖ ^ 2)) / p.2 ^ 2)
      atTop (𝓝 (∫ p in coreSourceRect, f p * coreSourceLimitDensity a p)) := by
  have hD : Continuous (fun q : ℝ × (ℝ × ℝ) => f q.2 * sourceDiagonal q.1 q.2) :=
    (hf.comp continuous_snd).mul sourceDiagonal_continuous
  have hC : Continuous (fun q : ℝ × (ℝ × ℝ) => f q.2 * sourceCross q.1 q.2) :=
    (hf.comp continuous_snd).mul sourceCross_continuous
  have hlimD := (continuous_parametric_integral_of_continuous hD coreSourceRect_compact).
    continuousAt.tendsto.comp ha
  have hlimC := coreSourcePhase_varying_cos_dephases
    (fun v p => f p * sourceCross v p) hC ha ht
  have hlim := hlimD.sub hlimC
  have he : (∫ p in coreSourceRect, f p * sourceDiagonal a p) =
      ∫ p in coreSourceRect, f p * coreSourceLimitDensity a p :=
    setIntegral_congr_fun coreSourceRect_measurable
      (fun p hp => by rw [sourceDiagonal_eq_density a hp])
  simp only [sub_zero, he] at hlim
  refine hlim.congr fun n => ?_
  simp only [Function.comp_apply]
  have hp : Continuous (fun p : ℝ × ℝ => ((u n).re, p)) := by fun_prop
  have hc : ContinuousOn (fun p => Real.cos ((u n).im * coreSourcePhase p)) coreSourceRect :=
    Real.continuous_cos.comp_continuousOn (continuousOn_const.mul coreSourcePhase_continuousOn)
  rw [← integral_sub
    (ContinuousOn.integrableOn_compact coreSourceRect_compact (hD.comp hp).continuousOn)
    (ContinuousOn.integrableOn_compact coreSourceRect_compact ((hC.comp hp).continuousOn.mul hc))]
  refine setIntegral_congr_fun coreSourceRect_measurable fun p hp => ?_
  have hn := normalized_residual_eq (hu n) (hur n) (hAu n) hp
  linear_combination -(f p) * hn

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
