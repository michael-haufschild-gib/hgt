import GaloisForLFunctions.RHTower.ConnesSobolevTranslationContinuity

/-!
# The translation operators of Connes' Sobolev space

Appendix I (3)-(5) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

`V(v)ξ = ξ(· − v)` is a bounded operator of `L²_δ(ℝ)` with `‖V(v)‖ ≤ (2^{δ/2} ρ_δ(v))^{1/2}`,
and `v ↦ V(v)ξ` is norm continuous: the difference of two translates is one translate of a
single difference, so continuity at an arbitrary shift follows from continuity at `0`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem connes_ae_translate {δ : ℝ} {f g : ℝ → ℂ}
    (h : f =ᵐ[connesSobolevMeasure δ] g) (v : ℝ) :
    (fun u => f (u - v)) =ᵐ[connesSobolevMeasure δ] fun u => g (u - v) := by
  have hw : Measurable (connesSobolevWeight δ) := measurable_connesSobolevWeight δ
  have hp : ∀ u, 0 < connesSobolevWeight δ u := connesSobolevWeight_pos δ
  have hv : f =ᵐ[volume] g := by
    rw [connesSobolevMeasure] at h
    exact (HTGeometry.withDensity_realDensity_ae_eq hw hp).mp h
  have hvt : (fun u => f (u - v)) =ᵐ[volume] fun u => g (u - v) :=
    (measurePreserving_sub_right volume v).quasiMeasurePreserving.ae_eq_comp hv
  rw [connesSobolevMeasure]
  exact (HTGeometry.withDensity_realDensity_ae_eq hw hp).mpr hvt

theorem connes_memLp_translate {δ : ℝ} (hδ : 0 ≤ δ) {ξ : ℝ → ℂ}
    (hξ : MemLp ξ 2 (connesSobolevMeasure δ)) (v : ℝ) :
    MemLp (fun u => ξ (u - v)) 2 (connesSobolevMeasure δ) := by
  have hvol := connes_aestronglyMeasurable_volume hξ.1
  refine ⟨connes_aestronglyMeasurable_sobolev (aestronglyMeasurable_translate hvol v), ?_⟩
  refine lt_of_le_of_lt (connes_eLpNorm_translate_le hδ hvol v) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hξ.2

/-- The translation operator `V(v)` of Connes' Sobolev space. -/
def connesTranslate {δ : ℝ} (hδ : 0 ≤ δ) (v : ℝ) (ξ : Lp ℂ 2 (connesSobolevMeasure δ)) :
    Lp ℂ 2 (connesSobolevMeasure δ) :=
  (connes_memLp_translate hδ (Lp.memLp ξ) v).toLp _

theorem connesTranslate_ae {δ : ℝ} (hδ : 0 ≤ δ) (v : ℝ)
    (ξ : Lp ℂ 2 (connesSobolevMeasure δ)) :
    (connesTranslate hδ v ξ : ℝ → ℂ)
      =ᵐ[connesSobolevMeasure δ] fun u => (ξ : ℝ → ℂ) (u - v) :=
  MemLp.coeFn_toLp _

theorem connesTranslate_zero {δ : ℝ} (hδ : 0 ≤ δ) (ξ : Lp ℂ 2 (connesSobolevMeasure δ)) :
    connesTranslate hδ 0 ξ = ξ := by
  refine Lp.ext ?_
  filter_upwards [connesTranslate_ae hδ 0 ξ] with u hu
  rw [hu, sub_zero]

theorem norm_connesTranslate_le {δ : ℝ} (hδ : 0 ≤ δ) (v : ℝ)
    (ξ : Lp ℂ 2 (connesSobolevMeasure δ)) :
    ‖connesTranslate hδ v ξ‖
      ≤ Real.sqrt (2 ^ (δ / 2) * connesSobolevWeight δ v) * ‖ξ‖ := by
  have hvol := connes_aestronglyMeasurable_volume (Lp.aestronglyMeasurable ξ)
  have hfin : eLpNorm (ξ : ℝ → ℂ) 2 (connesSobolevMeasure δ) ≠ ∞ := (Lp.memLp ξ).2.ne
  have hb := connes_eLpNorm_translate_le hδ hvol v
  have htop : ENNReal.ofReal (Real.sqrt (2 ^ (δ / 2) * connesSobolevWeight δ v))
      * eLpNorm (ξ : ℝ → ℂ) 2 (connesSobolevMeasure δ) ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hfin)).ne
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (connesTranslate_ae hδ v ξ)]
  calc (eLpNorm (fun u => (ξ : ℝ → ℂ) (u - v)) 2 (connesSobolevMeasure δ)).toReal
      ≤ (ENNReal.ofReal (Real.sqrt (2 ^ (δ / 2) * connesSobolevWeight δ v))
          * eLpNorm (ξ : ℝ → ℂ) 2 (connesSobolevMeasure δ)).toReal :=
        ENNReal.toReal_mono htop hb
    _ = Real.sqrt (2 ^ (δ / 2) * connesSobolevWeight δ v)
          * (eLpNorm (ξ : ℝ → ℂ) 2 (connesSobolevMeasure δ)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-- The difference of two translates is a single translate of one difference. -/
theorem connes_eLpNorm_translate_sub {δ : ℝ} (hδ : 0 ≤ δ) {ξ : ℝ → ℂ}
    (hξ : AEStronglyMeasurable ξ volume) (v w : ℝ) :
    eLpNorm (fun u => ξ (u - v) - ξ (u - w)) 2 (connesSobolevMeasure δ)
      ≤ ENNReal.ofReal (Real.sqrt (2 ^ (δ / 2) * connesSobolevWeight δ w))
          * eLpNorm (fun u => ξ (u - (v - w)) - ξ u) 2 (connesSobolevMeasure δ) := by
  have hdiff : AEStronglyMeasurable (fun y : ℝ => ξ (y - (v - w)) - ξ y) volume :=
    (aestronglyMeasurable_translate hξ (v - w)).sub hξ
  have key := connes_eLpNorm_translate_le hδ hdiff w
  have heq : (fun u => (fun y : ℝ => ξ (y - (v - w)) - ξ y) (u - w))
      = fun u => ξ (u - v) - ξ (u - w) := by
    funext u
    dsimp only
    have huv : u - w - (v - w) = u - v := by ring
    rw [huv]
  rwa [heq] at key

/-- **Strong continuity of the translation group on `L²_δ(ℝ)`.** -/
theorem continuous_connesTranslate {δ : ℝ} (hδ : 0 ≤ δ)
    (ξ : Lp ℂ 2 (connesSobolevMeasure δ)) :
    Continuous fun v : ℝ => connesTranslate hδ v ξ := by
  have hvol := connes_aestronglyMeasurable_volume (Lp.aestronglyMeasurable ξ)
  rw [continuous_iff_continuousAt]
  intro w
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set K : ℝ := Real.sqrt (2 ^ (δ / 2) * connesSobolevWeight δ w) with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hdiff : ∀ v : ℝ, ‖connesTranslate hδ v ξ - connesTranslate hδ w ξ‖
      ≤ K * (eLpNorm (fun u => (ξ : ℝ → ℂ) (u - (v - w)) - (ξ : ℝ → ℂ) u) 2
          (connesSobolevMeasure δ)).toReal := by
    intro v
    have hae : ((connesTranslate hδ v ξ - connesTranslate hδ w ξ : Lp ℂ 2 _) : ℝ → ℂ)
        =ᵐ[connesSobolevMeasure δ]
          fun u => (ξ : ℝ → ℂ) (u - v) - (ξ : ℝ → ℂ) (u - w) := by
      filter_upwards [Lp.coeFn_sub (connesTranslate hδ v ξ) (connesTranslate hδ w ξ),
        connesTranslate_ae hδ v ξ, connesTranslate_ae hδ w ξ] with u h1 h2 h3
      rw [h1]
      simp only [Pi.sub_apply]
      rw [h2, h3]
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
    have hfin : eLpNorm (fun u => (ξ : ℝ → ℂ) (u - (v - w)) - (ξ : ℝ → ℂ) u) 2
        (connesSobolevMeasure δ) ≠ ∞ := by
      have h1 : MemLp (fun u => (ξ : ℝ → ℂ) (u - (v - w))) 2 (connesSobolevMeasure δ) :=
        connes_memLp_translate hδ (Lp.memLp ξ) (v - w)
      exact (h1.sub (Lp.memLp ξ)).2.ne
    have htop : ENNReal.ofReal K * eLpNorm
        (fun u => (ξ : ℝ → ℂ) (u - (v - w)) - (ξ : ℝ → ℂ) u) 2 (connesSobolevMeasure δ) ≠ ∞ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hfin)).ne
    calc (eLpNorm (fun u => (ξ : ℝ → ℂ) (u - v) - (ξ : ℝ → ℂ) (u - w)) 2
            (connesSobolevMeasure δ)).toReal
        ≤ (ENNReal.ofReal K * eLpNorm
            (fun u => (ξ : ℝ → ℂ) (u - (v - w)) - (ξ : ℝ → ℂ) u) 2
              (connesSobolevMeasure δ)).toReal :=
          ENNReal.toReal_mono htop (connes_eLpNorm_translate_sub hδ hvol v w)
      _ = K * (eLpNorm (fun u => (ξ : ℝ → ℂ) (u - (v - w)) - (ξ : ℝ → ℂ) u) 2
            (connesSobolevMeasure δ)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0]
  have hshift : Tendsto (fun v : ℝ => v - w) (𝓝 w) (𝓝 0) := by
    have h : Tendsto (fun v : ℝ => v - w) (𝓝 w) (𝓝 (w - w)) :=
      tendsto_id.sub tendsto_const_nhds
    simpa using h
  have hcore : Tendsto (fun v : ℝ =>
      eLpNorm (fun u => (ξ : ℝ → ℂ) (u - (v - w)) - (ξ : ℝ → ℂ) u) 2
        (connesSobolevMeasure δ)) (𝓝 w) (𝓝 0) :=
    (connes_translation_tendsto hδ (Lp.memLp ξ)).comp hshift
  have hreal : Tendsto (fun v : ℝ =>
      K * (eLpNorm (fun u => (ξ : ℝ → ℂ) (u - (v - w)) - (ξ : ℝ → ℂ) u) 2
        (connesSobolevMeasure δ)).toReal) (𝓝 w) (𝓝 0) := by
    have htr : Tendsto (fun v : ℝ =>
        (eLpNorm (fun u => (ξ : ℝ → ℂ) (u - (v - w)) - (ξ : ℝ → ℂ) u) 2
          (connesSobolevMeasure δ)).toReal) (𝓝 w) (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal (by simp)).comp hcore
      simpa [Function.comp_def] using h
    have := htr.const_mul K
    simpa using this
  refine squeeze_zero (fun v => norm_nonneg _) hdiff hreal

end

end GaloisForLFunctions.RHTower
