import GaloisForLFunctions.RHTower.MellinRealDecay

/-!
# The continued Mellin transform vanishes at infinity on the real axis

The bound of `MellinRealDecay` pairs the kernel `t^{-σ}` against `t^{-1}` and loses the whole
decay when the aperture is `b = 1`.  Pairing the kernel against *itself* instead keeps it: by
Cauchy--Schwarz

  `|∫_b^∞ t^{-σ} g(t) dt| ≤ (∫_b^∞ t^{-2σ} dt)^{1/2}‖g‖ = (b^{1-2σ}/(2σ-1))^{1/2}‖g‖`,

which for `b ≥ 1` is at most `‖g‖/√(2σ−1)`.  Together with the head term `d·b^{1-σ}/(σ-1)` this
gives `M(f)(σ) → 0` as `σ → +∞` for **every** aperture `b ≥ 1`, and in particular for `b = 1`.

This is the input that forces the polynomial of `BurnolQuotientGrowth` to be the zero polynomial.

## Main results

* `norm_tail_integral_sqrt_le`
* `tendsto_extendedMellinContinuation_real_atTop`
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Cauchy--Schwarz against the kernel itself.**  The tail integral decays like
`(2σ−1)^{-1/2}` even at the critical aperture. -/
theorem norm_tail_integral_sqrt_le {b : ℝ} (hb : 0 < b) (g : SoninL2) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖
      ≤ Real.sqrt (b ^ (1 - 2 * σ) / (2 * σ - 1)) * ‖g‖ := by
  have h2σ : (0 : ℝ) < 2 * σ - 1 := by linarith
  have hg2 : Integrable (fun t : ℝ => ‖(g : ℝ → ℂ) t‖ ^ 2) (volume.restrict (Ioi b)) := by
    have h := (memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).1 (Lp.memLp g)
    exact h.restrict
  have hsqeq : ∀ t : ℝ, 0 < t → (t ^ (-σ)) ^ 2 = t ^ (-(2 * σ)) := by
    intro t ht0
    rw [← Real.rpow_natCast (t ^ (-σ)) 2, ← Real.rpow_mul ht0.le]
    norm_num
    ring_nf
  have hwsq : Integrable (fun t : ℝ => (t ^ (-σ)) ^ 2) (volume.restrict (Ioi b)) := by
    have hrw : (fun t : ℝ => (t ^ (-σ)) ^ 2)
        =ᵐ[volume.restrict (Ioi b)] fun t : ℝ => t ^ (-(2 * σ)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact hsqeq t (lt_trans hb ht)
    refine Integrable.congr ?_ hrw.symm
    exact integrableOn_Ioi_rpow_of_lt (a := -(2 * σ)) (by linarith) hb
  have hcontOn : ContinuousOn (fun t : ℝ => t ^ (-σ)) (Ioi b) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans hb ht
    exact (Real.continuousAt_rpow_const t (-σ) (Or.inl (ne_of_gt ht0))).continuousWithinAt
  have hval : (∫ t in Ioi b, (t ^ (-σ)) ^ 2) = b ^ (1 - 2 * σ) / (2 * σ - 1) := by
    have hrw : (∫ t in Ioi b, (t ^ (-σ)) ^ 2) = ∫ t in Ioi b, t ^ (-(2 * σ)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      exact hsqeq t (lt_trans hb ht)
    rw [hrw, integral_Ioi_rpow_of_lt (by linarith) hb,
      show -(2 * σ) + 1 = 1 - 2 * σ from by ring]
    have h1 : (1 : ℝ) - 2 * σ ≠ 0 := by intro h; linarith
    have h2 : (2 : ℝ) * σ - 1 ≠ 0 := by intro h; linarith
    field_simp
    ring
  set K : ℝ := b ^ (1 - 2 * σ) / (2 * σ - 1) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    positivity
  have hcs : (∫ t in Ioi b, t ^ (-σ) * ‖(g : ℝ → ℂ) t‖) ^ 2
      ≤ (∫ t in Ioi b, (t ^ (-σ)) ^ 2) * ∫ t in Ioi b, ‖(g : ℝ → ℂ) t‖ ^ 2 :=
    sq_integral_mul_le (hcontOn.aestronglyMeasurable measurableSet_Ioi)
      (((Lp.memLp g).1.norm).restrict) hwsq hg2
  have hX0 : 0 ≤ ∫ t in Ioi b, t ^ (-σ) * ‖(g : ℝ → ℂ) t‖ := by
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_trans hb ht
    positivity
  have hbound : (∫ t in Ioi b, t ^ (-σ) * ‖(g : ℝ → ℂ) t‖) ≤ Real.sqrt K * ‖g‖ := by
    have hsq : (∫ t in Ioi b, t ^ (-σ) * ‖(g : ℝ → ℂ) t‖) ^ 2 ≤ (Real.sqrt K * ‖g‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK0]
      calc (∫ t in Ioi b, t ^ (-σ) * ‖(g : ℝ → ℂ) t‖) ^ 2
          ≤ K * ∫ t in Ioi b, ‖(g : ℝ → ℂ) t‖ ^ 2 := by rw [hval] at hcs; exact hcs
        _ ≤ K * ‖g‖ ^ 2 :=
            mul_le_mul_of_nonneg_left (integral_norm_sq_le_norm_sq g (Ioi b)) hK0
    have hrhs0 : (0 : ℝ) ≤ Real.sqrt K * ‖g‖ := by positivity
    nlinarith [hsq, hX0, hrhs0]
  have hpt : ∀ t ∈ Ioi b, ‖((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖
      = t ^ (-σ) * ‖(g : ℝ → ℂ) t‖ := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans hb ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    congr 2
  calc ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖
      ≤ ∫ t in Ioi b, ‖((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t in Ioi b, t ^ (-σ) * ‖(g : ℝ → ℂ) t‖ :=
        setIntegral_congr_fun measurableSet_Ioi hpt
    _ ≤ Real.sqrt K * ‖g‖ := hbound

/-- At an aperture `b ≥ 1` the tail is at most `‖g‖/√(2σ−1)`. -/
theorem norm_tail_integral_sqrt_le_one {b : ℝ} (hb : 1 ≤ b) (g : SoninL2) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖
      ≤ ‖g‖ / Real.sqrt (2 * σ - 1) := by
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have h2σ : (0 : ℝ) < 2 * σ - 1 := by linarith
  refine le_trans (norm_tail_integral_sqrt_le hb0 g hσ) ?_
  have hpow : b ^ (1 - 2 * σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hb (by linarith)
  have hle : b ^ (1 - 2 * σ) / (2 * σ - 1) ≤ 1 / (2 * σ - 1) :=
    div_le_div_of_nonneg_right hpow h2σ.le
  have hmono : Real.sqrt (b ^ (1 - 2 * σ) / (2 * σ - 1)) ≤ Real.sqrt (1 / (2 * σ - 1)) :=
    Real.sqrt_le_sqrt hle
  have hsplit : Real.sqrt (1 / (2 * σ - 1)) = 1 / Real.sqrt (2 * σ - 1) := by
    rw [Real.sqrt_div' 1 (le_of_lt h2σ)]
    simp
  calc Real.sqrt (b ^ (1 - 2 * σ) / (2 * σ - 1)) * ‖g‖
      ≤ Real.sqrt (1 / (2 * σ - 1)) * ‖g‖ := mul_le_mul_of_nonneg_right hmono (norm_nonneg _)
    _ = ‖g‖ / Real.sqrt (2 * σ - 1) := by rw [hsplit]; ring

/-! ## The limit -/

variable {a : ℝ} {f : SoninL2} {c d : ℂ}

/-- **`M(f)(σ) → 0` on the real axis, for every aperture `a ≥ 1`.** -/
theorem tendsto_extendedMellinContinuation_real_atTop (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) :
    Tendsto (fun σ : ℝ => extendedMellinContinuation a c d f ((σ : ℝ) : ℂ)) atTop (𝓝 0) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  refine squeeze_zero_norm' (a := fun σ : ℝ => ‖f‖ / Real.sqrt (2 * σ - 1) + ‖d‖ / (σ - 1)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with σ hσ
    have hre : (((σ : ℝ) : ℂ)).re = σ := by simp
    have hs0 : ((σ : ℝ) : ℂ) ≠ 0 := by
      intro h; rw [h] at hre; simp at hre; linarith
    have hs1 : ((σ : ℝ) : ℂ) ≠ 1 := by
      intro h; rw [h] at hre; simp at hre; linarith
    rw [extendedMellinContinuation_eq_right a c d f (by rw [hre]; linarith) hs0 hs1,
      extendedMellinRight]
    have htail : extendedTailMellin a c f ((σ : ℝ) : ℂ)
        = ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (f : ℝ → ℂ) t :=
      extendedTailMellin_eq ha0 hc (by rw [hre]; linarith)
    rw [htail]
    have hT := norm_tail_integral_sqrt_le_one ha f (σ := σ) (by linarith)
    have hheadnorm : ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℝ) : ℂ)) / (1 - ((σ : ℝ) : ℂ))‖
        = ‖d‖ * a ^ (1 - σ) / (σ - 1) := by
      rw [norm_div, norm_mul]
      have hb1 : ‖((a : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℝ) : ℂ))‖ = a ^ (1 - σ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ha0]
        congr 1
      have hb2 : ‖(1 : ℂ) - ((σ : ℝ) : ℂ)‖ = σ - 1 := by
        have hval : (1 : ℂ) - ((σ : ℝ) : ℂ) = ((1 - σ : ℝ) : ℂ) := by push_cast; ring
        rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        ring
      rw [hb1, hb2]
    have hheadle : ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℝ) : ℂ)) / (1 - ((σ : ℝ) : ℂ))‖
        ≤ ‖d‖ / (σ - 1) := by
      rw [hheadnorm]
      have hpow : a ^ (1 - σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
      have hpos : (0 : ℝ) < σ - 1 := by linarith
      rw [div_le_div_iff_of_pos_right hpos]
      nlinarith [norm_nonneg d, Real.rpow_nonneg ha0.le (1 - σ)]
    calc ‖(∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (f : ℝ → ℂ) t)
          + d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℝ) : ℂ)) / (1 - ((σ : ℝ) : ℂ))‖
        ≤ ‖∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (f : ℝ → ℂ) t‖
          + ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℝ) : ℂ)) / (1 - ((σ : ℝ) : ℂ))‖ :=
          norm_add_le _ _
      _ ≤ ‖f‖ / Real.sqrt (2 * σ - 1) + ‖d‖ / (σ - 1) := add_le_add hT hheadle
  · have h1 : Tendsto (fun σ : ℝ => Real.sqrt (2 * σ - 1)) atTop atTop := by
      refine Real.tendsto_sqrt_atTop.comp ?_
      exact tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
    have h2 : Tendsto (fun σ : ℝ => σ - 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_id
    have hA : Tendsto (fun σ : ℝ => ‖f‖ / Real.sqrt (2 * σ - 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h1
    have hB : Tendsto (fun σ : ℝ => ‖d‖ / (σ - 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h2
    simpa using hA.add hB

end

end RHTower
