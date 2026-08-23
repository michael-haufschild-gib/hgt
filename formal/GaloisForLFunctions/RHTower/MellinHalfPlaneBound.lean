import GaloisForLFunctions.RHTower.MellinRealDecay

/-!
# The aperture bound on a half-plane

The estimate of `MellinRealDecay` holds verbatim for complex `s` with `Re s ≥ 2`, because the
kernel obeys `‖t^{-s}‖ = t^{-Re s}`.  For `a = 1` it says the continued Mellin transform is
*bounded* on `Re s ≥ 2` — which is exactly what makes the `a = 1` case of Burnol's Proposition 6.1
reachable without Krein's theorem.

## Main results

* `norm_tail_integral_halfPlane_le`
* `exists_norm_extendedMellin_halfPlane_le`
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem norm_tail_integral_halfPlane_le {b : ℝ} (hb : 0 < b) (g : SoninL2) {s : ℂ}
    (hs : 1 ≤ s.re) :
    ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t‖
      ≤ b ^ (1 - s.re) * (b ^ (-(1 / 2) : ℝ) * ‖g‖) := by
  have hg2 : Integrable (fun t : ℝ => ‖(g : ℝ → ℂ) t‖ ^ 2) (volume.restrict (Ioi b)) := by
    have h := (memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).1 (Lp.memLp g)
    exact h.restrict
  have hinvsq : Integrable (fun t : ℝ => (t ^ (-(1 : ℝ))) ^ 2) (volume.restrict (Ioi b)) := by
    have hrw : (fun t : ℝ => (t ^ (-(1 : ℝ))) ^ 2)
        =ᵐ[volume.restrict (Ioi b)] fun t : ℝ => t ^ (-(2 : ℝ)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := lt_trans hb ht
      rw [← Real.rpow_natCast (t ^ (-(1:ℝ))) 2, ← Real.rpow_mul ht0.le]
      norm_num
    refine Integrable.congr ?_ hrw.symm
    exact integrableOn_Ioi_rpow_of_lt (a := (-(2:ℝ))) (by norm_num) hb
  have hcontOn : ContinuousOn (fun t : ℝ => t ^ (-(1:ℝ))) (Ioi b) := by
    intro t ht
    have ht0 : (0:ℝ) < t := lt_trans hb ht
    exact (Real.continuousAt_rpow_const t (-(1:ℝ)) (Or.inl (ne_of_gt ht0))).continuousWithinAt
  have hpt : ∀ t ∈ Ioi b, ‖((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t‖
      ≤ b ^ (1 - s.re) * (t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖) := by
    intro t ht
    have ht0 : (0:ℝ) < t := lt_trans hb ht
    have hker : ‖((t : ℝ) : ℂ) ^ (-s)‖ = t ^ (-s.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      congr 1
    have hsplit : t ^ (-s.re) = t ^ (1 - s.re) * t ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    have hmono : t ^ (1 - s.re) ≤ b ^ (1 - s.re) :=
      Real.rpow_le_rpow_of_nonpos hb (le_of_lt ht) (by linarith)
    rw [norm_mul, hker, hsplit, mul_assoc]
    refine mul_le_mul_of_nonneg_right hmono ?_
    positivity
  have hcs : (∫ t in Ioi b, t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖) ^ 2
      ≤ (∫ t in Ioi b, (t ^ (-(1 : ℝ))) ^ 2) * ∫ t in Ioi b, ‖(g : ℝ → ℂ) t‖ ^ 2 := by
    refine sq_integral_mul_le (hcontOn.aestronglyMeasurable measurableSet_Ioi)
      (((Lp.memLp g).1.norm).restrict) hinvsq hg2
  have hval : (∫ t in Ioi b, (t ^ (-(1 : ℝ))) ^ 2) = b ^ (-(1 : ℝ)) := by
    have hrw : (∫ t in Ioi b, (t ^ (-(1 : ℝ))) ^ 2) = ∫ t in Ioi b, t ^ (-(2 : ℝ)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : (0:ℝ) < t := lt_trans hb ht
      rw [← Real.rpow_natCast (t ^ (-(1:ℝ))) 2, ← Real.rpow_mul ht0.le]
      norm_num
    rw [hrw, integral_Ioi_rpow_of_lt (by norm_num) hb]
    rw [show (-(2:ℝ)) + 1 = -1 by ring]
    field_simp
  have hintegrand : IntegrableOn
      (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t) (Ioi b) volume :=
    integrableOn_cpow_mul_Ioi hb g (by linarith)
  have hmaj : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖) (Ioi b) volume :=
    integrable_mul_of_sq_integrable (hcontOn.aestronglyMeasurable measurableSet_Ioi)
      (((Lp.memLp g).1.norm).restrict) hinvsq hg2
  have hX0 : 0 ≤ ∫ t in Ioi b, t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖ := by
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := lt_trans hb ht
    positivity
  have hbound : (∫ t in Ioi b, t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖) ≤ b ^ (-(1 / 2) : ℝ) * ‖g‖ := by
    have hsq : (∫ t in Ioi b, t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖) ^ 2
        ≤ (b ^ (-(1 / 2) : ℝ) * ‖g‖) ^ 2 := by
      have hle := hcs
      rw [hval] at hle
      have hg := integral_norm_sq_le_norm_sq g (Ioi b)
      have hb1 : (0:ℝ) ≤ b ^ (-(1:ℝ)) := by positivity
      have hrhs : (b ^ (-(1 / 2) : ℝ) * ‖g‖) ^ 2 = b ^ (-(1:ℝ)) * ‖g‖ ^ 2 := by
        rw [mul_pow, ← Real.rpow_natCast (b ^ (-(1/2 : ℝ))) 2, ← Real.rpow_mul hb.le]
        norm_num
      rw [hrhs]
      calc (∫ t in Ioi b, t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖) ^ 2
          ≤ b ^ (-(1:ℝ)) * ∫ t in Ioi b, ‖(g : ℝ → ℂ) t‖ ^ 2 := hle
        _ ≤ b ^ (-(1:ℝ)) * ‖g‖ ^ 2 := mul_le_mul_of_nonneg_left hg hb1
    have hrhs0 : (0:ℝ) ≤ b ^ (-(1 / 2) : ℝ) * ‖g‖ := by positivity
    nlinarith [hsq, hX0, hrhs0]
  have hpow0 : (0:ℝ) ≤ b ^ (1 - s.re) := by positivity
  calc ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t‖
      ≤ ∫ t in Ioi b, ‖((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi b, b ^ (1 - s.re) * (t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖) := by
        exact setIntegral_mono_on hintegrand.norm (hmaj.const_mul _) measurableSet_Ioi hpt
    _ = b ^ (1 - s.re) * ∫ t in Ioi b, t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖ := by
        rw [integral_const_mul]
    _ ≤ b ^ (1 - s.re) * (b ^ (-(1 / 2) : ℝ) * ‖g‖) := mul_le_mul_of_nonneg_left hbound hpow0

/-- **The aperture bound on the half-plane `Re s ≥ 2`.** -/
theorem exists_norm_extendedMellin_halfPlane_le {b : ℝ} (hb : 0 < b) {g : SoninL2} {c d : ℂ}
    (hev : g ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval b →
      ((fourierUnitary g : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (g : ℝ → ℂ) t = d) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ s.re →
      ‖extendedMellinContinuation b c d g s‖ ≤ C * b ^ (-s.re) := by
  refine ⟨‖d‖ * b + b ^ (1 / 2 : ℝ) * ‖g‖ + 1, by positivity, ?_⟩
  intro s hs
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  rw [extendedMellinContinuation_eq_right b c d g (by linarith) hs0 hs1, extendedMellinRight]
  have htail : extendedTailMellin b c g s = ∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t :=
    extendedTailMellin_eq hb hc (by linarith)
  rw [htail]
  have hT := norm_tail_integral_halfPlane_le hb g (s := s) (by linarith)
  -- the head
  have hone : (1 : ℝ) ≤ ‖(1 : ℂ) - s‖ := by
    have hre : ((1 : ℂ) - s).re = 1 - s.re := by simp
    have h := Complex.abs_re_le_norm ((1 : ℂ) - s)
    rw [hre] at h
    have : (1:ℝ) ≤ |1 - s.re| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    linarith
  have hheadle : ‖d * ((b : ℝ) : ℂ) ^ ((1 : ℂ) - s) / ((1 : ℂ) - s)‖
      ≤ ‖d‖ * b * b ^ (-s.re) := by
    rw [norm_div, norm_mul]
    have hb1 : ‖((b : ℝ) : ℂ) ^ ((1 : ℂ) - s)‖ = b ^ (1 - s.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hb]
      congr 1
    rw [hb1]
    have hsplit : b ^ (1 - s.re) = b * b ^ (-s.re) := by
      rw [show (1 : ℝ) - s.re = 1 + -s.re by ring, Real.rpow_add hb, Real.rpow_one]
    rw [hsplit]
    have hpos : (0:ℝ) < ‖(1 : ℂ) - s‖ := by linarith
    rw [div_le_iff₀ hpos]
    have hnn : (0:ℝ) ≤ ‖d‖ * (b * b ^ (-s.re)) := by positivity
    nlinarith [hnn]
  have htaille : ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t‖
      ≤ b ^ (1 / 2 : ℝ) * ‖g‖ * b ^ (-s.re) := by
    refine le_trans hT ?_
    have hrw : b ^ (1 - s.re) * (b ^ (-(1 / 2) : ℝ) * ‖g‖)
        = b ^ (1 / 2 : ℝ) * ‖g‖ * b ^ (-s.re) := by
      rw [show (1 : ℝ) - s.re = 1 + -s.re by ring, Real.rpow_add hb, Real.rpow_one]
      rw [show (1 : ℝ) / 2 = 1 + -(1 / 2 : ℝ) by ring, Real.rpow_add hb, Real.rpow_one]
      ring
    rw [hrw]
  have hpow0 : (0:ℝ) < b ^ (-s.re) := Real.rpow_pos_of_pos hb _
  calc ‖(∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t)
        + d * ((b : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s)‖
      ≤ ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-s) * (g : ℝ → ℂ) t‖
        + ‖d * ((b : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s)‖ := norm_add_le _ _
    _ ≤ b ^ (1 / 2 : ℝ) * ‖g‖ * b ^ (-s.re) + ‖d‖ * b * b ^ (-s.re) := add_le_add htaille hheadle
    _ ≤ (‖d‖ * b + b ^ (1 / 2 : ℝ) * ‖g‖ + 1) * b ^ (-s.re) := by nlinarith [hpow0.le]

end

end RHTower
