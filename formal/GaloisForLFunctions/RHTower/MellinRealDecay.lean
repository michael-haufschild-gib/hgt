import GaloisForLFunctions.RHTower.MellinLineMass
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import GaloisForLFunctions.HTGeometry.L2PairingEnergy

/-!
# Exponential decay of the continued Mellin transform on the real axis

For a vector of `L_b` the Mellin transform is `O(b^{-σ})` as `σ → +∞` along the reals: the head
contributes `d·b^{1-σ}/(σ-1)` and the tail, by Cauchy--Schwarz against `t^{-1}` on `(b,∞)`, at most
`b^{1-σ}·b^{-1/2}‖g‖`.  For `b > 1` this is genuine exponential decay — the mechanism behind
Burnol's `G(s)/ζ(s) = O(A^{Re s})` with `A = 1/b < 1`.

## Main results

* `norm_tail_integral_le`
* `exists_norm_extendedMellin_real_decay`
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem integral_norm_sq_le_norm_sq (g : SoninL2) (s : Set ℝ) :
    (∫ t in s, ‖(g : ℝ → ℂ) t‖ ^ 2) ≤ ‖g‖ ^ 2 := by
  have hfull : (∫ t : ℝ, ‖(g : ℝ → ℂ) t‖ ^ 2) = ‖g‖ ^ 2 :=
    (HTGeometry.norm_l2_sq_eq_integral_norm_sq (volume : Measure ℝ) g).symm
  have hint : Integrable (fun t : ℝ => ‖(g : ℝ → ℂ) t‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).1 (Lp.memLp g)
  rw [← hfull]
  refine setIntegral_le_integral hint ?_
  filter_upwards with t
  positivity

theorem norm_tail_integral_le {b : ℝ} (hb : 0 < b) (g : SoninL2) {σ : ℝ} (hσ : 1 ≤ σ) :
    ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖
      ≤ b ^ (1 - σ) * (b ^ (-(1 / 2) : ℝ) * ‖g‖) := by
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
    have := integrableOn_Ioi_rpow_of_lt (a := (-(2:ℝ))) (by norm_num) hb
    exact this
  -- the pointwise bound
  have hpt : ∀ t ∈ Ioi b, ‖((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖
      ≤ b ^ (1 - σ) * (t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖) := by
    intro t ht
    have ht0 : (0:ℝ) < t := lt_trans hb ht
    have hker : ‖((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ))‖ = t ^ (-σ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      congr 1
    have hsplit : t ^ (-σ) = t ^ (1 - σ) * t ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    have hmono : t ^ (1 - σ) ≤ b ^ (1 - σ) :=
      Real.rpow_le_rpow_of_nonpos hb (le_of_lt ht) (by linarith)
    rw [norm_mul, hker, hsplit, mul_assoc]
    refine mul_le_mul_of_nonneg_right hmono ?_
    positivity
  -- Cauchy--Schwarz on the majorant
  have hcs : (∫ t in Ioi b, t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖) ^ 2
      ≤ (∫ t in Ioi b, (t ^ (-(1 : ℝ))) ^ 2) * ∫ t in Ioi b, ‖(g : ℝ → ℂ) t‖ ^ 2 := by
    refine sq_integral_mul_le ?_ ?_ hinvsq hg2
    · have hcontOn : ContinuousOn (fun t : ℝ => t ^ (-(1:ℝ))) (Ioi b) := by
        intro t ht
        have ht0 : (0:ℝ) < t := lt_trans hb ht
        exact (Real.continuousAt_rpow_const t (-(1:ℝ)) (Or.inl (ne_of_gt ht0))).continuousWithinAt
      exact hcontOn.aestronglyMeasurable measurableSet_Ioi
    · exact ((Lp.memLp g).1.norm).restrict
  have hval : (∫ t in Ioi b, (t ^ (-(1 : ℝ))) ^ 2) = b ^ (-(1 : ℝ)) := by
    have hrw : (∫ t in Ioi b, (t ^ (-(1 : ℝ))) ^ 2) = ∫ t in Ioi b, t ^ (-(2 : ℝ)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : (0:ℝ) < t := lt_trans hb ht
      rw [← Real.rpow_natCast (t ^ (-(1:ℝ))) 2, ← Real.rpow_mul ht0.le]
      norm_num
    rw [hrw, integral_Ioi_rpow_of_lt (by norm_num) hb]
    rw [show (-(2:ℝ)) + 1 = -1 by ring]
    field_simp
  -- assemble
  have hintegrand : IntegrableOn
      (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t) (Ioi b) volume := by
    refine integrableOn_cpow_mul_Ioi hb g ?_
    simp only [Complex.ofReal_re]
    linarith
  have hmaj : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖) (Ioi b) volume := by
    have hcontOn : ContinuousOn (fun t : ℝ => t ^ (-(1:ℝ))) (Ioi b) := by
      intro t ht
      have ht0 : (0:ℝ) < t := lt_trans hb ht
      exact (Real.continuousAt_rpow_const t (-(1:ℝ)) (Or.inl (ne_of_gt ht0))).continuousWithinAt
    exact integrable_mul_of_sq_integrable (hcontOn.aestronglyMeasurable measurableSet_Ioi)
      (((Lp.memLp g).1.norm).restrict) hinvsq hg2
  have hstep1 : ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖
      ≤ ∫ t in Ioi b, ‖((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖ :=
    norm_integral_le_integral_norm _
  have hstep2 : (∫ t in Ioi b, ‖((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖)
      ≤ ∫ t in Ioi b, b ^ (1 - σ) * (t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖) := by
    refine setIntegral_mono_on hintegrand.norm (hmaj.const_mul _) measurableSet_Ioi ?_
    exact hpt
  have hstep3 : (∫ t in Ioi b, b ^ (1 - σ) * (t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖))
      = b ^ (1 - σ) * ∫ t in Ioi b, t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖ := by
    rw [integral_const_mul]
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
        _ ≤ b ^ (-(1:ℝ)) * ‖g‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_left hg hb1
    have hrhs0 : (0:ℝ) ≤ b ^ (-(1 / 2) : ℝ) * ‖g‖ := by positivity
    nlinarith [hsq, hX0, hrhs0]
  have hpow0 : (0:ℝ) ≤ b ^ (1 - σ) := by positivity
  calc ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖
      ≤ ∫ t in Ioi b, ‖((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖ := hstep1
    _ ≤ ∫ t in Ioi b, b ^ (1 - σ) * (t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖) := hstep2
    _ = b ^ (1 - σ) * ∫ t in Ioi b, t ^ (-(1 : ℝ)) * ‖(g : ℝ → ℂ) t‖ := hstep3
    _ ≤ b ^ (1 - σ) * (b ^ (-(1 / 2) : ℝ) * ‖g‖) := mul_le_mul_of_nonneg_left hbound hpow0

/-! ## The decay of the continued transform -/

/-- **Exponential decay on the real axis.**  For a vector of `L_b` the continued Mellin transform
is `O(b^{-σ})` — genuine exponential decay when `b > 1`. -/
theorem exists_norm_extendedMellin_real_decay {b : ℝ} (hb : 0 < b) {g : SoninL2} {c d : ℂ}
    (hev : g ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval b →
      ((fourierUnitary g : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (g : ℝ → ℂ) t = d) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 2 ≤ σ →
      ‖extendedMellinContinuation b c d g ((σ : ℝ) : ℂ)‖ ≤ C * b ^ (-σ) := by
  refine ⟨‖d‖ * b + b ^ (1 / 2 : ℝ) * ‖g‖ + 1, by positivity, ?_⟩
  intro σ hσ
  have hre : (((σ : ℝ) : ℂ)).re = σ := by simp
  have hs0 : ((σ : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hre; simp at hre; linarith
  have hs1 : ((σ : ℝ) : ℂ) ≠ 1 := by
    intro h; rw [h] at hre; simp at hre; linarith
  rw [extendedMellinContinuation_eq_right b c d g (by rw [hre]; linarith) hs0 hs1,
    extendedMellinRight]
  have htail : extendedTailMellin b c g ((σ : ℝ) : ℂ)
      = ∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t :=
    extendedTailMellin_eq hb hc (by rw [hre]; linarith)
  rw [htail]
  have hT := norm_tail_integral_le hb g (σ := σ) (by linarith)
  -- the head
  have hheadnorm : ‖d * ((b : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℝ) : ℂ)) / (1 - ((σ : ℝ) : ℂ))‖
      = ‖d‖ * b ^ (1 - σ) / (σ - 1) := by
    rw [norm_div, norm_mul]
    have hb1 : ‖((b : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℝ) : ℂ))‖ = b ^ (1 - σ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hb]
      congr 1
    have hb2 : ‖(1 : ℂ) - ((σ : ℝ) : ℂ)‖ = σ - 1 := by
      have hval : (1 : ℂ) - ((σ : ℝ) : ℂ) = ((1 - σ : ℝ) : ℂ) := by push_cast; ring
      rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    rw [hb1, hb2]
  have hheadle : ‖d * ((b : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℝ) : ℂ)) / (1 - ((σ : ℝ) : ℂ))‖
      ≤ ‖d‖ * b * b ^ (-σ) := by
    rw [hheadnorm]
    have hsplit : b ^ (1 - σ) = b * b ^ (-σ) := by
      rw [show (1 : ℝ) - σ = 1 + -σ by ring, Real.rpow_add hb, Real.rpow_one]
    rw [hsplit]
    have hpos : (0:ℝ) < σ - 1 := by linarith
    have hle1 : (1:ℝ) ≤ σ - 1 := by linarith
    have hnn : (0:ℝ) ≤ ‖d‖ * (b * b ^ (-σ)) := by positivity
    rw [div_le_iff₀ hpos]
    nlinarith [hnn]
  have htaille : ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖
      ≤ b ^ (1 / 2 : ℝ) * ‖g‖ * b ^ (-σ) := by
    refine le_trans hT ?_
    have hrw : b ^ (1 - σ) * (b ^ (-(1 / 2) : ℝ) * ‖g‖)
        = b ^ (1 / 2 : ℝ) * ‖g‖ * b ^ (-σ) := by
      rw [show (1 : ℝ) - σ = 1 + -σ by ring, Real.rpow_add hb, Real.rpow_one]
      rw [show (1 : ℝ) / 2 = 1 + -(1 / 2 : ℝ) by ring, Real.rpow_add hb, Real.rpow_one]
      ring
    rw [hrw]
  have hpow0 : (0:ℝ) < b ^ (-σ) := Real.rpow_pos_of_pos hb _
  calc ‖(∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t)
        + d * ((b : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℝ) : ℂ)) / (1 - ((σ : ℝ) : ℂ))‖
      ≤ ‖∫ t in Ioi b, ((t : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) * (g : ℝ → ℂ) t‖
        + ‖d * ((b : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℝ) : ℂ)) / (1 - ((σ : ℝ) : ℂ))‖ :=
        norm_add_le _ _
    _ ≤ b ^ (1 / 2 : ℝ) * ‖g‖ * b ^ (-σ) + ‖d‖ * b * b ^ (-σ) := by
        exact add_le_add htaille hheadle
    _ ≤ (‖d‖ * b + b ^ (1 / 2 : ℝ) * ‖g‖ + 1) * b ^ (-σ) := by
        have h1 : (0:ℝ) ≤ b ^ (-σ) := hpow0.le
        nlinarith [h1]

end

end RHTower
