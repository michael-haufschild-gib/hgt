import GaloisForLFunctions.RHTower.Sieve.PerronKernelResidue
import GaloisForLFunctions.HTGeometry.PerronKernelSegments

/-!
# Perron's lemma below the cutoff

For `0 < y < 1` the truncated vertical integral of the Perron kernel is small:

`‖∫_{-T}^{T} y^{σ+it}/(σ+it) dt‖ ≤ 2 y^σ/(|T| |log y|)`,   `σ > 0`, `T > 0`.

The proof is the rectangle `[σ, A] × [-T, T]`, which lies in the right half-plane and therefore contains
no pole, so its boundary integral vanishes (PNTPlus's `HolomorphicOn.vanishesOnRectangle`).  The two
horizontal sides are `≤ y^σ/(|T| |log y|)` each and the far vertical side is `≤ 2T y^A/|A|`, all
uniformly in `A`; letting `A → ∞` kills the far side because `y^A → 0`.

This is the `y < 1` half of Perron's lemma.  The `y > 1` half is the same rectangle to the *left*, whose
interior contains the origin, so its value is the residue `1` rather than `0`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Topology Filter GaloisForLFunctions.HTGeometry

/-- **Perron's lemma below the cutoff.**  For `0 < y < 1` the truncated vertical integral of `y^s/s` is
small: the rectangle to the right of the line contains no pole, its far edge vanishes as the abscissa
runs to infinity, and each horizontal side is `O(y^σ/(T|log y|))`. -/
theorem norm_vertical_perron_le_of_lt_one {y : ℝ} (hy0 : 0 < y) (hy : y < 1) {σ T : ℝ}
    (hσ : 0 < σ) (hT : 0 < T) :
    ‖∫ t in (-T)..T, ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * Complex.I))
        / ((σ : ℂ) + (t : ℝ) * Complex.I)‖
      ≤ 2 * (y ^ σ / (|T| * |Real.log y|)) := by
  set f : ℂ → ℂ := fun s => (y : ℂ) ^ s / s with hf
  have hTne : T ≠ 0 := hT.ne'
  have hholo : HolomorphicOn f {s : ℂ | 0 < s.re} := by
    intro s hs
    have hsne : s ≠ 0 := by
      intro h
      rw [h] at hs
      simp at hs
    refine DifferentiableWithinAt.div ?_ differentiableWithinAt_id hsne
    have hy0C : ((y : ℂ)) ≠ 0 := by simpa using hy0.ne'
    exact (differentiableAt_id.const_cpow (Or.inl hy0C)).differentiableWithinAt
  have hkey : ∀ A : ℝ, σ ≤ A →
      ‖∫ t in (-T)..T, f ((σ : ℂ) + (t : ℝ) * Complex.I)‖
        ≤ 2 * (y ^ σ / (|T| * |Real.log y|)) + 2 * T * (y ^ A / |A|) := by
    intro A hA
    have hApos : 0 < A := lt_of_lt_of_le hσ hA
    set z : ℂ := (σ : ℂ) + ((-T : ℝ) : ℝ) * Complex.I with hz
    set w : ℂ := (A : ℂ) + ((T : ℝ) : ℝ) * Complex.I with hw
    have hzre : z.re = σ := by simp [hz]
    have hzim : z.im = -T := by simp [hz]
    have hwre : w.re = A := by simp [hw]
    have hwim : w.im = T := by simp [hw]
    have hsub : Rectangle z w ⊆ {s : ℂ | 0 < s.re} := by
      intro s hs
      have hre := hs.1
      rw [hzre, hwre] at hre
      have := Set.mem_uIcc.mp hre
      rcases this with h | h
      · exact lt_of_lt_of_le hσ h.1
      · exact lt_of_lt_of_le hσ (le_trans hA h.1)
    have hvanish := hholo.vanishesOnRectangle hsub
    rw [RectangleIntegral, hzre, hzim, hwre, hwim] at hvanish
    have hVeq : VIntegral f σ (-T) T
        = HIntegral f σ A (-T) - HIntegral f σ A T + VIntegral f A (-T) T := by
      exact (sub_eq_zero.mp hvanish).symm
    have hnormV : ‖VIntegral f σ (-T) T‖
        = ‖∫ t in (-T)..T, f ((σ : ℂ) + (t : ℝ) * Complex.I)‖ := by
      rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
    rw [← hnormV, hVeq]
    have hb1 : ‖HIntegral f σ A (-T)‖ ≤ y ^ σ / (|(-T : ℝ)| * |Real.log y|) := by
      rw [HIntegral]
      exact norm_integral_horizontal_le' hy0 hy (by simpa using hTne) hA
    have hb2 : ‖HIntegral f σ A T‖ ≤ y ^ σ / (|T| * |Real.log y|) := by
      rw [HIntegral]
      exact norm_integral_horizontal_le' hy0 hy hTne hA
    have hb3 : ‖VIntegral f A (-T) T‖ ≤ 2 * T * (y ^ A / |A|) := by
      rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
      exact norm_integral_vertical_edge_cpow_le hy0 hApos.ne' hT.le
    have habsT : |(-T : ℝ)| = |T| := abs_neg T
    rw [habsT] at hb1
    calc ‖HIntegral f σ A (-T) - HIntegral f σ A T + VIntegral f A (-T) T‖
        ≤ ‖HIntegral f σ A (-T) - HIntegral f σ A T‖ + ‖VIntegral f A (-T) T‖ :=
          norm_add_le _ _
      _ ≤ (‖HIntegral f σ A (-T)‖ + ‖HIntegral f σ A T‖) + ‖VIntegral f A (-T) T‖ := by
          have := norm_sub_le (HIntegral f σ A (-T)) (HIntegral f σ A T)
          linarith
      _ ≤ (y ^ σ / (|T| * |Real.log y|) + y ^ σ / (|T| * |Real.log y|))
            + 2 * T * (y ^ A / |A|) := by linarith [hb1, hb2, hb3]
      _ = 2 * (y ^ σ / (|T| * |Real.log y|)) + 2 * T * (y ^ A / |A|) := by ring
  -- let the abscissa run to infinity
  have hlim : Tendsto (fun A : ℝ =>
      2 * (y ^ σ / (|T| * |Real.log y|)) + 2 * T * (y ^ A / |A|)) atTop
      (𝓝 (2 * (y ^ σ / (|T| * |Real.log y|)))) := by
    have hpow : Tendsto (fun A : ℝ => y ^ A) atTop (𝓝 0) :=
      tendsto_rpow_atTop_of_base_lt_one y (by linarith) hy
    have hsq : Tendsto (fun A : ℝ => y ^ A / |A|) atTop (𝓝 0) := by
      refine squeeze_zero' (Filter.Eventually.of_forall fun A => by positivity) ?_ hpow
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
      have hA0 : (0 : ℝ) < |A| := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ A)]
        linarith
      rw [div_le_iff₀ hA0]
      have hone : (1 : ℝ) ≤ |A| := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ A)]
        exact hA
      nlinarith [Real.rpow_nonneg hy0.le A, hone]
    have := (hsq.const_mul (2 * T)).const_add (2 * (y ^ σ / (|T| * |Real.log y|)))
    simpa using this
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop σ] with A hA
  exact hkey A hA

/-- **Perron's lemma above the cutoff.**  For `y > 1` the truncated vertical integral of `y^s/s` is `2π`
up to `O(y^σ/(T log y))`: the rectangle to the left of the line contains the pole at the origin, so its
boundary value is `2πi` times the residue. -/
theorem norm_vertical_perron_sub_two_pi_le_of_one_lt {y : ℝ} (hy : 1 < y) {σ T : ℝ}
    (hσ : 0 < σ) (hT : 0 < T) :
    ‖(∫ t in (-T)..T, ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * Complex.I))
          / ((σ : ℂ) + (t : ℝ) * Complex.I)) - 2 * (Real.pi : ℂ)‖
      ≤ 2 * (y ^ σ / (|T| * Real.log y)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  set f : ℂ → ℂ := fun s => (y : ℂ) ^ s / s with hf
  have hTne : T ≠ 0 := hT.ne'
  have hkey : ∀ A : ℝ, 0 < A →
      ‖(∫ t in (-T)..T, f ((σ : ℂ) + (t : ℝ) * Complex.I)) - 2 * (Real.pi : ℂ)‖
        ≤ 2 * (y ^ σ / (|T| * Real.log y)) + 2 * T * (y ^ (-A) / |(-A : ℝ)|) := by
    intro A hApos
    set z : ℂ := ((-A : ℝ) : ℂ) + ((-T : ℝ) : ℝ) * Complex.I with hz
    set w : ℂ := (σ : ℂ) + ((T : ℝ) : ℝ) * Complex.I with hw
    have hzre : z.re = -A := by simp [hz]
    have hzim : z.im = -T := by simp [hz]
    have hwre : w.re = σ := by simp [hw]
    have hwim : w.im = T := by simp [hw]
    have hre : z.re ≤ w.re := by rw [hzre, hwre]; linarith
    have him : z.im ≤ w.im := by rw [hzim, hwim]; linarith
    have hnhds : Rectangle z w ∈ 𝓝 (0 : ℂ) := by
      rw [rectangle_mem_nhds_iff, hzre, hzim, hwre, hwim,
        Set.uIoo_of_le (by linarith : (-A : ℝ) ≤ σ),
        Set.uIoo_of_le (by linarith : (-T : ℝ) ≤ T)]
      refine ⟨?_, ?_⟩
      · simp only [Set.mem_preimage, Complex.zero_re, Set.mem_Ioo]
        constructor <;> linarith
      · simp only [Set.mem_preimage, Complex.zero_im, Set.mem_Ioo]
        constructor <;> linarith
    have hres := rectangleIntegral'_cpow_div_eq_one hy0 hre him hnhds
    have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hrect : RectangleIntegral f z w = 2 * (Real.pi : ℂ) * Complex.I := by
      rw [RectangleIntegral', smul_eq_mul, one_div,
        inv_mul_eq_iff_eq_mul₀ h2pi, mul_one] at hres
      exact hres
    rw [RectangleIntegral, hzre, hzim, hwre, hwim] at hrect
    have hVeq : VIntegral f σ (-T) T - 2 * (Real.pi : ℂ) * Complex.I
        = -(HIntegral f (-A) σ (-T)) + HIntegral f (-A) σ T + VIntegral f (-A) (-T) T := by
      linear_combination hrect
    have hnormV : ‖VIntegral f σ (-T) T - 2 * (Real.pi : ℂ) * Complex.I‖
        = ‖(∫ t in (-T)..T, f ((σ : ℂ) + (t : ℝ) * Complex.I)) - 2 * (Real.pi : ℂ)‖ := by
      rw [VIntegral]
      have hfac : Complex.I • (∫ t in (-T)..T, f ((σ : ℂ) + (t : ℝ) * Complex.I))
            - 2 * (Real.pi : ℂ) * Complex.I
          = Complex.I * ((∫ t in (-T)..T, f ((σ : ℂ) + (t : ℝ) * Complex.I))
              - 2 * (Real.pi : ℂ)) := by
        rw [smul_eq_mul]
        ring
      rw [hfac, norm_mul, Complex.norm_I, one_mul]
    rw [← hnormV, hVeq]
    have hb1 : ‖HIntegral f (-A) σ (-T)‖ ≤ y ^ σ / (|(-T : ℝ)| * Real.log y) := by
      rw [HIntegral]
      exact norm_integral_horizontal_le hy (by simpa using hTne) (by linarith)
    have hb2 : ‖HIntegral f (-A) σ T‖ ≤ y ^ σ / (|T| * Real.log y) := by
      rw [HIntegral]
      exact norm_integral_horizontal_le hy hTne (by linarith)
    have hb3 : ‖VIntegral f (-A) (-T) T‖ ≤ 2 * T * (y ^ (-A) / |(-A : ℝ)|) := by
      rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
      exact norm_integral_vertical_edge_cpow_le hy0 (by simpa using hApos.ne') hT.le
    rw [abs_neg] at hb1
    calc ‖-(HIntegral f (-A) σ (-T)) + HIntegral f (-A) σ T + VIntegral f (-A) (-T) T‖
        ≤ ‖-(HIntegral f (-A) σ (-T)) + HIntegral f (-A) σ T‖
            + ‖VIntegral f (-A) (-T) T‖ := norm_add_le _ _
      _ ≤ (‖HIntegral f (-A) σ (-T)‖ + ‖HIntegral f (-A) σ T‖)
            + ‖VIntegral f (-A) (-T) T‖ := by
          have := norm_add_le (-(HIntegral f (-A) σ (-T))) (HIntegral f (-A) σ T)
          rw [norm_neg] at this
          linarith
      _ ≤ (y ^ σ / (|T| * Real.log y) + y ^ σ / (|T| * Real.log y))
            + 2 * T * (y ^ (-A) / |(-A : ℝ)|) := by linarith [hb1, hb2, hb3]
      _ = 2 * (y ^ σ / (|T| * Real.log y)) + 2 * T * (y ^ (-A) / |(-A : ℝ)|) := by ring
  have hlim : Tendsto (fun A : ℝ =>
      2 * (y ^ σ / (|T| * Real.log y)) + 2 * T * (y ^ (-A) / |(-A : ℝ)|)) atTop
      (𝓝 (2 * (y ^ σ / (|T| * Real.log y)))) := by
    have hinv : Tendsto (fun A : ℝ => (y⁻¹) ^ A) atTop (𝓝 0) := by
      have hinvpos : (0 : ℝ) < y⁻¹ := inv_pos.mpr hy0
      refine tendsto_rpow_atTop_of_base_lt_one (y⁻¹) (by linarith) ?_
      rw [inv_lt_one_iff₀]
      right
      exact hy
    have hneg : Tendsto (fun A : ℝ => y ^ (-A)) atTop (𝓝 0) := by
      refine hinv.congr fun A => ?_
      rw [Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le]
    have hsq : Tendsto (fun A : ℝ => y ^ (-A) / |(-A : ℝ)|) atTop (𝓝 0) := by
      refine squeeze_zero' (Filter.Eventually.of_forall fun A => by positivity) ?_ hneg
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
      have hA0 : (1 : ℝ) ≤ |(-A : ℝ)| := by
        rw [abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ A)]
        exact hA
      rw [div_le_iff₀ (by linarith : (0:ℝ) < |(-A : ℝ)|)]
      nlinarith [Real.rpow_nonneg hy0.le (-A), hA0]
    have := (hsq.const_mul (2 * T)).const_add (2 * (y ^ σ / (|T| * Real.log y)))
    simpa using this
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
  exact hkey A hA

end RHTower.Sieve
end
