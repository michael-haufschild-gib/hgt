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

end RHTower.Sieve
end
