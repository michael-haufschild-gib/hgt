import GaloisForLFunctions.HTGeometry.ClockMultiDimensionalDetermination
import GaloisForLFunctions.HTGeometry.ClockTubePotentialAlgebra
import GaloisForLFunctions.HTGeometry.ClockDatumExample

/-!
# A potential coupling several transverse coordinates

The theorems of the previous files are stated for potentials carrying a clock datum on a tube. This
file exhibits one, so that they are not vacuous:

`V(ξ, η, z) = sin ξ · cos η · cos (z¹ + ⋯ + zᵏ)`.

It is slice holomorphic in the transverse point, bounded on every tube by `cosh(kρ)`, continuously
differentiable in the two null coordinates, and real at real transverse points. It depends on all the
variables, and it is *not* separable in the transverse ones: a cosine of a sum is a sum of products,
so the dependence on the `k` transverse coordinates is genuinely coupled and not a sum or a product
of one-variable profiles.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-! ## The potential and its two null derivatives -/

/-- The example potential `sin ξ · cos η · cos (z¹ + ⋯ + zᵏ)`. -/
noncomputable def tubeCosPotential : ℝ → ℝ → (Fin k → ℂ) → ℂ :=
  fun s t z => ((Real.sin s * Real.cos t : ℝ) : ℂ) * Complex.cos (∑ i, z i)

/-- Its derivative along the first null coordinate. -/
noncomputable def tubeCosPotentialFst : ℝ → ℝ → (Fin k → ℂ) → ℂ :=
  fun s t z => ((Real.cos s * Real.cos t : ℝ) : ℂ) * Complex.cos (∑ i, z i)

/-- Its derivative along the second null coordinate. -/
noncomputable def tubeCosPotentialSnd : ℝ → ℝ → (Fin k → ℂ) → ℂ :=
  fun s t z => ((Real.sin s * -Real.sin t : ℝ) : ℂ) * Complex.cos (∑ i, z i)

theorem continuous_tubeCosPotential :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℂ) => tubeCosPotential q.1.1 q.1.2 q.2 :=
  (Complex.continuous_ofReal.comp
    ((Real.continuous_sin.comp (continuous_fst.comp continuous_fst)).mul
      (Real.continuous_cos.comp (continuous_snd.comp continuous_fst)))).mul
    (Complex.continuous_cos.comp (continuous_transverseSum.comp continuous_snd))

theorem continuous_tubeCosPotentialFst :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℂ) => tubeCosPotentialFst q.1.1 q.1.2 q.2 :=
  (Complex.continuous_ofReal.comp
    ((Real.continuous_cos.comp (continuous_fst.comp continuous_fst)).mul
      (Real.continuous_cos.comp (continuous_snd.comp continuous_fst)))).mul
    (Complex.continuous_cos.comp (continuous_transverseSum.comp continuous_snd))

theorem continuous_tubeCosPotentialSnd :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℂ) => tubeCosPotentialSnd q.1.1 q.1.2 q.2 :=
  (Complex.continuous_ofReal.comp
    ((Real.continuous_sin.comp (continuous_fst.comp continuous_fst)).mul
      ((Real.continuous_sin.comp (continuous_snd.comp continuous_fst)).neg))).mul
    (Complex.continuous_cos.comp (continuous_transverseSum.comp continuous_snd))

/-- **The example potential is slice holomorphic on every tube.** -/
theorem sliceHolo_tubeCosPotential (ρ : ℝ) (s t : ℝ) :
    SliceHolo (tubeCosPotential (k := k) s t) ρ := by
  intro z hz i
  have hsum : Differentiable ℂ fun ζ : ℂ => ∑ j, Function.update z i ζ j :=
    differentiable_transverseSumSlice z i
  exact ((differentiable_const _).mul
    (Complex.differentiable_cos.comp hsum)).differentiableOn

theorem tubePotential_tubeCosPotential (ρ : ℝ) : TubePotential (tubeCosPotential (k := k)) ρ where
  cont := continuous_tubeCosPotential.continuousOn
  holo := fun s t => sliceHolo_tubeCosPotential ρ s t

theorem tubePotentialC1_tubeCosPotential (ρ : ℝ) :
    TubePotentialC1 (tubeCosPotential (k := k)) tubeCosPotentialFst tubeCosPotentialSnd ρ where
  base := tubePotential_tubeCosPotential ρ
  hasDerivFst := by
    intro s t z _
    have hreal : HasDerivAt (fun x : ℝ => Real.sin x * Real.cos t)
        (Real.cos s * Real.cos t) s := (Real.hasDerivAt_sin s).mul_const _
    have hcast : HasDerivAt (fun x : ℝ => ((Real.sin x * Real.cos t : ℝ) : ℂ))
        (((Real.cos s * Real.cos t : ℝ) : ℂ)) s :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s hreal
    exact hcast.mul_const (Complex.cos (∑ i, z i))
  hasDerivSnd := by
    intro s t z _
    have hreal : HasDerivAt (fun x : ℝ => Real.sin s * Real.cos x)
        (Real.sin s * -Real.sin t) t := (Real.hasDerivAt_cos t).const_mul _
    have hcast : HasDerivAt (fun x : ℝ => ((Real.sin s * Real.cos x : ℝ) : ℂ))
        (((Real.sin s * -Real.sin t : ℝ) : ℂ)) t :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hreal
    exact hcast.mul_const (Complex.cos (∑ i, z i))
  contFst := continuous_tubeCosPotentialFst.continuousOn
  contSnd := continuous_tubeCosPotentialSnd.continuousOn

/-- **The example potential is bounded on every tube.** -/
theorem norm_tubeCosPotential_le {ρ : ℝ} (hρ : 0 ≤ ρ) (s t : ℝ) {z : Fin k → ℂ}
    (hz : z ∈ tube k ρ) : ‖tubeCosPotential s t z‖ ≤ Real.cosh (k * ρ) := by
  have him : |(∑ i, z i).im| ≤ (k : ℝ) * ρ := by
    rw [Complex.im_sum]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ i : Fin k, |(z i).im| ≤ ∑ _i : Fin k, ρ := Finset.sum_le_sum fun i _ => (hz i).le
      _ = (k : ℝ) * ρ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcoef : ‖((Real.sin s * Real.cos t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (Real.abs_sin_le_one s) (abs_nonneg _) (Real.abs_cos_le_one t)
  have hcos : ‖Complex.cos (∑ i, z i)‖ ≤ Real.cosh ((k : ℝ) * ρ) :=
    norm_cos_le_cosh (mul_nonneg (Nat.cast_nonneg k) hρ) him
  rw [tubeCosPotential, norm_mul]
  calc ‖((Real.sin s * Real.cos t : ℝ) : ℂ)‖ * ‖Complex.cos (∑ i, z i)‖
      ≤ 1 * Real.cosh ((k : ℝ) * ρ) :=
        mul_le_mul hcoef hcos (norm_nonneg _) (by norm_num)
    _ = Real.cosh ((k : ℝ) * ρ) := one_mul _

/-- **The example potential is real at real transverse points.** -/
theorem tubeCosPotential_im (s t : ℝ) (y : Fin k → ℝ) :
    (tubeCosPotential s t (realTube y)).im = 0 := by
  have hsum : ∑ i, realTube y i = ((∑ i, y i : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    rfl
  rw [tubeCosPotential, hsum, ← Complex.ofReal_cos, ← Complex.ofReal_mul, Complex.ofReal_im]

/-! ## The datum -/

/-- **The example potential carries a clock datum on a tube**, for every tube and every sufficiently
small rectangle. -/
theorem tubeDatum_tubeCosPotential {ρ₀ ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Real.cosh ((k : ℝ) * ρ₀) * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2
      / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 < ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 < ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 < ρ₃) (hρ₃ : ρ₃ < ρ₂) :
    TubeDatum (tubeCosPotential (k := k)) tubeCosPotentialFst tubeCosPotentialSnd ρ₀
      (Real.cosh ((k : ℝ) * ρ₀)) ρ ρ₁ ρ₂ ρ₃ T where
  pos := hρ₀
  potC1 := tubePotentialC1_tubeCosPotential ρ₀
  massNonneg := (Real.cosh_pos _).le
  mass := fun s t _ _ _ hz => norm_tubeCosPotential_le hρ₀.le s t hz
  radNonneg := hρ0
  rad := hρ
  sideNonneg := hT
  small := hsmall
  rad₁Pos := hρ₁0
  rad₁ := hρ₁
  rad₂Pos := hρ₂0
  rad₂ := hρ₂
  rad₃Pos := hρ₃0
  rad₃ := hρ₃

/-- **The class of potentials coupling several transverse coordinates is inhabited.** There is a
potential carrying a clock datum on a tube, real at real transverse points, depending on both null
coordinates and on *every one* of the transverse coordinates. -/
theorem exists_tubeDatum_coupled (k : ℕ) :
    ∃ (V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ) (ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ),
      TubeDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T ∧ 0 < T ∧
        (∀ s t : ℝ, ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv) ∧
        (∀ (s t : ℝ) (y : Fin k → ℝ), (V s t (realTube y)).im = 0) ∧
        (∀ i : Fin k, ∃ (s t : ℝ) (z : Fin k → ℂ) (ζ : ℂ),
          V s t (Function.update z i ζ) ≠ V s t z) ∧
        (∃ (s s' t : ℝ) (z : Fin k → ℂ), V s t z ≠ V s' t z) := by
  classical
  obtain ⟨T, hTpos, hsmall⟩ := exists_small_side
    (A := 4 * (k : ℝ) + Real.cosh ((k : ℝ) * 1) * (1 : ℝ) ^ (2 : ℕ) / 4)
    (B := ((1 : ℝ) - 1 / 2) / 2)
    (by positivity) (by norm_num)
  refine ⟨tubeCosPotential, tubeCosPotentialFst, tubeCosPotentialSnd, 1,
    Real.cosh ((k : ℝ) * 1), 1 / 2, 1 / 4, 1 / 8, 1 / 16, T,
    tubeDatum_tubeCosPotential one_pos (by norm_num) (by norm_num) hTpos.le hsmall
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hTpos, fun s t z hz => norm_tubeCosPotential_le zero_le_one s t hz, tubeCosPotential_im,
    ?_, ?_⟩
  · intro i
    refine ⟨Real.pi / 2, 0, 0, ((Real.pi : ℝ) : ℂ), ?_⟩
    have hupd : ∑ j, Function.update (0 : Fin k → ℂ) i ((Real.pi : ℝ) : ℂ) j
        = ((Real.pi : ℝ) : ℂ) := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      simp
    have hzero : ∑ _j : Fin k, (0 : ℂ) = 0 := by simp
    rw [tubeCosPotential, tubeCosPotential, hupd, Real.sin_pi_div_two, Real.cos_zero]
    show ((1 * 1 : ℝ) : ℂ) * Complex.cos ((Real.pi : ℝ) : ℂ)
      ≠ ((1 * 1 : ℝ) : ℂ) * Complex.cos (∑ _j : Fin k, (0 : ℂ))
    rw [hzero, Complex.cos_zero, ← Complex.ofReal_cos, Real.cos_pi]
    norm_num
  · refine ⟨0, Real.pi / 2, 0, 0, ?_⟩
    rw [tubeCosPotential, tubeCosPotential, Real.sin_zero, Real.sin_pi_div_two, Real.cos_zero]
    norm_num

end GaloisForLFunctions.HTGeometry
