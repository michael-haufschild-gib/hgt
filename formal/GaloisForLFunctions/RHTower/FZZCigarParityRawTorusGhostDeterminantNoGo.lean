import GaloisForLFunctions.HTGeometry.MultiplicativeThetaDivisor
import GaloisForLFunctions.HTGeometry.FZZCigarHigherGenusTwistRedshift

/-!
# Raw twisted torus determinant cannot be the FZZ-P passivity selector

The genus-one twisted `βγ`/ghost determinant is a theta section.  A direct fixed-threshold
proposal must select the whole zero-radial-holonomy wall `s₁ = 0`, uniformly in compact
holonomy `s₂`.  This is impossible before any arithmetic input:

* every continuous exact wall sublevel selector saturates its threshold everywhere on the wall;
* the raw multiplicative-theta determinant vanishes at trivial wall holonomy;
* it is nonzero at half wall holonomy;
* even continuous injective scalar postprocessing cannot remove this conflict.

This kills the raw determinant/ghost-norm branch of the remaining FZZ-P source edge

`fixed theta source → torus replica-area response → divisor-mode passivity → RH`.

The sharp survivor is tangential normalization: a viable determinant response must first remove
compact-holonomy variation by a non-pointwise operation such as a logarithmic circle average,
Quillen ratio, or covariant derivative.  Pointwise faithful rescaling is insufficient.

Physics sources:

* Hikida--Schomerus, arXiv:0805.3931, higher-genus twisted first-order system and Jacobian
  integration, especially Appendix C.
* Russo--Sciuto, arXiv:hep-th/0306129, twisted `bc` determinant/theta product.
* Halder--Jafferis, arXiv:2402.00932v3, equations (3.29), (3.33), and the still-unevaluated
  torus one-point area operator.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

open HTGeometry
open HTGeometry.FZZCigar

/-- Exact continuous sublevel selection of a codimension-one wall forces threshold saturation at
every point of that wall. -/
theorem continuous_exactWallSublevel_saturates
    (F : ℝ → ℝ → ℝ) (c : ℝ)
    (hcontinuous : ∀ y : ℝ, ContinuousAt (fun x : ℝ => F x y) 0)
    (hselector : ∀ x y : ℝ, F x y ≤ c ↔ x = 0) (y : ℝ) :
    F 0 y = c := by
  apply le_antisymm
  · exact (hselector 0 y).2 rfl
  · have hs : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hF : Tendsto
        (fun n : ℕ => F ((1 : ℝ) / ((n : ℝ) + 1)) y)
        atTop (𝓝 (F 0 y)) := (hcontinuous y).tendsto.comp hs
    have heventual : ∀ᶠ n : ℕ in atTop,
        c ≤ F ((1 : ℝ) / ((n : ℝ) + 1)) y := by
      filter_upwards with n
      have hxne : (1 : ℝ) / ((n : ℝ) + 1) ≠ 0 := by positivity
      exact le_of_lt (lt_of_not_ge (fun hle => hxne ((hselector _ y).mp hle)))
    have hsub : Tendsto
        (fun n : ℕ => c - F ((1 : ℝ) / ((n : ℝ) + 1)) y)
        atTop (𝓝 (c - F 0 y)) := tendsto_const_nhds.sub hF
    have : c - F 0 y ≤ 0 :=
      le_of_tendsto hsub (heventual.mono fun _ h => sub_nonpos.mpr h)
    linarith

/-- Raw norm of the twisted genus-one ghost determinant theta section. -/
def fzzRawTorusGhostDeterminantNorm (q : EulerNome) (twist : ℂ) : ℝ :=
  ‖multiplicativeTheta q
    (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * twist))‖

theorem continuous_fzzRawTorusGhostDeterminantNorm (q : EulerNome) :
    Continuous (fzzRawTorusGhostDeterminantNorm q) := by
  have htheta : Continuous
      (fun z : ℂ => multiplicativeTheta q (Complex.exp z)) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (analyticAt_multiplicativeTheta q (Complex.exp_ne_zero z)).continuousAt.comp_of_eq
      Complex.continuous_exp.continuousAt rfl
  exact htheta.comp (by fun_prop) |>.norm

theorem fzzRawTorusGhostDeterminantNorm_zero (q : EulerNome) :
    fzzRawTorusGhostDeterminantNorm q 0 = 0 := by
  unfold fzzRawTorusGhostDeterminantNorm
  simp only [mul_zero, Complex.exp_zero]
  rw [norm_eq_zero, multiplicativeTheta, qPochhammerInf_shift]
  ring

private theorem multiplicativeTheta_neg_one_ne_zero (q : EulerNome) :
    multiplicativeTheta q (-1) ≠ 0 := by
  let d : EulerPochhammerDatum :=
    { a := -(q : ℂ)
      q := q
      a_norm_lt_one := by simpa using q.norm_lt_one }
  have htail : qPochhammerInf (-(q : ℂ)) q ≠ 0 := by
    simpa [d] using qPochhammerInf_ne_zero d
  have hfirst : qPochhammerInf (-1) q ≠ 0 := by
    rw [qPochhammerInf_shift]
    apply mul_ne_zero
    · norm_num
    · simpa using htail
  have hsecond : qPochhammerInf ((q : ℂ) / (-1)) q ≠ 0 := by
    rw [show (q : ℂ) / (-1) = -(q : ℂ) by ring]
    exact htail
  exact mul_ne_zero hfirst hsecond

theorem fzzRawTorusGhostDeterminantNorm_half_ne_zero (q : EulerNome) :
    fzzRawTorusGhostDeterminantNorm q ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
  have hexp :
      Complex.exp
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((1 / 2 : ℝ) : ℂ))) = -1 := by
    rw [show (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((1 / 2 : ℝ) : ℂ))) =
        (Real.pi : ℂ) * Complex.I by push_cast; ring]
    exact Complex.exp_pi_mul_I
  rw [fzzRawTorusGhostDeterminantNorm, hexp, norm_ne_zero_iff]
  exact multiplicativeTheta_neg_one_ne_zero q

/-- No continuous injective scalar postprocessing of the raw twisted determinant norm can make a
fixed sublevel threshold select exactly the zero-radial-holonomy wall. -/
theorem not_exists_fzzRawTorusGhostDeterminantNorm_postprocess_threshold_selector
    (q : EulerNome) (τ : ℂ) (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hφinj : Function.Injective φ) :
    ¬ ∃ c : ℝ, ∀ s₁ s₂ : ℝ,
      φ (fzzRawTorusGhostDeterminantNorm q (torusJacobianTwist s₁ s₂ τ)) ≤ c ↔
        s₁ = 0 := by
  rintro ⟨c, hselector⟩
  let F : ℝ → ℝ → ℝ := fun s₁ s₂ =>
    φ (fzzRawTorusGhostDeterminantNorm q (torusJacobianTwist s₁ s₂ τ))
  have hFcontinuous : ∀ s₂ : ℝ, ContinuousAt (fun s₁ : ℝ => F s₁ s₂) 0 := by
    intro s₂
    exact hφ.continuousAt.comp_of_eq
      ((continuous_fzzRawTorusGhostDeterminantNorm q).continuousAt.comp_of_eq
        (by unfold torusJacobianTwist; fun_prop) rfl) rfl
  have hsaturates : ∀ s₂ : ℝ, F 0 s₂ = c :=
    continuous_exactWallSublevel_saturates F c hFcontinuous hselector
  have hwall :
      φ (fzzRawTorusGhostDeterminantNorm q 0) =
        φ (fzzRawTorusGhostDeterminantNorm q (((1 / 2 : ℝ) : ℂ))) := by
    calc
      φ (fzzRawTorusGhostDeterminantNorm q 0) = F 0 0 := by
        simp [F, torusJacobianTwist]
      _ = c := hsaturates 0
      _ = F 0 (1 / 2) := (hsaturates (1 / 2)).symm
      _ = φ (fzzRawTorusGhostDeterminantNorm q (((1 / 2 : ℝ) : ℂ))) := by
        simp [F, torusJacobianTwist]
  have hhalf_zero :
      fzzRawTorusGhostDeterminantNorm q (((1 / 2 : ℝ) : ℂ)) = 0 := by
    rw [← fzzRawTorusGhostDeterminantNorm_zero q]
    exact (hφinj hwall).symm
  exact fzzRawTorusGhostDeterminantNorm_half_ne_zero q hhalf_zero

/-- In particular, the unprocessed raw determinant norm is not a fixed-threshold wall selector. -/
theorem not_exists_fzzRawTorusGhostDeterminantNorm_threshold_selector
    (q : EulerNome) (τ : ℂ) :
    ¬ ∃ c : ℝ, ∀ s₁ s₂ : ℝ,
      fzzRawTorusGhostDeterminantNorm q (torusJacobianTwist s₁ s₂ τ) ≤ c ↔ s₁ = 0 := by
  simpa using
    not_exists_fzzRawTorusGhostDeterminantNorm_postprocess_threshold_selector
      q τ (fun x : ℝ => x) continuous_id Function.injective_id

end

end GaloisForLFunctions.RHTower
