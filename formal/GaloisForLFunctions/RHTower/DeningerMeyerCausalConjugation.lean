import GaloisForLFunctions.RHTower.DeningerMeyerCausalReflectionCovariance
import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogRealContinuity
import GaloisForLFunctions.RHTower.RiemannVonMangoldt

/-!
# Arithmetic conjugation on actual Meyer cohomology and causal sources

Pointwise conjugation preserves the even Schwartz endpoint kernel and intertwines
the literal Poisson sum.  It therefore descends through the actual Poisson range.
Its Mellin-jet covariance preserves the invisible submodule; uniqueness of the
entire causal divisions preserves the original finite causal source span.
-/

open Complex Set MeasureTheory
open scoped Classical

namespace RHTower
noncomputable section

theorem deningerFourierEval_eq_integral (f : SchwartzMap ℝ ℂ) :
    deningerFourierEval f = ∫ x : ℝ, f x := by
  change FourierTransform.fourier (f : ℝ → ℂ) 0 = _
  simp [Real.fourier_real_eq_integral_exp_smul]

/-- The original Schwartz source, with pointwise complex conjugation. -/
def deningerMeyerCapConj (f : DeningerMeyerCap) : DeningerMeyerCap :=
  ⟨SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) f, by
    obtain ⟨he, h0, hF⟩ := (deningerMeyerCap_mem_iff _).mp f.property
    apply (deningerMeyerCap_mem_iff _).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro x
      change star (f.val (-x)) = star (f.val x)
      rw [he]
    · change star (f.val 0) = 0
      rw [h0, star_zero]
    · change deningerFourierEval
        (SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) f) = 0
      rw [deningerFourierEval_eq_integral]
      change (∫ x : ℝ, (starRingEnd ℂ) (f.val x)) = 0
      rw [integral_conj]
      change deningerFourierEval (f : SchwartzMap ℝ ℂ) = 0 at hF
      rw [deningerFourierEval_eq_integral] at hF
      rw [hF, map_zero]⟩

@[simp]
theorem deningerMeyerCapConj_apply (f : DeningerMeyerCap) (x : ℝ) :
    (deningerMeyerCapConj f).val x = star (f.val x) := rfl

theorem deningerMeyerStrongLogConj_boundary (f : DeningerMeyerCap) :
    deningerMeyerStrongLogConj (deningerMeyerStrongLogSumLM f) =
      deningerMeyerStrongLogSumLM (deningerMeyerCapConj f) := by
  apply Subtype.ext
  funext t
  change star (∑' n : ℕ, f.val (((n : ℝ) + 1) * Real.exp t)) =
    ∑' n : ℕ, star (f.val (((n : ℝ) + 1) * Real.exp t))
  exact tsum_star

theorem deningerMeyerStrongLogConj_range_le :
    LinearMap.range deningerMeyerStrongLogSumLM ≤
      (LinearMap.range deningerMeyerStrongLogSumLM).comap
        deningerMeyerStrongLogConjₛₗ := by
  rintro _ ⟨f, rfl⟩
  exact ⟨deningerMeyerCapConj f, (deningerMeyerStrongLogConj_boundary f).symm⟩

/-- Arithmetic conjugation descended through the genuine Poisson boundary. -/
def deningerMeyerCohomologyConj :
    DeningerMeyerStrongLogCohomology →ₗ⋆[ℂ] DeningerMeyerStrongLogCohomology :=
  (LinearMap.range deningerMeyerStrongLogSumLM).mapQ
    (LinearMap.range deningerMeyerStrongLogSumLM)
    deningerMeyerStrongLogConjₛₗ deningerMeyerStrongLogConj_range_le

@[simp]
theorem deningerMeyerCohomologyConj_mk (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerCohomologyConj (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (deningerMeyerStrongLogConj g) := rfl

@[simp]
theorem deningerMeyerCohomologyConj_sq (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCohomologyConj (deningerMeyerCohomologyConj u) = u := by
  induction u using Submodule.Quotient.induction_on with
  | H g => simp

theorem deningerMeyerStrongLogMellinJetLM_conj (g : DeningerMeyerStrongLogTarget)
    (k : ℕ) (s : ℂ) :
    deningerMeyerStrongLogMellinJetLM k s (deningerMeyerStrongLogConj g) =
      star (deningerMeyerStrongLogMellinJetLM k (star s) g) := by
  change (∫ t : ℝ, deningerMeyerStrongLogMellinJet k s
      (deningerMeyerStrongLogConj g) t) =
    (starRingEnd ℂ) (∫ t : ℝ, deningerMeyerStrongLogMellinJet k (star s) g t)
  rw [← integral_conj]
  congr 1
  funext t
  simp [deningerMeyerStrongLogMellinJet, ← Complex.exp_conj]

theorem deningerMeyerStrongLogMellin_conj (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerStrongLogConj g) s =
      star (deningerMeyerStrongLogMellin g (star s)) :=
  deningerMeyerStrongLogMellinJetLM_conj g 0 s

theorem deningerMeyerStrongLogGenerator_conj (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogGenerator (deningerMeyerStrongLogConj g) =
      deningerMeyerStrongLogConj (deningerMeyerStrongLogGenerator g) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  change deningerMeyerStrongLogMellin _ s = deningerMeyerStrongLogMellin _ s
  simp [deningerMeyerStrongLogGenerator_mellin, deningerMeyerStrongLogMellin_conj]

theorem deningerMeyerCohomologyGenerator_conj (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCohomologyGenerator (deningerMeyerCohomologyConj u) =
      deningerMeyerCohomologyConj (deningerMeyerCohomologyGenerator u) := by
  induction u using Submodule.Quotient.induction_on with
  | H g => simp [deningerMeyerStrongLogGenerator_conj]

theorem deningerMeyerStrongLogConj_J (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogConj (deningerMeyerStrongLogJ g) =
      deningerMeyerStrongLogJ (deningerMeyerStrongLogConj g) := by
  apply Subtype.ext
  funext t
  change (starRingEnd ℂ) ((Real.exp (-t) : ℂ) * g.val (-t)) =
    (Real.exp (-t) : ℂ) * star (g.val (-t))
  rw [map_mul, Complex.conj_ofReal]
  rfl

theorem deningerMeyerCohomologyConj_J (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCohomologyConj (deningerMeyerStrongLogCohomologyJ u) =
      deningerMeyerStrongLogCohomologyJ (deningerMeyerCohomologyConj u) := by
  induction u using Submodule.Quotient.induction_on with
  | H g => simp [deningerMeyerStrongLogConj_J]

theorem deningerMeyerXiSupportJetEvaluationLM_conj (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerXiSupportJetEvaluationLM rho j (deningerMeyerCohomologyConj u) =
      star (deningerMeyerXiSupportJetEvaluationLM (xiSupportConj rho)
        ⟨j.val, by rw [xiSupportMultiplicity_conj]; exact j.isLt⟩ u) := by
  induction u using Submodule.Quotient.induction_on with
  | H g => exact deningerMeyerStrongLogMellinJetLM_conj g j.val (rho : ℂ)

theorem deningerMeyerInvisible_conj_mem (u : DeningerMeyerInvisible) :
    deningerMeyerCohomologyConj u ∈ DeningerMeyerInvisible := by
  apply (mem_deningerMeyerInvisible_iff _).mpr
  intro rho j
  rw [deningerMeyerXiSupportJetEvaluationLM_conj,
    (mem_deningerMeyerInvisible_iff _).mp u.property, star_zero]

/-- Conjugation covariance of causal divisions holds already on the actual source. -/
theorem deningerMeyerXiCausalSource_conj (rho : XiDivisorSupport) (k : ℕ)
    (hk : k ≤ xiSupportMultiplicity rho) :
    deningerMeyerStrongLogConj (deningerMeyerXiCausalSource rho k hk) =
      deningerMeyerXiCausalSource (xiSupportConj rho) k
        (by rw [xiSupportMultiplicity_conj]; exact hk) := by
  let hkc : k ≤ xiSupportMultiplicity (xiSupportConj rho) := by
    rw [xiSupportMultiplicity_conj]
    exact hk
  apply deningerMeyerStrongLogMellin_injective
  apply Continuous.ext_on (dense_compl_singleton (xiSupportConj rho : ℂ))
    (differentiable_deningerMeyerStrongLogMellin
      (deningerMeyerStrongLogConj (deningerMeyerXiCausalSource rho k hk)).property).continuous
    (differentiable_deningerMeyerStrongLogMellin
      (deningerMeyerXiCausalSource (xiSupportConj rho) k hkc).property).continuous
  intro s hs
  apply mul_left_cancel₀ (pow_ne_zero k (sub_ne_zero.mpr hs))
  rw [deningerMeyerStrongLogMellin_conj]
  calc
    (s - (xiSupportConj rho : ℂ)) ^ k *
        star (deningerMeyerStrongLogMellin (deningerMeyerXiCausalSource rho k hk) (star s)) =
      star ((star s - (rho : ℂ)) ^ k *
        deningerMeyerStrongLogMellin (deningerMeyerXiCausalSource rho k hk) (star s)) := by
          simp [xiSupportConj_coe]
    _ = star (xi (star s)) := by rw [← deningerMeyerXiCausalSource_factor rho k hk]
    _ = xi s := by
      change star (xi ((starRingEnd ℂ) s)) = xi s
      rw [xi_conj]
      simp
    _ = (s - (xiSupportConj rho : ℂ)) ^ k *
        deningerMeyerStrongLogMellin
          (deningerMeyerXiCausalSource (xiSupportConj rho) k hkc) s :=
      deningerMeyerXiCausalSource_factor _ _ _ _

theorem deningerMeyerXiJetSource_conj (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerCohomologyConj (deningerMeyerXiJetSource rho j) =
      deningerMeyerXiJetSource (xiSupportConj rho)
        ⟨j.val, by rw [xiSupportMultiplicity_conj]; exact j.isLt⟩ := by
  simp only [deningerMeyerXiJetSource, deningerMeyerXiCausalClass,
    deningerMeyerCohomologyConj_mk, deningerMeyerXiCausalSource_conj,
    xiSupportMultiplicity_conj]

theorem deningerMeyerFiniteCausalModes_conj_mem (u : DeningerMeyerFiniteCausalModes) :
    deningerMeyerCohomologyConj u ∈ DeningerMeyerFiniteCausalModes := by
  obtain ⟨S, c, hc⟩ := u.property
  rw [← hc, deningerMeyerFiniteXiCausalSynthesis_apply, map_sum]
  apply Submodule.sum_mem
  intro q _
  rw [LinearMap.map_smulₛₗ, deningerMeyerXiJetSource_conj]
  exact DeningerMeyerFiniteCausalModes.smul_mem _ (deningerMeyerXiJetSource_mem_finite _ _)

end
end RHTower
