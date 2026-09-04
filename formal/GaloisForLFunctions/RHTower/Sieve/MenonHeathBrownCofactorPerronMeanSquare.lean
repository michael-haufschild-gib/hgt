import GaloisForLFunctions.RHTower.Sieve.MenonPerronFiniteFamilyCauchy
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownSharpIntervalHandoff

/-!
# Exact Perron mean square with an unshifted cofactor

Menon's sharp twisted prime interval is replaced by its exact window-relevant Heath--Brown
integral.  Weighted Cauchy is applied to the complete integral, simultaneously over the finite
frequency family.  Consequently the Heath--Brown product is shifted by the integration variable,
while the cofactor polynomial remains at its original frequency.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- Exact sharp-interval Perron handoff for a finite family, with an arbitrary finite Dirichlet
cofactor retained at the unshifted ordinate. -/
theorem sum_normSq_vonMangoldtTwist_mul_dirPoly_le_fixedShiftPerron
    (L X k a b M : ℕ) (hXL : X < (L + 1) ^ k) (hab : a ≤ b) (hbX : b ≤ X)
    (T0 t : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    {sigma C : ℝ} (hsigma : 1 < sigma) (hC : 0 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖menonSharpIntervalMellinKernel (a : ℝ) (b : ℝ) sigma y‖ ≤
        C * (1 + y ^ 2)⁻¹)
    (S : Finset ℕ) (tau : ℕ → ℝ) (d : Fin M → ℂ) :
    ∑ r ∈ S,
        ‖((2 * Real.pi : ℝ) •
            (∑ n ∈ Finset.Ioc a b, vonMangoldtTwist (tau r) n)) *
          dirPoly M d (-tau r)‖ ^ 2 ≤
      C ^ 2 * Real.pi *
        ∫ y : ℝ,
          (∑ r ∈ S,
            ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (a : ℝ)
                ((sigma : ℂ) + ((y + tau r : ℝ) : ℂ) * Complex.I) *
              dirPoly M d (-tau r)‖ ^ 2) * (1 + y ^ 2)⁻¹ := by
  let A : ℕ → ℝ → ℂ := fun r y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (a : ℝ)
        ((sigma : ℂ) + ((y + tau r : ℝ) : ℂ) * Complex.I)
  let D : ℕ → ℂ := fun r => dirPoly M d (-tau r)
  let F : ℕ → ℝ → ℂ := fun r y => A r y * D r
  have haR : (0 : ℝ) < (a : ℝ) := by
    have hleft : (0 : ℝ) < ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t := by
      exact mul_pos (by positivity) (Real.rpow_pos_of_pos (by linarith) _)
    exact hleft.trans_le hscale
  have hX : 1 ≤ X := by
    have haPos : 0 < a := by exact_mod_cast haR
    exact (Nat.succ_le_iff.mpr haPos).trans (hab.trans hbX)
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k (a : ℝ) sigma
  have hFcont : ∀ r : ℕ, Continuous (F r) := by
    intro r
    have hshift : Continuous (fun y : ℝ => y + tau r) :=
      continuous_id.add continuous_const
    have hAcont : Continuous (A r) :=
      (continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
        L X k T0 t (a : ℝ) sigma).comp hshift
    exact hAcont.mul continuous_const
  have hAbound : ∀ r y, ‖A r y‖ ≤ P := by
    intro r y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t (a : ℝ) sigma (y + tau r) haR (by linarith)
  have hE : ∀ r ∈ S,
      Integrable fun y : ℝ => ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹ := by
    intro r _hr
    have hweightCont : Continuous fun y : ℝ => (1 + y ^ 2)⁻¹ :=
      (continuous_const.add (continuous_id.pow 2)).inv₀ (fun y => by
        simp only [Pi.add_apply, Pi.pow_apply, id_eq]
        exact ne_of_gt (by positivity))
    have hmajor : Integrable fun y : ℝ =>
        (P * ‖D r‖) ^ 2 * (1 + y ^ 2)⁻¹ :=
      integrable_inv_one_add_sq.const_mul ((P * ‖D r‖) ^ 2)
    refine Integrable.mono' hmajor
      (((hFcont r).norm.pow 2).mul hweightCont).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹)]
    have hFnorm : ‖F r y‖ ≤ P * ‖D r‖ := by
      rw [show ‖F r y‖ = ‖A r y‖ * ‖D r‖ by simp only [F, norm_mul]]
      exact mul_le_mul_of_nonneg_right (hAbound r y) (norm_nonneg _)
    have hsq := pow_le_pow_left₀ (norm_nonneg (F r y)) hFnorm 2
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  have hbase :=
    sum_norm_integral_menonSharpIntervalMellinKernel_sq_le S F (by linarith) hC
      (fun r _hr => (hFcont r).aestronglyMeasurable) hkernel hE
  have hperron : ∀ r : ℕ,
      ((2 * Real.pi : ℝ) •
          (∑ n ∈ Finset.Ioc a b, vonMangoldtTwist (tau r) n)) * D r =
        ∫ y : ℝ, F r y *
          menonSharpIntervalMellinKernel (a : ℝ) (b : ℝ) sigma y := by
    intro r
    rw [sum_Ioc_vonMangoldtTwist_eq_integral_windowRelevantAggregate
      L X k a b hXL hab hbX T0 t (tau r) hT0 hscale hsigma]
    rw [← MeasureTheory.integral_mul_const]
    apply integral_congr_ae
    filter_upwards with y
    simp only [F, A, D, menonSharpIntervalMellinKernel]
    ring
  have hleft :
      (∑ r ∈ S,
        ‖((2 * Real.pi : ℝ) •
            (∑ n ∈ Finset.Ioc a b, vonMangoldtTwist (tau r) n)) *
          dirPoly M d (-tau r)‖ ^ 2) =
        ∑ r ∈ S, ‖∫ y : ℝ, F r y *
          menonSharpIntervalMellinKernel (a : ℝ) (b : ℝ) sigma y‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro r _hr
    rw [show dirPoly M d (-tau r) = D r by rfl, hperron r]
  have hswap :
      (∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹) =
        ∫ y : ℝ, (∑ r ∈ S, ‖F r y‖ ^ 2) * (1 + y ^ 2)⁻¹ := by
    rw [← MeasureTheory.integral_finset_sum]
    · apply integral_congr_ae
      filter_upwards with y
      rw [Finset.sum_mul]
    · intro r hr
      exact hE r hr
  rw [hleft]
  refine hbase.trans ?_
  rw [hswap]

end RHTower.Sieve
