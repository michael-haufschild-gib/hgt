import GaloisForLFunctions.HTGeometry.TunableSecondKind

/-!
# One tunable transfer step

Combining the two propagate estimates: bounds `(S, P)` at `z` give bounds `(cS, cP)` at `w`, with
the
*same* factor `c = √((1+ε)/(1−δ))` on both, since the smallness condition and the leading constant
are shared between the first- and second-kind steps.

That shared factor is what lets a chain carry one scalar invariant instead of two.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **One tunable transfer step.** -/
theorem kernelRoot_bounds_propagate_tunable (h : PositiveMomentForm s) (z w : ℂ)
    {S P delta e : ℝ} (he : 0 < e) (hd1 : delta < 1)
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P)
    (hsmall : 4 * (1 + e⁻¹) *
      (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 * S ^ 2 * P ^ 2 ≤ delta) :
    (∀ N, kernelRoot s (fun j => monicOrthoC s j w) N
        ≤ Real.sqrt ((1 + e) / (1 - delta)) * S)
      ∧ (∀ N, kernelRoot s (fun j => secondKindC s j w) N
        ≤ Real.sqrt ((1 + e) / (1 - delta)) * P) := by
  have hSn : 0 ≤ S := le_trans (kernelRoot_nonneg _ _ 0) (hS 0)
  have hPn : 0 ≤ P := le_trans (kernelRoot_nonneg _ _ 0) (hP 0)
  have hdpos : 0 < 1 - delta := by linarith
  have hratio : 0 ≤ (1 + e) / (1 - delta) := by positivity
  have hcsq : Real.sqrt ((1 + e) / (1 - delta)) ^ 2 = (1 + e) / (1 - delta) :=
    Real.sq_sqrt hratio
  have hc0 : 0 ≤ Real.sqrt ((1 + e) / (1 - delta)) := Real.sqrt_nonneg _
  constructor
  · intro N
    have h1 := kernelRootQ_sq_le_tunable h z w he hS hP hsmall N
    have h2 : kernelRoot s (fun j => monicOrthoC s j w) N ^ 2
        ≤ (Real.sqrt ((1 + e) / (1 - delta)) * S) ^ 2 := by
      rw [mul_pow, hcsq, div_mul_eq_mul_div, le_div_iff₀ hdpos]
      linarith [h1]
    calc kernelRoot s (fun j => monicOrthoC s j w) N
        = Real.sqrt (kernelRoot s (fun j => monicOrthoC s j w) N ^ 2) :=
          (Real.sqrt_sq (kernelRoot_nonneg _ _ _)).symm
      _ ≤ Real.sqrt ((Real.sqrt ((1 + e) / (1 - delta)) * S) ^ 2) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt ((1 + e) / (1 - delta)) * S :=
          Real.sqrt_sq (mul_nonneg hc0 hSn)
  · intro N
    have h1 := kernelRootR_sq_le_tunable h z w he hS hP hsmall N
    have h2 : kernelRoot s (fun j => secondKindC s j w) N ^ 2
        ≤ (Real.sqrt ((1 + e) / (1 - delta)) * P) ^ 2 := by
      rw [mul_pow, hcsq, div_mul_eq_mul_div, le_div_iff₀ hdpos]
      linarith [h1]
    calc kernelRoot s (fun j => secondKindC s j w) N
        = Real.sqrt (kernelRoot s (fun j => secondKindC s j w) N ^ 2) :=
          (Real.sqrt_sq (kernelRoot_nonneg _ _ _)).symm
      _ ≤ Real.sqrt ((Real.sqrt ((1 + e) / (1 - delta)) * P) ^ 2) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt ((1 + e) / (1 - delta)) * P :=
          Real.sqrt_sq (mul_nonneg hc0 hPn)

end HTGeometry
