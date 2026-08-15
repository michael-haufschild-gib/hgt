import GaloisForLFunctions.RHTower.SuzukiGammaForcedStripHardy

/-!
# The forced Gamma particular solution has no half-log branch

The forced Gamma transport equation on the upper unit strip has the particular solution

`p(z) = H(z) ∫₀^z H(w)^{-1} b(w) dw`,

with the contour taken along the segment from the origin.  Both `H(z) = z^{-1/2}Q(z)` and
`H(w)^{-1} = w^{1/2}Q(w)^{-1}` carry the principal half power, and the point of the theorem is that
the two cancel exactly.  Parameterising the segment by `w = zs`, `s ∈ [0,1]`, the inner half power
splits as `(zs)^{1/2} = z^{1/2}s^{1/2}` because the second factor is a nonnegative real, so the
segment integral carries a single factor `z^{3/2}` out front, and

`p(z) = z · Q(z) ∫₀¹ s^{1/2} Q(zs)^{-1} b(zs) ds`.

The right side has no half power at all: every branch monodromy has cancelled, the particular
solution is single valued across the frequency origin, and it vanishes to first order there.  This
is what makes the same `p` appear in both frequency channels of the forced boundary problem, so that
the forced gluing criterion is exactly the homogeneous one.
-/

open Complex Filter MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- The inverse Gamma strip transport `Q(z)^{-1}`, the propagator inverse with the half power
removed. -/
def stripTransportInv (E : ℂ → ℂ) (T : X →L[ℂ] X) (z : ℂ) : X →L[ℂ] X :=
  ((Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z) * E z)⁻¹)
    • NormedSpace.exp (((Complex.I / 2) * z) • T)

theorem stripPropagatorInv_eq_cpow_smul (E : ℂ → ℂ) (T : X →L[ℂ] X) (z : ℂ) :
    stripPropagatorInv E T z = (z ^ ((1 : ℂ) / 2)) • stripTransportInv E T z := by
  have hpow : (z ^ (-(1 : ℂ) / 2))⁻¹ = z ^ ((1 : ℂ) / 2) := by
    rw [show -(1 : ℂ) / 2 = -((1 : ℂ) / 2) by ring, Complex.cpow_neg, inv_inv]
  rw [stripPropagatorInv, stripTransportInv, mul_inv, hpow, smul_smul]

/-- The half power splits along the segment, because the second factor is a nonnegative real. -/
private theorem cpow_half_mul_ofReal {z : ℂ} (hz : z ≠ 0) {s : ℝ} (hs : 0 < s) :
    (z * (s : ℂ)) ^ ((1 : ℂ) / 2) = z ^ ((1 : ℂ) / 2) * ((s : ℂ)) ^ ((1 : ℂ) / 2) := by
  have hsne : ((s : ℂ)) ≠ 0 := by
    simpa using hs.ne'
  have hzs : z * (s : ℂ) ≠ 0 := mul_ne_zero hz hsne
  rw [Complex.cpow_def_of_ne_zero hzs, Complex.cpow_def_of_ne_zero hz,
    Complex.cpow_def_of_ne_zero hsne, ← Complex.exp_add]
  congr 1
  rw [Complex.log_mul_ofReal s hs z hz, ← Complex.ofReal_log hs.le]
  ring

/-- **`(7)`: the particular solution** of the forced Gamma equation, with the contour integral taken
along the segment from the origin. -/
def forcedParticular (E : ℂ → ℂ) (T : X →L[ℂ] X) (b : ℂ → X) (z : ℂ) : X :=
  stripPropagator E T z
    (z • ∫ s in (0 : ℝ)..1, stripPropagatorInv E T (z * (s : ℂ)) (b (z * (s : ℂ))))

/-- The branch-cancelled kernel `Φ(z) = ∫₀¹ s^{1/2}Q(zs)^{-1}b(zs)ds`. -/
def forcedParticularKernel (E : ℂ → ℂ) (T : X →L[ℂ] X) (b : ℂ → X) (z : ℂ) : X :=
  ∫ s in (0 : ℝ)..1, ((s : ℂ) ^ ((1 : ℂ) / 2)) • stripTransportInv E T (z * (s : ℂ)) (b (z * (s : ℂ)))

/-- The half power of the segment parameter factors out of the inverse-propagator integral. -/
theorem integral_stripPropagatorInv_segment (E : ℂ → ℂ) (T : X →L[ℂ] X) (b : ℂ → X)
    {z : ℂ} (hz : z ≠ 0) :
    (∫ s in (0 : ℝ)..1, stripPropagatorInv E T (z * (s : ℂ)) (b (z * (s : ℂ))))
      = (z ^ ((1 : ℂ) / 2)) • forcedParticularKernel E T b z := by
  rw [forcedParticularKernel, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro s hs
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
  have hs0 : 0 < s := hs.1
  rw [stripPropagatorInv_eq_cpow_smul E T (z * (s : ℂ)), smul_apply,
    cpow_half_mul_ofReal hz hs0, smul_smul]

/-- **Theorem 1, branch cancellation.**  Every half power in the particular solution cancels: it is
`z` times a single-valued transport of the branch-free kernel.  In particular the particular
solution is single-valued across the frequency origin and vanishes to first order there. -/
theorem forcedParticular_eq (E : ℂ → ℂ) (T : X →L[ℂ] X) (b : ℂ → X) {z : ℂ} (hz : z ≠ 0) :
    forcedParticular E T b z = z • stripTransport E T z (forcedParticularKernel E T b z) := by
  have hsplit := integral_stripPropagatorInv_segment E T b hz
  have hcancel : z ^ (-(1 : ℂ) / 2) * z ^ ((1 : ℂ) / 2) = 1 := by
    rw [show -(1 : ℂ) / 2 = -((1 : ℂ) / 2) by ring, ← Complex.cpow_add _ _ hz]
    norm_num
  rw [forcedParticular, hsplit, smul_smul, stripPropagator, smul_apply,
    map_smul, smul_smul]
  congr 1
  rw [← mul_assoc, mul_comm (z ^ (-(1 : ℂ) / 2)) z, mul_assoc, hcancel, mul_one]

/-- **Theorem 1, `(8)`.**  The particular solution is `O(z)` at the frequency origin: it is bounded
by the transport norm times the segment bound on the branch-free integrand. -/
theorem norm_forcedParticular_le (E : ℂ → ℂ) (T : X →L[ℂ] X) (b : ℂ → X) {z : ℂ} (hz : z ≠ 0)
    {M : ℝ} (hM : ∀ s : ℝ, s ∈ Set.uIoc (0 : ℝ) 1 →
      ‖stripTransportInv E T (z * (s : ℂ)) (b (z * (s : ℂ)))‖ ≤ M) :
    ‖forcedParticular E T b z‖ ≤ ‖z‖ * ‖stripTransport E T z‖ * M := by
  have hM0 : 0 ≤ M := by
    have h1 : (1 : ℝ) ∈ Set.uIoc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact ⟨by norm_num, le_rfl⟩
    exact le_trans (norm_nonneg _) (hM 1 h1)
  have hker : ‖forcedParticularKernel E T b z‖ ≤ M := by
    have hbnd : ∀ s : ℝ, s ∈ Set.uIoc (0 : ℝ) 1 →
        ‖((s : ℂ) ^ ((1 : ℂ) / 2)) • stripTransportInv E T (z * (s : ℂ)) (b (z * (s : ℂ)))‖
          ≤ M := by
      intro s hs
      have hs01 : 0 < s ∧ s ≤ 1 := by
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
        exact ⟨hs.1, hs.2⟩
      have hnorm : ‖((s : ℂ) ^ ((1 : ℂ) / 2))‖ ≤ 1 := by
        have hcast : ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
        rw [hcast, ← Complex.ofReal_cpow hs01.1.le, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hs01.1.le _)]
        calc s ^ ((1 : ℝ) / 2) ≤ (1 : ℝ) ^ ((1 : ℝ) / 2) :=
              Real.rpow_le_rpow hs01.1.le hs01.2 (by norm_num)
          _ = 1 := Real.one_rpow _
      calc ‖((s : ℂ) ^ ((1 : ℂ) / 2))
              • stripTransportInv E T (z * (s : ℂ)) (b (z * (s : ℂ)))‖
          = ‖((s : ℂ) ^ ((1 : ℂ) / 2))‖
              * ‖stripTransportInv E T (z * (s : ℂ)) (b (z * (s : ℂ)))‖ := norm_smul _ _
        _ ≤ 1 * M := by
            refine mul_le_mul hnorm (hM s hs) (norm_nonneg _) (by norm_num)
        _ = M := one_mul M
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    simpa [forcedParticularKernel] using this
  rw [forcedParticular_eq E T b hz, norm_smul]
  calc ‖z‖ * ‖stripTransport E T z (forcedParticularKernel E T b z)‖
      ≤ ‖z‖ * (‖stripTransport E T z‖ * ‖forcedParticularKernel E T b z‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖z‖ * (‖stripTransport E T z‖ * M) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hker (norm_nonneg _)) (norm_nonneg _)
    _ = ‖z‖ * ‖stripTransport E T z‖ * M := by ring

end GaloisForLFunctions.RHTower
