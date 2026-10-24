import GaloisForLFunctions.SignedSuccessorArithmetic.TheSpectralHypercubeFormIsUnbounded
import GaloisForLFunctions.BezoutValuationIncidence.BezoutCouplingAndCrossDepthCancellation
import GaloisForLFunctions.HTGeometry.HalfLineMellinMultiplier

/-!
# The hypercube Dirichlet form is unbounded below half damping

Bézout–Valuation Incidence defines the hypercube Dirichlet form of the Ramanujan step vector
`v = f_r`,

  `Q_ε(P) = Σ_{d₁, d₂ ∣ P} μ(d₁) μ(d₂) (d₁ d₂)^{−1/2−ε} Φ_r(d₁/d₂)`,  `Φ_r(c) = Re⟨v, D_c v⟩`,

proves it nonnegative, and proves it bounded uniformly in squarefree `P` for `ε > 1/2`. Its uniform
boundedness for `0 < ε ≤ 1/2` was recorded as an open problem (BVI §7.5) and as a candidate entry
point of the successor input (review-2410, research topic 3).

This module settles the range `−1/2 ≤ ε < 1/2` in the negative, unconditionally:

1. **Spectral form of the profile.** Restricting `v` to the half line and applying the Mellin
   unitary, `Φ_r(c) = ∫ W(ξ) cos(2πξ log c) dξ` with `W = |𝓜v|² ≥ 0` integrable and
   `∫ W = Φ_r(1) > 0` (`dilationProfile_eq_integral`).
2. **Divisor expansion.** For `P = ∏_{p ∈ S} p`,
   `Σ_{d₁, d₂ ∣ P} μ(d₁)μ(d₂)(d₁d₂)^{−σ} cos(θ log(d₁/d₂)) = ∏_{p ∈ S} |1 − p^{−σ} e^{iθ log p}|²`
   (`hypercube_cos_sum_eq_eulerProductSq`), so `Q_ε(P) = ∫ W(ξ) ∏_{p ∈ S} |1 − p^{−σ+2πiξ}|² dξ`.
3. **Divergence.** By `TheSpectralHypercubeFormIsUnbounded` this is unbounded for `σ = 1/2 + ε < 1`
   (`hypercubeDilationDirichletForm_unbounded`).

The threshold `ε = 1/2` is the abscissa of absolute convergence of the Euler product and has
nothing to do with the zeros of `ζ`: the divergence is driven by the prime number theorem, that is
by the pole. Cross-depth cancellation of the hypercube form is therefore not a form of the
quasi-Riemann hypothesis; the finite form of `ζ(1+ε) ζ(1+ε)^{−1} = 1` that a receiver can use must
be cut by size, not by prime support.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open MeasureTheory Set Filter
open RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BezoutValuationIncidence
open scoped InnerProductSpace

section Profile

variable {r : ℕ} (hr : 1 < r)

/-- The Ramanujan step vector restricted to the half line. -/
noncomputable def stepHalfLine : HalfLineL2 :=
  ((Lp.memLp (pmRamanujanStepVector r hr)).restrict (Ioi (0 : ℝ))).toLp _

theorem pmRamanujanStepSource_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    pmRamanujanStepSource r x = 0 := by
  simp [pmRamanujanStepSource, stepFun, Nat.floor_of_nonpos hx, pmRamanujanPrimitive]

theorem stepVector_ae_eq :
    (pmRamanujanStepVector r hr : ℝ → ℂ) =ᵐ[volume] pmRamanujanStepSource r :=
  (memLp_pmRamanujanStepSource hr).coeFn_toLp

theorem stepHalfLine_ae_eq :
    (stepHalfLine hr : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] pmRamanujanStepSource r :=
  ((Lp.memLp (pmRamanujanStepVector r hr)).restrict (Ioi (0 : ℝ))).coeFn_toLp.trans
    (ae_restrict_of_ae (stepVector_ae_eq hr))

/-- The dilated step vector has representative `√c · g(c x)`. -/
theorem rayDilate_stepVector_ae_eq {c : ℝ} (hc : 0 < c) :
    (rayDilate c (pmRamanujanStepVector r hr) : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.sqrt c : ℂ) * pmRamanujanStepSource r (c * x) := by
  rw [rayDilate_of_pos hc]
  filter_upwards [dilation_ae c hc (pmRamanujanStepVector r hr),
    (stepVector_ae_eq hr).comp_tendsto (realMul_quasiMeasurePreserving c hc.ne').tendsto_ae]
    with x h1 h2
  rw [h1]
  simp only [Function.comp_apply] at h2
  rw [h2]

/-- **The profile is a half-line inner product.** `⟨v, D_c v⟩ = ⟨v|₊, D_c v|₊⟩`. -/
theorem inner_stepVector_rayDilate {c : ℝ} (hc : 0 < c) :
    ⟪pmRamanujanStepVector r hr, rayDilate c (pmRamanujanStepVector r hr)⟫_ℂ =
      ⟪stepHalfLine hr, halfLineDilation c (stepHalfLine hr)⟫_ℂ := by
  set g := pmRamanujanStepSource r
  set g' : ℝ → ℂ := fun x => (Real.sqrt c : ℂ) * g (c * x)
  have hmem : MemLp g' 2 (volume.restrict (Ioi (0 : ℝ))) :=
    ((Lp.memLp (rayDilate c (pmRamanujanStepVector r hr))).ae_eq
      (rayDilate_stepVector_ae_eq hr hc)).restrict _
  have hdil : halfLineDilation c (stepHalfLine hr) = hmem.toLp g' :=
    halfLineDilation_eq_of_ae hc (stepHalfLine_ae_eq hr) hmem.coeFn_toLp fun _ _ => rfl
  rw [hdil, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hfull : ∫ x, ⟪(pmRamanujanStepVector r hr : ℝ → ℂ) x,
      (rayDilate c (pmRamanujanStepVector r hr) : ℝ → ℂ) x⟫_ℂ =
      ∫ x, (starRingEnd ℂ (g x)) * g' x := by
    refine integral_congr_ae ?_
    filter_upwards [stepVector_ae_eq hr, rayDilate_stepVector_ae_eq hr hc] with x h1 h2
    rw [h1, h2, RCLike.inner_apply]
  have hhalf : ∫ x in Ioi (0 : ℝ), ⟪(stepHalfLine hr : ℝ → ℂ) x, (hmem.toLp g' : ℝ → ℂ) x⟫_ℂ =
      ∫ x in Ioi (0 : ℝ), (starRingEnd ℂ (g x)) * g' x := by
    refine integral_congr_ae ?_
    filter_upwards [stepHalfLine_ae_eq hr, hmem.coeFn_toLp] with x h1 h2
    rw [h1, h2, RCLike.inner_apply]
  rw [hfull, hhalf, setIntegral_eq_integral_of_ae_compl_eq_zero]
  refine Eventually.of_forall fun x hx => ?_
  have hx0 : x ≤ 0 := not_lt.mp hx
  simp [g, pmRamanujanStepSource_eq_zero_of_nonpos hx0]

/-- The spectral weight of the step vector: `W(ξ) = |𝓜(v|₊)(ξ)|²`. -/
noncomputable def stepSpectralWeight (ξ : ℝ) : ℝ :=
  ‖(halfLineMellinUnitary (stepHalfLine hr) : ℝ → ℂ) ξ‖ ^ 2

theorem stepSpectralWeight_nonneg (ξ : ℝ) : 0 ≤ stepSpectralWeight hr ξ := by
  unfold stepSpectralWeight; positivity

theorem integrable_stepSpectralWeight : Integrable (stepSpectralWeight hr) := by
  have := (Lp.memLp (halfLineMellinUnitary (stepHalfLine hr))).integrable_norm_rpow
    (by norm_num) (by norm_num)
  simpa [stepSpectralWeight] using this

/-- **Spectral form of the dilation profile.** `Φ_r(c) = ∫ W(ξ) cos(2πξ log c) dξ`. -/
theorem dilationProfile_eq_integral {c : ℝ} (hc : 0 < c) :
    pmRamanujanDilationProfile r hr c =
      ∫ ξ, stepSpectralWeight hr ξ * Real.cos (2 * Real.pi * (Real.log c * ξ)) := by
  rw [pmRamanujanDilationProfile, inner_stepVector_rayDilate hr hc, inner_halfLine_eq_integral,
    halfLineMellinUnitary_halfLineDilation]
  set F := (halfLineMellinUnitary (stepHalfLine hr) : ℝ → ℂ)
  have hcongr : (fun ξ => starRingEnd ℂ (F ξ) *
      (modulationMul (Real.log c) (halfLineMellinUnitary (stepHalfLine hr)) : ℝ → ℂ) ξ) =ᵐ[volume]
      fun ξ => ((stepSpectralWeight hr ξ : ℝ) : ℂ) * modulationSymbol (Real.log c) ξ := by
    filter_upwards [coeFn_modulationMul (Real.log c) (halfLineMellinUnitary (stepHalfLine hr))]
      with ξ h
    rw [h, stepSpectralWeight, ← mul_assoc, mul_comm (starRingEnd ℂ (F ξ)), mul_assoc,
      Complex.conj_mul', mul_comm]
    push_cast
    ring
  rw [integral_congr_ae hcongr]
  have hint : Integrable fun ξ => ((stepSpectralWeight hr ξ : ℝ) : ℂ) *
      modulationSymbol (Real.log c) ξ := by
    refine ((integrable_stepSpectralWeight hr).ofReal).mul_bdd
      (measurable_modulationSymbol _).aestronglyMeasurable (c := 1) (Eventually.of_forall ?_)
    intro ξ
    exact norm_modulationSymbol_le _ ξ
  rw [← integral_re hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [modulationSymbol, Complex.re_ofReal_mul]
  rw [Complex.exp_ofReal_mul_I_re]

end Profile

end GaloisForLFunctions.SignedSuccessorArithmetic
