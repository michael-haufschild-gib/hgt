import GaloisForLFunctions.RHTower.WallForcedProfileMemLp

/-!
# The Gamma-wall block Hardy transfer

The one-block estimate has the block weight `e^{max(0,−m)}`, exactly the weight of the physical
source norm

`N_σ(G) = Σ_m e^{max(0,−m)} ‖e^{σL}G‖_{L²(I_m;X)}`.

So when that norm is finite the block solutions are absolutely summable in `L²(ℝ;X)`, hence
summable: the series of block solutions converges.  Nothing here is a limit theorem about the
individual blocks — the whole content is that the estimate's weight is the norm's weight.

The second half of the transfer is Plancherel: the physical profile and the transported profile have
proportional `L²` norms, so the shifted-line `L²` condition on the solution is exactly the weighted
`L²` condition on its physical boundary value.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- **`(24)`: the block series converges in `L²`.** -/
theorem summable_blockSolutions
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {G : ℤ → ℝ → X} (hG2 : ∀ k : ℤ, MemLp (G k) 2 (volume : Measure ℝ))
    (hGm : ∀ k : ℤ, StronglyMeasurable (G k))
    (hsupp : ∀ k : ℤ, ∀ L : ℝ, L ∉ Icc (k : ℝ) ((k : ℝ) + 1) → G k L = 0)
    (hN : Summable fun k : ℤ =>
      Real.exp (max 0 (-(k : ℝ))) * Real.sqrt (∫ L : ℝ, ‖G k L‖ ^ 2)) :
    Summable fun k : ℤ =>
      (memLp_forcedProfile_blockSource hEdiff hE hEne hT hσ0 hσ1 (hG2 k) (hGm k) (hsupp k)
        (0 : X)).toLp _ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_bound_eLpNorm_forcedProfile_blockSource hEdiff hE hEne hT hσ0 hσ1
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hN.mul_left C)
  rw [Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  have h := hbound (G k) 0 (k : ℝ) (hG2 k) (hGm k) (hsupp k)
  simpa using h

/-- **`(25)`: Plancherel on the shifted line.**  The physical profile and the transported profile
have proportional `L²` norms, so the shifted-line `L²` condition on the solution is exactly the
weighted `L²` condition on its physical boundary value. -/
theorem eLpNorm_vectorAngularTransform_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {f : ℝ → H} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    eLpNorm (vectorAngularTransform f) 2 (volume : Measure ℝ)
      = ENNReal.ofReal (Real.sqrt (2 * Real.pi)) * eLpNorm f 2 (volume : Measure ℝ) := by
  have hsq : Integrable (fun x : ℝ => ‖f x‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hf2.aestronglyMeasurable).mp hf2
  have hsqT : Integrable (fun z : ℝ => ‖vectorAngularTransform f z‖ ^ 2) (volume : Measure ℝ) :=
    integrable_norm_sq_vectorAngularTransform hf1 hf2
  have hI0 : (0 : ℝ) ≤ ∫ x : ℝ, ‖f x‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hL : (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) = ENNReal.ofReal (∫ x : ℝ, ‖f x‖ ^ 2) :=
    lintegral_enorm_sq_eq_ofReal_integral hsq
  have hLT : (∫⁻ z : ℝ, ‖vectorAngularTransform f z‖ₑ ^ 2)
      = ENNReal.ofReal ((2 * Real.pi) * ∫ x : ℝ, ‖f x‖ ^ 2) := by
    rw [lintegral_enorm_sq_eq_ofReal_integral hsqT,
      integral_norm_sq_vectorAngularTransform_eq hf1 hf2]
  rw [eLpNorm_two_eq_sq, eLpNorm_two_eq_sq, hL, hLT,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hI0 (by norm_num), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (by positivity), ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

end GaloisForLFunctions.RHTower
