import GaloisForLFunctions.RHTower.WallOneBlockEstimate

/-!
# The block solution as an element of `L²`

The one-block estimate bounds the extended squared mass of the block solution.  To sum the blocks
one needs the solution as a point of the Banach space `L²(ℝ;X)`, which asks for two more things:
that it is measurable, and that the estimate reads as a bound on its norm.

Measurability comes from continuity, and continuity from the primitive: the transported source is
interval integrable on every interval, so its primitive is continuous, and the Gamma transport is
continuous along the shifted line.

The norm bound is the square root of the estimate, `√(a²+b²) ≤ a + b`, which is the form the block
series needs.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

omit [Nontrivial X] in
/-- **The block solution is continuous.** -/
theorem continuous_forcedProfile_blockSource
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m : ℝ} (hg : IntegrableOn g (Icc m (m + 1))) (c : X) :
    Continuous (forcedProfile E T (blockSource g m) c σ) := by
  have hH : Continuous fun x : ℝ => stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) :=
    continuous_stripPropagator_line hEdiff hE hEne hσ0 hσ1
  have hprim : Continuous fun x : ℝ =>
      ∫ t in (0 : ℝ)..x, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)
        (blockSource g m t) :=
    intervalIntegral.continuous_primitive
      (fun a b => intervalIntegrable_stripPropagatorInv_blockSource hEdiff hE hEne hσ0 hσ1 hg a b) 0
  have h1 : Continuous fun x : ℝ => stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c :=
    hH.clm_apply continuous_const
  have h2 : Continuous fun x : ℝ => forcedWindowPart E T (blockSource g m) σ x :=
    hH.clm_apply hprim
  exact h1.add h2

omit [InnerProductSpace ℂ X] [CompleteSpace X] [Nontrivial X] in
/-- The `L²` norm of a profile, as the square root of its extended squared mass. -/
theorem eLpNorm_two_eq_sq {f : ℝ → X} :
    eLpNorm f 2 (volume : Measure ℝ) = (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) ^ ((1 : ℝ) / 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num

/-- **The block solution lies in `L²`.** -/
theorem memLp_forcedProfile_blockSource
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m : ℝ} (hg2 : MemLp g 2 (volume : Measure ℝ))
    (hgm : StronglyMeasurable g) (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) (c : X) :
    MemLp (forcedProfile E T (blockSource g m) c σ) 2 (volume : Measure ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_bound_lintegral_sq_forcedProfile_oneBlock hEdiff hE hEne hT hσ0 hσ1
  have hg1 : Integrable g := integrable_zeroExtension hg2 hsupp
  refine ⟨(continuous_forcedProfile_blockSource hEdiff hE hEne hσ0 hσ1 hg1.integrableOn
    c).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_two_eq_sq]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound g c m hg2 hgm hsupp)

/-- **The `L²` norm of a block solution.** -/
theorem exists_bound_eLpNorm_forcedProfile_blockSource
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℝ → X) (c : X) (m : ℝ),
      MemLp g 2 (volume : Measure ℝ) → StronglyMeasurable g →
      (∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) →
      eLpNorm (forcedProfile E T (blockSource g m) c σ) 2 (volume : Measure ℝ)
        ≤ ENNReal.ofReal
            (C * (‖c‖ + Real.exp (max 0 (-m)) * Real.sqrt (∫ L : ℝ, ‖g L‖ ^ 2))) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_bound_lintegral_sq_forcedProfile_oneBlock hEdiff hE hEne hT hσ0 hσ1
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun g c m hg2 hgm hsupp => ?_⟩
  set N : ℝ := ∫ L : ℝ, ‖g L‖ ^ 2 with hNdef
  have hN0 : 0 ≤ N := integral_nonneg fun _ => by positivity
  set a : ℝ := ‖c‖ with hadef
  set b : ℝ := Real.exp (max 0 (-m)) * Real.sqrt N with hbdef
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := by positivity
  have hbsq : b ^ 2 = Real.exp (2 * max 0 (-m)) * N := by
    rw [hbdef, mul_pow, Real.sq_sqrt hN0, ← Real.exp_nat_mul]
    norm_num
  rw [eLpNorm_two_eq_sq]
  have hstep : (∫⁻ x : ℝ, ‖forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (C * (a ^ 2 + b ^ 2))) ^ ((1 : ℝ) / 2) := by
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [hbsq, hadef]
    exact hbound g c m hg2 hgm hsupp
  refine hstep.trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hC]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hle : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by nlinarith
  calc Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt ((a + b) ^ 2) := Real.sqrt_le_sqrt hle
    _ = a + b := Real.sqrt_sq (by positivity)

end GaloisForLFunctions.RHTower
