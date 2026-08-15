import GaloisForLFunctions.RHTower.WallBlockSliceProfile
import GaloisForLFunctions.RHTower.WallBlockSourceExpansion

/-!
# The first boundary term as a Laplace superposition

The first boundary term produced by the two-fold integration by parts is, after propagation, the
block average of `e^{-ixL}C(x,L)^{-1}g(L)`.  It does not decay in the frequency, so its square
integrability cannot come from a power bound; what makes it square integrable is that the resolvent
is a Laplace transform of the accretive semigroup, which turns the term into a superposition of
slices

`∫₀^∞ e^{-sB(x+iσ)} Ψ(x,s) ds`,   `Ψ(x,s) = ∫ e^{-ixL}e^{-Ls}g(L)dL`.

The interchange of the block and the Laplace ray is dominated: the semigroup contributes `e^{-μ s}`
from the numerical floor and the physical weight contributes `e^{-Ls} ≤ e^{-ms}` on the block, so the
joint integrand is dominated by the product `‖g(L)‖·e^{-μ₀ s}` with `μ₀ ≤ floor + m`.  The semigroup
then leaves the block integral because it is a bounded operator, and what remains inside is exactly
the angular transform of the weighted profile.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {T : X →L[ℂ] X}

/-- The first boundary term of the propagated expansion, as a block average. -/
def firstBoundary (T : X →L[ℂ] X) (g : ℝ → X) (σ x : ℝ) : X :=
  ∫ L : ℝ, Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
    • (invFamily (wallGeneratorShift T σ L) x (g L))

/-- The joint integrand of the Laplace superposition. -/
def firstBoundaryKernel (T : X →L[ℂ] X) (g : ℝ → X) (σ x : ℝ) (L s : ℝ) : X :=
  Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
    • (Real.exp (-(L * s)) • accretiveSemigroup (wallGenerator T σ x) s (g L))

theorem norm_firstBoundaryKernel_le {σ m μ₀ : ℝ} {g : ℝ → X}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    {x : ℝ} (hfloor : μ₀ ≤ wallFloor T σ x + m) (L : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ‖firstBoundaryKernel T g σ x L s‖ ≤ ‖g L‖ * Real.exp (-(μ₀ * s)) := by
  by_cases hL : L ∈ Icc m (m + 1)
  · have hLm : m ≤ L := hL.1
    have hB : ∀ u : X, wallFloor T σ x * ‖u‖ ^ 2 ≤ (inner ℂ (wallGenerator T σ x u) u).re :=
      fun u => re_inner_wallGenerator_ge hσ0 hσ1 x u
    have hsem := norm_accretiveSemigroup_apply_le hB (g L) hs
    have hexp : Real.exp (-(L * s)) * Real.exp (-(wallFloor T σ x * s))
        ≤ Real.exp (-(μ₀ * s)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hs, hLm, hfloor]
    rw [firstBoundaryKernel, norm_smul, norm_expPhase, one_mul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-(L * s)) * ‖accretiveSemigroup (wallGenerator T σ x) s (g L)‖
        ≤ Real.exp (-(L * s)) * (Real.exp (-(wallFloor T σ x * s)) * ‖g L‖) :=
          mul_le_mul_of_nonneg_left hsem (Real.exp_pos _).le
      _ = (Real.exp (-(L * s)) * Real.exp (-(wallFloor T σ x * s))) * ‖g L‖ := by ring
      _ ≤ Real.exp (-(μ₀ * s)) * ‖g L‖ :=
          mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
      _ = ‖g L‖ * Real.exp (-(μ₀ * s)) := by ring
  · rw [firstBoundaryKernel, hsupp L hL]
    simp

/-! ## The superposition identity -/

theorem continuous_accretiveSemigroup (B : X →L[ℂ] X) :
    Continuous (fun s : ℝ => accretiveSemigroup B s) := by
  have hfun : (fun s : ℝ => NormedSpace.exp (s • (-B))) = fun s : ℝ => accretiveSemigroup B s := by
    funext s
    rw [accretiveSemigroup_eq]
  rw [← hfun, continuous_iff_continuousAt]
  intro s
  exact (hasDerivAt_exp_smul_const (-B) s).continuousAt

theorem aestronglyMeasurable_firstBoundaryKernel {σ x : ℝ} {g : ℝ → X}
    (hg : AEStronglyMeasurable g (volume : Measure ℝ)) :
    AEStronglyMeasurable (Function.uncurry (firstBoundaryKernel T g σ x))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hgfst : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := hg.comp_fst
  have hsnd : AEStronglyMeasurable
      (fun p : ℝ × ℝ => accretiveSemigroup (wallGenerator T σ x) p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (continuous_accretiveSemigroup (wallGenerator T σ x)).aestronglyMeasurable.comp_snd
  have hev : AEStronglyMeasurable
      (fun p : ℝ × ℝ => accretiveSemigroup (wallGenerator T σ x) p.2 (g p.1))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    ContinuousLinearMap.aestronglyMeasurable_comp₂ (ContinuousLinearMap.apply ℂ X) hgfst hsnd
  have hw : AEStronglyMeasurable (fun p : ℝ × ℝ => Real.exp (-(p.1 * p.2)))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    fun_prop
  have hph : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Complex.exp (-(Complex.I) * (p.1 : ℂ) * (x : ℂ)))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have : Continuous fun p : ℝ × ℝ => Complex.exp (-(Complex.I) * (p.1 : ℂ) * (x : ℂ)) := by
      fun_prop
    exact this.aestronglyMeasurable
  exact hph.smul (hw.smul hev)

/-- **The first boundary term is a Laplace superposition of semigroup slices.** -/
theorem firstBoundary_eq_laplace {σ m μ₀ : ℝ} {g : ℝ → X}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    {x : ℝ} (hfloor : μ₀ ≤ wallFloor T σ x + m) :
    firstBoundary T g σ x
      = ∫ s in Ioi (0 : ℝ), accretiveSemigroup (wallGenerator T σ x) s (blockSlice g s x) := by
  have hg1 : Integrable g := integrable_zeroExtension hg2 hsupp
  -- step 1: replace the resolvent by its orbit integral
  have hstep1 : firstBoundary T g σ x
      = ∫ L : ℝ, ∫ s in Ioi (0 : ℝ), firstBoundaryKernel T g σ x L s := by
    rw [firstBoundary]
    refine integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
    show Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
        • (invFamily (wallGeneratorShift T σ L) x (g L))
        = ∫ s in Ioi (0 : ℝ), firstBoundaryKernel T g σ x L s
    by_cases hL : L ∈ Icc m (m + 1)
    · have hgap : 0 < wallFloor T σ x + L := by
        have hLm : m ≤ L := hL.1
        linarith
      rw [invFamily_wallGeneratorShift_eq_laplace hσ0 hσ1 hgap (g L),
        ← integral_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      rfl
    · rw [hsupp L hL]
      have hzero : ∀ s : ℝ, firstBoundaryKernel T g σ x L s = 0 := by
        intro s
        rw [firstBoundaryKernel, hsupp L hL]
        simp
      simp only [map_zero, smul_zero]
      rw [integral_congr_ae (Filter.Eventually.of_forall hzero), integral_zero]
  -- step 2: Fubini
  have hw₂ : IntegrableOn (fun s : ℝ => Real.exp (-(μ₀ * s))) (Ioi (0 : ℝ)) := by
    simpa using exp_neg_integrableOn_Ioi (0 : ℝ) hμ
  have hbound : ∀ᵐ p ∂((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))),
      ‖Function.uncurry (firstBoundaryKernel T g σ x) p‖ ≤ ‖g p.1‖ * Real.exp (-(μ₀ * p.2)) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioi)] with p hp
    exact norm_firstBoundaryKernel_le hσ0 hσ1 hsupp hfloor p.1 (le_of_lt hp.2)
  have hswap := integral_swap_of_dominated_prod hg1.norm hw₂
    (aestronglyMeasurable_firstBoundaryKernel hg2.aestronglyMeasurable) hbound
  rw [hstep1, hswap]
  -- step 3: the semigroup leaves the block integral
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
  have hint : Integrable (fun L : ℝ =>
      Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) • blockWeighted g s L) := by
    refine Integrable.mono' (hg1.norm.const_mul (Real.exp (-(m * s)))) ?_
      (Filter.Eventually.of_forall fun L => ?_)
    · exact (continuous_expPhase_block x).aestronglyMeasurable.smul
        (aestronglyMeasurable_blockWeighted hg1.aestronglyMeasurable)
    · rw [norm_smul, norm_expPhase, one_mul]
      exact norm_blockWeighted_le hs0 hsupp L
  have hker : ∀ L : ℝ, firstBoundaryKernel T g σ x L s
      = accretiveSemigroup (wallGenerator T σ x) s
        (Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) • blockWeighted g s L) := by
    intro L
    rw [firstBoundaryKernel, blockWeighted, map_smul,
      ContinuousLinearMap.map_smul_of_tower]
  have hslice : blockSlice g s x
      = ∫ L : ℝ, Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) • blockWeighted g s L := by
    rw [blockSlice, vectorAngularTransform]
    refine integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
    have hcomm : -(Complex.I) * (x : ℂ) * (L : ℂ) = -(Complex.I) * (L : ℂ) * (x : ℂ) := by ring
    show Complex.exp (-(Complex.I) * (x : ℂ) * (L : ℂ)) • blockWeighted g s L
        = Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) • blockWeighted g s L
    rw [hcomm]
  rw [integral_congr_ae (Filter.Eventually.of_forall hker),
    ContinuousLinearMap.integral_comp_comm _ hint, hslice]

end GaloisForLFunctions.RHTower
