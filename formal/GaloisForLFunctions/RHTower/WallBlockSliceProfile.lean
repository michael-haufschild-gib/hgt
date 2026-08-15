import GaloisForLFunctions.RHTower.WallResolventLaplace
import GaloisForLFunctions.RHTower.SuzukiWallBlockSliceBound
import GaloisForLFunctions.RHTower.VectorFourierPlancherelIntegral
import GaloisForLFunctions.HTGeometry.BlockWindowFubini

/-!
# The slice profile of the first boundary term

Substituting the Laplace representation of the resolvent into the first boundary term turns it into a
superposition of semigroup slices, and each slice acts on the *angular transform of the weighted
block profile*

`Ψ(x,s) = ∫_{I_m} e^{-ixL} e^{-Ls} g(L) dL`.

Its frequency energy is computed exactly: Plancherel in the angular convention contributes `2π`, and
the physical weight `e^{-Ls}` on a block supported in `[m, m+1]` contributes `e^{-2sm}`, because
`L ≥ m` there.  So

`∫ ‖Ψ(·,s)‖² = 2π e^{-2sm} ∫ ‖g‖²`,

which is the slice hypothesis of the block Laplace bound; combined with the semigroup rate it makes
the two exponentials add, and the block index cancels against the frequency threshold.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- The block profile weighted by the Laplace parameter. -/
def blockWeighted (g : ℝ → X) (s : ℝ) : ℝ → X := fun L => Real.exp (-(L * s)) • g L

/-- The slice profile of the Laplace superposition: the angular transform of the weighted
profile. -/
def blockSlice (g : ℝ → X) (s x : ℝ) : X := vectorAngularTransform (blockWeighted g s) x

omit [InnerProductSpace ℂ X] [CompleteSpace X] in
/-- A zero-extended square-integrable block profile is integrable. -/
theorem integrable_zeroExtension {g : ℝ → X} {m : ℝ} (hg2 : MemLp g 2 (volume : Measure ℝ))
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) : Integrable g := by
  have hfin : IsFiniteMeasure (volume.restrict (Icc m (m + 1))) :=
    ⟨by simp [Real.volume_Icc]⟩
  have hon : IntegrableOn g (Icc m (m + 1)) :=
    (hg2.restrict (Icc m (m + 1))).integrable (by norm_num)
  have hcompl : IntegrableOn g (Icc m (m + 1))ᶜ := by
    refine IntegrableOn.congr_fun (integrable_zero ℝ X volume).integrableOn ?_
      measurableSet_Icc.compl
    intro L hL
    exact (hsupp L hL).symm
  have hall : IntegrableOn g (Icc m (m + 1) ∪ (Icc m (m + 1))ᶜ) := hon.union hcompl
  rw [union_compl_self, integrableOn_univ] at hall
  exact hall

omit [CompleteSpace X] in
theorem norm_blockWeighted_le {g : ℝ → X} {m s : ℝ} (hs : 0 ≤ s)
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) (L : ℝ) :
    ‖blockWeighted g s L‖ ≤ Real.exp (-(m * s)) * ‖g L‖ := by
  by_cases hL : L ∈ Icc m (m + 1)
  · have hLm : m ≤ L := hL.1
    have hexp : Real.exp (-(L * s)) ≤ Real.exp (-(m * s)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hs, hLm]
    rw [blockWeighted, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  · rw [blockWeighted, hsupp L hL]
    simp

omit [CompleteSpace X] in
theorem aestronglyMeasurable_blockWeighted {g : ℝ → X} {s : ℝ}
    (hg : AEStronglyMeasurable g (volume : Measure ℝ)) :
    AEStronglyMeasurable (blockWeighted g s) (volume : Measure ℝ) :=
  (by fun_prop : Continuous fun L : ℝ => Real.exp (-(L * s))).aestronglyMeasurable.smul hg

omit [CompleteSpace X] in
theorem integrable_blockWeighted {g : ℝ → X} {m s : ℝ} (hs : 0 ≤ s)
    (hg1 : Integrable g) (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    Integrable (blockWeighted g s) := by
  refine Integrable.mono' (hg1.norm.const_mul (Real.exp (-(m * s))))
    (aestronglyMeasurable_blockWeighted hg1.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun L => norm_blockWeighted_le hs hsupp L)

omit [CompleteSpace X] in
theorem memLp_blockWeighted {g : ℝ → X} {m s : ℝ} (hs : 0 ≤ s)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    MemLp (blockWeighted g s) 2 (volume : Measure ℝ) := by
  refine MemLp.of_le (hg2.const_smul (Real.exp (-(m * s))))
    (aestronglyMeasurable_blockWeighted hg2.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun L => ?_)
  refine le_trans (norm_blockWeighted_le hs hsupp L) (le_of_eq ?_)
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]

/-! ## The slice bound -/

omit [CompleteSpace X] in
theorem integral_norm_sq_blockWeighted_le {g : ℝ → X} {m s : ℝ} (hs : 0 ≤ s)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    (∫ L : ℝ, ‖blockWeighted g s L‖ ^ 2)
      ≤ Real.exp (-(2 * s * m)) * ∫ L : ℝ, ‖g L‖ ^ 2 := by
  have hgsq : Integrable (fun L : ℝ => ‖g L‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hg2.aestronglyMeasurable).mp hg2
  have hwsq : Integrable (fun L : ℝ => ‖blockWeighted g s L‖ ^ 2) (volume : Measure ℝ) := by
    have hw := memLp_blockWeighted hs hg2 hsupp
    exact (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw
  have hpt : ∀ L : ℝ, ‖blockWeighted g s L‖ ^ 2
      ≤ Real.exp (-(2 * s * m)) * ‖g L‖ ^ 2 := by
    intro L
    have hbase := norm_blockWeighted_le hs hsupp L
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hbase 2
    refine hsq.trans (le_of_eq ?_)
    have hexp : Real.exp (-(m * s)) ^ 2 = Real.exp (-(2 * s * m)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [mul_pow, hexp]
  calc (∫ L : ℝ, ‖blockWeighted g s L‖ ^ 2)
      ≤ ∫ L : ℝ, Real.exp (-(2 * s * m)) * ‖g L‖ ^ 2 :=
        integral_mono hwsq (hgsq.const_mul _) hpt
    _ = Real.exp (-(2 * s * m)) * ∫ L : ℝ, ‖g L‖ ^ 2 := integral_const_mul _ _

/-- **The slice bound.**  The Laplace slice of the block profile has frequency energy
`2π e^{-2sm}` times the physical block energy: Plancherel supplies the `2π` and the physical weight
supplies the block rate. -/
theorem integral_norm_sq_blockSlice_le {g : ℝ → X} {m s : ℝ} (hs : 0 ≤ s)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    (∫ x : ℝ, ‖blockSlice g s x‖ ^ 2)
      ≤ Real.exp (-(2 * s * m)) * ((2 * Real.pi) * ∫ L : ℝ, ‖g L‖ ^ 2) := by
  have hg1 : Integrable g := integrable_zeroExtension hg2 hsupp
  have hw1 : Integrable (blockWeighted g s) := integrable_blockWeighted hs hg1 hsupp
  have hw2 : MemLp (blockWeighted g s) 2 (volume : Measure ℝ) := memLp_blockWeighted hs hg2 hsupp
  have hpar := integral_norm_sq_vectorAngularTransform_eq hw1 hw2
  have hbase := integral_norm_sq_blockWeighted_le hs hg2 hsupp
  calc (∫ x : ℝ, ‖blockSlice g s x‖ ^ 2)
      = (2 * Real.pi) * ∫ L : ℝ, ‖blockWeighted g s L‖ ^ 2 := hpar
    _ ≤ (2 * Real.pi) * (Real.exp (-(2 * s * m)) * ∫ L : ℝ, ‖g L‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = Real.exp (-(2 * s * m)) * ((2 * Real.pi) * ∫ L : ℝ, ‖g L‖ ^ 2) := by ring

end GaloisForLFunctions.RHTower
