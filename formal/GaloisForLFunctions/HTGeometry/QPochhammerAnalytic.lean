import GaloisForLFunctions.HTGeometry.MultiplicativeTheta
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Analytic q-Pochhammer product
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One linear factor of `(z;q)_∞`. -/
def qPochhammerFactor (q : EulerNome) (n : ℕ) (z : ℂ) : ℂ :=
  1 - z * (q : ℂ) ^ n

/-- The q-Pochhammer product converges locally uniformly on the complex plane. -/
theorem hasProdLocallyUniformlyOn_qPochhammerFactor (q : EulerNome) :
    HasProdLocallyUniformlyOn (qPochhammerFactor q) (fun z => qPochhammerInf z q)
      Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨C, hC⟩ := hK.bddAbove_image continuous_norm.continuousOn
  let D : ℝ := max C 0
  have hD : ∀ z ∈ K, ‖z‖ ≤ D := by
    intro z hz
    exact (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hweights : Summable (fun n : ℕ => ‖(q : ℂ)‖ ^ n) :=
    by simpa only [norm_neg, one_mul, norm_pow, norm_one, one_mul] using
      (qPochhammer_summable_defect (1 : ℂ) q).norm
  have hu : Summable (fun n : ℕ => D * ‖(q : ℂ)‖ ^ n) := hweights.mul_left D
  have hbound : ∀ᶠ n : ℕ in cofinite, ∀ z ∈ K,
      ‖-(z * (q : ℂ) ^ n)‖ ≤ D * ‖(q : ℂ)‖ ^ n := by
    filter_upwards with n
    intro z hz
    simp only [norm_neg, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hD z hz) (pow_nonneg (norm_nonneg _) _)
  convert! Summable.hasProdUniformlyOn_one_add hK hu hbound (fun n => by
    exact ((continuous_id.mul continuous_const).neg).continuousOn) using 1

/-- Every q-Pochhammer factor is entire. -/
theorem differentiable_qPochhammerFactor (q : EulerNome) (n : ℕ) :
    Differentiable ℂ (qPochhammerFactor q n) := by
  intro z
  exact (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)).differentiableAt

/-- The infinite q-Pochhammer product is entire in its first argument. -/
theorem differentiable_qPochhammerInf (q : EulerNome) :
    Differentiable ℂ (fun z => qPochhammerInf z q) := by
  have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    (hasProdLocallyUniformlyOn_qPochhammerFactor q)
  have hd : ∀ᶠ S : Finset ℕ in atTop,
      DifferentiableOn ℂ (fun z => ∏ n ∈ S, qPochhammerFactor q n z) Set.univ := by
    filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun n _ =>
      (differentiable_qPochhammerFactor q n).differentiableOn
  intro z
  simpa only [differentiableWithinAt_univ] using
    ht.differentiableOn hd isOpen_univ z (Set.mem_univ z)

/-- The q-Pochhammer product is analytic at every complex point. -/
theorem analyticAt_qPochhammerInf (q : EulerNome) (z : ℂ) :
    AnalyticAt ℂ (fun w => qPochhammerInf w q) z :=
  (differentiable_qPochhammerInf q).analyticAt z

end

end GaloisForLFunctions.HTGeometry
