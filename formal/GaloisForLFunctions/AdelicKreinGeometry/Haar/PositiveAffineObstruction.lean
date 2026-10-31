import GaloisForLFunctions.AdelicKreinGeometry.Haar.ScaledHaarObstruction
import GaloisForLFunctions.AdelicKreinGeometry.TheIndexOfAnInducedState
import GaloisForLFunctions.BiarithmeticGeometry.Affine.PositiveAffineIndex

/-!
# The Haar obstruction on positive rational slopes

Extension by zero transfers the rational-affine obstruction through the positive-slope
subgroup, whose index is two.
-/

open Filter Topology
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- Extension by zero from positive slopes costs at most two copies of a finite index bound. -/
theorem negIndex_extend_posAffine_le {k : posAffine → ℂ} (hk : IsHermKernel k)
    {r : ℕ} (hi : negIndex k ≤ r) :
    negIndex (extendFromSubgroup posAffine k) ≤ ((2 * r : ℕ) : ℕ∞) := by
  simpa only [posAffine_index] using negIndex_extendFromSubgroup_le hk hi

/-- The nonzero scaled Haar obstruction holds on the positive-slope rational affine group. -/
theorem negIndex_posAffine_eq_top_of_nonzero_haar_continuous_dilation
    {k : posAffine → ℂ} {z : ℂ} (hk : IsHermKernel k) (hz : z ≠ 0)
    (hs : ∀ b : ℚ, k (posAffineTranslation b) = if b.den = 1 then z else 0)
    {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hdil : ∀ u : posUnits, k (posAffineDilation u) = f ((u : ℚˣ) : ℚ)) :
    negIndex k = ⊤ := by
  let K := extendFromSubgroup posAffine k
  have hK : IsHermKernel K :=
    GaloisForLFunctions.AdelicKreinGeometry.IsHermKernel.extendFromSubgroup hk
  have hS (b : ℚ) : K (translation b) = if b.den = 1 then z else 0 := by
    change extendFromSubgroup posAffine k (posAffineTranslation b) = _
    rw [extendFromSubgroup_subtype]
    exact hs b
  have hD (u : ℚˣ) (hu : 0 < (u : ℚ)) : K (dilation u) = f (u : ℚ) := by
    change extendFromSubgroup posAffine k (posAffineDilation ⟨u, hu⟩) = _
    rw [extendFromSubgroup_subtype]
    exact hdil ⟨u, hu⟩
  have htop := negIndex_eq_top_of_nonzero_haar_continuous_dilation hK hz hS hf hD
  have hno (r : ℕ) (hi : negIndex k ≤ r) : False := by
    have hb := negIndex_extend_posAffine_le hk hi
    rw [htop] at hb
    exact (not_le_of_gt (ENat.coe_lt_top (2 * r))) hb
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  by_contra hn
  exact hno n (le_of_lt (lt_of_not_ge hn))

/-- The Haar obstruction already holds on the positive-slope rational affine group. -/
theorem negIndex_posAffine_eq_top_of_haar_continuous_dilation {k : posAffine → ℂ}
    (hk : IsHermKernel k)
    (hs : ∀ b : ℚ, k (posAffineTranslation b) = if b.den = 1 then 1 else 0)
    {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hdil : ∀ u : posUnits, k (posAffineDilation u) = f ((u : ℚˣ) : ℚ)) :
    negIndex k = ⊤ :=
  negIndex_posAffine_eq_top_of_nonzero_haar_continuous_dilation hk one_ne_zero hs hf hdil

#print axioms negIndex_extend_posAffine_le
#print axioms negIndex_posAffine_eq_top_of_nonzero_haar_continuous_dilation
#print axioms negIndex_posAffine_eq_top_of_haar_continuous_dilation
end GaloisForLFunctions.AdelicKreinGeometry
