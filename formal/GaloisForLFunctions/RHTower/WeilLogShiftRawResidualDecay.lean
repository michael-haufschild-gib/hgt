import GaloisForLFunctions.RHTower.WeilLogShiftResidualContraction
import GaloisForLFunctions.RHTower.WeilLogShiftActualVarianceLimit
import GaloisForLFunctions.RHTower.WeilLogShiftJointCharacteristic

/-! The centered index and scaled correction agree in raw mean square and first moment. -/

open Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower

theorem tendsto_finiteWeilCanonicalFluctuationResidual_zero (t : ℕ → ℕ) :
    Tendsto (fun r => finiteWeilCanonicalFluctuationResidual r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun r : ℕ => ((r + 1 : ℕ) : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_mono (fun r => by exact_mod_cast Nat.le_succ r)
      tendsto_natCast_atTop_atTop
  apply squeeze_zero (fun r => finiteWeilCanonicalFluctuationResidual_nonneg r _)
    (fun r => finiteWeilCanonicalFluctuationResidual_quadratic_variance_bound r (t r))
  have hu := (tendsto_finiteWeilCanonicalEdgeIndexVariance_quarter t).mul
    (tendsto_inv_atTop_zero.comp hn)
  simp only [mul_zero] at hu
  convert hu using 1
  funext r
  dsimp
  ring

def finiteWeilCanonicalRawFluctuationGap (r k : ℕ) : ℝ :=
  ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
    |finiteWeilCanonicalFluctuationResidualValue r k i|

theorem finiteWeilCanonicalRawFluctuationGap_nonneg (r k : ℕ) :
    0 ≤ finiteWeilCanonicalRawFluctuationGap r k :=
  Finset.sum_nonneg fun i _ =>
    mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (abs_nonneg _)

theorem finiteWeilCanonicalRawFluctuationGap_sq_le (r k : ℕ) :
    finiteWeilCanonicalRawFluctuationGap r k ^ 2 ≤ finiteWeilCanonicalFluctuationResidual r k := by
  let m := finiteWeilCanonicalEdgeMass r k
  let D := finiteWeilCanonicalFluctuationResidualValue r k
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin (r + 1)))
    (r := fun i => m i * |D i|) (f := fun i => m i * D i ^ 2) (g := m)
    (fun i _ => mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (sq_nonneg _))
    (fun i _ => (finiteWeilCanonicalEdgeMass_pos r k i).le)
    (fun i _ => le_of_eq (by rw [mul_pow, sq_abs]; ring))
  change finiteWeilCanonicalRawFluctuationGap r k ^ 2 ≤
    finiteWeilCanonicalFluctuationResidual r k * (∑ i, finiteWeilCanonicalEdgeMass r k i) at h
  simpa only [finiteWeilCanonicalEdgeMass_sum, mul_one] using h

theorem finiteWeilCanonicalRawFluctuationGap_le_sqrt (r k : ℕ) :
    finiteWeilCanonicalRawFluctuationGap r k ≤ Real.sqrt (finiteWeilCanonicalFluctuationResidual r k) :=
  (Real.le_sqrt (finiteWeilCanonicalRawFluctuationGap_nonneg r k)
    (finiteWeilCanonicalFluctuationResidual_nonneg r k)).mpr
    (finiteWeilCanonicalRawFluctuationGap_sq_le r k)

theorem tendsto_finiteWeilCanonicalRawFluctuationGap_zero (t : ℕ → ℕ) :
    Tendsto (fun r => finiteWeilCanonicalRawFluctuationGap r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun r => finiteWeilCanonicalRawFluctuationGap_nonneg r _)
    (fun r => finiteWeilCanonicalRawFluctuationGap_le_sqrt r _)
  have h := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_finiteWeilCanonicalFluctuationResidual_zero t)
  rw [Real.sqrt_zero] at h
  convert h using 1
  funext r
  rfl

end RHTower
