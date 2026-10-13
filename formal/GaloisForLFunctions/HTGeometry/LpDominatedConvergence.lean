import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Dominated coordinate convergence in normed-fiber ℓ²

A fixed square-summable coordinate envelope upgrades coordinate convergence
along any filter to convergence in the full norm.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology

theorem tendsto_lpTwo_of_dominated {I A : Type*} {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] {l : Filter A}
    (v : A → lp E 2) (w b : lp E 2)
    (hv : ∀ a i, ‖v a i‖ ≤ ‖b i‖) (hw : ∀ i, ‖w i‖ ≤ ‖b i‖)
    (hc : ∀ i, Tendsto (fun a => v a i) l (𝓝 (w i))) : Tendsto v l (𝓝 w) := by
  have hs : Summable (fun i => ‖b i‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) b).summable
  have ht (i : I) : Tendsto (fun a => ‖v a i - w i‖ ^ 2) l (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      ((hc i).sub (tendsto_const_nhds (x := w i))).norm.pow 2
  have hb (a : A) (i : I) : ‖‖v a i - w i‖ ^ 2‖ ≤ 4 * ‖b i‖ ^ 2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := (norm_sub_le (v a i) (w i)).trans (add_le_add (hv a i) (hw i))
    nlinarith [norm_nonneg (v a i - w i), norm_nonneg (b i)]
  have htSum := tendsto_tsum_of_dominated_convergence (hs.mul_left 4) ht
    (Eventually.of_forall hb)
  have he (a : A) : ‖v a - w‖ ^ 2 = ∑' i, ‖v a i - w i‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, lp.coeFn_sub, Pi.sub_apply] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (v a - w)
  have hsq : Tendsto (fun a => ‖v a - w‖ ^ 2) l (𝓝 0) := by
    simpa only [he, tsum_zero] using htSum
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

end
end GaloisForLFunctions.HTGeometry
