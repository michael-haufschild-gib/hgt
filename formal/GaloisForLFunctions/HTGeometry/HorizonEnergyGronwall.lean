import GaloisForLFunctions.HTGeometry.GronwallBackward

/-! A negative-ray energy bound with an integrable backward loss. -/
namespace GaloisForLFunctions.HTGeometry
open Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Integrable backward loss and bounded forward growth control the entire negative ray
from one interior datum, without supplying an endpoint limit. -/
theorem horizon_energy_bound {F dF : ℝ → ℝ} {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hF : ∀ t < 0, 0 ≤ F t) (hd : ∀ t < 0, HasDerivAt F (dF t) t)
    (hlo : ∀ t < 0, -C*Real.exp (2*t)*(F t+1) ≤ dF t)
    (hhi : ∀ t < 0, dF t ≤ K*(F t+1)) :
    ∀ t < 0, F t+1 ≤ max ((F (-1)+1)*Real.exp (C/2)) ((F (-1)+1)*Real.exp K) := by
  let G : ℝ → ℝ := fun t => (F t+1)*Real.exp (C/2*Real.exp (2*t))
  have hG (t : ℝ) (ht : t < 0) : HasDerivAt G
      ((dF t+C*Real.exp (2*t)*(F t+1))*Real.exp (C/2*Real.exp (2*t))) t := by
    have he := (((((hasDerivAt_id t).const_mul 2).exp).const_mul (C/2)).exp)
    convert! ((hd t ht).add_const 1).mul he using 1
    dsimp
    ring
  have hm : MonotoneOn G (Iio 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iio 0)
      (fun t ht => (hG t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hG t (by simpa using ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hG t (by simpa using ht)).deriv]
    exact mul_nonneg (by linarith [hlo t (by simpa using ht)]) (Real.exp_pos _).le
  let H : ℝ → ℝ := fun t => (F t+1)*Real.exp (-K*t)
  have hH (t : ℝ) (ht : t < 0) : HasDerivAt H
      ((dF t-K*(F t+1))*Real.exp (-K*t)) t := by
    convert! ((hd t ht).add_const 1).mul (((hasDerivAt_id t).const_mul (-K)).exp) using 1
    dsimp
    ring
  have ha : AntitoneOn H (Iio 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iio 0)
      (fun t ht => (hH t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hH t (by simpa using ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hH t (by simpa using ht)).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hhi t (by simpa using ht)]) (Real.exp_pos _).le
  have hF1 : 0 ≤ F (-1)+1 := by linarith [hF (-1) (by norm_num)]
  intro t ht
  have htF : 0 ≤ F t+1 := by linarith [hF t ht]
  by_cases ht1 : t ≤ -1
  · have hl : F t+1 ≤ G t := le_mul_of_one_le_right htF
      (Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) (Real.exp_pos _).le))
    have he : G (-1) ≤ (F (-1)+1)*Real.exp (C/2) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hF1
      exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by norm_num))
    exact (hl.trans ((hm ht (by norm_num) ht1).trans he)).trans (le_max_left _ _)
  · have hl : F t+1 ≤ H t := le_mul_of_one_le_right htF
      (Real.one_le_exp_iff.mpr (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hK) ht.le))
    have he : H t ≤ (F (-1)+1)*Real.exp K := by
      simpa [H] using ha (show (-1:ℝ) ∈ Iio 0 by norm_num) ht (le_of_not_ge ht1)
    exact (hl.trans he).trans (le_max_right _ _)

end
end GaloisForLFunctions.HTGeometry
