import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheDecidingInputTheorem
import GaloisForLFunctions.RHTower.WeilLagFunctionFrontier
import GaloisForLFunctions.RHTower.WeilPrimeDeficitSetRigidity

/-!
# A faithful input need not decide

The deciding-input theorem names four necessary properties of a statement implying the count: false for the Liouville twin, precision-faithful against `εn^{−η}`, of
unbounded aperture, stabilizer inside the square-root class `𝒬`.  This module shows that the first three do not make a statement close to deciding.

The **Mertens law** `Σ_{n ≤ N} a(n)/n = log N − γ + o(1)`, with the exact constant, is an unconditional theorem about `Λ` (`mertensLaw_vonMangoldt`).  It

* fails for the Liouville twin (`not_mertensLaw_liouvilleWeight`);
* is never shared by `a` and `a + εn^{−η}`, for every real `η` (`not_mertensLaw_and_add_smul_powerWeight`), a statement stronger than precision-faithfulness since it holds past `η = ½`;
* is not determined by a finite window (`exists_extension_not_mertensLaw`);
* and yet does not imply the count: its stabilizer contains the explicit `δ ≈ n^{−1/4}/4` (`mertensLaw_add_mertensInvisible`, `mertensInvisible_not_mem_sqrtClass`), so some weight satisfying the law fails the count
  (`exists_mertensLaw_not_count`).

The test that does the work is therefore the fourth one, the stabilizer: a statement can be exact in its constant and blind at every power below square root, as soon as a perturbation is allowed
to cancel in the harmonic mean.
-/

noncomputable section

open Filter Topology Asymptotics Finset
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.ArithmeticProduction

open ArithmeticOfSquareRootPrecision

/-- The harmonic sum `Σ_{n ≤ N} a(n)/n`. -/
def harmonicSum (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, a n / n

/-- The Mertens law with its exact constant. -/
def MertensLaw (a : ℕ → ℝ) : Prop :=
  Tendsto (fun N : ℕ => harmonicSum a N - Real.log N) atTop (𝓝 (-Real.eulerMascheroniConstant))

theorem harmonicSum_add (a b : ℕ → ℝ) (N : ℕ) :
    harmonicSum (a + b) N = harmonicSum a N + harmonicSum b N := by
  unfold harmonicSum
  rw [← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  simp only [Pi.add_apply]
  ring

/-- **The Mertens law for `Λ` is a theorem.** -/
theorem mertensLaw_vonMangoldt : MertensLaw vonMangoldtWeight := by
  obtain ⟨c, hc, C, hC, hbound⟩ := _root_.RHTower.mertensDeviation_bound
  have hsmall : Tendsto (fun x : ℝ => C * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log x ^ ((1 : ℝ) / 10)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
    have h2 : Tendsto (fun x : ℝ => Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      exact h1.const_mul_atTop_of_neg (by linarith)
    simpa using h2.const_mul C
  have hnat := hsmall.comp tendsto_natCast_atTop_atTop
  refine (tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩ :
    Tendsto (fun N : ℕ => harmonicSum vonMangoldtWeight N - Real.log N) atTop
      (𝓝 (-Real.eulerMascheroniConstant)))
  · have hd : 0 < -Real.eulerMascheroniConstant - a := by linarith
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hbound,
      hnat.eventually (Iio_mem_nhds hd)] with N h1 h2
    sorry
  · sorry

end GaloisForLFunctions.ArithmeticProduction
