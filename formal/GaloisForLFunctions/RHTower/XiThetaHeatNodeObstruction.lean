import GaloisForLFunctions.RHTower.XiThetaHeatReparametrization
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The infinite theta reader is forced to be singular at the compactified heat boundary

Compactify the square heat rate by the node x_m = exp(-pi m squared). These positive nodes converge
to zero. A moment reader holomorphic on a connected compactified domain containing zero and all
nodes would be represented by a symbol whose values at x_m are Kronecker delta data.

The isolated-zero principle makes this impossible in that category: zeros at every sufficiently
large node accumulate at zero, forcing local vanishing and then vanishing across the connected
domain. Therefore an exact compactified moment-symbol reader must be singular or nonanalytic at
x = 0. Finite polynomial interpolants can exist, but no holomorphic connected-domain limit can
retain the delta normalization.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped ENNReal Topology FourierTransform

noncomputable section

namespace RHTower

/-- The compactified square heat node. -/
def thetaHeatNode (m : ℕ) : ℝ :=
  Real.exp (-π * (m : ℝ) ^ 2)

theorem thetaHeatNode_pos (m : ℕ) : 0 < thetaHeatNode m :=
  Real.exp_pos _

/-- The compactified square spectrum accumulates at the heat boundary zero. -/
theorem thetaHeatNode_tendsto_zero :
    Tendsto thetaHeatNode atTop (𝓝 0) := by
  have hsq : Tendsto (fun m : ℕ => (m : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hneg : Tendsto (fun m : ℕ => -π * (m : ℝ) ^ 2) atTop atBot := by
    have h := hsq.atTop_mul_const_of_neg (neg_lt_zero.mpr Real.pi_pos)
    simpa [mul_comm] using h
  exact Real.tendsto_exp_atBot.comp hneg

theorem thetaHeatNode_complex_tendsto_zero :
    Tendsto (fun m : ℕ => (thetaHeatNode m : ℂ)) atTop (𝓝 0) := by
  exact (Complex.continuous_ofReal.tendsto 0).comp thetaHeatNode_tendsto_zero

theorem thetaHeatNode_complex_tendsto_punctured_zero :
    Tendsto (fun m : ℕ => (thetaHeatNode m : ℂ)) atTop (𝓝[≠] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨thetaHeatNode_complex_tendsto_zero, ?_⟩
  exact Eventually.of_forall fun m =>
    Complex.ofReal_ne_zero.mpr (thetaHeatNode_pos m).ne'

/-- A compactified moment symbol holomorphic on a connected domain containing zero and every
square heat node cannot vanish on every node except one without vanishing at that node too. -/
theorem no_analyticOnNhd_thetaHeatNode_reader
    (F : ℂ → ℂ) {U : Set ℂ} (hU : IsPreconnected U)
    (hF : AnalyticOnNhd ℂ F U) (h0 : 0 ∈ U)
    (hnodes : ∀ m : ℕ, 1 ≤ m → (thetaHeatNode m : ℂ) ∈ U)
    {n : ℕ} (hn : 1 ≤ n)
    (hzero : ∀ m : ℕ, 1 ≤ m → m ≠ n → F (thetaHeatNode m) = 0) :
    F (thetaHeatNode n) = 0 := by
  rcases (hF 0 h0).eventually_eq_zero_or_eventually_ne_zero with hlocal | hne
  · have hEq : EqOn F 0 U :=
      hF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU h0 hlocal
    exact hEq (hnodes n hn)
  · have hevent : ∀ᶠ m : ℕ in atTop, F (thetaHeatNode m) ≠ 0 :=
      thetaHeatNode_complex_tendsto_punctured_zero.eventually hne
    exfalso
    rcases (eventually_atTop.1 hevent) with ⟨M, hM⟩
    let m := max M (n + 1)
    have hmM : M ≤ m := le_max_left _ _
    have hmn : n < m := by simp [m]
    have hm1 : 1 ≤ m := by omega
    exact hM m hmM (hzero m hm1 (Nat.ne_of_gt hmn))

/-- An entire moment symbol vanishing on every square heat node except possibly one also vanishes
at that node. -/
theorem no_entire_thetaHeatNode_reader
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) {n : ℕ} (hn : 1 ≤ n)
    (hzero : ∀ m : ℕ, 1 ≤ m → m ≠ n → F (thetaHeatNode m) = 0) :
    F (thetaHeatNode n) = 0 := by
  have hFan : AnalyticOnNhd ℂ F univ :=
    hF.differentiableOn.analyticOnNhd isOpen_univ
  exact no_analyticOnNhd_thetaHeatNode_reader F isPreconnected_univ hFan
    (mem_univ 0) (fun _ _ => mem_univ _) hn hzero

/-- No symbol holomorphic on a connected compactified domain containing zero and every square heat
node can realize the infinite Kronecker-delta interpolation data. -/
theorem no_analyticOnNhd_thetaHeatNode_delta
    (F : ℂ → ℂ) {U : Set ℂ} (hU : IsPreconnected U)
    (hF : AnalyticOnNhd ℂ F U) (h0 : 0 ∈ U)
    (hnodes : ∀ m : ℕ, 1 ≤ m → (thetaHeatNode m : ℂ) ∈ U)
    {n : ℕ} (hn : 1 ≤ n) (hself : F (thetaHeatNode n) = 1)
    (hother : ∀ m : ℕ, 1 ≤ m → m ≠ n → F (thetaHeatNode m) = 0) :
    False := by
  have hz := no_analyticOnNhd_thetaHeatNode_reader F hU hF h0 hnodes hn hother
  rw [hself] at hz
  exact one_ne_zero hz

/-- No entire symbol can interpolate one at a selected square heat node and zero at all the
others. The infinite reader is forced out of the analytic moment-symbol category. -/
theorem no_entire_thetaHeatNode_delta
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) {n : ℕ} (hn : 1 ≤ n)
    (hself : F (thetaHeatNode n) = 1)
    (hother : ∀ m : ℕ, 1 ≤ m → m ≠ n → F (thetaHeatNode m) = 0) :
    False := by
  have hz := no_entire_thetaHeatNode_reader F hF hn hother
  rw [hself] at hz
  exact one_ne_zero hz

end RHTower
