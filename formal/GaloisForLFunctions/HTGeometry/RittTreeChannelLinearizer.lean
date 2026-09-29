import GaloisForLFunctions.HTGeometry.RittMeromorphicGermFrame
import GaloisForLFunctions.HTGeometry.RittTreeChannelInterior
import GaloisForLFunctions.HTGeometry.RittTreeChannelDegree

/-!
# Linearizers of an interior tree channel are hypertranscendental

The tree channel map `R(y) = ((1+uy)^p − (1+vy)^p)/((1+uy)^p + (1+vy)^p)` fixes `0` with multiplier
`p(u − v)/2`.  For an interior channel `−1 < v < u < 1` this multiplier is a positive real, so it is
not a root of unity unless it equals one.  Away from that parabolic value, Ritt's implication at the
fixed point turns a differentially algebraic linearizer into a rational cocycle of `R`, and an
interior channel has none: every local linearizer `κ(R(y)) = q·κ(y)` with `κ'(0) ≠ 0` satisfies no
algebraic differential equation on any neighbourhood of `0`.
-/

open Filter Topology Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {p : ℕ} {u v : ℂ}

theorem treeDen_eval_zero : (treeDen p u v).eval 0 = 2 := by
  simp [treeDen]
  norm_num

theorem treeNum_eval_zero : (treeNum p u v).eval 0 = 0 := by
  simp [treeNum]

theorem derivative_treeNum_eval_zero :
    (derivative (treeNum p u v)).eval 0 = (p : ℂ) * (u - v) := by
  simp [treeNum, derivative_pow]
  ring

theorem treeDen_ne_zero : treeDen p u v ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  rw [treeDen_eval_zero, eval_zero] at this
  norm_num at this

/-- The map is a quotient of its polynomial numerator and denominator near `0`. -/
theorem ratValue_treeRG_eventually :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      ratValue (treeRG p u v) z = (treeNum p u v).eval z / (treeDen p u v).eval z := by
  have hcont : ContinuousAt (fun z => (treeDen p u v).eval z) 0 :=
    (treeDen p u v).continuous.continuousAt
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), (treeDen p u v).eval z ≠ 0 :=
    hcont.eventually_ne (by rw [treeDen_eval_zero]; norm_num)
  filter_upwards [hne] with z hz
  rw [treeRG, ratValue_div_algebraMap hz]

theorem treeRG_regular_zero : 0 ≤ ratOrder (treeRG p u v) 0 := by
  have hden : ¬ (treeDen p u v).IsRoot 0 := by
    rw [IsRoot, treeDen_eval_zero]; norm_num
  have hB : algebraMap ℂ[X] (RatFunc ℂ) (treeDen p u v) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr treeDen_ne_zero
  rw [treeRG]
  rcases eq_or_ne (treeNum p u v) 0 with h | h
  · rw [h, map_zero, zero_div, ratOrder_zero]
  have hA : algebraMap ℂ[X] (RatFunc ℂ) (treeNum p u v) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr h
  rw [div_eq_mul_inv, ratOrder_mul hA (inv_ne_zero hB), ratOrder_inv hB, ratOrder_algebraMap,
    ratOrder_algebraMap, rootMultiplicity_eq_zero hden]
  simp

theorem treeRG_value_zero : ratValue (treeRG p u v) 0 = 0 := by
  rw [treeRG, ratValue_div_algebraMap (by rw [treeDen_eval_zero]; norm_num), treeNum_eval_zero,
    zero_div]

/-- **The multiplier of the tree channel map at `0` is `p(u − v)/2`.** -/
theorem treeRG_multiplier :
    ratValue (ratFuncDeriv (treeRG p u v)) 0 = (p : ℂ) * (u - v) / 2 := by
  rw [← deriv_ratValue_zero treeRG_regular_zero,
    Filter.EventuallyEq.deriv_eq ratValue_treeRG_eventually]
  have h := ((treeNum p u v).hasDerivAt 0).div ((treeDen p u v).hasDerivAt 0)
    (by rw [treeDen_eval_zero]; norm_num)
  rw [show (fun z => (treeNum p u v).eval z / (treeDen p u v).eval z)
      = (fun z => (treeNum p u v).eval z) / (fun z => (treeDen p u v).eval z) from rfl, h.deriv,
    treeNum_eval_zero, treeDen_eval_zero, derivative_treeNum_eval_zero]
  ring

/-- **An interior, non-parabolic tree channel map has a linearizable fixed point at `0`.** -/
theorem isLinearizableFixedPoint_treeRG_interior (hp : 2 ≤ p) {u v : ℝ} (huv : v < u)
    (hpar : (p : ℝ) * (u - v) / 2 ≠ 1) :
    IsLinearizableFixedPoint (treeRG p (u : ℂ) (v : ℂ)) := by
  have hmult : ratValue (ratFuncDeriv (treeRG p (u : ℂ) (v : ℂ))) 0
      = (((p : ℝ) * (u - v) / 2 : ℝ) : ℂ) := by
    rw [treeRG_multiplier]
    push_cast
    ring
  have hpos : 0 < (p : ℝ) * (u - v) / 2 := by
    have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have : 0 < u - v := by linarith
    positivity
  refine ⟨treeRG_regular_zero, treeRG_value_zero, ?_, ?_⟩
  · rw [hmult]
    exact_mod_cast hpos.ne'
  · intro n hn h
    rw [hmult] at h
    have h' : ((p : ℝ) * (u - v) / 2) ^ n = 1 := by exact_mod_cast h
    exact hpar ((pow_eq_one_iff_of_nonneg hpos.le (by omega)).mp h')

theorem treeRG_not_const (hp : 2 ≤ p) {u v : ℝ} (huv : v < u) :
    ¬ ∃ c : ℂ, treeRG p (u : ℂ) (v : ℂ) = RatFunc.C c := by
  rintro ⟨c, hc⟩
  have hdeg := ratFuncDegree_treeRG (K := ℂ) (p := p) (by omega)
    (u := (u : ℂ)) (v := (v : ℂ)) (by exact_mod_cast huv.ne')
  rw [hc, ratFuncDegree] at hdeg
  simp at hdeg
  omega

/-- **Linearizers of an interior tree channel are hypertranscendental.**  For `−1 < v < u < 1`,
`p ≥ 2` and multiplier `p(u − v)/2 ≠ 1`, no analytic germ `κ` with `κ'(0) ≠ 0` and
`κ(R(y)) = q·κ(y)` near `0` satisfies an algebraic differential equation on a neighbourhood of `0`.
-/
theorem not_differentiallyAlgebraicOn_linearizer_treeRG_interior (hp : 2 ≤ p) {u v : ℝ}
    (hv : -1 < v) (huv : v < u) (hu : u < 1) (hpar : (p : ℝ) * (u - v) / 2 ≠ 1)
    {κ : ℂ → ℂ} (hκ : AnalyticAt ℂ κ 0) (hκ' : deriv κ 0 ≠ 0) {q : ℂ} (hq : q ≠ 0)
    (hfe : ∀ᶠ y in 𝓝 (0 : ℂ), κ (((1 + u * y) ^ p - (1 + v * y) ^ p)
      / ((1 + u * y) ^ p + (1 + v * y) ^ p)) = q * κ y)
    {U : Set ℂ} (hU : U ∈ 𝓝 (0 : ℂ)) : ¬ DifferentiallyAlgebraicOn κ U := by
  intro hDA
  have hR := treeRG_not_const hp huv
  have hd : 2 ≤ ratFuncDegree (treeRG p (u : ℂ) (v : ℂ)) := by
    rw [ratFuncDegree_treeRG (by omega) (by exact_mod_cast huv.ne')]
    exact hp
  have hfe' : ∀ᶠ y in 𝓝 (0 : ℂ),
      κ (ratValue (treeRG p (u : ℂ) (v : ℂ)) y) = q * κ y := by
    filter_upwards [hfe, ratValue_treeRG_eventually] with y hy hval
    rw [hval]
    simpa [treeNum, treeDen] using hy
  obtain ⟨N, hN, β, hβ, A, hA, htr⟩ :=
    ratTransport_of_differentiallyAlgebraicOn_linearizer hR hd
      (isLinearizableFixedPoint_treeRG_interior hp huv hpar) hκ hκ' hq hfe' hU hDA
  exact treeRG_no_cocycle_interior hp hv huv hu (by exact_mod_cast hN.ne') hβ hA htr

end

end GaloisForLFunctions.HTGeometry
