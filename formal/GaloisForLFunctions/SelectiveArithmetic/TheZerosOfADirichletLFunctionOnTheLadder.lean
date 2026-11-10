import GaloisForLFunctions.SelectiveArithmetic.AnIsolatedPairShowsAtTheRungOfItsDepth
import GaloisForLFunctions.SelectiveArithmetic.TheMassOfAConductorPaysEveryDominatedContact
import GaloisForLFunctions.RHTower.DirichletLUniformRvM

/-!
# The zeros of a Dirichlet `L`-function on the ladder of its conductor

For a primitive character `χ` of conductor `q` the zeros of `L(s, χ)` have the local count
`N(t, t+1] ≤ A (log q + 1) log(|t| + 3)` with an absolute constant `A` (corpus). The mass at a
zero `ρ₀ = ½ + δ + iγ₀` is `m = A (log q + 1) log(|γ₀| + 3)`, and `log m = log log q + O(1)` at a
bounded height.

* **Below the rung one** the sum over the zeros is positive on every packet, with a margin
  (`exists_trivialAperture_margin`).
* **Above the rung of a depth** (`dirichlet_companion_of_rung`): if `2δκ > 1` and `log m` is
  large, nonnegativity of the form of the zeros on the tests supported in
  `[−κ log m, κ log m]` forces a second off-line zero of `L(s, χ)` within the ordinate distance
  `m^κ` of every zero of depth `δ`.

So an exceptional zero `β = ½ + δ` whose neighbours up to the height `m^κ` lie on the line is one
negative square of the twisted part at the aperture `κ log m`, for every `κ > 1/(2δ)`; as
`β → 1` the rung tends to one, the trivial aperture.
-/

open Filter Topology Set
open Zeta23

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

/-- The conductor-uniform local count of the zeros of `L(s, χ)`, as a count of the
configuration: `N(t, t+1] ≤ A (log q + 1) log(|t| + 3)`. -/
theorem dirichletZeros_local_count {q : ℕ} [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (t : ℝ) :
    ((_root_.RHTower.dirichletZeros hq hprim).N t (t + 1) : ℝ) ≤
      2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) * (Real.log q + 1) *
        Real.log (|t| + 3) := by
  have hN := Zeta23.ThmE.LZeros_N (Zeta23.ThmE.LSeam_of hq hprim) t (t + 1)
  have h := _root_.RHTower.localCountChi_uniform' hq hprim t
  rw [← hN] at h
  have hA := _root_.RHTower.one_le_uniformLocalCountConst
  have hlog3 : 1 ≤ Real.log (|t| + 3) := _root_.RHTower.one_le_log_abs_add_three t
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have h2 : Real.log q + Real.log (|t| + 3) ≤ (Real.log q + 1) * Real.log (|t| + 3) := by
    nlinarith
  calc ((_root_.RHTower.dirichletZeros hq hprim).N t (t + 1) : ℝ)
      ≤ 2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) *
          (Real.log q + Real.log (|t| + 3)) := h
    _ ≤ 2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) *
          ((Real.log q + 1) * Real.log (|t| + 3)) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = 2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) * (Real.log q + 1) *
          Real.log (|t| + 3) := by ring

/-- **A zero of `L(s, χ)` shows at the rung of its depth.** Let `2δκ > 1`. There are `A₀ ≥ 1`
and `M₀` such that for every primitive character `χ` of conductor `q > 1` and every zero
`ρ₀ = ½ + δ + iγ₀` of `L(s, χ)` with `log m ≥ M₀`, `m = A₀ (log q + 1) log(|γ₀| + 3)`: if the form
of the zeros is nonnegative on the tests supported in `[−κ log m, κ log m]`, then another
off-line zero, different from `1 − ρ̄₀`, lies within the ordinate distance `m^κ` of `ρ₀`. -/
theorem dirichlet_companion_of_rung {δ κ : ℝ} (hδ : 0 < δ) (hκ : 1 < 2 * δ * κ) :
    ∃ A₀ M₀ : ℝ, 1 ≤ A₀ ∧ ∀ {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
      (hprim : χ.IsPrimitive), ∀ ρ₀ ∈ (_root_.RHTower.dirichletZeros hq hprim).carrier,
      ρ₀.re = 1 / 2 + δ →
      M₀ ≤ Real.log (A₀ * (Real.log q + 1) * Real.log (|ρ₀.im| + 3)) →
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
        tsupport f ⊆ Icc (-(κ * Real.log (A₀ * (Real.log q + 1) * Real.log (|ρ₀.im| + 3))))
          (κ * Real.log (A₀ * (Real.log q + 1) * Real.log (|ρ₀.im| + 3))) →
        0 ≤ ((_root_.RHTower.dirichletZeros hq hprim).W f f).re) →
      ∃ ρ ∈ (_root_.RHTower.dirichletZeros hq hprim).carrier, ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ ∧
        |ρ.im - ρ₀.im| ≤
          Real.exp (κ * Real.log (A₀ * (Real.log q + 1) * Real.log (|ρ₀.im| + 3))) ∧
        ρ.re ≠ 1 / 2 := by
  obtain ⟨M₀, hM₀⟩ := exists_companion_of_rung hδ hκ
  have hA := _root_.RHTower.one_le_uniformLocalCountConst
  refine ⟨2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84), M₀, hA,
    fun {q} _ hq χ hprim ρ₀ hρ₀ hre hM hpos => ?_⟩
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hA1 : 1 ≤ 2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) * (Real.log q + 1) := by
    nlinarith
  exact hM₀ (_root_.RHTower.dirichletZeros hq hprim) hA1
    (fun t => dirichletZeros_local_count hq hprim t) hρ₀ hre hM hpos

end GaloisForLFunctions.SelectiveArithmetic
