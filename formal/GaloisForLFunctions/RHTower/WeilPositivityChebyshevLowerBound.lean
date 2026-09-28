import GaloisForLFunctions.RHTower.WeilPositivitySparseWeightsObstruction

/-!
# Weil positivity produces a Chebyshev lower bound

Let `R` be the autocorrelation of the Fejér test `ψ` (supported in `|y| < 17/25`) and
`S(Y) = ∑_n lam(n) n^{-1/2} R(log n − Y)` the smoothed atom sum of the weights `lam` at `e^Y`.

* **Chebyshev lower bound** (`weilPositive_smoothedMean_lower`).  If `lam` is Weil-positive and
  `e^{-Y/2} S(Y) → L`, then `4π L ≥ −∫ |ψ̂|² A > 0`.  The far-polar inequality at scale `X` reads
  `η − o(1) ≤ 4π(c_X S(X) − (c_X²/4) S(2X))` with `c_X e^{X/2} → 2`; its right side tends to
  `4π(2L − L)`.
* **Zero mean density** (`not_weilPositive_of_smoothedMean_zero`).  If `e^{-Y/2} S(Y) → 0`, the
  weights are not Weil-positive.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

local notation "Rf" => flatBumpCorr (17 / 50) (17 / 1000)

/-- The smoothed atom mean `S(Y) = ∑_n lam(n) n^{-1/2} R(log n − Y)` of `lam` at the scale `e^Y`,
with `R` the autocorrelation of the Fejér test (supported in `|y| < 17/25`). -/
def smoothedAtomSum (lam : ℕ → ℝ) (Y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (Y + 17 / 25)⌋₊, lam n / Real.sqrt n * Rf (Real.log n - Y)

/-- Any cutoff past `e^{Y+1}` gives the same smoothed sum. -/
theorem sum_Icc_eq_smoothedAtomSum (lam : ℕ → ℝ) {Y : ℝ} {N : ℕ}
    (hN : ⌊Real.exp (Y + 17 / 25)⌋₊ ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * Rf (Real.log n - Y) = smoothedAtomSum lam Y := by
  unfold smoothedAtomSum
  symm
  refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN) fun n hn hnot => ?_
  rw [Finset.mem_Icc] at hn hnot
  have hbig : ⌊Real.exp (Y + 17 / 25)⌋₊ < n := by
    by_contra h; push Not at h; exact hnot ⟨hn.1, h⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hexp : Real.exp (Y + 17 / 25) < n := (Nat.floor_lt (Real.exp_pos _).le).mp hbig
  have hlog : Y + 17 / 25 < Real.log n := by
    rw [← Real.log_exp (Y + 17 / 25)]; exact Real.log_lt_log (Real.exp_pos _) hexp
  rw [fejerCorr_eq_zero (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]

/-- **Weil positivity produces a Chebyshev lower bound.**  If `lam` is Weil-positive and its
smoothed atom means `e^{-Y/2} S(Y)` converge to `L`, then `4π L ≥ −∫|ψ̂|² A > 0`: every positive
completion of `ζ`'s archimedean datum has a positive mean density of prime atoms, of the size forced
by the pole.  (For `Λ` the prime number theorem gives `L = (∫ ψ(x) e^{x/2} dx)²`, and the bound is
the small-support Weil positivity of `ψ` with its pole term.) -/
theorem weilPositive_smoothedMean_lower {lam : ℕ → ℝ} (hW : WeilPositive lam) {L : ℝ}
    (hL : Tendsto (fun Y => Real.exp (-(Y / 2)) * smoothedAtomSum lam Y) atTop (𝓝 L)) :
    -(∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))) ≤ 4 * π * L := by
  set η := -(∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))) with hη
  set I := fejerArchAbsEnergy
  -- rewrite the far-polar inequality in terms of the smoothed means
  have hineq : ∀ X : ℝ, 0 ≤ X → η - (2 * farPolarCoeff X + farPolarCoeff X ^ 2) * I ≤
      4 * π * (farPolarCoeff X * smoothedAtomSum lam X -
        farPolarCoeff X ^ 2 / 4 * smoothedAtomSum lam (2 * X)) := by
    intro X hX
    have h := weilPositive_farPolar_inequality hW hX
    set N := ⌊Real.exp (2 * (X + 17 / 50))⌋₊
    have hN1 : ⌊Real.exp (X + 17 / 25)⌋₊ ≤ N :=
      Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
    have hN2 : ⌊Real.exp (2 * X + 17 / 25)⌋₊ ≤ N :=
      Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
    have hsplit : ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        (farPolarCoeff X * Rf (Real.log n - X) - farPolarCoeff X ^ 2 / 4 * Rf (Real.log n - 2 * X)) =
        farPolarCoeff X * (∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * Rf (Real.log n - X)) -
          farPolarCoeff X ^ 2 / 4 *
            (∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * Rf (Real.log n - 2 * X)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hsplit, sum_Icc_eq_smoothedAtomSum lam hN1, sum_Icc_eq_smoothedAtomSum lam hN2] at h
    exact h
  -- the limits of the two scaled means
  have hc : Tendsto (fun X => farPolarCoeff X * Real.exp (X / 2)) atTop (𝓝 2) := by
    have e : ∀ X : ℝ, farPolarCoeff X * Real.exp (X / 2) = 2 / (1 + Real.exp (-X)) := by
      intro X
      unfold farPolarCoeff
      rw [Real.cosh_eq]
      have h1 : Real.exp (X / 2) * Real.exp (-(X / 2)) = 1 := by rw [← Real.exp_add]; simp
      have h2 : Real.exp (-X) = Real.exp (-(X / 2)) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [h2]
      field_simp
      nlinarith [Real.exp_pos (X / 2), Real.exp_pos (-(X / 2))]
    simp_rw [e]
    have := ((Real.tendsto_exp_neg_atTop_nhds_zero.const_add 1).inv₀ (by norm_num)).const_mul 2
    simpa [div_eq_mul_inv] using this
  have hL2 : Tendsto (fun X => Real.exp (-X) * smoothedAtomSum lam (2 * X)) atTop (𝓝 L) := by
    have := hL.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    refine this.congr fun X => ?_
    simp only [Function.comp_apply, id]
    congr 2; ring
  have hfirst : Tendsto (fun X => farPolarCoeff X * smoothedAtomSum lam X) atTop (𝓝 (2 * L)) := by
    have := hc.mul hL
    refine this.congr fun X => ?_
    have : Real.exp (X / 2) * Real.exp (-(X / 2)) = 1 := by rw [← Real.exp_add]; simp
    calc farPolarCoeff X * Real.exp (X / 2) * (Real.exp (-(X / 2)) * smoothedAtomSum lam X)
        = farPolarCoeff X * smoothedAtomSum lam X * (Real.exp (X / 2) * Real.exp (-(X / 2))) := by
          ring
      _ = farPolarCoeff X * smoothedAtomSum lam X := by rw [this, mul_one]
  have hsecond : Tendsto (fun X => farPolarCoeff X ^ 2 / 4 * smoothedAtomSum lam (2 * X)) atTop
      (𝓝 L) := by
    have := ((hc.pow 2).div_const 4).mul hL2
    have e : (2 : ℝ) ^ 2 / 4 * L = L := by ring
    rw [e] at this
    refine this.congr fun X => ?_
    have h1 : Real.exp (X / 2) ^ 2 * Real.exp (-X) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf; simp
    calc (farPolarCoeff X * Real.exp (X / 2)) ^ 2 / 4 * (Real.exp (-X) * smoothedAtomSum lam (2 * X))
        = farPolarCoeff X ^ 2 / 4 * smoothedAtomSum lam (2 * X) *
            (Real.exp (X / 2) ^ 2 * Real.exp (-X)) := by ring
      _ = _ := by rw [h1, mul_one]
  have hleft : Tendsto (fun X => η - (2 * farPolarCoeff X + farPolarCoeff X ^ 2) * I) atTop
      (𝓝 (η - (2 * 0 + 0 ^ 2) * I)) :=
    tendsto_const_nhds.sub (((tendsto_farPolarCoeff.const_mul 2).add
      (tendsto_farPolarCoeff.pow 2)).mul_const I)
  have hright : Tendsto (fun X => 4 * π * (farPolarCoeff X * smoothedAtomSum lam X -
      farPolarCoeff X ^ 2 / 4 * smoothedAtomSum lam (2 * X))) atTop (𝓝 (4 * π * (2 * L - L))) :=
    (hfirst.sub hsecond).const_mul _
  have hlim := le_of_tendsto_of_tendsto hleft hright
    ((eventually_ge_atTop (0 : ℝ)).mono fun X hX => hineq X hX)
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, zero_mul, sub_zero] at hlim
  linarith

/-- **Zero mean density is never Weil-positive.**  A weight system whose smoothed atom means are
`o(e^{Y/2})` (for instance the von Mangoldt weights twisted by a non-principal character, or any
system with mean zero) is not Weil-positive. -/
theorem not_weilPositive_of_smoothedMean_zero {lam : ℕ → ℝ}
    (h0 : Tendsto (fun Y => Real.exp (-(Y / 2)) * smoothedAtomSum lam Y) atTop (𝓝 0)) :
    ¬ WeilPositive lam := by
  intro hW
  have h := weilPositive_smoothedMean_lower hW h0
  have hneg := integral_normSq_paperFT_fejerTest_mul_arch_neg
  linarith

end RHTower
