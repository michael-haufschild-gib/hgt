import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.FiniteAperturePositivityCannotDecide
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional
import GaloisForLFunctions.SelectiveArithmetic.TheFirstSelectiveWindowOfZeta

/-!
# Certificates converge to the primes

The Riemann hypothesis holds exactly when every aperture admits *some* real weight system with
nonnegative Weil form: a certificate, which need not be arithmetic and may change with the
aperture. This module shows how much freedom the existence quantifier has in the limit: none.

* A weight system feasible at an aperture is bounded in each visible coordinate (the box law),
  and the Weil form of a test reads the weights through finitely many coordinates.
* Hence a coordinatewise limit of systems feasible at apertures tending to infinity, along any
  ultrafilter, is feasible on all tests; such a system is the von Mangoldt function
  (uniqueness of the Weil cone).
* `tendsto_weight_of_aperturePositive_seq`: any sequence of certificates at apertures tending to
  infinity converges to `Λ` in every coordinate.
* `exists_aperture_forall_abs_weight_sub_le`: uniformly, for every `n ≥ 2` and `ε > 0` there is
  an aperture beyond which every feasible system has `|λ(n) − Λ(n)| ≤ ε`. The feasible sets
  shrink to the arithmetic point in every coordinate, whether or not they stay nonempty.
-/

open Complex Filter Topology Set
open Zeta23

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open ArithmeticOfSquareRootPrecision SelectiveArithmetic
open _root_.RHTower

/-! ### Feasible systems -/

/-- Feasibility is inherited by smaller apertures. -/
theorem aperturePositive_mono {A A' : ℝ} {lam : ℕ → ℝ} (h : AperturePositive A' lam)
    (hA : A ≤ A') : AperturePositive A lam := fun f hf hfs =>
  h f hf (hfs.trans (Icc_subset_Icc (neg_le_neg hA) hA))

/-- A system feasible on complex tests is feasible on real packets. -/
theorem poleFeasible_of_aperturePositive {A : ℝ} {lam : ℕ → ℝ} (h : AperturePositive A lam) :
    PoleFeasible A lam := fun f hf hfs =>
  h (fun u => (f u : ℂ))
    (show ContDiff ℝ 2 (fun u => (f u : ℂ)) from Complex.ofRealCLM.contDiff.comp hf) hfs

/-- **The box law at one coordinate.** Beyond the aperture at which `n` becomes visible every
feasible system has `|λ(n)| ≤ B`, with `B` depending only on `n`. -/
theorem exists_bound_of_aperturePositive {n : ℕ} (hn : 2 ≤ n) :
    ∃ B A₁ : ℝ, ∀ {A : ℝ} {lam : ℕ → ℝ}, A₁ ≤ A → AperturePositive A lam → |lam n| ≤ B := by
  obtain ⟨C, hC⟩ := exists_abs_weight_le_of_poleFeasible
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine ⟨Real.sqrt n * (Real.log (1 + 1 / (1 / (4 * (n : ℝ)))) + C),
    Real.log n / 2 + 1 / (4 * (n : ℝ)), fun {A lam} hA hpos => ?_⟩
  exact hC hn (div_pos one_pos (mul_pos (by norm_num) hn0)) le_rfl hA
    (poleFeasible_of_aperturePositive hpos)

/-- The real part of the Weil functional of a compactly supported test reads the weights
through finitely many coordinates, affinely. -/
theorem exists_re_weilFullFunctional_eq_finite {k : ℝ → ℂ} (hk : HasCompactSupport k) :
    ∃ N : ℕ, ∀ lam : ℕ → ℝ, (weilFullFunctional lam k).re =
      (EF.literatureRHS k).re - ∑ n ∈ Finset.range N,
        (if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n else 0) *
          (k (Real.log n) + k (-Real.log n)).re := by
  obtain ⟨N, hN⟩ := exists_forall_log_eq_zero hk
  refine ⟨N, fun lam => ?_⟩
  have hfin : (∑' n : ℕ,
      ((if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) =
      ∑ n ∈ Finset.range N,
        ((if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n else 0 : ℝ) : ℂ) *
          (k (Real.log n) + k (-Real.log n)) :=
    tsum_eq_sum fun n hn => by
      rw [Finset.mem_range, not_lt] at hn
      rw [(hN n hn).1, (hN n hn).2, add_zero, mul_zero]
  rw [weilFullFunctional_eq_sub lam hk, hfin, Complex.sub_re, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.re_ofReal_mul]

/-! ### Limits of certificates -/

/-- **Certificates converge to the primes.** If `λ_k` is feasible at the aperture `A_k` and
`A_k → ∞`, then `λ_k(n) → Λ(n)` for every `n ≥ 2`. -/
theorem tendsto_weight_of_aperturePositive_seq {A : ℕ → ℝ} {lam : ℕ → ℕ → ℝ}
    (hA : Tendsto A atTop atTop) (hpos : ∀ k, AperturePositive (A k) (lam k)) {n : ℕ}
    (hn : 2 ≤ n) :
    Tendsto (fun k => lam k n) atTop (𝓝 (ArithmeticFunction.vonMangoldt n)) := by
  classical
  rw [tendsto_iff_ultrafilter]
  intro U hU
  -- along the ultrafilter every visible coordinate converges: the box law and compactness
  have hlim : ∀ m : ℕ, 2 ≤ m → ∃ x : ℝ, Tendsto (fun k => lam k m) U (𝓝 x) := by
    intro m hm
    obtain ⟨B, A₁, hB⟩ := exists_bound_of_aperturePositive hm
    have hlate : ∀ᶠ k in (U : Filter ℕ), A₁ ≤ A k := hU (hA.eventually_ge_atTop A₁)
    have hev : ∀ᶠ k in (U : Filter ℕ), lam k m ∈ Icc (-B) B :=
      hlate.mono fun k hk => abs_le.mp (hB hk (hpos k))
    have hle : ((U.map fun k => lam k m : Ultrafilter ℝ) : Filter ℝ) ≤ 𝓟 (Icc (-B) B) := by
      rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
      exact hev
    obtain ⟨x, -, hx⟩ := isCompact_Icc.ultrafilter_le_nhds _ hle
    rw [Ultrafilter.coe_map] at hx
    exact ⟨x, hx⟩
  choose! μ hμ using hlim
  -- the limit system is feasible on every test
  have hW : WeilPositiveFull μ := by
    intro f hf hfc
    obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
    obtain ⟨N, hN⟩ :=
      exists_re_weilFullFunctional_eq_finite (EF.weilTest_hasCompactSupport hfc hfc)
    have hev : ∀ᶠ k in (U : Filter ℕ),
        0 ≤ (weilFullFunctional (lam k) (EF.weilTest f f)).re := by
      have hlate : ∀ᶠ k in (U : Filter ℕ), R ≤ A k := hU (hA.eventually_ge_atTop R)
      refine hlate.mono fun k hk => hpos k f hf fun x hx => ?_
      have hx' := hR hx
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx'
      exact ⟨by linarith only [(abs_le.mp hx').1, hk], by linarith only [(abs_le.mp hx').2, hk]⟩
    have htend : Tendsto (fun k => (weilFullFunctional (lam k) (EF.weilTest f f)).re) U
        (𝓝 (weilFullFunctional μ (EF.weilTest f f)).re) := by
      simp only [hN]
      refine tendsto_const_nhds.sub (tendsto_finsetSum _ fun m _ => ?_)
      by_cases hm : 2 ≤ m
      · simp only [if_pos hm]
        exact (((hμ m hm).sub_const _).div_const _).mul_const _
      · simp only [if_neg hm]
        exact tendsto_const_nhds
    exact ge_of_tendsto htend hev
  -- the Weil cone has one point
  rw [← WeilSpectral.eq_vonMangoldt_of_weilPositiveFull hW n hn]
  exact hμ n hn

/-- **The feasible sets shrink to the arithmetic point.** For every `n ≥ 2` and `ε > 0` there
is an aperture beyond which every feasible weight system satisfies `|λ(n) − Λ(n)| ≤ ε`. -/
theorem exists_aperture_forall_abs_weight_sub_le {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → ∀ lam : ℕ → ℝ, AperturePositive A lam →
      |lam n - ArithmeticFunction.vonMangoldt n| ≤ ε := by
  by_contra hcon
  push Not at hcon
  choose A hA lam hlam hbig using fun k : ℕ => hcon (k : ℝ)
  have hAtop : Tendsto A atTop atTop := tendsto_atTop_mono hA tendsto_natCast_atTop_atTop
  have hlim := tendsto_weight_of_aperturePositive_seq hAtop hlam hn
  have hev := (tendsto_order.mp ((hlim.sub_const (ArithmeticFunction.vonMangoldt n)).abs)).2 ε
    (by simpa using hε)
  obtain ⟨k, hk⟩ := hev.exists
  exact absurd hk (not_lt.mpr (hbig k).le)

end GaloisForLFunctions.FloorFreeArithmetic
