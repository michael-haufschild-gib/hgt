import GaloisForLFunctions.RHTower.LandauRelativeRigidity
import GaloisForLFunctions.HTGeometry.BallLogarithm

/-!
# Systems that only add primes vanish at their real abscissa

A system of generalized primes that only adds primes to another one multiplies the zeta
function by an Euler factor `E = exp D`, where `D(s) = Σ a_j e^{−λ_j s}` has nonnegative
coefficients. Let `σ_c` be the real abscissa of `D`. By Landau's theorem `D` has no holomorphic
continuation to a neighbourhood of `σ_c` (`RHTower.gdSeries_no_continuation_at_abscissa`). For
the factor itself this means:

* `exists_zero_of_eulerFactor_differentiableOn`: if `E` extends holomorphically to a disc
  around `σ_c`, it has a zero in that disc. Otherwise `E` would have a holomorphic logarithm on
  the disc, which differs from `D` by a constant on the right half and continues `D`.
* `eulerFactor_abscissa_eq_zero`: hence `E(σ_c) = 0`.

A new zero of the perturbed zeta function lies at or left of `σ_c`
(`RHTower.re_le_abscissa_of_eulerFactor_zero`). So a system that only adds primes pays for a
zero at `ρ` with a singularity or a zero of its Euler factor on the real axis at or beyond
`Re ρ`: a model with a finite non-real layer and a factor that is regular and free of zeros on
the real axis has to remove primes as well.
-/

open Complex Metric Set Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

variable {ι : Type*} {a lam : ι → ℝ}

/-- **A holomorphic Euler factor of a positive perturbation has a zero near its real
abscissa.** If `E = exp D` right of the real abscissa `σ_c` of a nonnegative general Dirichlet
series `D`, and `E` is holomorphic on a disc around `σ_c`, then `E` vanishes somewhere in the
disc. -/
theorem exists_zero_of_eulerFactor_differentiableOn (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σc : ℝ} (hsum : ∀ σ, σc < σ → Summable (gdTwistTerm a lam σ 0))
    (hdiv : ∀ σ, σ < σc → ¬ Summable (gdTwistTerm a lam σ 0))
    {E : ℂ → ℂ} (hE : ∀ s : ℂ, σc < s.re → E s = cexp (gdSeries a lam s))
    {r : ℝ} (hr : 0 < r) (hdiff : DifferentiableOn ℂ E (ball (σc : ℂ) r)) :
    ∃ s ∈ ball (σc : ℂ) r, E s = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hg, -, hEg⟩ := exists_log_on_ball hr hdiff hcon
  -- the right half of the disc
  obtain ⟨H, hH⟩ : ∃ H : Set ℂ, H = ball (σc : ℂ) r ∩ {s : ℂ | σc < s.re} := ⟨_, rfl⟩
  have hHopen : IsOpen H := by
    rw [hH]
    exact isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hHconn : IsPreconnected H := by
    rw [hH]
    exact ((convex_ball _ _).inter (convex_halfSpace_re_gt _)).isPreconnected
  have hmem : ∀ {s : ℂ}, s ∈ H → s ∈ ball (σc : ℂ) r ∧ σc < s.re := fun {s} hs => by
    rw [hH] at hs
    exact hs
  have hDat : ∀ s ∈ H, DifferentiableAt ℂ (gdSeries a lam) s := fun s hs =>
    RHTower.differentiableAt_gdSeries ha hlam
      (hsum ((σc + s.re) / 2) (by linarith only [(hmem hs).2]))
      (by linarith only [(hmem hs).2])
  have hgat : ∀ s ∈ H, DifferentiableAt ℂ g s := fun s hs =>
    hg.differentiableAt (isOpen_ball.mem_nhds (hmem hs).1)
  -- `D − g` has the constant exponential `E(σ_c)` on the right half
  have hexp : ∀ s ∈ H, cexp (gdSeries a lam s - g s) = E (σc : ℂ) := fun s hs => by
    rw [Complex.exp_sub, ← hE s (hmem hs).2, hEg s (hmem hs).1,
      mul_div_cancel_right₀ _ (Complex.exp_ne_zero _)]
  -- hence a vanishing derivative
  have hderiv : ∀ s ∈ H, deriv (fun z => gdSeries a lam z - g z) s = 0 := fun s hs => by
    have hd : HasDerivAt (fun z => gdSeries a lam z - g z)
        (deriv (fun z => gdSeries a lam z - g z) s) s :=
      ((hDat s hs).sub (hgat s hs)).hasDerivAt
    have hconst : (fun _ : ℂ => E (σc : ℂ)) =ᶠ[𝓝 s]
        fun z => cexp (gdSeries a lam z - g z) := by
      filter_upwards [hHopen.mem_nhds hs] with z hz using (hexp z hz).symm
    have h0 := (hasDerivAt_const s (E (σc : ℂ))).unique (hd.cexp.congr_of_eventuallyEq hconst)
    exact (mul_eq_zero.mp h0.symm).resolve_left (Complex.exp_ne_zero _)
  have hhd : DifferentiableOn ℂ (fun z => gdSeries a lam z - g z) H := fun s hs =>
    ((hDat s hs).sub (hgat s hs)).differentiableWithinAt
  -- so `D = g + k` on the right half, and `g + k` continues `D` to the disc
  have hs₀ : ((σc + r / 2 : ℝ) : ℂ) ∈ H := by
    rw [hH]
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        add_sub_cancel_left, abs_of_pos (by linarith only [hr])]
      linarith only [hr]
    · show σc < ((σc + r / 2 : ℝ) : ℂ).re
      rw [Complex.ofReal_re]
      linarith only [hr]
  obtain ⟨k, hk⟩ : ∃ k : ℂ, k = gdSeries a lam ((σc + r / 2 : ℝ) : ℂ) -
      g ((σc + r / 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hconstk : ∀ s ∈ H, gdSeries a lam s - g s = k := fun s hs => by
    rw [hk]
    exact hHopen.is_const_of_deriv_eq_zero hHconn hhd hderiv hs hs₀
  exact RHTower.gdSeries_no_continuation_at_abscissa ha hlam hsum hdiv hr
    (G := fun s => g s + k) (hg.add_const k) fun s hs hre => by
      have h := hconstk s (by rw [hH]; exact ⟨hs, hre⟩)
      show g s + k = gdSeries a lam s
      rw [← h]
      ring

/-- **A holomorphic Euler factor of a positive perturbation vanishes at its real abscissa.** -/
theorem eulerFactor_abscissa_eq_zero (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σc : ℝ} (hsum : ∀ σ, σc < σ → Summable (gdTwistTerm a lam σ 0))
    (hdiv : ∀ σ, σ < σc → ¬ Summable (gdTwistTerm a lam σ 0))
    {E : ℂ → ℂ} (hE : ∀ s : ℂ, σc < s.re → E s = cexp (gdSeries a lam s))
    {R : ℝ} (hR : 0 < R) (hdiff : DifferentiableOn ℂ E (ball (σc : ℂ) R)) :
    E (σc : ℂ) = 0 := by
  by_contra hne
  have hcont : ContinuousAt E (σc : ℂ) :=
    hdiff.continuousOn.continuousAt (ball_mem_nhds _ hR)
  obtain ⟨ε, hε, hεE⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne hne)
  obtain ⟨s, hs, hzero⟩ := exists_zero_of_eulerFactor_differentiableOn ha hlam hsum hdiv hE
    (lt_min hε hR) (hdiff.mono (ball_subset_ball (min_le_right ε R)))
  exact hεE (lt_of_lt_of_le (mem_ball.mp hs) (min_le_left ε R)) hzero

end GaloisForLFunctions.FloorFreeArithmetic
