import GaloisForLFunctions.HTGeometry.GeneralDirichletLandau
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Relative Landau rigidity: a positive perturbation pays for every new zero with a real singularity

A generalized-prime perturbation of `ζ` with nonnegative weights `a_j` at frequencies `λ_j ≥ 0` has
logarithmic Euler factor `D(s) = Σ a_j e^{-λ_j s}`, a general Dirichlet series with nonnegative
coefficients, and Euler factor `exp D`.  Let `σ_c` be its real abscissa: `D` converges for
`Re s > σ_c` and diverges at every real `σ < σ_c`.

* `differentiableAt_gdSeries` — `D` is holomorphic on `Re s > σ_c`.
* `gdSeries_no_continuation_at_abscissa` — **Landau:** `D` has no holomorphic continuation to any
  neighbourhood of the real point `σ_c`.  A continuation on a small ball around `σ_c`, glued to `D`
  on the half-plane, would be holomorphic on a closed disk centred to the right of `σ_c` and
  reaching past it; the corpus transfer theorem then forces convergence left of `σ_c`.
* `re_le_abscissa_of_eulerFactor_zero` — any extension of the Euler factor that vanishes at `ρ`
  has `Re ρ ≤ σ_c`, because `exp D ≠ 0` wherever `D` converges.
* `landau_relative_rigidity` — hence a zero of the perturbed zeta `ζ · E` at a point `ρ` that is
  not a zero of `ζ` certifies `Re ρ ≤ σ_c` together with a real singular point of the logarithmic
  Euler factor at `σ_c`.

This is the exact relative content of the observation that the corpus countermodels enlarge the
real boundary when they create off-line zeros.  It is relative to `ζ`: it constrains what a positive
perturbation can do, and says nothing about the zeros of `ζ` itself.
-/

open Complex Metric GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

noncomputable section

variable {ι : Type*} {a lam : ι → ℝ}

/-- A nonnegative general Dirichlet series is holomorphic at every point of its half-plane of
convergence: the point lies in a disk of convergence centred far to the right on the real axis. -/
theorem differentiableAt_gdSeries (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σ₁ : ℝ} (hsum : Summable (gdTwistTerm a lam σ₁ 0)) {s : ℂ} (hs : σ₁ < s.re) :
    DifferentiableAt ℂ (gdSeries a lam) s := by
  set d : ℝ := s.re - σ₁ with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set h : ℝ := d + s.im ^ 2 / d + 1 with hh
  have hhpos : 0 < h := by
    rw [hh]
    have : 0 ≤ s.im ^ 2 / d := div_nonneg (sq_nonneg _) hdpos.le
    linarith
  have hball := hasFPowerSeriesOnBall_gdSeries ha hlam hsum hhpos
  have hmem : s ∈ Metric.eball (((σ₁ + h : ℝ) : ℂ)) (ENNReal.ofReal h) := by
    rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_ofReal_iff hhpos, dist_eq_norm]
    have hsq : ‖s - ((σ₁ + h : ℝ) : ℂ)‖ ^ 2 = (s.re - (σ₁ + h)) ^ 2 + s.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      ring
    have hlt : ‖s - ((σ₁ + h : ℝ) : ℂ)‖ ^ 2 < h ^ 2 := by
      rw [hsq]
      have hre : s.re - (σ₁ + h) = d - h := by rw [hd]; ring
      rw [hre]
      have hkey : d ^ 2 + s.im ^ 2 < 2 * h * d := by
        have h1 : s.im ^ 2 / d * d = s.im ^ 2 := div_mul_cancel₀ _ hdpos.ne'
        rw [hh]
        nlinarith [h1, hdpos]
      nlinarith [hkey]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hhpos.le (by norm_num)).mp hlt
  exact (hball.analyticAt_of_mem hmem).differentiableAt

/-- The closed disk of radius `2 + ε` centred at `σ_c + 2` lies in the half-plane `Re s > σ_c`
together with the ball of radius `r` around `σ_c`, provided `ε ≤ 1/2` and `ε ≤ r²/6`. -/
theorem closedBall_subset_halfPlane_union_ball {σc r ε : ℝ} (hr : 0 < r)
    (hε1 : ε ≤ 1 / 2) (hε2 : ε ≤ r ^ 2 / 6) (hε0 : 0 ≤ ε) :
    closedBall (((σc + 1 + 1 : ℝ) : ℂ)) (2 + ε) ⊆ {z : ℂ | σc < z.re} ∪ ball ((σc : ℂ)) r := by
  intro z hz
  by_cases hre : σc < z.re
  · exact Or.inl hre
  · right
    have hre' : z.re ≤ σc := not_lt.mp hre
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    have hsq1 : ‖z - ((σc + 1 + 1 : ℝ) : ℂ)‖ ^ 2 = (z.re - (σc + 1 + 1)) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      ring
    have hsq2 : ‖z - (σc : ℂ)‖ ^ 2 = (z.re - σc) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      ring
    have hz2 : ‖z - ((σc + 1 + 1 : ℝ) : ℂ)‖ ^ 2 ≤ (2 + ε) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hz 2
    rw [hsq1] at hz2
    have hlt : (z.re - σc) ^ 2 + z.im ^ 2 < r ^ 2 := by
      have ha0 : 0 ≤ σc - z.re := by linarith [hre']
      have hε2' : ε ^ 2 ≤ ε / 2 := by nlinarith
      nlinarith [hz2, ha0, hε2', hε2, hr]
    rw [← hsq2] at hlt
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr.le (by norm_num)).mp hlt

/-- **Landau: the real abscissa is a singular point.**  If a nonnegative general Dirichlet series
converges for every real `σ > σ_c` and diverges for every real `σ < σ_c`, then no function
holomorphic on a ball around `σ_c` agrees with it on the part of the ball to the right of `σ_c`. -/
theorem gdSeries_no_continuation_at_abscissa (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σc : ℝ} (hsum : ∀ σ, σc < σ → Summable (gdTwistTerm a lam σ 0))
    (hdiv : ∀ σ, σ < σc → ¬ Summable (gdTwistTerm a lam σ 0))
    {r : ℝ} (hr : 0 < r) {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball ((σc : ℂ)) r))
    (hagree : ∀ s ∈ ball ((σc : ℂ)) r, σc < s.re → G s = gdSeries a lam s) : False := by
  classical
  set F : ℂ → ℂ := fun s => if σc < s.re then gdSeries a lam s else G s with hF
  set ε : ℝ := min (1 / 2) (r ^ 2 / 6) with hε
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hε2 : ε ≤ r ^ 2 / 6 := min_le_right _ _
  have hεpos : 0 < ε := lt_min (by norm_num) (by positivity)
  have hsum1 : Summable (gdTwistTerm a lam (σc + 1) 0) := hsum _ (by linarith)
  set R : NNReal := (2 + ε).toNNReal with hRdef
  have hRcoe : ((R : NNReal) : ℝ) = 2 + ε := Real.coe_toNNReal _ (by linarith)
  have hopen : IsOpen {z : ℂ | σc < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hcover : closedBall (((σc + 1 + 1 : ℝ) : ℂ)) ((R : NNReal) : ℝ)
      ⊆ {z : ℂ | σc < z.re} ∪ ball ((σc : ℂ)) r := by
    rw [hRcoe]
    exact closedBall_subset_halfPlane_union_ball hr hε1 hε2 hεpos.le
  have hFd : DifferentiableOn ℂ F (closedBall (((σc + 1 + 1 : ℝ) : ℂ)) ((R : NNReal) : ℝ)) := by
    intro s hs
    rcases hcover hs with hs1 | hs2
    · have hFev : F =ᶠ[nhds s] gdSeries a lam := by
        filter_upwards [hopen.mem_nhds hs1] with z hz
        have hz' : σc < z.re := hz
        show (if σc < z.re then gdSeries a lam z else G z) = gdSeries a lam z
        rw [if_pos hz']
      have hmid : σc < (σc + s.re) / 2 := by
        have : σc < s.re := hs1
        linarith
      have hd : DifferentiableAt ℂ (gdSeries a lam) s :=
        differentiableAt_gdSeries ha hlam (hsum _ hmid) (by
          have : σc < s.re := hs1
          linarith)
      exact (hd.congr_of_eventuallyEq hFev).differentiableWithinAt
    · have hFeq : ∀ z ∈ ball ((σc : ℂ)) r, F z = G z := by
        intro z hz
        show (if σc < z.re then gdSeries a lam z else G z) = G z
        by_cases hzre : σc < z.re
        · rw [if_pos hzre]
          exact (hagree z hz hzre).symm
        · rw [if_neg hzre]
      have hFev : F =ᶠ[nhds s] G := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hs2] with z hz
        exact hFeq z hz
      have hd : DifferentiableAt ℂ G s :=
        (hG s hs2).differentiableAt (Metric.isOpen_ball.mem_nhds hs2)
      exact (hd.congr_of_eventuallyEq hFev).differentiableWithinAt
  have hFagree : ∀ s : ℂ, σc + 1 < s.re → F s = gdSeries a lam s := by
    intro s hs
    have : σc < s.re := by linarith
    show (if σc < s.re then gdSeries a lam s else G s) = gdSeries a lam s
    rw [if_pos this]
  have hleft : σc + 1 + 1 - ((R : NNReal) : ℝ) < σc - ε / 2 := by
    rw [hRcoe]
    linarith
  have hsummable :=
    general_landau_summable_transfer ha hlam hsum1 (h := (1 : ℝ)) one_pos (R := R) hFd hFagree
      (σ := σc - ε / 2) hleft
  exact hdiv _ (by linarith) hsummable

/-- Any extension of the Euler factor `exp D` that vanishes at `ρ` has `Re ρ ≤ σ_c`: the
exponential of a convergent series never vanishes. -/
theorem re_le_abscissa_of_eulerFactor_zero {σc : ℝ} {E : ℂ → ℂ}
    (hE : ∀ s : ℂ, σc < s.re → E s = Complex.exp (gdSeries a lam s))
    {ρ : ℂ} (hρ : E ρ = 0) : ρ.re ≤ σc := by
  by_contra h
  have h' : σc < ρ.re := not_le.mp h
  rw [hE ρ h'] at hρ
  exact Complex.exp_ne_zero _ hρ

/-- **Relative Landau rigidity.**  Let `E` extend the Euler factor `exp D` of a nonnegative
generalized-prime perturbation with real abscissa `σ_c`.  If the perturbed zeta `ζ · E` vanishes at a
point `ρ` where `ζ` does not, then `Re ρ ≤ σ_c`, and `σ_c` is a real singular point of the
logarithmic Euler factor: no function holomorphic on a ball around `σ_c` agrees with `D` to the
right of `σ_c`.  A new zero is paid for by a real singularity at or beyond its real part. -/
theorem landau_relative_rigidity (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σc : ℝ} (hsum : ∀ σ, σc < σ → Summable (gdTwistTerm a lam σ 0))
    (hdiv : ∀ σ, σ < σc → ¬ Summable (gdTwistTerm a lam σ 0))
    {E : ℂ → ℂ} (hE : ∀ s : ℂ, σc < s.re → E s = Complex.exp (gdSeries a lam s))
    {ρ : ℂ} (hζ : riemannZeta ρ ≠ 0) (hzero : riemannZeta ρ * E ρ = 0) :
    ρ.re ≤ σc ∧
      ∀ r : ℝ, 0 < r → ∀ G : ℂ → ℂ, DifferentiableOn ℂ G (ball ((σc : ℂ)) r) →
        (∀ s ∈ ball ((σc : ℂ)) r, σc < s.re → G s = gdSeries a lam s) → False := by
  have hEρ : E ρ = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h hζ
    · exact h
  exact ⟨re_le_abscissa_of_eulerFactor_zero hE hEρ,
    fun r hr G hG hagree => gdSeries_no_continuation_at_abscissa ha hlam hsum hdiv hr hG hagree⟩

end

end RHTower
