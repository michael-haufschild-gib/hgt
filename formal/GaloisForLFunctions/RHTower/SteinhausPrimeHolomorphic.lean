import GaloisForLFunctions.RHTower.SteinhausPrimeDivergence
import GaloisForLFunctions.RHTower.DirichletUniformAbel
import GaloisForLFunctions.RHTower.DirichletWidthOne
import GaloisForLFunctions.HTGeometry.IndependentCoordSeriesConvergence

/-!
# The random prime Dirichlet series is almost surely holomorphic past the half line

Right of the half line the prime series `∑_p p^{-σ} X_p` has square summable terms, so Kolmogorov's
convergence criterion applies: it converges almost surely at every real `σ > 1/2`.  Convergence at a
point propagates to the right and is locally uniform there, so almost surely the series defines a
holomorphic function on the whole half plane `Re s > 1/2`, agreeing with the absolutely convergent
sum where the latter exists.

Together with `SteinhausPrimeDivergence` this pins the almost-sure abscissa of convergence of the
prime series at exactly `1/2`: divergence at every `σ ≤ 1/2`, convergence at every `σ > 1/2`.
-/

noncomputable section

open MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower.SteinhausModel

/-- The coefficient bound of the prime term. -/
def primeTermBound (σ : ℝ) (n : ℕ) : ℝ := if n.Prime then (n : ℝ) ^ (-σ) else 0

theorem primeTermBound_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ primeTermBound σ n := by
  rw [primeTermBound]
  by_cases h : n.Prime
  · rw [if_pos h]; positivity
  · rw [if_neg h]

theorem norm_primeTerm_le (σ : ℝ) (n : ℕ) (y : ℝ) :
    ‖primeTerm σ n y‖ ≤ primeTermBound σ n := by
  rw [primeTerm, primeTermBound]
  by_cases h : n.Prime
  · rw [if_pos h, if_pos h, norm_mul, Complex.norm_real, Complex.norm_exp]
    have hre : (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((y : ℝ) : ℂ)).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre, Real.exp_zero, mul_one, Real.norm_of_nonneg (by positivity)]
  · rw [if_neg h, if_neg h, norm_zero]

theorem norm_primeTerm_eq (σ : ℝ) (n : ℕ) (y : ℝ) :
    ‖primeTerm σ n y‖ = primeTermBound σ n := by
  rw [primeTerm, primeTermBound]
  by_cases h : n.Prime
  · rw [if_pos h, if_pos h, norm_mul, Complex.norm_real, Complex.norm_exp]
    have hre : (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((y : ℝ) : ℂ)).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre, Real.exp_zero, mul_one, Real.norm_of_nonneg (by positivity)]
  · rw [if_neg h, if_neg h, norm_zero]

/-- The prime term is centred: a nontrivial phase averages to zero. -/
theorem integral_primeTerm (σ : ℝ) (n : ℕ) :
    ∫ y, primeTerm σ n y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 0 := by
  show ∫ y, (if n.Prime then (((n : ℝ) ^ (-σ) : ℝ) : ℂ)
      * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((y : ℝ) : ℂ)) else 0)
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 0
  by_cases h : n.Prime
  · have hfun : (fun y : ℝ => if n.Prime then (((n : ℝ) ^ (-σ) : ℝ) : ℂ)
        * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((y : ℝ) : ℂ)) else 0)
        = fun y : ℝ => (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * charFactor 1 y := by
      funext y
      rw [if_pos h, charFactor]
      congr 2
      push_cast
      ring
    rw [hfun, integral_const_mul, charInt 1]
    norm_num
  · simp only [if_neg h]
    exact integral_zero _ _

/-- The prime term is square summable in mean past the half line. -/
theorem summable_integral_normSq_primeTerm {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun n => ∫ y, ‖primeTerm σ n y‖ ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hconst : ∀ n : ℕ,
      ∫ y, ‖primeTerm σ n y‖ ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
        = (primeTermBound σ n) ^ 2 := by
    intro n
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y => by
      rw [norm_primeTerm_eq σ n y])]
    rw [integral_const, measureReal_def]
    have : (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 := by
      rw [Measure.restrict_apply_univ, Real.volume_Icc]
      norm_num
    rw [this]
    simp
  rw [funext hconst]
  have hmaj : Summable fun n : ℕ => (n : ℝ) ^ (-(2 * σ)) := by
    rw [Real.summable_nat_rpow]
    linarith
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  rw [primeTermBound]
  by_cases h : n.Prime
  · rw [if_pos h]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [← Real.rpow_natCast ((n : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hn]
    norm_num
    rw [show -(σ * (2:ℝ)) = -(2 * σ) by ring]
  · rw [if_neg h]
    have : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 * σ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    simpa using this

/-- **The prime random Dirichlet series converges almost surely past the half line.** -/
theorem measure_coordSeriesConverges_primeTerm_eq_one {σ : ℝ} (hσ : 1 / 2 < σ) :
    steinhausMeasure (coordSeriesConverges (primeTerm σ)) = 1 := by
  have := measure_coordSeriesConverges_eq_one (primeTerm σ)
    (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1))
    (c := primeTermBound σ) (measurable_primeTerm σ) (norm_primeTerm_le σ)
    (primeTermBound_nonneg σ) (integral_primeTerm σ)
    (summable_integral_normSq_primeTerm hσ) (fun _ => 0)
  rwa [← steinhausMeasure] at this


/-! ### The Dirichlet-series indexing -/

/-- The prime phase coefficients in the `dirichletPartialSum` indexing, where the `n`-th
coefficient multiplies `(n+1)^{-s}`. -/
def primePhaseCoeff (ω : Omega) (n : ℕ) : ℂ := if (n + 1).Prime then X (n + 1) ω else 0

theorem dirichletPartialSum_primePhaseCoeff (σ : ℝ) (ω : Omega) (N : ℕ) :
    dirichletPartialSum (primePhaseCoeff ω) N ((σ : ℝ) : ℂ)
      = coordPartialSum (primeTerm σ) (N + 1) ω := by
  show ∑ n ∈ Finset.range N, primePhaseCoeff ω n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ))
    = ∑ n ∈ Finset.range (N + 1), primeTerm σ n (ω n)
  rw [Finset.sum_range_succ' (fun n => primeTerm σ n (ω n)) N]
  have hzero : primeTerm σ 0 (ω 0) = 0 := by
    rw [primeTerm, if_neg Nat.not_prime_zero]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [primePhaseCoeff, primeTerm]
  by_cases h : (n + 1).Prime
  · rw [if_pos h, if_pos h, X_prime_eq h]
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    have hpow : (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ))
        = ((((n + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [← hcast]
      rw [Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ (n : ℝ) + 1)]
      congr 1
      push_cast
      ring
    rw [hpow]
    ring
  · rw [if_neg h, if_neg h, zero_mul]

theorem convergesAt_primePhaseCoeff {σ : ℝ} {ω : Omega}
    (h : ω ∈ coordSeriesConverges (primeTerm σ)) :
    DirichletConvergesAt (primePhaseCoeff ω) ((σ : ℝ) : ℂ) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨L, ?_⟩
  have hshift : Tendsto (fun N => coordPartialSum (primeTerm σ) (N + 1) ω) atTop (𝓝 L) :=
    hL.comp (tendsto_add_atTop_nat 1)
  exact hshift.congr fun N => (dirichletPartialSum_primePhaseCoeff σ ω N).symm

/-- The full-measure event on which the prime series converges at every rational cut past the
half line. -/
def primeHolomorphicEvent : Set Omega :=
  ⋂ j : ℕ, coordSeriesConverges (primeTerm (1 / 2 + 1 / ((j : ℝ) + 1)))

theorem measurableSet_primeHolomorphicEvent : MeasurableSet primeHolomorphicEvent :=
  MeasurableSet.iInter fun _ =>
    measurableSet_coordSeriesConverges _ (measurable_primeTerm _)

/-- **The event has full measure.** -/
theorem measure_primeHolomorphicEvent : steinhausMeasure primeHolomorphicEvent = 1 := by
  have hone : ∀ j : ℕ,
      steinhausMeasure (coordSeriesConverges (primeTerm (1 / 2 + 1 / ((j : ℝ) + 1)))) = 1 := by
    intro j
    refine measure_coordSeriesConverges_primeTerm_eq_one ?_
    have : (0:ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  have hae : ∀ᵐ ω ∂steinhausMeasure, ∀ j : ℕ,
      ω ∈ coordSeriesConverges (primeTerm (1 / 2 + 1 / ((j : ℝ) + 1))) := by
    rw [ae_all_iff]
    intro j
    have hmeas := measurableSet_coordSeriesConverges
      (primeTerm (1 / 2 + 1 / ((j : ℝ) + 1))) (measurable_primeTerm _)
    have hc := (prob_compl_eq_zero_iff hmeas).mpr (hone j)
    rw [ae_iff]
    exact hc
  have haeI : ∀ᵐ ω ∂steinhausMeasure, ω ∈ primeHolomorphicEvent := by
    filter_upwards [hae] with ω hω
    exact Set.mem_iInter.mpr hω
  exact (prob_compl_eq_zero_iff measurableSet_primeHolomorphicEvent).mp (ae_iff.mp haeI)

/-- **Almost surely the prime series is holomorphic on the whole half plane `Re s > 1/2`.** -/
theorem differentiableOn_dirichletSum_primePhaseCoeff {ω : Omega}
    (hω : ω ∈ primeHolomorphicEvent) :
    DifferentiableOn ℂ (dirichletSum (primePhaseCoeff ω)) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have hs' : (1:ℝ) / 2 < s.re := hs
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 1 / ((j : ℝ) + 1) < s.re - 1 / 2 := by
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (by linarith : (0:ℝ) < s.re - 1 / 2)
    exact ⟨j, hj⟩
  set σ : ℝ := 1 / 2 + 1 / ((j : ℝ) + 1) with hσdef
  have hconv : DirichletConvergesAt (primePhaseCoeff ω) ((σ : ℝ) : ℂ) :=
    convergesAt_primePhaseCoeff (Set.mem_iInter.mp hω j)
  have hlt : ((σ : ℝ) : ℂ).re < s.re := by
    simp only [Complex.ofReal_re, hσdef]
    linarith
  have hopen : IsOpen {s' : ℂ | ((σ : ℝ) : ℂ).re < s'.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hdiff := differentiableOn_dirichletSum hconv
  exact ((hdiff.differentiableAt (hopen.mem_nhds hlt)).differentiableWithinAt)


/-! ### The Euler-side identification on the half plane of absolute convergence -/

/-- The index shift from the primes into the `dirichletPartialSum` indexing. -/
def primeShift (p : Nat.Primes) : ℕ := (p : ℕ) - 1

theorem primeShift_injective : Function.Injective primeShift := by
  intro p q hpq
  have hp : 1 ≤ (p : ℕ) := p.2.one_lt.le.trans' (by norm_num)
  have hq : 1 ≤ (q : ℕ) := q.2.one_lt.le.trans' (by norm_num)
  have : (p : ℕ) = (q : ℕ) := by
    rw [primeShift, primeShift] at hpq
    omega
  exact Subtype.ext this

theorem primeShift_add_one (p : Nat.Primes) : primeShift p + 1 = (p : ℕ) := by
  have hp : 1 ≤ (p : ℕ) := p.2.one_lt.le.trans' (by norm_num)
  rw [primeShift]
  omega

theorem notMem_range_primeShift {n : ℕ} (hn : n ∉ Set.range primeShift) : ¬ (n + 1).Prime := by
  intro hprime
  exact hn ⟨⟨n + 1, hprime⟩, by rw [primeShift]; simp⟩

/-- **On the half plane of absolute convergence the holomorphic sum is the prime Euler sum.** -/
theorem hasSum_primePhase_dirichletSum {ω : Omega} {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : Nat.Primes => X (p : ℕ) ω * ((p : ℕ) : ℂ) ^ (-s))
      (dirichletSum (primePhaseCoeff ω) s) := by
  classical
  set f : ℕ → ℂ := fun n => primePhaseCoeff ω n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) with hf
  have hnorm : ∀ n, ‖f n‖ ≤ ((n : ℝ) + 1) ^ (-s.re) := by
    intro n
    rw [hf]
    simp only
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) _]
    have hcoeff : ‖primePhaseCoeff ω n‖ ≤ 1 := by
      rw [primePhaseCoeff]
      by_cases h : (n + 1).Prime
      · rw [if_pos h, norm_X]
      · rw [if_neg h, norm_zero]; norm_num
    have hre : ((-s).re) = -s.re := by simp
    rw [hre]
    calc ‖primePhaseCoeff ω n‖ * ((n : ℝ) + 1) ^ (-s.re)
        ≤ 1 * ((n : ℝ) + 1) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (by positivity) _)
      _ = ((n : ℝ) + 1) ^ (-s.re) := one_mul _
  have hsummable : Summable f :=
    Summable.of_norm_bounded (summable_shift_rpow_neg hs) hnorm
  have hsum : HasSum f (∑' n, f n) := hsummable.hasSum
  have hconv : DirichletConvergesAt (primePhaseCoeff ω) s := ⟨∑' n, f n, hsum.tendsto_sum_nat⟩
  have heq : dirichletSum (primePhaseCoeff ω) s = ∑' n, f n :=
    tendsto_nhds_unique (tendsto_dirichletSum hconv) hsum.tendsto_sum_nat
  rw [heq]
  refine (Function.Injective.hasSum_iff (f := f) primeShift_injective ?_).mpr hsum |>.congr_fun ?_
  · intro n hn
    rw [hf]
    simp only
    rw [primePhaseCoeff, if_neg (notMem_range_primeShift hn), zero_mul]
  · intro p
    rw [Function.comp_apply, hf]
    simp only
    have h1 : (primeShift p : ℝ) + 1 = ((p : ℕ) : ℝ) := by
      rw [← primeShift_add_one p]
      push_cast
      ring
    rw [primePhaseCoeff, if_pos (by rw [primeShift_add_one]; exact p.2), primeShift_add_one, h1]
    norm_cast

end GaloisForLFunctions.RHTower

end
