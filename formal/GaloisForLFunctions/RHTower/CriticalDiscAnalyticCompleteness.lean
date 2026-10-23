import GaloisForLFunctions.RHTower.CriticalDiscEulerCompleteness
import GaloisForLFunctions.RHTower.OneDimensionalPowerSeriesPolynomial

/-!
# Full analytic completeness on the critical disc

This file upgrades FE-odd polynomial completeness to the literal holomorphic
compact-open statement.  Cauchy power-series partial sums converge uniformly
on every smaller closed disc; oddifying those scalar polynomials keeps them in
the paired Euler-tangent closed span.
-/

noncomputable section

namespace RHTower

open Complex Metric Set Filter Topology

/-- Restriction of a function continuous on a larger critical disc to a
smaller literal closed disc. -/
def criticalDiscRestriction
    (f : ℂ → ℂ) (r : ℝ) (hf : ContinuousOn f (closedBall (1 / 2 : ℂ) r)) :
    C(CriticalClosedDisc r, ℂ) where
  toFun z := f z
  continuous_toFun := hf.restrict

/-- Full finite-exception compact-disc theorem.  A function differentiable on
the larger closed disc and FE odd on the smaller disc restricts to the closed
span of the actual paired Euler tangents there. -/
theorem criticalDisc_analytic_odd_mem_closedSpan_compl_finset
    (f : ℂ → ℂ) {r₀ r₁ : ℝ}
    (hr₀ : 0 ≤ r₀) (hr01 : r₀ < r₁) (hr1 : r₁ < 1 / 2)
    (hf : DiffContOnCl ℂ f (ball (1 / 2 : ℂ) r₁))
    (hodd : ∀ z ∈ closedBall (1 / 2 : ℂ) r₀, f (1 - z) = -f z)
    (S : Finset Nat.Primes) :
    criticalDiscRestriction f r₀
        (hf.continuousOn_ball.mono (Metric.closedBall_subset_closedBall hr01.le)) ∈
      (Submodule.span ℂ
        (Set.range fun p : {p : Nat.Primes // p ∉ S} =>
          compactPrimeEulerUnitFETangent
            (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
            (p : Nat.Primes))).topologicalClosure := by
  have hr₁pos : 0 < r₁ := lt_of_le_of_lt hr₀ hr01
  let R : NNReal := ⟨r₁, hr₁pos.le⟩
  let rmid : NNReal := ⟨(r₀ + r₁) / 2, by linarith⟩
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    cauchyPowerSeries f (1 / 2 : ℂ) R
  have hp : HasFPowerSeriesOnBall f p (1 / 2 : ℂ) R := by
    dsimp [p]
    exact hf.hasFPowerSeriesOnBall (by exact_mod_cast hr₁pos)
  have hrmid : (rmid : ENNReal) < (R : ENNReal) := by
    apply ENNReal.coe_lt_coe.mpr
    apply NNReal.coe_lt_coe.mp
    change (r₀ + r₁) / 2 < r₁
    linarith
  have hu := hp.tendstoUniformlyOn hrmid
  let P : ℕ → Polynomial ℂ := fun N =>
    shiftedFmlsPolynomial p N (1 / 2 : ℂ)
  let q : ℕ → C(CriticalClosedDisc r₀, ℂ) := fun N =>
    (1 / 2 : ℂ) •
      (compactPolynomialEval (criticalDiscCoordinate r₀) (P N) -
        compactPolynomialEval (1 - criticalDiscCoordinate r₀) (P N))
  let F : C(CriticalClosedDisc r₀, ℂ) :=
    criticalDiscRestriction f r₀
      (hf.continuousOn_ball.mono (Metric.closedBall_subset_closedBall hr01.le))
  have hqmem : ∀ N, q N ∈
      (Submodule.span ℂ
        (Set.range fun p : {p : Nat.Primes // p ∉ S} =>
          compactPrimeEulerUnitFETangent
            (criticalDiscCoordinate r₀) (criticalDiscReflection r₀)
            (p : Nat.Primes))).topologicalClosure := by
    intro N
    exact Submodule.smul_mem _ _
      (criticalDisc_fe_odd_polynomial_mem_closedSpan_compl_finset
        (hr01.trans hr1) S (P N))
  have hqF : Tendsto q atTop (nhds F) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hevent : ∀ᶠ N : ℕ in atTop, ∀ y ∈ ball (0 : ℂ) rmid,
        dist (f ((1 / 2 : ℂ) + y)) (p.partialSum N y) < ε :=
      (Metric.tendstoUniformlyOn_iff.mp hu) ε hε
    obtain ⟨N₀, hN₀⟩ := (eventually_atTop.1 hevent)
    refine ⟨N₀, fun N hN => ?_⟩
    rw [dist_eq_norm]
    apply (ContinuousMap.norm_lt_iff (q N - F) hε).2
    intro k
    change ‖q N k - F k‖ < ε
    let z : ℂ := (k : ℂ)
    let z' : ℂ := 1 - z
    let y : ℂ := z - 1 / 2
    let y' : ℂ := z' - 1 / 2
    have hk : ‖y‖ ≤ r₀ := by
      have := k.prop
      rw [mem_closedBall, dist_eq] at this
      simpa [y, z] using this
    have hk' : ‖y'‖ ≤ r₀ := by
      have heq : y' = -y := by dsimp [y', y, z']; ring
      rw [heq, norm_neg]
      exact hk
    have hrmidR : r₀ < (rmid : ℝ) := by
      change r₀ < (r₀ + r₁) / 2
      linarith
    have hy : y ∈ ball (0 : ℂ) rmid := by
      simpa [mem_ball, dist_zero_right] using hk.trans_lt hrmidR
    have hy' : y' ∈ ball (0 : ℂ) rmid := by
      simpa [mem_ball, dist_zero_right] using hk'.trans_lt hrmidR
    have happrox := hN₀ N hN y hy
    have happrox' := hN₀ N hN y' hy'
    have hP : (P N).eval z = p.partialSum N y := by
      simpa [P, y, z] using
        shiftedFmlsPolynomial_eval p N (1 / 2 : ℂ) z
    have hP' : (P N).eval z' = p.partialSum N y' := by
      simpa [P, y', z'] using
        shiftedFmlsPolynomial_eval p N (1 / 2 : ℂ) z'
    have hzmem : z ∈ closedBall (1 / 2 : ℂ) r₀ := k.prop
    have hoddz := hodd z hzmem
    have happroxNorm : ‖(P N).eval z - f z‖ < ε := by
      rw [hP]
      have hcenter : (1 / 2 : ℂ) + y = z := by dsimp [y]; ring
      rw [hcenter] at happrox
      simpa [dist_eq_norm, norm_sub_rev] using happrox
    have happroxNorm' : ‖(P N).eval z' - f z'‖ < ε := by
      rw [hP']
      have hcenter : (1 / 2 : ℂ) + y' = z' := by dsimp [y']; ring
      rw [hcenter] at happrox'
      simpa [dist_eq_norm, norm_sub_rev] using happrox'
    have hqeq : q N k - F k =
        (1 / 2 : ℂ) *
          (((P N).eval z - f z) - ((P N).eval z' - f z')) := by
      simp only [q, F, ContinuousMap.smul_apply, ContinuousMap.sub_apply,
        compactPolynomialEval_apply, criticalDiscRestriction, criticalDiscCoordinate]
      dsimp [z, z'] at hoddz ⊢
      rw [hoddz]
      ring
    rw [hqeq, norm_mul]
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hhalf]
    have htri := norm_sub_le ((P N).eval z - f z) ((P N).eval z' - f z')
    linarith
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hqF
    (Filter.Eventually.of_forall hqmem)

end RHTower
