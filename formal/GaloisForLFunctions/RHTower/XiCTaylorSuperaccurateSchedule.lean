import GaloisForLFunctions.RHTower.XiCTaylorFluxBoundGate

/-!
# A super-accurate source-selected Xi Taylor schedule

The canonical Taylor polynomials of `XiC` and their first derivatives converge locally uniformly.
This module diagonalizes those two compact-open convergences without using the Xi divisor: it
selects a strictly increasing Taylor degree `N n` whose value and derivative errors are both below
`(n+1)^(-(n+1))` on the closed ball of radius `n`.

This is the unconditional approximation input for finite-polynomial top-down RH criteria with a
moving evaluation mesh.  The schedule contains no RH, zero-location, positivity, or spectral
hypothesis.
-/

open Complex Metric Set Filter Topology

namespace RHTower

noncomputable section

/-- The super-polynomial target tolerance used by the diagonal Taylor schedule. -/
def xiCTaylorScheduleTolerance (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ) ^ (n + 1))⁻¹

theorem xiCTaylorScheduleTolerance_pos (n : ℕ) :
    0 < xiCTaylorScheduleTolerance n := by
  unfold xiCTaylorScheduleTolerance
  positivity

/-- A Taylor schedule is super-accurate when both values and first derivatives are within
`(n+1)^(-(n+1))` on the expanding ball of radius `n`. -/
def XiCTaylorSuperaccurateSchedule (N : ℕ → ℕ) : Prop :=
  StrictMono N ∧ ∀ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) n,
    dist (XiC z) (xiCTaylorApprox (N n) z) < xiCTaylorScheduleTolerance n ∧
    dist (deriv XiC z) (deriv (xiCTaylorApprox (N n)) z) <
      xiCTaylorScheduleTolerance n

/-- The canonical Xi Taylor family admits a source-selected super-accurate diagonal schedule. -/
theorem exists_xiCTaylorSuperaccurateSchedule :
    ∃ N : ℕ → ℕ, XiCTaylorSuperaccurateSchedule N := by
  have hthreshold : ∀ n : ℕ, ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      (∀ z ∈ closedBall (0 : ℂ) n,
        dist (XiC z) (xiCTaylorApprox m z) < xiCTaylorScheduleTolerance n) ∧
      (∀ z ∈ closedBall (0 : ℂ) n,
        dist (deriv XiC z) (deriv (xiCTaylorApprox m) z) <
          xiCTaylorScheduleTolerance n) := by
    intro n
    have hfun : TendstoUniformlyOn xiCTaylorApprox XiC atTop
        (closedBall (0 : ℂ) n) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        (isCompact_closedBall (0 : ℂ) n)).mp
          xiCTaylorApprox_tendstoLocallyUniformly.tendstoLocallyUniformlyOn
    have hderiv : TendstoUniformlyOn (deriv ∘ xiCTaylorApprox) (deriv XiC) atTop
        (closedBall (0 : ℂ) n) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        (isCompact_closedBall (0 : ℂ) n)).mp
          xiCTaylorApprox_deriv_tendstoLocallyUniformly.tendstoLocallyUniformlyOn
    have hevFun := (Metric.tendstoUniformlyOn_iff.mp hfun)
      (xiCTaylorScheduleTolerance n) (xiCTaylorScheduleTolerance_pos n)
    have hevDeriv := (Metric.tendstoUniformlyOn_iff.mp hderiv)
      (xiCTaylorScheduleTolerance n) (xiCTaylorScheduleTolerance_pos n)
    obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (hevFun.and hevDeriv)
    refine ⟨k, fun m hm => ?_⟩
    obtain ⟨hfm, hdm⟩ := hk m hm
    refine ⟨hfm, ?_⟩
    intro z hz
    simpa only [Function.comp_apply] using hdm z hz
  choose K hK using hthreshold
  let N : ℕ → ℕ := fun n => Nat.rec (K 0)
    (fun j previous => max (previous + 1) (K (j + 1))) n
  have hN_zero : N 0 = K 0 := by rfl
  have hN_succ (n : ℕ) : N (n + 1) = max (N n + 1) (K (n + 1)) := by
    rfl
  have hKN : ∀ n : ℕ, K n ≤ N n := by
    intro n
    induction n with
    | zero => rw [hN_zero]
    | succ n _ =>
        rw [hN_succ]
        exact Nat.le_max_right _ _
  have hstrict : StrictMono N := strictMono_nat_of_lt_succ fun n => by
    rw [hN_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self (N n)) (Nat.le_max_left _ _)
  refine ⟨N, hstrict, ?_⟩
  intro n z hz
  obtain ⟨hvalue, hderiv⟩ := hK n (N n) (hKN n)
  exact ⟨hvalue z hz, hderiv z hz⟩

end

end RHTower
