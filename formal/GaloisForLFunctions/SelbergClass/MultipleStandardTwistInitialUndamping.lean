import GaloisForLFunctions.SelbergClass.MultipleStandardTwistNormalFamily

/-!
# Uniform initial-domain undamping for multiple standard twists

On every ball whose fixed doubled left shift stays in the initial
absolute-convergence domain, the concrete damped tensor `D.damped X` converges
uniformly to `D.initial` as `X → ∞`.  The proof is the direct finite-head plus
summable-tail argument: no continuation provider, normal-family interface, or
extra analytic hypothesis is introduced.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass

/-- Each concrete damped summand converges uniformly on a ball to its undamped
summand.  The fixed shifted undamped summand bounds its spatial amplitude,
while the damping exponential tends to the unit-modulus phase independently of
the spatial variable. -/
theorem tendstoUniformlyOn_dampedMultipleStandardTwistTerm_atTop_initial_on_ball
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ)
    (s₀ : Fin N → ℂ) {r : ℝ} (hr : 0 < r) (n : Fin N → ℕ+) :
    TendstoUniformlyOn
      (fun X : ℝ => fun z : Fin N → ℂ =>
        dampedMultipleStandardTwistTerm a κ α X z n)
      (fun z : Fin N → ℂ => multipleStandardTwistTerm a κ α z n)
      atTop (Metric.ball s₀ r) := by
  let q : Fin N → ℂ := fun i => s₀ i - (2 * r : ℝ)
  let M : ℝ := ‖multipleStandardTwistTerm a κ α q n‖
  have hphase : Tendsto
      (fun X : ℝ => Complex.exp
        (-multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ)))
      atTop (𝓝 (multipleStandardTwistPhase κ α n)) := by
    have hz := tendsto_multipleTwistDampingParameter_atTop α
    have harg := hz.neg.mul_const (multipleIndexPower κ n : ℂ)
    have h := Complex.continuous_exp.continuousAt.tendsto.comp harg
    rw [multipleStandardTwistPhase]
    change Tendsto
      (Complex.exp ∘ fun X : ℝ =>
        -multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ))
      atTop
      (𝓝 (Complex.exp
        (-(2 * (Real.pi : ℂ) * (α : ℂ) * I) * (multipleIndexPower κ n : ℂ))))
    exact h
  have hzero : Tendsto
      (fun X : ℝ => M * ‖Complex.exp
        (-multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ)) -
          multipleStandardTwistPhase κ α n‖)
      atTop (𝓝 0) := by
    have hsub := hphase.sub
      (tendsto_const_nhds : Tendsto
        (fun _ : ℝ => multipleStandardTwistPhase κ α n) atTop
        (𝓝 (multipleStandardTwistPhase κ α n)))
    have hnorm := hsub.norm
    have hmul :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => M) atTop (𝓝 M)).mul hnorm
    simpa using hmul
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ X : ℝ in atTop,
      M * ‖Complex.exp
        (-multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ)) -
          multipleStandardTwistPhase κ α n‖ < ε :=
    (tendsto_order.1 hzero).2 ε hε
  filter_upwards [hsmall] with X hX z hz
  have hmajor := norm_multipleStandardTwistTerm_le_shift_of_mem_ball
    a κ α s₀ z n hr hz
  have hbase :
      ‖∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-z i))‖ ≤ M := by
    rw [show ‖∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-z i))‖ =
      ‖multipleStandardTwistTerm a κ α z n‖ by
        rw [multipleStandardTwistTerm, norm_mul, norm_multipleStandardTwistPhase, mul_one]]
    simpa only [M, q] using hmajor
  calc
    dist (multipleStandardTwistTerm a κ α z n)
        (dampedMultipleStandardTwistTerm a κ α X z n) =
        ‖(∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-z i))) *
          (multipleStandardTwistPhase κ α n -
            Complex.exp (-multipleTwistDampingParameter α X *
              (multipleIndexPower κ n : ℂ)))‖ := by
          rw [multipleStandardTwistTerm, dampedMultipleStandardTwistTerm,
            dist_eq_norm, mul_sub]
    _ = ‖∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-z i))‖ *
          ‖multipleStandardTwistPhase κ α n -
            Complex.exp (-multipleTwistDampingParameter α X *
              (multipleIndexPower κ n : ℂ))‖ := by rw [norm_mul]
    _ = ‖∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-z i))‖ *
          ‖Complex.exp (-multipleTwistDampingParameter α X *
            (multipleIndexPower κ n : ℂ)) - multipleStandardTwistPhase κ α n‖ := by
          rw [norm_sub_rev]
    _ ≤ M * ‖Complex.exp (-multipleTwistDampingParameter α X *
          (multipleIndexPower κ n : ℂ)) - multipleStandardTwistPhase κ α n‖ :=
      mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
    _ < ε := hX

/-- The actual Kaczorowski--Perelli damped tensor converges uniformly to its
undamped initial tensor on every ball whose doubled left shift stays in the
initial domain.  This proves only initial-domain undamping; it neither crosses
the boundary nor supplies a meromorphic continuation. -/
theorem MultipleStandardTwistData.tendstoUniformlyOn_damped_atTop_initial_on_ball
    {N : ℕ} (D : MultipleStandardTwistData N) (s₀ : Fin N → ℂ) {r : ℝ}
    (hr : 0 < r) (hshift : ∀ i, 1 < (s₀ i - (2 * r : ℝ)).re) :
    TendstoUniformlyOn (fun X : ℝ => D.damped X) D.initial atTop
      (Metric.ball s₀ r) := by
  let q : Fin N → ℂ := fun i => s₀ i - (2 * r : ℝ)
  let M : (Fin N → ℕ+) → ℝ := fun n =>
    ‖multipleStandardTwistTerm D.coeff D.kappa D.alpha q n‖
  have hM : Summable M := by
    exact D.summable_norm_initialTerm q (by simpa [q] using hshift)
  have htermInitial : ∀ (n : Fin N → ℕ+) (z : Fin N → ℂ),
      z ∈ Metric.ball s₀ r →
      ‖multipleStandardTwistTerm D.coeff D.kappa D.alpha z n‖ ≤ M n := by
    intro n z hz
    simpa only [M, q] using
      norm_multipleStandardTwistTerm_le_shift_of_mem_ball
        D.coeff D.kappa D.alpha s₀ z n hr hz
  have htermDamped : ∀ (n : Fin N → ℕ+) (X : ℝ) (z : Fin N → ℂ),
      X ∈ Set.Ioi 0 → z ∈ Metric.ball s₀ r →
      ‖dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n‖ ≤ M n := by
    intro n X z hX hz
    calc
      ‖dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n‖ ≤
          ‖multipleStandardTwistTerm D.coeff D.kappa D.alpha z n‖ :=
        norm_dampedMultipleStandardTwistTerm_le_undamped D.coeff D.kappa
          D.alpha_pos.le hX z n
      _ ≤ M n := htermInitial n z hz
  have hInitialTail : TendstoUniformlyOn
      (fun t : Finset (Fin N → ℕ+) => fun z : Fin N → ℂ =>
        ∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n)
      D.initial atTop (Metric.ball s₀ r) := by
    change TendstoUniformlyOn
      (fun t : Finset (Fin N → ℕ+) => fun z : Fin N → ℂ =>
        ∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n)
      (fun z : Fin N → ℂ =>
        ∑' n : Fin N → ℕ+, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n)
      atTop (Metric.ball s₀ r)
    exact tendstoUniformlyOn_tsum hM (fun n z hz => htermInitial n z hz)
  have hDampedTail : TendstoUniformlyOn
      (fun t : Finset (Fin N → ℕ+) => fun p : ℝ × (Fin N → ℂ) =>
        ∑ n ∈ t, dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha p.1 p.2 n)
      (fun p : ℝ × (Fin N → ℂ) => D.damped p.1 p.2)
      atTop (Set.Ioi 0 ×ˢ Metric.ball s₀ r) := by
    simpa only [MultipleStandardTwistData.damped, dampedMultipleStandardTwist] using
      (tendstoUniformlyOn_tsum hM (fun n p hp =>
        htermDamped n p.1 p.2 hp.1 hp.2))
  have hhead : ∀ t : Finset (Fin N → ℕ+), TendstoUniformlyOn
      (fun X : ℝ => fun z : Fin N → ℂ =>
        ∑ n ∈ t, dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n)
      (fun z : Fin N → ℂ =>
        ∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n)
      atTop (Metric.ball s₀ r) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        filter_upwards with X z hz
        simpa using hε
    | insert n t hn ht =>
        let hd : (ℝ → (Fin N → ℂ) → ℂ) := fun X z =>
          dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n
        let hdt : ℝ → (Fin N → ℂ) → ℂ := fun X z =>
          ∑ m ∈ t, dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z m
        let hi : (Fin N → ℂ) → ℂ := fun z =>
          multipleStandardTwistTerm D.coeff D.kappa D.alpha z n
        let hit : (Fin N → ℂ) → ℂ := fun z =>
          ∑ m ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z m
        have hdEq : (fun X : ℝ => fun z : Fin N → ℂ =>
            ∑ m ∈ insert n t,
              dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z m) = hd + hdt := by
          funext X z
          exact Finset.sum_insert hn
        have hiEq : (fun z : Fin N → ℂ =>
            ∑ m ∈ insert n t,
              multipleStandardTwistTerm D.coeff D.kappa D.alpha z m) = hi + hit := by
          funext z
          exact Finset.sum_insert hn
        rw [hdEq, hiEq]
        exact (tendstoUniformlyOn_dampedMultipleStandardTwistTerm_atTop_initial_on_ball
          D.coeff D.kappa D.alpha s₀ hr n).add ht
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hI := (Metric.tendstoUniformlyOn_iff.mp hInitialTail) (ε / 3) hε3
  have hD := (Metric.tendstoUniformlyOn_iff.mp hDampedTail) (ε / 3) hε3
  obtain ⟨t, htI, htD⟩ := (hI.and hD).exists
  have hH := (Metric.tendstoUniformlyOn_iff.mp (hhead t)) (ε / 3) hε3
  filter_upwards [eventually_gt_atTop (0 : ℝ), hH] with X hX hH' z hz
  have hI' := htI z hz
  have hD' : dist (D.damped X z)
      (∑ n ∈ t, dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n) < ε / 3 := by
    simpa only [Prod.fst, Prod.snd] using
      htD (X, z) (by simpa only [Set.mem_prod, Set.mem_Ioi] using ⟨hX, hz⟩)
  have hDrev : dist
      (∑ n ∈ t, dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n)
      (D.damped X z) < ε / 3 := by
    rw [dist_comm]
    exact hD'
  calc
    dist (D.initial z) (D.damped X z) ≤
        dist (D.initial z)
          (∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n) +
          dist (∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n)
            (∑ n ∈ t, dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n) +
          dist (∑ n ∈ t, dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n)
            (D.damped X z) := by
      calc
        dist (D.initial z) (D.damped X z) ≤
            dist (D.initial z)
              (∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n) +
            dist (∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n)
              (D.damped X z) := dist_triangle _ _ _
        _ ≤ dist (D.initial z)
              (∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n) +
            (dist (∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n)
              (∑ n ∈ t, dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n) +
            dist (∑ n ∈ t, dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n)
              (D.damped X z)) := by
          calc
            dist (D.initial z)
                (∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n) +
                dist (∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n)
                  (D.damped X z) =
                dist (∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n)
                  (D.damped X z) +
                dist (D.initial z)
                  (∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n) := by ring
            _ ≤ (dist (∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n)
                  (∑ n ∈ t, dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n) +
                dist (∑ n ∈ t, dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n)
                  (D.damped X z)) +
                dist (D.initial z)
                  (∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n) :=
              add_le_add_left (dist_triangle
                (∑ n ∈ t, multipleStandardTwistTerm D.coeff D.kappa D.alpha z n)
                (∑ n ∈ t, dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n)
                (D.damped X z)) _
            _ = _ := by ring
        _ = _ := by ring
    _ < ε := by
      nlinarith [hI', hH' z hz, hDrev]

end GaloisForLFunctions.SelbergClass
