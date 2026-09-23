import GaloisForLFunctions.RHTower.SuzukiHarmonicRieszClockTransmutation

/-!
# Observer-jet formation and Suzuki source reduction

Finite source charges split canonically into mass, drift, and second-boundary history. Their
pairing with an observer clock is the exact value--slope--curvature Green identity. The literal
harmonic--Riesz clock has bounded second curvature, and the completed arithmetic source lands in
this decomposition. A linear bound for its signed second-formation action therefore implies RH.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def observerJetMass (q : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), q k

def observerJetDrift (q : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), (k : ℝ) * q k

def observerJetAffinePart (q : ℕ → ℝ) (N k : ℕ) : ℝ :=
  (if k = 0 then observerJetMass q N - observerJetDrift q N else 0) +
    (if k = 1 then observerJetDrift q N else 0)

def observerJetResidual (q : ℕ → ℝ) (N k : ℕ) : ℝ :=
  q k - observerJetAffinePart q N k

def observerJetPrefix (r : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1), r k

def observerJetSecondHistory (r : ℕ → ℝ) (j : ℕ) : ℝ :=
  observerJetPrefix (observerJetPrefix r) j

def observerJetCurvature (rate : ℕ → ℝ) (j : ℕ) : ℝ :=
  rate (j + 2) - 2 * rate (j + 1) + rate j

@[simp] theorem observerJetPrefix_zero (r : ℕ → ℝ) :
    observerJetPrefix r 0 = r 0 := by
  simp [observerJetPrefix]

theorem observerJetPrefix_succ (r : ℕ → ℝ) (j : ℕ) :
    observerJetPrefix r (j + 1) = observerJetPrefix r j + r (j + 1) := by
  simp [observerJetPrefix, Finset.sum_range_succ]

@[simp] theorem observerJetSecondHistory_zero (r : ℕ → ℝ) :
    observerJetSecondHistory r 0 = r 0 := by
  simp [observerJetSecondHistory]

theorem observerJetSecondHistory_succ (r : ℕ → ℝ) (j : ℕ) :
    observerJetSecondHistory r (j + 1) =
      observerJetSecondHistory r j + observerJetPrefix r (j + 1) := by
  exact observerJetPrefix_succ (observerJetPrefix r) j

theorem observerJetAbelSummation (a f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a n * f n) =
      observerJetPrefix a N * f N +
        ∑ n ∈ Finset.range N,
          observerJetPrefix a n * (f n - f (n + 1)) := by
  have hbp := Finset.sum_range_by_parts f a (N + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hbp
  have hlhs : (∑ n ∈ Finset.range (N + 1), a n * f n) =
      ∑ n ∈ Finset.range (N + 1), f n * a n := by
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hinner : ∀ n ∈ Finset.range N,
      (f (n + 1) - f n) * (∑ k ∈ Finset.range (n + 1), a k) =
        -(observerJetPrefix a n * (f n - f (n + 1))) := by
    intro n _
    rw [observerJetPrefix]
    ring
  rw [hlhs, hbp, Finset.sum_congr rfl hinner, Finset.sum_neg_distrib,
    observerJetPrefix]
  ring

theorem observerJetResidual_mass_zero
    (q : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.range (N + 1), observerJetResidual q N k) = 0 := by
  have hN0 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  simp only [observerJetResidual, Finset.sum_sub_distrib]
  simp only [observerJetAffinePart, Finset.sum_add_distrib]
  simp [observerJetMass, hN0]

theorem observerJetResidual_drift_zero
    (q : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.range (N + 1), (k : ℝ) * observerJetResidual q N k) = 0 := by
  have hN0 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  simp only [observerJetResidual, mul_sub, Finset.sum_sub_distrib]
  simp only [observerJetAffinePart, mul_add, Finset.sum_add_distrib]
  simp [observerJetDrift, hN0]

theorem observerJetResidual_prefix_terminal
    (q : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    observerJetPrefix (observerJetResidual q N) N = 0 := by
  simpa [observerJetPrefix] using observerJetResidual_mass_zero q N hN

theorem observerJetResidual_history_terminal_pred
    (q : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    observerJetSecondHistory (observerJetResidual q N) (N - 1) = 0 := by
  let r := observerJetResidual q N
  have hmass : observerJetPrefix r N = 0 :=
    observerJetResidual_prefix_terminal q N hN
  have hdrift : (∑ k ∈ Finset.range (N + 1), (k : ℝ) * r k) = 0 :=
    observerJetResidual_drift_zero q N hN
  have hdrift' : (∑ k ∈ Finset.range (N + 1), r k * (k : ℝ)) = 0 := by
    calc
      (∑ k ∈ Finset.range (N + 1), r k * (k : ℝ)) =
          ∑ k ∈ Finset.range (N + 1), (k : ℝ) * r k := by
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = 0 := hdrift
  have habel := observerJetAbelSummation r (fun k => (k : ℝ)) N
  have hlen : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hhist : observerJetSecondHistory r (N - 1) =
      ∑ k ∈ Finset.range N, observerJetPrefix r k := by
    rw [observerJetSecondHistory, observerJetPrefix, hlen]
  rw [hdrift', hmass, zero_mul] at habel
  simp only [Nat.cast_add, Nat.cast_one] at habel
  have hsum : (∑ k ∈ Finset.range N, observerJetPrefix r k) = 0 := by
    have hweighted :
        (∑ k ∈ Finset.range N,
          observerJetPrefix r k * ((k : ℝ) - ((k + 1 : ℕ) : ℝ))) = 0 := by
      simpa using habel.symm
    calc
      (∑ k ∈ Finset.range N, observerJetPrefix r k) =
          -(∑ k ∈ Finset.range N,
            observerJetPrefix r k * ((k : ℝ) - ((k + 1 : ℕ) : ℝ))) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro k _
              push_cast
              ring
      _ = 0 := by rw [hweighted]; ring
  rw [hhist, hsum]

theorem observerJetResidual_history_terminal
    (q : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    observerJetSecondHistory (observerJetResidual q N) N = 0 := by
  have hpred := observerJetResidual_history_terminal_pred q N hN
  have hpref := observerJetResidual_prefix_terminal q N hN
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hpred' : observerJetSecondHistory (observerJetResidual q (j + 1)) j = 0 := by
    simpa using hpred
  have hpref' : observerJetPrefix (observerJetResidual q (j + 1)) (j + 1) = 0 := by
    simpa using hpref
  rw [observerJetSecondHistory_succ, hpred', hpref']
  ring

theorem observerJetResidual_reconstruct_zero
    (q : ℕ → ℝ) (N : ℕ) :
    q 0 = observerJetMass q N - observerJetDrift q N +
      observerJetSecondHistory (observerJetResidual q N) 0 := by
  simp [observerJetSecondHistory, observerJetPrefix, observerJetResidual,
    observerJetAffinePart]

theorem observerJetResidual_reconstruct_one
    (q : ℕ → ℝ) (N : ℕ) :
    q 1 = observerJetDrift q N +
      observerJetSecondHistory (observerJetResidual q N) 1 -
        2 * observerJetSecondHistory (observerJetResidual q N) 0 := by
  rw [observerJetSecondHistory_succ]
  simp [observerJetPrefix_succ, observerJetResidual, observerJetAffinePart]
  ring

theorem observerJetResidual_reconstruct_succ_succ
    (q : ℕ → ℝ) (N j : ℕ) :
    q (j + 2) = observerJetSecondHistory (observerJetResidual q N) (j + 2) -
        2 * observerJetSecondHistory (observerJetResidual q N) (j + 1) +
          observerJetSecondHistory (observerJetResidual q N) j := by
  let r := observerJetResidual q N
  have hH1 := observerJetSecondHistory_succ r j
  have hH2 := observerJetSecondHistory_succ r (j + 1)
  have hP := observerJetPrefix_succ r (j + 1)
  have hsecond : observerJetSecondHistory r (j + 2) -
        2 * observerJetSecondHistory r (j + 1) + observerJetSecondHistory r j =
      r (j + 2) := by
    rw [show j + 2 = (j + 1) + 1 by omega, hH2, hH1, hP]
    ring
  rw [hsecond]
  simp [r, observerJetResidual, observerJetAffinePart]

theorem observerJetGreenIdentity
    (q rate : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.range (N + 1), q k * rate k) =
      observerJetMass q N * rate 0 +
        observerJetDrift q N * (rate 1 - rate 0) +
          ∑ j ∈ Finset.range (N - 1),
            observerJetSecondHistory (observerJetResidual q N) j *
              observerJetCurvature rate j := by
  let r := observerJetResidual q N
  have hq : ∀ k, q k = observerJetAffinePart q N k + r k := by
    intro k
    simp [r, observerJetResidual]
  simp_rw [hq, add_mul, Finset.sum_add_distrib]
  have haff : (∑ k ∈ Finset.range (N + 1),
      observerJetAffinePart q N k * rate k) =
      observerJetMass q N * rate 0 +
        observerJetDrift q N * (rate 1 - rate 0) := by
    have hN0 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
    simp_rw [observerJetAffinePart, add_mul]
    rw [Finset.sum_add_distrib]
    simp [hN0]
    ring
  rw [haff]
  congr 1
  have hmass : observerJetPrefix r N = 0 :=
    observerJetResidual_prefix_terminal q N hN
  have hfirst := observerJetAbelSummation r rate N
  rw [hmass, zero_mul, zero_add] at hfirst
  rw [hfirst]
  let d : ℕ → ℝ := fun k => rate k - rate (k + 1)
  have hpred : observerJetSecondHistory r (N - 1) = 0 :=
    observerJetResidual_history_terminal_pred q N hN
  have hsecond := observerJetAbelSummation (observerJetPrefix r) d (N - 1)
  have hpred' : observerJetPrefix (observerJetPrefix r) (N - 1) = 0 := by
    simpa only [observerJetSecondHistory] using hpred
  have hlen : N - 1 + 1 = N := Nat.sub_add_cancel hN
  rw [hlen] at hsecond
  change (∑ n ∈ Finset.range N, observerJetPrefix r n * d n) = _ at hsecond
  rw [hpred', zero_mul, zero_add] at hsecond
  rw [hsecond]
  apply Finset.sum_congr rfl
  intro j _
  change observerJetSecondHistory r j * (d j - d (j + 1)) =
    observerJetSecondHistory r j * observerJetCurvature rate j
  unfold d observerJetCurvature
  ring

def observerJetSqrtGap (x : ℝ) : ℝ := Real.sqrt (x + 1) - Real.sqrt x

def observerJetClockReal (x : ℝ) : ℝ := x * (x + 1) * observerJetSqrtGap x

def observerJetSqrtGapDeriv (x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt (x + 1)) - 1 / (2 * Real.sqrt x)

def observerJetSqrtGapSecondDeriv (x : ℝ) : ℝ :=
  (1 / (x * Real.sqrt x) - 1 / ((x + 1) * Real.sqrt (x + 1))) / 4

def observerJetClockRealDeriv (x : ℝ) : ℝ :=
  (2 * x + 1) * observerJetSqrtGap x + x * (x + 1) * observerJetSqrtGapDeriv x

def observerJetClockRealSecondDeriv (x : ℝ) : ℝ :=
  2 * observerJetSqrtGap x + 2 * (2 * x + 1) * observerJetSqrtGapDeriv x +
    x * (x + 1) * observerJetSqrtGapSecondDeriv x

theorem hasDerivAt_observerJetSqrtGap
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt observerJetSqrtGap (observerJetSqrtGapDeriv x) x := by
  unfold observerJetSqrtGap observerJetSqrtGapDeriv
  have hshift : HasDerivAt (fun y : ℝ => y + 1) 1 x :=
    (hasDerivAt_id x).add_const 1
  have h := ((Real.hasDerivAt_sqrt (by linarith : x + 1 ≠ 0)).comp x hshift).sub
    (Real.hasDerivAt_sqrt hx.ne')
  apply (h.congr_deriv (by ring)).congr_of_eventuallyEq
  filter_upwards with y
  simp only [Function.comp_def, Pi.sub_apply]

theorem hasDerivAt_observerJetSqrtGapDeriv
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt observerJetSqrtGapDeriv (observerJetSqrtGapSecondDeriv x) x := by
  unfold observerJetSqrtGapDeriv observerJetSqrtGapSecondDeriv
  have hxp : x + 1 ≠ 0 := by linarith
  have hx0 : x ≠ 0 := hx.ne'
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hsxp : Real.sqrt (x + 1) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hsqx : Real.sqrt x ^ (2 : ℕ) = x := Real.sq_sqrt hx.le
  have hsqxp : Real.sqrt (x + 1) ^ (2 : ℕ) = x + 1 := Real.sq_sqrt (by linarith)
  have hshift : HasDerivAt (fun y : ℝ => y + 1) 1 x :=
    (hasDerivAt_id x).add_const 1
  have hs1 : HasDerivAt (fun y : ℝ => Real.sqrt (y + 1))
      (1 / (2 * Real.sqrt (x + 1))) x := by
    simpa only [Function.comp_def, mul_one] using!
      ((Real.hasDerivAt_sqrt hxp).comp x hshift)
  have hs0 : HasDerivAt (fun y : ℝ => Real.sqrt y)
      (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hx0
  have hrecip1 : HasDerivAt (fun y : ℝ => 1 / (2 * Real.sqrt (y + 1)))
      (-1 / (4 * (x + 1) * Real.sqrt (x + 1))) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).div (hs1.const_mul 2) (by
      change 2 * Real.sqrt (x + 1) ≠ 0
      positivity)
    apply (h.congr_deriv (by
      simp only [zero_mul, one_mul, zero_sub]
      field_simp [hsxp, hxp]
      nlinarith)).congr_of_eventuallyEq
    filter_upwards with y
    simp only [Pi.div_apply]
  have hrecip0 : HasDerivAt (fun y : ℝ => 1 / (2 * Real.sqrt y))
      (-1 / (4 * x * Real.sqrt x)) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).div (hs0.const_mul 2) (by
      change 2 * Real.sqrt x ≠ 0
      positivity)
    apply (h.congr_deriv (by
      simp only [zero_mul, one_mul, zero_sub]
      field_simp [hsx, hx0]
      nlinarith)).congr_of_eventuallyEq
    filter_upwards with y
    simp only [Pi.div_apply]
  have h := hrecip1.sub hrecip0
  apply (h.congr_deriv (by
    field_simp [hsx, hsxp, hx0, hxp]
    ring)).congr_of_eventuallyEq
  filter_upwards with y
  simp only [Pi.sub_apply]

theorem hasDerivAt_observerJetClockReal
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt observerJetClockReal (observerJetClockRealDeriv x) x := by
  unfold observerJetClockReal observerJetClockRealDeriv
  have hpoly : HasDerivAt (fun y : ℝ => y * (y + 1)) (2 * x + 1) x := by
    have h := (hasDerivAt_id x).mul ((hasDerivAt_id x).add_const 1)
    apply (h.congr_deriv (by simp only [id_eq]; ring)).congr_of_eventuallyEq
    filter_upwards with y
    simp only [Pi.mul_apply, id_eq]
  have h := hpoly.mul (hasDerivAt_observerJetSqrtGap hx)
  apply (h.congr_deriv (by ring)).congr_of_eventuallyEq
  filter_upwards with y
  simp only [Pi.mul_apply]

theorem hasDerivAt_observerJetClockRealDeriv
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt observerJetClockRealDeriv (observerJetClockRealSecondDeriv x) x := by
  unfold observerJetClockRealDeriv observerJetClockRealSecondDeriv
  have hcoef : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 x := by
    have h := ((hasDerivAt_id x).const_mul 2).const_add 1
    apply (h.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards with y
    simp only [id_eq]
    ring
  have hpoly : HasDerivAt (fun y : ℝ => y * (y + 1)) (2 * x + 1) x := by
    have h := (hasDerivAt_id x).mul ((hasDerivAt_id x).add_const 1)
    apply (h.congr_deriv (by simp only [id_eq]; ring)).congr_of_eventuallyEq
    filter_upwards with y
    simp only [Pi.mul_apply, id_eq]
  have h := (hcoef.mul (hasDerivAt_observerJetSqrtGap hx)).add
    (hpoly.mul (hasDerivAt_observerJetSqrtGapDeriv hx))
  apply (h.congr_deriv (by ring)).congr_of_eventuallyEq
  filter_upwards with y
  simp only [Pi.add_apply, Pi.mul_apply]

theorem observerJetSqrtGap_mul_sum {x : ℝ} (hx : 0 ≤ x) :
    observerJetSqrtGap x * (Real.sqrt (x + 1) + Real.sqrt x) = 1 := by
  unfold observerJetSqrtGap
  have hx1 : 0 ≤ x + 1 := by linarith
  rw [mul_add, sub_mul]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hx1]

theorem observerJetSqrtGap_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < observerJetSqrtGap x := by
  unfold observerJetSqrtGap
  exact sub_pos.mpr (Real.sqrt_lt_sqrt hx (by linarith))

theorem observerJetSqrtGap_le {x : ℝ} (hx : 0 < x) :
    observerJetSqrtGap x ≤ 1 / (2 * Real.sqrt x) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsum : 2 * Real.sqrt x ≤ Real.sqrt (x + 1) + Real.sqrt x := by
    have := Real.sqrt_le_sqrt (by linarith : x ≤ x + 1)
    linarith
  have hgap := observerJetSqrtGap_mul_sum hx.le
  have hgap0 := (observerJetSqrtGap_pos hx.le).le
  rw [← hgap]
  calc
    observerJetSqrtGap x * (Real.sqrt (x + 1) + Real.sqrt x) /
          (2 * Real.sqrt x) = observerJetSqrtGap x *
          ((Real.sqrt (x + 1) + Real.sqrt x) / (2 * Real.sqrt x)) := by ring
    _ ≥ observerJetSqrtGap x * 1 := by
      gcongr
      apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt x)).2
      simpa using hsum
    _ = observerJetSqrtGap x := by ring

theorem observerJetSqrtGapDeriv_eq_neg {x : ℝ} (hx : 0 < x) :
    observerJetSqrtGapDeriv x =
      -observerJetSqrtGap x /
        (2 * Real.sqrt x * Real.sqrt (x + 1)) := by
  unfold observerJetSqrtGapDeriv observerJetSqrtGap
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hsx1 : Real.sqrt (x + 1) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  field_simp [hsx, hsx1]
  ring

theorem abs_observerJetSqrtGapDeriv_le {x : ℝ} (hx : 0 < x) :
    |observerJetSqrtGapDeriv x| ≤ 1 / (4 * x * Real.sqrt x) := by
  let a := Real.sqrt x
  let b := Real.sqrt (x + 1)
  have ha : 0 < a := Real.sqrt_pos.2 hx
  have hb : 0 < b := Real.sqrt_pos.2 (by linarith)
  have haa : a ^ (2 : ℕ) = x := Real.sq_sqrt hx.le
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hgap0 : 0 ≤ observerJetSqrtGap x := (observerJetSqrtGap_pos hx.le).le
  have hgap := observerJetSqrtGap_le hx
  rw [observerJetSqrtGapDeriv_eq_neg hx, abs_div, abs_neg,
    abs_of_nonneg hgap0, abs_of_pos (by positivity : 0 < 2 * a * b)]
  change observerJetSqrtGap x / (2 * a * b) ≤ 1 / (4 * x * a)
  apply (div_le_iff₀ (by positivity : 0 < 2 * a * b)).2
  calc
    observerJetSqrtGap x ≤ 1 / (2 * a) := by simpa [a] using hgap
    _ ≤ 1 / (4 * x * a) * (2 * a * b) := by
      field_simp [ha.ne', hx.ne']
      nlinarith

theorem observerJetSqrtGapSecondDeriv_split {x : ℝ} (hx : 0 < x) :
    observerJetSqrtGapSecondDeriv x =
      (1 / (x * (x + 1) * Real.sqrt x) +
        observerJetSqrtGap x /
          ((x + 1) * Real.sqrt x * Real.sqrt (x + 1))) / 4 := by
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hsx1 : Real.sqrt (x + 1) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hx0 : x ≠ 0 := hx.ne'
  have hx1 : x + 1 ≠ 0 := by linarith
  have hsquare : Real.sqrt x ^ (2 : ℕ) = x := Real.sq_sqrt hx.le
  have hsquare1 : Real.sqrt (x + 1) ^ (2 : ℕ) = x + 1 := Real.sq_sqrt (by linarith)
  unfold observerJetSqrtGapSecondDeriv observerJetSqrtGap
  field_simp [hx0, hx1, hsx, hsx1]
  nlinarith

theorem observerJetSqrtGapSecondDeriv_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ observerJetSqrtGapSecondDeriv x := by
  rw [observerJetSqrtGapSecondDeriv_split hx]
  have hgap0 : 0 ≤ observerJetSqrtGap x := (observerJetSqrtGap_pos hx.le).le
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsxp : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.2 (by linarith)
  exact div_nonneg (add_nonneg (by positivity) (div_nonneg hgap0 (by positivity))) (by norm_num)

theorem observerJetSqrtGapSecondDeriv_le {x : ℝ} (hx : 0 < x) :
    observerJetSqrtGapSecondDeriv x ≤
      3 / (8 * x ^ (2 : ℕ) * Real.sqrt x) := by
  let a := Real.sqrt x
  let b := Real.sqrt (x + 1)
  have ha : 0 < a := Real.sqrt_pos.2 hx
  have hb : 0 < b := Real.sqrt_pos.2 (by linarith)
  have haa : a ^ (2 : ℕ) = x := Real.sq_sqrt hx.le
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hgap0 : 0 ≤ observerJetSqrtGap x := (observerJetSqrtGap_pos hx.le).le
  have hgap := observerJetSqrtGap_le hx
  have h1 : 1 / (x * (x + 1) * a) ≤ 1 / (x ^ (2 : ℕ) * a) := by
    gcongr
    nlinarith
  have habmul : x ≤ a * b := by
    nlinarith [mul_le_mul_of_nonneg_left hab ha.le]
  have hden : x ^ (2 : ℕ) ≤ (x + 1) * a * b := by
    nlinarith [mul_le_mul_of_nonneg_left habmul (show 0 ≤ x by positivity)]
  have h2 : observerJetSqrtGap x / ((x + 1) * a * b) ≤
      1 / (2 * x ^ (2 : ℕ) * a) := by
    apply (div_le_iff₀ (by positivity : 0 < (x + 1) * a * b)).2
    calc
      observerJetSqrtGap x ≤ 1 / (2 * a) := by simpa [a] using hgap
      _ ≤ 1 / (2 * x ^ (2 : ℕ) * a) * ((x + 1) * a * b) := by
        field_simp [ha.ne', hx.ne']
        nlinarith
  rw [observerJetSqrtGapSecondDeriv_split hx]
  change (1 / (x * (x + 1) * a) +
      observerJetSqrtGap x / ((x + 1) * a * b)) / 4 ≤
    3 / (8 * x ^ (2 : ℕ) * a)
  have hsum := add_le_add h1 h2
  have hpos : 0 < x ^ (2 : ℕ) * a := by positivity
  calc
    (1 / (x * (x + 1) * a) +
        observerJetSqrtGap x / ((x + 1) * a * b)) / 4 ≤
        (1 / (x ^ (2 : ℕ) * a) + 1 / (2 * x ^ (2 : ℕ) * a)) / 4 :=
      div_le_div_of_nonneg_right hsum (by norm_num)
    _ = 3 / (8 * x ^ (2 : ℕ) * a) := by field_simp; ring

theorem abs_observerJetClockRealSecondDeriv_le
    {x : ℝ} (hx : 1 ≤ x) :
    |observerJetClockRealSecondDeriv x| ≤ 13 / (4 * Real.sqrt x) := by
  let a := Real.sqrt x
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have ha : 0 < a := Real.sqrt_pos.2 hx0
  have hgap0 : 0 ≤ observerJetSqrtGap x := (observerJetSqrtGap_pos hx0.le).le
  have hgap := observerJetSqrtGap_le hx0
  have hderiv := abs_observerJetSqrtGapDeriv_le hx0
  have hsecond0 := observerJetSqrtGapSecondDeriv_nonneg hx0
  have hsecond := observerJetSqrtGapSecondDeriv_le hx0
  have hxplus : x + 1 ≤ 2 * x := by linarith
  have hcoef : 2 * x + 1 ≤ 3 * x := by linarith
  have hterm0 : |2 * observerJetSqrtGap x| ≤ 1 / a := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hgap0)]
    change 2 * observerJetSqrtGap x ≤ 1 / a
    calc
      2 * observerJetSqrtGap x ≤ 2 * (1 / (2 * a)) :=
        mul_le_mul_of_nonneg_left (by simpa [a] using hgap) (by norm_num)
      _ = 1 / a := by field_simp
  have hterm1 : |2 * (2 * x + 1) * observerJetSqrtGapDeriv x| ≤
      3 / (2 * a) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
      abs_of_nonneg (by linarith : 0 ≤ 2 * x + 1)]
    calc
      2 * (2 * x + 1) * |observerJetSqrtGapDeriv x| ≤
          2 * (3 * x) * (1 / (4 * x * a)) := by gcongr
      _ = 3 / (2 * a) := by field_simp; ring
  have hterm2 : |x * (x + 1) * observerJetSqrtGapSecondDeriv x| ≤
      3 / (4 * a) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hx0.le,
      abs_of_nonneg (by linarith : 0 ≤ x + 1), abs_of_nonneg hsecond0]
    calc
      x * (x + 1) * observerJetSqrtGapSecondDeriv x ≤
          x * (2 * x) * (3 / (8 * x ^ (2 : ℕ) * a)) := by gcongr
      _ = 3 / (4 * a) := by field_simp; ring
  unfold observerJetClockRealSecondDeriv
  calc
    |2 * observerJetSqrtGap x + 2 * (2 * x + 1) * observerJetSqrtGapDeriv x +
        x * (x + 1) * observerJetSqrtGapSecondDeriv x| ≤
        |2 * observerJetSqrtGap x| +
          |2 * (2 * x + 1) * observerJetSqrtGapDeriv x| +
            |x * (x + 1) * observerJetSqrtGapSecondDeriv x| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ 1 / a + 3 / (2 * a) + 3 / (4 * a) := by gcongr
    _ = 13 / (4 * Real.sqrt x) := by change _ = 13 / (4 * a); field_simp; ring

theorem observerJetClockReal_secondDifference_bound
    {x : ℝ} (hx : 1 ≤ x) :
    |observerJetClockReal (x + 2) - 2 * observerJetClockReal (x + 1) +
        observerJetClockReal x| ≤ 13 / (4 * Real.sqrt x) := by
  let g : ℝ → ℝ := fun y => observerJetClockReal (y + 1) - observerJetClockReal y
  let g' : ℝ → ℝ := fun y =>
    observerJetClockRealDeriv (y + 1) - observerJetClockRealDeriv y
  have hgder : ∀ y ∈ Set.Ioo x (x + 1), HasDerivAt g (g' y) y := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one (hx.trans hy.1.le)
    have hshift : HasDerivAt (fun z : ℝ => z + 1) 1 y :=
      (hasDerivAt_id y).add_const 1
    have h := ((hasDerivAt_observerJetClockReal
      (by linarith : 0 < y + 1)).comp y hshift).sub
        (hasDerivAt_observerJetClockReal hy0)
    apply (h.congr_deriv (by simp only [g', mul_one])).congr_of_eventuallyEq
    filter_upwards with z
    simp only [g, Function.comp_def, Pi.sub_apply]
  have hgcont : ContinuousOn g (Set.Icc x (x + 1)) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one (hx.trans hy.1)
    have hshift : HasDerivAt (fun z : ℝ => z + 1) 1 y :=
      (hasDerivAt_id y).add_const 1
    have h := ((hasDerivAt_observerJetClockReal
      (by linarith : 0 < y + 1)).comp y hshift).sub
        (hasDerivAt_observerJetClockReal hy0)
    have hgAt : HasDerivAt g
        (observerJetClockRealDeriv (y + 1) - observerJetClockRealDeriv y) y := by
      apply (h.congr_deriv (by simp only [mul_one])).congr_of_eventuallyEq
      filter_upwards with z
      simp only [g, Function.comp_def, Pi.sub_apply]
    exact hgAt.continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcSlope⟩ := exists_hasDerivAt_eq_slope g g'
    (by linarith : x < x + 1) hgcont hgder
  have hc0 : 0 < c := lt_trans (lt_of_lt_of_le zero_lt_one hx) hc.1
  have hf'der : ∀ y ∈ Set.Ioo c (c + 1),
      HasDerivAt observerJetClockRealDeriv (observerJetClockRealSecondDeriv y) y := by
    intro y hy
    exact hasDerivAt_observerJetClockRealDeriv (lt_trans hc0 hy.1)
  have hf'cont : ContinuousOn observerJetClockRealDeriv (Set.Icc c (c + 1)) := by
    intro y hy
    exact (hasDerivAt_observerJetClockRealDeriv
      (lt_of_lt_of_le hc0 hy.1)).continuousAt.continuousWithinAt
  obtain ⟨d, hd, hdSlope⟩ := exists_hasDerivAt_eq_slope
    observerJetClockRealDeriv observerJetClockRealSecondDeriv
    (by linarith : c < c + 1) hf'cont hf'der
  have heq : observerJetClockReal (x + 2) - 2 * observerJetClockReal (x + 1) +
      observerJetClockReal x = observerJetClockRealSecondDeriv d := by
    dsimp [g, g'] at hcSlope
    simp only [add_sub_cancel_left, div_one] at hcSlope hdSlope
    have hcEq : observerJetClockReal (x + 2) - 2 * observerJetClockReal (x + 1) +
        observerJetClockReal x =
          observerJetClockRealDeriv (c + 1) - observerJetClockRealDeriv c := by
      rw [hcSlope]
      ring
    rw [hcEq, hdSlope]
  rw [heq]
  have hdx : x ≤ d := le_trans hc.1.le hd.1.le
  have hdbound := abs_observerJetClockRealSecondDeriv_le
    (x := d) (hx.trans hdx)
  calc
    |observerJetClockRealSecondDeriv d| ≤ 13 / (4 * Real.sqrt d) := hdbound
    _ ≤ 13 / (4 * Real.sqrt x) := by
      gcongr

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

theorem completedRieszHarmonicClockRatio_eq_observerJetClockReal (k : ℕ) :
    completedRieszHarmonicClockRatio k = observerJetClockReal (k + 1) := by
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hgap : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) =
      1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    field_simp [h1.ne', h2.ne']
    ring
  rw [completedRieszHarmonicClockRatio, hgap]
  unfold observerJetClockReal observerJetSqrtGap
  push_cast
  field_simp [h1.ne', h2.ne']
  have hk : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
  rw [hk]

/-- The harmonic--Riesz observer has bounded curvature at the exact second-formation rate. -/
theorem abs_observerJetCurvature_completedRieszHarmonicClockRatio_le (j : ℕ) :
    |observerJetCurvature completedRieszHarmonicClockRatio j| ≤
      13 / (4 * Real.sqrt (j + 1 : ℕ)) := by
  rw [observerJetCurvature, completedRieszHarmonicClockRatio_eq_observerJetClockReal,
    completedRieszHarmonicClockRatio_eq_observerJetClockReal,
    completedRieszHarmonicClockRatio_eq_observerJetClockReal]
  push_cast
  have hbound := observerJetClockReal_secondDifference_bound
    (x := (j : ℝ) + 1) (by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
  convert hbound using 1
  all_goals ring

def completedSourceObserverJetMass (M : ℕ) : ℝ :=
  observerJetMass completedPrimePolarGammaHarmonicCharge (M - 2)

def completedSourceObserverJetDrift (M : ℕ) : ℝ :=
  observerJetDrift completedPrimePolarGammaHarmonicCharge (M - 2)

def completedSourceObserverJetHistory (M j : ℕ) : ℝ :=
  observerJetSecondHistory
    (observerJetResidual completedPrimePolarGammaHarmonicCharge (M - 2)) j

def completedSourceObserverJetWeightedAction (M : ℕ) : ℝ :=
  |completedSourceObserverJetDrift M| +
    ∑ j ∈ Finset.range (M - 3),
      |completedSourceObserverJetHistory M j| / Real.sqrt (j + 1 : ℕ)

/-- Exact completed-source value--slope--curvature landing. -/
theorem mobiusDivisorSquareRootAbelMoment_eq_completedSourceObserverJet
    {M : ℕ} (hM : 3 ≤ M) :
    mobiusDivisorSquareRootAbelMoment M =
      completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0 +
        completedSourceObserverJetDrift M *
          (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0) +
        ∑ j ∈ Finset.range (M - 3),
          completedSourceObserverJetHistory M j *
            observerJetCurvature completedRieszHarmonicClockRatio j := by
  rw [mobiusDivisorSquareRootAbelMoment_eq_harmonicCharge_clock (by omega : 1 ≤ M)]
  have hN : 1 ≤ M - 2 := by omega
  have hlen : M - 2 + 1 = M - 1 := by omega
  have hhist : M - 2 - 1 = M - 3 := by omega
  have hgreen := observerJetGreenIdentity completedPrimePolarGammaHarmonicCharge
    completedRieszHarmonicClockRatio (M - 2) hN
  rw [hlen, hhist] at hgreen
  simpa [completedSourceObserverJetMass, completedSourceObserverJetDrift,
    completedSourceObserverJetHistory] using hgreen

/-- Curvature-weighted estimate for the literal completed source. -/
theorem abs_mobiusDivisorSquareRootAbelMoment_le_completedSourceObserverJet
    {M : ℕ} (hM : 3 ≤ M) :
    |mobiusDivisorSquareRootAbelMoment M| ≤
      |completedRieszHarmonicClockRatio 0| * |completedSourceObserverJetMass M| +
        |completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0| *
          |completedSourceObserverJetDrift M| +
        (13 / 4) *
          (∑ j ∈ Finset.range (M - 3),
            |completedSourceObserverJetHistory M j| / Real.sqrt (j + 1 : ℕ)) := by
  rw [mobiusDivisorSquareRootAbelMoment_eq_completedSourceObserverJet hM]
  calc
    |completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0 +
          completedSourceObserverJetDrift M *
            (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0) +
          ∑ j ∈ Finset.range (M - 3), completedSourceObserverJetHistory M j *
            observerJetCurvature completedRieszHarmonicClockRatio j| ≤
        |completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0| +
          |completedSourceObserverJetDrift M *
            (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0)| +
          |∑ j ∈ Finset.range (M - 3), completedSourceObserverJetHistory M j *
            observerJetCurvature completedRieszHarmonicClockRatio j| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ |completedRieszHarmonicClockRatio 0| * |completedSourceObserverJetMass M| +
        |completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0| *
          |completedSourceObserverJetDrift M| +
        ∑ j ∈ Finset.range (M - 3),
          |completedSourceObserverJetHistory M j *
            observerJetCurvature completedRieszHarmonicClockRatio j| := by
      rw [abs_mul, abs_mul, mul_comm |completedSourceObserverJetMass M|,
        mul_comm |completedSourceObserverJetDrift M|]
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ |completedRieszHarmonicClockRatio 0| * |completedSourceObserverJetMass M| +
        |completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0| *
          |completedSourceObserverJetDrift M| +
        (13 / 4) *
          (∑ j ∈ Finset.range (M - 3),
            |completedSourceObserverJetHistory M j| / Real.sqrt (j + 1 : ℕ)) := by
      apply add_le_add_right
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      have hc := abs_observerJetCurvature_completedRieszHarmonicClockRatio_le j
      have hs : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.2 (by positivity)
      calc
        |completedSourceObserverJetHistory M j| *
            |observerJetCurvature completedRieszHarmonicClockRatio j| ≤
            |completedSourceObserverJetHistory M j| *
              (13 / (4 * Real.sqrt (j + 1 : ℕ))) :=
          mul_le_mul_of_nonneg_left hc (abs_nonneg _)
        _ = (13 / 4) *
            (|completedSourceObserverJetHistory M j| /
              Real.sqrt (j + 1 : ℕ)) := by field_simp

theorem abs_completedSourceObserverJetMass_le (M : ℕ) :
    |completedSourceObserverJetMass M| ≤
      ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k| := by
  have hs : Summable (fun k : ℕ => |completedPrimePolarGammaHarmonicCharge k|) :=
    summable_completedPrimePolarGammaHarmonicCharge.abs
  unfold completedSourceObserverJetMass observerJetMass
  calc
    |∑ k ∈ Finset.range (M - 2 + 1), completedPrimePolarGammaHarmonicCharge k| ≤
        ∑ k ∈ Finset.range (M - 2 + 1),
          |completedPrimePolarGammaHarmonicCharge k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k| :=
      hs.sum_le_tsum (Finset.range (M - 2 + 1)) (fun _ _ => abs_nonneg _)

/-- Open producer isolated by the observer-jet theorem: linear growth of drift plus weighted
second-boundary history for the literal completed source. -/
def CompletedSourceObserverJetLinearActionBounded : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 3 ≤ M →
    completedSourceObserverJetWeightedAction M ≤ C * M

/-- The source-native second-formation action estimate closes RH. -/
theorem riemannHypothesis_of_completedSourceObserverJetLinearActionBounded
    (hsource : CompletedSourceObserverJetLinearActionBounded) :
    RiemannHypothesis := by
  rcases hsource with ⟨C, hC, hsource⟩
  let massBudget : ℝ := ∑' k : ℕ, |completedPrimePolarGammaHarmonicCharge k|
  let driftClock : ℝ :=
    |completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0|
  let curvatureClock : ℝ := 13 / 4
  let actionClock : ℝ := max driftClock curvatureClock
  let affineBudget : ℝ := |completedRieszHarmonicClockRatio 0| * massBudget
  let globalBudget : ℝ := max
    |mobiusDivisorSquareRootAbelMoment 2 / 2|
    (affineBudget + actionClock * C)
  have hmass : 0 ≤ massBudget := tsum_nonneg (fun _ => abs_nonneg _)
  have hdrift : 0 ≤ driftClock := abs_nonneg _
  have hcurv : 0 ≤ curvatureClock := by norm_num [curvatureClock]
  have haction : 0 ≤ actionClock := le_trans hdrift (le_max_left _ _)
  have haffine : 0 ≤ affineBudget := mul_nonneg (abs_nonneg _) hmass
  have hglobal : 0 ≤ globalBudget := le_trans (abs_nonneg _) (le_max_left _ _)
  have hbounded : MobiusDivisorSquareRootAbelBounded := by
    refine ⟨globalBudget, hglobal, ?_⟩
    intro M hM
    by_cases hM2 : M = 2
    · subst M
      exact le_max_left _ _
    · have hM3 : 3 ≤ M := by omega
      have hmain := abs_mobiusDivisorSquareRootAbelMoment_le_completedSourceObserverJet hM3
      have hmassM := abs_completedSourceObserverJetMass_le M
      have hclockDrift : driftClock ≤ actionClock := le_max_left _ _
      have hclockCurv : curvatureClock ≤ actionClock := le_max_right _ _
      have hactionM := hsource M hM3
      have hsplit :
          driftClock * |completedSourceObserverJetDrift M| +
              curvatureClock *
                (∑ j ∈ Finset.range (M - 3),
                  |completedSourceObserverJetHistory M j| /
                    Real.sqrt (j + 1 : ℕ)) ≤
            actionClock * completedSourceObserverJetWeightedAction M := by
        let historyAction : ℝ := ∑ j ∈ Finset.range (M - 3),
          |completedSourceObserverJetHistory M j| / Real.sqrt (j + 1 : ℕ)
        have hhistory : 0 ≤ historyAction := by
          dsimp only [historyAction]
          exact Finset.sum_nonneg fun j _ =>
            div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
        have hdriftTerm := mul_le_mul_of_nonneg_right hclockDrift
          (abs_nonneg (completedSourceObserverJetDrift M))
        have hcurvTerm := mul_le_mul_of_nonneg_right hclockCurv hhistory
        change driftClock * |completedSourceObserverJetDrift M| +
            curvatureClock * historyAction ≤
          actionClock * (|completedSourceObserverJetDrift M| + historyAction)
        nlinarith
      have hraw : |mobiusDivisorSquareRootAbelMoment M| ≤
          affineBudget + actionClock * (C * M) := by
        change |mobiusDivisorSquareRootAbelMoment M| ≤
          |completedRieszHarmonicClockRatio 0| * massBudget +
            actionClock * (C * (M : ℝ))
        calc
          |mobiusDivisorSquareRootAbelMoment M| ≤
              |completedRieszHarmonicClockRatio 0| *
                  |completedSourceObserverJetMass M| +
                driftClock * |completedSourceObserverJetDrift M| +
                curvatureClock *
                  (∑ j ∈ Finset.range (M - 3),
                    |completedSourceObserverJetHistory M j| /
                      Real.sqrt (j + 1 : ℕ)) := hmain
          _ = |completedRieszHarmonicClockRatio 0| *
                  |completedSourceObserverJetMass M| +
                (driftClock * |completedSourceObserverJetDrift M| +
                  curvatureClock *
                    (∑ j ∈ Finset.range (M - 3),
                      |completedSourceObserverJetHistory M j| /
                        Real.sqrt (j + 1 : ℕ))) := by ring
          _ ≤ |completedRieszHarmonicClockRatio 0| * massBudget +
                actionClock * completedSourceObserverJetWeightedAction M := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hmassM (abs_nonneg _)) hsplit
          _ ≤ |completedRieszHarmonicClockRatio 0| * massBudget +
                actionClock * (C * (M : ℝ)) := by
              exact add_le_add_right
                (mul_le_mul_of_nonneg_left hactionM haction) _
      have hMR : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
      have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hMR
      rw [abs_div, abs_of_pos hMpos]
      calc
        |mobiusDivisorSquareRootAbelMoment M| / (M : ℝ) ≤
            (affineBudget + actionClock * (C * (M : ℝ))) / (M : ℝ) :=
          div_le_div_of_nonneg_right hraw hMpos.le
        _ = affineBudget / (M : ℝ) + actionClock * C := by
          field_simp
        _ ≤ affineBudget + actionClock * C := by
          gcongr
          exact div_le_self haffine hMR
        _ ≤ globalBudget := le_max_right _ _
  exact riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded.mpr hbounded

end

end GaloisForLFunctions.RHTower
