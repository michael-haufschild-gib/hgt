import Mathlib

/-!
# Grönwall comparison for perturbed linear second-order equations

A solution of `u'' = P_c u + Q_c u'` on a compact window is compared with a solution of the limiting
equation `v'' = P v` carrying the same initial phase vector.  Passing to the phase pair `(u, u')`
turns both into first-order systems whose vector fields differ by

`(0, (P_c − P) u + Q_c u')` ,

so Grönwall's inequality bounds the phase distance by the size of that difference times an
exponential factor depending only on the limiting field.  Since the equation is linear, the zero
solution is a trajectory, and the same inequality also supplies the a priori bound on `(u, u')`
needed to make the difference estimate effective.

Nothing here is asymptotic: both statements are explicit inequalities on `[a, b]`.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- The phase pair of a function and its derivative. -/
noncomputable def phasePair (u u' : ℝ → ℝ) (x : ℝ) : ℝ × ℝ := (u x, u' x)

theorem norm_phasePair (u u' : ℝ → ℝ) (x : ℝ) :
    ‖phasePair u u' x‖ = max |u x| |u' x| := by
  simp [phasePair, Prod.norm_def, Real.norm_eq_abs]

theorem hasDerivAt_phasePair {u u' u'' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x) (x : ℝ) :
    HasDerivAt (phasePair u u') (phasePair u' u'' x) x := (hu x).prodMk (hu' x)

/-- **A priori phase bound.**  A solution of `u'' = P u + Q u'` on `[a,b]` has phase pair growing at
most exponentially, with rate the Lipschitz constant `1 ⊔ (Lp + Lq)` of the linear field. -/
theorem phasePair_norm_le
    {u u' u'' P Q : ℝ → ℝ} {a b Lp Lq δ : ℝ} (_hab : a ≤ b)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (heq : ∀ x ∈ Icc a b, u'' x = P x * u x + Q x * u' x)
    (hP : ∀ x ∈ Icc a b, |P x| ≤ Lp) (hQ : ∀ x ∈ Icc a b, |Q x| ≤ Lq)
    (h0 : max |u a| |u' a| ≤ δ) :
    ∀ x ∈ Icc a b, max |u x| |u' x| ≤ δ * Real.exp (max 1 (Lp + Lq) * (x - a)) := by
  set L : ℝ := max 1 (Lp + Lq) with hL
  have hL1 : (1 : ℝ) ≤ L := le_max_left _ _
  have hLpq : Lp + Lq ≤ L := le_max_right _ _
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hcont : ContinuousOn (phasePair u u') (Icc a b) := by
    refine Continuous.continuousOn ?_
    exact (continuous_iff_continuousAt.2 fun x => (hu x).continuousAt).prodMk
      (continuous_iff_continuousAt.2 fun x => (hu' x).continuousAt)
  have hderiv : ∀ x ∈ Ico a b,
      HasDerivWithinAt (phasePair u u') (phasePair u' u'' x) (Ici x) x := by
    intro x _
    exact (hasDerivAt_phasePair hu hu' x).hasDerivWithinAt
  have hstart : ‖phasePair u u' a‖ ≤ δ := by rw [norm_phasePair]; exact h0
  have hbound : ∀ x ∈ Ico a b, ‖phasePair u' u'' x‖ ≤ L * ‖phasePair u u' x‖ + 0 := by
    intro x hx
    have hxm : x ∈ Icc a b := ⟨hx.1, hx.2.le⟩
    have hPn : (0 : ℝ) ≤ Lp := le_trans (abs_nonneg _) (hP x hxm)
    have hQn : (0 : ℝ) ≤ Lq := le_trans (abs_nonneg _) (hQ x hxm)
    rw [norm_phasePair, norm_phasePair, add_zero]
    have h1 : |u x| ≤ max |u x| |u' x| := le_max_left _ _
    have h2 : |u' x| ≤ max |u x| |u' x| := le_max_right _ _
    have hu2 : |u'' x| ≤ L * max |u x| |u' x| := by
      rw [heq x hxm]
      have := abs_add_le (P x * u x) (Q x * u' x)
      have hA : |P x * u x| ≤ Lp * max |u x| |u' x| := by
        rw [abs_mul]
        exact mul_le_mul (hP x hxm) h1 (abs_nonneg _) hPn
      have hB : |Q x * u' x| ≤ Lq * max |u x| |u' x| := by
        rw [abs_mul]
        exact mul_le_mul (hQ x hxm) h2 (abs_nonneg _) hQn
      have hmnn : (0 : ℝ) ≤ max |u x| |u' x| := le_trans (abs_nonneg _) h1
      nlinarith
    have hu1 : |u' x| ≤ L * max |u x| |u' x| := by
      have hmnn : (0 : ℝ) ≤ max |u x| |u' x| := le_trans (abs_nonneg _) h1
      nlinarith
    exact max_le hu1 hu2
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv hstart hbound
  intro x hx
  have := hmain x hx
  rwa [gronwallBound_ε0, norm_phasePair] at this

/-- **Comparison estimate.**  Solutions of `u'' = P_c u + Q_c u'` and `v'' = P v` with the same
initial phase vector separate by at most `((εp + εq) B / L)(exp (L (x−a)) − 1)`, where `εp`, `εq`
bound the coefficient perturbation, `B` bounds the phase pair of `u`, and `L = 1 ⊔ Lp`. -/
theorem phasePair_dist_le
    {u u' u'' v v' v'' P Pc Qc : ℝ → ℝ} {a b Lp εp εq B : ℝ} (hab : a ≤ b)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' (v'' x) x)
    (hequ : ∀ x ∈ Icc a b, u'' x = Pc x * u x + Qc x * u' x)
    (heqv : ∀ x ∈ Icc a b, v'' x = P x * v x)
    (hP : ∀ x ∈ Icc a b, |P x| ≤ Lp)
    (hεp : ∀ x ∈ Icc a b, |Pc x - P x| ≤ εp) (hεq : ∀ x ∈ Icc a b, |Qc x| ≤ εq)
    (hB : ∀ x ∈ Icc a b, max |u x| |u' x| ≤ B)
    (h0 : u a = v a) (h0' : u' a = v' a) :
    ∀ x ∈ Icc a b, max |u x - v x| |u' x - v' x|
      ≤ ((εp + εq) * B / max 1 Lp) * (Real.exp (max 1 Lp * (x - a)) - 1) := by
  set L : ℝ := max 1 Lp with hL
  have hL1 : (1 : ℝ) ≤ L := le_max_left _ _
  have hLp : Lp ≤ L := le_max_right _ _
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hLne : L ≠ 0 := ne_of_gt hLpos
  set w : ℝ → ℝ × ℝ := fun x => (u x - v x, u' x - v' x) with hw
  set w' : ℝ → ℝ × ℝ := fun x => (u' x - v' x, u'' x - v'' x) with hw'
  have hnw : ∀ x, ‖w x‖ = max |u x - v x| |u' x - v' x| := by
    intro x; simp [hw, Prod.norm_def, Real.norm_eq_abs]
  have hnw' : ∀ x, ‖w' x‖ = max |u' x - v' x| |u'' x - v'' x| := by
    intro x; simp [hw', Prod.norm_def, Real.norm_eq_abs]
  have hcont : ContinuousOn w (Icc a b) := by
    refine Continuous.continuousOn ?_
    exact ((continuous_iff_continuousAt.2 fun x => (hu x).continuousAt).sub
      (continuous_iff_continuousAt.2 fun x => (hv x).continuousAt)).prodMk
      ((continuous_iff_continuousAt.2 fun x => (hu' x).continuousAt).sub
        (continuous_iff_continuousAt.2 fun x => (hv' x).continuousAt))
  have hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt w (w' x) (Ici x) x := by
    intro x _
    exact (((hu x).sub (hv x)).prodMk ((hu' x).sub (hv' x))).hasDerivWithinAt
  have hstart : ‖w a‖ ≤ 0 := by
    rw [hnw, h0, h0']
    simp
  have hεpn : (0 : ℝ) ≤ εp := le_trans (abs_nonneg _) (hεp a ⟨le_rfl, hab⟩)
  have hεqn : (0 : ℝ) ≤ εq := le_trans (abs_nonneg _) (hεq a ⟨le_rfl, hab⟩)
  have hBn : (0 : ℝ) ≤ B := le_trans (le_trans (abs_nonneg _) (le_max_left _ _))
    (hB a ⟨le_rfl, hab⟩)
  have hbound : ∀ x ∈ Ico a b, ‖w' x‖ ≤ L * ‖w x‖ + (εp + εq) * B := by
    intro x hx
    have hxm : x ∈ Icc a b := ⟨hx.1, hx.2.le⟩
    have hPn : (0 : ℝ) ≤ Lp := le_trans (abs_nonneg _) (hP x hxm)
    rw [hnw, hnw']
    have h1 : |u x - v x| ≤ max |u x - v x| |u' x - v' x| := le_max_left _ _
    have h2 : |u' x - v' x| ≤ max |u x - v x| |u' x - v' x| := le_max_right _ _
    have hmnn : (0 : ℝ) ≤ max |u x - v x| |u' x - v' x| := le_trans (abs_nonneg _) h1
    have hux : |u x| ≤ B := le_trans (le_max_left _ _) (hB x hxm)
    have hu'x : |u' x| ≤ B := le_trans (le_max_right _ _) (hB x hxm)
    have hdec : u'' x - v'' x
        = P x * (u x - v x) + ((Pc x - P x) * u x + Qc x * u' x) := by
      rw [hequ x hxm, heqv x hxm]; ring
    have hA : |P x * (u x - v x)| ≤ Lp * max |u x - v x| |u' x - v' x| := by
      rw [abs_mul]
      exact mul_le_mul (hP x hxm) h1 (abs_nonneg _) hPn
    have hC : |(Pc x - P x) * u x| ≤ εp * B := by
      rw [abs_mul]
      exact mul_le_mul (hεp x hxm) hux (abs_nonneg _) hεpn
    have hD : |Qc x * u' x| ≤ εq * B := by
      rw [abs_mul]
      exact mul_le_mul (hεq x hxm) hu'x (abs_nonneg _) hεqn
    have hsum : |u'' x - v'' x| ≤ Lp * max |u x - v x| |u' x - v' x| + (εp * B + εq * B) := by
      rw [hdec]
      calc |P x * (u x - v x) + ((Pc x - P x) * u x + Qc x * u' x)|
          ≤ |P x * (u x - v x)| + |(Pc x - P x) * u x + Qc x * u' x| := abs_add_le _ _
        _ ≤ |P x * (u x - v x)| + (|(Pc x - P x) * u x| + |Qc x * u' x|) := by
            gcongr
            exact abs_add_le _ _
        _ ≤ Lp * max |u x - v x| |u' x - v' x| + (εp * B + εq * B) := by gcongr
    have hfin2 : |u'' x - v'' x| ≤ L * max |u x - v x| |u' x - v' x| + (εp + εq) * B := by
      nlinarith
    have hfin1 : |u' x - v' x| ≤ L * max |u x - v x| |u' x - v' x| + (εp + εq) * B := by
      nlinarith
    exact max_le hfin1 hfin2
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv hstart hbound
  intro x hx
  have hxb := hmain x hx
  have hgb : gronwallBound 0 L ((εp + εq) * B) (x - a)
      = ((εp + εq) * B / L) * (Real.exp (L * (x - a)) - 1) := by
    simp only [gronwallBound, if_neg hLne]
    ring
  rw [hnw, hgb] at hxb
  exact hxb


/-- **Two-sided comparison.**  Solutions of two perturbed linear equations `u'' = P_u u + Q_u u'` and
`v'' = P_v v + Q_v v'` with the same initial phase vector separate by the Grönwall envelope built
from the differences of their coefficients.  Taking `Q_v = 0` recovers `phasePair_dist_le`; taking
both perturbed recovers the Cauchy property of a family whose coefficients converge. -/
theorem phasePair_dist_le_pair
    {u u' u'' v v' v'' Pu Qu Pv Qv : ℝ → ℝ} {a b Lp Lq εp εq B : ℝ} (hab : a ≤ b)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' (v'' x) x)
    (hequ : ∀ x ∈ Icc a b, u'' x = Pu x * u x + Qu x * u' x)
    (heqv : ∀ x ∈ Icc a b, v'' x = Pv x * v x + Qv x * v' x)
    (hP : ∀ x ∈ Icc a b, |Pv x| ≤ Lp) (hQ : ∀ x ∈ Icc a b, |Qv x| ≤ Lq)
    (hεp : ∀ x ∈ Icc a b, |Pu x - Pv x| ≤ εp) (hεq : ∀ x ∈ Icc a b, |Qu x - Qv x| ≤ εq)
    (hB : ∀ x ∈ Icc a b, max |u x| |u' x| ≤ B)
    (h0 : u a = v a) (h0' : u' a = v' a) :
    ∀ x ∈ Icc a b, max |u x - v x| |u' x - v' x|
      ≤ ((εp + εq) * B / max 1 (Lp + Lq))
        * (Real.exp (max 1 (Lp + Lq) * (x - a)) - 1) := by
  set L : ℝ := max 1 (Lp + Lq) with hL
  have hL1 : (1 : ℝ) ≤ L := le_max_left _ _
  have hLpq : Lp + Lq ≤ L := le_max_right _ _
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hLne : L ≠ 0 := ne_of_gt hLpos
  set w : ℝ → ℝ × ℝ := fun x => (u x - v x, u' x - v' x) with hw
  set w' : ℝ → ℝ × ℝ := fun x => (u' x - v' x, u'' x - v'' x) with hw'
  have hnw : ∀ x, ‖w x‖ = max |u x - v x| |u' x - v' x| := by
    intro x; simp [hw, Prod.norm_def, Real.norm_eq_abs]
  have hnw' : ∀ x, ‖w' x‖ = max |u' x - v' x| |u'' x - v'' x| := by
    intro x; simp [hw', Prod.norm_def, Real.norm_eq_abs]
  have hcont : ContinuousOn w (Icc a b) := by
    refine Continuous.continuousOn ?_
    exact ((continuous_iff_continuousAt.2 fun x => (hu x).continuousAt).sub
      (continuous_iff_continuousAt.2 fun x => (hv x).continuousAt)).prodMk
      ((continuous_iff_continuousAt.2 fun x => (hu' x).continuousAt).sub
        (continuous_iff_continuousAt.2 fun x => (hv' x).continuousAt))
  have hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt w (w' x) (Ici x) x := by
    intro x _
    exact (((hu x).sub (hv x)).prodMk ((hu' x).sub (hv' x))).hasDerivWithinAt
  have hstart : ‖w a‖ ≤ 0 := by
    rw [hnw, h0, h0']
    simp
  have hεpn : (0 : ℝ) ≤ εp := le_trans (abs_nonneg _) (hεp a ⟨le_rfl, hab⟩)
  have hεqn : (0 : ℝ) ≤ εq := le_trans (abs_nonneg _) (hεq a ⟨le_rfl, hab⟩)
  have hBn : (0 : ℝ) ≤ B := le_trans (le_trans (abs_nonneg _) (le_max_left _ _))
    (hB a ⟨le_rfl, hab⟩)
  have hbound : ∀ x ∈ Ico a b, ‖w' x‖ ≤ L * ‖w x‖ + (εp + εq) * B := by
    intro x hx
    have hxm : x ∈ Icc a b := ⟨hx.1, hx.2.le⟩
    have hPn : (0 : ℝ) ≤ Lp := le_trans (abs_nonneg _) (hP x hxm)
    have hQn : (0 : ℝ) ≤ Lq := le_trans (abs_nonneg _) (hQ x hxm)
    rw [hnw, hnw']
    have h1 : |u x - v x| ≤ max |u x - v x| |u' x - v' x| := le_max_left _ _
    have h2 : |u' x - v' x| ≤ max |u x - v x| |u' x - v' x| := le_max_right _ _
    have hmnn : (0 : ℝ) ≤ max |u x - v x| |u' x - v' x| := le_trans (abs_nonneg _) h1
    have hux : |u x| ≤ B := le_trans (le_max_left _ _) (hB x hxm)
    have hu'x : |u' x| ≤ B := le_trans (le_max_right _ _) (hB x hxm)
    have hdec : u'' x - v'' x
        = Pv x * (u x - v x) + Qv x * (u' x - v' x)
          + ((Pu x - Pv x) * u x + (Qu x - Qv x) * u' x) := by
      rw [hequ x hxm, heqv x hxm]; ring
    have hA : |Pv x * (u x - v x)| ≤ Lp * max |u x - v x| |u' x - v' x| := by
      rw [abs_mul]
      exact mul_le_mul (hP x hxm) h1 (abs_nonneg _) hPn
    have hAq : |Qv x * (u' x - v' x)| ≤ Lq * max |u x - v x| |u' x - v' x| := by
      rw [abs_mul]
      exact mul_le_mul (hQ x hxm) h2 (abs_nonneg _) hQn
    have hC : |(Pu x - Pv x) * u x| ≤ εp * B := by
      rw [abs_mul]
      exact mul_le_mul (hεp x hxm) hux (abs_nonneg _) hεpn
    have hD : |(Qu x - Qv x) * u' x| ≤ εq * B := by
      rw [abs_mul]
      exact mul_le_mul (hεq x hxm) hu'x (abs_nonneg _) hεqn
    have hsum : |u'' x - v'' x|
        ≤ (Lp + Lq) * max |u x - v x| |u' x - v' x| + (εp * B + εq * B) := by
      rw [hdec]
      calc |Pv x * (u x - v x) + Qv x * (u' x - v' x)
              + ((Pu x - Pv x) * u x + (Qu x - Qv x) * u' x)|
          ≤ |Pv x * (u x - v x) + Qv x * (u' x - v' x)|
              + |(Pu x - Pv x) * u x + (Qu x - Qv x) * u' x| := abs_add_le _ _
        _ ≤ (|Pv x * (u x - v x)| + |Qv x * (u' x - v' x)|)
              + (|(Pu x - Pv x) * u x| + |(Qu x - Qv x) * u' x|) := by
            gcongr <;> exact abs_add_le _ _
        _ ≤ (Lp + Lq) * max |u x - v x| |u' x - v' x| + (εp * B + εq * B) := by
            nlinarith [hA, hAq, hC, hD]
    have hfin2 : |u'' x - v'' x| ≤ L * max |u x - v x| |u' x - v' x| + (εp + εq) * B := by
      nlinarith
    have hfin1 : |u' x - v' x| ≤ L * max |u x - v x| |u' x - v' x| + (εp + εq) * B := by
      nlinarith
    exact max_le hfin1 hfin2
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv hstart hbound
  intro x hx
  have hxb := hmain x hx
  have hgb : gronwallBound 0 L ((εp + εq) * B) (x - a)
      = ((εp + εq) * B / L) * (Real.exp (L * (x - a)) - 1) := by
    simp only [gronwallBound, if_neg hLne]
    ring
  rw [hnw, hgb] at hxb
  exact hxb

end GaloisForLFunctions.HTGeometry
