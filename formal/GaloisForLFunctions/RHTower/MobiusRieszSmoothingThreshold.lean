import GaloisForLFunctions.RHTower.MobiusRieszCausalCalculus

/-!
# Sharp smoothing order for finite Möbius--Riesz packets

For a nonempty list of positive logarithmic shifts, the cutoff-preserving
finite-difference Riesz packet becomes everywhere nonnegative exactly after
`length - 1` causal integrations. At that order it has an explicit positive
exponential tail. One order below, the same tail is strictly negative.
No fixed integration order therefore repairs arbitrarily long packets.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.MobiusRieszSmoothing

def tailMass (A : List ℝ) : ℝ := (A.map (fun a => Real.exp a - 1)).prod

theorem tailMass_pos : ∀ A : List ℝ, (∀ a ∈ A, 0 < a) → 0 < tailMass A := by
  intro A
  induction A with
  | nil => intro _; norm_num [tailMass]
  | cons a A ih =>
      intro hA
      have ha := hA a (by simp)
      have he : 1 < Real.exp a := by simpa using Real.exp_lt_exp.mpr ha
      exact mul_pos (sub_pos.mpr he) (ih (fun b hb => hA b (by simp [hb])))

/-- The first nonnegative order: one primitive for every prime after the first. -/
theorem threshold_nonneg : ∀ A : List ℝ, (∀ a ∈ A, 0 ≤ a) → A ≠ [] →
    ∀ t, 0 ≤ smoothed A (A.length - 1) t := by
  intro A
  induction A with
  | nil => intro _ h; exact (h rfl).elim
  | cons a A ih =>
      intro hA _ t
      have ha := hA a (by simp)
      have hrest : ∀ b ∈ A, 0 ≤ b := fun b hb => hA b (by simp [hb])
      cases A with
      | nil =>
          change 0 ≤ hinge t - hinge (t - a)
          exact sub_nonneg.mpr (monotone_hinge (by linarith))
      | cons b B =>
          simp only [List.length_cons, Nat.add_sub_cancel] at ih ⊢
          rw [smoothed_cons_succ hrest ha B.length t]
          exact intervalIntegral.integral_nonneg (show t - a ≤ t by linarith)
            (fun u _ => ih hrest (by simp) u)

/-- Exact exponential tail of the positive box-integral kernel. -/
theorem threshold_tail : ∀ A : List ℝ, (∀ a ∈ A, 0 ≤ a) → A ≠ [] →
    ∀ t, A.sum ≤ t →
      smoothed A (A.length - 1) t = Real.exp (-t) * tailMass A := by
  intro A
  induction A with
  | nil => intro _ h; exact (h rfl).elim
  | cons a A ih =>
      intro hA _ t ht
      have ha := hA a (by simp)
      have hrest : ∀ b ∈ A, 0 ≤ b := fun b hb => hA b (by simp [hb])
      cases A with
      | nil =>
          have hat : a ≤ t := by simpa using ht
          change hinge t - hinge (t - a) = _
          rw [hinge_of_nonneg (ha.trans hat), hinge_of_nonneg (by linarith)]
          simp only [tailMass, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
            mul_one]
          rw [show -(t - a) = -t + a by ring, Real.exp_add]
          ring
      | cons b B =>
          have hrec := smoothed_cons_succ hrest ha B.length t
          simp only [List.length_cons, Nat.add_sub_cancel] at ih ⊢
          rw [hrec]
          have hfun : ∀ u ∈ Set.uIcc (t - a) t,
              smoothed (b :: B) B.length u = Real.exp (-u) * tailMass (b :: B) := by
            intro u hu
            rw [Set.uIcc_of_le (by linarith : t - a ≤ t)] at hu
            apply ih hrest (by simp)
            simp only [List.sum_cons] at ht ⊢
            linarith [hu.1]
          rw [intervalIntegral.integral_congr hfun]
          have hd (u : ℝ) :
              HasDerivAt (fun u : ℝ => -Real.exp (-u) * tailMass (b :: B))
                (Real.exp (-u) * tailMass (b :: B)) u := by
            convert! (((Real.hasDerivAt_exp (-u)).comp u
              (hasDerivAt_id' u).neg).neg.mul_const (tailMass (b :: B))) using 1
            ring
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
            (show IntervalIntegrable (fun u : ℝ => Real.exp (-u) * tailMass (b :: B))
              volume (t - a) t from (by fun_prop : Continuous _).intervalIntegrable _ _)]
          change -Real.exp (-t) * tailMass (b :: B) -
              (-Real.exp (-(t - a)) * tailMass (b :: B)) =
            Real.exp (-t) * ((Real.exp a - 1) * tailMass (b :: B))
          rw [show -(t - a) = -t + a by ring, Real.exp_add]
          ring

/-- One order below positivity, the open tail has the opposite, strictly negative sign. -/
theorem below_threshold_tail {A : List ℝ} (hA : ∀ a ∈ A, 0 ≤ a)
    (hlen : 2 ≤ A.length) {t : ℝ} (ht : A.sum < t) :
    smoothed A (A.length - 2) t = -(Real.exp (-t) * tailMass A) := by
  have hne : A ≠ [] := by intro h; simp [h] at hlen
  have hd : HasDerivAt (smoothed A (A.length - 1))
      (smoothed A (A.length - 2) t) t := by
    have heq : A.length - 1 = (A.length - 2) + 1 := by omega
    rw [heq]
    exact hasDerivAt_primitive (continuous_smoothed A (A.length - 2)) t
  have hde : HasDerivAt (fun u => Real.exp (-u) * tailMass A)
      (-(Real.exp (-t) * tailMass A)) t := by
    convert! ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id' t).neg).mul_const
      (tailMass A) using 1
    ring
  have heq : smoothed A (A.length - 1) =ᶠ[𝓝 t]
      (fun u => Real.exp (-u) * tailMass A) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact threshold_tail A hA hne u hu.le
  exact hd.unique (hde.congr_of_eventuallyEq heq)

theorem below_threshold_neg {A : List ℝ} (hA : ∀ a ∈ A, 0 < a)
    (hlen : 2 ≤ A.length) {t : ℝ} (ht : A.sum < t) :
    smoothed A (A.length - 2) t < 0 := by
  rw [below_threshold_tail (fun a ha => (hA a ha).le) hlen ht]
  exact neg_lt_zero.mpr (mul_pos (Real.exp_pos _) (tailMass_pos A hA))

/-- Exact smoothing threshold for every nonempty finite packet of positive shifts. -/
theorem smoothing_threshold {A : List ℝ} (hA : ∀ a ∈ A, 0 < a)
    (hne : A ≠ []) (r : ℕ) :
    (∀ t, 0 ≤ smoothed A r t) ↔ A.length - 1 ≤ r := by
  have hA0 : ∀ a ∈ A, 0 ≤ a := fun a ha => (hA a ha).le
  constructor
  · intro hr
    by_contra hbad
    have hlen : 2 ≤ A.length := by omega
    let s := A.length - 2 - r
    have heq : primIter s (smoothed A r) = smoothed A (A.length - 2) := by
      dsimp [smoothed]
      rw [← primIter_add]
      congr 1
      dsimp [s]
      omega
    have hp := primIter_nonneg (causal_smoothed hA0 r) hr s (A.sum + 1)
    rw [heq] at hp
    exact (not_le_of_gt (below_threshold_neg hA hlen (by linarith : A.sum < A.sum + 1))) hp
  · intro hr
    let s := r - (A.length - 1)
    have heq : smoothed A r = primIter s (smoothed A (A.length - 1)) := by
      dsimp [smoothed]
      rw [← primIter_add]
      congr 1
      dsimp [s]
      omega
    rw [heq]
    exact primIter_nonneg (causal_smoothed hA0 _) (threshold_nonneg A hA0 hne) s

/-- Every subcritical smoothing order retains a negative region. -/
theorem exists_negative_of_insufficient_smoothing {A : List ℝ}
    (hA : ∀ a ∈ A, 0 < a) (hne : A ≠ []) {r : ℕ} (hr : r < A.length - 1) :
    ∃ t, smoothed A r t < 0 := by
  by_contra h
  have hnonneg : ∀ t, 0 ≤ smoothed A r t := by simpa using h
  exact (not_le_of_gt hr) ((smoothing_threshold hA hne r).mp hnonneg)

end RHTower.MobiusRieszSmoothing
