import GaloisForLFunctions.GaloisTheoryOfZeros.TheTransportsOverForwardTimesFormAGroup
import GaloisForLFunctions.GaloisTheoryOfZeros.TheSignBranchPointsLieInTheForwardHalfPlane

/-!
# The turn around a forward branch time is a nontrivial forward monodromy

Near a collision of order `m` at `(τ₀, z₀)` the zeros of `H_{τ₀+s²}` are the `m` sheets
`Z_ρ(s)`, `ρ` a root of the Hermite profile, and `Z_ρ(−s) = Z_{−ρ}(s)`. This file turns the
local law into elements of the forward monodromy group.

* **The Hermite reflection is a transport.** For a collision at a forward time `τ₀`, the circle
  `τ₀ + r²e^{2πis}` of small radius is a forward path, and along it the zero `Z_ρ(r)` is
  transported to `Z_{−ρ}(r)` (`IsCollision.exists_transports_turn`): the lift is
  `Z_ρ(re^{πis})`. Turning twice returns every sheet
  (`IsCollision.exists_transports_turn_twice`).
* A collision of order `m ≥ 2` has a root `ρ ≠ 0` of the profile, and `Z_ρ(r) ≠ Z_{−ρ}(r)`.
  At the centre `Z_{−ρ}(r) = −Z_ρ(r)`; away from the centre `Z_{−ρ}(r) ≠ −Z_ρ(r)`, since both
  zeros are close to `z₀ ≠ 0` (`exists_turn_transports_ne`).
* **A loop acts at every base time.** A forward loop conjugated by a forward path to the time
  `τ` is an element of the group at `τ` with the same action on the transported zeros
  (`IsForwardPath.exists_mem_forwardMonodromy_of_loop`).

Consequences, for every forward base time `τ` off the branch times:

* every forward branch time gives an element `≠ 1` of the group
  (`exists_mem_forwardMonodromy_ne_one_of_mem_branchTimes`);
* the group contains an element which exchanges a zero `z ≠ 0` with `−z`
  (`exists_mem_forwardMonodromy_flip`), from a centre time; in particular the group is not
  trivial (`forwardMonodromy_ne_bot`);
* a collision away from the centre at a forward time gives an element which carries a zero `z`
  to a zero outside the pair `{z, −z}` (`exists_mem_forwardMonodromy_moving_pair`);
* **if every element of the group preserves every pair `{z, −z}`, the Riemann hypothesis holds**
  (`riemannHypothesis_of_forwardMonodromy_preserves_pairs`): a failure of RH is a real
  collision at a positive time, and no real time is a centre time.
-/

open Complex Filter Topology Set Metric
open RHTower RHTower.DeBruijn
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

variable {τ₀ z₀ : ℂ} {m : ℕ} {ρ : ℂ}

/-! ## The turn -/

/-- The square root of the turn: the half circle of radius `r` from `r` to `−r`. -/
def turnRoot (r : ℝ) (s : ℝ) : ℂ := (r : ℂ) * cexp (((Real.pi * s : ℝ) : ℂ) * I)

/-- The turn around `τ₀`: the circle of radius `r²` based at `τ₀ + r²`. -/
def turnPath (τ₀ : ℂ) (r : ℝ) (s : ℝ) : ℂ := τ₀ + turnRoot r s ^ 2

theorem turnRoot_zero (r : ℝ) : turnRoot r 0 = r := by simp [turnRoot]

theorem turnRoot_one (r : ℝ) : turnRoot r 1 = -r := by
  rw [turnRoot, mul_one, Complex.exp_pi_mul_I]
  ring

theorem norm_turnRoot (r s : ℝ) : ‖turnRoot r s‖ = |r| := by
  rw [turnRoot, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

theorem continuous_turnRoot (r : ℝ) : Continuous (turnRoot r) := by
  show Continuous fun s : ℝ => (r : ℂ) * cexp (((Real.pi * s : ℝ) : ℂ) * I)
  fun_prop

theorem continuous_turnPath (τ₀ : ℂ) (r : ℝ) : Continuous (turnPath τ₀ r) := by
  show Continuous fun s : ℝ => τ₀ + turnRoot r s ^ 2
  exact continuous_const.add ((continuous_turnRoot r).pow 2)

theorem turnPath_zero (τ₀ : ℂ) (r : ℝ) : turnPath τ₀ r 0 = τ₀ + (r : ℂ) ^ 2 := by
  rw [turnPath, turnRoot_zero]

theorem turnPath_one (τ₀ : ℂ) (r : ℝ) : turnPath τ₀ r 1 = τ₀ + (r : ℂ) ^ 2 := by
  rw [turnPath, turnRoot_one, neg_sq]

theorem norm_turnPath_sub (τ₀ : ℂ) (r s : ℝ) : ‖turnPath τ₀ r s - τ₀‖ = r ^ 2 := by
  rw [turnPath, add_sub_cancel_left, norm_pow, norm_turnRoot, sq_abs]

/-- A small turn around a forward time is a forward path: it stays in the half-plane and the
branch times are isolated. -/
theorem exists_isForwardPath_turnPath (hτ₀ : 0 < τ₀.re) :
    ∃ r₀ > 0, ∀ r ∈ Ioo (0 : ℝ) r₀, IsForwardPath (turnPath τ₀ r) := by
  obtain ⟨δ, hδ, hball⟩ := exists_ball_branchTimes_subset hτ₀
  refine ⟨min 1 (min δ τ₀.re), lt_min one_pos (lt_min hδ hτ₀), fun r hr => ?_⟩
  have hr1 : r < 1 := hr.2.trans_le (min_le_left _ _)
  have hrδ : r < δ := hr.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrτ : r < τ₀.re := hr.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsq : r ^ 2 ≤ r := by
    rw [sq]
    exact mul_le_of_le_one_left hr.1.le hr1.le
  have hsq0 : 0 < r ^ 2 := pow_pos hr.1 2
  refine ⟨(continuous_turnPath τ₀ r).continuousOn, fun s _ => ?_, fun s _ hmem => ?_⟩
  · have h1 := norm_turnPath_sub τ₀ r s
    have h2 := Complex.abs_re_le_norm (turnPath τ₀ r s - τ₀)
    have h3 := neg_abs_le (turnPath τ₀ r s - τ₀).re
    rw [Complex.sub_re] at h2 h3
    linarith
  · have h1 : turnPath τ₀ r s ∈ ball τ₀ δ := by
      rw [mem_ball, dist_eq_norm, norm_turnPath_sub]
      linarith
    have h3 := norm_turnPath_sub τ₀ r s
    rw [hball _ h1 hmem, sub_self, norm_zero] at h3
    linarith

/-! ## The sheets along the turn -/

theorem collisionZero_zero (τ₀ z₀ : ℂ) (m : ℕ) (ρ : ℂ) : collisionZero τ₀ z₀ m ρ 0 = z₀ := by
  rw [collisionZero, zero_mul, add_zero]

theorem IsCollision.continuousAt_collisionZero (hc : IsCollision τ₀ z₀ m)
    (hρ : heatModelFwd m ρ = 0) : ContinuousAt (collisionZero τ₀ z₀ m ρ) 0 := by
  have h1 : ContinuousAt (fun s => z₀ + s * collisionBranch τ₀ z₀ m ρ s) 0 :=
    continuousAt_const.add (continuousAt_id.mul (collisionBranch_spec hc hρ).1.continuousAt)
  exact h1

/-- Near `s = 0` a sheet of a collision is continuous, consists of zeros, and the turn `s ↦ −s`
carries it to the opposite sheet. -/
theorem IsCollision.exists_ball_sheet (hc : IsCollision τ₀ z₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∃ ε > 0, ContinuousOn (collisionZero τ₀ z₀ m ρ) (ball 0 ε) ∧ ∀ s ∈ ball (0 : ℂ) ε,
      complexHeat (τ₀ + s ^ 2) (collisionZero τ₀ z₀ m ρ s) = 0 ∧
        collisionZero τ₀ z₀ m ρ (-s) = collisionZero τ₀ z₀ m (-ρ) s := by
  have han := (collisionBranch_spec hc hρ).1.eventually_analyticAt
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff_ball.1
    (han.and ((complexHeat_collisionZero hc hρ).and (collisionZero_neg hc hρ)))
  refine ⟨ε, hε, fun s hs => ?_, fun s hs => (h s hs).2⟩
  have h1 : ContinuousAt (fun s => z₀ + s * collisionBranch τ₀ z₀ m ρ s) s :=
    continuousAt_const.add (continuousAt_id.mul (h s hs).1.continuousAt)
  exact h1.continuousWithinAt

/-- **The Hermite reflection is a transport.** Along a small turn around a collision the zero
on the sheet `ρ` is transported to the zero on the sheet `−ρ`. -/
theorem IsCollision.exists_transports_turn (hc : IsCollision τ₀ z₀ m)
    (hρ : heatModelFwd m ρ = 0) :
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε, Transports (turnPath τ₀ r)
      (collisionZero τ₀ z₀ m ρ r) (collisionZero τ₀ z₀ m (-ρ) r) := by
  obtain ⟨ε, hε, hcont, hz⟩ := hc.exists_ball_sheet hρ
  refine ⟨ε, hε, fun r hr => ?_⟩
  have hmem : ∀ s : ℝ, turnRoot r s ∈ ball (0 : ℂ) ε := fun s => by
    rw [mem_ball_zero_iff, norm_turnRoot, abs_of_pos hr.1]
    exact hr.2
  have hr' : (r : ℂ) ∈ ball (0 : ℂ) ε := by
    have := hmem 0
    rwa [turnRoot_zero] at this
  refine ⟨fun s => collisionZero τ₀ z₀ m ρ (turnRoot r s),
    ⟨hcont.comp (continuous_turnRoot r).continuousOn fun s _ => hmem s,
      fun s _ => (hz _ (hmem s)).1⟩, ?_, ?_⟩
  · show collisionZero τ₀ z₀ m ρ (turnRoot r 0) = _
    rw [turnRoot_zero]
  · show collisionZero τ₀ z₀ m ρ (turnRoot r 1) = _
    rw [turnRoot_one]
    exact (hz _ hr').2

/-- **The local monodromy has order two.** Turning twice around a collision returns the zero on
every sheet. -/
theorem IsCollision.exists_transports_turn_twice (hc : IsCollision τ₀ z₀ m)
    (hρ : heatModelFwd m ρ = 0) :
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε, Transports (pathJoin (turnPath τ₀ r) (turnPath τ₀ r))
      (collisionZero τ₀ z₀ m ρ r) (collisionZero τ₀ z₀ m ρ r) := by
  have hρ' : heatModelFwd m (-ρ) = 0 := by rw [heatModelFwd_neg, hρ, mul_zero]
  obtain ⟨ε₁, hε₁, h₁⟩ := hc.exists_transports_turn hρ
  obtain ⟨ε₂, hε₂, h₂⟩ := hc.exists_transports_turn hρ'
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun r hr => ?_⟩
  have h := h₂ r ⟨hr.1, hr.2.trans_le (min_le_right _ _)⟩
  rw [neg_neg] at h
  exact (h₁ r ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩).trans h

/-- A property that holds near `0` off `0` holds at all small positive real points. -/
theorem exists_forall_Ioo_of_eventually {P : ℂ → Prop} (h : ∀ᶠ s in 𝓝[≠] (0 : ℂ), P s) :
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε, P (r : ℂ) := by
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_nhdsWithin_iff.1 h)
  refine ⟨ε, hε, fun r hr => hP _ ?_ ?_⟩
  · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    exact hr.2
  · exact Complex.ofReal_ne_zero.2 hr.1.ne'

private theorem eq_zero_of_eq_neg {z : ℂ} (h : z = -z) : z = 0 := by
  have h2 : (2 : ℂ) * z = 0 := by linear_combination h
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

/-- Away from the centre the opposite sheet is not the reflected sheet: both zeros are close to
`z₀ ≠ 0`. -/
theorem IsCollision.eventually_ne_neg (hc : IsCollision τ₀ z₀ m) (hρ : heatModelFwd m ρ = 0)
    (hz₀ : z₀ ≠ 0) :
    ∀ᶠ s in 𝓝 (0 : ℂ), collisionZero τ₀ z₀ m (-ρ) s ≠ -collisionZero τ₀ z₀ m ρ s := by
  have hρ' : heatModelFwd m (-ρ) = 0 := by rw [heatModelFwd_neg, hρ, mul_zero]
  have h : Tendsto (fun s => collisionZero τ₀ z₀ m (-ρ) s + collisionZero τ₀ z₀ m ρ s) (𝓝 0)
      (𝓝 (z₀ + z₀)) := by
    have h1 := (hc.continuousAt_collisionZero hρ').tendsto
    have h2 := (hc.continuousAt_collisionZero hρ).tendsto
    rw [collisionZero_zero] at h1 h2
    exact h1.add h2
  have hne : z₀ + z₀ ≠ 0 := fun h0 => hz₀ (eq_zero_of_eq_neg (by linear_combination h0))
  filter_upwards [h.eventually_ne hne] with s hs heq
  exact hs (by rw [heq, neg_add_cancel])

/-- A multiple zero is a collision of order at least two. -/
theorem exists_isCollision_two_le (h0 : complexHeat τ₀ z₀ = 0)
    (hd : deriv (complexHeat τ₀) z₀ = 0) : ∃ m, 2 ≤ m ∧ IsCollision τ₀ z₀ m := by
  obtain ⟨m, hm, hc⟩ := exists_isCollision h0
  refine ⟨m, ?_, hc⟩
  by_contra hlt
  have hm1 : m = 1 := by omega
  have h1 := hc.top_ne_zero
  rw [hm1, iteratedDeriv_one] at h1
  exact h1 hd

/-- A profile of degree at least two has a root other than `0`. -/
theorem exists_profile_root_ne_zero (hm : 2 ≤ m) : ∃ ρ : ℂ, ρ ≠ 0 ∧ heatModelFwd m ρ = 0 := by
  obtain ⟨b, hb, hb0⟩ := Finset.exists_mem_ne (s := profileRoots m)
    (by rw [card_profileRoots]; omega) 0
  exact ⟨(b : ℂ), Complex.ofReal_ne_zero.2 hb0, heatModelFwd_profileRoot hb⟩

/-- **The turn around a forward branch point moves a zero.** Along every small turn around a
forward time with a multiple zero `z₀`, some zero `z` is transported to a zero `z' ≠ z`. If
`z₀` is the centre then `z' = −z`; otherwise `z' ≠ −z`. -/
theorem exists_turn_transports_ne (hτ₀ : 0 < τ₀.re) (h0 : complexHeat τ₀ z₀ = 0)
    (hd : deriv (complexHeat τ₀) z₀ = 0) :
    ∃ r₀ > 0, ∀ r ∈ Ioo (0 : ℝ) r₀, IsForwardPath (turnPath τ₀ r) ∧ ∃ z z' : ℂ,
      z' ≠ z ∧ (z₀ = 0 → z' = -z) ∧ (z₀ ≠ 0 → z' ≠ -z) ∧ Transports (turnPath τ₀ r) z z' := by
  obtain ⟨m, hm, hc⟩ := exists_isCollision_two_le h0 hd
  obtain ⟨ρ, hρ0, hρ⟩ := exists_profile_root_ne_zero hm
  have hρ' : heatModelFwd m (-ρ) = 0 := by rw [heatModelFwd_neg, hρ, mul_zero]
  have hsign : ∀ᶠ s in 𝓝 (0 : ℂ),
      (z₀ = 0 → collisionZero τ₀ z₀ m (-ρ) s = -collisionZero τ₀ z₀ m ρ s) ∧
        (z₀ ≠ 0 → collisionZero τ₀ z₀ m (-ρ) s ≠ -collisionZero τ₀ z₀ m ρ s) := by
    rcases eq_or_ne z₀ 0 with rfl | hz
    · filter_upwards [collisionZero_reflect hc hρ] with s hs
      rw [neg_zero] at hs
      exact ⟨fun _ => hs.symm, fun h => absurd rfl h⟩
    · filter_upwards [hc.eventually_ne_neg hρ hz] with s hs
      exact ⟨fun h => absurd h hz, fun _ => hs⟩
  obtain ⟨r₁, hr₁, hpath⟩ := exists_isForwardPath_turnPath hτ₀
  obtain ⟨r₂, hr₂, hturn⟩ := hc.exists_transports_turn hρ
  obtain ⟨r₃, hr₃, hloc⟩ := exists_forall_Ioo_of_eventually
    ((collisionZero_ne hc hρ hρ' fun h => hρ0 (eq_zero_of_eq_neg h)).and
      (hsign.filter_mono nhdsWithin_le_nhds))
  refine ⟨min r₁ (min r₂ r₃), lt_min hr₁ (lt_min hr₂ hr₃), fun r hr => ?_⟩
  have h1 : r ∈ Ioo (0 : ℝ) r₁ := ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩
  have h2 : r ∈ Ioo (0 : ℝ) r₂ :=
    ⟨hr.1, hr.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
  have h3 : r ∈ Ioo (0 : ℝ) r₃ :=
    ⟨hr.1, hr.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨hne, hcentre, hoff⟩ := hloc r h3
  exact ⟨hpath r h1, _, _, hne.symm, hcentre, hoff, hturn r h2⟩

/-! ## A loop acts at every base time -/

/-- **A forward loop acts in the group at every base time.** For a forward loop `γ` and a
forward time `τ` off the branch times there are a forward path `δ` from the base of `γ` to `τ`
and an element `σ` of the group at `τ` which acts on the zeros transported along `δ` as `γ`
acts at its base. -/
theorem IsForwardPath.exists_mem_forwardMonodromy_of_loop {γ : ℝ → ℂ} (hγ : IsForwardPath γ)
    (hloop : γ 1 = γ 0) {τ : ℂ} (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) :
    ∃ δ, IsForwardPath δ ∧ δ 0 = γ 0 ∧ δ 1 = τ ∧ ∃ σ ∈ forwardMonodromy τ hτ hb,
      ∀ z z' : ℂ, Transports γ z z' → ∀ p : {w : ℂ // complexHeat τ w = 0},
        Transports δ z p.1 → Transports δ z' (σ p).1 := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨δ, hδ, hδ0, hδ1⟩ := exists_isForwardPath (hγ.re_pos 0 h01) hτ (hγ.simple 0 h01) hb
  have hloopPath : IsForwardPath (pathJoin (pathRev δ) (pathJoin γ δ)) :=
    hδ.reverse.join (hγ.join hδ (hloop.trans hδ0.symm))
      (by rw [pathRev_one, pathJoin_zero, hδ0])
  obtain ⟨σ, hσ, hT⟩ := hloopPath.exists_mem_forwardMonodromy (hτ := hτ) (hb := hb)
    (by rw [pathJoin_zero, pathRev_zero, hδ1]) (by rw [pathJoin_one, pathJoin_one, hδ1])
  refine ⟨δ, hδ, hδ0, hδ1, σ, hσ, fun z z' hzz' p hp => ?_⟩
  obtain ⟨q, hq⟩ := hδ.exists_transports (z₀ := z') (by
    rw [hδ0, ← hloop]
    exact hzz'.zero_right)
  have h1 : Transports (pathJoin (pathRev δ) (pathJoin γ δ)) p.1 q :=
    hp.symm.trans (hzz'.trans hq)
  rw [hloopPath.transports_unique (hT p) h1]
  exact hq

/-- The action of a forward loop on one zero, read at the base time `τ`: the group at `τ` has
an element `σ` and the fibre a point `p` such that `σ p` relates to `p` and to `−p` as the
transported zero `z'` relates to `z` and to `−z`. -/
theorem IsForwardPath.exists_mem_forwardMonodromy_of_transports {γ : ℝ → ℂ}
    (hγ : IsForwardPath γ) (hloop : γ 1 = γ 0) {z z' : ℂ} (hzz' : Transports γ z z') {τ : ℂ}
    (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) :
    ∃ σ ∈ forwardMonodromy τ hτ hb, ∃ p : {w : ℂ // complexHeat τ w = 0},
      (z' ≠ z → σ p ≠ p) ∧ (z' = -z → σ p = fibreNeg τ p) ∧
        (z' ≠ -z → σ p ≠ fibreNeg τ p) := by
  obtain ⟨δ, hδ, hδ0, hδ1, σ, hσ, hact⟩ := hγ.exists_mem_forwardMonodromy_of_loop hloop hτ hb
  obtain ⟨p₁, hp₁⟩ := hδ.exists_transports (z₀ := z) (by
    rw [hδ0]
    exact hzz'.zero_left)
  have hp₁0 : complexHeat τ p₁ = 0 := by
    have := hp₁.zero_right
    rwa [hδ1] at this
  have hq : Transports δ z' (σ ⟨p₁, hp₁0⟩).1 := hact z z' hzz' ⟨p₁, hp₁0⟩ hp₁
  refine ⟨σ, hσ, ⟨p₁, hp₁0⟩, fun hne h => ?_, fun h => Subtype.ext ?_, fun hne h => ?_⟩
  · rw [h] at hq
    exact hne (hδ.transports_injective hq hp₁)
  · have h1 := hp₁.neg
    rw [← h] at h1
    exact hδ.transports_unique hq h1
  · rw [h] at hq
    exact hne (hδ.transports_injective hq hp₁.neg)

/-! ## The group at every base time -/

variable {τ : ℂ}

/-- **Every forward branch point acts in the forward monodromy group.** A multiple zero `z₀` at
a forward time gives, at every base time, an element `σ` and a zero `p` with `σ p ≠ p`. If `z₀`
is the centre then `σ p = −p`; otherwise `σ p ≠ −p`. -/
theorem exists_mem_forwardMonodromy_of_multipleZero (hτ₀ : 0 < τ₀.re)
    (h0 : complexHeat τ₀ z₀ = 0) (hd : deriv (complexHeat τ₀) z₀ = 0) (hτ : 0 < τ.re)
    (hb : τ ∉ branchTimes) :
    ∃ σ ∈ forwardMonodromy τ hτ hb, ∃ p : {w : ℂ // complexHeat τ w = 0},
      σ p ≠ p ∧ (z₀ = 0 → σ p = fibreNeg τ p) ∧ (z₀ ≠ 0 → σ p ≠ fibreNeg τ p) := by
  obtain ⟨r₀, hr₀, hturn⟩ := exists_turn_transports_ne hτ₀ h0 hd
  obtain ⟨hpath, z, z', hne, hcentre, hoff, hT⟩ :=
    hturn (r₀ / 2) ⟨half_pos hr₀, half_lt_self hr₀⟩
  obtain ⟨σ, hσ, p, h1, h2, h3⟩ := hpath.exists_mem_forwardMonodromy_of_transports
    (by rw [turnPath_one, turnPath_zero]) hT hτ hb
  exact ⟨σ, hσ, p, h1 hne, fun h => h2 (hcentre h), fun h => h3 (hoff h)⟩

/-- Every forward branch time gives a nontrivial element of the group at every base time. -/
theorem exists_mem_forwardMonodromy_ne_one_of_mem_branchTimes (hτ₀ : 0 < τ₀.re)
    (hmem : τ₀ ∈ branchTimes) (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) :
    ∃ σ ∈ forwardMonodromy τ hτ hb, σ ≠ 1 := by
  obtain ⟨⟨τ', z₀⟩, ⟨h0, hd⟩, hτ'⟩ := hmem
  have hτ'' : τ' = τ₀ := hτ'
  subst hτ''
  obtain ⟨σ, hσ, p, hne, -, -⟩ := exists_mem_forwardMonodromy_of_multipleZero hτ₀ h0 hd hτ hb
  exact ⟨σ, hσ, fun h => hne (by rw [h]; rfl)⟩

/-- **The forward monodromy group contains a sign change.** At every base time some element of
the group exchanges a zero `z ≠ 0` with `−z`: the turn around a centre time. -/
theorem exists_mem_forwardMonodromy_flip (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) :
    ∃ σ ∈ forwardMonodromy τ hτ hb, ∃ p : {w : ℂ // complexHeat τ w = 0},
      σ p ≠ p ∧ σ p = fibreNeg τ p := by
  obtain ⟨τ₀, hτ₀⟩ := infinite_centerTimes.nonempty
  have hτ₀' : complexHeat τ₀ 0 = 0 := hτ₀
  obtain ⟨m, hm, -, hc⟩ := exists_isCollision_center hτ₀'
  have hd := hc.vanish 1 (by omega)
  rw [iteratedDeriv_one] at hd
  obtain ⟨σ, hσ, p, hne, hflip, -⟩ := exists_mem_forwardMonodromy_of_multipleZero
    (re_pos_of_centreValue_eq_zero hτ₀') hτ₀' hd hτ hb
  exact ⟨σ, hσ, p, hne, hflip rfl⟩

/-- **The forward monodromy group is not trivial.** -/
theorem forwardMonodromy_ne_bot (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) :
    forwardMonodromy τ hτ hb ≠ ⊥ := by
  obtain ⟨σ, hσ, p, hne, -⟩ := exists_mem_forwardMonodromy_flip hτ hb
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hσ
  exact hne (by rw [hσ]; rfl)

/-- **A collision away from the centre moves a pair.** A multiple zero `z₀ ≠ 0` at a forward
time gives, at every base time, an element of the group which carries some zero `z` to a zero
outside the pair `{z, −z}`. -/
theorem exists_mem_forwardMonodromy_moving_pair (hτ₀ : 0 < τ₀.re)
    (h0 : complexHeat τ₀ z₀ = 0) (hd : deriv (complexHeat τ₀) z₀ = 0) (hz₀ : z₀ ≠ 0)
    (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) :
    ∃ σ ∈ forwardMonodromy τ hτ hb, ∃ p : {w : ℂ // complexHeat τ w = 0},
      σ p ≠ p ∧ σ p ≠ fibreNeg τ p := by
  obtain ⟨σ, hσ, p, hne, -, hoff⟩ := exists_mem_forwardMonodromy_of_multipleZero hτ₀ h0 hd hτ hb
  exact ⟨σ, hσ, p, hne, hoff hz₀⟩

/-- **A forward monodromy group of sign changes implies the Riemann hypothesis.** If every
element of the group at one base time preserves every pair `{z, −z}`, then RH holds: a failure
of RH is a multiple zero at a positive real time, and it is not at the centre. -/
theorem riemannHypothesis_of_forwardMonodromy_preserves_pairs (hτ : 0 < τ.re)
    (hb : τ ∉ branchTimes)
    (h : ∀ σ ∈ forwardMonodromy τ hτ hb, ∀ p, σ p = p ∨ σ p = fibreNeg τ p) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_pos_not_mem_branchTimes]
  rintro t ht ⟨⟨τ', z₀⟩, ⟨h0, hd⟩, hτ'⟩
  have hτ'' : τ' = (t : ℂ) := hτ'
  subst hτ''
  have hz₀ : z₀ ≠ 0 := by
    rintro rfl
    exact im_ne_zero_of_complexHeat_center_eq_zero h0 (Complex.ofReal_im t)
  obtain ⟨σ, hσ, p, h1, h2⟩ := exists_mem_forwardMonodromy_moving_pair
    (by rw [Complex.ofReal_re]; exact ht) h0 hd hz₀ hτ hb
  rcases h σ hσ p with h3 | h3
  · exact h1 h3
  · exact h2 h3

end

end GaloisForLFunctions.GaloisTheoryOfZeros
