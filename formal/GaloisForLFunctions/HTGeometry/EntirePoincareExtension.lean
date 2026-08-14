import GaloisForLFunctions.HTGeometry.PoincareFunctionGerm

/-!
# The entire extension of a Poincaré germ

A germ solving `Φ(λ w) = f(Φ w)` at a repelling fixed point of an entire map extends to an entire
solution on the whole plane: the rescaled iterates `f^[n](Φ₀(w/λⁿ))` are eventually independent of
`n` at each point, and each of them is entire on the disc where the germ argument is admissible.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The rescaled iterates of a Poincaré germ. -/
def poincareApprox (f Φ₀ : ℂ → ℂ) (lam : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  f^[n] (Φ₀ (w / lam ^ n))

theorem poincareApprox_succ_of_admissible {f Φ₀ : ℂ → ℂ} {lam : ℂ} {ρ : ℝ}
    (hlam : lam ≠ 0)
    (hsemi : ∀ w : ℂ, ‖lam * w‖ < ρ → Φ₀ (lam * w) = f (Φ₀ w))
    {n : ℕ} {w : ℂ} (hadm : ‖w‖ < ρ * ‖lam‖ ^ n) :
    poincareApprox f Φ₀ lam (n + 1) w = poincareApprox f Φ₀ lam n w := by
  have hlamn : (lam : ℂ) ^ (n + 1) ≠ 0 := pow_ne_zero _ hlam
  have hkey : lam * (w / lam ^ (n + 1)) = w / lam ^ n := by
    field_simp
    ring
  have hnorm : ‖lam * (w / lam ^ (n + 1))‖ < ρ := by
    rw [hkey, norm_div, norm_pow]
    rw [div_lt_iff₀ (by positivity)]
    exact hadm
  have hstep := hsemi (w / lam ^ (n + 1)) hnorm
  rw [hkey] at hstep
  rw [poincareApprox, poincareApprox, Function.iterate_succ_apply, ← hstep]

theorem poincareApprox_eq_of_le {f Φ₀ : ℂ → ℂ} {lam : ℂ} {ρ : ℝ}
    (hlam : lam ≠ 0) (hlam1 : 1 ≤ ‖lam‖) (hρ : 0 < ρ)
    (hsemi : ∀ w : ℂ, ‖lam * w‖ < ρ → Φ₀ (lam * w) = f (Φ₀ w))
    {n : ℕ} {w : ℂ} (hadm : ‖w‖ < ρ * ‖lam‖ ^ n) :
    ∀ m : ℕ, n ≤ m → poincareApprox f Φ₀ lam m w = poincareApprox f Φ₀ lam n w := by
  intro m hm
  induction m with
  | zero =>
    have : n = 0 := Nat.le_zero.mp hm
    rw [this]
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hnm : n ≤ m := Nat.lt_succ_iff.mp hlt
      have hadmm : ‖w‖ < ρ * ‖lam‖ ^ m := by
        have hmono : ‖lam‖ ^ n ≤ ‖lam‖ ^ m := pow_le_pow_right₀ hlam1 hnm
        nlinarith [hρ.le, pow_nonneg (le_trans zero_le_one hlam1) n]
      rw [poincareApprox_succ_of_admissible hlam hsemi hadmm]
      exact ih hnm
    · have : n = m + 1 := le_antisymm hm hge
      rw [this]

/-- Admissible exponents exist for every point. -/
theorem exists_admissible_exponent {lam : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hlam : 1 < ‖lam‖) (w : ℂ) :
    ∃ n : ℕ, ‖w‖ < ρ * ‖lam‖ ^ n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖w‖ / ρ) hlam
  refine ⟨n, ?_⟩
  rw [div_lt_iff₀ hρ] at hn
  linarith [hn]

theorem differentiable_iterate_self {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    Differentiable ℂ (f^[n]) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hfun : (f^[n + 1]) = f ∘ f^[n] := by
      funext z
      rw [Function.iterate_succ_apply']
      rfl
    rw [hfun]
    exact hf.comp ih

/-- **The entire Poincaré extension.**  A Poincaré germ at a repelling fixed point of an entire map
extends to an entire solution of the same functional equation on the whole plane. -/
theorem exists_entire_poincare {f Φ₀ : ℂ → ℂ} {lam : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hlam : 1 < ‖lam‖) (hf : Differentiable ℂ f)
    (hΦ₀ : DifferentiableOn ℂ Φ₀ (Metric.ball (0 : ℂ) ρ))
    (hsemi : ∀ w : ℂ, ‖lam * w‖ < ρ → Φ₀ (lam * w) = f (Φ₀ w)) :
    ∃ Φ : ℂ → ℂ, Differentiable ℂ Φ ∧
      (∀ w : ℂ, Φ (lam * w) = f (Φ w)) ∧
      (∀ w : ℂ, ‖w‖ < ρ → Φ w = Φ₀ w) := by
  classical
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlam
    linarith
  have hlam1 : (1 : ℝ) ≤ ‖lam‖ := hlam.le
  set Φ : ℂ → ℂ := fun w => poincareApprox f Φ₀ lam
    (Nat.find (exists_admissible_exponent hρ hlam w)) w with hΦdef
  have hΦeq : ∀ (w : ℂ) (n : ℕ), ‖w‖ < ρ * ‖lam‖ ^ n →
      Φ w = poincareApprox f Φ₀ lam n w := by
    intro w n hn
    have hN := Nat.find_spec (exists_admissible_exponent hρ hlam w)
    have h1 : poincareApprox f Φ₀ lam
        (max (Nat.find (exists_admissible_exponent hρ hlam w)) n) w
        = poincareApprox f Φ₀ lam (Nat.find (exists_admissible_exponent hρ hlam w)) w :=
      poincareApprox_eq_of_le hlam0 hlam1 hρ hsemi hN _ (le_max_left _ _)
    have h2 : poincareApprox f Φ₀ lam
        (max (Nat.find (exists_admissible_exponent hρ hlam w)) n) w
        = poincareApprox f Φ₀ lam n w :=
      poincareApprox_eq_of_le hlam0 hlam1 hρ hsemi hn _ (le_max_right _ _)
    exact h1.symm.trans h2
  have hdiff : ∀ (n : ℕ) (R : ℝ), R ≤ ρ * ‖lam‖ ^ n →
      DifferentiableOn ℂ (poincareApprox f Φ₀ lam n) (Metric.ball (0 : ℂ) R) := by
    intro n R hR
    have hmaps : Set.MapsTo (fun w : ℂ => w / lam ^ n) (Metric.ball (0 : ℂ) R)
        (Metric.ball (0 : ℂ) ρ) := by
      intro w hw
      rw [Metric.mem_ball, dist_zero_right] at hw ⊢
      rw [norm_div, norm_pow]
      rw [div_lt_iff₀ (by positivity)]
      calc ‖w‖ < R := hw
        _ ≤ ρ * ‖lam‖ ^ n := hR
    have hinner : DifferentiableOn ℂ (fun w : ℂ => Φ₀ (w / lam ^ n)) (Metric.ball (0 : ℂ) R) :=
      hΦ₀.comp ((differentiable_id.div_const _).differentiableOn) hmaps
    exact (differentiable_iterate_self hf n).comp_differentiableOn hinner
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨n, hn⟩ := exists_admissible_exponent hρ hlam w
    have hballmem : w ∈ Metric.ball (0 : ℂ) (ρ * ‖lam‖ ^ n) := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hn
    have hagree : Set.EqOn Φ (poincareApprox f Φ₀ lam n)
        (Metric.ball (0 : ℂ) (ρ * ‖lam‖ ^ n)) := by
      intro z hz
      rw [Metric.mem_ball, dist_zero_right] at hz
      exact hΦeq z n hz
    have hdn := hdiff n (ρ * ‖lam‖ ^ n) le_rfl
    have hda : DifferentiableAt ℂ (poincareApprox f Φ₀ lam n) w :=
      hdn.differentiableAt (Metric.isOpen_ball.mem_nhds hballmem)
    exact hda.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hballmem) hagree)
  · intro w
    obtain ⟨n, hn⟩ := exists_admissible_exponent hρ hlam w
    have hn' : ‖lam * w‖ < ρ * ‖lam‖ ^ (n + 1) := by
      rw [norm_mul, pow_succ]
      have hpos : (0 : ℝ) < ‖lam‖ := lt_trans zero_lt_one hlam
      nlinarith [hn, hpos]
    rw [hΦeq (lam * w) (n + 1) hn', hΦeq w n hn]
    have hlamn : (lam : ℂ) ^ (n + 1) ≠ 0 := pow_ne_zero _ hlam0
    have harg : lam * w / lam ^ (n + 1) = w / lam ^ n := by
      field_simp
      ring
    rw [poincareApprox, poincareApprox, harg, Function.iterate_succ_apply']
  · intro w hw
    have h0 : ‖w‖ < ρ * ‖lam‖ ^ 0 := by simpa using hw
    rw [hΦeq w 0 h0, poincareApprox]
    simp

end

end GaloisForLFunctions.HTGeometry
