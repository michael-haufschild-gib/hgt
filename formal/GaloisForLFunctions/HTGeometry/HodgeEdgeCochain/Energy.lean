import GaloisForLFunctions.HTGeometry.HodgeEdgeCochain.Interaction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The exact energy identity and coercive long-time dynamics

This file formalises §3.3, §3.4, §4 and the energy half of §5 of Boudourides, *Hodge Coercivity
and Global Dynamics in Two-Field Edge-Cochain Systems with MHD-Type Cancellation*
(arXiv:2608.19360).

The two-field system is

```text
u̇ = -ν Δ u + B(u,u) - B(h,h) + f ,      ḣ = -η Δ h + B(u,h) - B(h,u) + g ,
```

on a real inner-product phase space, with `Δ` a nonnegative self-adjoint dissipative operator and
`B` in the cancellation class of `Interaction.lean`.

## Main results

* `hasDerivAt_energy` — **Theorem 2**, the exact energy identity (12).
* `integral_dissipation_identity` — the integrated identity (15)–(16).
* `energy_deriv_le_forced` — the forced scalar inequality (13).
* `energy_le_forced` — the explicit bound (14) of **Proposition 2**.
* `energy_le_unforced` — **Theorem 4**, unforced coercive decay `E(t) ≤ E(0) e^{-2βt}`.
* `absorbing_ball_positively_invariant` — the positive invariance half of **Theorem 3**.
* `energy_diff_le` — the continuous-dependence estimate (11) of §3.4.
* `energy_le_apriori` — an unconditional a priori bound, used for global existence.
-/

open Set intervalIntegral MeasureTheory
open scoped InnerProductSpace

set_option maxSynthPendingDepth 3

namespace GaloisForLFunctions.HTGeometry.HodgeEdgeCochain

section TwoField

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (A : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (nu eta : ℝ) (f g : E)

/-- The velocity-like field of equation (5). -/
noncomputable def velocityField (u h : E) : E := -(nu • A u) + B u u - B h h + f

/-- The magnetic-like field of equation (6). -/
noncomputable def magneticField (u h : E) : E := -(eta • A h) + B u h - B h u + g

/-- `(u,h)` solves the two-field system (5)–(6) on the set `s`. -/
def IsSolutionOn (u h : ℝ → E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivAt u (velocityField A B nu f (u t) (h t)) t ∧
    HasDerivAt h (magneticField A B eta g (u t) (h t)) t

/-- The system with the whole vector field rescaled by a time-dependent scalar `c`.  Only the
truncation used for global existence needs this; the paper's system is `c ≡ 1`. -/
def IsScaledSolutionOn (c : ℝ → ℝ) (u h : ℝ → E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivAt u (c t • velocityField A B nu f (u t) (h t)) t ∧
    HasDerivAt h (c t • magneticField A B eta g (u t) (h t)) t

/-- The total energy `E = ‖u‖² + ‖h‖²`. -/
def energy (u h : ℝ → E) (t : ℝ) : ℝ := ‖u t‖ ^ 2 + ‖h t‖ ^ 2

/-- The instantaneous dissipation `ν⟨Δu,u⟩ + η⟨Δh,h⟩`. -/
noncomputable def dissipation (u h : ℝ → E) (t : ℝ) : ℝ :=
  nu * ⟪A (u t), u t⟫_ℝ + eta * ⟪A (h t), h t⟫_ℝ

/-- The instantaneous forcing power `⟨f,u⟩ + ⟨g,h⟩`. -/
def forcingPower (u h : ℝ → E) (t : ℝ) : ℝ := ⟪f, u t⟫_ℝ + ⟪g, h t⟫_ℝ

variable {A B nu eta f g}

/-- The energy identity for the system whose whole vector field is rescaled by a scalar `c`.
Only the truncation used for global existence needs this generality; the paper's system is the
case `c = 1` recorded in `hasDerivAt_energy`. -/
theorem hasDerivAt_energy_smul (hB : IsCancelling B) {u h : ℝ → E} {t c : ℝ}
    (hu : HasDerivAt u (c • velocityField A B nu f (u t) (h t)) t)
    (hh : HasDerivAt h (c • magneticField A B eta g (u t) (h t)) t) :
    HasDerivAt (energy u h)
      (2 * c * (-(dissipation A nu eta u h t) + forcingPower f g u h t)) t := by
  have e1 : ⟪velocityField A B nu f (u t) (h t), u t⟫_ℝ
      = -(nu * ⟪A (u t), u t⟫_ℝ) + ⟪B (u t) (u t), u t⟫_ℝ - ⟪B (h t) (h t), u t⟫_ℝ
        + ⟪f, u t⟫_ℝ := by
    simp only [velocityField, inner_add_left, inner_sub_left, inner_neg_left,
      real_inner_smul_left]
  have e2 : ⟪magneticField A B eta g (u t) (h t), h t⟫_ℝ
      = -(eta * ⟪A (h t), h t⟫_ℝ) + ⟪B (u t) (h t), h t⟫_ℝ - ⟪B (h t) (u t), h t⟫_ℝ
        + ⟪g, h t⟫_ℝ := by
    simp only [magneticField, inner_add_left, inner_sub_left, inner_neg_left,
      real_inner_smul_left]
  have c1 : ⟪B (u t) (u t), u t⟫_ℝ = 0 := hB.inner_self_eq_zero _ _
  have c2 : ⟪B (u t) (h t), h t⟫_ℝ = 0 := hB.inner_self_eq_zero _ _
  have c3 : ⟪B (h t) (h t), u t⟫_ℝ = -⟪B (h t) (u t), h t⟫_ℝ := hB _ _ _
  have hval : ⟪u t, c • velocityField A B nu f (u t) (h t)⟫_ℝ
        + ⟪c • velocityField A B nu f (u t) (h t), u t⟫_ℝ
        + (⟪h t, c • magneticField A B eta g (u t) (h t)⟫_ℝ
          + ⟪c • magneticField A B eta g (u t) (h t), h t⟫_ℝ)
      = 2 * c * (-(dissipation A nu eta u h t) + forcingPower f g u h t) := by
    have s1 : ⟪u t, velocityField A B nu f (u t) (h t)⟫_ℝ
        = ⟪velocityField A B nu f (u t) (h t), u t⟫_ℝ := real_inner_comm _ _
    have s2 : ⟪h t, magneticField A B eta g (u t) (h t)⟫_ℝ
        = ⟪magneticField A B eta g (u t) (h t), h t⟫_ℝ := real_inner_comm _ _
    rw [real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_left, s1, s2, e1, e2, c1, c2, c3]
    simp only [dissipation, forcingPower]
    ring
  have hrw : energy u h = fun s => ⟪u s, u s⟫_ℝ + ⟪h s, h s⟫_ℝ := by
    funext s
    simp [energy]
  rw [hrw, ← hval]
  exact (hu.inner ℝ hu).add (hh.inner ℝ hh)

/-- **Theorem 2 (exact energy identity).**  Every solution of the cancellation class obeys
`½ dE/dt + ν⟨Δu,u⟩ + η⟨Δh,h⟩ = ⟨f,u⟩ + ⟨g,h⟩`. -/
theorem hasDerivAt_energy (hB : IsCancelling B) {u h : ℝ → E} {t : ℝ}
    (hu : HasDerivAt u (velocityField A B nu f (u t) (h t)) t)
    (hh : HasDerivAt h (magneticField A B eta g (u t) (h t)) t) :
    HasDerivAt (energy u h)
      (2 * (-(dissipation A nu eta u h t) + forcingPower f g u h t)) t := by
  have hu' : HasDerivAt u ((1 : ℝ) • velocityField A B nu f (u t) (h t)) t := by
    simpa using hu
  have hh' : HasDerivAt h ((1 : ℝ) • magneticField A B eta g (u t) (h t)) t := by
    simpa using hh
  simpa using hasDerivAt_energy_smul hB hu' hh'

/-- The energy of a solution is differentiable, hence continuous. -/
theorem continuousOn_energy (hB : IsCancelling B) {u h : ℝ → E} {s : Set ℝ}
    (hsol : IsSolutionOn A B nu eta f g u h s) : ContinuousOn (energy u h) s := by
  intro t ht
  exact ((hasDerivAt_energy hB (hsol t ht).1 (hsol t ht).2).continuousAt).continuousWithinAt

end TwoField

/-! ## A scalar comparison lemma -/

section Comparison

/-- Grönwall comparison in the form used below: a real function with `φ' ≤ K φ + c` is bounded by
the corresponding Grönwall envelope. -/
theorem le_gronwallBound_of_hasDerivAt {φ φ' : ℝ → ℝ} {K c T : ℝ}
    (hcont : ContinuousOn φ (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivAt φ (φ' t) t)
    (hbound : ∀ t ∈ Ico 0 T, φ' t ≤ K * φ t + c) :
    ∀ t ∈ Icc 0 T, φ t ≤ gronwallBound (φ 0) K c t := by
  have key := le_gronwallBound_of_liminf_deriv_right_le (f := φ) (f' := φ') (δ := φ 0)
    (K := K) (ε := c) (a := 0) (b := T) hcont
    (fun x hx r hr => by
      have hs := ((hderiv x hx).hasDerivWithinAt (s := Ici x)).liminf_right_slope_le hr
      simpa [slope, smul_eq_mul] using hs)
    le_rfl hbound
  intro t ht
  simpa using key t ht

end Comparison

/-! ## The energy inequalities -/

section Estimates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E →L[ℝ] E} {B : E →L[ℝ] E →L[ℝ] E} {nu eta : ℝ} {f g : E}

/-- **The integrated energy identity (15)–(16).** -/
theorem integral_dissipation_identity (hB : IsCancelling B) {u h : ℝ → E} {T : ℝ}
    (hsol : IsSolutionOn A B nu eta f g u h (uIcc 0 T)) :
    2 * ∫ t in (0 : ℝ)..T, dissipation A nu eta u h t
      = energy u h 0 - energy u h T + 2 * ∫ t in (0 : ℝ)..T, forcingPower f g u h t := by
  have hcontu : ContinuousOn u (uIcc 0 T) := fun t ht =>
    ((hsol t ht).1.continuousAt).continuousWithinAt
  have hconth : ContinuousOn h (uIcc 0 T) := fun t ht =>
    ((hsol t ht).2.continuousAt).continuousWithinAt
  have hcd : ContinuousOn (dissipation A nu eta u h) (uIcc 0 T) := by
    refine ContinuousOn.add (ContinuousOn.mul continuousOn_const ?_)
      (ContinuousOn.mul continuousOn_const ?_)
    · exact (continuous_inner.comp_continuousOn ((A.continuous.comp_continuousOn hcontu).prodMk
        hcontu))
    · exact (continuous_inner.comp_continuousOn ((A.continuous.comp_continuousOn hconth).prodMk
        hconth))
  have hcf : ContinuousOn (forcingPower f g u h) (uIcc 0 T) := by
    refine ContinuousOn.add ?_ ?_
    · exact (continuous_inner.comp_continuousOn (continuousOn_const.prodMk hcontu))
    · exact (continuous_inner.comp_continuousOn (continuousOn_const.prodMk hconth))
  have hd : IntervalIntegrable (dissipation A nu eta u h) volume 0 T := hcd.intervalIntegrable
  have hf' : IntervalIntegrable (forcingPower f g u h) volume 0 T := hcf.intervalIntegrable
  have hint : ∫ t in (0 : ℝ)..T, (2 * (-(dissipation A nu eta u h t) + forcingPower f g u h t))
      = energy u h T - energy u h 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_energy hB (hsol t ht).1 (hsol t ht).2)
      ((hd.neg.add hf').const_mul 2)
  have hsplit : ∫ x in (0 : ℝ)..T, (-(dissipation A nu eta u h x) + forcingPower f g u h x)
      = (∫ x in (0 : ℝ)..T, -(dissipation A nu eta u h x))
        + ∫ x in (0 : ℝ)..T, forcingPower f g u h x :=
    intervalIntegral.integral_add hd.neg hf'
  have hneg : ∫ x in (0 : ℝ)..T, -(dissipation A nu eta u h x)
      = -∫ x in (0 : ℝ)..T, dissipation A nu eta u h x := intervalIntegral.integral_neg
  rw [intervalIntegral.integral_const_mul, hsplit, hneg] at hint
  linarith

/-- **§4.1 (bounded time-averaged dissipation).**  Since the energy is nonnegative, the integrated
identity bounds the mean dissipation by the initial energy and the forcing work. -/
theorem two_mul_integral_dissipation_le (hB : IsCancelling B) {u h : ℝ → E} {T : ℝ}
    (hsol : IsSolutionOn A B nu eta f g u h (uIcc 0 T)) :
    2 * ∫ t in (0 : ℝ)..T, dissipation A nu eta u h t
      ≤ energy u h 0 + 2 * ∫ t in (0 : ℝ)..T, forcingPower f g u h t := by
  have hid := integral_dissipation_identity hB hsol
  have hnn : 0 ≤ energy u h T := by simp only [energy]; positivity
  linarith

end Estimates

/-! ## Coercive long-time dynamics -/

section Coercive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E →L[ℝ] E} {B : E →L[ℝ] E →L[ℝ] E} {nu eta lam : ℝ} {f g : E}

/-- The decay rate `β = min(ν,η) λ` of the paper. -/
def decayRate (nu eta lam : ℝ) : ℝ := min nu eta * lam

theorem decayRate_pos (hnu : 0 < nu) (heta : 0 < eta) (hlam : 0 < lam) :
    0 < decayRate nu eta lam := mul_pos (lt_min hnu heta) hlam

/-- Nonnegativity of the dissipation. -/
theorem dissipation_nonneg (hA : ∀ v : E, 0 ≤ ⟪A v, v⟫_ℝ) (hnu : 0 ≤ nu) (heta : 0 ≤ eta)
    (u h : ℝ → E) (t : ℝ) : 0 ≤ dissipation A nu eta u h t :=
  add_nonneg (mul_nonneg hnu (hA _)) (mul_nonneg heta (hA _))

/-- Coercivity of `Δ` transfers to the two-field dissipation with the rate `β`.  The coercivity
is only needed on a set `W` containing the trajectory; the paper's coercive case is `W = univ`
and the harmonic-fibre case of §5 is `W = V₀`. -/
theorem decayRate_mul_energy_le_dissipation {W : Set E}
    (hcoe : ∀ v ∈ W, lam * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) (hnu : 0 < nu) (heta : 0 < eta)
    (hlam : 0 ≤ lam) (u h : ℝ → E) (t : ℝ) (hu : u t ∈ W) (hh : h t ∈ W) :
    decayRate nu eta lam * energy u h t ≤ dissipation A nu eta u h t := by
  have h1 : min nu eta * (lam * ‖u t‖ ^ 2) ≤ nu * ⟪A (u t), u t⟫_ℝ := by
    have hmin : min nu eta ≤ nu := min_le_left _ _
    have hpos : (0 : ℝ) ≤ lam * ‖u t‖ ^ 2 := mul_nonneg hlam (sq_nonneg _)
    nlinarith [hcoe (u t) hu]
  have h2 : min nu eta * (lam * ‖h t‖ ^ 2) ≤ eta * ⟪A (h t), h t⟫_ℝ := by
    have hmin : min nu eta ≤ eta := min_le_right _ _
    have hpos : (0 : ℝ) ≤ lam * ‖h t‖ ^ 2 := mul_nonneg hlam (sq_nonneg _)
    nlinarith [hcoe (h t) hh]
  simp only [decayRate, energy, dissipation]
  nlinarith

/-- Young's inequality applied to the forcing power. -/
theorem two_mul_forcingPower_le (hbeta : 0 < decayRate nu eta lam) (u h : ℝ → E) (t : ℝ) :
    2 * forcingPower f g u h t
      ≤ decayRate nu eta lam * energy u h t
        + (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam := by
  set b := decayRate nu eta lam with hb
  have hbne : b ≠ 0 := ne_of_gt hbeta
  have hfu : ⟪f, u t⟫_ℝ ≤ ‖f‖ * ‖u t‖ := real_inner_le_norm _ _
  have hgh : ⟪g, h t⟫_ℝ ≤ ‖g‖ * ‖h t‖ := real_inner_le_norm _ _
  have hcf : ‖f‖ ^ 2 / b * b = ‖f‖ ^ 2 := div_mul_cancel₀ _ hbne
  have hcg : ‖g‖ ^ 2 / b * b = ‖g‖ ^ 2 := div_mul_cancel₀ _ hbne
  have y1 : 2 * (‖f‖ * ‖u t‖) ≤ b * ‖u t‖ ^ 2 + ‖f‖ ^ 2 / b := by
    nlinarith [sq_nonneg (b * ‖u t‖ - ‖f‖), hbeta, hcf]
  have y2 : 2 * (‖g‖ * ‖h t‖) ≤ b * ‖h t‖ ^ 2 + ‖g‖ ^ 2 / b := by
    nlinarith [sq_nonneg (b * ‖h t‖ - ‖g‖), hbeta, hcg]
  have hsplit : (‖f‖ ^ 2 + ‖g‖ ^ 2) / b = ‖f‖ ^ 2 / b + ‖g‖ ^ 2 / b := by ring
  simp only [forcingPower, energy]
  rw [hsplit]
  nlinarith [hfu, hgh, y1, y2]

/-- **Proposition 2 (the forced scalar inequality (13)).** -/
theorem energy_deriv_le_forced {W : Set E}
    (hcoe : ∀ v ∈ W, lam * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) (hnu : 0 < nu) (heta : 0 < eta)
    (hlam : 0 < lam) (u h : ℝ → E) (t : ℝ) (hu : u t ∈ W) (hh : h t ∈ W) :
    2 * (-(dissipation A nu eta u h t) + forcingPower f g u h t)
      ≤ -(decayRate nu eta lam) * energy u h t
        + (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam := by
  have hbeta := decayRate_pos hnu heta hlam
  have h1 := decayRate_mul_energy_le_dissipation hcoe hnu heta hlam.le u h t hu hh
  have h2 := two_mul_forcingPower_le (f := f) (g := g) hbeta u h t
  linarith

/-- **Proposition 2, explicit envelope (14).** -/
theorem energy_le_forced (hB : IsCancelling B) {W : Set E}
    (hcoe : ∀ v ∈ W, lam * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) (hnu : 0 < nu) (heta : 0 < eta)
    (hlam : 0 < lam) {u h : ℝ → E} {T : ℝ}
    (hsol : IsSolutionOn A B nu eta f g u h (Icc 0 T))
    (hmem : ∀ t ∈ Icc (0 : ℝ) T, u t ∈ W ∧ h t ∈ W) :
    ∀ t ∈ Icc (0 : ℝ) T, energy u h t
      ≤ energy u h 0 * Real.exp (-(decayRate nu eta lam) * t)
        + (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam ^ 2
          * (1 - Real.exp (-(decayRate nu eta lam) * t)) := by
  have hbeta := decayRate_pos (nu := nu) (eta := eta) (lam := lam) hnu heta hlam
  have hne : -(decayRate nu eta lam) ≠ 0 := by
    intro hc
    exact absurd (neg_eq_zero.mp hc) (ne_of_gt hbeta)
  have hgb := le_gronwallBound_of_hasDerivAt (φ := energy u h)
    (φ' := fun t => 2 * (-(dissipation A nu eta u h t) + forcingPower f g u h t))
    (K := -(decayRate nu eta lam)) (c := (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam) (T := T)
    (continuousOn_energy hB hsol)
    (fun t ht => hasDerivAt_energy hB (hsol t (Ico_subset_Icc_self ht)).1
      (hsol t (Ico_subset_Icc_self ht)).2)
    (fun t ht => energy_deriv_le_forced hcoe hnu heta hlam u h t
      (hmem t (Ico_subset_Icc_self ht)).1 (hmem t (Ico_subset_Icc_self ht)).2)
  intro t ht
  have hb := hgb t ht
  rw [gronwallBound_of_K_ne_0 hne] at hb
  refine le_trans hb (le_of_eq ?_)
  field_simp
  ring

/-- **Theorem 4 (unforced coercive decay).**  With zero forcing the origin attracts every
trajectory at the exponential rate `2β`. -/
theorem energy_le_unforced (hB : IsCancelling B) {W : Set E}
    (hcoe : ∀ v ∈ W, lam * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) (hnu : 0 < nu) (heta : 0 < eta)
    (hlam : 0 < lam) {u h : ℝ → E} {T : ℝ}
    (hsol : IsSolutionOn A B nu eta (0 : E) (0 : E) u h (Icc 0 T))
    (hmem : ∀ t ∈ Icc (0 : ℝ) T, u t ∈ W ∧ h t ∈ W) :
    ∀ t ∈ Icc (0 : ℝ) T, energy u h t
      ≤ energy u h 0 * Real.exp (-(2 * decayRate nu eta lam) * t) := by
  have hbeta := decayRate_pos (nu := nu) (eta := eta) (lam := lam) hnu heta hlam
  have hzero : ∀ t : ℝ, forcingPower (0 : E) (0 : E) u h t = 0 := by
    intro t; simp [forcingPower]
  have hgb := le_gronwallBound_of_hasDerivAt (φ := energy u h)
    (φ' := fun t => 2 * (-(dissipation A nu eta u h t) + forcingPower (0 : E) (0 : E) u h t))
    (K := -(2 * decayRate nu eta lam)) (c := 0) (T := T)
    (continuousOn_energy hB hsol)
    (fun t ht => hasDerivAt_energy hB (hsol t (Ico_subset_Icc_self ht)).1
      (hsol t (Ico_subset_Icc_self ht)).2)
    (fun t ht => by
      have h1 := decayRate_mul_energy_le_dissipation hcoe hnu heta hlam.le u h t
        (hmem t (Ico_subset_Icc_self ht)).1 (hmem t (Ico_subset_Icc_self ht)).2
      rw [hzero t]
      linarith)
  intro t ht
  have hb := hgb t ht
  rwa [gronwallBound_ε0] at hb

/-- **Theorem 3 (positively invariant absorbing ball).**  For `R > F/β` the ball `E ≤ R²` is
positively invariant. -/
theorem energy_le_sq_of_le_sq (hB : IsCancelling B) {W : Set E}
    (hcoe : ∀ v ∈ W, lam * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) (hnu : 0 < nu) (heta : 0 < eta)
    (hlam : 0 < lam) {u h : ℝ → E} {T R : ℝ}
    (hsol : IsSolutionOn A B nu eta f g u h (Icc 0 T))
    (hmem : ∀ t ∈ Icc (0 : ℝ) T, u t ∈ W ∧ h t ∈ W)
    (hR : Real.sqrt (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam < R)
    (h0 : energy u h 0 ≤ R ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, energy u h t ≤ R ^ 2 := by
  have hbeta := decayRate_pos (nu := nu) (eta := eta) (lam := lam) hnu heta hlam
  have hF2 : (0 : ℝ) ≤ ‖f‖ ^ 2 + ‖g‖ ^ 2 := by positivity
  have hFsq : Real.sqrt (‖f‖ ^ 2 + ‖g‖ ^ 2) ^ 2 = ‖f‖ ^ 2 + ‖g‖ ^ 2 := Real.sq_sqrt hF2
  have hFnn : 0 ≤ Real.sqrt (‖f‖ ^ 2 + ‖g‖ ^ 2) := Real.sqrt_nonneg _
  have hquot : 0 ≤ Real.sqrt (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam :=
    div_nonneg hFnn hbeta.le
  have hkey : (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam ^ 2 ≤ R ^ 2 := by
    have hsq : (Real.sqrt (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam) ^ 2 ≤ R ^ 2 := by
      nlinarith [hquot, hR]
    rw [div_pow, hFsq] at hsq
    exact hsq
  intro t ht
  have hbnd := energy_le_forced hB hcoe hnu heta hlam hsol hmem t ht
  have hexp : Real.exp (-(decayRate nu eta lam) * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ t := ht.1
    nlinarith
  have hexp0 : 0 < Real.exp (-(decayRate nu eta lam) * t) := Real.exp_pos _
  nlinarith [hbnd, hkey, h0, hexp, hexp0]

/-- **Theorem 3 (absorption).**  Every bounded set of initial data enters the ball `E ≤ R²`
after a uniform time. -/
theorem exists_absorbing_time
    (hnu : 0 < nu) (heta : 0 < eta) (hlam : 0 < lam) {R rho : ℝ}
    (hR : Real.sqrt (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam < R) (hrho : 0 ≤ rho) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ {u h : ℝ → E} {T : ℝ},
      IsCancelling B → IsSolutionOn A B nu eta f g u h (Icc 0 T) →
      (∀ v : E, lam * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) →
      energy u h 0 ≤ rho → ∀ t ∈ Icc (0 : ℝ) T, T₀ ≤ t → energy u h t ≤ R ^ 2 := by
  have hbeta := decayRate_pos (nu := nu) (eta := eta) (lam := lam) hnu heta hlam
  have hF2 : (0 : ℝ) ≤ ‖f‖ ^ 2 + ‖g‖ ^ 2 := by positivity
  have hFsq : Real.sqrt (‖f‖ ^ 2 + ‖g‖ ^ 2) ^ 2 = ‖f‖ ^ 2 + ‖g‖ ^ 2 := Real.sq_sqrt hF2
  have hFnn : 0 ≤ Real.sqrt (‖f‖ ^ 2 + ‖g‖ ^ 2) := Real.sqrt_nonneg _
  have hquot : 0 ≤ Real.sqrt (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam :=
    div_nonneg hFnn hbeta.le
  set c : ℝ := R ^ 2 - (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam ^ 2 with hc
  have hcpos : 0 < c := by
    have hsq : (Real.sqrt (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam) ^ 2 < R ^ 2 := by
      nlinarith [hquot, hR]
    rw [div_pow, hFsq] at hsq
    simp only [hc]
    linarith
  refine ⟨Real.log ((rho + c) / c) / decayRate nu eta lam, ?_, ?_⟩
  · have h1 : 1 ≤ (rho + c) / c := by
      rw [le_div_iff₀ hcpos]
      linarith
    exact div_nonneg (Real.log_nonneg h1) hbeta.le
  · intro u h T hB hsol hcoe h0 t ht hT
    have hbnd := energy_le_forced hB (W := Set.univ) (fun v _ => hcoe v) hnu heta hlam hsol
      (fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩) t ht
    have hexp0 : 0 < Real.exp (-(decayRate nu eta lam) * t) := Real.exp_pos _
    have hexp1 : Real.exp (-(decayRate nu eta lam) * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [ht.1]
    have hlogle : Real.log ((rho + c) / c) ≤ decayRate nu eta lam * t := by
      have := (div_le_iff₀ hbeta).mp hT
      linarith [this]
    have hexp2 : (rho + c) / c ≤ Real.exp (decayRate nu eta lam * t) := by
      have hpos : 0 < (rho + c) / c := by positivity
      calc (rho + c) / c = Real.exp (Real.log ((rho + c) / c)) := (Real.exp_log hpos).symm
        _ ≤ Real.exp (decayRate nu eta lam * t) := Real.exp_le_exp.mpr hlogle
    have hinv : Real.exp (-(decayRate nu eta lam) * t)
        = (Real.exp (decayRate nu eta lam * t))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    have hepos : 0 < Real.exp (decayRate nu eta lam * t) := Real.exp_pos _
    have hle : rho * Real.exp (-(decayRate nu eta lam) * t) ≤ c := by
      rw [hinv, mul_inv_le_iff₀ hepos]
      have hrc : 0 < rho + c := by linarith
      have := (div_le_iff₀ hcpos).mp hexp2
      nlinarith [hcpos, hrho]
    have hQnn : (0 : ℝ) ≤ (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam ^ 2 := by positivity
    have hEe : energy u h 0 * Real.exp (-(decayRate nu eta lam) * t)
        ≤ rho * Real.exp (-(decayRate nu eta lam) * t) :=
      mul_le_mul_of_nonneg_right h0 hexp0.le
    have hQ1 : (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam ^ 2
          * (1 - Real.exp (-(decayRate nu eta lam) * t))
        ≤ (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam ^ 2 := by
      nlinarith [hQnn, hexp0]
    linarith [hc]

/-- An unconditional a priori bound: dropping the dissipation entirely, the energy of any
solution grows at most exponentially.  This is what rules out finite-time blow-up. -/
theorem energy_le_apriori (hB : IsCancelling B) (hA : ∀ v : E, 0 ≤ ⟪A v, v⟫_ℝ)
    (hnu : 0 ≤ nu) (heta : 0 ≤ eta) {u h : ℝ → E} {T : ℝ}
    (hsol : IsSolutionOn A B nu eta f g u h (Icc 0 T)) :
    ∀ t ∈ Icc (0 : ℝ) T, energy u h t
      ≤ energy u h 0 * Real.exp t + (‖f‖ ^ 2 + ‖g‖ ^ 2) * (Real.exp t - 1) := by
  have hgb := le_gronwallBound_of_hasDerivAt (φ := energy u h)
    (φ' := fun t => 2 * (-(dissipation A nu eta u h t) + forcingPower f g u h t))
    (K := 1) (c := ‖f‖ ^ 2 + ‖g‖ ^ 2) (T := T)
    (continuousOn_energy hB hsol)
    (fun t ht => hasDerivAt_energy hB (hsol t (Ico_subset_Icc_self ht)).1
      (hsol t (Ico_subset_Icc_self ht)).2)
    (fun t _ => by
      have hd := dissipation_nonneg hA hnu heta u h t
      have hfu : ⟪f, u t⟫_ℝ ≤ ‖f‖ * ‖u t‖ := real_inner_le_norm _ _
      have hgh : ⟪g, h t⟫_ℝ ≤ ‖g‖ * ‖h t‖ := real_inner_le_norm _ _
      have y1 : 2 * (‖f‖ * ‖u t‖) ≤ ‖u t‖ ^ 2 + ‖f‖ ^ 2 := by
        nlinarith [sq_nonneg (‖u t‖ - ‖f‖)]
      have y2 : 2 * (‖g‖ * ‖h t‖) ≤ ‖h t‖ ^ 2 + ‖g‖ ^ 2 := by
        nlinarith [sq_nonneg (‖h t‖ - ‖g‖)]
      simp only [forcingPower, energy]
      linarith)
  intro t ht
  have hb := hgb t ht
  rw [gronwallBound_of_K_ne_0 (one_ne_zero)] at hb
  simpa using hb


/-! ### The paper's whole-space forms -/

/-- **Proposition 2 (14)** on a coercive phase space. -/
theorem energy_le_forced_of_coercive (hB : IsCancelling B)
    (hcoe : ∀ v : E, lam * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) (hnu : 0 < nu) (heta : 0 < eta)
    (hlam : 0 < lam) {u h : ℝ → E} {T : ℝ}
    (hsol : IsSolutionOn A B nu eta f g u h (Icc 0 T)) :
    ∀ t ∈ Icc (0 : ℝ) T, energy u h t
      ≤ energy u h 0 * Real.exp (-(decayRate nu eta lam) * t)
        + (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam ^ 2
          * (1 - Real.exp (-(decayRate nu eta lam) * t)) :=
  energy_le_forced hB (W := Set.univ) (fun v _ => hcoe v) hnu heta hlam hsol
    (fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩)

/-- **Theorem 4 (unforced coercive decay)** on a coercive phase space. -/
theorem energy_le_unforced_of_coercive (hB : IsCancelling B)
    (hcoe : ∀ v : E, lam * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) (hnu : 0 < nu) (heta : 0 < eta)
    (hlam : 0 < lam) {u h : ℝ → E} {T : ℝ}
    (hsol : IsSolutionOn A B nu eta (0 : E) (0 : E) u h (Icc 0 T)) :
    ∀ t ∈ Icc (0 : ℝ) T, energy u h t
      ≤ energy u h 0 * Real.exp (-(2 * decayRate nu eta lam) * t) :=
  energy_le_unforced hB (W := Set.univ) (fun v _ => hcoe v) hnu heta hlam hsol
    (fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩)

/-- **Theorem 3 (positively invariant absorbing ball)** on a coercive phase space. -/
theorem absorbing_ball_positively_invariant (hB : IsCancelling B)
    (hcoe : ∀ v : E, lam * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) (hnu : 0 < nu) (heta : 0 < eta)
    (hlam : 0 < lam) {u h : ℝ → E} {T R : ℝ}
    (hsol : IsSolutionOn A B nu eta f g u h (Icc 0 T))
    (hR : Real.sqrt (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate nu eta lam < R)
    (h0 : energy u h 0 ≤ R ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, energy u h t ≤ R ^ 2 :=
  energy_le_sq_of_le_sq hB (W := Set.univ) (fun v _ => hcoe v) hnu heta hlam hsol
    (fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩) hR h0

end Coercive

/-! ## Continuous dependence on bounded sets (§3.4) -/

section ContinuousDependence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E →L[ℝ] E} {B : E →L[ℝ] E →L[ℝ] E} {nu eta : ℝ} {f g : E}

/-- The difference of the two velocity fields is forcing free. -/
theorem velocityField_sub (u h ubar hbar : E) :
    velocityField A B nu f u h - velocityField A B nu f ubar hbar
      = -(nu • A (u - ubar)) + (B u u - B ubar ubar) - (B h h - B hbar hbar) := by
  simp only [velocityField, map_sub, smul_sub]
  abel

/-- The difference of the two magnetic fields is forcing free. -/
theorem magneticField_sub (u h ubar hbar : E) :
    magneticField A B eta g u h - magneticField A B eta g ubar hbar
      = -(eta • A (h - hbar)) + (B u h - B ubar hbar) - (B h u - B hbar ubar) := by
  simp only [magneticField, map_sub, smul_sub]
  abel

/-- The energy of the difference of two solutions is differentiable, with the expected
derivative. -/
theorem hasDerivAt_energyDiff {u h ubar hbar : ℝ → E} {t : ℝ}
    (hu : HasDerivAt u (velocityField A B nu f (u t) (h t)) t)
    (hh : HasDerivAt h (magneticField A B eta g (u t) (h t)) t)
    (hu2 : HasDerivAt ubar (velocityField A B nu f (ubar t) (hbar t)) t)
    (hh2 : HasDerivAt hbar (magneticField A B eta g (ubar t) (hbar t)) t) :
    HasDerivAt (fun s => ‖u s - ubar s‖ ^ 2 + ‖h s - hbar s‖ ^ 2)
      (2 * (⟪velocityField A B nu f (u t) (h t) - velocityField A B nu f (ubar t) (hbar t),
              u t - ubar t⟫_ℝ
            + ⟪magneticField A B eta g (u t) (h t) - magneticField A B eta g (ubar t) (hbar t),
              h t - hbar t⟫_ℝ)) t := by
  have hw := hu.sub hu2
  have hz := hh.sub hh2
  have hrw : (fun s => ‖u s - ubar s‖ ^ 2 + ‖h s - hbar s‖ ^ 2)
      = fun s => ⟪u s - ubar s, u s - ubar s⟫_ℝ + ⟪h s - hbar s, h s - hbar s⟫_ℝ := by
    funext s
    simp
  have s1 : ⟪u t - ubar t,
        velocityField A B nu f (u t) (h t) - velocityField A B nu f (ubar t) (hbar t)⟫_ℝ
      = ⟪velocityField A B nu f (u t) (h t) - velocityField A B nu f (ubar t) (hbar t),
        u t - ubar t⟫_ℝ := real_inner_comm _ _
  have s2 : ⟪h t - hbar t,
        magneticField A B eta g (u t) (h t) - magneticField A B eta g (ubar t) (hbar t)⟫_ℝ
      = ⟪magneticField A B eta g (u t) (h t) - magneticField A B eta g (ubar t) (hbar t),
        h t - hbar t⟫_ℝ := real_inner_comm _ _
  have hval : ⟪u t - ubar t,
        velocityField A B nu f (u t) (h t) - velocityField A B nu f (ubar t) (hbar t)⟫_ℝ
        + ⟪velocityField A B nu f (u t) (h t) - velocityField A B nu f (ubar t) (hbar t),
          u t - ubar t⟫_ℝ
      + (⟪h t - hbar t,
          magneticField A B eta g (u t) (h t) - magneticField A B eta g (ubar t) (hbar t)⟫_ℝ
        + ⟪magneticField A B eta g (u t) (h t) - magneticField A B eta g (ubar t) (hbar t),
          h t - hbar t⟫_ℝ)
      = 2 * (⟪velocityField A B nu f (u t) (h t) - velocityField A B nu f (ubar t) (hbar t),
              u t - ubar t⟫_ℝ
            + ⟪magneticField A B eta g (u t) (h t) - magneticField A B eta g (ubar t) (hbar t),
              h t - hbar t⟫_ℝ) := by
    rw [s1, s2]; ring
  rw [hrw, ← hval]
  exact (hw.inner ℝ hw).add (hz.inner ℝ hz)

/-- **Estimate (11).**  On a ball of radius `R` the difference energy obeys a linear differential
inequality with constant `8‖B‖R`. -/
theorem inner_field_diff_le (hA : ∀ v : E, 0 ≤ ⟪A v, v⟫_ℝ) (hnu : 0 ≤ nu) (heta : 0 ≤ eta)
    {R : ℝ} {u h ubar hbar : E} (hu : ‖u‖ ≤ R) (hh : ‖h‖ ≤ R) (hub : ‖ubar‖ ≤ R)
    (hhb : ‖hbar‖ ≤ R) :
    2 * (⟪velocityField A B nu f u h - velocityField A B nu f ubar hbar, u - ubar⟫_ℝ
        + ⟪magneticField A B eta g u h - magneticField A B eta g ubar hbar, h - hbar⟫_ℝ)
      ≤ 8 * ‖B‖ * R * (‖u - ubar‖ ^ 2 + ‖h - hbar‖ ^ 2) := by
  have hR : 0 ≤ R := le_trans (norm_nonneg u) hu
  have hBn : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  have hwn : 0 ≤ ‖u - ubar‖ := norm_nonneg _
  have hzn : 0 ≤ ‖h - hbar‖ := norm_nonneg _
  have hV : ⟪velocityField A B nu f u h - velocityField A B nu f ubar hbar, u - ubar⟫_ℝ
      = ⟪-(nu • A (u - ubar)), u - ubar⟫_ℝ + ⟪B u u - B ubar ubar, u - ubar⟫_ℝ
        - ⟪B h h - B hbar hbar, u - ubar⟫_ℝ := by
    rw [velocityField_sub, inner_sub_left, inner_add_left]
  have hM : ⟪magneticField A B eta g u h - magneticField A B eta g ubar hbar, h - hbar⟫_ℝ
      = ⟪-(eta • A (h - hbar)), h - hbar⟫_ℝ + ⟪B u h - B ubar hbar, h - hbar⟫_ℝ
        - ⟪B h u - B hbar ubar, h - hbar⟫_ℝ := by
    rw [magneticField_sub, inner_sub_left, inner_add_left]
  have d1 : ⟪-(nu • A (u - ubar)), u - ubar⟫_ℝ ≤ 0 := by
    rw [inner_neg_left, real_inner_smul_left]
    have := hA (u - ubar)
    nlinarith
  have d2 : ⟪-(eta • A (h - hbar)), h - hbar⟫_ℝ ≤ 0 := by
    rw [inner_neg_left, real_inner_smul_left]
    have := hA (h - hbar)
    nlinarith
  have q1 : ⟪B u u - B ubar ubar, u - ubar⟫_ℝ
      ≤ 2 * ‖B‖ * R * ‖u - ubar‖ * ‖u - ubar‖ := by
    refine le_trans (real_inner_le_norm _ _) ?_
    exact mul_le_mul_of_nonneg_right (norm_interaction_diag_sub_le B hu hub) hwn
  have q2 : -⟪B h h - B hbar hbar, u - ubar⟫_ℝ
      ≤ 2 * ‖B‖ * R * ‖h - hbar‖ * ‖u - ubar‖ := by
    refine le_trans (neg_le_abs _) (le_trans (abs_real_inner_le_norm _ _) ?_)
    exact mul_le_mul_of_nonneg_right (norm_interaction_diag_sub_le B hh hhb) hwn
  have q3 : ⟪B u h - B ubar hbar, h - hbar⟫_ℝ
      ≤ ‖B‖ * R * (‖u - ubar‖ + ‖h - hbar‖) * ‖h - hbar‖ := by
    refine le_trans (real_inner_le_norm _ _) ?_
    exact mul_le_mul_of_nonneg_right (norm_interaction_mixed_sub_le B hu hh hub hhb) hzn
  have q4 : -⟪B h u - B hbar ubar, h - hbar⟫_ℝ
      ≤ ‖B‖ * R * (‖h - hbar‖ + ‖u - ubar‖) * ‖h - hbar‖ := by
    refine le_trans (neg_le_abs _) (le_trans (abs_real_inner_le_norm _ _) ?_)
    exact mul_le_mul_of_nonneg_right (norm_interaction_mixed_sub_le B hh hu hhb hub) hzn
  rw [hV, hM]
  nlinarith [q1, q2, q3, q4, d1, d2, sq_nonneg (‖u - ubar‖ - ‖h - hbar‖), mul_nonneg hBn hR]

/-- **Continuous dependence, §3.4 estimate (11).**  Two solutions whose four component norms
stay bounded by `R` on `[0,T]` satisfy `E(t) ≤ E(0) e^{C R t}` with `C = 8‖B‖`. -/
theorem energy_diff_le (hA : ∀ v : E, 0 ≤ ⟪A v, v⟫_ℝ) (hnu : 0 ≤ nu) (heta : 0 ≤ eta)
    {u h ubar hbar : ℝ → E} {T R : ℝ}
    (hsol : IsSolutionOn A B nu eta f g u h (Icc 0 T))
    (hsol2 : IsSolutionOn A B nu eta f g ubar hbar (Icc 0 T))
    (hbu : ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R) (hbh : ∀ t ∈ Icc (0 : ℝ) T, ‖h t‖ ≤ R)
    (hbu2 : ∀ t ∈ Icc (0 : ℝ) T, ‖ubar t‖ ≤ R) (hbh2 : ∀ t ∈ Icc (0 : ℝ) T, ‖hbar t‖ ≤ R) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖u t - ubar t‖ ^ 2 + ‖h t - hbar t‖ ^ 2
      ≤ (‖u 0 - ubar 0‖ ^ 2 + ‖h 0 - hbar 0‖ ^ 2) * Real.exp (8 * ‖B‖ * R * t) := by
  have hderiv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s => ‖u s - ubar s‖ ^ 2 + ‖h s - hbar s‖ ^ 2)
        (2 * (⟪velocityField A B nu f (u t) (h t) - velocityField A B nu f (ubar t) (hbar t),
                u t - ubar t⟫_ℝ
              + ⟪magneticField A B eta g (u t) (h t)
                  - magneticField A B eta g (ubar t) (hbar t), h t - hbar t⟫_ℝ)) t :=
    fun t ht => hasDerivAt_energyDiff (hsol t ht).1 (hsol t ht).2 (hsol2 t ht).1 (hsol2 t ht).2
  have hcont : ContinuousOn (fun s => ‖u s - ubar s‖ ^ 2 + ‖h s - hbar s‖ ^ 2) (Icc 0 T) :=
    fun t ht => ((hderiv t ht).continuousAt).continuousWithinAt
  have hgb := le_gronwallBound_of_hasDerivAt
    (φ := fun s => ‖u s - ubar s‖ ^ 2 + ‖h s - hbar s‖ ^ 2)
    (φ' := fun t => 2 * (⟪velocityField A B nu f (u t) (h t)
            - velocityField A B nu f (ubar t) (hbar t), u t - ubar t⟫_ℝ
          + ⟪magneticField A B eta g (u t) (h t) - magneticField A B eta g (ubar t) (hbar t),
              h t - hbar t⟫_ℝ))
    (K := 8 * ‖B‖ * R) (c := 0) (T := T) hcont
    (fun t ht => hderiv t (Ico_subset_Icc_self ht))
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      have := inner_field_diff_le (A := A) (B := B) (nu := nu) (eta := eta) (f := f) (g := g)
        hA hnu heta (hbu t ht') (hbh t ht') (hbu2 t ht') (hbh2 t ht')
      linarith)
  intro t ht
  have hb := hgb t ht
  rwa [gronwallBound_ε0] at hb

/-- **§3.4 with any admissible constant.**  Any `C ≥ 8‖B‖` may be used in the continuous-dependence
estimate (11). -/
theorem energy_diff_le_const (hA : ∀ v : E, 0 ≤ ⟪A v, v⟫_ℝ) (hnu : 0 ≤ nu) (heta : 0 ≤ eta)
    {C : ℝ} (hC : 8 * ‖B‖ ≤ C) {u h ubar hbar : ℝ → E} {T R : ℝ} (hR0 : 0 ≤ R)
    (hsol : IsSolutionOn A B nu eta f g u h (Icc 0 T))
    (hsol2 : IsSolutionOn A B nu eta f g ubar hbar (Icc 0 T))
    (hbu : ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R) (hbh : ∀ t ∈ Icc (0 : ℝ) T, ‖h t‖ ≤ R)
    (hbu2 : ∀ t ∈ Icc (0 : ℝ) T, ‖ubar t‖ ≤ R) (hbh2 : ∀ t ∈ Icc (0 : ℝ) T, ‖hbar t‖ ≤ R) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖u t - ubar t‖ ^ 2 + ‖h t - hbar t‖ ^ 2
      ≤ (‖u 0 - ubar 0‖ ^ 2 + ‖h 0 - hbar 0‖ ^ 2) * Real.exp (C * R * t) := by
  intro t ht
  have hbase := energy_diff_le hA hnu heta hsol hsol2 hbu hbh hbu2 hbh2 t ht
  have hmono : 8 * ‖B‖ * R * t ≤ C * R * t := by
    have h1 : (0 : ℝ) ≤ R * t := mul_nonneg hR0 ht.1
    nlinarith
  have hexp : Real.exp (8 * ‖B‖ * R * t) ≤ Real.exp (C * R * t) := Real.exp_le_exp.mpr hmono
  have hD : (0 : ℝ) ≤ ‖u 0 - ubar 0‖ ^ 2 + ‖h 0 - hbar 0‖ ^ 2 := by positivity
  nlinarith [hbase, hexp, hD]

end ContinuousDependence

/-! ## The explicit constant `C_J = 16‖J‖` of §3.4 -/

section DiagConstant

variable {ι : Type*} [Fintype ι] {W : Submodule ℝ (EuclideanSpace ℝ ι)}
variable {A : ↥W →L[ℝ] ↥W} {J : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
variable {nu eta : ℝ} {f g : ↥W}

/-- **§3.4, the paper's constant.**  For the diagonal anticommutator realization of Proposition 1
the continuous-dependence estimate (11) holds with `C_J = 16‖J‖`. -/
theorem energy_diff_le_diagAnticommutator (hA : ∀ v : ↥W, 0 ≤ ⟪A v, v⟫_ℝ) (hnu : 0 ≤ nu)
    (heta : 0 ≤ eta) {u h ubar hbar : ℝ → ↥W} {T R : ℝ} (hR0 : 0 ≤ R)
    (hsol : IsSolutionOn A (projectedInteraction W (anticommutator (diagOp ι) J)) nu eta f g
      u h (Icc 0 T))
    (hsol2 : IsSolutionOn A (projectedInteraction W (anticommutator (diagOp ι) J)) nu eta f g
      ubar hbar (Icc 0 T))
    (hbu : ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R) (hbh : ∀ t ∈ Icc (0 : ℝ) T, ‖h t‖ ≤ R)
    (hbu2 : ∀ t ∈ Icc (0 : ℝ) T, ‖ubar t‖ ≤ R) (hbh2 : ∀ t ∈ Icc (0 : ℝ) T, ‖hbar t‖ ≤ R) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖u t - ubar t‖ ^ 2 + ‖h t - hbar t‖ ^ 2
      ≤ (‖u 0 - ubar 0‖ ^ 2 + ‖h 0 - hbar 0‖ ^ 2) * Real.exp (16 * ‖J‖ * R * t) := by
  refine energy_diff_le_const hA hnu heta ?_ hR0 hsol hsol2 hbu hbh hbu2 hbh2
  have := opNorm_diagAnticommutatorInteraction_le W J
  linarith

end DiagConstant


/-! ## The a priori bound for the rescaled system -/

section Scaled

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E →L[ℝ] E} {B : E →L[ℝ] E →L[ℝ] E} {nu eta : ℝ} {f g : E} {c : ℝ → ℝ}

theorem IsSolutionOn.isScaledSolutionOn {u h : ℝ → E} {s : Set ℝ}
    (hsol : IsSolutionOn A B nu eta f g u h s) :
    IsScaledSolutionOn A B nu eta f g (fun _ => 1) u h s := by
  intro t ht
  exact ⟨by simpa using (hsol t ht).1, by simpa using (hsol t ht).2⟩

theorem continuousOn_energy_scaled (hB : IsCancelling B) {u h : ℝ → E} {s : Set ℝ}
    (hsol : IsScaledSolutionOn A B nu eta f g c u h s) : ContinuousOn (energy u h) s := by
  intro t ht
  exact ((hasDerivAt_energy_smul hB (hsol t ht).1 (hsol t ht).2).continuousAt).continuousWithinAt

/-- **The a priori bound.**  For any rescaling `0 ≤ c ≤ 1` of the vector field, the energy of a
solution grows at most exponentially.  This is the estimate that rules out finite-time blow-up,
and it is what makes the truncated system of `GlobalExistence.lean` stay in a fixed ball. -/
theorem energy_le_apriori_scaled (hB : IsCancelling B) (hA : ∀ v : E, 0 ≤ ⟪A v, v⟫_ℝ)
    (hnu : 0 ≤ nu) (heta : 0 ≤ eta) (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1)
    {u h : ℝ → E} {T : ℝ}
    (hsol : IsScaledSolutionOn A B nu eta f g c u h (Icc 0 T)) :
    ∀ t ∈ Icc (0 : ℝ) T, energy u h t
      ≤ energy u h 0 * Real.exp t + (‖f‖ ^ 2 + ‖g‖ ^ 2) * (Real.exp t - 1) := by
  have hgb := le_gronwallBound_of_hasDerivAt (φ := energy u h)
    (φ' := fun t => 2 * c t * (-(dissipation A nu eta u h t) + forcingPower f g u h t))
    (K := 1) (c := ‖f‖ ^ 2 + ‖g‖ ^ 2) (T := T)
    (continuousOn_energy_scaled hB hsol)
    (fun t ht => hasDerivAt_energy_smul hB (hsol t (Ico_subset_Icc_self ht)).1
      (hsol t (Ico_subset_Icc_self ht)).2)
    (fun t _ => by
      have hd := dissipation_nonneg hA hnu heta u h t
      have hfu : ⟪f, u t⟫_ℝ ≤ ‖f‖ * ‖u t‖ := real_inner_le_norm _ _
      have hgh : ⟪g, h t⟫_ℝ ≤ ‖g‖ * ‖h t‖ := real_inner_le_norm _ _
      have y1 : 2 * (‖f‖ * ‖u t‖) ≤ ‖u t‖ ^ 2 + ‖f‖ ^ 2 := by
        nlinarith [sq_nonneg (‖u t‖ - ‖f‖)]
      have y2 : 2 * (‖g‖ * ‖h t‖) ≤ ‖h t‖ ^ 2 + ‖g‖ ^ 2 := by
        nlinarith [sq_nonneg (‖h t‖ - ‖g‖)]
      have hPle : 2 * forcingPower f g u h t ≤ 1 * energy u h t + (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
        simp only [forcingPower, energy]
        linarith
      have hEnn : 0 ≤ 1 * energy u h t + (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
        have : 0 ≤ energy u h t := by
          simp only [energy]; positivity
        nlinarith [sq_nonneg ‖f‖, sq_nonneg ‖g‖]
      nlinarith [hc0 t, hc1 t, hd, hPle, hEnn])
  intro t ht
  have hb := hgb t ht
  rw [gronwallBound_of_K_ne_0 (one_ne_zero)] at hb
  simpa using hb

end Scaled

end GaloisForLFunctions.HTGeometry.HodgeEdgeCochain
