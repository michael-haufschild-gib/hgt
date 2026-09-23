import GaloisForLFunctions.HTGeometry.HodgeEdgeCochain.Energy
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Harmonic affine fibres in the noncoercive case

This file formalises §5 of Boudourides, *Hodge Coercivity and Global Dynamics in Two-Field
Edge-Cochain Systems with MHD-Type Cancellation* (arXiv:2608.19360).

When the harmonic space `H¹` is nontrivial the Hodge Laplacian does not damp the harmonic
directions, and equations (17)–(18) show that a general admissible interaction can still move
energy in and out of them.  The *harmonic-decoupled* interaction

```text
B₀(a,b) = P₀ B̃(P₀ a, P₀ b)
```

removes every nonlinear input to the harmonic equation, so each affine fibre
`X = {(u,h) : Qu = u_H, Qh = h_H}` becomes invariant and carries the coercive reduced dynamics.

## Main results

* `hasDerivAt_harmonic_component` — equations (17)–(18).
* `isCancelling_decoupled`, `harmonic_decoupled_range` — **Lemma 3**.
* `harmonic_component_const` — **Theorem 5**: the affine fibre is positively invariant.
* `isSolutionOn_reduced` — the reduced system (20)–(21).
* `fibre_energy_le_unforced`, `fibre_converges` — the fibre-wise exponential decay to the
  harmonic label at rate `2β₊`.
* `fibre_absorbing_ball` — the forced fibre-wise absorbing ball.
-/

open Set
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry.HodgeEdgeCochain

section Fibre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {A : E →L[ℝ] E} {Bt : E →L[ℝ] E →L[ℝ] E} {nu eta lam : ℝ} {f g : E}
variable {P0 Q : E →L[ℝ] E}

/-! ## Equations (17)–(18) -/

/-- **Equations (17)–(18).**  Applying the harmonic projector to the velocity equation leaves only
the nonlinear and forcing contributions: harmonic modes are undamped by `Δ`, but for a general
admissible interaction they are not conserved either. -/
theorem hasDerivAt_harmonic_component (hQA : ∀ x : E, Q (A x) = 0)
    {B : E →L[ℝ] E →L[ℝ] E} {u h : ℝ → E} {t : ℝ}
    (hu : HasDerivAt u (velocityField A B nu f (u t) (h t)) t) :
    HasDerivAt (fun s => Q (u s)) (Q (B (u t) (u t)) - Q (B (h t) (h t)) + Q f) t := by
  have hcomp := Q.hasFDerivAt.comp_hasDerivAt t hu
  have hval : Q (velocityField A B nu f (u t) (h t))
      = Q (B (u t) (u t)) - Q (B (h t) (h t)) + Q f := by
    simp only [velocityField, map_add, map_sub, map_neg, map_smul, hQA]
    simp
  rw [← hval]
  simpa [Function.comp_def] using hcomp

/-- The magnetic half of (17)–(18). -/
theorem hasDerivAt_harmonic_component' (hQA : ∀ x : E, Q (A x) = 0)
    {B : E →L[ℝ] E →L[ℝ] E} {u h : ℝ → E} {t : ℝ}
    (hh : HasDerivAt h (magneticField A B eta g (u t) (h t)) t) :
    HasDerivAt (fun s => Q (h s)) (Q (B (u t) (h t)) - Q (B (h t) (u t)) + Q g) t := by
  have hcomp := Q.hasFDerivAt.comp_hasDerivAt t hh
  have hval : Q (magneticField A B eta g (u t) (h t))
      = Q (B (u t) (h t)) - Q (B (h t) (u t)) + Q g := by
    simp only [magneticField, map_add, map_sub, map_neg, map_smul, hQA]
    simp
  rw [← hval]
  simpa [Function.comp_def] using hcomp

/-! ## The harmonic-decoupled interaction (19) -/

/-- The bilinear map `(a,b) ↦ P₀ B̃(P₀ a, P₀ b)` of equation (19). -/
noncomputable def decoupledBil (P0 : E →L[ℝ] E) (Bt : E →L[ℝ] E →L[ℝ] E) :
    E →ₗ[ℝ] E →ₗ[ℝ] E where
  toFun a :=
    { toFun := fun b => P0 (Bt (P0 a) (P0 b))
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  map_add' := by intro x y; ext b; simp
  map_smul' := by intro c x; ext b; simp

/-- The harmonic-decoupled interaction `B₀` of equation (19). -/
noncomputable def decoupled (P0 : E →L[ℝ] E) (Bt : E →L[ℝ] E →L[ℝ] E) :
    E →L[ℝ] E →L[ℝ] E := bilinearCLM (decoupledBil P0 Bt)

@[simp] theorem decoupled_apply (P0 : E →L[ℝ] E) (Bt : E →L[ℝ] E →L[ℝ] E) (a b : E) :
    decoupled P0 Bt a b = P0 (Bt (P0 a) (P0 b)) := rfl

/-- **Lemma 3 (decoupled cancellation).**  `B₀` satisfies the trilinear antisymmetry (4). -/
theorem isCancelling_decoupled (hsymm : ∀ x y : E, ⟪P0 x, y⟫_ℝ = ⟪x, P0 y⟫_ℝ)
    (hB : IsCancelling Bt) : IsCancelling (decoupled P0 Bt) := by
  intro a b c
  rw [decoupled_apply, decoupled_apply, hsymm, hsymm]
  exact hB (P0 a) (P0 b) (P0 c)

/-- **Lemma 3 (range).**  `Q B₀ = 0`: the decoupled interaction feeds nothing into the harmonic
equation. -/
theorem harmonic_decoupled_range (hQP : ∀ x : E, Q (P0 x) = 0)
    (Bt : E →L[ℝ] E →L[ℝ] E) (a b : E) : Q (decoupled P0 Bt a b) = 0 := hQP _

/-! ## Theorem 5: invariant fibres and the reduced system -/

/-- **Theorem 5 (invariant harmonic fibres).**  With the decoupled interaction and harmonic-free
forcing, the harmonic components of every solution are constant, so each affine fibre
`{Qu = u_H, Qh = h_H}` is positively invariant. -/
theorem harmonic_component_const (hQP : ∀ x : E, Q (P0 x) = 0) (hQA : ∀ x : E, Q (A x) = 0)
    (hQf : Q f = 0) (hQg : Q g = 0) {u h : ℝ → E} {T : ℝ}
    (hsol : IsSolutionOn A (decoupled P0 Bt) nu eta f g u h (Icc 0 T)) :
    (∀ t ∈ Icc (0 : ℝ) T, Q (u t) = Q (u 0)) ∧ ∀ t ∈ Icc (0 : ℝ) T, Q (h t) = Q (h 0) := by
  have hdu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (fun s => Q (u s)) 0 t := by
    intro t ht
    have := hasDerivAt_harmonic_component (Q := Q) hQA (hsol t ht).1
    rwa [harmonic_decoupled_range hQP Bt _ _, harmonic_decoupled_range hQP Bt _ _, hQf,
      sub_zero, add_zero] at this
  have hdh : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (fun s => Q (h s)) 0 t := by
    intro t ht
    have := hasDerivAt_harmonic_component' (Q := Q) (eta := eta) hQA (hsol t ht).2
    rwa [harmonic_decoupled_range hQP Bt _ _, harmonic_decoupled_range hQP Bt _ _, hQg,
      sub_zero, add_zero] at this
  constructor
  · refine constant_of_has_deriv_right_zero
      (fun t ht => ((hdu t ht).continuousAt).continuousWithinAt)
      (fun t ht => ((hdu t (Ico_subset_Icc_self ht)).hasDerivWithinAt))
  · refine constant_of_has_deriv_right_zero
      (fun t ht => ((hdh t ht).continuousAt).continuousWithinAt)
      (fun t ht => ((hdh t (Ico_subset_Icc_self ht)).hasDerivWithinAt))

/-- **Equations (20)–(21).**  The complementary components solve the same system with the
projected forcings, and no coefficient depends on the harmonic label. -/
theorem isSolutionOn_reduced (hP0 : ∀ x : E, P0 (P0 x) = P0 x)
    (hPA : ∀ x : E, P0 (A x) = A (P0 x)) {u h : ℝ → E} {s : Set ℝ}
    (hsol : IsSolutionOn A (decoupled P0 Bt) nu eta f g u h s) :
    IsSolutionOn A (decoupled P0 Bt) nu eta (P0 f) (P0 g)
      (fun t => P0 (u t)) (fun t => P0 (h t)) s := by
  intro t ht
  have hu := (hsol t ht).1
  have hh := (hsol t ht).2
  have hvel : P0 (velocityField A (decoupled P0 Bt) nu f (u t) (h t))
      = velocityField A (decoupled P0 Bt) nu (P0 f) (P0 (u t)) (P0 (h t)) := by
    simp only [velocityField, map_add, map_sub, map_neg, map_smul, decoupled_apply, hPA, hP0]
  have hmag : P0 (magneticField A (decoupled P0 Bt) eta g (u t) (h t))
      = magneticField A (decoupled P0 Bt) eta (P0 g) (P0 (u t)) (P0 (h t)) := by
    simp only [magneticField, map_add, map_sub, map_neg, map_smul, decoupled_apply, hPA, hP0]
  constructor
  · have := P0.hasFDerivAt.comp_hasDerivAt t hu
    rw [← hvel]
    simpa [Function.comp_def] using this
  · have := P0.hasFDerivAt.comp_hasDerivAt t hh
    rw [← hmag]
    simpa [Function.comp_def] using this

/-! ## Theorem 5: fibre-wise attractors -/

/-- **Theorem 5 (unforced fibre decay).**  On each harmonic fibre the complementary energy decays
exponentially at the rate `2β₊ = 2 min(ν,η) λ₊`. -/
theorem fibre_energy_le_unforced (hP0 : ∀ x : E, P0 (P0 x) = P0 x)
    (hPA : ∀ x : E, P0 (A x) = A (P0 x))
    (hsymm : ∀ x y : E, ⟪P0 x, y⟫_ℝ = ⟪x, P0 y⟫_ℝ) (hB : IsCancelling Bt)
    (hcoe : ∀ v ∈ Set.range (P0 : E → E), lam * ‖v‖ ^ (2 : ℕ) ≤ ⟪A v, v⟫_ℝ)
    (hnu : 0 < nu) (heta : 0 < eta) (hlam : 0 < lam) {u h : ℝ → E} {T : ℝ}
    (hsol : IsSolutionOn A (decoupled P0 Bt) nu eta (0 : E) (0 : E) u h (Icc 0 T)) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖P0 (u t)‖ ^ (2 : ℕ) + ‖P0 (h t)‖ ^ (2 : ℕ)
      ≤ (‖P0 (u 0)‖ ^ (2 : ℕ) + ‖P0 (h 0)‖ ^ (2 : ℕ))
        * Real.exp (-(2 * decayRate nu eta lam) * t) := by
  have hred := isSolutionOn_reduced hP0 hPA hsol
  simp only [map_zero] at hred
  have hkey := energy_le_unforced (isCancelling_decoupled hsymm hB) hcoe hnu heta hlam hred
    (fun t _ => ⟨⟨u t, rfl⟩, ⟨h t, rfl⟩⟩)
  simpa [energy] using hkey

/-- **Theorem 5 (convergence to the harmonic label).**  Every unforced trajectory on the fibre
`X_{u_H,h_H}` converges to `(u_H, h_H)`. -/
theorem fibre_converges (hP0 : ∀ x : E, P0 (P0 x) = P0 x)
    (hPA : ∀ x : E, P0 (A x) = A (P0 x)) (hQP : ∀ x : E, Q (P0 x) = 0)
    (hQA : ∀ x : E, Q (A x) = 0) (hsum : ∀ x : E, Q x + P0 x = x)
    (hsymm : ∀ x y : E, ⟪P0 x, y⟫_ℝ = ⟪x, P0 y⟫_ℝ) (hB : IsCancelling Bt)
    (hcoe : ∀ v ∈ Set.range (P0 : E → E), lam * ‖v‖ ^ (2 : ℕ) ≤ ⟪A v, v⟫_ℝ)
    (hnu : 0 < nu) (heta : 0 < eta) (hlam : 0 < lam) {u h : ℝ → E} {T : ℝ}
    (hsol : IsSolutionOn A (decoupled P0 Bt) nu eta (0 : E) (0 : E) u h (Icc 0 T)) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖u t - Q (u 0)‖ ^ (2 : ℕ) + ‖h t - Q (h 0)‖ ^ (2 : ℕ)
      ≤ (‖u 0 - Q (u 0)‖ ^ (2 : ℕ) + ‖h 0 - Q (h 0)‖ ^ (2 : ℕ))
        * Real.exp (-(2 * decayRate nu eta lam) * t) := by
  have hconst := harmonic_component_const hQP hQA (by simp) (by simp) hsol
  have hsplit : ∀ (w : ℝ → E) (t : ℝ), Q (w t) = Q (w 0) → w t - Q (w 0) = P0 (w t) := by
    intro w t hq
    have := hsum (w t)
    rw [hq] at this
    linear_combination (norm := abel) -this
  have hdecay := fibre_energy_le_unforced hP0 hPA hsymm hB hcoe hnu heta hlam hsol
  intro t ht
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, ht.1.trans ht.2⟩
  rw [hsplit u t (hconst.1 t ht), hsplit h t (hconst.2 t ht),
    hsplit u 0 (hconst.1 0 h0mem), hsplit h 0 (hconst.2 0 h0mem)]
  exact hdecay t ht

/-- **Theorem 5 (forced fibre-wise absorbing ball).**  With the harmonic label fixed, the
complementary variables obey the coercive absorbing estimate on `V₀`. -/
theorem fibre_absorbing_ball (hP0 : ∀ x : E, P0 (P0 x) = P0 x)
    (hPA : ∀ x : E, P0 (A x) = A (P0 x))
    (hsymm : ∀ x y : E, ⟪P0 x, y⟫_ℝ = ⟪x, P0 y⟫_ℝ) (hB : IsCancelling Bt)
    (hcoe : ∀ v ∈ Set.range (P0 : E → E), lam * ‖v‖ ^ (2 : ℕ) ≤ ⟪A v, v⟫_ℝ)
    (hnu : 0 < nu) (heta : 0 < eta) (hlam : 0 < lam) {u h : ℝ → E} {T R : ℝ}
    (hsol : IsSolutionOn A (decoupled P0 Bt) nu eta f g u h (Icc 0 T))
    (hR : Real.sqrt (‖P0 f‖ ^ (2 : ℕ) + ‖P0 g‖ ^ (2 : ℕ)) / decayRate nu eta lam < R)
    (h0 : ‖P0 (u 0)‖ ^ (2 : ℕ) + ‖P0 (h 0)‖ ^ (2 : ℕ) ≤ R ^ (2 : ℕ)) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖P0 (u t)‖ ^ (2 : ℕ) + ‖P0 (h t)‖ ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := by
  have hred := isSolutionOn_reduced hP0 hPA hsol
  have hkey := energy_le_sq_of_le_sq (isCancelling_decoupled hsymm hB) hcoe hnu heta hlam hred
    (fun t _ => ⟨⟨u t, rfl⟩, ⟨h t, rfl⟩⟩) hR (by simpa [energy] using h0)
  intro t ht
  simpa [energy] using hkey t ht

/-- **§5.2 (spectrum of the linearization).**  Every eigenvalue of the block-diagonal
linearization `diag(-ν Δ|V₀, -η Δ|V₀)` at the fibre equilibrium is at most `-β₊`. -/
theorem eigenvalue_le_neg_decayRate {W : Set E}
    (hcoe : ∀ v ∈ W, lam * ‖v‖ ^ (2 : ℕ) ≤ ⟪A v, v⟫_ℝ) (hnu : 0 < nu) (heta : 0 < eta)
    (hlam : 0 ≤ lam) {mu : ℝ} {v w : E} (hv : v ∈ W) (hw : w ∈ W)
    (hne : ¬ (v = 0 ∧ w = 0))
    (hev : -(nu • A v) = mu • v) (hew : -(eta • A w) = mu • w) :
    mu ≤ -(decayRate nu eta lam) := by
  have h1 : -(nu * ⟪A v, v⟫_ℝ) = mu * ‖v‖ ^ (2 : ℕ) := by
    have := congrArg (fun z => ⟪z, v⟫_ℝ) hev
    simpa [inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq] using this
  have h2 : -(eta * ⟪A w, w⟫_ℝ) = mu * ‖w‖ ^ (2 : ℕ) := by
    have := congrArg (fun z => ⟪z, w⟫_ℝ) hew
    simpa [inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq] using this
  have hcv := hcoe v hv
  have hcw := hcoe w hw
  have hmin1 : min nu eta ≤ nu := min_le_left _ _
  have hmin2 : min nu eta ≤ eta := min_le_right _ _
  have hvn : (0 : ℝ) ≤ ‖v‖ ^ (2 : ℕ) := by positivity
  have hwn : (0 : ℝ) ≤ ‖w‖ ^ (2 : ℕ) := by positivity
  have hpos : 0 < ‖v‖ ^ (2 : ℕ) + ‖w‖ ^ (2 : ℕ) := by
    rcases not_and_or.mp hne with hv0 | hw0
    · have : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      nlinarith
    · have : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      nlinarith
  have hd1 : min nu eta * (lam * ‖v‖ ^ (2 : ℕ)) ≤ nu * ⟪A v, v⟫_ℝ := by
    have hpv : (0 : ℝ) ≤ lam * ‖v‖ ^ (2 : ℕ) := mul_nonneg hlam hvn
    nlinarith
  have hd2 : min nu eta * (lam * ‖w‖ ^ (2 : ℕ)) ≤ eta * ⟪A w, w⟫_ℝ := by
    have hpw : (0 : ℝ) ≤ lam * ‖w‖ ^ (2 : ℕ) := mul_nonneg hlam hwn
    nlinarith
  have hkey : mu * (‖v‖ ^ (2 : ℕ) + ‖w‖ ^ (2 : ℕ))
      ≤ -(decayRate nu eta lam) * (‖v‖ ^ (2 : ℕ) + ‖w‖ ^ (2 : ℕ)) := by
    simp only [decayRate]
    nlinarith
  nlinarith [hkey, hpos]

end Fibre

end GaloisForLFunctions.HTGeometry.HodgeEdgeCochain
