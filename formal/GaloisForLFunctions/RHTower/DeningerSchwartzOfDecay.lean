import GaloisForLFunctions.RHTower.DeningerLandauInterpolation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Rapid decay plus bounded derivatives is Schwartz

A smooth function all of whose derivatives are bounded and which itself decays faster than every
power is automatically Schwartz: the Landau interpolation with the shrinking window `δ = x^{-B}`
converts the decay of `u` at order `2B` into the decay of `u'` at order `B`, and the induction runs
through all derivative orders.

This is the exact shape produced by a Fourier transform: `ℱv` has bounded derivatives of every
order as soon as `v` has all moments, so only the decay of the function itself has to be supplied
by hand.

* `deningerDecayRight_iteratedDeriv` : **decay propagates to every derivative.**
* `deningerSchwartzOfDecay` : **the Schwartz map built from decay and bounded derivatives.**
-/

namespace RHTower

open SchwartzMap

open scoped ContDiff

noncomputable section

/-- The iterated derivatives of a smooth function are smooth. -/
theorem deningerIteratedDeriv_contDiff {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (r : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv r u) := by
  rw [iteratedDeriv_eq_iterate]
  exact hu.iterate_deriv r

/-- **Decay on the right ray propagates to every derivative.** -/
theorem deningerDecayRight_iteratedDeriv {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hbd : ∀ r : ℕ, ∃ M : ℝ, ∀ x : ℝ, ‖iteratedDeriv r u x‖ ≤ M)
    (hdec : ∀ B : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖u x‖ ≤ C / x ^ B) :
    ∀ (r B : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖iteratedDeriv r u x‖ ≤ C / x ^ B := by
  intro r
  induction r with
  | zero =>
    intro B
    obtain ⟨C, hCnn, hC⟩ := hdec B
    exact ⟨C, hCnn, fun x hx => by simpa using hC x hx⟩
  | succ r ih =>
    intro B
    obtain ⟨C', hC'nn, hC'⟩ := ih (2 * B)
    obtain ⟨M, hM⟩ := hbd (r + 2)
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
    refine ⟨2 * C' + M, by positivity, fun x hx => ?_⟩
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hxB : (0 : ℝ) < x ^ B := by positivity
    set δ : ℝ := 1 / x ^ B with hδdef
    have hδpos : 0 < δ := by positivity
    have hδle : δ ≤ 1 := by
      rw [hδdef, div_le_one hxB]
      exact one_le_pow₀ hx
    have hsmooth : ContDiff ℝ ∞ (iteratedDeriv r u) := deningerIteratedDeriv_contDiff hu r
    have hsecond : ∀ y : ℝ, ‖deriv (deriv (iteratedDeriv r u)) y‖ ≤ M := by
      intro y
      have h1 : deriv (iteratedDeriv r u) = iteratedDeriv (r + 1) u :=
        (iteratedDeriv_succ (n := r) (f := u)).symm
      have h2 : deriv (iteratedDeriv (r + 1) u) = iteratedDeriv (r + 2) u :=
        (iteratedDeriv_succ (n := r + 1) (f := u)).symm
      rw [h1, h2]
      exact hM y
    have hwindow : ∀ y ∈ Set.Icc x (x + δ),
        ‖iteratedDeriv r u y‖ ≤ C' / x ^ (2 * B) := by
      intro y hy
      have hy1 : (1 : ℝ) ≤ y := le_trans hx hy.1
      refine le_trans (hC' y hy1) ?_
      have hmono : x ^ (2 * B) ≤ y ^ (2 * B) := pow_le_pow_left₀ (by linarith) hy.1 _
      exact div_le_div_of_nonneg_left hC'nn (by positivity) hmono
    have hlandau := deningerLandau_deriv_le hsmooth hsecond hδpos hwindow
    have hderiv : deriv (iteratedDeriv r u) x = iteratedDeriv (r + 1) u x := by
      rw [(iteratedDeriv_succ (n := r) (f := u)).symm]
    rw [hderiv] at hlandau
    refine le_trans hlandau (le_of_eq ?_)
    have hsq : x ^ (2 * B) = x ^ B * x ^ B := by
      rw [two_mul, pow_add]
    rw [hδdef, hsq]
    field_simp

/-! ## The Schwartz map -/

/-- **A smooth function with bounded derivatives which decays faster than every power on both rays
is Schwartz.** -/
def deningerSchwartzOfDecay (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hbd : ∀ r : ℕ, ∃ M : ℝ, ∀ x : ℝ, ‖iteratedDeriv r u x‖ ≤ M)
    (hR : ∀ B : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖u x‖ ≤ C / x ^ B)
    (hL : ∀ B : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖u (-x)‖ ≤ C / x ^ B) :
    𝓢(ℝ, ℂ) where
  toFun := u
  smooth' := hu
  decay' k n := by
    have hunegsmooth : ContDiff ℝ ∞ fun x : ℝ => u (-x) := hu.comp contDiff_neg
    have hnegderiv : ∀ (r : ℕ) (x : ℝ),
        ‖iteratedDeriv r (fun y : ℝ => u (-y)) x‖ = ‖iteratedDeriv r u (-x)‖ := by
      intro r x
      rw [iteratedDeriv_comp_neg r u x, norm_smul]
      simp
    have hnegbd : ∀ r : ℕ, ∃ M : ℝ, ∀ x : ℝ,
        ‖iteratedDeriv r (fun y : ℝ => u (-y)) x‖ ≤ M := by
      intro r
      obtain ⟨M, hM⟩ := hbd r
      exact ⟨M, fun x => by rw [hnegderiv r x]; exact hM (-x)⟩
    obtain ⟨CR, hCRnn, hCR⟩ := deningerDecayRight_iteratedDeriv hu hbd hR n k
    obtain ⟨CL, hCLnn, hCL⟩ :=
      deningerDecayRight_iteratedDeriv hunegsmooth hnegbd hL n k
    obtain ⟨M, hM⟩ := hbd n
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
    refine ⟨max (max CR CL) M, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    rcases le_total 1 |x| with hbig | hsmall
    · rcases le_total 0 x with hpos | hneg
      · have hx1 : (1 : ℝ) ≤ x := by rwa [abs_of_nonneg hpos] at hbig
        have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
        have hbound := hCR x hx1
        rw [Real.norm_eq_abs, abs_of_nonneg hpos]
        rw [div_eq_mul_inv] at hbound
        have hxk : (0 : ℝ) < x ^ k := by positivity
        calc x ^ k * ‖iteratedDeriv n u x‖ ≤ x ^ k * (CR / x ^ k) :=
              mul_le_mul_of_nonneg_left (hCR x hx1) (by positivity)
          _ = CR := by field_simp
          _ ≤ max (max CR CL) M := le_trans (le_max_left _ _) (le_max_left _ _)
      · have hx1 : (1 : ℝ) ≤ -x := by rwa [abs_of_nonpos hneg] at hbig
        have hxk : (0 : ℝ) < (-x) ^ k := by positivity
        have hbound := hCL (-x) hx1
        rw [hnegderiv n (-x), neg_neg] at hbound
        rw [Real.norm_eq_abs, abs_of_nonpos hneg]
        calc (-x) ^ k * ‖iteratedDeriv n u x‖ ≤ (-x) ^ k * (CL / (-x) ^ k) :=
              mul_le_mul_of_nonneg_left hbound (by positivity)
          _ = CL := by field_simp
          _ ≤ max (max CR CL) M := le_trans (le_max_right _ _) (le_max_left _ _)
    · have hxk : ‖x‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (by rwa [Real.norm_eq_abs])
      calc ‖x‖ ^ k * ‖iteratedDeriv n u x‖ ≤ 1 * M :=
            mul_le_mul hxk (hM x) (norm_nonneg _) zero_le_one
        _ = M := one_mul M
        _ ≤ max (max CR CL) M := le_max_right _ _

@[simp]
theorem deningerSchwartzOfDecay_apply (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hbd : ∀ r : ℕ, ∃ M : ℝ, ∀ x : ℝ, ‖iteratedDeriv r u x‖ ≤ M)
    (hR : ∀ B : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖u x‖ ≤ C / x ^ B)
    (hL : ∀ B : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖u (-x)‖ ≤ C / x ^ B) (x : ℝ) :
    deningerSchwartzOfDecay u hu hbd hR hL x = u x := rfl

end

end RHTower
