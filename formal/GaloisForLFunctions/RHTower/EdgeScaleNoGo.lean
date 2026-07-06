/-
The sharp scale of the edge forcing engine.

The monotone-phase engine forces band-edge events at one per phase advance `π`, so its
resolution is the phase-π quantum `π/ρ₀`.  This module certifies the quantum sharp from
below: on any edge segment where the rate floor `ρ₀` advances the phase by less than `π`,
NOTHING is forced.  The witness carrier realises the floor exactly and keeps its incidence
phase inside a single open π-interval, so the incidence value stays off the real axis along
the whole segment and no member of the real-ratio pencil vanishes there — an instance
satisfying every hypothesis of the forcing engine, endpoint-orientation agreement included,
with an empty event set.  Consequently a consumer demanding events inside windows shorter
than `π/ρ₀` cannot be fed by this engine: the producer's scale is the phase-π quantum, and
below it the rate floor constrains nothing.
-/
import GaloisForLFunctions.RHTower.LateralWindingFloor
import GaloisForLFunctions.RHTower.MirrorPencil

open Complex Metric

namespace RHTower

/-- No member of the real-ratio pencil vanishes at a point where the incidence value is
off the real axis: the member through a real ratio `c` vanishes exactly on the level set
`incidence = c`, and a nonreal value meets no real level. -/
theorem pencil_real_member_ne_zero_of_im_ne_zero {Λ₁ Λ₂ : ℂ → ℂ} {s₀ : ℂ}
    (hΛ : Λ₁ s₀ ≠ 0) (him : (incidence Λ₁ Λ₂ s₀).im ≠ 0) (c : ℝ) :
    pencil Λ₁ Λ₂ (c : ℂ) 1 s₀ ≠ 0 := by
  intro h0
  have hc := (pencil_eq_zero_iff_incidence one_ne_zero hΛ).mp h0
  rw [div_one] at hc
  exact him (by rw [← hc, Complex.ofReal_im])

/-- **The engine forces nothing below the phase-π quantum.**  On any lateral edge segment
whose length times the rate floor stays below `π`, there is a carrier pair meeting every
hypothesis of the edge forcing engine — entire, nonvanishing, rate floor `ρ₀` attained,
endpoint orientations agreeing — whose incidence value has strictly positive imaginary
part along the whole segment, so that NO member of the real-ratio pencil vanishes
anywhere on it.  The witness is the pure phase carrier `exp(ρ₀(z−σ−ia) + iθₐ)` with the
launch angle `θₐ = (π − ρ₀(b−a))/2` centring the phase run `[θₐ, π−θₐ]` inside `(0,π)`:
the phase advances at exactly the floor rate and never completes a half-turn. -/
theorem short_window_engine_no_events {σ a b ρ₀ : ℝ} (hab : a < b) (hρ : 0 < ρ₀)
    (hshort : ρ₀ * (b - a) < Real.pi) :
    ∃ Λ₁ Λ₂ : ℂ → ℂ,
      AnalyticOnNhd ℂ Λ₁ Set.univ ∧ (∀ z ∈ Set.univ, Λ₁ z ≠ 0) ∧
      AnalyticOnNhd ℂ Λ₂ Set.univ ∧ (∀ z ∈ Set.univ, Λ₂ z ≠ 0) ∧
      (∀ τ ∈ Set.Icc a b,
        ρ₀ ≤ (logDeriv Λ₂ (stripPt σ τ) - logDeriv Λ₁ (stripPt σ τ)).re) ∧
      (0 < (incidence Λ₁ Λ₂ (stripPt σ a)).im ↔
        0 < (incidence Λ₁ Λ₂ (stripPt σ b)).im) ∧
      ∀ τ ∈ Set.Icc a b, ∀ c : ℝ, pencil Λ₁ Λ₂ (c : ℂ) 1 (stripPt σ τ) ≠ 0 := by
  set θa : ℝ := (Real.pi - ρ₀ * (b - a)) / 2 with hθa_def
  have hθa : 0 < θa := by rw [hθa_def]; linarith
  set w : ℂ := stripPt σ a with hw_def
  set g : ℂ → ℂ := fun z => (ρ₀ : ℂ) * (z - w) + (θa : ℂ) * I with hg_def
  set Λ₂ : ℂ → ℂ := fun z => -exp (g z) with hΛ₂_def
  -- entirety of the phase carrier
  have hdiff : Differentiable ℂ Λ₂ := by
    have hgd : Differentiable ℂ g := by
      rw [hg_def]
      exact ((differentiable_id.sub_const w).const_mul _).add_const _
    rw [hΛ₂_def]
    exact hgd.cexp.neg
  -- the log-derivative is the constant rate ρ₀
  have hld : ∀ z : ℂ, logDeriv Λ₂ z = (ρ₀ : ℂ) := by
    intro z
    have hg' : HasDerivAt g (ρ₀ : ℂ) z := by
      rw [hg_def]
      simpa using
        (((hasDerivAt_id z).sub_const w).const_mul (ρ₀ : ℂ)).add_const ((θa : ℂ) * I)
    have hd : HasDerivAt Λ₂ (-(exp (g z) * (ρ₀ : ℂ))) z := by
      rw [hΛ₂_def]
      exact hg'.cexp.neg
    rw [logDeriv_apply, hd.deriv, hΛ₂_def, neg_div_neg_eq, mul_comm, mul_div_assoc,
      div_self (exp_ne_zero _), mul_one]
  -- the incidence value along the edge is the pure phase exp(iφ(τ))
  have hval : ∀ τ : ℝ, incidence (fun _ => (1 : ℂ)) Λ₂ (stripPt σ τ) =
      exp (((θa + ρ₀ * (τ - a) : ℝ) : ℂ) * I) := by
    intro τ
    have hgτ : g (stripPt σ τ) = ((θa + ρ₀ * (τ - a) : ℝ) : ℂ) * I := by
      rw [hg_def, hw_def]
      simp only [stripPt]
      push_cast
      ring
    simp only [incidence, hΛ₂_def, neg_neg, div_one, hgτ]
  -- the phase never completes a half-turn: Im stays strictly positive
  have him : ∀ τ ∈ Set.Icc a b,
      0 < (incidence (fun _ => (1 : ℂ)) Λ₂ (stripPt σ τ)).im := by
    intro τ hτ
    rw [hval τ, Complex.exp_ofReal_mul_I_im]
    have h1 : 0 < θa + ρ₀ * (τ - a) := by
      have : 0 ≤ ρ₀ * (τ - a) := mul_nonneg hρ.le (by linarith [hτ.1])
      linarith
    have h2 : θa + ρ₀ * (τ - a) < Real.pi := by
      have : ρ₀ * (τ - a) ≤ ρ₀ * (b - a) :=
        mul_le_mul_of_nonneg_left (by linarith [hτ.2]) hρ.le
      rw [hθa_def]; linarith
    exact Real.sin_pos_of_pos_of_lt_pi h1 h2
  refine ⟨fun _ => 1, Λ₂, fun z _ => analyticAt_const, fun z _ => one_ne_zero,
    fun z _ => hdiff.differentiableOn.analyticAt Filter.univ_mem,
    fun z _ => by rw [hΛ₂_def]; exact neg_ne_zero.mpr (exp_ne_zero _),
    ?_, ?_, ?_⟩
  · intro τ _
    rw [hld, logDeriv_const]
    simp
  · exact ⟨fun _ => him b ⟨hab.le, le_refl b⟩, fun _ => him a ⟨le_refl a, hab.le⟩⟩
  · intro τ hτ c
    exact pencil_real_member_ne_zero_of_im_ne_zero one_ne_zero (ne_of_gt (him τ hτ)) c

end RHTower
