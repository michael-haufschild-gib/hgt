import Mathlib

/-!
# Penalized maxima

Adding a linear penalty `−δ|L − L₀|` to a bounded continuous profile forces a maximum to exist: the
penalty drives the sum to `−∞`, so the supremum is attained on a compact set.  At such a maximizer
the profile obeys a one-sided Lipschitz inequality with constant the penalty slope,

`H(X + s) ≤ H(X) + δ|s|`,

because moving away from the maximizer can gain at most what the penalty charges.  This is the
mechanism that converts a limiting supremum into a pointwise inequality usable in an equation.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- The penalized profile. -/
noncomputable def penalized (H : ℝ → ℝ) (δ L₀ L : ℝ) : ℝ := H L - δ * |L - L₀|

/-- **The one-sided inequality at a penalized maximizer.**  Moving away from a maximizer of the
penalized profile can gain at most the penalty charge, so the profile itself is one-sided Lipschitz
there with constant `δ`. -/
theorem le_of_isMaxOn_penalized {H : ℝ → ℝ} {δ L₀ X : ℝ} {s : Set ℝ}
    (hmax : IsMaxOn (penalized H δ L₀) s X) (hδ : 0 ≤ δ) {y : ℝ} (hy : y ∈ s) :
    H y ≤ H X + δ * |y - X| := by
  have hle : penalized H δ L₀ y ≤ penalized H δ L₀ X := hmax hy
  unfold penalized at hle
  have htri : |y - L₀| - |X - L₀| ≤ |y - X| := by
    have h := abs_sub_abs_le_abs_sub (y - L₀) (X - L₀)
    rwa [show (y - L₀) - (X - L₀) = y - X by ring] at h
  have hpen : δ * |y - L₀| - δ * |X - L₀| ≤ δ * |y - X| := by
    nlinarith [htri, hδ]
  linarith

/-- The one-sided inequality in the two-sided form the transport argument consumes: at a penalized
maximizer, symmetric increments are dominated by the penalty slope times the shift. -/
theorem le_of_isMaxOn_penalized_shift {H : ℝ → ℝ} {δ L₀ X : ℝ} {s : Set ℝ}
    (hmax : IsMaxOn (penalized H δ L₀) s X) (hδ : 0 ≤ δ) {t : ℝ} (ht : 0 ≤ t)
    (hp : X + t ∈ s) (hm : X - t ∈ s) :
    H (X + t) ≤ H X + δ * t ∧ H (X - t) ≤ H X + δ * t := by
  constructor
  · have h := le_of_isMaxOn_penalized hmax hδ hp
    rwa [show X + t - X = t by ring, abs_of_nonneg ht] at h
  · have h := le_of_isMaxOn_penalized hmax hδ hm
    rwa [show X - t - X = -t by ring, abs_neg, abs_of_nonneg ht] at h

/-! ## Existence of the maximizer

The penalty drives the sum to `−∞`, so beyond a computable radius the penalized profile is below
its value at the left endpoint.  The supremum is therefore attained on a compact subinterval, and
that maximizer is global on the whole ray.
-/

/-- **A penalized bounded profile attains its maximum on a ray.**  The penalty forces the profile
below its endpoint value beyond a finite radius, so a compact maximum is a global one. -/
theorem exists_isMaxOn_penalized {H : ℝ → ℝ} {δ L₀ a B : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousOn H (Ici a)) (hB : ∀ L ∈ Ici a, H L ≤ B) :
    ∃ X ∈ Ici a, IsMaxOn (penalized H δ L₀) (Ici a) X := by
  set Φ := penalized H δ L₀ with hΦ
  have hΦcont : ContinuousOn Φ (Ici a) := by
    rw [hΦ]
    unfold penalized
    exact hcont.sub (continuous_const.mul ((continuous_id.sub continuous_const).abs)).continuousOn
  set R : ℝ := max a (L₀ + (B - Φ a) / δ + 1) with hR
  have haR : a ≤ R := le_max_left _ _
  have hcompact : IsCompact (Icc a R) := isCompact_Icc
  have hne : (Icc a R).Nonempty := ⟨a, ⟨le_refl a, haR⟩⟩
  obtain ⟨X, hXmem, hXmax⟩ :=
    hcompact.exists_isMaxOn hne (hΦcont.mono fun x hx => hx.1)
  refine ⟨X, hXmem.1, fun L hL => ?_⟩
  rcases le_or_gt L R with hLR | hLR
  · exact hXmax ⟨hL, hLR⟩
  · have hfar : Φ L < Φ a := by
      have h1 : L₀ + (B - Φ a) / δ + 1 ≤ R := le_max_right _ _
      have h2 : L₀ + (B - Φ a) / δ < L := by linarith
      have h3 : (B - Φ a) / δ < L - L₀ := by linarith
      have h4 : B - Φ a < δ * (L - L₀) := by
        rw [div_lt_iff₀ hδ] at h3
        linarith
      have h5 : L - L₀ ≤ |L - L₀| := le_abs_self _
      have h6 : H L ≤ B := hB L hL
      have hval : Φ L = H L - δ * |L - L₀| := rfl
      nlinarith [h4, h5, h6, hδ]
    have haIcc : a ∈ Icc a R := ⟨le_refl a, haR⟩
    exact le_of_lt (lt_of_lt_of_le hfar (hXmax haIcc))

end GaloisForLFunctions.HTGeometry
