import GaloisForLFunctions.RHTower.XiCriticalityEveryScale

/-!
# Local rigidity from a resonance-free box

**Theorem** (`rigidAt_of_local_resonance_free`). Let `E` be strict lower Pólya, nonzero on `ℝ`,
with `Re E = Ξ` on `ℝ`. Suppose `E` has no zero `z` with `X − m ≤ Re z ≤ Y + m` and `−h ≤ Im z ≤ 0`,
where `X < Y`. Then every ordered ordinate `γ_k` with `X ≤ γ_k` and `γ_{k+2} ≤ Y` is
`(min h m / 2)`-rigid.

**Proof.** In the window the phase speed of `E` is log-Lipschitz with constant `2/min h m`
(`phaseSpeed_window_margin`). It is positive, because a zero of the phase speed would make the
phase constant on `[X, Y]`, and then `Ξ = A cos φ` would vanish on `[X, Y]`, since `Ξ(γ_k) = 0`.
Gap rigidity of the phase (`gap_rigidity_of_phase_window`) then compares consecutive gaps.

`RigidAt.mono`: rigidity at a scale gives rigidity at every smaller positive scale.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry (phaseSpeed exists_phase_rep gap_rigidity_of_phase_window)

namespace RHTower

noncomputable section

/-- Rigidity at a scale implies rigidity at every smaller positive scale. -/
theorem RigidAt.mono {h h' : ℝ} (hh' : 0 < h') (hle : h' ≤ h) {k : ℕ} (H : RigidAt h k) :
    RigidAt h' k := by
  obtain ⟨hs, hup, hdown⟩ := H
  have hg0 := ordinateGap_nonneg k
  have hg1 := ordinateGap_nonneg (k + 1)
  have hexp : Real.exp ((ordinateGap k + ordinateGap (k + 1)) / h) ≤
      Real.exp ((ordinateGap k + ordinateGap (k + 1)) / h') :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (by positivity) hh' hle)
  exact ⟨hs, hup.trans (mul_le_mul_of_nonneg_left hexp hg0),
    hdown.trans (mul_le_mul_of_nonneg_left hexp hg1)⟩

/-- **Local rigidity from a resonance-free box.** -/
theorem rigidAt_of_local_resonance_free {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E)
    (hrep : ∀ t : ℝ, Xi t = (E t).re) (hne : ∀ t : ℝ, E t ≠ 0) {h m X Y : ℝ} (hh : 0 < h)
    (hm : 0 < m) (hXY : X < Y)
    (hfree : ∀ z : ℂ, X - m ≤ z.re → z.re ≤ Y + m → -h ≤ z.im → z.im ≤ 0 → E z ≠ 0)
    {k : ℕ} (hk1 : X ≤ xiOrderedPositiveOrdinate k)
    (hk2 : xiOrderedPositiveOrdinate (k + 2) ≤ Y) :
    RigidAt (min h m / 2) k := by
  have hRH := riemannHypothesis_of_strictLowerPolya_realization hE hrep
  have hEd := hE.differentiable
  have hne' : ∀ t : ℝ, E ((t : ℂ) + ((0 : ℝ) : ℂ) * I) ≠ 0 := fun t => by simpa using hne t
  have hrep' : ∀ t : ℝ, Xi t = (E ((t : ℂ) + ((0 : ℝ) : ℂ) * I)).re := fun t => by
    simpa using hrep t
  obtain ⟨A, φ, hA, hφ, hAφ⟩ := exists_phase_rep hEd hne'
  have hXi : ∀ t, Xi t = A t * Real.cos (φ t) := fun t => by rw [hrep' t, hAφ t]
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  have hm1 : 0 < min h m := lt_min hh hm
  set γ := xiOrderedPositiveOrdinate with hγ
  have hk01 : γ k ≤ γ (k + 1) := xiOrderedPositiveOrdinate_monotone (Nat.le_succ _)
  have hk12 : γ (k + 1) ≤ γ (k + 2) := xiOrderedPositiveOrdinate_monotone (Nat.le_succ _)
  obtain ⟨hω0, hLL⟩ := hE.phaseSpeed_window_margin hh hm hXY.le hne' hfree
  -- the phase speed is positive on the window
  have hωpos : ∀ t ∈ Icc X Y, 0 < phaseSpeed E 0 t := by
    intro t₀ ht₀
    by_contra hle
    push Not at hle
    have h0 : phaseSpeed E 0 t₀ = 0 := le_antisymm hle (hω0 t₀)
    have hz : ∀ s ∈ Icc X Y, phaseSpeed E 0 s = 0 := fun s hs => by
      have := hLL s hs t₀ ht₀
      rw [h0, mul_zero] at this
      exact le_antisymm this (hω0 s)
    have hconst : ∀ y ∈ Icc X Y, φ y = φ X := by
      intro y hy
      rcases eq_or_lt_of_le hy.1 with hXy | hXy
      · rw [hXy]
      obtain ⟨ξ, hξ, hmv⟩ := exists_hasDerivAt_eq_slope φ (fun t => -phaseSpeed E 0 t) hXy
        hφc.continuousOn fun x _ => hφ x
      have hyX : y - X ≠ 0 := by linarith
      rw [hz ξ ⟨hξ.1.le, hξ.2.le.trans hy.2⟩, eq_div_iff hyX] at hmv
      linarith
    have hcos0 : Real.cos (φ X) = 0 := by
      have := Xi_orderedPositiveOrdinate_eq_zero hRH k
      rw [hXi, hconst _ ⟨hk1, by linarith⟩] at this
      exact (mul_eq_zero.mp this).resolve_left (hA _).ne'
    have hY0 : 0 < Y := lt_of_lt_of_le (xiOrderedPositiveOrdinate_pos (k + 2)) hk2
    have hsub : Ioo (max X 0) Y ⊆ γ '' Iio (xiZeroCount Y).toNat := by
      intro y hy
      have hy0 : 0 < y := lt_of_le_of_lt (le_max_right _ _) hy.1
      have hyX : X < y := lt_of_le_of_lt (le_max_left _ _) hy.1
      have hXiy : Xi y = 0 := by rw [hXi, hconst y ⟨hyX.le, hy.2.le⟩, hcos0, mul_zero]
      obtain ⟨n, hn⟩ := exists_orderedPositiveOrdinate_eq_of_Xi_eq_zero hy0 hXiy
      exact ⟨n, lt_toNat_xiZeroCount_iff.mpr (by rw [hn]; exact hy.2.le), hn⟩
    exact Set.Ioo_infinite (max_lt hXY hY0) (((Set.finite_Iio _).image γ).subset hsub)
  have hs0 := ordinate_lt_succ_of_phaseSpeed_pos hEd hrep' hRH (hne' _)
    (hωpos _ ⟨hk1, by linarith⟩)
  have hs1 := ordinate_lt_succ_of_phaseSpeed_pos hEd hrep' hRH (hne' _)
    (hωpos _ ⟨by linarith, by linarith⟩)
  have hz : ∀ j, A (γ j) * Real.cos (φ (γ j)) = 0 := fun j => by
    rw [← hXi]; exact Xi_orderedPositiveOrdinate_eq_zero hRH j
  have hno : ∀ j, ∀ x ∈ Ioo (γ j) (γ (j + 1)), A x * Real.cos (φ x) ≠ 0 := fun j x hx => by
    rw [← hXi]; exact Xi_ne_zero_of_mem_Ioo_ordinates hx
  have hgr := gap_rigidity_of_phase_window hm1 hA hφ hωpos hLL hk1 hk2 hs0 hs1 (hz k)
    (hz (k + 1)) (hz (k + 2)) (hno k) (hno (k + 1))
  have he : 2 * (γ (k + 2) - γ k) / min h m =
      (ordinateGap k + ordinateGap (k + 1)) / (min h m / 2) := by
    simp only [ordinateGap, hγ]
    field_simp
    ring
  rw [he] at hgr
  have e1 : γ (k + 2) - γ (k + 1) = ordinateGap (k + 1) := by simp only [ordinateGap, hγ]
  have e2 : γ (k + 1) - γ k = ordinateGap k := by simp only [ordinateGap, hγ]
  rw [e1, e2] at hgr
  exact ⟨hs0, hgr.1, hgr.2⟩

end

end RHTower
