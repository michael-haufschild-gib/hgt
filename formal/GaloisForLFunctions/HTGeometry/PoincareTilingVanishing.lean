import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact

/-!
# Poincaré inequality on tilings with a zero in every tile

If a `C¹` real function vanishes somewhere in an interval `[α, β]`, then
`∫_α^β s² ≤ (β − α)² ∫_α^β s′²` (`integral_sq_le_of_vanishing`): `|s x| ≤ ∫|s′|` and
Cauchy–Schwarz. Summing over a tiling of `[T, T + M h]` into `M` intervals of length `h`, each
containing a zero of `s`, gives `∫_T^{T+Mh} s² ≤ h² ∫_T^{T+Mh} s′²` (`integral_sq_le_of_tiling`).

This turns zeros at every scale `h` into a lower bound for the mean-square frequency `∫s′²/∫s²`.
-/

open MeasureTheory intervalIntegral Set

namespace GaloisForLFunctions.HTGeometry

theorem integral_sq_le_of_vanishing {s s' : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hs : ∀ x ∈ Icc α β, HasDerivAt s (s' x) x) (hs'c : ContinuousOn s' (Icc α β))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc α β) (hzero : s x₀ = 0) :
    ∫ x in α..β, s x ^ 2 ≤ (β - α) ^ 2 * ∫ x in α..β, s' x ^ 2 := by
  have hscont : ContinuousOn s (Icc α β) := fun x hx => (hs x hx).continuousAt.continuousWithinAt
  set J := ∫ y in α..β, |s' y| with hJ
  have hJ0 : 0 ≤ J := integral_nonneg hαβ (fun y _ => abs_nonneg _)
  have hpt : ∀ x ∈ Icc α β, |s x| ≤ J := by
    intro x hx
    have key : ∀ {u v : ℝ}, u ∈ Icc α β → v ∈ Icc α β → u ≤ v → |s v - s u| ≤ J := by
      intro u v hu hv huv
      have huvI : Icc u v ⊆ Icc α β := Icc_subset_Icc hu.1 hv.2
      have hFTC : ∫ y in u..v, s' y = s v - s u := by
        refine integral_eq_sub_of_hasDerivAt (fun y hy => ?_) ?_
        · rw [uIcc_of_le huv] at hy; exact hs y (huvI hy)
        · exact (hs'c.mono huvI).intervalIntegrable_of_Icc huv
      rw [← hFTC]
      refine (abs_integral_le_integral_abs huv).trans ?_
      exact integral_mono_interval hu.1 huv hv.2 (Filter.Eventually.of_forall fun y => abs_nonneg _)
        ((continuous_abs.comp_continuousOn hs'c).intervalIntegrable_of_Icc hαβ)
    rcases le_total x₀ x with h | h
    · have := key hx₀ hx h; rwa [hzero, sub_zero] at this
    · have := key hx hx₀ h; rwa [hzero, zero_sub, abs_neg] at this
  have hsq : ∫ x in α..β, s x ^ 2 ≤ (β - α) * J ^ 2 := by
    have := integral_mono_on hαβ ((hscont.pow 2).intervalIntegrable_of_Icc hαβ)
      (intervalIntegrable_const (μ := volume) (c := J ^ 2)) (fun x hx => by
        calc s x ^ 2 = |s x| ^ 2 := (sq_abs _).symm
          _ ≤ J ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hpt x hx) 2)
    rwa [intervalIntegral.integral_const, smul_eq_mul] at this
  have hCS : J ^ 2 ≤ (β - α) * ∫ x in α..β, s' x ^ 2 := by
    rcases eq_or_lt_of_le hαβ with h | h
    · subst h; simp [hJ]
    have hℓ : 0 < β - α := sub_pos.mpr h
    set μ := J / (β - α)
    have hint2 : IntervalIntegrable (fun x => s' x ^ 2) volume α β :=
      (hs'c.pow 2).intervalIntegrable_of_Icc hαβ
    have hintA : IntervalIntegrable (fun x => |s' x|) volume α β :=
      (continuous_abs.comp_continuousOn hs'c).intervalIntegrable_of_Icc hαβ
    have hnn : 0 ≤ ∫ x in α..β, (|s' x| - μ) ^ 2 := integral_nonneg hαβ (fun x _ => sq_nonneg _)
    have hexp : ∫ x in α..β, (|s' x| - μ) ^ 2 =
        (∫ x in α..β, s' x ^ 2) - 2 * μ * J + μ ^ 2 * (β - α) := by
      have hpt' : (fun x => (|s' x| - μ) ^ 2) = fun x => s' x ^ 2 - 2 * μ * |s' x| + μ ^ 2 := by
        funext x; rw [sub_sq, sq_abs]; ring
      rw [hpt', integral_add (hint2.sub (hintA.const_mul _)) intervalIntegrable_const,
        integral_sub hint2 (hintA.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hexp] at hnn
    have hμ : μ * (β - α) = J := div_mul_cancel₀ J hℓ.ne'
    nlinarith [hμ]
  calc ∫ x in α..β, s x ^ 2 ≤ (β - α) * J ^ 2 := hsq
    _ ≤ (β - α) * ((β - α) * ∫ x in α..β, s' x ^ 2) := by gcongr
    _ = (β - α) ^ 2 * ∫ x in α..β, s' x ^ 2 := by ring

/-- **Tiling Poincaré.** A zero in each of `M` consecutive tiles of length `h` gives
`∫ s² ≤ h² ∫ s′²` over the union. -/
theorem integral_sq_le_of_tiling {s s' : ℝ → ℝ} {T h : ℝ} (hh : 0 ≤ h) (M : ℕ)
    (hs : ∀ x ∈ Icc T (T + M * h), HasDerivAt s (s' x) x)
    (hs'c : ContinuousOn s' (Icc T (T + M * h)))
    (hzero : ∀ j : ℕ, j < M → ∃ x ∈ Icc (T + j * h) (T + (j + 1) * h), s x = 0) :
    ∫ x in T..T + M * h, s x ^ 2 ≤ h ^ 2 * ∫ x in T..T + M * h, s' x ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hsub : Icc T (T + M * h) ⊆ Icc T (T + (M + 1 : ℕ) * h) := by
      apply Icc_subset_Icc le_rfl; push_cast; nlinarith
    have ih' := ih (fun x hx => hs x (hsub hx)) (hs'c.mono hsub)
      (fun j hj => hzero j (by omega))
    have htile : Icc (T + M * h) (T + (M + 1 : ℕ) * h) ⊆ Icc T (T + (M + 1 : ℕ) * h) := by
      apply Icc_subset_Icc _ le_rfl; nlinarith [Nat.cast_nonneg (α := ℝ) M]
    obtain ⟨x₀, hx₀, hz⟩ := hzero M (by omega)
    have hle : T + M * h ≤ T + (M + 1 : ℕ) * h := by push_cast; nlinarith
    have hlast := integral_sq_le_of_vanishing hle (fun x hx => hs x (htile hx))
      (hs'c.mono htile) (by push_cast at hx₀ ⊢; exact hx₀) hz
    have hlen : T + (M + 1 : ℕ) * h - (T + M * h) = h := by push_cast; ring
    rw [hlen] at hlast
    have hTM : T ≤ T + M * h := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
    have hsc : ContinuousOn s (Icc T (T + (M + 1 : ℕ) * h)) :=
      fun x hx => (hs x hx).continuousAt.continuousWithinAt
    have hTM1 : T ≤ T + (M + 1 : ℕ) * h := hTM.trans hle
    have i1 : IntervalIntegrable (fun x => s x ^ 2) volume T (T + M * h) :=
      ((hsc.mono hsub).pow 2).intervalIntegrable_of_Icc hTM
    have i2 : IntervalIntegrable (fun x => s x ^ 2) volume (T + M * h) (T + (M + 1 : ℕ) * h) :=
      ((hsc.mono htile).pow 2).intervalIntegrable_of_Icc hle
    have j1 : IntervalIntegrable (fun x => s' x ^ 2) volume T (T + M * h) :=
      ((hs'c.mono hsub).pow 2).intervalIntegrable_of_Icc hTM
    have j2 : IntervalIntegrable (fun x => s' x ^ 2) volume (T + M * h) (T + (M + 1 : ℕ) * h) :=
      ((hs'c.mono htile).pow 2).intervalIntegrable_of_Icc hle
    rw [← integral_add_adjacent_intervals i1 i2, ← integral_add_adjacent_intervals j1 j2]
    nlinarith [ih', hlast]

end GaloisForLFunctions.HTGeometry
