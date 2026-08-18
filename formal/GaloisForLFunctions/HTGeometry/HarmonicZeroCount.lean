import GaloisForLFunctions.HTGeometry.ExpShift

/-!
# The degenerate count: a pure harmonic

The Sturm descent removes the conjugate pair `± iγ` from the support.  When nothing is left the
reduced polynomial vanishes identically and no finite set contains its zeros, so the descent step
does not apply: that case has to be counted on its own.

It is the case where the exponential polynomial *is* the harmonic `A cos γt + B sin γt`.  Two zeros
closer than `π/γ` make the linear system

`A cos γt₁ + B sin γt₁ = 0`,  `A cos γt₂ + B sin γt₂ = 0`

have determinant `sin (γ(t₂-t₁)) > 0`, hence force `A = B = 0`.  So a nonzero harmonic has
`π/γ`-separated zeros, and a `d`-separated subset of an interval of length `b - a` has at most
`(b-a)/d + 1` elements.  This is the sharp count — no factor two, no additive slack beyond the
inevitable endpoint — and it is what closes the degenerate branch of the descent.
-/

open Set Filter Real

namespace GaloisForLFunctions.HTGeometry

/-! ## Separated points in an interval -/

/-- A finite subset of `[a,b]` whose points are pairwise at distance at least `d` has at most
`(b-a)/d + 1` elements. -/
theorem card_le_of_separated {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b) (Z : Finset ℝ)
    (hmem : ∀ x ∈ Z, x ∈ Icc a b)
    (hsep : ∀ x ∈ Z, ∀ y ∈ Z, x < y → d ≤ y - x) :
    (Z.card : ℝ) ≤ (b - a) / d + 1 := by
  classical
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hnn : (0 : ℝ) ≤ (b - a) / d := div_nonneg hba hd.le
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Z.card = m := ⟨_, rfl⟩
  match m, hm with
  | 0, hm =>
    rw [hm]
    simp only [Nat.cast_zero]
    linarith
  | (n + 1), hm =>
    set e : Fin (n + 1) ↪o ℝ := Z.orderEmbOfFin hm with he
    have hemem : ∀ i : Fin (n + 1), e i ∈ Z := fun i => Z.orderEmbOfFin_mem hm i
    have hIcc : ∀ i : Fin (n + 1), e i ∈ Icc a b := fun i => hmem _ (hemem i)
    have hstep : ∀ k : Fin n, e k.castSucc < e k.succ := fun k =>
      (OrderEmbedding.lt_iff_lt e).mpr (Fin.castSucc_lt_succ (i := k))
    have hcount := nsmul_le_of_disjoint_intervals n
      (fun k : Fin n => e k.castSucc) (fun k : Fin n => e k.succ) a b d hab
      (fun k => (hIcc _).1) (fun k => (hIcc _).2) (fun k => (hstep k).le)
      (fun k l hkl => by
        refine e.monotone ?_
        rw [Fin.le_def]
        have : (k : ℕ) < (l : ℕ) := hkl
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega)
      (fun k => hsep _ (hemem _) _ (hemem _) (hstep k))
    rw [hm]
    push_cast
    have : (n : ℝ) ≤ (b - a) / d := (le_div_iff₀ hd).mpr hcount
    linarith

/-! ## The harmonic -/

/-- Two zeros of `A cos γt + B sin γt` at distance less than `π/γ` force `A = B = 0`: the linear
system they impose has determinant `sin (γ t₂ - γ t₁) > 0`. -/
theorem harmonic_coeff_eq_zero {γ A B t₁ t₂ : ℝ}
    (h₁ : A * cos (γ * t₁) + B * sin (γ * t₁) = 0)
    (h₂ : A * cos (γ * t₂) + B * sin (γ * t₂) = 0)
    (hlo : 0 < γ * t₂ - γ * t₁) (hhi : γ * t₂ - γ * t₁ < π) :
    A = 0 ∧ B = 0 := by
  have hs : 0 < sin (γ * t₂ - γ * t₁) := Real.sin_pos_of_pos_of_lt_pi hlo hhi
  have hexp : sin (γ * t₂ - γ * t₁)
      = sin (γ * t₂) * cos (γ * t₁) - cos (γ * t₂) * sin (γ * t₁) := Real.sin_sub _ _
  have hA : A * sin (γ * t₂ - γ * t₁) = 0 := by
    rw [hexp]
    linear_combination sin (γ * t₂) * h₁ - sin (γ * t₁) * h₂
  have hB : B * sin (γ * t₂ - γ * t₁) = 0 := by
    rw [hexp]
    linear_combination cos (γ * t₁) * h₂ - cos (γ * t₂) * h₁
  constructor
  · rcases mul_eq_zero.mp hA with h | h
    · exact h
    · exact absurd h (ne_of_gt hs)
  · rcases mul_eq_zero.mp hB with h | h
    · exact h
    · exact absurd h (ne_of_gt hs)

/-- **The gap.**  Distinct zeros of a nonzero harmonic of frequency `γ` are at least `π/γ` apart. -/
theorem harmonic_gap {γ A B t₁ t₂ : ℝ} (hγ : 0 < γ) (hAB : ¬ (A = 0 ∧ B = 0))
    (h₁ : A * cos (γ * t₁) + B * sin (γ * t₁) = 0)
    (h₂ : A * cos (γ * t₂) + B * sin (γ * t₂) = 0)
    (hlt : t₁ < t₂) : π / γ ≤ t₂ - t₁ := by
  by_contra hcon
  push Not at hcon
  refine hAB (harmonic_coeff_eq_zero h₁ h₂ ?_ ?_)
  · nlinarith
  · have h1 : γ * (t₂ - t₁) < γ * (π / γ) := mul_lt_mul_of_pos_left hcon hγ
    have h2 : γ * (π / γ) = π := by field_simp
    have h3 : γ * (t₂ - t₁) = γ * t₂ - γ * t₁ := by ring
    linarith

/-- **The degenerate count.**  A nonzero harmonic of frequency `γ` has at most
`(b-a)γ/π + 1` zeros in `[a,b]`. -/
theorem card_zeros_harmonic {γ A B a b : ℝ} (hγ : 0 < γ) (hab : a ≤ b)
    (hAB : ¬ (A = 0 ∧ B = 0)) (Z : Finset ℝ)
    (hmem : ∀ x ∈ Z, x ∈ Icc a b)
    (hzero : ∀ x ∈ Z, A * cos (γ * x) + B * sin (γ * x) = 0) :
    (Z.card : ℝ) ≤ (b - a) * γ / π + 1 := by
  have hd : (0 : ℝ) < π / γ := by positivity
  have hcount := card_le_of_separated hd hab Z hmem
    (fun x hx y hy hxy => harmonic_gap hγ hAB (hzero x hx) (hzero y hy) hxy)
  have hrw : (b - a) / (π / γ) = (b - a) * γ / π := by
    field_simp
  rw [hrw] at hcount
  exact hcount

end GaloisForLFunctions.HTGeometry
