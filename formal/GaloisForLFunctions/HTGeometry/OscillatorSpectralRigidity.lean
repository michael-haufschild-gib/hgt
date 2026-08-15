import GaloisForLFunctions.HTGeometry.OscillatorBoundaryVanishing

/-!
# Square-integrable solutions of the oscillator equation exist only on the ladder

For a nontrivial square-integrable solution of `v″ = (ξ² − μ)v` the ladder identity gives
`‖Av‖² = (μ − 1)‖v‖²` with `A v = v′ + ξ v`, so `μ ≥ 1`; and `Av` solves the same equation with `μ`
replaced by `μ − 2`.  Iterating, either some `A^k v` vanishes identically — which pins
`μ = 2k + 1` — or the separation constant would have to exceed every odd integer.

Hence `μ = 2n + 1` for some natural `n`.  Nothing is assumed beyond the equation, nontriviality and
square integrability; in particular no decay rate and no spectral theory.
-/

open Set MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Uniqueness to the right.**  A solution with vanishing phase vector at a point vanishes to the
right of it. -/
theorem eq_zero_of_phase_zero_right {mu : ℝ} {v v' : ℝ → ℝ} {y0 : ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x)
    (h0 : v y0 = 0) (h0' : v' y0 = 0) : ∀ x, y0 ≤ x → v x = 0 := by
  intro x hx
  have hbound := phasePair_norm_le (u := v) (u' := v') (u'' := fun t => (t ^ 2 - mu) * v t)
    (P := fun t => t ^ 2 - mu) (Q := fun _ => (0 : ℝ)) (a := y0) (b := x)
    (Lp := max (y0 ^ 2) (x ^ 2) + |mu|) (Lq := 0) (δ := 0) hx hv hv' ?_ ?_ ?_ ?_ x ⟨hx, le_rfl⟩
  · have hb2 : v x = 0 ∧ v' x = 0 := by simpa using hbound
    exact hb2.1
  · intro t _
    ring
  · intro t ht
    have ht1 : y0 ≤ t := ht.1
    have ht2 : t ≤ x := ht.2
    have hts : t ^ 2 ≤ max (y0 ^ 2) (x ^ 2) := by
      rcases le_total t 0 with h | h
      · have hy : t ^ 2 ≤ y0 ^ 2 := by nlinarith
        exact le_trans hy (le_max_left _ _)
      · have hxx : t ^ 2 ≤ x ^ 2 := by nlinarith
        exact le_trans hxx (le_max_right _ _)
    rw [abs_le]
    constructor
    · linarith [sq_nonneg t, le_abs_self mu, sq_nonneg y0, le_max_left (y0 ^ 2) (x ^ 2)]
    · linarith [hts, neg_abs_le mu]
  · intro t _
    simp
  · rw [h0, h0']
    simp

/-- **Uniqueness.**  A solution with vanishing phase vector at a point vanishes identically. -/
theorem eq_zero_of_phase_zero {mu : ℝ} {v v' : ℝ → ℝ} {y0 : ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x)
    (h0 : v y0 = 0) (h0' : v' y0 = 0) : ∀ x, v x = 0 := by
  intro x
  rcases le_total y0 x with h | h
  · exact eq_zero_of_phase_zero_right hv hv' h0 h0' x h
  · obtain ⟨hw, hw'⟩ := hasDerivAt_reflect hv hv'
    have hz : (fun t => v (-t)) (-y0) = 0 := by simpa using h0
    have hz' : (fun t => -v' (-t)) (-y0) = 0 := by simpa using h0'
    have := eq_zero_of_phase_zero_right (mu := mu) hw hw' hz hz' (-x) (by linarith)
    simpa using this

/-- A nontrivial solution has positive square norm. -/
theorem integral_sq_pos_of_nontrivial {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hnt : ∀ y, v y ≠ 0 ∨ v' y ≠ 0)
    (hint : Integrable (fun x => v x ^ 2)) : 0 < ∫ x, v x ^ 2 := by
  have hnn : (0 : ℝ) ≤ ∫ x, v x ^ 2 := integral_nonneg fun x => sq_nonneg _
  rcases lt_or_eq_of_le hnn with h | h
  · exact h
  · exfalso
    have hzero : (fun x => v x ^ 2) =ᵐ[volume] 0 := by
      rw [← integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint]
      exact h.symm
    have hcont : Continuous fun x => v x ^ 2 := (continuous_of_hasDerivAt hv).pow 2
    have heqfun := (hcont.ae_eq_iff_eq volume continuous_const).1 hzero
    have hall : ∀ x, v x ^ 2 = 0 := fun x => congrFun heqfun x
    have hv0 : ∀ x, v x = 0 := fun x => pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (hall x)
    have hv'0 : v' 0 = 0 := by
      have hd : HasDerivAt v (v' 0) 0 := hv 0
      have hc : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 := hasDerivAt_const 0 0
      have hd' : HasDerivAt v 0 0 := by
        refine hc.congr_of_eventuallyEq ?_
        exact Filter.Eventually.of_forall fun x => (hv0 x)
      exact hd.unique hd'
    rcases hnt 0 with hcon | hcon
    · exact hcon (hv0 0)
    · exact hcon hv'0

/-- Auxiliary induction: bounded separation constants lie on the ladder. -/
theorem exists_rung_aux : ∀ (n : ℕ) (mu : ℝ) (v v' : ℝ → ℝ),
    mu ≤ 2 * (n : ℝ) + 1 →
    (∀ x, HasDerivAt v (v' x) x) →
    (∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x) →
    (∀ y, v y ≠ 0 ∨ v' y ≠ 0) →
    Integrable (fun x => v x ^ 2) →
    ∃ k : ℕ, mu = 2 * (k : ℝ) + 1 := by
  intro n
  induction n with
  | zero =>
    intro mu v v' hle hv hv' hnt hint
    set a : ℝ := max 1 (|mu| + 1) with hadef
    have ha : 0 < a := lt_of_lt_of_le one_pos (le_max_left _ _)
    have ha1 : (1 : ℝ) ≤ a := le_max_left _ _
    have hmu : mu < a ^ 2 := by
      have h1 : |mu| + 1 ≤ a := le_max_right _ _
      have h2 : mu ≤ |mu| := le_abs_self mu
      nlinarith
    have hB := tendsto_oscBoundary_atTop_zero ha hmu hv hv' hnt hint
    have hBneg := tendsto_oscBoundary_atBot_zero ha hmu hv hv' hnt hint
    have hpos := integral_sq_pos_of_nontrivial hv hnt hint
    have hge := one_le_of_integrable_of_pos hv hv' hB hBneg hint hpos
    refine ⟨0, ?_⟩
    push_cast
    push_cast at hle
    linarith
  | succ n ih =>
    intro mu v v' hle hv hv' hnt hint
    set a : ℝ := max 1 (|mu| + 1) with hadef
    have ha : 0 < a := lt_of_lt_of_le one_pos (le_max_left _ _)
    have ha1 : (1 : ℝ) ≤ a := le_max_left _ _
    have hmu : mu < a ^ 2 := by
      have h1 : |mu| + 1 ≤ a := le_max_right _ _
      have h2 : mu ≤ |mu| := le_abs_self mu
      nlinarith
    have hB := tendsto_oscBoundary_atTop_zero ha hmu hv hv' hnt hint
    have hBneg := tendsto_oscBoundary_atBot_zero ha hmu hv hv' hnt hint
    have hpos := integral_sq_pos_of_nontrivial hv hnt hint
    have hid := integral_oscLower_sq_eq hv hv' hB hBneg hint
    have hintL := integrable_oscLower_sq hv hv' hB hBneg hint
    by_cases hw : ∀ y, oscLower v v' y ≠ 0 ∨ oscLowerDeriv mu v v' y ≠ 0
    · have hle2 : mu - 2 ≤ 2 * (n : ℝ) + 1 := by
        push_cast at hle
        linarith
      obtain ⟨k, hk⟩ := ih (mu - 2) (oscLower v v') (oscLowerDeriv mu v v') hle2
        (fun x => hasDerivAt_oscLower hv hv' x)
        (fun x => hasDerivAt_oscLowerDeriv hv hv' x) hw hintL
      exact ⟨k + 1, by push_cast; linarith⟩
    · rw [not_forall] at hw
      obtain ⟨y0, hy0raw⟩ := hw
      rw [not_or, not_not, not_not] at hy0raw
      obtain ⟨hy0, hy0'⟩ := hy0raw
      have hzero : ∀ x, oscLower v v' x = 0 :=
        eq_zero_of_phase_zero (mu := mu - 2) (fun x => hasDerivAt_oscLower hv hv' x)
          (fun x => hasDerivAt_oscLowerDeriv hv hv' x) hy0 hy0'
      have hintzero : (∫ x, oscLower v v' x ^ 2) = 0 := by
        have : (fun x => oscLower v v' x ^ 2) = fun _ => (0 : ℝ) := by
          funext x
          rw [hzero x]
          ring
        rw [this]
        simp
      rw [hintzero] at hid
      refine ⟨0, ?_⟩
      push_cast
      nlinarith

/-- **Spectral rigidity of the harmonic oscillator.**  A nontrivial square-integrable solution of
`v″ = (ξ² − μ)v` forces `μ` onto the oscillator ladder. -/
theorem exists_rung_of_integrable {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x)
    (hnt : ∀ y, v y ≠ 0 ∨ v' y ≠ 0)
    (hint : Integrable (fun x => v x ^ 2)) :
    ∃ n : ℕ, mu = 2 * (n : ℝ) + 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt mu
  exact exists_rung_aux N mu v v' (by linarith) hv hv' hnt hint

end GaloisForLFunctions.HTGeometry
