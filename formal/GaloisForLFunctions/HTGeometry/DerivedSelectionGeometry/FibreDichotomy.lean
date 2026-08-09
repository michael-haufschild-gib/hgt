import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.TwoPathIncompatibility

/-!
# The fibrewise zero/full dichotomy and its Riemann specialisation

Specialising the universal two-path family at a point `q = λ` of the monodromy line replaces the
base by a field.  There the minimal stable boundary can only be zero or everything:

* `minStableBoundary_eq_bot_of_eq_one`, `minStableBoundary_eq_top_of_ne_one`,
  `minStableBoundary_eq_bot_iff` — `B_min(λ) = 0` exactly at `λ = 1` and `B_min(λ) = k²`
  otherwise.

Under the arithmetic pullback `q = δ_n(ρ) = n^{2 Re ρ - 1}` the identity point is exactly the
critical line:

* `riemannSpecial_eq_one_iff` — for `n ≥ 2`, `δ_n(ρ) = 1 ↔ Re ρ = 1/2`;
* `minStableBoundary_riemann_eq_bot_iff`, `minStableBoundary_riemann_eq_top_iff` — the boundary
  family `B_{min,ρ}` is `0` on the critical line and the whole two-leg target off it.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

universe u

section FieldFibre

variable {F : Type u} [Field F] {q c : F}

theorem wallSquare_eq_bot_of_eq_one (h : q = 1) : wallSquare (R := F) q = ⊥ := by
  rw [wallSquare, h, sub_self, Ideal.span_singleton_eq_bot.2 rfl, Submodule.prod_bot]

theorem wallSquare_eq_top_of_ne_one (h : q ≠ 1) : wallSquare (R := F) q = ⊤ := by
  have hu : IsUnit (q - 1) := (Ne.isUnit (sub_ne_zero.2 h))
  rw [wallSquare, Ideal.span_singleton_eq_top.2 hu, Submodule.prod_top]

/-- **Corollary 4.2 (4.4), vanishing half.**  At the identity point the specialised boundary is
zero. -/
theorem minStableBoundary_eq_bot_of_eq_one (hc : IsUnit c) (h : q = 1) :
    minStableBoundary q c = ⊥ := by
  rw [minStableBoundary_eq q c hc, wallSquare_eq_bot_of_eq_one h]

/-- **Corollary 4.2 (4.4), full half.**  Away from the identity point the specialised boundary is
the whole two-leg target. -/
theorem minStableBoundary_eq_top_of_ne_one (hc : IsUnit c) (h : q ≠ 1) :
    minStableBoundary q c = ⊤ := by
  rw [minStableBoundary_eq q c hc, wallSquare_eq_top_of_ne_one h]

theorem minStableBoundary_eq_bot_iff (hc : IsUnit c) :
    minStableBoundary q c = ⊥ ↔ q = 1 := by
  refine ⟨fun h => ?_, minStableBoundary_eq_bot_of_eq_one hc⟩
  by_contra hq
  rw [minStableBoundary_eq_top_of_ne_one hc hq] at h
  exact absurd h.symm bot_ne_top

theorem minStableBoundary_eq_top_iff (hc : IsUnit c) :
    minStableBoundary q c = ⊤ ↔ q ≠ 1 := by
  refine ⟨fun h hq => ?_, minStableBoundary_eq_top_of_ne_one hc⟩
  rw [minStableBoundary_eq_bot_of_eq_one hc hq] at h
  exact bot_ne_top h

end FieldFibre

section Riemann

/-- For a base `b > 1` the real power `b^x` equals `1` exactly at `x = 0`. -/
theorem rpow_eq_one_iff_of_one_lt {b x : ℝ} (hb : 1 < b) : b ^ x = 1 ↔ x = 0 := by
  rw [Real.rpow_def_of_pos (by linarith), Real.exp_eq_one_iff, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (ne_of_gt (Real.log_pos hb))
    · exact h
  · intro h; exact Or.inr h

/-- The arithmetic pullback `δ_n(ρ) = n^{2 Re ρ - 1}` of the universal monodromy parameter. -/
noncomputable def riemannSpecial (n : ℕ) (ρ : ℂ) : ℝ := (n : ℝ) ^ (2 * ρ.re - 1)

/-- **Corollary 8A.3, arithmetic half.**  For `n ≥ 2` the identity point of the pullback is exactly
the critical line. -/
theorem riemannSpecial_eq_one_iff {n : ℕ} (hn : 2 ≤ n) (ρ : ℂ) :
    riemannSpecial n ρ = 1 ↔ ρ.re = 1 / 2 := by
  have hb : (1 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [riemannSpecial, rpow_eq_one_iff_of_one_lt hb]
  constructor <;> intro h <;> linarith

variable {n : ℕ} {ρ : ℂ} {c : ℂ}

/-- **(7.2), critical-line half.**  On the critical line the specialised boundary vanishes. -/
theorem minStableBoundary_riemann_eq_bot_iff (hn : 2 ≤ n) (hc : IsUnit c) :
    minStableBoundary ((riemannSpecial n ρ : ℝ) : ℂ) c = ⊥ ↔ ρ.re = 1 / 2 := by
  rw [minStableBoundary_eq_bot_iff hc, ← riemannSpecial_eq_one_iff hn ρ]
  exact_mod_cast Complex.ofReal_eq_one

/-- **(7.2), off-line half.**  Off the critical line the specialised boundary is the whole physical
two-leg target. -/
theorem minStableBoundary_riemann_eq_top_iff (hn : 2 ≤ n) (hc : IsUnit c) :
    minStableBoundary ((riemannSpecial n ρ : ℝ) : ℂ) c = ⊤ ↔ ρ.re ≠ 1 / 2 := by
  rw [minStableBoundary_eq_top_iff hc]
  rw [not_iff_not, ← riemannSpecial_eq_one_iff hn ρ]
  exact_mod_cast Complex.ofReal_eq_one

end Riemann

end GaloisForLFunctions.HTGeometry.DerivedSelection
