import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# The zero sets of `ζ` and `ξ`

`ξ` is `ζ` with its pole and its trivial zeros removed, so the two zero sets differ exactly by the
trivial ladder `-2, -4, -6, …`.  The corpus states that correspondence only inside the open critical
strip (`xi_eq_zero_iff`), because strip containment of a `ζ` zero was a hypothesis rather than a
theorem.  With `riemannZeta_zero_re_mem_Ioo` it is a theorem, and the correspondence becomes global
and hypothesis-free in both directions.

Two consequences for the shape of the Riemann hypothesis:

* mathlib's `RiemannHypothesis` carries a clause `s ≠ 1`, which is redundant: a nontrivial zero of
  `ζ` lies in the open critical strip and so is never the pole.
* RH is equivalent to the plain statement that every `ξ` zero has real part `1/2`, with no
  half-plane restriction — the corpus's `rh_iff_xi_ne_zero_right` restricts to `Re s > 1/2`.
-/

namespace RHTower

open Complex

/-- **Global correspondence between the zero sets of `ξ` and of `ζ`.** A point is a zero of `ξ`
exactly when it is a zero of `ζ` other than a trivial one.  Neither direction needs a strip
hypothesis: a zero of `ξ` lies in the open strip by `xi_zero_re_mem_open_unit`, and a nontrivial
zero of `ζ` lies there by `riemannZeta_zero_re_mem_Ioo`. -/
theorem xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial {ρ : ℂ} :
    xi ρ = 0 ↔ riemannZeta ρ = 0 ∧ ∀ n : ℕ, ρ ≠ -(2 * ((n : ℂ) + 1)) := by
  constructor
  · intro h
    obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit h
    have hne1 : ρ ≠ 1 := by
      intro hc
      rw [hc, Complex.one_re] at h1
      exact absurd h1 (lt_irrefl 1)
    refine ⟨(xi_eq_zero_iff h0 hne1).mp h, fun n hc => ?_⟩
    rw [show (-(2 * ((n : ℂ) + 1))) = ((-(2 * ((n : ℝ) + 1)) : ℝ) : ℂ) by push_cast; ring] at hc
    rw [hc, Complex.ofReal_re] at h0
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · rintro ⟨hz, htriv⟩
    obtain ⟨h0, h1⟩ := riemannZeta_zero_re_mem_Ioo hz htriv
    have hne1 : ρ ≠ 1 := by
      intro hc
      rw [hc, Complex.one_re] at h1
      exact absurd h1 (lt_irrefl 1)
    exact (xi_eq_zero_iff h0 hne1).mpr hz

/-- **The zero set of `ζ` is that of `ξ` together with the trivial ladder.** -/
theorem riemannZeta_eq_zero_iff_xi_or_trivial {ρ : ℂ} :
    riemannZeta ρ = 0 ↔ xi ρ = 0 ∨ ∃ n : ℕ, ρ = -(2 * ((n : ℂ) + 1)) := by
  constructor
  · intro h
    by_cases ht : ∃ n : ℕ, ρ = -(2 * ((n : ℂ) + 1))
    · exact Or.inr ht
    · exact Or.inl (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr
        ⟨h, fun n hn => ht ⟨n, hn⟩⟩)
  · rintro (h | ⟨n, rfl⟩)
    · exact (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp h).1
    · rw [show -(2 * ((n : ℂ) + 1)) = -2 * ((n : ℂ) + 1) by ring]
      exact riemannZeta_neg_two_mul_nat_add_one n

/-- **The Riemann hypothesis without the pole clause.** mathlib's statement excludes `s = 1`
explicitly; the clause is redundant, because a nontrivial zero of `ζ` lies in the open critical
strip and therefore is not `1`. -/
theorem riemannHypothesis_iff_forall_nontrivial_zero :
    RiemannHypothesis ↔
      ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s.re = 1 / 2 := by
  constructor
  · intro hRH s hz ht
    exact hRH s hz ht (riemannZeta_zero_ne_one hz)
  · intro h s hz ht _
    exact h s hz ht

/-- **The Riemann hypothesis as a plain statement about `ξ`.** No half-plane restriction is needed:
`ξ` zeros come in reflected pairs, so pinning the right half already pins everything. -/
theorem riemannHypothesis_iff_xi_zero_re_eq_half :
    RiemannHypothesis ↔ ∀ ρ : ℂ, xi ρ = 0 → ρ.re = 1 / 2 := by
  constructor
  · intro hRH ρ hρ
    exact xi_zero_re_eq_half_of_RH hRH hρ
  · intro h
    refine rh_iff_xi_ne_zero_right.mpr fun s hs hz => ?_
    rw [mem_rightHalf, h s hz] at hs
    exact absurd hs (lt_irrefl _)

end RHTower
