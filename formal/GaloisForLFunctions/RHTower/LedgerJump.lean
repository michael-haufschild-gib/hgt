/-
The ledger jump (MWM lane, M1 arc — task #124; completes identity (L) of
15-conservation-program.md).

`deckClass_jump`: if two functions on the ball differ by exactly one enclosed zero —
`f' = (z − ρ')^{m'} · f` with `‖ρ' − a‖ ≤ r₀` — then ANY local `n`-th roots of the two
functions on the slit annulus charts have deck classes differing by exactly the factor
`exp(2πi·m'/n)`. Proof: two evaluations of the banked `deckClass_multi_zero` (the
extended configuration is indexed by `Option ι`, the new zero at `none`), and the ratio
of the two explicit classes. No new analysis; no argument principle.

Together with `deckClass_deformation_invariant` (no-flux case, DeckHomotopy.lean) this
makes the conservation ledger (L) — charge difference ≡ boundary multiplicity flux
mod n — a theorem for piecewise-generic deformations: between crossings the class is
constant, and each transversal crossing multiplies it by the crossing zero's
`exp(2πi·m/n)`.
-/
import GaloisForLFunctions.RHTower.DeckMultiZero

namespace RHTower

open Complex Metric

/-- **The ledger jump.** If `f' = (z − ρ')^{m'} · f` on the ball — the enclosed
configuration gains one zero of multiplicity `m'` — then any local `n`-th roots of `f'`
and of `f` on the two annulus charts have deck classes differing by the factor
`exp(2πi·m'/n)`. -/
theorem deckClass_jump {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    {ρ' : ℂ} {m' : ℕ} {f f' h G₁ G₂ H₁ H₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) {n : ℕ} (hn : 0 < n)
    (hρ : ∀ i ∈ s, ‖ρ i - a‖ ≤ r₀) (hρ' : ‖ρ' - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (∏ i ∈ s, (z - ρ i) ^ m i) * h z)
    (hfact' : ∀ z ∈ ball a R, f' z = (z - ρ') ^ m' * f z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ n = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ n = f z)
    (hH₁ : AnalyticOnNhd ℂ H₁ (chartRA a r₀ R))
    (hH₂ : AnalyticOnNhd ℂ H₂ (chartLA a r₀ R))
    (hpH₁ : ∀ z ∈ chartRA a r₀ R, H₁ z ^ n = f' z)
    (hpH₂ : ∀ z ∈ chartLA a r₀ R, H₂ z ^ n = f' z) :
    deckClass H₁ H₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) =
      exp (2 * (Real.pi : ℂ) * I * (m' : ℂ) / n) *
        deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) := by
  classical
  have hG := deckClass_multi_zero s ρ m h0 hrR hn hρ hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂
  have hnone : (none : Option ι) ∉ s.map ⟨some, Option.some_injective ι⟩ := by
    simp
  have hρ'' : ∀ o ∈ insert none (s.map ⟨some, Option.some_injective ι⟩),
      ‖(o.elim ρ' ρ : ℂ) - a‖ ≤ r₀ := by
    intro o ho
    rw [Finset.mem_insert] at ho
    rcases ho with rfl | ho
    · exact hρ'
    · rw [Finset.mem_map] at ho
      obtain ⟨i, hi, rfl⟩ := ho
      exact hρ i hi
  have hprod : ∀ z : ℂ,
      (∏ o ∈ insert none (s.map ⟨some, Option.some_injective ι⟩),
        (z - o.elim ρ' ρ) ^ o.elim m' m) =
      (z - ρ') ^ m' * ∏ i ∈ s, (z - ρ i) ^ m i := by
    intro z
    rw [Finset.prod_insert hnone, Finset.prod_map]
    simp only [Function.Embedding.coeFn_mk, Option.elim_none, Option.elim_some]
  have hfact'' : ∀ z ∈ ball a R, f' z =
      (∏ o ∈ insert none (s.map ⟨some, Option.some_injective ι⟩),
        (z - o.elim ρ' ρ) ^ o.elim m' m) * h z := by
    intro z hz
    rw [hfact' z hz, hfact z hz, hprod]
    ring
  have hH := deckClass_multi_zero (insert none (s.map ⟨some, Option.some_injective ι⟩))
    (fun o => o.elim ρ' ρ) (fun o => o.elim m' m) h0 hrR hn hρ'' hh hh0 hfact''
    hH₁ hH₂ hpH₁ hpH₂
  have hsum : (∑ o ∈ insert none (s.map ⟨some, Option.some_injective ι⟩),
      ((o.elim m' m : ℕ) : ℂ)) = (m' : ℂ) + ∑ i ∈ s, (m i : ℂ) := by
    rw [Finset.sum_insert hnone, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, Option.elim_none, Option.elim_some]
  rw [hsum] at hH
  rw [hH, hG, ← exp_add]
  congr 1
  ring

end RHTower
