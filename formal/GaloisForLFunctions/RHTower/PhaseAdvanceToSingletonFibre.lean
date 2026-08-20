import GaloisForLFunctions.RHTower.HardySignChainCount
import GaloisForLFunctions.HTGeometry.PhaseSignChain

/-!
# From a phase advance to the singleton-fibre bound

This is the single interface every Levinson-type argument has to hit.  Given, on a window
`[T₁, T₂] ⊆ (0, ∞)`, a polar representation `Z = ρ·cos ψ` with `ρ > 0` and `ψ` continuous whose
advance across the window is at least `nπ`, the whole downstream chain fires:

```text
phase advance nπ  →  n sign changes of Z  →  n critical zeros of odd order
                  →  n distinct odd fibres  →  H₁(T₂) ≥ (3/2)n − N(T₂)/2.
```

Everything here is unconditional.  What an analytic argument must still supply is the polar
representation together with a lower bound for its advance.
-/

open Set


noncomputable section

namespace RHTower

/-- **A phase advance of `nπ` for Hardy's `Z` gives `n` odd-order ordinates.**  This is the interface
every Levinson-type argument produces: a polar representation `Z = ρ·cos ψ` on a window inside
`(0, T₂]`, with `ρ > 0`, `ψ` continuous, and `ψ` advancing by at least `nπ`. -/
theorem le_xiOddFiberCount_of_phase_advance {T₁ T₂ : ℝ} (h0 : 0 < T₁) (hT : T₁ ≤ T₂)
    {ρ ψ : ℝ → ℝ} {m₀ : ℤ} {n : ℕ}
    (hψ : ContinuousOn ψ (Icc T₁ T₂))
    (hρ : ∀ τ ∈ Icc T₁ T₂, 0 < ρ τ)
    (hpolar : ∀ τ ∈ Icc T₁ T₂, hardyZ τ = ρ τ * Real.cos (ψ τ))
    (hlow : ψ T₁ ≤ (m₀ : ℝ) * Real.pi)
    (hhigh : ((m₀ : ℝ) + (n : ℝ)) * Real.pi ≤ ψ T₂) :
    n ≤ xiOddFiberCount T₂ := by
  obtain ⟨g, hgmem, hgstep, hgsign⟩ :=
    exists_sign_chain_of_phase_increase hT hψ hρ hlow hhigh
  refine le_xiOddFiberCount_of_sign_chain hgstep ?_ ?_ ?_
  · exact lt_of_lt_of_le h0 (hgmem 0 (Nat.zero_le n)).1
  · exact (hgmem n le_rfl).2
  · intro i hi
    have h1 := hpolar (g i) (hgmem i (by omega))
    have h2 := hpolar (g (i + 1)) (hgmem (i + 1) (by omega))
    rw [h1, h2]
    exact hgsign i hi

/-- The same, delivered as the singleton-fibre bound of `horizontal-singleton-zero-fibers`. -/
theorem xiSingletonFiberCount_ge_of_phase_advance {T₁ T₂ : ℝ} (h0 : 0 < T₁) (hT : T₁ ≤ T₂)
    {ρ ψ : ℝ → ℝ} {m₀ : ℤ} {n : ℕ}
    (hψ : ContinuousOn ψ (Icc T₁ T₂))
    (hρ : ∀ τ ∈ Icc T₁ T₂, 0 < ρ τ)
    (hpolar : ∀ τ ∈ Icc T₁ T₂, hardyZ τ = ρ τ * Real.cos (ψ τ))
    (hlow : ψ T₁ ≤ (m₀ : ℝ) * Real.pi)
    (hhigh : ((m₀ : ℝ) + (n : ℝ)) * Real.pi ≤ ψ T₂) :
    (3 / 2 : ℝ) * (n : ℝ) - (xiPosZeroCount T₂ : ℝ) / 2
      ≤ (xiSingletonFiberCount T₂ : ℝ) := by
  have h1 := le_xiOddFiberCount_of_phase_advance h0 hT hψ hρ hpolar hlow hhigh
  have h2 := three_mul_xiOddFiberCount_le T₂
  have hR : (3 : ℝ) * (n : ℝ)
      ≤ 2 * (xiSingletonFiberCount T₂ : ℝ) + (xiPosZeroCount T₂ : ℝ) := by
    have : 3 * n ≤ 2 * xiSingletonFiberCount T₂ + xiPosZeroCount T₂ := by omega
    exact_mod_cast this
  linarith

end RHTower

end
