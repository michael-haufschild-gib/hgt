import GaloisForLFunctions.RHTower.SecularEquationInterlacing

/-!
# The secular root converges to the coordinate ratio

The two-sided location bounds for the root of the secular equation read

```text
S / (S + L + T/(M−1))  ≤  μ / d_{k+1}  ≤  S / (S + L) + ε ,
```

with `S = ∑_{j≤k} ℓ_j²`, `L = ℓ_{k+1}²`, `T = ∑_{j>k+1} ℓ_j²`, and `ε`, `1/(M−1)` the two
gap slacks.  Along any family in which the coordinates converge and both slacks vanish, the two
sides converge to the same limit `A/(A+B)`, so the normalized root does too.

This is the glue between the coordinate limits and the root location: once `ℓ_j → a_j` is known, the
root of the secular equation is pinned to the explicit ratio of the limiting coordinate masses, with
no further information about the family.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- **The secular root converges to the limiting coordinate ratio.**  The hypotheses are exactly the
two location bounds, the coordinate limits, and the vanishing of the two slacks. -/
theorem tendsto_secular_ratio_of_limits {ι : Type*} {Lf : Filter ι}
    {S L T ε M ratio : ι → ℝ} {A B : ℝ}
    (hS : Tendsto S Lf (𝓝 A)) (hL : Tendsto L Lf (𝓝 B))
    (hT : Tendsto (fun i => T i / (M i - 1)) Lf (𝓝 0))
    (hε : Tendsto ε Lf (𝓝 0))
    (hAB : A + B ≠ 0)
    (hlow : ∀ᶠ i in Lf, S i / (S i + L i + T i / (M i - 1)) ≤ ratio i)
    (hup : ∀ᶠ i in Lf, ratio i ≤ S i / (S i + L i) + ε i) :
    Tendsto ratio Lf (𝓝 (A / (A + B))) := by
  have hsum : Tendsto (fun i => S i + L i) Lf (𝓝 (A + B)) := hS.add hL
  have hsumT : Tendsto (fun i => S i + L i + T i / (M i - 1)) Lf (𝓝 (A + B)) := by
    have h := hsum.add hT
    simpa using h
  have hupper : Tendsto (fun i => S i / (S i + L i) + ε i) Lf (𝓝 (A / (A + B))) := by
    have h := (hS.div hsum hAB).add hε
    simpa using h
  have hlower : Tendsto (fun i => S i / (S i + L i + T i / (M i - 1))) Lf
      (𝓝 (A / (A + B))) := hS.div hsumT hAB
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper hlow hup

/-- The limiting ratio in the card's normalization: with `A` the head mass and `B` the next
coordinate's mass, the root sits at `A/(A+B)`, which is the root of the degenerate secular
equation. -/
theorem secular_limit_ratio_eq {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    -(A / (A / (A + B))) + B / (1 - A / (A + B)) = 0 := by
  have hAB : 0 < A + B := by linarith
  have hne : A / (A + B) ≠ 0 := by
    rw [div_ne_zero_iff]
    exact ⟨ne_of_gt hA, ne_of_gt hAB⟩
  have h1 : (1 : ℝ) - A / (A + B) = B / (A + B) := by
    field_simp
    ring
  rw [h1]
  field_simp
  ring

end GaloisForLFunctions.RHTower

end
