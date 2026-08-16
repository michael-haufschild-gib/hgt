import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# The harmonic-primitive limit reduces to Mertens' second theorem

The closed form of the harmonic primitive is `J_N = ∑_{n≤N} Λ(n)/n − H_N − R(N)/(N+1)`.  Since
`H_N − log N → γ`, the limit `J_N → −2γ` is exactly Mertens' second theorem
`∑_{n≤N} Λ(n)/n − log N → −γ`, together with the vanishing of the boundary term.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- **The harmonic-primitive limit is Mertens' second theorem.**  Given the boundary term of the
Abel identity tends to zero, `J_N → −2γ` is equivalent to
`∑_{n≤N} Λ(n)/n − log N → −γ`. -/
theorem tendsto_harmonicPrimitive_of_mertens {S R : ℕ → ℝ}
    (hR : Tendsto (fun N : ℕ => R N / (N + 1)) atTop (𝓝 0))
    (hS : Tendsto (fun N : ℕ => S N - Real.log N) atTop
      (𝓝 (-Real.eulerMascheroniConstant))) :
    Tendsto (fun N : ℕ => S N - (harmonic N : ℝ) - R N / (N + 1)) atTop
      (𝓝 (-2 * Real.eulerMascheroniConstant)) := by
  have hharm : Tendsto (fun N : ℕ => (harmonic N : ℝ) - Real.log N) atTop
      (𝓝 Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have hdiff : Tendsto (fun N : ℕ => (S N - Real.log N) - ((harmonic N : ℝ) - Real.log N)) atTop
      (𝓝 (-Real.eulerMascheroniConstant - Real.eulerMascheroniConstant)) := hS.sub hharm
  have hcong : ∀ N : ℕ, (S N - Real.log N) - ((harmonic N : ℝ) - Real.log N)
      = S N - (harmonic N : ℝ) := by
    intro N
    ring
  have hmain : Tendsto (fun N : ℕ => S N - (harmonic N : ℝ)) atTop
      (𝓝 (-Real.eulerMascheroniConstant - Real.eulerMascheroniConstant)) :=
    hdiff.congr hcong
  have hfinal := hmain.sub hR
  have hval : -Real.eulerMascheroniConstant - Real.eulerMascheroniConstant - 0
      = -2 * Real.eulerMascheroniConstant := by ring
  rw [hval] at hfinal
  exact hfinal

/-- **The converse reduction.**  Conversely, if the harmonic primitive tends to `−2γ` and the
boundary term vanishes, then Mertens' second theorem holds. -/
theorem tendsto_mertens_of_harmonicPrimitive {S R : ℕ → ℝ}
    (hR : Tendsto (fun N : ℕ => R N / (N + 1)) atTop (𝓝 0))
    (hJ : Tendsto (fun N : ℕ => S N - (harmonic N : ℝ) - R N / (N + 1)) atTop
      (𝓝 (-2 * Real.eulerMascheroniConstant))) :
    Tendsto (fun N : ℕ => S N - Real.log N) atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hharm : Tendsto (fun N : ℕ => (harmonic N : ℝ) - Real.log N) atTop
      (𝓝 Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have hsum := (hJ.add hR).add hharm
  have hcong : ∀ N : ℕ, (S N - (harmonic N : ℝ) - R N / (N + 1)) + R N / (N + 1)
      + ((harmonic N : ℝ) - Real.log N) = S N - Real.log N := by
    intro N
    ring
  have hval : -2 * Real.eulerMascheroniConstant + 0 + Real.eulerMascheroniConstant
      = -Real.eulerMascheroniConstant := by ring
  rw [hval] at hsum
  exact hsum.congr hcong

end

end RHTower
