import Mathlib

/-!
# The contraction form of a Volterra estimate

A Volterra estimate delivers, for every bound `M` on the unknown, an estimate of the form
`|R − 1| ≤ M κ` with `κ` the total kernel mass.  When `κ < 1` this is a contraction: the maximum of
`|R|` on a compact interval satisfies `M ≤ 1 + M κ`, hence `M ≤ 1/(1−κ)` and

```text
|R − 1| ≤ κ/(1 − κ) .
```

No Grönwall inequality is involved, and in particular no continuity of the kernel is needed.  That
matters at a regular singular endpoint, where the kernel density genuinely diverges — logarithmically
— while remaining integrable.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

/-- **The contraction.**  A self-referential Volterra bound with mass `κ < 1` pins the unknown to a
neighbourhood of `1` whose radius depends only on `κ`. -/
theorem abs_sub_one_le_of_self_bound {α β κ : ℝ} {R : ℝ → ℝ}
    (hαβ : α ≤ β) (hRc : ContinuousOn R (Icc α β)) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hbd : ∀ y ∈ Icc α β, ∀ M : ℝ, (∀ t ∈ Icc α β, |R t| ≤ M) → |R y - 1| ≤ M * κ) :
    ∀ y ∈ Icc α β, |R y - 1| ≤ κ / (1 - κ) := by
  have hne : (Icc α β).Nonempty := nonempty_Icc.2 hαβ
  have hcomp : IsCompact (Icc α β) := isCompact_Icc
  obtain ⟨y₀, hy₀, hmax⟩ := hcomp.exists_isMaxOn hne hRc.abs
  set M := |R y₀| with hM
  have hMbd : ∀ t ∈ Icc α β, |R t| ≤ M := fun t ht => hmax ht
  have hM0 : 0 ≤ M := abs_nonneg _
  have hstep : |R y₀ - 1| ≤ M * κ := hbd y₀ hy₀ M hMbd
  have hMle : M ≤ 1 + M * κ := by
    have := abs_sub_abs_le_abs_sub (R y₀) 1
    simp only [abs_one] at this
    linarith [hstep, this]
  have hMfin : M ≤ 1 / (1 - κ) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [hMle]
  intro y hy
  have h := hbd y hy M hMbd
  have hfin : M * κ ≤ κ / (1 - κ) := by
    rw [div_eq_mul_inv, ← one_div]
    nlinarith [hMfin, hκ0, (by linarith : (0:ℝ) < 1 - κ)]
  linarith [h, hfin]

end GaloisForLFunctions.HTGeometry

end
