import GaloisForLFunctions.HTGeometry.ArchCount

/-!
# The Sturm window dichotomy

A **window** is a pair of adjacent arches of `g`: three consecutive zeros `p < m < q` with `g > 0` on
`(p,m)` and `g < 0` on `(m,q)`.  Sturm comparison gives a clean dichotomy for each window:

> either the Sturm expression `g'' + γ² g` vanishes somewhere inside the window, or the window is at
> least `π/γ` long.

Windows are disjoint when the underlying zeros are consecutive, so the two alternatives are counted
separately: `h`-zeros are counted by the zero set of `h`, long windows by the length of the ambient
interval.  Where `h` has no zero at all, only the second alternative survives and the window count is
at most `(b-a)γ/π`.

This is the descent step of a Pólya-type zero bound.  Turning it into a bound on the zeros of a full
exponential polynomial additionally requires the *structure* of the zero set — that it is finite and
that the arches alternate — which is a real-analyticity question, not a counting one.
-/

open Set Real

namespace GaloisForLFunctions.HTGeometry

/-- **The window dichotomy.**  Either the Sturm expression vanishes inside the window, or the window
spans at least `π/γ`. -/
theorem sturm_window_dichotomy {g gd gdd h : ℝ → ℝ} {γ p m q : ℝ} (hγ : 0 < γ)
    (hg : ∀ t, HasDerivAt g (gd t) t) (hgd : ∀ t, HasDerivAt gd (gdd t) t)
    (hh : ∀ t, h t = gdd t + γ ^ (2 : ℕ) * g t) (hhcont : Continuous h)
    (hpm : p < m) (hmq : m < q)
    (hgp : g p = 0) (hgm : g m = 0) (hgq : g q = 0)
    (hpos : ∀ t ∈ Ioo p m, 0 < g t) (hneg : ∀ t ∈ Ioo m q, g t < 0) :
    (∃ ξ ∈ Ioo p q, h ξ = 0) ∨ π / γ ≤ q - p := by
  by_cases h1 : m - p < π / γ
  · by_cases h2 : q - m < π / γ
    · exact Or.inl
        (exists_sturm_zero hγ hg hgd hh hhcont hpm hmq h1 h2 hgp hgm hgq hpos hneg)
    · push Not at h2
      exact Or.inr (by linarith)
  · push Not at h1
    exact Or.inr (by linarith)

/-- **The window count where the Sturm expression does not vanish.**  Disjoint windows inside an
interval free of zeros of `g'' + γ² g` number at most `(b-a)γ/π`. -/
theorem card_windows_le {g gd gdd h : ℝ → ℝ} {γ a b : ℝ} (hγ : 0 < γ) (hab : a ≤ b)
    (hg : ∀ t, HasDerivAt g (gd t) t) (hgd : ∀ t, HasDerivAt gd (gdd t) t)
    (hh : ∀ t, h t = gdd t + γ ^ (2 : ℕ) * g t) (hhcont : Continuous h)
    (hnoh : ∀ t ∈ Ioo a b, h t ≠ 0)
    {k : ℕ} (p mid q : Fin k → ℝ)
    (hpa : ∀ i, a ≤ p i) (hqb : ∀ i, q i ≤ b)
    (hpm : ∀ i, p i < mid i) (hmq : ∀ i, mid i < q i)
    (hgp : ∀ i, g (p i) = 0) (hgm : ∀ i, g (mid i) = 0) (hgq : ∀ i, g (q i) = 0)
    (hpos : ∀ i, ∀ t ∈ Ioo (p i) (mid i), 0 < g t)
    (hneg : ∀ i, ∀ t ∈ Ioo (mid i) (q i), g t < 0)
    (hdisj : ∀ i j : Fin k, i < j → q i ≤ p j) :
    (k : ℝ) ≤ (b - a) * γ / π := by
  have hlong : ∀ i, π / γ ≤ q i - p i := by
    intro i
    rcases sturm_window_dichotomy hγ hg hgd hh hhcont (hpm i) (hmq i) (hgp i) (hgm i) (hgq i)
      (hpos i) (hneg i) with ⟨ξ, hξ, hξ0⟩ | hlen
    · exact absurd hξ0 (hnoh ξ ⟨lt_of_le_of_lt (hpa i) hξ.1,
        lt_of_lt_of_le hξ.2 (hqb i)⟩)
    · exact hlen
  have hsum := nsmul_le_of_disjoint_intervals k p q a b (π / γ) hab hpa hqb
    (fun i => le_of_lt (lt_trans (hpm i) (hmq i))) hdisj hlong
  rw [le_div_iff₀ Real.pi_pos]
  have hmul : (k : ℝ) * (π / γ) * γ ≤ (b - a) * γ :=
    mul_le_mul_of_nonneg_right hsum hγ.le
  have hrw : (k : ℝ) * (π / γ) * γ = (k : ℝ) * π := by field_simp
  rw [hrw] at hmul
  linarith

end GaloisForLFunctions.HTGeometry
