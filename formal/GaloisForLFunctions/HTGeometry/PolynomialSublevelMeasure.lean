import Mathlib

/-!
# Sublevel sets of a polynomial have small measure

If a product of `d` distances from a real point to `d` complex points is small, then one of the
distances is small: otherwise the product would exceed the bound.  Hence the sublevel set of a
degree-`d` polynomial with leading coefficient `a` is covered by `d` intervals of half-length
`(ε/a)^{1/d}`, and its Lebesgue measure is at most `2d(ε/a)^{1/d}`.

This is the elementary one-dimensional form of the Łojasiewicz-type estimate that turns a
discriminant lower bound into a measure bound for the near-degeneracy locus.
-/

open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

section Sublevel

variable {d : ℕ}

/-- A real point is at least as far from a complex point as from its real part. -/
theorem abs_sub_re_le_norm (x : ℝ) (z : ℂ) : |x - z.re| ≤ ‖(x : ℂ) - z‖ := by
  have hre : ((x : ℂ) - z).re = x - z.re := by
    simp
  calc |x - z.re| = |((x : ℂ) - z).re| := by rw [hre]
    _ ≤ ‖(x : ℂ) - z‖ := Complex.abs_re_le_norm _

/-- **One factor is small.**  If the product of the `d` distances is at most `δ^d`, some distance is
at most `δ`. -/
theorem exists_norm_sub_le_of_prod_le {z : Fin d → ℂ} {x : ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hd : 0 < d)
    (hprod : ∏ i, ‖(x : ℂ) - z i‖ ≤ δ ^ d) :
    ∃ i, ‖(x : ℂ) - z i‖ ≤ δ := by
  by_contra hcon
  push Not at hcon
  have hne : (Finset.univ : Finset (Fin d)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd)
  rcases eq_or_lt_of_le hδ with hzero | hpos
  · have hprodpos : 0 < ∏ i, ‖(x : ℂ) - z i‖ :=
      Finset.prod_pos fun i _ => lt_of_le_of_lt hδ (hcon i)
    have : δ ^ d = 0 := by
      rw [← hzero]
      exact zero_pow (by omega)
    rw [this] at hprod
    exact absurd hprod (not_le.mpr hprodpos)
  · have hlt : δ ^ d < ∏ i, ‖(x : ℂ) - z i‖ := by
      calc δ ^ d = ∏ _i : Fin d, δ := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ < ∏ i, ‖(x : ℂ) - z i‖ :=
            Finset.prod_lt_prod_of_nonempty (fun i _ => hpos) (fun i _ => hcon i) hne
    exact absurd hprod (not_le.mpr hlt)

/-- **The sublevel set is covered by `d` short intervals.** -/
theorem sublevel_subset_iUnion {z : Fin d → ℂ} {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hd : 0 < d)
    {ε : ℝ} (hεδ : ε / a ≤ δ ^ d) :
    {x : ℝ | a * ∏ i, ‖(x : ℂ) - z i‖ ≤ ε}
      ⊆ ⋃ i, Icc ((z i).re - δ) ((z i).re + δ) := by
  intro x hx
  simp only [mem_setOf_eq] at hx
  have hprod : ∏ i, ‖(x : ℂ) - z i‖ ≤ δ ^ d := by
    have hPa : (∏ i, ‖(x : ℂ) - z i‖) * a ≤ ε := by
      rw [mul_comm]
      exact hx
    exact le_trans ((le_div_iff₀ ha).mpr hPa) hεδ
  obtain ⟨i, hi⟩ := exists_norm_sub_le_of_prod_le hδ hd hprod
  refine mem_iUnion.mpr ⟨i, ?_⟩
  have habs : |x - (z i).re| ≤ δ := le_trans (abs_sub_re_le_norm x (z i)) hi
  have := abs_le.mp habs
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- **The sublevel measure bound.**  The set where a product of `d` distances is below `ε/a` has
measure at most `2dδ`. -/
theorem volume_sublevel_le {z : Fin d → ℂ} {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hd : 0 < d)
    {ε : ℝ} (hεδ : ε / a ≤ δ ^ d) :
    volume {x : ℝ | a * ∏ i, ‖(x : ℂ) - z i‖ ≤ ε}
      ≤ ENNReal.ofReal (2 * d * δ) := by
  classical
  refine le_trans (measure_mono (sublevel_subset_iUnion ha hδ hd hεδ)) ?_
  refine le_trans (measure_iUnion_fintype_le _ _) ?_
  have hterm : ∀ i : Fin d, volume (Icc ((z i).re - δ) ((z i).re + δ))
      ≤ ENNReal.ofReal (2 * δ) := by
    intro i
    rw [Real.volume_Icc]
    refine le_of_eq ?_
    ring_nf
  calc ∑ i : Fin d, volume (Icc ((z i).re - δ) ((z i).re + δ))
      ≤ ∑ _i : Fin d, ENNReal.ofReal (2 * δ) := Finset.sum_le_sum fun i _ => hterm i
    _ = (d : ℝ≥0∞) * ENNReal.ofReal (2 * δ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal (2 * d * δ) := by
        rw [show (2 : ℝ) * d * δ = d * (2 * δ) by ring,
          ENNReal.ofReal_mul (by positivity)]
        simp

end Sublevel

end GaloisForLFunctions.HTGeometry
