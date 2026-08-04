import GaloisForLFunctions.RHTower.Sieve.ZeroFreeAssembly
import GaloisForLFunctions.RHTower.Sieve.InvZetaRegular

/-!
# The reciprocal bound along the segment, at nonzero height

`norm_inv_riemannZeta_left_le` bounds `‖1/ζ‖` left of the abscissa in terms of three data attached
to the horizontal segment joining `β + iγ` to `σ + iγ`: that the segment misses the pole, a bound
for `ζ'` along it, and the comparison `M·(σ-β) ≤ (lower bound)/2`.

At nonzero height the first two are unconditional and are discharged here.  The segment misses the
pole for the cheapest possible reason — every point on it has imaginary part `γ`, so the pole, which
sits at height `0`, is not among them.  The derivative bound is Cauchy's estimate on a disc of
radius `R` centred on the segment, whose hypotheses reduce to inequalities on `σ`, `|γ|` and `N`
because the segment stays inside the vertical strip `β ≤ re s ≤ σ`.

What is left as an explicit hypothesis is the comparison, which is the only place a genuine balance
between the offset `σ - 1`, the distance `σ - β` and the growth of `M` has to be struck.
-/

namespace RHTower.Sieve

open Complex

/-- **The segment misses the pole at nonzero height.**  Every point of the horizontal segment has
imaginary part `γ`, and the pole sits at height `0`. -/
theorem segment_ne_one_of_im_ne_zero {β σ γ : ℝ} (hγ : γ ≠ 0) (t : ℝ) :
    ((β : ℂ) + (γ : ℂ) * Complex.I)
      + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)) ≠ 1 := by
  intro h
  have him := (segment_re_im β σ γ t).2
  rw [h] at him
  exact hγ (by simpa using him.symm)

/-- **The derivative bound along the segment.**  Cauchy's estimate applies at every point of the
segment at once: the real part is between `β` and `σ`, the imaginary part is exactly `γ`, so the
single condition `σ + |γ| + R ≤ N` covers the whole segment. -/
theorem norm_deriv_riemannZeta_segment_le {β σ γ R : ℝ} {N : ℕ} (hR : 0 < R)
    (hβσ : β ≤ σ) (hβ : 1 / 2 + R ≤ β) (hlow : 1 - 1 / Real.log N ≤ β - R)
    (hγ : R < |γ|) (hN : 2 ≤ N) (hNbig : σ + |γ| + R ≤ (N : ℝ)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv riemannZeta (((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)))‖
        ≤ (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R := by
  intro t ht
  obtain ⟨hre, him⟩ := segment_re_im β σ γ t
  have hβ0 : 0 ≤ β := by linarith
  have hrege : β ≤ (((β : ℂ) + (γ : ℂ) * Complex.I)
      + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))).re := by
    rw [hre]
    nlinarith [ht.1, ht.2]
  have hreb : (((β : ℂ) + (γ : ℂ) * Complex.I)
      + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))).re
      ≤ σ := by
    rw [hre]
    nlinarith [ht.1, ht.2]
  have hnorm : ‖((β : ℂ) + (γ : ℂ) * Complex.I)
      + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))‖ + R
      ≤ (N : ℝ) := by
    have hb := Complex.norm_le_abs_re_add_abs_im (((β : ℂ) + (γ : ℂ) * Complex.I)
      + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)))
    rw [hre, him] at hb
    have habs : |β + t * (σ - β)| = β + t * (σ - β) := by
      refine abs_of_nonneg ?_
      nlinarith [ht.1, ht.2]
    rw [habs] at hb
    have hle : β + t * (σ - β) ≤ σ := by nlinarith [ht.1, ht.2]
    linarith
  exact norm_deriv_riemannZeta_le_log_of_re_ge hR hrege him hβ hlow hγ hN hnorm

/-- **The reciprocal bound left of the abscissa, with the geometry discharged.**  Only the
comparison between the derivative bound, the distance moved left, and the lower bound at `σ` is left
as a hypothesis; everything about the segment and about Cauchy's estimate is proved. -/
theorem norm_inv_riemannZeta_left_le_segment {β σ γ R : ℝ} {N : ℕ} (hR : 0 < R)
    (hσ1 : 1 < σ) (hβσ : β ≤ σ) (hβ : 1 / 2 + R ≤ β) (hlow : 1 - 1 / Real.log N ≤ β - R)
    (hγ : R < |γ|) (hN : 2 ≤ N) (hNbig : σ + |γ| + R ≤ (N : ℝ))
    {B₀ : ℝ} (hB : ‖riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤ B₀)
    (hhalf : (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R
        * (σ - β)
      ≤ Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4) / 2) :
    ‖(riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I))⁻¹‖
      ≤ 2 / Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4) := by
  have hγ0 : γ ≠ 0 := by
    intro h
    rw [h] at hγ
    simp at hγ
    linarith
  exact norm_inv_riemannZeta_left_le hσ1
    (fun t _ => segment_ne_one_of_im_ne_zero hγ0 t)
    (norm_deriv_riemannZeta_segment_le hR hβσ hβ hlow hγ hN hNbig)
    hβσ hB hhalf

/-- The same bound transported to `invZeta`, which is the function the contour argument uses. -/
theorem norm_invZeta_left_le_segment {β σ γ R : ℝ} {N : ℕ} (hR : 0 < R)
    (hσ1 : 1 < σ) (hβσ : β ≤ σ) (hβ : 1 / 2 + R ≤ β) (hlow : 1 - 1 / Real.log N ≤ β - R)
    (hγ : R < |γ|) (hN : 2 ≤ N) (hNbig : σ + |γ| + R ≤ (N : ℝ))
    {B₀ : ℝ} (hB : ‖riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤ B₀)
    (hhalf : (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R
        * (σ - β)
      ≤ Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4) / 2) :
    ‖invZeta ((β : ℂ) + (γ : ℂ) * Complex.I)‖
      ≤ 2 / Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4) := by
  have hγ0 : γ ≠ 0 := by
    intro h
    rw [h] at hγ
    simp at hγ
    linarith
  have hne : ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 1 := by
    intro h
    exact hγ0 (by simpa using congrArg Complex.im h)
  rw [norm_invZeta_eq hne]
  exact norm_inv_riemannZeta_left_le_segment hR hσ1 hβσ hβ hlow hγ hN hNbig hB hhalf

end RHTower.Sieve
