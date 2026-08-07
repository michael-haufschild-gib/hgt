import GaloisForLFunctions.RHTower.GammaCoPoissonSoninQuadrantSection
import GaloisForLFunctions.RHTower.BurnolCoPoissonMellinNonvanishing
import GaloisForLFunctions.RHTower.BurnolCoPoissonIndicatorSource

/-!
# Co-Poisson annihilator characters in the right half-strip are zeta zeros

Burnol's explicit indicator source is an unconditional inhabitant of the co-Poisson source layer at
every aperture `0 < b ≤ 1`, and its completed Mellin evaluation carries the factor `zeta(w)` times a
factor that is nonzero on `0 < Re w < 1` for `b < 1`.  A point annihilating the whole closed source
space therefore annihilates that inhabitant, which forces `zeta(w) = 0`.

Consequently the standing hypothesis of the quadrant boundary section is exactly the existence of a
nontrivial zeta zero off the critical line: the forced escape law is an unconditional Riemann
hypothesis interface, not a statement about an unconstrained parameter.
-/

open Complex Real
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The cosine transform of the explicit indicator co-Poisson vector is a source generator. -/
theorem coPoissonIndicatorSoninCosine_mem_sourceSpace {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ((coPoissonIndicatorSoninCosine hb hb1 : soninExtendedSpace b) : evenSubspace) ∈
      burnolCoPoissonSourceSpace b := by
  refine (burnolCoPoissonAlgebraicSourceSpace b).le_topologicalClosure ?_
  refine Submodule.subset_span ?_
  exact ⟨coPoissonIndicatorSourceUnconditional hb hb1, Or.inr rfl⟩

/-- **A co-Poisson annihilator character in the right half-strip is a zeta zero.** -/
theorem riemannZeta_eq_zero_of_burnolCoPoissonAnnihilatorPoint
    {w : ℂ} {b : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b) (hb1 : b < 1)
    (hann : BurnolCoPoissonAnnihilatorPoint w b hlo hhi hb) :
    riemannZeta w = 0 := by
  by_contra hz
  have hval := hann ⟨((coPoissonIndicatorSoninCosine hb hb1.le : soninExtendedSpace b) :
      evenSubspace), coPoissonIndicatorSoninCosine_mem_sourceSpace hb hb1.le⟩
  exact (soninMellinEvaluation_coPoissonIndicatorSoninCosine_ne_zero_iff hb hb1
    (by linarith) hhi).mpr hz hval

/-- Every aperture of the ladder is at most the initial one. -/
theorem soninAperture_le {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) (j : ℕ) :
    soninAperture a r j ≤ a := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  rw [soninAperture]
  exact div_le_self ha.le (one_le_pow₀ hr)

/-- **The standing hypothesis of the quadrant section forces a zeta zero off the critical
line.** -/
theorem riemannZeta_eq_zero_of_coPoissonLadderAnnihilator
    {w : ℂ} {a r : ℝ} {hlo : 1 / 2 < w.re} {hhi : w.re < 1} {ha : 0 < a} {hr : 0 < r}
    (ha1 : a < 1) (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) :
    riemannZeta w = 0 := by
  have hlt : soninAperture a r 0 < 1 :=
    lt_of_le_of_lt (soninAperture_le ha hr1 0) ha1
  exact riemannZeta_eq_zero_of_burnolCoPoissonAnnihilatorPoint hlo hhi
    (soninAperture_pos ha hr 0) hlt (hann 0)

/-- **The escape law is a Riemann hypothesis interface.**  If every nontrivial zeta zero lies on the
critical line, no aperture ladder with `a < 1` has a co-Poisson annihilator character in the right
half-strip, so the forced escape never occurs there. -/
theorem not_coPoissonLadderAnnihilator_of_forall_re_eq_half
    {w : ℂ} {a r : ℝ} {hlo : 1 / 2 < w.re} {hhi : w.re < 1} {ha : 0 < a} {hr : 0 < r}
    (ha1 : a < 1) (hr1 : 1 ≤ r)
    (hRH : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2) :
    ¬ CoPoissonLadderAnnihilator w hlo hhi a r ha hr := by
  intro hann
  have hz := riemannZeta_eq_zero_of_coPoissonLadderAnnihilator ha1 hr1 hann
  have := hRH w (by linarith) hhi hz
  linarith

end RHTower
