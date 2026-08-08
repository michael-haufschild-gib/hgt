import GaloisForLFunctions.HTGeometry.JacobiThetaSourcePrincipalPart
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# The line atom of a rank-three mixed-constraint class

A source of vanishing orbital divisor has its poles on finitely many full lattice lines.  The
function that carries one such line is a translate of the theta source:

`A_q(z) = δ log θ(z - q ; σ)`.

It is `1`-periodic, drops by the constant `2πi` under a `σ`-step — hence has vanishing mixed second
difference in every second direction — and its complete principal part is a simple pole of residue
`1` at each point of `q + (1+σ)/2 + ℤ + ℤσ`, with no singularity anywhere else.

* `lineAtom`, `lineAtom_periodic`, `lineAtom_shift`, `lineAtom_mixed_eq_zero`;
* `laurentCoeff_lineAtom_line` — residue `1` on the line;
* `laurentCoeff_lineAtom_of_le`, `laurentCoeff_lineAtom_of_notMem` — and nothing else;
* `iteratedDeriv_periodic` — a period of a function is a period of all its jets.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- A period of a function is a period of every one of its iterated derivatives. -/
theorem iteratedDeriv_periodic {f : ℂ → ℂ} {p : ℂ} (h : ∀ z, f (z + p) = f z) :
    ∀ (j : ℕ) (z : ℂ), iteratedDeriv j f (z + p) = iteratedDeriv j f z := by
  intro j
  induction j with
  | zero => intro z; simpa using h z
  | succ k ih =>
      intro z
      have hfun : (fun w => iteratedDeriv k f (w + p)) = iteratedDeriv k f := funext ih
      have hd := deriv_comp_add_const (iteratedDeriv k f) p z
      rw [hfun] at hd
      rw [iteratedDeriv_succ]
      exact hd.symm

/-- The atom carrying one full `σ`-line of simple poles through `q`. -/
def lineAtom (σ q : ℂ) : ℂ → ℂ := fun z => thetaSource σ (z - q)

theorem lineAtom_periodic (σ q z : ℂ) : lineAtom σ q (z + 1) = lineAtom σ q z := by
  rw [lineAtom, lineAtom, show z + 1 - q = (z - q) + 1 from by ring, thetaSource_periodic]

/-- **The line atom drops by `2πi` under a `σ`-step**, off its poles. -/
theorem lineAtom_shift {σ : ℂ} (hσ : 0 < σ.im) (q : ℂ) {z : ℂ}
    (hz : jacobiTheta₂ (z - q) σ ≠ 0) :
    lineAtom σ q (z + σ) = lineAtom σ q z - 2 * (Real.pi : ℂ) * Complex.I := by
  rw [lineAtom, lineAtom, show z + σ - q = (z - q) + σ from by ring, thetaSource_shift hσ hz]

/-- **The line atom has vanishing mixed second difference.**  The `σ`-difference is constant, so any
further difference of it is zero. -/
theorem lineAtom_mixed_eq_zero {σ : ℂ} (hσ : 0 < σ.im) (q τ : ℂ) {z : ℂ}
    (hz : jacobiTheta₂ (z - q) σ ≠ 0) (hzτ : jacobiTheta₂ (z + τ - q) σ ≠ 0) :
    lineAtom σ q (z + τ + σ) - lineAtom σ q (z + τ) - lineAtom σ q (z + σ)
      + lineAtom σ q z = 0 := by
  have h1 : lineAtom σ q (z + τ + σ) = lineAtom σ q (z + τ) - 2 * (Real.pi : ℂ) * Complex.I :=
    lineAtom_shift hσ q hzτ
  have h2 : lineAtom σ q (z + σ) = lineAtom σ q z - 2 * (Real.pi : ℂ) * Complex.I :=
    lineAtom_shift hσ q hz
  rw [h1, h2]
  ring

/-! ### The complete principal part -/

theorem laurentCoeff_lineAtom (σ q : ℂ) (w : ℂ) (ℓ : ℤ) :
    laurentCoeff (lineAtom σ q) w ℓ = laurentCoeff (thetaSource σ) (w - q) ℓ := by
  have hfun : lineAtom σ q = fun z => thetaSource σ (z + -q) := by
    funext z
    rw [lineAtom, sub_eq_add_neg]
  have h := laurentCoeff_comp_add (thetaSource σ) w (-q) ℓ
  rw [show w + -q = w - q from by ring] at h
  rw [hfun]
  exact h

/-- **The line atom has residue one at every point of its line.** -/
theorem laurentCoeff_lineAtom_line {σ : ℂ} (hσ : 0 < σ.im) (q : ℂ) (m n : ℤ) :
    laurentCoeff (lineAtom σ q) (q + thetaHalfPeriod σ + (m : ℂ) + (n : ℂ) * σ) (-1) = 1 := by
  rw [laurentCoeff_lineAtom,
    show q + thetaHalfPeriod σ + (m : ℂ) + (n : ℂ) * σ - q
      = thetaHalfPeriod σ + (m : ℂ) + (n : ℂ) * σ from by ring]
  exact laurentCoeff_thetaSource_lattice hσ m n

/-- **The line atom has no coefficient below the residue.** -/
theorem laurentCoeff_lineAtom_of_le {σ : ℂ} (hσ : 0 < σ.im) (q w : ℂ) {ℓ : ℤ} (hℓ : ℓ ≤ -2) :
    laurentCoeff (lineAtom σ q) w ℓ = 0 := by
  rw [laurentCoeff_lineAtom]
  exact laurentCoeff_thetaSource_of_le hσ (w - q) hℓ

/-- **Off its line the atom is analytic.** -/
theorem laurentCoeff_lineAtom_of_notMem {σ : ℂ} (hσ : 0 < σ.im) {q w : ℂ}
    (hw : ¬ ∃ m n : ℤ, w = q + thetaHalfPeriod σ + (m : ℂ) + (n : ℂ) * σ) {ℓ : ℤ} (hℓ : ℓ < 0) :
    laurentCoeff (lineAtom σ q) w ℓ = 0 := by
  rw [laurentCoeff_lineAtom]
  refine laurentCoeff_thetaSource_of_notMem hσ ?_ hℓ
  rintro ⟨m, n, hmn⟩
  exact hw ⟨m, n, by linear_combination hmn⟩

theorem meromorphicAt_lineAtom {σ : ℂ} (hσ : 0 < σ.im) (q : ℂ) (z : ℂ) :
    MeromorphicAt (lineAtom σ q) z := by
  have hfun : lineAtom σ q = fun w => thetaSource σ (w + -q) := by
    funext w
    rw [lineAtom, sub_eq_add_neg]
  have h : MeromorphicAt (fun w => thetaSource σ (w + -q)) z :=
    meromorphicAt_comp_add.mpr (meromorphicAt_thetaSource hσ (z + -q))
  rw [hfun]
  exact h

theorem meromorphicOn_lineAtom {σ : ℂ} (hσ : 0 < σ.im) (q : ℂ) :
    MeromorphicOn (lineAtom σ q) Set.univ :=
  fun z _ => meromorphicAt_lineAtom hσ q z

end

end GaloisForLFunctions.HTGeometry
