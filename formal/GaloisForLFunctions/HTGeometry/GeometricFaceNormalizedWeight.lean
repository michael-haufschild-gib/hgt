import GaloisForLFunctions.HTGeometry.TorsionLanguageFaceExactification

/-!
# Normalized weights on the locked geometric ADE face

For the least geometric face of the surviving bounded ADE patterns, normalize every grouped
integer weight by the common maximal polynomial degree and normalize its convergent valuation
correction.  Each normalized weight converges, and at least one limiting weight is nonzero.
-/

namespace GaloisForLFunctions

open Filter Finset PowerSeries Polynomial Topology

noncomputable section

def geometricPolynomialPatternFace
    (n D K τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (M : ℕ)
    (lam : ℝ) : Finset (Fin M → Fin (D + 1)) :=
  geometricPatternFace lam (polynomialPatternSurvivors n D K τ Q M)

def geometricPolynomialPatternWeight
    (n D K τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {M : ℕ} (p : Fin M → Fin (D + 1)) : ℂ[X] :=
  polynomialPatternWeightPoly n D K τ Q p

def geometricPolynomialFaceWeightDegree
    (n D K τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (M : ℕ)
    (lam : ℝ) : ℕ :=
  finitePolynomialFamilyMaxDegree
    (geometricPolynomialPatternFace n D K τ Q M lam)
    (geometricPolynomialPatternWeight n D K τ Q)

def geometricPolynomialFaceWeightLimit
    (n D K τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (M : ℕ)
    (lam : ℝ) (p : Fin M → Fin (D + 1)) : ℂ :=
  finitePolynomialFamilyLimit
    (geometricPolynomialPatternFace n D K τ Q M lam)
    (geometricPolynomialPatternWeight n D K τ Q) p

/-- The actual grouped ADE weight, polynomially normalized and corrected by the subleading
valuation displacement from the common face limit. -/
def normalizedGeometricPolynomialFaceWeight
    (n D K τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (M : ℕ)
    (lam c0 : ℝ) (c : ℕ → ℝ) (t : ℕ)
    (p : Fin M → Fin (D + 1)) : ℂ :=
  aevalWeight n (D * (t + K) + τ) Q
      (shiftedAtomPatternKey (t + K) K p) /
      ((t + K : ℕ) : ℂ) ^ geometricPolynomialFaceWeightDegree n D K τ Q M lam *
    (Real.exp (-(geometricPatternRemainder c (t + K) K p - D * c0)) : ℂ)

theorem geometricPolynomialPatternFace_nonempty
    {n D K τ M : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ) (lam : ℝ)
    (hS : (polynomialPatternSurvivors n D K τ Q M).Nonempty) :
    (geometricPolynomialPatternFace n D K τ Q M lam).Nonempty :=
  geometricPatternFace_nonempty lam _ hS

/-- Some member of every nonempty locked face has a nonzero normalized limiting weight. -/
theorem exists_ne_zero_geometricPolynomialFaceWeightLimit
    {n D K τ M : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ) (lam : ℝ)
    (hS : (polynomialPatternSurvivors n D K τ Q M).Nonempty) :
    ∃ p ∈ geometricPolynomialPatternFace n D K τ Q M lam,
      geometricPolynomialFaceWeightLimit n D K τ Q M lam p ≠ 0 := by
  let Face := geometricPolynomialPatternFace n D K τ Q M lam
  let P : (Fin M → Fin (D + 1)) → ℂ[X] :=
    geometricPolynomialPatternWeight n D K τ Q
  have hFace : Face.Nonempty := geometricPolynomialPatternFace_nonempty Q lam hS
  have hP : ∀ p ∈ Face, P p ≠ 0 := by
    intro p hp
    exact polynomialPatternSurvivors_weightPoly_ne_zero
      (mem_geometricPatternFace_iff.mp hp).1
  exact exists_ne_zero_finitePolynomialFamilyLimit Face P hFace hP

/-- Every normalized actual grouped weight on the locked face converges to its selected top
coefficient. -/
theorem tendsto_normalizedGeometricPolynomialFaceWeight
    {n D K τ M : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {lam c0 : ℝ} {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 c0))
    {p : Fin M → Fin (D + 1)}
    (hp : p ∈ geometricPolynomialPatternFace n D K τ Q M lam) :
    Tendsto (fun t => normalizedGeometricPolynomialFaceWeight
      n D K τ Q M lam c0 c t p) atTop
      (𝓝 (geometricPolynomialFaceWeightLimit n D K τ Q M lam p)) := by
  have hpS : p ∈ polynomialPatternSurvivors n D K τ Q M :=
    (mem_geometricPatternFace_iff.mp hp).1
  have hcount : (∑ r, (p r : ℕ)) = D :=
    polynomialPatternSurvivors_count hpS
  let Face := geometricPolynomialPatternFace n D K τ Q M lam
  let P : (Fin M → Fin (D + 1)) → ℂ[X] :=
    geometricPolynomialPatternWeight n D K τ Q
  let H := geometricPolynomialFaceWeightDegree n D K τ Q M lam
  let ell := geometricPolynomialFaceWeightLimit n D K τ Q M lam p
  have hpoly0 := tendsto_finitePolynomialFamily_eval_nat_div_pow Face P hp
  have hpoly := hpoly0.comp (tendsto_add_atTop_nat K)
  have hweight : Tendsto (fun t : ℕ =>
      aevalWeight n (D * (t + K) + τ) Q
          (shiftedAtomPatternKey (t + K) K p) /
        (((t + K : ℕ) : ℂ) ^ H)) atTop (𝓝 ell) := by
    apply hpoly.congr'
    filter_upwards [eventually_ge_atTop n] with t ht
    rw [aevalWeight_shiftedAtomPatternKey_eq_eval_poly n D K τ Q p hcount]
    · rfl
    · omega
  have hrem0 := tendsto_geometricPatternRemainder hc K p hcount
  have hrem := hrem0.comp (tendsto_add_atTop_nat K)
  have hreal : Tendsto (fun t : ℕ =>
      Real.exp (-(geometricPatternRemainder c (t + K) K p - D * c0)))
      atTop (𝓝 1) := by
    have hzero : Tendsto (fun t : ℕ =>
        -(geometricPatternRemainder c (t + K) K p - D * c0))
        atTop (𝓝 0) := by
      simpa only [sub_self, neg_zero] using (hrem.sub_const (D * c0)).neg
    simpa only [Real.exp_zero] using hzero.rexp
  have hexp : Tendsto (fun t : ℕ =>
      (Real.exp (-(geometricPatternRemainder c (t + K) K p - D * c0)) : ℂ))
      atTop (𝓝 1) := by
    simpa only [Function.comp_apply, Complex.ofReal_one] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  simpa only [normalizedGeometricPolynomialFaceWeight, H, ell, mul_one] using
    hweight.mul hexp

end

end GaloisForLFunctions
