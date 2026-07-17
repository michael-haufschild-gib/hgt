import GaloisForLFunctions.HTGeometry.GeometricPeriodicPhase
import GaloisForLFunctions.HTGeometry.DATaylorLogRatioResonance

/-!
# Algebraic consequence of an exact geometric pattern tie

Two distinct bounded multiplicity patterns at the same geometric valuation produce an explicit
nonzero integer polynomial vanishing at the geometric ratio.
-/

namespace GaloisForLFunctions

open Finset Polynomial

theorem atomPatternDifferencePolynomial_eval₂_eq_geometricPatternValue_sub
    {M D : ℕ} (lam : ℝ) (p₀ p₁ : Fin M → Fin (D + 1)) :
    Polynomial.eval₂ (algebraMap ℤ ℝ) lam
        (atomPatternDifferencePolynomial p₀ p₁) =
      geometricPatternValue lam p₁ - geometricPatternValue lam p₀ := by
  classical
  rw [geometricPatternValue, geometricPatternValue, ← Finset.sum_sub_distrib]
  rw [atomPatternDifferencePolynomial, Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.eval₂_monomial]
  push_cast
  ring

theorem isAlgebraic_of_distinct_geometricPatternValue_eq
    {M D : ℕ} {lam : ℝ} {p₀ p₁ : Fin M → Fin (D + 1)}
    (hne : p₀ ≠ p₁)
    (hvalue : geometricPatternValue lam p₀ = geometricPatternValue lam p₁) :
    IsAlgebraic ℤ lam := by
  let Q := atomPatternDifferencePolynomial p₀ p₁
  have hQ : Q ≠ 0 := atomPatternDifferencePolynomial_ne_zero hne
  refine ⟨Q, hQ, ?_⟩
  rw [Polynomial.aeval_def]
  change Polynomial.eval₂ (algebraMap ℤ ℝ) lam Q = 0
  rw [show Q = atomPatternDifferencePolynomial p₀ p₁ by rfl,
    atomPatternDifferencePolynomial_eval₂_eq_geometricPatternValue_sub]
  exact sub_eq_zero.mpr hvalue.symm

/-- If a nonempty finite exact geometric cascade has nonzero grouped weights and phases, every
atom has a distinct tied partner; consequently the geometric ratio is algebraic. -/
theorem isAlgebraic_of_nonempty_exactGeometricPattern_cascade
    {M D : ℕ} (S : Finset (Fin M → Fin (D + 1)))
    (weight : (Fin M → Fin (D + 1)) → ℂ[X])
    (phase : (Fin M → Fin (D + 1)) → ℂ)
    {A lam : ℝ} (hA : 0 < A) (hlam : 1 < lam)
    (hS : S.Nonempty)
    (hphase : ∀ a ∈ S, phase a ≠ 0)
    (hweight : ∀ a ∈ S, weight a ≠ 0)
    (hidentity : ∀ q : ℕ,
      ∑ a ∈ S, (weight a).eval (q : ℂ) * phase a *
        ((Real.exp (-A * geometricPatternValue lam a * lam ^ q) : ℝ) : ℂ) = 0) :
    IsAlgebraic ℤ lam := by
  classical
  obtain ⟨a, haS⟩ := hS
  let Face := S.filter fun b => geometricPatternValue lam b = geometricPatternValue lam a
  have haFace : a ∈ Face := by simp [Face, haS]
  have hcard := finite_exactGeometricLevel_no_singleton S
    (geometricPatternValue lam) weight phase hA hlam hphase hweight hidentity
    (geometricPatternValue lam a)
  have htie : ∃ b ∈ Face, b ≠ a := by
    by_contra hnot
    have hFaceEq : Face = {a} := by
      ext b
      constructor
      · intro hb
        have hba : b = a := by
          by_contra hne
          exact hnot ⟨b, hb, hne⟩
        simpa [hba]
      · intro hb
        have hba : b = a := by simpa using hb
        simpa [hba] using haFace
    apply hcard
    rw [show S.filter (fun b => geometricPatternValue lam b =
      geometricPatternValue lam a) = Face by rfl, hFaceEq]
    simp
  obtain ⟨b, hbFace, hba⟩ := htie
  have hvalue := (Finset.mem_filter.mp hbFace).2
  exact isAlgebraic_of_distinct_geometricPatternValue_eq hba.symm hvalue.symm

end GaloisForLFunctions
