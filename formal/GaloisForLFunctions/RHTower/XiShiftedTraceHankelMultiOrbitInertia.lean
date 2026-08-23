import GaloisForLFunctions.RHTower.TraceHankelMultiOrbitInertia
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryPadeContactParity

/-!
# Simultaneous off-critical Xi orbit inertia in the full trace--Hankel source

Conjugation folding preserves the absolute summability and local finiteness of the shifted
reciprocal-square Xi divisor. Its folded trace--Hankel Gram is exactly twice the existing aperture
Hankel source form. Consequently, any `k` distinct nonreal folded Xi divisor nodes force a
negative-definite `k`-dimensional polynomial block in the full, multiplicity-retaining source.
-/

namespace RHTower

open scoped ComplexConjugate BigOperators
open Complex Filter Matrix Polynomial Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Upper-half-plane conjugation folding preserves complex norm. -/
theorem norm_complexConjugationFold (z : ℂ) :
    ‖complexConjugationFold z‖ = ‖z‖ := by
  rcases complexConjugationFold_eq_self_or_conj z with hz | hz
  · rw [hz]
  · rw [hz, norm_conj]

/-- The conjugation-folded shifted reciprocal-square Xi divisor remains absolutely summable. -/
theorem summable_folded_xiShiftedReciprocalSquare
    {y : ℝ} (hy : 0 ≤ y) :
    Summable (fun q : XiZeroCopy =>
      complexConjugationFold (xiShiftedReciprocalSquare y q)) := by
  apply Summable.of_norm
  simpa [norm_complexConjugationFold] using
    (summable_xiShiftedReciprocalSquare_pow hy 0).norm

/-- Every diagonal polynomial trace test over the folded shifted Xi divisor is summable. -/
theorem summable_folded_xiShiftedReciprocalTraceHankelTerm
    {y : ℝ} (hy : 0 ≤ y) (p : Polynomial ℝ) :
    Summable (fun q : XiZeroCopy =>
      complexConjugationFold (xiShiftedReciprocalSquare y q) *
        evalRealPolynomial p
          (complexConjugationFold (xiShiftedReciprocalSquare y q)) ^ 2) := by
  apply Summable.of_norm
  exact (summable_xiShiftedReciprocalTraceHankelTerm hy p).norm.congr fun q => by
    let z := xiShiftedReciprocalSquare y q
    rcases complexConjugationFold_eq_self_or_conj z with hz | hz
    · simp only [z, hz, xiShiftedReciprocalTraceHankelTerm]
    · simp only [z, hz, xiShiftedReciprocalTraceHankelTerm,
        evalRealPolynomial_conj, ← map_pow, ← map_mul, norm_conj]

/-- Polarization upgrades diagonal folded trace summability to all polynomial pairs. -/
theorem summable_folded_xiShiftedReciprocalTraceHankelPairTerm
    {y : ℝ} (hy : 0 ≤ y) (p r : Polynomial ℝ) :
    Summable (fun q : XiZeroCopy =>
      complexConjugationFold (xiShiftedReciprocalSquare y q) *
        evalRealPolynomial p
          (complexConjugationFold (xiShiftedReciprocalSquare y q)) *
        evalRealPolynomial r
          (complexConjugationFold (xiShiftedReciprocalSquare y q))) := by
  let lam : XiZeroCopy → ℂ := fun q =>
    complexConjugationFold (xiShiftedReciprocalSquare y q)
  have hp := summable_folded_xiShiftedReciprocalTraceHankelTerm hy p
  have hr := summable_folded_xiShiftedReciprocalTraceHankelTerm hy r
  have hpr := summable_folded_xiShiftedReciprocalTraceHankelTerm hy (p + r)
  have h := ((hpr.sub hp).sub hr).mul_left (2 : ℂ)⁻¹
  exact h.congr fun q => by
    have heval : evalRealPolynomial (p + r)
        (complexConjugationFold (xiShiftedReciprocalSquare y q)) =
      evalRealPolynomial p
          (complexConjugationFold (xiShiftedReciprocalSquare y q)) +
        evalRealPolynomial r
          (complexConjugationFold (xiShiftedReciprocalSquare y q)) := by
      simp [evalRealPolynomial]
    rw [heval]
    ring

/-- The folded abstract trace--Hankel Gram is exactly twice the full shifted Xi aperture source. -/
theorem foldedTraceHankelGram_xiShiftedReciprocalSquare_eq
    {y : ℝ} (hy : 0 ≤ y) (p r : Polynomial ℝ) :
    foldedTraceHankelGram
        (fun q : XiZeroCopy =>
          complexConjugationFold (xiShiftedReciprocalSquare y q)) p r =
      2 * ∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y p r q := by
  rw [foldedTraceHankelGram]
  rw [Complex.re_tsum
    (summable_folded_xiShiftedReciprocalTraceHankelPairTerm hy p r)]
  congr 1
  apply tsum_congr
  intro q
  exact (xiShiftedApertureHankelPairTerm_eq_conjugationFold y p r q).symm

/-- Any finite packet of distinct off-critical folded Xi divisor nodes forces a negative-definite
block of the same dimension in the full, multiplicity-retaining shifted Xi source form. -/
theorem exists_xiShiftedApertureHankelPolynomialSubspace_negative
    {y : ℝ} (hy : 0 < y) {k : ℕ} (s : Fin k → XiZeroCopy)
    (hfold : Function.Injective (fun j =>
      complexConjugationFold (xiShiftedReciprocalSquare y (s j))))
    (him : ∀ j,
      (complexConjugationFold (xiShiftedReciprocalSquare y (s j))).im ≠ 0) :
    ∃ q : Fin k → Polynomial ℝ,
      Module.finrank ℝ (Submodule.span ℝ (Set.range q)) = k ∧
      ∀ x : Fin k → ℝ, x ≠ 0 →
        realQuad (fun j l => ∑' a : XiZeroCopy,
          xiShiftedApertureHankelPairTerm y (q j) (q l) a) x < 0 := by
  let lam : XiZeroCopy → ℂ := fun a =>
    complexConjugationFold (xiShiftedReciprocalSquare y a)
  have hne : ∀ a, lam a ≠ 0 := by
    intro a
    dsimp only [lam]
    rcases complexConjugationFold_eq_self_or_conj
      (xiShiftedReciprocalSquare y a) with ha | ha
    · rw [ha]
      exact xiShiftedReciprocalSquare_ne_zero hy.le a
    · rw [ha]
      simpa using xiShiftedReciprocalSquare_ne_zero hy.le a
  have hfinite : ∀ {r : ℝ}, 0 < r → {a : XiZeroCopy | r ≤ ‖lam a‖}.Finite := by
    intro r hr
    simpa only [lam, norm_complexConjugationFold] using
      xiShiftedReciprocalSquare_finite_norm_ge hy.le hr
  have hsum : Summable lam := by
    simpa only [lam] using summable_folded_xiShiftedReciprocalSquare hy.le
  have hupper : ∀ a, 0 ≤ (lam a).im := by
    intro a
    simp [lam, complexConjugationFold]
  obtain ⟨q, hdim, hneg⟩ :=
    exists_foldedTraceHankelPolynomialSubspace_negative_of_upper
      lam hne hfinite hsum hupper s hfold him
  refine ⟨q, hdim, ?_⟩
  intro x hx
  let M : Matrix (Fin k) (Fin k) ℝ := fun j l =>
    ∑' a : XiZeroCopy, xiShiftedApertureHankelPairTerm y (q j) (q l) a
  have hentry (j l : Fin k) :
      foldedTraceHankelGram lam (q j) (q l) = 2 * M j l := by
    simpa only [lam, M] using
      foldedTraceHankelGram_xiShiftedReciprocalSquare_eq hy.le (q j) (q l)
  have hscale : realQuad (fun j l => foldedTraceHankelGram lam (q j) (q l)) x =
      2 * realQuad M x := by
    simp only [realQuad, hentry]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _hl
    ring
  have hxneg := hneg x hx
  rw [hscale] at hxneg
  change realQuad M x < 0
  linarith

end

end RHTower
