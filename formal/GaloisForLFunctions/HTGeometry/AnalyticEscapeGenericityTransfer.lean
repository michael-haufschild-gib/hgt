import GaloisForLFunctions.HTGeometry.AnalyticSpectralRelationEscape
import GaloisForLFunctions.HTGeometry.PolynomialHermitianMatrixProjectiveGenericity

/-!
# From one analytic branch escape to real-parameter spectral genericity

A complex polynomial law vanishing at every real parameter vanishes identically, because its
coefficientwise real and imaginary parts are real polynomials vanishing on all of `ℝ^m`.  So a
single complex parameter at which a balanced spectral obstruction survives already produces a real
one.

Combining this with the simultaneous analytic escape of every labelling of a spectral relation
turns local analytic information -- eigenvalue branches on one connected chart, each labelling
escaped somewhere on that chart -- into the global genericity statement: the real parameters whose
spectrum admits no balanced integer relation are dense, residual, and of full measure.
-/

open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coefficients of the coefficientwise real part are the real parts of the coefficients. -/
theorem coeff_complexMvPolynomialRealPart {θ : Type*} (P : MvPolynomial θ ℂ) (d : θ →₀ ℕ) :
    MvPolynomial.coeff d (complexMvPolynomialRealPart P) = (MvPolynomial.coeff d P).re := by
  classical
  rw [complexMvPolynomialRealPart, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' P.support d fun e => (MvPolynomial.coeff e P).re]
  by_cases hd : d ∈ P.support
  · rw [if_pos hd]
  · rw [if_neg hd, MvPolynomial.notMem_support_iff.mp hd, Complex.zero_re]

/-- Coefficients of the coefficientwise imaginary part are the imaginary parts of the
coefficients. -/
theorem coeff_complexMvPolynomialImagPart {θ : Type*} (P : MvPolynomial θ ℂ) (d : θ →₀ ℕ) :
    MvPolynomial.coeff d (complexMvPolynomialImagPart P) = (MvPolynomial.coeff d P).im := by
  classical
  rw [complexMvPolynomialImagPart, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' P.support d fun e => (MvPolynomial.coeff e P).im]
  by_cases hd : d ∈ P.support
  · rw [if_pos hd]
  · rw [if_neg hd, MvPolynomial.notMem_support_iff.mp hd, Complex.zero_im]

/-- **Real parameters are Zariski dense.**  A complex polynomial law vanishing at every real
parameter is the zero polynomial. -/
theorem eq_zero_of_eval_real_eq_zero {m : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (h : ∀ p : Fin m → ℝ,
      MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ)) P = 0) :
    P = 0 := by
  have hre : complexMvPolynomialRealPart P = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [eval_complexMvPolynomialRealPart, h x, Complex.zero_re, map_zero]
  have him : complexMvPolynomialImagPart P = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [eval_complexMvPolynomialImagPart, h x, Complex.zero_im, map_zero]
  refine MvPolynomial.ext _ _ fun d => ?_
  refine Complex.ext ?_ ?_
  · rw [← coeff_complexMvPolynomialRealPart, hre]
    simp
  · rw [← coeff_complexMvPolynomialImagPart, him]
    simp

/-- **Complex witnesses give real witnesses.**  A complex polynomial law nonzero at one complex
parameter is nonzero at some real parameter. -/
theorem exists_real_eval_ne_zero_of_complex {m : ℕ} (P : MvPolynomial (Fin m) ℂ)
    {z : Fin m → ℂ} (h : MvPolynomial.eval₂ (RingHom.id ℂ) z P ≠ 0) :
    ∃ p : Fin m → ℝ,
      MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ)) P ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact h (by rw [eq_zero_of_eval_real_eq_zero P hcon, MvPolynomial.eval₂_zero])

/-- Genericity of a polynomial matrix family from real witnesses for each balanced obstruction. -/
theorem polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure_of_witness
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (hwitness :
      ∀ k : I → ℤ,
        SpectralCharacterBalanced k →
        k ≠ 0 →
        ∃ p : Fin m → ℝ,
          MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ))
            (complexSpectralCoefficientObstructionPullback
              (matrixCharacteristicElementaryPolynomial M) k) ≠ 0) :
    Dense (polynomialMatrixProjectiveGenericSet M) ∧
      polynomialMatrixProjectiveGenericSet M ∈ residual (Fin m → ℝ) ∧
      volume (polynomialMatrixProjectiveGenericSet M)ᶜ = 0 :=
  complexSpectralCoefficientProjectiveGenericSet_dense_residual_fullMeasure_of_witness
    (matrixCharacteristicElementaryPolynomial M) hwitness

/-- **Analytic escape transfer.**  Analytic eigenvalue branches on one connected chart which are
simple there, together with an escape of every labelling of every nonzero balanced relation
somewhere on that chart, force the real parameters with no balanced integer spectral relation to be
dense, residual, and of full measure. -/
theorem polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure_of_analyticBranchEscape
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (U : Set (Fin m → ℂ)) (hUopen : IsOpen U) (hUconnected : IsPreconnected U)
    (hUnonempty : U.Nonempty)
    (branch : I → (Fin m → ℂ) → ℂ)
    (hbranchA : ∀ x, AnalyticOnNhd ℂ (branch x) U)
    (hbranchInj : ∀ p ∈ U, Function.Injective fun x => branch x p)
    (hbranchRoot : ∀ x, ∀ p ∈ U,
      matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) p), branch x p) = 0)
    (hlabel :
      ∀ k : I → ℤ,
        SpectralCharacterBalanced k →
        k ≠ 0 →
        ∀ σ : Equiv.Perm I,
          ∃ p ∈ U, permutedAnalyticSpectralRelation k branch σ p ≠ 0) :
    Dense (polynomialMatrixProjectiveGenericSet M) ∧
      polynomialMatrixProjectiveGenericSet M ∈ residual (Fin m → ℝ) ∧
      volume (polynomialMatrixProjectiveGenericSet M)ᶜ = 0 := by
  refine polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure_of_witness M ?_
  intro k hbalanced hk
  obtain ⟨p, hpU, hp⟩ :=
    exists_spectralRelationOrbitValueComplex_ne_zero_of_analytic k branch U hUopen hUconnected
      hUnonempty hbranchA (hlabel k hbalanced hk)
  refine exists_real_eval_ne_zero_of_complex _ (z := p) ?_
  rw [eval_complexSpectralCoefficientObstructionPullback]
  have hcoeff : ∀ i : Fin (Fintype.card I),
      MvPolynomial.eval₂ (RingHom.id ℂ) p (matrixCharacteristicElementaryPolynomial M i)
        = MvPolynomial.eval₂ (Rat.castHom ℂ) (fun x => branch x p)
            (MvPolynomial.esymm I ℚ (i.1 + 1)) := by
    intro i
    rw [eval_matrixCharacteristicElementaryPolynomial]
    exact matrixCharacteristicElementaryCoefficient_eq_rootPacket _ (fun x => branch x p)
      (hbranchInj p hpU) (fun x => hbranchRoot x p hpU) i
  simp only [hcoeff]
  rw [eval₂_spectralRelationCoefficientPolynomial_complex_esymm,
    eval₂_spectralRelationOrbitPolynomial_complex]
  exact hp

end

end GaloisForLFunctions.HTGeometry
