import GaloisForLFunctions.HTGeometry.RealPolynomialGenericity

/-!
# Complex polynomial laws on real parameter spaces

The real and imaginary parts of a complex-coefficient multivariate
polynomial, restricted to real inputs, are real polynomials.  Hence a
countable family of complex polynomial laws, each nonzero at some real
parameter, is simultaneously nonzero on a dense residual full-measure
real parameter set.
-/

open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coefficientwise real part of a complex polynomial, viewed on real
variables. -/
def complexMvPolynomialRealPart
    {θ : Type*} (P : MvPolynomial θ ℂ) :
    MvPolynomial θ ℝ :=
  ∑ d ∈ P.support,
    MvPolynomial.monomial d
      (MvPolynomial.coeff d P).re

/-- Coefficientwise imaginary part of a complex polynomial, viewed on real
variables. -/
def complexMvPolynomialImagPart
    {θ : Type*} (P : MvPolynomial θ ℂ) :
    MvPolynomial θ ℝ :=
  ∑ d ∈ P.support,
    MvPolynomial.monomial d
      (MvPolynomial.coeff d P).im

private theorem realMonomial_complexification
    {θ : Type*} (x : θ → ℝ)
    (d : θ →₀ ℕ) :
    (d.prod fun n e => (x n : ℂ) ^ e) =
      (d.prod fun n e => x n ^ e : ℝ) := by
  change
    (∏ n ∈ d.support, (x n : ℂ) ^ d n) =
      ((∏ n ∈ d.support, x n ^ d n : ℝ) : ℂ)
  norm_cast

theorem eval_complexMvPolynomialRealPart
    {θ : Type*}
    (P : MvPolynomial θ ℂ) (x : θ → ℝ) :
    MvPolynomial.eval x
        (complexMvPolynomialRealPart P) =
      (MvPolynomial.eval₂ (RingHom.id ℂ)
        (fun i => (x i : ℂ)) P).re := by
  rw [complexMvPolynomialRealPart,
    MvPolynomial.eval_sum]
  have hcomplex :
      MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun i => (x i : ℂ)) P =
        ∑ d ∈ P.support,
          MvPolynomial.eval₂ (RingHom.id ℂ)
            (fun i => (x i : ℂ))
            (MvPolynomial.monomial d
              (MvPolynomial.coeff d P)) := by
    conv_lhs => rw [P.as_sum]
    rw [MvPolynomial.eval₂_sum]
  rw [hcomplex]
  change
    _ = Complex.reCLM
      (∑ d ∈ P.support,
        MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun i => (x i : ℂ))
          (MvPolynomial.monomial d
            (MvPolynomial.coeff d P)))
  rw [map_sum]
  simp only [MvPolynomial.eval_monomial,
    MvPolynomial.eval₂_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  rw [realMonomial_complexification]
  simp

theorem eval_complexMvPolynomialImagPart
    {θ : Type*}
    (P : MvPolynomial θ ℂ) (x : θ → ℝ) :
    MvPolynomial.eval x
        (complexMvPolynomialImagPart P) =
      (MvPolynomial.eval₂ (RingHom.id ℂ)
        (fun i => (x i : ℂ)) P).im := by
  rw [complexMvPolynomialImagPart,
    MvPolynomial.eval_sum]
  have hcomplex :
      MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun i => (x i : ℂ)) P =
        ∑ d ∈ P.support,
          MvPolynomial.eval₂ (RingHom.id ℂ)
            (fun i => (x i : ℂ))
            (MvPolynomial.monomial d
              (MvPolynomial.coeff d P)) := by
    conv_lhs => rw [P.as_sum]
    rw [MvPolynomial.eval₂_sum]
  rw [hcomplex]
  change
    _ = Complex.imCLM
      (∑ d ∈ P.support,
        MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun i => (x i : ℂ))
          (MvPolynomial.monomial d
            (MvPolynomial.coeff d P)))
  rw [map_sum]
  simp only [MvPolynomial.eval_monomial,
    MvPolynomial.eval₂_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  rw [realMonomial_complexification]
  simp

/-- Real parameters avoiding every member of a complex polynomial family. -/
def complexPolynomialRealAvoidanceSet
    {m : ℕ}
    (P : ℕ → MvPolynomial (Fin m) ℂ) :
    Set (Fin m → ℝ) :=
  {x |
    ∀ k,
      MvPolynomial.eval₂ (RingHom.id ℂ)
        (fun i => (x i : ℂ)) (P k) ≠ 0}

/-- Countably many complex polynomial laws that are individually nonzero at
real parameter values are simultaneously nonzero on a dense residual
full-measure real parameter set. -/
theorem
    complexPolynomialRealAvoidanceSet_dense_residual_fullMeasure
    {m : ℕ}
    (P : ℕ → MvPolynomial (Fin m) ℂ)
    (hwitness :
      ∀ k, ∃ x : Fin m → ℝ,
        MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun i => (x i : ℂ)) (P k) ≠ 0) :
    Dense (complexPolynomialRealAvoidanceSet P) ∧
    complexPolynomialRealAvoidanceSet P ∈
      residual (Fin m → ℝ) ∧
    volume (complexPolynomialRealAvoidanceSet P)ᶜ = 0 := by
  choose witness hwitness using hwitness
  let Q : ℕ → MvPolynomial (Fin m) ℝ :=
    fun k =>
      if
        (MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun i => (witness k i : ℂ))
          (P k)).re ≠ 0
      then complexMvPolynomialRealPart (P k)
      else complexMvPolynomialImagPart (P k)
  have hQ : ∀ k, Q k ≠ 0 := by
    intro k
    by_cases hre :
        (MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun i => (witness k i : ℂ))
          (P k)).re ≠ 0
    · rw [show Q k =
          complexMvPolynomialRealPart (P k) by
            unfold Q
            rw [if_pos hre]]
      intro hzero
      apply hre
      rw [← eval_complexMvPolynomialRealPart,
        hzero]
      simp
    · have him :
          (MvPolynomial.eval₂ (RingHom.id ℂ)
            (fun i => (witness k i : ℂ))
            (P k)).im ≠ 0 := by
        intro himzero
        apply hwitness k
        apply Complex.ext
        · simpa using not_ne_iff.mp hre
        · simpa using himzero
      rw [show Q k =
          complexMvPolynomialImagPart (P k) by
            unfold Q
            rw [if_neg hre]]
      intro hzero
      apply him
      rw [← eval_complexMvPolynomialImagPart,
        hzero]
      simp
  obtain ⟨hQdense, hQresidual, hQnull⟩ :=
    realPolynomialAvoidanceSet_dense_residual_fullMeasure
      Q hQ
  have hsubset :
      realPolynomialAvoidanceSet Q ⊆
        complexPolynomialRealAvoidanceSet P := by
    intro x hx k
    by_cases hre :
        (MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun i => (witness k i : ℂ))
          (P k)).re ≠ 0
    · intro hzero
      have hxreal := hx k
      rw [show Q k =
          complexMvPolynomialRealPart (P k) by
            unfold Q
            rw [if_pos hre],
        eval_complexMvPolynomialRealPart,
        hzero] at hxreal
      simp at hxreal
    · intro hzero
      have hximag := hx k
      rw [show Q k =
          complexMvPolynomialImagPart (P k) by
            unfold Q
            rw [if_neg hre],
        eval_complexMvPolynomialImagPart,
        hzero] at hximag
      simp at hximag
  constructor
  · exact hQdense.mono hsubset
  constructor
  · exact Filter.mem_of_superset hQresidual hsubset
  · apply measure_mono_null
      (compl_subset_compl.mpr hsubset)
      hQnull

end

end GaloisForLFunctions.HTGeometry
