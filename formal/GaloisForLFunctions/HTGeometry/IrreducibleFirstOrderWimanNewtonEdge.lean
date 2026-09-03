import GaloisForLFunctions.HTGeometry.FirstOrderWimanSourceEdge
import GaloisForLFunctions.HTGeometry.IrreducibleFirstOrderRelation

open Finset Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ}

/-- Every transcendental entire order-one ADE has a fixed positive-slope Newton edge carried by an
irreducible polynomial relation on the actual analytic derivative component.  The shifted Wiman
row is exactly `X₀^d X₂ P`, so its nonzero edge root cannot belong to the added `X₂` factor. -/
theorem exists_irreducibleFirstOrderWimanNewtonEdge
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : GaloisForLFunctions.DifferentiallyAlgebraicOfOrder (coeffFun a) 1) :
    ∃ (P : MvPolynomial (Fin 3) ℂ)
        (S S₀ : Finset (ℕ × ℕ))
        (A A₀ : ℕ × ℕ → Polynomial ℂ) (d m : ℕ)
        (y : ℕ → ℝ) (z : ℕ → ℂ) (q : ℝ) (i₁ i₂ : ℕ × ℕ) (c : ℂ),
      P ≠ 0 ∧ Irreducible P ∧
      (∀ w : ℂ, MvPolynomial.eval
        (Fin.cons w fun j : Fin 2 => iteratedDeriv (j : ℕ) (coeffFun a) w) P = 0) ∧
      (∀ i ∈ S, i.1 + i.2 ≤ d) ∧
      (∀ w : ℂ,
        ∑ i ∈ S, (A i).eval w * (coeffFun a w) ^ i.1 *
          (deriv (coeffFun a) w) ^ i.2 = 0) ∧
      1 ≤ m ∧ m ≤ d ∧ (d - m, m) ∈ S ∧
      (∀ i ∈ S, i.1 + i.2 = d → i.2 ≤ m) ∧
      A (d - m, m) ≠ 0 ∧ d ≤ (A (d - m, m)).natDegree ∧
      0 < q ∧ Tendsto (fun n => Real.exp (y n)) atTop atTop ∧
      (∀ n, ‖z n‖ = Real.exp (y n)) ∧
      (∀ n, 0 < (centralIndex a (Real.exp (y n)) : ℝ)) ∧
      Tendsto (fun n => Real.log ((centralIndex a (Real.exp (y n)) : ℕ) : ℝ) / y n)
        atTop (nhds q) ∧
      Tendsto (fun n =>
        ‖∑ i ∈ S.filter (fun i => i.1 + i.2 = d),
          (A i).eval (z n) * (deriv (coeffFun a) (z n) / coeffFun a (z n)) ^ i.2‖)
        atTop (nhds 0) ∧
      Tendsto (fun n =>
        ‖z n * deriv (coeffFun a) (z n) / coeffFun a (z n) -
          (centralIndex a (Real.exp (y n)) : ℂ)‖ /
            (centralIndex a (Real.exp (y n)) : ℝ)) atTop (nhds 0) ∧
      firstOrderMvPoly S A =
        MvPolynomial.X 0 ^ d * MvPolynomial.X 2 * P ∧
      IsPositiveDerivativeCoefficientShift P S A d ∧
      firstOrderMvPoly S₀ A₀ = P ∧
      (∀ i ∈ S₀, A₀ i ≠ 0) ∧
      S = S₀.image firstOrderDerivativeShift ∧
      (∀ i ∈ S₀,
        A (firstOrderDerivativeShift i) = Polynomial.X ^ d * A₀ i) ∧
      (∀ i ∈ S₀, i.1 + i.2 ≤ d - 1) ∧
      firstOrderSourceNewtonFace S₀ S A d (q - 1)
          (firstOrderNewtonWeight A (q - 1) i₁) =
        firstOrderMaxNewtonFace S₀ A₀ (d - 1) (q - 1)
          (firstOrderNewtonWeight A (q - 1) i₁ - d - (q - 1)) ∧
      i₁ ∈ firstOrderMaxNewtonFace S A d (q - 1)
        (firstOrderNewtonWeight A (q - 1) i₁) ∧
      i₂ ∈ firstOrderMaxNewtonFace S A d (q - 1)
        (firstOrderNewtonWeight A (q - 1) i₁) ∧ i₁ ≠ i₂ ∧
      firstOrderNewtonWeight A (q - 1) i₁ = firstOrderNewtonWeight A (q - 1) i₂ ∧
      (∃ pRat : ℚ, (pRat : ℝ) = q - 1 ∧ 0 < (pRat : ℝ) + 1) ∧
      (∀ i ∈ firstOrderTopNewtonFace S A d,
        firstOrderNewtonWeight A (q - 1) i ≤ firstOrderNewtonWeight A (q - 1) i₁) ∧
      c ≠ 0 ∧ (firstOrderNewtonEdgePolynomial
        (firstOrderMaxNewtonFace S A d (q - 1)
          (firstOrderNewtonWeight A (q - 1) i₁)) A).IsRoot c ∧
      (firstOrderNewtonEdgePolynomial
        (firstOrderMaxNewtonFace S₀ A₀ (d - 1) (q - 1)
          (firstOrderNewtonWeight A (q - 1) i₁ - d - (q - 1))) A₀).IsRoot c := by
  obtain ⟨P, hP, hPirred, hPrel⟩ :=
    exists_irreducible_firstOrderRelation (differentiable_coeffFun ha) hDA
  obtain ⟨S, A, d, m, y, z, q, i₁, i₂, c, hdeg, hrel, hmpos, hmle, htarget,
    htopdeg, hAne, hAdeg, hqpos, hρ, hz, hνpos, hslope, htoplim, hdefectlim,
    hpoly, hshift, hi₁, hi₂, hi₁₂, hweight, hmax, hcne, hcroot⟩ :=
      exists_firstOrderWimanNewtonEdge_of_relation ha hn₀ htrans P hP hPrel
  obtain ⟨S₀, A₀, hsourcePoly, hsourceA, hsourceS, hsourceCoeff, hsourceDeg,
    hsourceFace, hsourceRoot⟩ :=
    exists_sourceNewtonEdgeRoot_of_positiveDerivativeShift hshift hdeg ⟨i₁, hi₁⟩ hcne hcroot
  have hi₁deg : i₁.1 + i₁.2 = d := by
    have h := hi₁
    rw [firstOrderMaxNewtonFace, Finset.mem_filter,
      firstOrderTopNewtonFace, Finset.mem_filter] at h
    exact h.1.2.1
  have hi₂deg : i₂.1 + i₂.2 = d := by
    have h := hi₂
    rw [firstOrderMaxNewtonFace, Finset.mem_filter,
      firstOrderTopNewtonFace, Finset.mem_filter] at h
    exact h.1.2.1
  have hi₁₂snd : i₁.2 ≠ i₂.2 :=
    snd_ne_of_ne_of_add_eq_add_eq hi₁deg hi₂deg hi₁₂
  obtain ⟨pRat, hpRat⟩ :=
    exists_rational_eq_slope_of_eq_firstOrderNewtonWeight hi₁₂snd hweight
  have hpRatPos : 0 < (pRat : ℝ) + 1 := by
    rw [hpRat]
    linarith
  exact ⟨P, S, S₀, A, A₀, d, m, y, z, q, i₁, i₂, c, hP, hPirred, hPrel, hdeg, hrel,
    hmpos, hmle, htarget, htopdeg, hAne, hAdeg, hqpos, hρ, hz, hνpos, hslope,
    htoplim, hdefectlim, hpoly, hshift, hsourcePoly, hsourceA, hsourceS,
    hsourceCoeff, hsourceDeg, hsourceFace, hi₁, hi₂, hi₁₂, hweight,
    ⟨pRat, hpRat, hpRatPos⟩, hmax, hcne, hcroot, hsourceRoot⟩

end

end GaloisForLFunctions.HTGeometry
