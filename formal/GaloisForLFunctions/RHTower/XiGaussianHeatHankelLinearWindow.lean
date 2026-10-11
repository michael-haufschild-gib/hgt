import GaloisForLFunctions.RHTower.XiShiftedParabolicDegreeHorizon
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminants

/-!
# The linear small-time window of the heat Hankel form

**Theorem** (`heatHankel_re_pos_of_window`).  Let `κ = routeUCompletedPrimeGammaAperture`, an
explicit positive constant.  For every heat time `a > 0` and every nonzero `P ∈ ℂ[X]` with
`a (deg P + 1) ≤ κ`,

`Re Σ_q e^{-a w_q} P(w_q) \overline{P(\overline{w_q})} > 0`.

Consequently the Hankel determinants satisfy `Δ_N(a) > 0` whenever `a N ≤ κ`
(`heatMomentDet_pos_of_mul_le`).  This holds unconditionally.

Proof.  Split `P = A + i B` with real-coefficient `A, B`.  Since `A` and `B` have real coefficients,
`P(w) \overline{P(\bar w)} = A(w)² + B(w)²`.  So the heat Hankel form is the sum of the two
polynomial-square Gaussian traces of `A` and `B`.  On the Route-U completed prime–Gamma wedge
`a (deg + 1) ≤ κ`, each such trace is at least a positive constant times its native
polynomial-Gaussian mass (`xiPolynomialGaussianHeatTraceReal_ge_parabolicWedgeMass`).  That mass is
positive for a nonzero polynomial.  The input is the explicit formula: Gamma positivity on the wedge
dominates the absolutely convergent prime tail.  No zero-location premise enters.

RH is the statement that the window is all of `a > 0` for every degree
(`riemannHypothesis_iff_heatHankel_nonneg`).  Without RH an off-line zero is detected at degree
`≪ a^{-1} log³(1/a)`, so the linear window is sharp up to logarithms.
-/

open Complex Polynomial Matrix
open GaloisForLFunctions.HTGeometry (leadingMatrix)

namespace RHTower

noncomputable section

/-! ## Real and imaginary parts of a complex polynomial -/

/-- The polynomial of real parts of the coefficients. -/
def realPartPoly (P : ℂ[X]) : ℝ[X] :=
  ∑ i ∈ Finset.range (P.natDegree + 1), C (P.coeff i).re * X ^ i

/-- The polynomial of imaginary parts of the coefficients. -/
def imagPartPoly (P : ℂ[X]) : ℝ[X] :=
  ∑ i ∈ Finset.range (P.natDegree + 1), C (P.coeff i).im * X ^ i

theorem coeff_realPartPoly (P : ℂ[X]) (k : ℕ) :
    (realPartPoly P).coeff k = (P.coeff k).re := by
  rw [realPartPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_re]

theorem coeff_imagPartPoly (P : ℂ[X]) (k : ℕ) :
    (imagPartPoly P).coeff k = (P.coeff k).im := by
  rw [imagPartPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_im]

theorem natDegree_realPartPoly_le (P : ℂ[X]) : (realPartPoly P).natDegree ≤ P.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_realPartPoly, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hN), zero_re]

theorem natDegree_imagPartPoly_le (P : ℂ[X]) : (imagPartPoly P).natDegree ≤ P.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_imagPartPoly, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hN), zero_im]

theorem eq_realPartPoly_add_imagPartPoly (P : ℂ[X]) :
    P = (realPartPoly P).map (algebraMap ℝ ℂ) + C I * (imagPartPoly P).map (algebraMap ℝ ℂ) := by
  ext k
  rw [coeff_add, coeff_C_mul, coeff_map, coeff_map, coeff_realPartPoly, coeff_imagPartPoly]
  simp only [Complex.coe_algebraMap]
  rw [mul_comm]
  exact (Complex.re_add_im (P.coeff k)).symm

theorem realPartPoly_ne_zero_or_imagPartPoly_ne_zero {P : ℂ[X]} (hP : P ≠ 0) :
    realPartPoly P ≠ 0 ∨ imagPartPoly P ≠ 0 := by
  by_contra h
  push Not at h
  apply hP
  rw [eq_realPartPoly_add_imagPartPoly P, h.1, h.2]
  simp

/-- Conjugation commutes with evaluation of a real-coefficient polynomial. -/
theorem conj_eval_map_algebraMap (A : ℝ[X]) (w : ℂ) :
    (starRingEnd ℂ) ((A.map (algebraMap ℝ ℂ)).eval ((starRingEnd ℂ) w)) =
      (A.map (algebraMap ℝ ℂ)).eval w := by
  rw [eval_map, eval_map, Polynomial.hom_eval₂, Complex.conj_conj]
  congr 1
  ext r
  simp

/-! ## The heat Hankel form as a sum of two polynomial-square traces -/

theorem heatHankelTermAt_eq_add (a : ℝ) (P : ℂ[X]) (q : XiZeroCopy) :
    heatHankelTermAt a P P (xiHeatFrequency q) =
      xiPolynomialGaussianHeatTerm (realPartPoly P) a q +
        xiPolynomialGaussianHeatTerm (imagPartPoly P) a q := by
  set A := (realPartPoly P).map (algebraMap ℝ ℂ) with hA
  set B := (imagPartPoly P).map (algebraMap ℝ ℂ) with hB
  set w := xiHeatFrequency q with hw
  have hP := eq_realPartPoly_add_imagPartPoly P
  have hcA := conj_eval_map_algebraMap (realPartPoly P) w
  have hcB := conj_eval_map_algebraMap (imagPartPoly P) w
  rw [← hA] at hcA
  rw [← hB] at hcB
  have hconj : (starRingEnd ℂ) (P.eval ((starRingEnd ℂ) w)) = A.eval w - I * B.eval w := by
    conv_lhs => rw [hP]
    rw [eval_add, eval_mul, eval_C, map_add, map_mul, Complex.conj_I, hcA, hcB]
    ring
  have hev : P.eval w = A.eval w + I * B.eval w := by
    conv_lhs => rw [hP]
    rw [eval_add, eval_mul, eval_C]
  rw [heatHankelTermAt, hconj, hev, xiPolynomialGaussianHeatTerm, xiPolynomialGaussianHeatTerm,
    xiGaussianHeatTerm, evalRealPolynomial, evalRealPolynomial, ← hA, ← hB, hw, xiHeatFrequency]
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination (-(Complex.exp (-(a : ℂ) * xiSpectralPoint q ^ (2 : ℕ)) *
    (B.eval (xiSpectralPoint q ^ (2 : ℕ))) ^ 2)) * hI

theorem heatHankel_eq_add_polynomialTrace {a : ℝ} (ha : 0 < a) (P : ℂ[X]) :
    heatHankel a P P =
      xiPolynomialGaussianHeatTrace (realPartPoly P) a +
        xiPolynomialGaussianHeatTrace (imagPartPoly P) a := by
  rw [heatHankel, xiPolynomialGaussianHeatTrace, xiPolynomialGaussianHeatTrace,
    ← (summable_xiPolynomialGaussianHeatTerm ha _).tsum_add
      (summable_xiPolynomialGaussianHeatTerm ha _)]
  exact tsum_congr fun q => heatHankelTermAt_eq_add a P q

/-! ## The window -/

theorem xiPolynomialGaussianHeatTraceReal_zero (a : ℝ) :
    xiPolynomialGaussianHeatTraceReal 0 a = 0 := by
  simp [xiPolynomialGaussianHeatTraceReal, xiPolynomialGaussianHeatTrace,
    xiPolynomialGaussianHeatTerm]

/-- A real polynomial in the Route-U wedge has a nonnegative trace, positive if it is nonzero. -/
theorem xiPolynomialGaussianHeatTraceReal_window {a : ℝ} (ha : 0 < a) (Q : ℝ[X])
    (hwin : a * (Q.natDegree + 1) ≤ routeUCompletedPrimeGammaAperture) :
    0 ≤ xiPolynomialGaussianHeatTraceReal Q a ∧
      (Q ≠ 0 → 0 < xiPolynomialGaussianHeatTraceReal Q a) := by
  by_cases hQ : Q = 0
  · subst hQ
    rw [xiPolynomialGaussianHeatTraceReal_zero]
    exact ⟨le_rfl, fun h => absurd rfl h⟩
  set t : routeUCompletedPrimeGammaWedge Q := ⟨a, ha, hwin⟩
  have h := xiPolynomialGaussianHeatTraceReal_ge_parabolicWedgeMass Q t
  have hm := routeUPolynomialGaussianMass_pos ⟨Q, hQ⟩ t.heat
  have hpos : 0 < routeUParabolicWedgeCoefficient * routeUPolynomialGaussianMass Q t.heat :=
    mul_pos routeUParabolicWedgeCoefficient_pos hm
  have hpos' := lt_of_lt_of_le hpos h
  exact ⟨hpos'.le, fun _ => hpos'⟩

/-- **The linear small-time window.**  For `a > 0` and nonzero `P` with
`a (deg P + 1) ≤ κ`, the heat Hankel form is positive. -/
theorem heatHankel_re_pos_of_window {a : ℝ} (ha : 0 < a) {P : ℂ[X]} (hP : P ≠ 0)
    (hwin : a * (P.natDegree + 1) ≤ routeUCompletedPrimeGammaAperture) :
    0 < (heatHankel a P P).re := by
  rw [heatHankel_eq_add_polynomialTrace ha, add_re]
  have hle : ∀ Q : ℝ[X], Q.natDegree ≤ P.natDegree →
      a * (Q.natDegree + 1) ≤ routeUCompletedPrimeGammaAperture := fun Q hQ => by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ ha.le) hwin
    have : (Q.natDegree : ℝ) ≤ P.natDegree := by exact_mod_cast hQ
    linarith
  have hA := xiPolynomialGaussianHeatTraceReal_window ha _
    (hle _ (natDegree_realPartPoly_le P))
  have hB := xiPolynomialGaussianHeatTraceReal_window ha _
    (hle _ (natDegree_imagPartPoly_le P))
  change 0 < xiPolynomialGaussianHeatTraceReal (realPartPoly P) a +
    xiPolynomialGaussianHeatTraceReal (imagPartPoly P) a
  rcases realPartPoly_ne_zero_or_imagPartPoly_ne_zero hP with h | h
  · linarith [hA.2 h, hB.1]
  · linarith [hA.1, hB.2 h]

/-- **Fixed-degree form.**  For every degree `d` the window `0 < a ≤ κ/(d+1)` makes the heat Hankel
form positive on all nonzero polynomials of degree `≤ d`. -/
theorem exists_heatHankel_pos_of_natDegree_le (d : ℕ) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ → ∀ P : ℂ[X], P ≠ 0 → P.natDegree ≤ d →
      0 < (heatHankel a P P).re := by
  refine ⟨routeUCompletedPrimeGammaAperture / (d + 1),
    div_pos routeUCompletedPrimeGammaAperture_pos (by positivity),
    fun a ha haa P hP hPd => heatHankel_re_pos_of_window ha hP ?_⟩
  rw [lt_div_iff₀ (by positivity)] at haa
  have : (P.natDegree : ℝ) ≤ d := by exact_mod_cast hPd
  nlinarith

/-- **Determinant bridge.**  If the heat Hankel form is positive on every nonzero polynomial of
degree `< N`, then `Δ_N(a) = det (M_{i+j}(a))_{i,j<N} > 0`. -/
theorem heatMomentDet_pos_of_forall {a : ℝ} (ha : 0 < a) {N : ℕ}
    (hpos : ∀ P : ℂ[X], P ≠ 0 → P.natDegree < N → 0 < (heatHankel a P P).re) :
    0 < (leadingMatrix (heatMomentArray a) N).det := by
  refine PosDef.det_pos (posDef_iff_dotProduct_mulVec.2 ⟨?_, fun u hu => ?_⟩)
  · ext i j
    simp [leadingMatrix, conjTranspose_apply, heatMomentArray_symm]
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      exact absurd (Subsingleton.elim u 0) hu
    · exact h
  set P : ℂ[X] := ∑ i : Fin N, C ((u i : ℝ) : ℂ) * X ^ (i : ℕ) with hP
  have hcoeff := coeff_sum_C_mul_X_pow u
  have hdeg : P.natDegree < N := by
    by_cases hP0 : P = 0
    · rw [hP0, natDegree_zero]; exact hN
    · rw [natDegree_lt_iff_degree_lt hP0, degree_lt_iff_coeff_zero]
      intro m hm
      rw [hP, hcoeff, dif_neg (by omega)]
  have hquad : star u ⬝ᵥ (leadingMatrix (heatMomentArray a) N *ᵥ u) = (heatHankel a P P).re := by
    rw [re_heatHankel_eq_quadratic ha P hdeg]
    simp only [hP, hcoeff, Fin.is_lt, dif_pos, Fin.eta, ofReal_re, ofReal_im, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero]
    simp only [dotProduct, mulVec, leadingMatrix, of_apply, star_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hquad]
  have hP0 : P ≠ 0 := by
    intro h0
    apply hu
    funext i
    have := congrArg (fun R : ℂ[X] => R.coeff i) h0
    simp only [coeff_zero] at this
    rw [hcoeff, dif_pos i.2] at this
    simp only [Fin.eta, ofReal_eq_zero] at this
    simpa using this
  exact hpos P hP0 hdeg

/-- **Determinant window.**  `Δ_N(a) = det (M_{i+j}(a))_{i,j<N} > 0` whenever `0 < a` and
`a N ≤ κ`. -/
theorem heatMomentDet_pos_of_mul_le {a : ℝ} (ha : 0 < a) {N : ℕ}
    (hwin : a * N ≤ routeUCompletedPrimeGammaAperture) :
    0 < (leadingMatrix (heatMomentArray a) N).det := by
  refine heatMomentDet_pos_of_forall ha fun P hP0 hdeg => ?_
  refine heatHankel_re_pos_of_window ha hP0 (le_trans ?_ hwin)
  refine mul_le_mul_of_nonneg_left ?_ ha.le
  have : (P.natDegree : ℝ) + 1 ≤ N := by exact_mod_cast hdeg
  exact this

end

end RHTower
