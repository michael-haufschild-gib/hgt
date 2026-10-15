import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLinearWindow
import GaloisForLFunctions.HTGeometry.FiniteMomentNullPolynomialRoots
import GaloisForLFunctions.HTGeometry.LogCurvatureEndpointRigidity

/-!
# Strict endpoint rigidity of the heat Hankel head

Suppose the size-`n+1` actual heat section is positive definite before a finite
positive time `T`. Its size-`n` head remains strictly positive at `T`.

For a nonzero polynomial `P` of degree below `n`, the heat derivative chain gives
`f' = -H(P, XP)` and `f'' = H(XP, XP)` for `f = H(P, P)`. Both polynomials are
visible in the positive section. Cauchy--Schwarz gives `(f')² ≤ f f''`, and
logarithmic-curvature rigidity prevents `f` from vanishing at the endpoint.
The argument needs neither a simple determinant zero nor a generic heat time.
-/

open Polynomial Matrix Set Filter Topology
open HTGeometry
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

def heatRealMoments (a : ℝ) (k : ℕ) : ℝ := (xiHeatMoment k a).re

theorem heatMomentMatrix_eq (a : ℝ) (n : ℕ) :
    momentHankelMatrix (heatRealMoments a) n = leadingMatrix (heatMomentArray a) n := rfl

theorem hasDerivAt_heatRealMoments (k : ℕ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun t => heatRealMoments t k) (-heatRealMoments a (k + 1)) a := by
  simpa only [heatRealMoments, Complex.neg_re] using
    (hasDerivAt_xiHeatMoment k (τ₀ := (a : ℂ)) (by simpa using ha)).real_of_complex

theorem momentFunctional_X_mul_shift (s : ℕ → ℝ) (P : ℝ[X]) :
    momentFunctional s (X * P) = momentFunctional (fun k => s (k + 1)) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [mul_add, momentFunctional_add, hP, hQ]
  | monomial n c => simp [X_mul_monomial]

theorem hasDerivAt_heatMomentFunctional (P : ℝ[X]) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun t => momentFunctional (heatRealMoments t) P)
      (-momentFunctional (heatRealMoments a) (X * P)) a := by
  rw [momentFunctional_X_mul_shift]
  simp only [momentFunctional_eq_support_sum]
  have hsum : (fun t => ∑ k ∈ P.support, P.coeff k * heatRealMoments t k) =
      ∑ k ∈ P.support, (fun t => P.coeff k * heatRealMoments t k) := by
    funext t
    simp only [Finset.sum_apply]
  rw [hsum]
  simpa only [mul_neg, Finset.sum_neg_distrib] using
    (HasDerivAt.sum (u := P.support)
      (fun k _ => (hasDerivAt_heatRealMoments k ha).const_mul (P.coeff k)))

theorem hasDerivAt_heatMomentInner (P Q : ℝ[X]) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun t => momentInner (heatRealMoments t) P Q)
      (-momentInner (heatRealMoments a) P (X * Q)) a := by
  simpa only [momentInner_def, mul_left_comm X P Q] using
    hasDerivAt_heatMomentFunctional (P * Q) ha

theorem momentInner_sq_le_of_finite_posDef {s : ℕ → ℝ} {n : ℕ}
    (hs : (momentHankelMatrix s n).PosDef) {P Q : ℝ[X]}
    (hP : P ≠ 0) (hdP : P.natDegree < n) (hdQ : Q.natDegree < n) :
    (momentInner s P Q) ^ 2 ≤ momentInner s P P * momentInner s Q Q := by
  let A := momentInner s P P
  let B := momentInner s P Q
  let C := momentInner s Q Q
  have hA : 0 < A := momentInner_self_pos_of_natDegree_lt hs hP hdP
  let V := (-B) • P + A • Q
  have hVdeg : V.natDegree < n :=
    (natDegree_add_le _ _).trans_lt (max_lt
      ((natDegree_smul_le _ _).trans_lt hdP) ((natDegree_smul_le _ _).trans_lt hdQ))
  have hV : 0 ≤ momentInner s V V := by
    by_cases hz : V = 0
    · simp [hz]
    · exact (momentInner_self_pos_of_natDegree_lt hs hz hVdeg).le
  have heq : momentInner s V V = A * (A * C - B ^ 2) := by
    dsimp [V]
    simp only [momentInner_add_left, momentInner_add_right,
      momentInner_smul_left, momentInner_smul_right, momentInner_comm s Q P]
    change (-B) * ((-B) * A + A * B) + A * ((-B) * B + A * C) = _
    ring
  rw [heq] at hV
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hA).mp hV)

/-- Positivity along the heat flow forces strict positivity of the preceding
head at its finite endpoint. No simplicity or nondegeneracy is assumed there. -/
theorem heatMoment_head_posDef_at_endpoint {n : ℕ} {T : ℝ} (hT : 0 < T)
    (hpos : ∀ t ∈ Ioo 0 T, (momentHankelMatrix (heatRealMoments t) (n + 1)).PosDef) :
    (momentHankelMatrix (heatRealMoments T) n).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨momentHankelMatrix_isHermitian _ _, fun x hx => ?_⟩
  let P : ℝ[X] := Polynomial.ofFn n x
  have hP : P ≠ 0 := by
    intro hz
    apply hx
    have hh := congrArg (Polynomial.toFn n) hz
    simpa only [P, Polynomial.toFn_comp_ofFn_eq_id, map_zero] using hh
  have hdP : P.natDegree < n :=
    (natDegree_lt_iff_degree_lt hP).mpr (Polynomial.ofFn_degree_lt x)
  have hdP' : P.natDegree < n + 1 := by omega
  have hdXP : (X * P).natDegree < n + 1 := by
    have hb := Polynomial.natDegree_mul_le (p := (X : ℝ[X])) (q := P)
    rw [Polynomial.natDegree_X] at hb
    omega
  have hsecond (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun y => -momentInner (heatRealMoments y) P (X * P))
        (momentInner (heatRealMoments t) (X * P) (X * P)) t := by
    convert (hasDerivAt_heatMomentInner P (X * P) ht).neg using 1 <;>
      first | rfl | simp only [neg_neg, momentInner_X_mul]
  have hresult : 0 < momentInner (heatRealMoments T) P P := by
    apply pos_right_endpoint_of_logarithmic_curvature (l := T / 2) (b := T)
      (f := fun t => momentInner (heatRealMoments t) P P)
      (f₁ := fun t => -momentInner (heatRealMoments t) P (X * P))
      (f₂ := fun t => momentInner (heatRealMoments t) (X * P) (X * P))
      (by linarith)
    · intro t ht
      exact (hasDerivAt_heatMomentInner P P (by linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht
      exact hasDerivAt_heatMomentInner P P (by linarith [ht.1])
    · intro t ht
      exact hsecond t (by linarith [ht.1])
    · intro t ht
      exact momentInner_self_pos_of_natDegree_lt
        (hpos t ⟨by linarith [ht.1], ht.2⟩) hP hdP'
    · intro t ht
      simpa only [neg_sq] using momentInner_sq_le_of_finite_posDef
        (hpos t ⟨by linarith [ht.1], ht.2⟩) hP hdP' hdXP
  simpa only [P, momentInner_ofFn_ofFn, star_trivial] using hresult

end RHTower
