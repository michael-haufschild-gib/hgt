import GaloisForLFunctions.RHTower.XiJensenHermiteIdentity
import GaloisForLFunctions.HTGeometry.FinitePolynomialInterpolationLimits

/-!
# Fixed-degree Jensen–Hermite asymptotics for the actual Xi coefficients

For every fixed degree, the affine-normalized Jensen polynomial of
`xiJensenCoeff` converges coefficientwise to the probabilists' Hermite
polynomial. The theta concentration estimates and the coefficient identity
are proved in the imported leaves; no asymptotic estimate is a hypothesis.

Precisely, `γ(n)⁻¹ δ(n)⁻ᵈ J^{d,n}((δ(n) X - 1)/A(n)) → He_d`, where
`δ(n) = 1/sqrt(n+1/2)`, `A(n) = s(n)²/(4(n+1/2))`, and the positive saddle
satisfies `π s(n) exp(2s(n)) - 9s(n)/4 = n+1/2`.
-/

open Polynomial Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.SignAlternation

noncomputable section

namespace RHTower

theorem tendsto_xiJensenHermitePolynomial_eval (d : ℕ) (x : ℝ) :
    Tendsto (fun n => (xiJensenHermitePolynomial n d).eval x) atTop
      (𝓝 ((hermiteReal d).eval x)) := by
  simpa only [eval_xiJensenHermitePolynomial] using tendsto_xiThetaHermiteExpectation d x

theorem natDegree_xiJensenHermitePolynomial_le (n d : ℕ) :
    (xiJensenHermitePolynomial n d).natDegree ≤ d := by
  have hlinear : (C ((xiJensenScale n)⁻¹) * (C (xiJensenDelta n) * X - 1)).natDegree ≤ 1 := by
    refine (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (max_le ?_ ?_))
    · simpa only [natDegree_X] using natDegree_C_mul_le (xiJensenDelta n) (X : ℝ[X])
    · simp
  unfold xiJensenHermitePolynomial
  refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
  exact (Nat.mul_le_mul (natDegree_jensenPoly_le xiJensenCoeff d n) hlinear).trans_eq (Nat.mul_one d)

private theorem tendsto_coeff_of_bounded_degree {p : ℕ → ℝ[X]} {q : ℝ[X]} {d : ℕ}
    (hp : ∀ n, (p n).natDegree ≤ d) (hq : q.natDegree ≤ d)
    (heval : ∀ x : ℝ, Tendsto (fun n => (p n).eval x) atTop (𝓝 (q.eval x))) (j : ℕ) :
    Tendsto (fun n => (p n).coeff j) atTop (𝓝 (q.coeff j)) := by
  let nodes : Fin (d + 1) → ℝ := fun i => (i.val : ℝ)
  have hinj : Set.InjOn nodes (Finset.univ : Finset (Fin (d + 1))) := by
    intro a ha b hb hab
    apply Fin.ext
    exact_mod_cast hab
  have hrepr (f : ℝ[X]) (hf : f.natDegree ≤ d) :
      Lagrange.interpolate Finset.univ nodes (fun i => f.eval (nodes i)) = f := by
    apply (Lagrange.eq_interpolate hinj ?_).symm
    have hdeg : f.degree < ((d + 1 : ℕ) : WithBot ℕ) :=
      lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hf)
    simpa only [Finset.card_univ, Fintype.card_fin] using hdeg
  have hn (n : ℕ) :
      Lagrange.interpolate Finset.univ nodes (fun i => (p n).eval (nodes i)) = p n := hrepr _ (hp n)
  have hqrepr := hrepr q hq
  have h := tendsto_lagrange_interpolate_coeff nodes (fun n i => (p n).eval (nodes i))
    (fun i => q.eval (nodes i)) (fun i => heval (nodes i)) j
  simpa only [hn, hqrepr] using h

/-- The unconditional fixed-degree, increasing-shift Xi Jensen–Hermite limit. -/
theorem tendsto_xiJensenHermitePolynomial_coeff (d j : ℕ) :
    Tendsto (fun n => (xiJensenHermitePolynomial n d).coeff j) atTop
      (𝓝 ((hermiteReal d).coeff j)) := by
  apply tendsto_coeff_of_bounded_degree (fun n => natDegree_xiJensenHermitePolynomial_le n d)
    (le_of_eq (natDegree_hermiteReal d))
  exact tendsto_xiJensenHermitePolynomial_eval d

end RHTower
