import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheLorentzianClassIsClosedUnderNonnegativeSubstitution

/-!
# The Jensen polynomials of `ξ` satisfy Laguerre's inequality on the half-line

A real-rooted polynomial `J` of degree `d` satisfies Laguerre's inequality
`d J J'' ≤ (d − 1) J'²` on the whole real line. For the Jensen polynomials of `ξ` real-rootedness
is the Riemann hypothesis (Pólya); their roots, if real, are negative. The Lorentzian layer proves
the inequality unconditionally where the roots are not: on the half-line `s ≥ 0`.

* **Homogenization** (`bivPoly`, `coeff_bivPoly`): `Σ_k a_k x^k y^{d−k}` as a polynomial whose
  coefficients are `bivariateCoeff d a`; its value and `x`-derivatives at `(s, 1)` are those of the
  dehomogenization `J(s) = Σ_k a_k s^k` (`eval_bivPoly`, `eval_pderiv_bivPoly`,
  `eval_pderiv_pderiv_bivPoly`).
* **Lorentzian forms satisfy Laguerre on the half-line** (`laguerre_halfLine_of_isLorentzianPoly`):
  strong log-concavity of the mixed-Lorentzian homogenization at the nonnegative point `(s, 1)`
  along `(1, 0)` (`IsMixedLorentzian.logConcave`) is `d J(s) J''(s) ≤ (d − 1) J'(s)²`; for `J > 0`
  this says that `J^{1/d}` is concave on `[0, ∞)`.
* **The Jensen polynomials of `ξ`** (`xi_jensen_laguerre_halfLine`): every Jensen polynomial
  `Σ_k C(d, k) γ_{n+k} s^k` of the Taylor coefficients of `ξ(½ + x)` satisfies Laguerre's
  inequality for `s ≥ 0`. At `d = 2` this is the Turán inequality itself, independent of `s`;
  the Riemann hypothesis is the same family of inequalities on the negative half-line.
-/

noncomputable section

open MvPolynomial Finset

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

/-- The homogenization `Σ_{k ≤ d} a_k x^k y^{d−k}`. -/
def bivPoly (d : ℕ) (a : ℕ → ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∑ k ∈ range (d + 1), monomial (bimon d k) (a k)

theorem coeff_bivPoly (d : ℕ) (a : ℕ → ℝ) (β : Fin 2 →₀ ℕ) :
    coeff β (bivPoly d a) = bivariateCoeff d a β := by
  rw [bivPoly, coeff_sum]
  simp only [coeff_monomial]
  unfold bivariateCoeff
  split_ifs with h
  · rw [Finset.sum_eq_single (β 0)]
    · rw [if_pos (eq_bimon h).symm]
    · intro k _ hne
      rw [if_neg]
      intro hb
      apply hne
      rw [← hb, bimon_apply_zero]
    · intro hnot
      exfalso
      exact hnot (mem_range.mpr (by omega))
  · refine sum_eq_zero fun k hk => if_neg fun hb => h ?_
    rw [← hb, bimon_apply_zero, bimon_apply_one]
    have := mem_range.mp hk
    omega

theorem eval_monomial_fin_two (s : ℝ) (γ : Fin 2 →₀ ℕ) (c : ℝ) :
    eval ![s, 1] (monomial γ c) = c * s ^ (γ 0) := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ fun i => pow_zero _, Fin.prod_univ_two]
  simp

theorem eval_bivPoly (d : ℕ) (a : ℕ → ℝ) (s : ℝ) :
    eval ![s, 1] (bivPoly d a) = ∑ k ∈ range (d + 1), a k * s ^ k := by
  simp only [bivPoly, map_sum, eval_monomial_fin_two, bimon_apply_zero]

theorem eval_pderiv_bivPoly (d : ℕ) (a : ℕ → ℝ) (s : ℝ) :
    eval ![s, 1] (pderiv 0 (bivPoly d a)) = ∑ k ∈ range (d + 1), a k * k * s ^ (k - 1) := by
  simp only [bivPoly, map_sum, pderiv_monomial, eval_monomial_fin_two, Finsupp.tsub_apply,
    bimon_apply_zero, Finsupp.single_eq_same]

theorem eval_pderiv_pderiv_bivPoly (d : ℕ) (a : ℕ → ℝ) (s : ℝ) :
    eval ![s, 1] (pderiv 0 (pderiv 0 (bivPoly d a))) =
      ∑ k ∈ range (d + 1), a k * k * ((k - 1 : ℕ) : ℝ) * s ^ (k - 2) := by
  simp only [bivPoly, map_sum, pderiv_monomial, eval_monomial_fin_two, Finsupp.tsub_apply,
    bimon_apply_zero, Finsupp.single_eq_same, Nat.sub_sub]

theorem dirDeriv_fin_two_e0 (q : MvPolynomial (Fin 2) ℝ) : dirDeriv ![1, 0] q = pderiv 0 q := by
  simp [dirDeriv, Fin.sum_univ_two]

/-- **A Lorentzian bivariate form satisfies Laguerre's inequality on the half-line**: for
`J(s) = Σ_k a_k s^k` of degree `d = m + 2`, `d J(s) J''(s) ≤ (d − 1) J'(s)²` for all `s ≥ 0`. -/
theorem laguerre_halfLine_of_isLorentzianPoly {m : ℕ} {a : ℕ → ℝ}
    (hL : IsLorentzianPoly (m + 2) (bivariateCoeff (m + 2) a)) {s : ℝ} (hs : 0 ≤ s) :
    ((m : ℝ) + 2) * (∑ k ∈ range (m + 3), a k * s ^ k) *
        (∑ k ∈ range (m + 3), a k * k * ((k - 1 : ℕ) : ℝ) * s ^ (k - 2)) ≤
      ((m : ℝ) + 1) * (∑ k ∈ range (m + 3), a k * k * s ^ (k - 1)) ^ 2 := by
  have hc : (fun β => coeff β (bivPoly (m + 2) a)) = bivariateCoeff (m + 2) a :=
    funext (coeff_bivPoly _ _)
  have hP : IsLorentzianPolynomial (m + 2) (bivPoly (m + 2) a) := by
    unfold IsLorentzianPolynomial; rw [hc]; exact hL
  have h := hP.isMixedLorentzian.logConcave (x := ![s, 1])
    (fun i => by fin_cases i <;> simp [hs]) ![1, 0]
  rwa [dirDeriv_fin_two_e0, dirDeriv_fin_two_e0, eval_bivPoly, eval_pderiv_bivPoly,
    eval_pderiv_pderiv_bivPoly] at h

/-- **Every Jensen polynomial of `ξ` satisfies Laguerre's inequality on the half-line**: with
`γ_k` the Taylor coefficients of `ξ(½ + x) = Σ γ_k x^{2k}` and
`J(s) = Σ_{k ≤ d} C(d, k) γ_{n+k} s^k`, `d = m + 2`, one has `d J J'' ≤ (d − 1) J'²` on `[0, ∞)`. -/
theorem xi_jensen_laguerre_halfLine (m n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    let a := jensenCoeff (m + 2) n (RHTower.evenTaylorRe fun x => RHTower.xi (1 / 2 + x))
    ((m : ℝ) + 2) * (∑ k ∈ range (m + 3), a k * s ^ k) *
        (∑ k ∈ range (m + 3), a k * k * ((k - 1 : ℕ) : ℝ) * s ^ (k - 2)) ≤
      ((m : ℝ) + 1) * (∑ k ∈ range (m + 3), a k * k * s ^ (k - 1)) ^ 2 :=
  laguerre_halfLine_of_isLorentzianPoly (xi_jensen_isLorentzianPoly (m + 2) n) hs

end GaloisForLFunctions.ArithmeticLorentzianGeometry
