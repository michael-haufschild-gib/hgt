import GaloisForLFunctions.HTGeometry.StrelitzEntireHeatSubquadraticDichotomy

/-!
# Algebraic descent of the zero Strelitz branch

If exact zero roots recur along the escaping first-jet sequence, the constant coefficient of the
fixed polynomial in the second-jet variable vanishes identically.  Thus the zero branch is not
merely an asymptotic alternative: it exposes an exact global factor in the fixed jet curve.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- A zero of a specialized Strelitz curve is exactly a zero of its constant coefficient. -/
theorem eval_coeff_zero_strelitzJetCurvePolynomial_eq_zero_of_isRoot_zero
    (S : MvPolynomial (Fin 2) ℂ) (u : ℂ)
    (hroot : (strelitzJetCurveSpecialization S u).IsRoot 0) :
    MvPolynomial.eval ![u] ((strelitzJetCurvePolynomial S).coeff 0) = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa [Polynomial.IsRoot, strelitzJetCurveSpecialization] using hroot

/-- Recurrent exact-zero roots over an escaping first jet force the constant-in-`v` coefficient of
the fixed Strelitz curve to vanish identically. -/
theorem coeff_zero_strelitzJetCurvePolynomial_eq_zero_of_zeroBranch
    (S : MvPolynomial (Fin 2) ℂ) {u root : ℕ → ℂ} {ns : ℕ → ℕ}
    (huTop : Tendsto (fun n => ‖u n‖) atTop atTop) (hns : StrictMono ns)
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hzero : ∀ k, root (ns k) = 0) :
    (strelitzJetCurvePolynomial S).coeff 0 = 0 := by
  let Q : Polynomial ℂ := finOnePolynomial ((strelitzJetCurvePolynomial S).coeff 0)
  have huSub : Tendsto (fun k => ‖u (ns k)‖) atTop atTop :=
    huTop.comp hns.tendsto_atTop
  have hQzero : ∀ᶠ k : ℕ in atTop, Q.eval (u (ns k)) = 0 := by
    have hrootSub := hns.tendsto_atTop.eventually hroot
    filter_upwards [hrootSub] with k hk
    have hk0 : (strelitzJetCurveSpecialization S (u (ns k))).IsRoot 0 := by
      simpa [hzero k] using hk
    change (finOnePolynomial ((strelitzJetCurvePolynomial S).coeff 0)).eval
      (u (ns k)) = 0
    rw [eval_finOnePolynomial]
    exact eval_coeff_zero_strelitzJetCurvePolynomial_eq_zero_of_isRoot_zero S _ hk0
  by_contra hcoeff
  have hQ : Q ≠ 0 := by
    dsimp [Q]
    exact finOnePolynomial_ne_zero hcoeff
  have hasymp := GaloisForLFunctions.tendsto_eval_div_pow_natDegree_of_norm_atTop
    huSub Q
  have hzeroLim : Tendsto (fun k => Q.eval (u (ns k)) / (u (ns k)) ^ Q.natDegree)
      atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hQzero] with k hk
    simp [hk]
  have hlc : Q.leadingCoeff = 0 := tendsto_nhds_unique hasymp hzeroLim
  exact (Polynomial.leadingCoeff_ne_zero.mpr hQ) hlc

/-- Equivalently, the recurrent zero branch exposes an exact factor of the second-jet variable in
the fixed Strelitz curve polynomial. -/
theorem X_dvd_strelitzJetCurvePolynomial_of_zeroBranch
    (S : MvPolynomial (Fin 2) ℂ) {u root : ℕ → ℂ} {ns : ℕ → ℕ}
    (huTop : Tendsto (fun n => ‖u n‖) atTop atTop) (hns : StrictMono ns)
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hzero : ∀ k, root (ns k) = 0) :
    Polynomial.X ∣ strelitzJetCurvePolynomial S :=
  Polynomial.X_dvd_iff.mpr
    (coeff_zero_strelitzJetCurvePolynomial_eq_zero_of_zeroBranch
      S huTop hns hroot hzero)

/-- The sharpened Strelitz dichotomy with exact algebraic content in both branches: either a
matched nonzero subquadratic Newton edge exists, or the second-jet variable divides the fixed curve
and the observed second jet vanishes on a cofinal exact-zero branch. -/
theorem strelitzJetCurve_subquadraticEdge_or_zeroFactorBranch
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {ν : ℕ → ℕ} {u v root : ℕ → ℂ} (hνTop : Tendsto ν atTop atTop)
    (hu : ∀ n : ℕ, ‖u n - (ν n : ℂ)‖ ≤
      (1 / ((n : ℝ) + 1)) * (ν n : ℝ))
    (hv : ∀ n : ℕ, ‖v n‖ ≤ (1 / ((n : ℝ) + 1)) * (ν n : ℝ) ^ (2 : ℕ))
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hclose : Tendsto (fun n => ‖v n - root n‖) atTop (nhds 0)) :
    HasStrelitzJetCurveSubquadraticMatchedNewtonEdgeLimit S u root ∨
      (Polynomial.X ∣ strelitzJetCurvePolynomial S) ∧
        ∃ ns : ℕ → ℕ, StrictMono ns ∧
          (∀ k, root (ns k) = 0) ∧
          Tendsto (fun k => ‖v (ns k)‖) atTop (nhds 0) := by
  rcases strelitzJetCurve_subquadraticMatchedNewtonEdge_or_zeroBranch
      hS hνTop hu hv hroot hclose with hmatched | ⟨ns, hns, hzero, hvzero⟩
  · exact Or.inl hmatched
  · right
    have huTop : Tendsto (fun n => ‖u n‖) atTop atTop :=
      tendsto_norm_atTop_of_nat_tendsto_atTop_of_strelitzRelativeError hνTop hu
    exact ⟨X_dvd_strelitzJetCurvePolynomial_of_zeroBranch
      S huTop hns hroot hzero, ns, hns, hzero, hvzero⟩

end

end GaloisForLFunctions.HTGeometry
