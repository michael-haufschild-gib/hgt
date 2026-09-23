import GaloisForLFunctions.RHTower.CompletedFluxPrimeArchDecomposition
import GaloisForLFunctions.RHTower.XiLaguerrePolya

/-!
# The second completed-flux coefficient is the strict Laguerre reader

At a nonzero point `ρ`, the removable completed-flux germ is
`x ↦ x · (-ξ'/ξ)(ρ+x)`.  Its second Taylor coefficient is therefore the derivative of
`-ξ'/ξ` at `ρ`.  On the critical line the rotation `s = 1/2 + it` reverses the sign of the
second logarithmic derivative, giving the exact division-free identity

`(Xi')² - Xi·Xi'' = -Xi² · completedFluxTaylorCoeff (linePt t) 2`.

Consequently, positivity of the real part of this single source coefficient is equivalent to the
strict Laguerre failure already known to refute RH.  The fixed prime--archimedean decomposition then
turns the reader into an exact competition between the continued Euler-prime coefficient and the
archimedean/boundary coefficient.  No cutoff or carrier limit is introduced.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Away from a zero of `xi`, the quadratic coefficient of the removable completed-flux germ is
the derivative of the completed seam flux itself. -/
theorem completedFluxTaylorCoeff_two_of_ne_zero {ρ : ℂ} (hρ : xi ρ ≠ 0) :
    completedFluxTaylorCoeff ρ 2 = deriv seamFluxCochain ρ := by
  have hord : (analyticOrderAt xi ρ).toNat = 0 := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hρ)]
    simp
  have hfun : completedFluxGermAt ρ = fun x => x * seamFluxCochain (ρ + x) := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [completedFluxGermAt, hord]
    · simp [completedFluxGermAt, hx]
  have hxi : AnalyticAt ℂ xi ρ := xi_analyticOnNhd_univ ρ (Set.mem_univ ρ)
  have hlog : AnalyticAt ℂ (logDeriv xi) ρ := by
    rw [show logDeriv xi = fun z => deriv xi z / xi z by rfl]
    exact hxi.deriv.div hxi hρ
  have hseam : AnalyticAt ℂ seamFluxCochain ρ := by
    change AnalyticAt ℂ (fun z => -logDeriv xi z) ρ
    exact hlog.neg
  have hshift : AnalyticAt ℂ (fun x : ℂ => seamFluxCochain (ρ + x)) 0 := by
    have hadd : AnalyticAt ℂ (fun x : ℂ => ρ + x) 0 := by fun_prop
    have hcomp := AnalyticAt.comp_of_eq hseam hadd (by simp)
    simpa [Function.comp_def] using hcomp
  have hshiftDeriv : deriv (fun x : ℂ => seamFluxCochain (ρ + x)) 0 =
      deriv seamFluxCochain ρ := by
    have hadd : HasDerivAt (fun x : ℂ => ρ + x) 1 0 := by
      convert! (hasDerivAt_const (x := (0 : ℂ)) (c := ρ)).add
        (hasDerivAt_id (𝕜 := ℂ) (x := 0)) using 1
      all_goals ring
    have houter : HasDerivAt seamFluxCochain (deriv seamFluxCochain ρ) (ρ + 0) := by
      simpa using hseam.differentiableAt.hasDerivAt
    simpa using! (houter.comp 0 hadd).deriv
  have hmul := iteratedDeriv_mul (n := 2) (x := (0 : ℂ))
    (analyticAt_id.contDiffAt (n := 2)) (hshift.contDiffAt (n := 2))
  have htwo : iteratedDeriv 2 (fun x : ℂ => x * seamFluxCochain (ρ + x)) 0 =
      2 * deriv seamFluxCochain ρ := by
    change iteratedDeriv 2 (fun x : ℂ => x * seamFluxCochain (ρ + x)) 0 = _ at hmul
    rw [hmul]
    norm_num [Finset.sum_range_succ, iteratedDeriv_one, iteratedDeriv_id, hshiftDeriv]
  rw [completedFluxTaylorCoeff, hfun, htwo]
  norm_num

private theorem XiC_deriv_eq_xi_deriv_mul_I (z : ℂ) :
    deriv XiC z = deriv xi (1 / 2 + z * I) * I := by
  have haff : HasDerivAt (fun w : ℂ => 1 / 2 + w * I) I z := by
    convert! (hasDerivAt_const (x := z) (c := (1 / 2 : ℂ))).add
      ((hasDerivAt_id (𝕜 := ℂ) (x := z)).mul_const I) using 1
    all_goals ring
  exact (xi_differentiable.differentiableAt.hasDerivAt.comp z haff).deriv

private theorem XiC_secondDeriv_eq_neg_xi_secondDeriv (z : ℂ) :
    deriv (deriv XiC) z = -deriv (deriv xi) (1 / 2 + z * I) := by
  have hfun : deriv XiC = fun w => deriv xi (1 / 2 + w * I) * I := by
    funext w
    exact XiC_deriv_eq_xi_deriv_mul_I w
  rw [hfun]
  have haff : HasDerivAt (fun w : ℂ => 1 / 2 + w * I) I z := by
    convert! (hasDerivAt_const (x := z) (c := (1 / 2 : ℂ))).add
      ((hasDerivAt_id (𝕜 := ℂ) (x := z)).mul_const I) using 1
    all_goals ring
  have hxi2 : HasDerivAt (deriv xi) (deriv (deriv xi) (1 / 2 + z * I))
      (1 / 2 + z * I) :=
    (xi_analyticOnNhd_univ (1 / 2 + z * I) (Set.mem_univ _)).deriv.differentiableAt.hasDerivAt
  have hcomp := (hxi2.comp z haff).mul_const I
  convert! hcomp.deriv using 1
  rw [mul_assoc, I_mul_I]
  ring

private theorem seamFluxCochain_deriv_eq_xi_laguerre_div {ρ : ℂ} (hρ : xi ρ ≠ 0) :
    deriv seamFluxCochain ρ =
      ((deriv xi ρ) ^ (2 : ℕ) - xi ρ * deriv (deriv xi) ρ) / (xi ρ) ^ (2 : ℕ) := by
  have hxi : HasDerivAt xi (deriv xi ρ) ρ := xi_differentiable.differentiableAt.hasDerivAt
  have hxi2 : HasDerivAt (deriv xi) (deriv (deriv xi) ρ) ρ :=
    (xi_analyticOnNhd_univ ρ (Set.mem_univ ρ)).deriv.differentiableAt.hasDerivAt
  change deriv (fun z => -logDeriv xi z) ρ = _
  have hquot := hxi2.div hxi hρ
  rw [show logDeriv xi = fun z => deriv xi z / xi z by rfl]
  have hder : deriv (fun z => -(deriv xi z / xi z)) ρ =
      -((deriv (deriv xi) ρ * xi ρ - deriv xi ρ * deriv xi ρ) / xi ρ ^ (2 : ℕ)) := by
    simpa only [Pi.neg_apply, Pi.div_apply] using! hquot.neg.deriv
  rw [hder]
  field_simp
  ring

/-- **Exact constraint reader.**  At every nonzero critical-line value, the first real Laguerre
margin is `-Xi(t)²` times the quadratic Taylor coefficient of the completed-flux germ. -/
theorem xi_laguerre_margin_eq_neg_sq_mul_completedFluxTaylorCoeff_two
    (t : ℝ) (ht : Xi t ≠ 0) :
    (((deriv Xi t) ^ (2 : ℕ) - Xi t * deriv (deriv Xi) t : ℝ) : ℂ) =
      -((Xi t : ℂ) ^ (2 : ℕ)) * completedFluxTaylorCoeff (linePt t) 2 := by
  have hline : linePt t = 1 / 2 + (t : ℂ) * I := by
    unfold linePt
    norm_num
  have hxi : xi (linePt t) ≠ 0 := by
    rw [hline, xiHalfLine_real]
    exact_mod_cast ht
  rw [completedFluxTaylorCoeff_two_of_ne_zero hxi,
    seamFluxCochain_deriv_eq_xi_laguerre_div hxi]
  rw [hline]
  have h0 := XiC_ofReal t
  have h1 := XiC_deriv_ofReal t
  have h2 := XiC_secondDeriv_ofReal t
  rw [XiC] at h0
  rw [XiC_deriv_eq_xi_deriv_mul_I] at h1
  rw [XiC_secondDeriv_eq_neg_xi_secondDeriv] at h2
  have hd : deriv xi (1 / 2 + (t : ℂ) * I) = -((deriv Xi t : ℝ) : ℂ) * I := by
    calc
      deriv xi (1 / 2 + (t : ℂ) * I) =
          (deriv xi (1 / 2 + (t : ℂ) * I) * I) * (-I) := by
            rw [mul_assoc, mul_neg, I_mul_I]
            ring
      _ = ((deriv Xi t : ℝ) : ℂ) * (-I) := by rw [h1]
      _ = -((deriv Xi t : ℝ) : ℂ) * I := by ring
  have hd2 : deriv (deriv xi) (1 / 2 + (t : ℂ) * I) =
      -((deriv (deriv Xi) t : ℝ) : ℂ) := by
    rw [← h2]
    simp
  rw [h0, hd, hd2]
  have htC : (((Xi t : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast ht
  push_cast
  field_simp [htC]
  simp [I_sq]
  ring

/-- Positivity of the quadratic completed-flux coefficient is pointwise equivalent to strict
failure of the first Laguerre inequality. -/
theorem completedFluxTaylorCoeff_two_line_re_pos_iff_laguerre_failure
    (t : ℝ) (ht : Xi t ≠ 0) :
    0 < (completedFluxTaylorCoeff (linePt t) 2).re ↔
      (deriv Xi t) ^ (2 : ℕ) < Xi t * deriv (deriv Xi) t := by
  have hreaderC := xi_laguerre_margin_eq_neg_sq_mul_completedFluxTaylorCoeff_two t ht
  have hscale : -((Xi t : ℂ) ^ (2 : ℕ)) = ((-(Xi t) ^ (2 : ℕ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hscale] at hreaderC
  have hreader := congrArg Complex.re hreaderC
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at hreader
  constructor <;> intro h <;> nlinarith [sq_pos_of_ne_zero ht]

/-- The existential source certificate is exactly the already-formalized strict Laguerre
certificate.  The nonvanishing clause on the source side is automatic on the Laguerre side. -/
theorem exists_completedFluxTaylorCoeff_two_line_re_pos_iff_laguerre_failure :
    (∃ t : ℝ, Xi t ≠ 0 ∧ 0 < (completedFluxTaylorCoeff (linePt t) 2).re) ↔
      ∃ t : ℝ, (deriv Xi t) ^ (2 : ℕ) < Xi t * deriv (deriv Xi) t := by
  constructor
  · rintro ⟨t, ht, hcoeff⟩
    exact ⟨t, (completedFluxTaylorCoeff_two_line_re_pos_iff_laguerre_failure t ht).mp hcoeff⟩
  · rintro ⟨t, hfail⟩
    have ht : Xi t ≠ 0 := by
      intro hzero
      rw [hzero] at hfail
      nlinarith [sq_nonneg (deriv Xi t)]
    exact ⟨t, ht,
      (completedFluxTaylorCoeff_two_line_re_pos_iff_laguerre_failure t ht).mpr hfail⟩

/-- **Quadratic completed-flux refutation certificate.**  A positive real quadratic coefficient
at one nonzero critical-line point refutes RH. -/
theorem completedFluxTaylorCoeff_two_line_re_pos_not_RH
    (h : ∃ t : ℝ, Xi t ≠ 0 ∧ 0 < (completedFluxTaylorCoeff (linePt t) 2).re) :
    ¬ RiemannHypothesis :=
  laguerre_margin_neg_not_RH
    (exists_completedFluxTaylorCoeff_two_line_re_pos_iff_laguerre_failure.mp h)

/-- On the critical line, the quadratic completed coefficient is exactly the sum of its fixed
continued-prime and archimedean/boundary coefficients. -/
theorem completedFluxTaylorCoeff_two_line_eq_prime_add_archimedean (t : ℝ) :
    completedFluxTaylorCoeff (linePt t) 2 =
      infinitePrimeFluxTaylorCoeff (linePt t) 2 +
        archimedeanBoundaryFluxTaylorCoeff (linePt t) 2 := by
  apply completedFluxTaylorCoeff_eq_prime_add_archimedean
  rw [linePt_re]
  norm_num

/-- **Euler--Gamma source refutation certificate.**  If the real part of the fixed continued-prime
plus archimedean quadratic coefficient is positive at one nonzero critical-line point, RH is false. -/
theorem prime_archimedean_second_coeff_line_re_pos_not_RH
    (h : ∃ t : ℝ, Xi t ≠ 0 ∧
      0 < (infinitePrimeFluxTaylorCoeff (linePt t) 2 +
        archimedeanBoundaryFluxTaylorCoeff (linePt t) 2).re) :
    ¬ RiemannHypothesis := by
  apply completedFluxTaylorCoeff_two_line_re_pos_not_RH
  obtain ⟨t, ht, hpos⟩ := h
  refine ⟨t, ht, ?_⟩
  rw [completedFluxTaylorCoeff_two_line_eq_prime_add_archimedean]
  exact hpos

end

end RHTower
