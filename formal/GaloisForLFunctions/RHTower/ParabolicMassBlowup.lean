import GaloisForLFunctions.RHTower.MassInformationHorizon
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The parabolic blow-up of the mass-shifted spectrum

With `β_a = √(a² + w)` the square-root equation gives the exact remainder identity

`2a(β_a - a) = w - w²/(β_a + a)²`,

so the renormalized propagator `e^{2a²t} e^{-2at β_a} = e^{-t·2a(β_a-a)}` converges to the Gaussian
heat factor `e^{-tw}` as the mass grows.  The domination that makes the limit pass through the
whole spectrum is the orbit inequality

`a(M - a) ≥ a(R² - 1/4)/(2a + R) ≥ (35/108) R`   (uniformly for `a ≥ 1`, `R > 3`, `|J| ≤ 1/2`),

which turns every polynomial in `w` into a fixed exponentially decaying majorant in `R`.

No approximate multiplier is needed for the polynomial jets: `L_a = ∂_τ² - a²` has the mass-shifted
exponential `e^{-τβ_a}` as an exact eigenvector with eigenvalue `β_a² - a² = w`, so a polynomial in
`L_a` acts on it by the same polynomial in `w`.  Finally, on any half line `t ≥ t₀ > 0` the heat
factor is Lipschitz in time with constant `|w| e^{-t₀ Re w}`.
-/

open Filter Topology Complex

namespace RHTower

noncomputable section

/-! ## The orbit is confined by the mass and the real part -/

/-- **(24.93) without a nonvanishing transverse part.**  Any solution of the mass-shift equations
has `M ≤ a + R`. -/
theorem massOrbit_upper {R J a M K : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a) (hM : 0 < M)
    (hsq : M ^ (2 : ℕ) - K ^ (2 : ℕ) = R ^ (2 : ℕ) - J ^ (2 : ℕ) + a ^ (2 : ℕ)) (hprod : M * K = R * J) :
    M ≤ a + R := by
  have hquart : M ^ (2 : ℕ) * (M ^ (2 : ℕ) - R ^ (2 : ℕ) + J ^ (2 : ℕ) - a ^ (2 : ℕ)) = R ^ (2 : ℕ) * J ^ (2 : ℕ) := by
    have hK : M ^ (2 : ℕ) * K ^ (2 : ℕ) = R ^ (2 : ℕ) * J ^ (2 : ℕ) := by
      rw [← mul_pow, ← mul_pow, hprod]
    nlinarith [hsq, hK]
  have haR : 0 ≤ a + R := by linarith
  have haRnn : 0 ≤ a * R := mul_nonneg ha hR
  have hkey : ((a + R) ^ (2 : ℕ) - M ^ (2 : ℕ)) * (2 * a * R + M ^ (2 : ℕ) + J ^ (2 : ℕ))
      = (a + R) ^ (2 : ℕ) * (2 * a * R + J ^ (2 : ℕ)) - R ^ (2 : ℕ) * J ^ (2 : ℕ) := by
    linear_combination -hquart
  have hfs : 0 ≤ (a + R) ^ (2 : ℕ) * (2 * a * R + J ^ (2 : ℕ)) - R ^ (2 : ℕ) * J ^ (2 : ℕ) := by
    nlinarith [haRnn, sq_nonneg J, sq_nonneg (a + R), sq_nonneg R]
  have hfactor : 0 < 2 * a * R + M ^ (2 : ℕ) + J ^ (2 : ℕ) := by nlinarith [haRnn, sq_nonneg J, hM]
  have hM2 : M ^ (2 : ℕ) ≤ (a + R) ^ (2 : ℕ) := by nlinarith [hkey, hfs, hfactor]
  nlinarith [hM, haR]

/-- **(24.108)** The mass gap of the orbit is bounded below by the real part of the spectral
point. -/
theorem parabolic_gap_lower {R J a M K : ℝ} (hR : 3 < R) (hJ : |J| ≤ 1 / 2) (ha : 0 < a)
    (hM : 0 < M) (hsq : M ^ (2 : ℕ) - K ^ (2 : ℕ) = R ^ (2 : ℕ) - J ^ (2 : ℕ) + a ^ (2 : ℕ)) (hprod : M * K = R * J) :
    a * (R ^ (2 : ℕ) - 1 / 4) / (2 * a + R) ≤ a * (M - a) := by
  have hRnn : (0 : ℝ) ≤ R := by linarith
  have hupper : M ≤ a + R := massOrbit_upper hRnn ha.le hM hsq hprod
  have hJ2 : J ^ (2 : ℕ) ≤ 1 / 4 := by
    have habs := abs_le.1 hJ
    nlinarith [habs.1, habs.2]
  have hprodlow : R ^ (2 : ℕ) - 1 / 4 ≤ (M - a) * (M + a) := by
    nlinarith [sq_nonneg K, hsq, hJ2]
  have hden : 0 < 2 * a + R := by linarith
  have hMa : M + a ≤ 2 * a + R := by linarith
  have hgapnn : 0 ≤ M - a := by
    nlinarith [hprodlow, hM, ha]
  have hstep : (R ^ (2 : ℕ) - 1 / 4) / (2 * a + R) ≤ M - a := by
    rw [div_le_iff₀ hden]
    nlinarith [hprodlow, hgapnn, hMa, hM, ha]
  calc a * (R ^ (2 : ℕ) - 1 / 4) / (2 * a + R) = a * ((R ^ (2 : ℕ) - 1 / 4) / (2 * a + R)) := by ring
    _ ≤ a * (M - a) := mul_le_mul_of_nonneg_left hstep ha.le

/-- **(24.108)** The uniform form: the mass gap dominates a fixed positive multiple of the real
part, for every mass at least one. -/
theorem parabolic_gap_uniform_lower {R J a M K : ℝ} (hR : 3 < R) (hJ : |J| ≤ 1 / 2) (ha : 1 ≤ a)
    (hM : 0 < M) (hsq : M ^ (2 : ℕ) - K ^ (2 : ℕ) = R ^ (2 : ℕ) - J ^ (2 : ℕ) + a ^ (2 : ℕ)) (hprod : M * K = R * J) :
    35 / 108 * R ≤ a * (M - a) := by
  have hapos : 0 < a := by linarith
  have hbase := parabolic_gap_lower hR hJ hapos hM hsq hprod
  have hden : 0 < 2 * a + R := by linarith
  have hRpos : (0 : ℝ) < R := by linarith
  have hsq9 : 9 ≤ R ^ (2 : ℕ) := by nlinarith
  have hquarter : (35 : ℝ) / 36 * R ^ (2 : ℕ) ≤ R ^ (2 : ℕ) - 1 / 4 := by nlinarith
  have hRle : R ≤ R ^ (2 : ℕ) := by nlinarith
  have hkey : 35 / 108 * R ≤ a * (R ^ (2 : ℕ) - 1 / 4) / (2 * a + R) := by
    rw [le_div_iff₀ hden]
    rcases le_or_gt R a with hcase | hcase
    · have hA : 35 / 108 * R * (2 * a + R) ≤ 35 / 108 * R * (3 * a) := by nlinarith
      have hC : 35 / 108 * R * (3 * a) ≤ a * (35 / 36 * R ^ (2 : ℕ)) := by nlinarith
      have hB : a * (35 / 36 * R ^ (2 : ℕ)) ≤ a * (R ^ (2 : ℕ) - 1 / 4) := by nlinarith
      linarith
    · have hA : 35 / 108 * R * (2 * a + R) ≤ 35 / 108 * R * (3 * R) := by nlinarith
      have hB : 35 / 108 * R * (3 * R) = 35 / 36 * R ^ (2 : ℕ) := by ring
      have hC : 35 / 36 * R ^ (2 : ℕ) ≤ a * (R ^ (2 : ℕ) - 1 / 4) := by nlinarith
      linarith
  linarith

/-! ## The exact remainder identity and the parabolic limit -/

/-- **(24.106)** The exact square-root remainder identity. -/
theorem parabolic_remainder_identity {a : ℝ} {w beta : ℂ} (hbeta : beta ^ (2 : ℕ) = (a : ℂ) ^ (2 : ℕ) + w)
    (hne : beta + (a : ℂ) ≠ 0) :
    2 * (a : ℂ) * (beta - (a : ℂ)) = w - w ^ (2 : ℕ) / (beta + (a : ℂ)) ^ (2 : ℕ) := by
  have hw : w = (beta - (a : ℂ)) * (beta + (a : ℂ)) := by
    linear_combination -hbeta
  have hne2 : (beta + (a : ℂ)) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hne
  rw [hw]
  field_simp
  ring

/-- The renormalized propagator is the exponential of the remainder. -/
theorem parabolic_renormalized_exp (a t : ℝ) (beta : ℂ) :
    Complex.exp ((2 * (a : ℂ) ^ (2 : ℕ) * (t : ℂ)))
        * Complex.exp (-(2 * (a : ℂ) * (t : ℂ) * beta))
      = Complex.exp (-(t : ℂ) * (2 * (a : ℂ) * (beta - (a : ℂ)))) := by
  rw [← Complex.exp_add]
  congr 1
  ring

/-- **(24.107)** The renormalized remainder converges to the spectral point. -/
theorem tendsto_parabolic_remainder {w : ℂ} {beta : ℝ → ℂ}
    (hbeta : ∀ a : ℝ, beta a ^ (2 : ℕ) = (a : ℂ) ^ (2 : ℕ) + w)
    (hre : ∀ a : ℝ, 0 ≤ (beta a).re) :
    Tendsto (fun a : ℝ => 2 * (a : ℂ) * (beta a - (a : ℂ))) atTop (nhds w) := by
  have hzero : Tendsto (fun a : ℝ => w ^ (2 : ℕ) / (beta a + (a : ℂ)) ^ (2 : ℕ)) atTop (nhds 0) := by
    have hmajor : ∀ᶠ a : ℝ in atTop,
        ‖w ^ (2 : ℕ) / (beta a + (a : ℂ)) ^ (2 : ℕ)‖ ≤ ‖w‖ ^ (2 : ℕ) / a ^ (2 : ℕ) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      have hre' : (a : ℝ) ≤ (beta a + (a : ℂ)).re := by
        simp only [Complex.add_re, Complex.ofReal_re]
        linarith [hre a]
      have hden : (a : ℝ) ≤ ‖beta a + (a : ℂ)‖ := by
        calc (a : ℝ) ≤ (beta a + (a : ℂ)).re := hre'
          _ ≤ |(beta a + (a : ℂ)).re| := le_abs_self _
          _ ≤ ‖beta a + (a : ℂ)‖ := Complex.abs_re_le_norm _
      have hpos : (0 : ℝ) < ‖beta a + (a : ℂ)‖ := lt_of_lt_of_le ha hden
      rw [norm_div, norm_pow, norm_pow]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      nlinarith [hden, ha.le, norm_nonneg (beta a + (a : ℂ))]
    have hgo : Tendsto (fun a : ℝ => ‖w‖ ^ (2 : ℕ) / a ^ (2 : ℕ)) atTop (nhds 0) := by
      have hinv : Tendsto (fun a : ℝ => a ^ (2 : ℕ)) atTop atTop :=
        tendsto_pow_atTop (by norm_num)
      exact tendsto_const_nhds.div_atTop hinv
    exact squeeze_zero_norm' hmajor hgo
  have hlim : Tendsto (fun a : ℝ => w - w ^ (2 : ℕ) / (beta a + (a : ℂ)) ^ (2 : ℕ)) atTop (nhds (w - 0)) :=
    tendsto_const_nhds.sub hzero
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have hne : beta a + (a : ℂ) ≠ 0 := by
    intro hcon
    have hrez : (beta a + (a : ℂ)).re = 0 := by rw [hcon]; simp
    simp only [Complex.add_re, Complex.ofReal_re] at hrez
    linarith [hre a]
  exact (parabolic_remainder_identity (hbeta a) hne).symm

/-- **(24.107)** The renormalized propagator converges to the Gaussian heat factor. -/
theorem tendsto_parabolic_heat {w : ℂ} {beta : ℝ → ℂ}
    (hbeta : ∀ a : ℝ, beta a ^ (2 : ℕ) = (a : ℂ) ^ (2 : ℕ) + w)
    (hre : ∀ a : ℝ, 0 ≤ (beta a).re) (t : ℝ) :
    Tendsto
      (fun a : ℝ => Complex.exp (2 * (a : ℂ) ^ (2 : ℕ) * (t : ℂ))
        * Complex.exp (-(2 * (a : ℂ) * (t : ℂ) * beta a)))
      atTop (nhds (Complex.exp (-(t : ℂ) * w))) := by
  have hbase := (tendsto_parabolic_remainder hbeta hre).const_mul (-(t : ℂ))
  have hcomp := (Complex.continuous_exp.tendsto _).comp hbase
  refine hcomp.congr fun a => ?_
  rw [Function.comp_apply, parabolic_renormalized_exp]

/-! ## The mass jet operator has the shifted exponential as an exact eigenvector -/

/-- The mass jet operator `L_a = ∂_τ² - a²`. -/
def massJetOp (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun tau => deriv (deriv f) tau - (a : ℂ) ^ (2 : ℕ) * f tau

theorem hasDerivAt_expScaled (c beta : ℂ) (tau : ℝ) :
    HasDerivAt (fun s : ℝ => c * Complex.exp (-(s : ℂ) * beta))
      (c * (-beta) * Complex.exp (-(tau : ℂ) * beta)) tau := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 tau := by
    simpa using (hasDerivAt_id tau).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => -(s : ℂ) * beta) (-beta) tau := by
    simpa using h1.neg.mul_const beta
  have h3 : HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ) * beta))
      (Complex.exp (-(tau : ℂ) * beta) * (-beta)) tau := h2.cexp
  have h4 := h3.const_mul c
  have heq : c * (-beta) * Complex.exp (-(tau : ℂ) * beta)
      = c * (Complex.exp (-(tau : ℂ) * beta) * (-beta)) := by ring
  rw [heq]
  exact h4

theorem deriv_expScaled (c beta : ℂ) :
    deriv (fun s : ℝ => c * Complex.exp (-(s : ℂ) * beta))
      = fun tau : ℝ => c * (-beta) * Complex.exp (-(tau : ℂ) * beta) := by
  funext tau
  exact (hasDerivAt_expScaled c beta tau).deriv

/-- **(24.112)** The mass jet operator acts on the shifted exponential by the spectral point. -/
theorem massJetOp_expScaled (a : ℝ) (c beta : ℂ) :
    massJetOp a (fun s : ℝ => c * Complex.exp (-(s : ℂ) * beta))
      = fun tau : ℝ => c * (beta ^ (2 : ℕ) - (a : ℂ) ^ (2 : ℕ)) * Complex.exp (-(tau : ℂ) * beta) := by
  funext tau
  rw [massJetOp, deriv_expScaled, deriv_expScaled]
  ring

/-- **(24.112)** Every power of the mass jet operator acts by the corresponding power. -/
theorem massJetOp_iterate_expScaled (a : ℝ) (c beta : ℂ) (k : ℕ) :
    (massJetOp a)^[k] (fun s : ℝ => c * Complex.exp (-(s : ℂ) * beta))
      = fun tau : ℝ => c * (beta ^ (2 : ℕ) - (a : ℂ) ^ (2 : ℕ)) ^ k * Complex.exp (-(tau : ℂ) * beta) := by
  induction k generalizing c with
  | zero =>
    funext tau
    simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, massJetOp_expScaled, ih]
    funext tau
    ring

/-- A polynomial in the mass jet operator. -/
def polyJet (a : ℝ) (P : Polynomial ℝ) (f : ℝ → ℂ) (tau : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (P.natDegree + 1),
    ((P.coeff k : ℝ) : ℂ) * ((massJetOp a)^[k] f tau)

/-- **(24.112)** A polynomial in the mass jet operator acts on the shifted exponential by the same
polynomial in the spectral point. -/
theorem polyJet_exp (a : ℝ) (P : Polynomial ℝ) (beta : ℂ) (tau : ℝ) :
    polyJet a P (fun s : ℝ => Complex.exp (-(s : ℂ) * beta)) tau
      = (Polynomial.aeval (beta ^ (2 : ℕ) - (a : ℂ) ^ (2 : ℕ)) P) * Complex.exp (-(tau : ℂ) * beta) := by
  have hfun : (fun s : ℝ => Complex.exp (-(s : ℂ) * beta))
      = fun s : ℝ => (1 : ℂ) * Complex.exp (-(s : ℂ) * beta) := by
    funext s
    rw [one_mul]
  rw [polyJet, hfun, Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [massJetOp_iterate_expScaled]
  rw [Algebra.smul_def, Algebra.algebraMap_eq_smul_one]
  simp only [Complex.real_smul, one_mul]
  ring

/-- **(24.112)** The squared polynomial jet of the shifted exponential is the squared polynomial in
the spectral point. -/
theorem polyJet_sq_exp (a : ℝ) (P : Polynomial ℝ) (beta : ℂ) (tau : ℝ) :
    polyJet a (P * P) (fun s : ℝ => Complex.exp (-(s : ℂ) * beta)) tau
      = (Polynomial.aeval (beta ^ (2 : ℕ) - (a : ℂ) ^ (2 : ℕ)) P) ^ (2 : ℕ) * Complex.exp (-(tau : ℂ) * beta) := by
  rw [polyJet_exp, map_mul, sq]
  ring

/-- **(24.112)** In spectral coordinates, the eigenvalue is exactly the spectral point `w`. -/
theorem polyJet_sq_exp_spectral {a : ℝ} {w beta : ℂ} (hbeta : beta ^ (2 : ℕ) = (a : ℂ) ^ (2 : ℕ) + w)
    (P : Polynomial ℝ) (tau : ℝ) :
    polyJet a (P * P) (fun s : ℝ => Complex.exp (-(s : ℂ) * beta)) tau
      = (Polynomial.aeval w P) ^ (2 : ℕ) * Complex.exp (-(tau : ℂ) * beta) := by
  have hw : beta ^ (2 : ℕ) - (a : ℂ) ^ (2 : ℕ) = w := by
    rw [hbeta]
    ring
  rw [polyJet_sq_exp, hw]

/-! ## The heat factor is Lipschitz in time on every half line -/

/-- **(24.117)** The integral Lipschitz bound for the heat factor. -/
theorem norm_exp_neg_mul_sub_le {w : ℂ} (hw : 0 ≤ w.re) {t0 s t : ℝ} (hs : t0 ≤ s) (ht : t0 ≤ t) :
    ‖Complex.exp (-(t : ℂ) * w) - Complex.exp (-(s : ℂ) * w)‖
      ≤ |t - s| * (‖w‖ * Real.exp (-(t0 * w.re))) := by
  have hderiv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => Complex.exp (-(r : ℂ) * w))
      (-w * Complex.exp (-(r : ℂ) * w)) r := by
    intro r
    have h := hasDerivAt_expScaled 1 w r
    simp only [one_mul] at h
    exact h
  have hcont : Continuous fun r : ℝ => -w * Complex.exp (-(r : ℂ) * w) := by
    fun_prop
  have hint : IntervalIntegrable (fun r : ℝ => -w * Complex.exp (-(r : ℂ) * w))
      MeasureTheory.volume s t := hcont.intervalIntegrable _ _
  have hftc : ∫ r in s..t, (-w * Complex.exp (-(r : ℂ) * w))
      = Complex.exp (-(t : ℂ) * w) - Complex.exp (-(s : ℂ) * w) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint
  have hbound : ∀ r ∈ Set.uIoc s t,
      ‖-w * Complex.exp (-(r : ℂ) * w)‖ ≤ ‖w‖ * Real.exp (-(t0 * w.re)) := by
    intro r hr
    have hr0 : t0 ≤ r := by
      rcases Set.mem_uIoc.1 hr with h | h
      · exact le_trans hs h.1.le
      · exact le_trans ht h.1.le
    have hnorm : ‖Complex.exp (-(r : ℂ) * w)‖ = Real.exp (-(r * w.re)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    rw [norm_mul, norm_neg, hnorm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    nlinarith
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hftc] at hle
  calc ‖Complex.exp (-(t : ℂ) * w) - Complex.exp (-(s : ℂ) * w)‖
      ≤ ‖w‖ * Real.exp (-(t0 * w.re)) * |t - s| := hle
    _ = |t - s| * (‖w‖ * Real.exp (-(t0 * w.re))) := by ring

end

end RHTower
