import GaloisForLFunctions.HTGeometry.StrelitzBaseCoefficient

/-!
# Heat-specific growth of the Strelitz logarithmic jets

The logarithmic radii in the selected Wiman sequence tend to infinity.  Entire complex-time heat
evolution makes the central index sublinear in that logarithmic radius.  The explicit Wiman errors
then bound the first and second logarithmic jets by `2x` and `x²`.  These bounds supply the scale
separation needed to discard every lower `z`-degree below the nonzero highest face.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter GaloisForLFunctions

/-- Any real sequence lying above the natural index tends to positive infinity. -/
theorem tendsto_atTop_of_natCast_le {x : ℕ → ℝ}
    (hx : ∀ n : ℕ, (n : ℝ) ≤ x n) : Tendsto x atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  obtain ⟨N, hN⟩ := exists_nat_ge b
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN.trans (le_trans (by exact_mod_cast hn) (hx n))

/-- Sublinear central index plus the explicit Strelitz errors gives fixed logarithmic bounds for
both logarithmic jets. -/
theorem eventually_strelitzJet_le_logRadius
    {x : ℕ → ℝ} {ν : ℕ → ℕ} {u v : ℕ → ℂ}
    (hxTop : Tendsto x atTop atTop)
    (hνx : Tendsto (fun n => (ν n : ℝ) / x n) atTop (nhds 0))
    (hu : ∀ n : ℕ, ‖u n - (ν n : ℂ)‖ ≤
      (1 / ((n : ℝ) + 1)) * (ν n : ℝ))
    (hv : ∀ n : ℕ, ‖v n‖ ≤
      (1 / ((n : ℝ) + 1)) * (ν n : ℝ) ^ 2) :
    ∀ᶠ n : ℕ in atTop,
      (ν n : ℝ) ≤ x n ∧ ‖u n‖ ≤ 2 * x n ∧ ‖v n‖ ≤ (x n) ^ 2 := by
  have hxpos : ∀ᶠ n : ℕ in atTop, 0 < x n := hxTop.eventually_gt_atTop 0
  have hratio : ∀ᶠ n : ℕ in atTop, (ν n : ℝ) / x n < 1 :=
    hνx.eventually_lt_const zero_lt_one
  filter_upwards [hxpos, hratio] with n hxn hratio
  have hνle : (ν n : ℝ) ≤ x n := le_of_lt ((div_lt_one hxn).mp hratio)
  have hrec : (1 / ((n : ℝ) + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    norm_num
  have herr : ‖u n - (ν n : ℂ)‖ ≤ (ν n : ℝ) := by
    exact (hu n).trans (by
      have hνnonneg : (0 : ℝ) ≤ (ν n : ℝ) := by positivity
      nlinarith)
  have hu' : ‖u n‖ ≤ 2 * x n := by
    have htri : ‖u n‖ ≤ ‖u n - (ν n : ℂ)‖ + ‖(ν n : ℂ)‖ := by
      simpa using norm_add_le (u n - (ν n : ℂ)) (ν n : ℂ)
    rw [Complex.norm_natCast] at htri
    linarith
  have hv' : ‖v n‖ ≤ (x n) ^ 2 := by
    calc
      ‖v n‖ ≤ (1 / ((n : ℝ) + 1)) * (ν n : ℝ) ^ 2 := hv n
      _ ≤ (ν n : ℝ) ^ 2 := by
        have hνsq : (0 : ℝ) ≤ (ν n : ℝ) ^ 2 := sq_nonneg _
        nlinarith
      _ ≤ (x n) ^ 2 := pow_le_pow_left₀ (by positivity) hνle 2
  exact ⟨hνle, hu', hv'⟩

variable {a : ℕ → ℂ}

/-- **Heat-scale Strelitz package.** Besides the fixed nonzero highest `z`-face and exact Wiman
data, the selected log radii escape, the central index is `o(x)`, and both logarithmic jets have
fixed polynomial bounds in `x`. -/
theorem exists_nonzero_strelitzBaseCoefficient_with_logarithmicJetBounds_of_order_two_entireHeat
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ P : MvPolynomial (Fin 2) (Polynomial ℂ), P ≠ 0 ∧
      strelitzBaseCoefficient P (polynomialMvCoeffDegree P) ≠ 0 ∧
      ∃ (x : ℕ → ℝ) (z : ℕ → ℂ),
        (∀ n : ℕ, (n : ℝ) ≤ x n) ∧
        (∀ n : ℕ, ‖z n‖ = Real.exp (x n)) ∧
        (∀ n : ℕ, maxTerm a (Real.exp (x n)) ≤ ‖coeffFun a (z n)‖) ∧
        (∀ n : ℕ, coeffFun a (z n) ≠ 0) ∧
        (∀ n : ℕ, ‖eulerLogDeriv (coeffFun a) (z n) -
            (centralIndex a (Real.exp (x n)) : ℂ)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ)) ∧
        (∀ n : ℕ, ‖eulerLogDerivSecond (coeffFun a) (z n)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ 2) ∧
        Tendsto x atTop atTop ∧
        Tendsto (fun n => (centralIndex a (Real.exp (x n)) : ℝ) / x n)
          atTop (nhds 0) ∧
        (∀ᶠ n : ℕ in atTop,
          (centralIndex a (Real.exp (x n)) : ℝ) ≤ x n ∧
          ‖eulerLogDeriv (coeffFun a) (z n)‖ ≤ 2 * x n ∧
          ‖eulerLogDerivSecond (coeffFun a) (z n)‖ ≤ (x n) ^ 2) ∧
        ∀ j : ℕ, Tendsto (fun n : ℕ =>
          ‖(strelitzBaseSpecialization P
            ![eulerLogDeriv (coeffFun a) (z n),
              eulerLogDerivSecond (coeffFun a) (z n)]).eval (z n)‖ *
            (Real.exp (x n)) ^ j) atTop (nhds 0) := by
  obtain ⟨P, hP, hface, x, z, hx, hz, hfloor, hfz, hu, hv, hsmall⟩ :=
    exists_nonzero_strelitzBaseCoefficient_of_order_two_entireHeat ha hheat htrans hDA
  have hxTop : Tendsto x atTop atTop := tendsto_atTop_of_natCast_le hx
  obtain ⟨n₀, -, hn₀⟩ := htrans 0
  have hνx : Tendsto (fun n => (centralIndex a (Real.exp (x n)) : ℝ) / x n)
      atTop (nhds 0) := by
    have hcomp := (tendsto_entireHeat_centralIndex_div_log_zero ha hheat hn₀).comp
      (Real.tendsto_exp_atTop.comp hxTop)
    change Tendsto (fun n =>
      (centralIndex a (Real.exp (x n)) : ℝ) / Real.log (Real.exp (x n)))
        atTop (nhds 0) at hcomp
    simpa only [Real.log_exp] using hcomp
  have hjets := eventually_strelitzJet_le_logRadius hxTop hνx hu hv
  exact ⟨P, hP, hface, x, z, hx, hz, hfloor, hfz, hu, hv,
    hxTop, hνx, hjets, hsmall⟩

end

end GaloisForLFunctions.HTGeometry
