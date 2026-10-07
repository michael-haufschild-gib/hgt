import GaloisForLFunctions.HTGeometry.PolynomialSegmentArgument

/-!
# Radial logarithms of polynomials without zeros on the polydisk

For a polynomial `P` in finitely many variables and a point `w`, the radial restriction
`s ↦ P(s w)` is the one-variable polynomial `radialPoly P w`, of degree at most the total degree.
If `P(s w) ≠ 0` for `s ∈ [0,1]`, the radial logarithm

`radialLog P w = log P(0) + ∫₀¹ ∂ₛP(sw)/P(sw) ds`

satisfies `exp (radialLog P w) = P(w)` (`exp_radialLog`) and
`|Im radialLog P w − arg P(0)| ≤ π · totalDegree P` (`abs_im_radialLog_sub_le`).

Along a continuous path `x ↦ w(x)` whose radial segments avoid the zeros of `P`, `x ↦ radialLog P (w x)`
is continuous (`continuous_radialLog_comp`).  Hence it is a continuous logarithm of `P ∘ w`, and its
derivative is the logarithmic derivative (`hasDerivAt_radialLog_comp`).  This turns argument
variation of `P` along any such path into a difference of two radial values, each within
`π · totalDegree P` of `arg P(0)`.
-/

open Complex Polynomial Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The radial restriction `s ↦ P(s w)` as a one-variable polynomial. -/
def radialPoly (P : MvPolynomial ι ℂ) (w : ι → ℂ) : ℂ[X] :=
  ∑ α ∈ P.support, C (MvPolynomial.coeff α P * ∏ j, w j ^ α j) * X ^ (∑ j, α j)

theorem eval_radialPoly (P : MvPolynomial ι ℂ) (w : ι → ℂ) (s : ℂ) :
    (radialPoly P w).eval s = MvPolynomial.eval (fun j => s * w j) P := by
  rw [radialPoly, MvPolynomial.eval_eq', Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem natDegree_radialPoly_le (P : MvPolynomial ι ℂ) (w : ι → ℂ) :
    (radialPoly P w).natDegree ≤ P.totalDegree := by
  unfold radialPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro α hα
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  have := MvPolynomial.le_totalDegree hα
  rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this

/-- The `s`-derivative of the radial restriction, written out. -/
theorem eval_derivative_radialPoly (P : MvPolynomial ι ℂ) (w : ι → ℂ) (s : ℂ) :
    (derivative (radialPoly P w)).eval s =
      ∑ α ∈ P.support, MvPolynomial.coeff α P * (∏ j, w j ^ α j) *
        ((∑ j, α j : ℕ) * s ^ (∑ j, α j - 1)) := by
  rw [radialPoly, Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, Polynomial.eval_mul,
    Polynomial.eval_C]
  simp only [Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X,
    map_natCast]

/-- The radial logarithm. -/
def radialLog (P : MvPolynomial ι ℂ) (w : ι → ℂ) : ℂ :=
  Complex.log (MvPolynomial.eval 0 P) +
    ∫ s in (0 : ℝ)..1, (derivative (radialPoly P w)).eval (s : ℂ) / (radialPoly P w).eval (s : ℂ)

/-- Radial segments avoiding the zeros of `P`. -/
def RadialFree (P : MvPolynomial ι ℂ) (w : ι → ℂ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, MvPolynomial.eval (fun j => (s : ℂ) * w j) P ≠ 0

theorem RadialFree.eval_ne {P : MvPolynomial ι ℂ} {w : ι → ℂ} (h : RadialFree P w) :
    ∀ s ∈ Icc (0 : ℝ) 1, (radialPoly P w).eval (s : ℂ) ≠ 0 := by
  intro s hs
  rw [eval_radialPoly]
  exact h s hs

theorem radialPoly_eval_zero (P : MvPolynomial ι ℂ) (w : ι → ℂ) :
    (radialPoly P w).eval 0 = MvPolynomial.eval 0 P := by
  rw [eval_radialPoly]
  simp only [zero_mul]
  rfl

/-- `exp (radialLog P w) = P(w)`. -/
theorem exp_radialLog {P : MvPolynomial ι ℂ} {w : ι → ℂ} (h : RadialFree P w) :
    Complex.exp (radialLog P w) = MvPolynomial.eval w P := by
  have := exp_log_add_integral_logDeriv h.eval_ne
  rw [radialPoly_eval_zero, eval_radialPoly] at this
  simpa [radialLog] using this

/-- `|Im radialLog P w − arg P(0)| ≤ π · totalDegree P`. -/
theorem abs_im_radialLog_sub_le {P : MvPolynomial ι ℂ} {w : ι → ℂ} (h : RadialFree P w) :
    |(radialLog P w).im - (Complex.log (MvPolynomial.eval 0 P)).im| ≤
      Real.pi * P.totalDegree := by
  have hint : IntervalIntegrable (fun s : ℝ => (derivative (radialPoly P w)).eval (s : ℂ) /
      (radialPoly P w).eval (s : ℂ)) MeasureTheory.volume 0 1 :=
    (continuousOn_logDeriv_poly_segment h.eval_ne).intervalIntegrable
  have him : (∫ s in (0 : ℝ)..1, (derivative (radialPoly P w)).eval (s : ℂ) /
      (radialPoly P w).eval (s : ℂ)).im =
      ∫ s in (0 : ℝ)..1, ((derivative (radialPoly P w)).eval (s : ℂ) /
        (radialPoly P w).eval (s : ℂ)).im :=
    (Complex.imCLM.intervalIntegral_comp_comm hint).symm
  rw [radialLog, Complex.add_im, add_sub_cancel_left, him]
  refine (abs_integral_im_logDeriv_le _ _ rfl h.eval_ne).trans ?_
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast natDegree_radialPoly_le P w)
    Real.pi_pos.le

/-! ## Continuity and differentiation along paths -/

/-- The clamped radial integrand as a function of the path parameter and `s`. -/
def radialIntegrand (P : MvPolynomial ι ℂ) (w : ℝ → ι → ℂ) (x s : ℝ) : ℂ :=
  clampedLogDeriv (radialPoly P (w x)) s

theorem continuous_radialIntegrand {P : MvPolynomial ι ℂ} {w : ℝ → ι → ℂ} (hw : Continuous w)
    (hfree : ∀ x, RadialFree P (w x)) :
    Continuous (Function.uncurry (radialIntegrand P w)) := by
  have hp : Continuous fun q : ℝ × ℝ => ((projIcc (0 : ℝ) 1 zero_le_one q.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
  have hwx : Continuous fun q : ℝ × ℝ => w q.1 := hw.comp continuous_fst
  have hnum : Continuous fun q : ℝ × ℝ =>
      (derivative (radialPoly P (w q.1))).eval ((projIcc (0 : ℝ) 1 zero_le_one q.2 : ℝ) : ℂ) := by
    simp_rw [eval_derivative_radialPoly]
    apply continuous_finsetSum
    intro α _
    have hwj : ∀ j, Continuous fun q : ℝ × ℝ => w q.1 j :=
      fun j => (continuous_apply j).comp hwx
    fun_prop
  have hden : Continuous fun q : ℝ × ℝ =>
      (radialPoly P (w q.1)).eval ((projIcc (0 : ℝ) 1 zero_le_one q.2 : ℝ) : ℂ) := by
    simp_rw [eval_radialPoly]
    have hwj : ∀ j, Continuous fun q : ℝ × ℝ => w q.1 j :=
      fun j => (continuous_apply j).comp hwx
    exact (MvPolynomial.continuous_eval P).comp (continuous_pi fun j => hp.mul (hwj j))
  refine hnum.div hden ?_
  intro q
  exact (hfree q.1).eval_ne _ (projIcc (0 : ℝ) 1 zero_le_one q.2).2

theorem radialLog_eq_clamped (P : MvPolynomial ι ℂ) (w : ι → ℂ) :
    radialLog P w = Complex.log (MvPolynomial.eval 0 P) +
      ∫ s in (0 : ℝ)..1, clampedLogDeriv (radialPoly P w) s := by
  rw [radialLog, integral_clampedLogDeriv]

theorem continuous_radialLog_comp {P : MvPolynomial ι ℂ} {w : ℝ → ι → ℂ} (hw : Continuous w)
    (hfree : ∀ x, RadialFree P (w x)) :
    Continuous fun x => radialLog P (w x) := by
  simp_rw [radialLog_eq_clamped]
  exact continuous_const.add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_radialIntegrand hw hfree) 0 1)

/-- **The radial logarithm differentiates to the logarithmic derivative along a path.** -/
theorem hasDerivAt_radialLog_comp {P : MvPolynomial ι ℂ} {w : ℝ → ι → ℂ} (hw : Continuous w)
    (hfree : ∀ x, RadialFree P (w x)) {x₀ : ℝ} {g' : ℂ}
    (hg : HasDerivAt (fun x => MvPolynomial.eval (w x) P) g' x₀) :
    HasDerivAt (fun x => radialLog P (w x)) (g' / MvPolynomial.eval (w x₀) P) x₀ := by
  have hne : MvPolynomial.eval (w x₀) P ≠ 0 := by
    have := hfree x₀ 1 ⟨zero_le_one, le_rfl⟩
    rw [Complex.ofReal_one] at this
    simp only [one_mul] at this
    exact this
  exact hasDerivAt_of_exp_eq (g := fun x => MvPolynomial.eval (w x) P)
    (L := fun x => radialLog P (w x)) hg hne (continuous_radialLog_comp hw hfree).continuousAt
    (Eventually.of_forall fun x => exp_radialLog (hfree x))

end

end GaloisForLFunctions.HTGeometry
