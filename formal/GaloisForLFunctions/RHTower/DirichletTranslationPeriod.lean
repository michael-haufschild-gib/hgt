import GaloisForLFunctions.RHTower.ArithmeticDirichletTwistedBoundary
import GaloisForLFunctions.RHTower.ArithmeticLDifferenceHolder
import GaloisForLFunctions.Hurwitz.NonRationality
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Translation periods of finite-abscissa Dirichlet sources

Equality with a fixed complex translate on all sufficiently large real arguments
is equivalent to fixing every supported arithmetic coefficient under that shift.
Thus the exact period condition is `n^(-a)=1` at every nonzero coefficient.

The literal zeta source has all positive coefficients equal to one. Its phase
condition forces `a=0`, using the existing non-rationality of `n^(-a)` for a
nonintegral exponent. A primitive with derivative zeta on a right half-plane also
has no nontrivial constant additive translation law.

These statements exclude direct identification of the unchanged source with an
ordinary periodic cusp, including the additive-primitive repair. They do not
classify arbitrary coordinate changes or fractional-linear monodromy. Absence of
a period of a function does not exclude arithmetic progressions in its zero set,
and this result gives no zero-location theorem or new RH proof route.
-/

open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower.DirichletTranslationPeriod

private theorem abscissa_lt_top (f : finiteAbscissaArithmeticSubalgebra) :
    LSeries.abscissaOfAbsConv (fun n => f.1 n) < ⊤ := by
  obtain ⟨H, hH⟩ := finiteAbscissaArithmetic_abscissa_le f
  exact hH.trans_lt (EReal.coe_lt_top H)

/-- Equality with a translate at the real upper end is exactly coefficient invariance. -/
theorem eventually_shift_eq_iff (f : finiteAbscissaArithmeticSubalgebra) (a : ℂ) :
    ((fun x : ℝ => LSeries (fun n => f.1 n) ((x : ℂ) + a)) =ᶠ[atTop]
      (fun x : ℝ => LSeries (fun n => f.1 n) (x : ℂ))) ↔
      dirichletShift a f.1 = f.1 := by
  constructor
  · intro h
    have he : (fun x : ℝ => LSeries (fun n => dirichletShift a f.1 n) (x : ℂ))
        =ᶠ[atTop] (fun x : ℝ => LSeries (fun n => f.1 n) (x : ℂ)) :=
      h.mono fun x hx => (LSeries_dirichletShift a (x : ℂ) f.1).trans hx
    apply ArithmeticFunction.ext
    intro n
    by_cases hn : n = 0
    · subst n; simp only [ArithmeticFunction.map_zero]
    · exact LSeries.eq_of_LSeries_eventually_eq
        (abscissa_lt_top (finiteAbscissaDirichletShift a f)) (abscissa_lt_top f) he hn
  · intro h
    apply Filter.Eventually.of_forall
    intro x
    exact (LSeries_dirichletShift a (x : ℂ) f.1).symm.trans
      (congrArg (fun g : ArithmeticFunction ℂ => LSeries (fun n => g n) (x : ℂ)) h)

/-- Every supported coefficient must have trivial translation phase, and this suffices. -/
theorem eventually_shift_eq_iff_support (f : finiteAbscissaArithmeticSubalgebra) (a : ℂ) :
    ((fun x : ℝ => LSeries (fun n => f.1 n) ((x : ℂ) + a)) =ᶠ[atTop]
      (fun x : ℝ => LSeries (fun n => f.1 n) (x : ℂ))) ↔
      ∀ n : ℕ, f.1 n ≠ 0 → (n : ℂ) ^ (-a) = 1 := by
  rw [eventually_shift_eq_iff]
  constructor
  · intro h n hn
    have he := congrArg (fun g : ArithmeticFunction ℂ => g n) h
    change (n : ℂ) ^ (-a) * f.1 n = f.1 n at he
    exact mul_right_cancel₀ hn (he.trans (one_mul _).symm)
  · intro h
    apply ArithmeticFunction.ext
    intro n
    rw [ArithmeticTwistedBoundary.twist_apply]
    by_cases hn : f.1 n = 0
    · rw [hn, mul_zero]
    · rw [h n hn, one_mul]

private theorem eq_zero_of_all_nat_cpow_eq_one {a : ℂ}
    (h : ∀ n : ℕ, n ≠ 0 → (n : ℂ) ^ (-a) = 1) : a = 0 := by
  have hre : a.re = 0 := by
    by_contra ha
    exact ArithmeticTwistedBoundary.nat_cpow_ne_one ha Nat.one_lt_two (h 2 (Nat.succ_ne_zero 1))
  by_contra ha
  have hint : ∀ k : ℤ, a ≠ (k : ℂ) := by
    intro k hk
    have hkR : (k : ℝ) = 0 := (congrArg Complex.re hk).symm.trans hre
    have hk0 : k = 0 := Int.cast_eq_zero.mp hkR
    exact ha (hk.trans (by rw [hk0, Int.cast_zero]))
  apply HurwitzNonRat.not_eventually_cpow_polyRatio hint
    (num := (1 : Polynomial ℂ)) (denom := 1) one_ne_zero one_ne_zero
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [Polynomial.eval_one, mul_one]
  exact h n hn.ne'

/-- The actual zeta function has no nonzero translation period even at the real upper end. -/
theorem zeta_eventually_shift_eq_iff (a : ℂ) :
    ((fun x : ℝ => riemannZeta ((x : ℂ) + a)) =ᶠ[atTop]
      (fun x : ℝ => riemannZeta (x : ℂ))) ↔ a = 0 := by
  constructor
  · intro h
    have he : (fun x : ℝ => LSeries (fun n => zetaFiniteAbscissaSource.1 n) ((x : ℂ) + a))
        =ᶠ[atTop] (fun x : ℝ => LSeries (fun n => zetaFiniteAbscissaSource.1 n) (x : ℂ)) := by
      filter_upwards [h, eventually_gt_atTop (1 : ℝ),
        eventually_gt_atTop (1 - a.re)] with x hx hx1 hxa
      have hxa' : 1 < ((x : ℂ) + a).re := sub_lt_iff_lt_add.mp hxa
      exact (LSeries_riemannZetaArithmeticLFunction_eq hxa').trans
        (hx.trans (LSeries_riemannZetaArithmeticLFunction_eq hx1).symm)
    have hs := (eventually_shift_eq_iff_support zetaFiniteAbscissaSource a).mp he
    apply eq_zero_of_all_nat_cpow_eq_one
    intro n hn
    apply hs n
    rw [zetaFiniteAbscissaSource_apply hn]
    exact one_ne_zero
  · rintro rfl
    exact Filter.Eventually.of_forall fun x => congrArg riemannZeta (add_zero _)

/-- A primitive of zeta on a right half-plane has no nontrivial constant additive translation law. -/
theorem primitive_additive_period_trivial (f : ℂ → ℂ) (H : ℝ) (a b : ℂ)
    (hd : ∀ z : ℂ, H < z.re → HasDerivAt f (riemannZeta z) z)
    (hp : ∀ z : ℂ, H < z.re → f (z + a) = f z + b) : a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    apply (zeta_eventually_shift_eq_iff a).mp
    filter_upwards [eventually_gt_atTop H, eventually_gt_atTop (H - a.re)] with x hx hxa
    have hxa' : H < ((x : ℂ) + a).re := sub_lt_iff_lt_add.mp hxa
    have hshift := (hd ((x : ℂ) + a) hxa').comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const a)
    rw [mul_one] at hshift
    have he : (fun z => f z + b) =ᶠ[𝓝 (x : ℂ)] (fun z => f (z + a)) := by
      filter_upwards [(Complex.continuous_re.tendsto (x : ℂ)).eventually
        (eventually_gt_nhds hx)] with z hz
      exact (hp z hz).symm
    exact (hshift.congr_of_eventuallyEq he).unique ((hd (x : ℂ) hx).add_const b)
  refine ⟨ha, ?_⟩
  have he := hp ((H + 1 : ℝ) : ℂ) (lt_add_one H)
  rw [ha, add_zero] at he
  exact add_left_cancel (he.symm.trans (add_zero _).symm)

end RHTower.DirichletTranslationPeriod
