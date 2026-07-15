import GaloisForLFunctions.HTGeometry.DirichletLSeriesDifferentialTransfer

/-!
# Finite-abscissa Dirichlet series at the complex upper end

Arithmetic functions whose Dirichlet series has some finite abscissa of absolute convergence form
a complex algebra. Rotation by `s = -I z` realizes this algebra faithfully as analytic germs at
the upper end. Unlike the fixed half-plane algebra, this carrier is stable under arbitrary finite
translations of the Dirichlet variable.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Filter Set Topology

noncomputable section

open scoped LSeries.notation

/-- Arithmetic functions absolutely summable to the right of some finite vertical line. -/
def finiteAbscissaArithmeticSubalgebra : Subalgebra ℂ (ArithmeticFunction ℂ) where
  carrier := {f | ∃ H : ℝ, ∀ y : ℝ, H < y →
    LSeriesSummable (fun n => f n) (y : ℂ)}
  zero_mem' := by
    refine ⟨0, fun y hy => ?_⟩
    change LSeriesSummable (0 : ℕ → ℂ) (y : ℂ)
    rw [LSeriesSummable]
    convert (summable_zero : Summable (0 : ℕ → ℂ)) using 1
    funext n
    simp [LSeries.term]
  one_mem' := by
    refine ⟨0, fun y hy => ?_⟩
    change LSeriesSummable (fun n => (1 : ArithmeticFunction ℂ) n) (y : ℂ)
    have hdelta : (fun n => (1 : ArithmeticFunction ℂ) n) = LSeries.delta := by
      funext n
      exact ArithmeticFunction.one_apply
    rw [hdelta, LSeriesSummable]
    apply summable_of_hasFiniteSupport
    refine Set.Finite.subset (Set.finite_singleton 1) ?_
    intro n hn
    simpa [Function.support, LSeries.term_delta] using hn
  add_mem' := by
    rintro f g ⟨H, hH⟩ ⟨K, hK⟩
    refine ⟨max H K, fun y hy => (hH y (lt_of_le_of_lt (le_max_left H K) hy)).add
      (hK y (lt_of_le_of_lt (le_max_right H K) hy))⟩
  mul_mem' := by
    rintro f g ⟨H, hH⟩ ⟨K, hK⟩
    refine ⟨max H K, fun y hy => ArithmeticFunction.LSeriesSummable_mul
      (hH y (lt_of_le_of_lt (le_max_left H K) hy))
      (hK y (lt_of_le_of_lt (le_max_right H K) hy))⟩
  algebraMap_mem' := by
    intro c
    refine ⟨1, fun y hy => ?_⟩
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := ‖c‖)
    · intro n hn
      by_cases h1 : n = 1 <;>
        simp [Algebra.algebraMap_eq_smul_one, ArithmeticFunction.smul_map,
          h1]
    · simpa using hy

/-- A finite-abscissa element has absolute-convergence abscissa bounded by one of its witnesses. -/
theorem finiteAbscissaArithmetic_abscissa_le
    (f : finiteAbscissaArithmeticSubalgebra) :
    ∃ H : ℝ, LSeries.abscissaOfAbsConv (fun n => f.1 n) ≤ H := by
  obtain ⟨H, hH⟩ := f.2
  exact ⟨H, LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable hH⟩

/-! ## Stability under Dirichlet shifts and logarithmic weights -/

/-- Coefficient shifting translates every individual L-series term. -/
theorem dirichletShift_LSeries_term (a s : ℂ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    LSeries.term (fun m => dirichletShift a f m) s n =
      LSeries.term (fun m => f m) (s + a) n := by
  rw [LSeries.term_def₀ (by simp) s,
    LSeries.term_def₀ (by simp) (s + a)]
  rw [dirichletShift_apply, cpowWeight]
  by_cases hn : n = 0
  · subst n
    simp
  · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [neg_add, Complex.cpow_add _ _ hn']
    ring

/-- Absolute convergence of a shifted coefficient stream is exactly convergence of the original
stream at the translated Dirichlet variable. -/
theorem dirichletShift_LSeriesSummable_iff (a s : ℂ) (f : ArithmeticFunction ℂ) :
    LSeriesSummable (fun n => dirichletShift a f n) s ↔
      LSeriesSummable (fun n => f n) (s + a) := by
  unfold LSeriesSummable
  exact summable_congr (dirichletShift_LSeries_term a s f)

/-- The L-series of a shifted coefficient stream is the translated original L-series. -/
theorem LSeries_dirichletShift (a s : ℂ) (f : ArithmeticFunction ℂ) :
    LSeries (fun n => dirichletShift a f n) s =
      LSeries (fun n => f n) (s + a) := by
  unfold LSeries
  exact tsum_congr (dirichletShift_LSeries_term a s f)

/-- Arbitrary complex Dirichlet shifts preserve finite abscissa. -/
def finiteAbscissaDirichletShift (a : ℂ) (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaArithmeticSubalgebra := by
  refine ⟨dirichletShift a f.1, ?_⟩
  obtain ⟨H, hH⟩ := f.2
  refine ⟨H - a.re, fun y hy =>
    (dirichletShift_LSeriesSummable_iff a (y : ℂ) f.1).mpr ?_⟩
  apply (LSeriesSummable_iff_of_re_eq_re (s := ((y + a.re : ℝ) : ℂ))
    (s' := (y : ℂ) + a) (by simp)).mp
  exact hH (y + a.re) (by linarith)

@[simp]
theorem finiteAbscissaDirichletShift_apply
    (a : ℂ) (f : finiteAbscissaArithmeticSubalgebra) (n : ℕ) :
    (finiteAbscissaDirichletShift a f).1 n = cpowWeight a n * f.1 n :=
  rfl

/-- The logarithmic coefficient derivation preserves finite abscissa. -/
def finiteAbscissaLogWeight (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaArithmeticSubalgebra := by
  refine ⟨logWeight f.1, ?_⟩
  obtain ⟨H, hH⟩ := finiteAbscissaArithmetic_abscissa_le f
  refine ⟨H, fun y hy => ?_⟩
  have hs := LSeriesSummable_logMul_of_lt_re
    (f := fun n => f.1 n) (s := (y : ℂ))
    (lt_of_le_of_lt hH (EReal.coe_lt_coe_iff.mpr hy))
  rw [lSeries_logMul_eq_logWeight] at hs
  exact hs

/-- The rotated coefficient derivation corresponding to differentiation in the upper-end
coordinate. -/
def finiteAbscissaRotatedDeriv (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaArithmeticSubalgebra :=
  Complex.I • finiteAbscissaLogWeight f

@[simp]
theorem finiteAbscissaRotatedDeriv_apply
    (f : finiteAbscissaArithmeticSubalgebra) (n : ℕ) :
    (finiteAbscissaRotatedDeriv f).1 n =
      Complex.I * (Real.log n : ℂ) * f.1 n := by
  simp [finiteAbscissaRotatedDeriv, finiteAbscissaLogWeight,
    ArithmeticFunction.smul_map, logWeight_apply]
  ring

/-- Exact coefficient formula for every iterate of the finite-abscissa rotated derivation. -/
theorem finiteAbscissaRotatedDeriv_iterate_apply
    (f : finiteAbscissaArithmeticSubalgebra) (k n : ℕ) :
    ((finiteAbscissaRotatedDeriv^[k]) f).1 n =
      (Complex.I * (Real.log n : ℂ)) ^ k * f.1 n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', finiteAbscissaRotatedDeriv_apply, ih, pow_succ]
      ring

/-- Rotation produces an analytic representative above a sufficiently high horizontal line. -/
theorem finiteAbscissa_rotatedLSeries_eventuallyAnalytic
    (f : finiteAbscissaArithmeticSubalgebra) :
    ∃ H : ℝ, AnalyticOnNhd ℂ
      (fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) (upperTail H) := by
  obtain ⟨H, hH⟩ := finiteAbscissaArithmetic_abscissa_le f
  refine ⟨H, (LSeries_analyticOnNhd (fun n => f.1 n)).comp
    (analyticOnNhd_const.mul analyticOnNhd_id) ?_⟩
  intro z hz
  change LSeries.abscissaOfAbsConv (fun n => f.1 n) <
    (((-Complex.I * z).re : ℝ) : EReal)
  have hre : (-Complex.I * z).re = z.im := by simp [Complex.mul_re]
  rw [hre]
  exact lt_of_le_of_lt hH (EReal.coe_lt_coe_iff.mpr (by simpa [upperTail] using hz))

/-- Constant complex germs as a ring homomorphism. -/
def complexToUpperEndGerm : ℂ →+* Germ upperEndFilter ℂ where
  toFun c := (c : Germ upperEndFilter ℂ)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The canonical complex-algebra structure on upper-end germs. -/
noncomputable instance upperEndGermAlgebra : Algebra ℂ (Germ upperEndFilter ℂ) :=
  complexToUpperEndGerm.toAlgebra

/-- Faithful rotated L-series realization for every finite absolute-convergence abscissa. -/
noncomputable def finiteAbscissaLSeriesToUpperEndGerm :
    finiteAbscissaArithmeticSubalgebra →ₐ[ℂ] Germ upperEndFilter ℂ where
  toFun f := Germ.coeRingHom upperEndFilter
    (fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z))
  map_zero' := by
    change Germ.coeRingHom upperEndFilter
      (fun z : ℂ => LSeries (0 : ℕ → ℂ) (-Complex.I * z)) = 0
    simpa only [LSeries_zero, Pi.zero_apply] using
      (Germ.coeRingHom upperEndFilter).map_zero
  map_one' := by
    change Germ.coeRingHom upperEndFilter
      (fun z : ℂ => LSeries (fun n => (1 : ArithmeticFunction ℂ) n) (-Complex.I * z)) = 1
    have hdelta : (fun n => (1 : ArithmeticFunction ℂ) n) = LSeries.delta := by
      funext n
      exact ArithmeticFunction.one_apply
    rw [hdelta, LSeries_delta]
    exact (Germ.coeRingHom upperEndFilter).map_one
  map_add' := by
    intro f g
    obtain ⟨H, hH⟩ := f.2
    obtain ⟨K, hK⟩ := g.2
    change (↑(fun z : ℂ =>
        LSeries (fun n => (f + g : finiteAbscissaArithmeticSubalgebra).1 n)
          (-Complex.I * z)) : Germ upperEndFilter ℂ) =
      (↑(fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) :
          Germ upperEndFilter ℂ) +
        (↑(fun z : ℂ => LSeries (fun n => g.1 n) (-Complex.I * z)) :
          Germ upperEndFilter ℂ)
    rw [← Germ.coe_add, Germ.coe_eq]
    change ∀ᶠ z in upperEndFilter,
      LSeries (fun n => (f + g : finiteAbscissaArithmeticSubalgebra).1 n)
          (-Complex.I * z) =
        LSeries (fun n => f.1 n) (-Complex.I * z) +
          LSeries (fun n => g.1 n) (-Complex.I * z)
    rw [upperEndFilter_basis.eventually_iff]
    refine ⟨max H K + 1, trivial, fun z hz => ?_⟩
    have hz' : max H K + 1 < z.im := by simpa [upperTail] using hz
    have hmax : max H K < z.im := (lt_add_one (max H K)).trans hz'
    apply LSeries_add
    · exact (LSeriesSummable_iff_of_re_eq_re (by simp [Complex.mul_re])).mpr
        (hH z.im (lt_of_le_of_lt (le_max_left H K) hmax))
    · exact (LSeriesSummable_iff_of_re_eq_re (by simp [Complex.mul_re])).mpr
        (hK z.im (lt_of_le_of_lt (le_max_right H K) hmax))
  map_mul' := by
    intro f g
    obtain ⟨H, hH⟩ := f.2
    obtain ⟨K, hK⟩ := g.2
    change (↑(fun z : ℂ =>
        LSeries (fun n => (f * g : finiteAbscissaArithmeticSubalgebra).1 n)
          (-Complex.I * z)) : Germ upperEndFilter ℂ) =
      (↑(fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) :
          Germ upperEndFilter ℂ) *
        (↑(fun z : ℂ => LSeries (fun n => g.1 n) (-Complex.I * z)) :
          Germ upperEndFilter ℂ)
    rw [← Germ.coe_mul, Germ.coe_eq]
    change ∀ᶠ z in upperEndFilter,
      LSeries (fun n => (f * g : finiteAbscissaArithmeticSubalgebra).1 n)
          (-Complex.I * z) =
        LSeries (fun n => f.1 n) (-Complex.I * z) *
          LSeries (fun n => g.1 n) (-Complex.I * z)
    rw [upperEndFilter_basis.eventually_iff]
    refine ⟨max H K + 1, trivial, fun z hz => ?_⟩
    have hz' : max H K + 1 < z.im := by simpa [upperTail] using hz
    have hmax : max H K < z.im := (lt_add_one (max H K)).trans hz'
    apply ArithmeticFunction.LSeries_mul'
    · exact (LSeriesSummable_iff_of_re_eq_re (by simp [Complex.mul_re])).mpr
        (hH z.im (lt_of_le_of_lt (le_max_left H K) hmax))
    · exact (LSeriesSummable_iff_of_re_eq_re (by simp [Complex.mul_re])).mpr
        (hK z.im (lt_of_le_of_lt (le_max_right H K) hmax))
  commutes' := by
    intro c
    change Germ.coeRingHom upperEndFilter
        (fun z : ℂ => LSeries
          (fun n => (algebraMap ℂ (ArithmeticFunction ℂ) c) n) (-Complex.I * z)) =
      algebraMap ℂ (Germ upperEndFilter ℂ) c
    have hcoeff : (fun n => (algebraMap ℂ (ArithmeticFunction ℂ) c) n) =
        c • LSeries.delta := by
      funext n
      simp [Algebra.algebraMap_eq_smul_one, ArithmeticFunction.smul_map,
        ArithmeticFunction.one_apply, LSeries.delta]
    rw [hcoeff]
    change (↑(fun z : ℂ => LSeries (c • LSeries.delta) (-Complex.I * z)) :
      Germ upperEndFilter ℂ) = algebraMap ℂ (Germ upperEndFilter ℂ) c
    have hfun : (fun z : ℂ => LSeries (c • LSeries.delta) (-Complex.I * z)) =
        fun _ => c := by
      funext z
      rw [LSeries_smul, LSeries_delta]
      simp
    rw [hfun]
    rfl

/-- Equality of upper-end L-series germs determines every Dirichlet coefficient. -/
theorem finiteAbscissaLSeriesToUpperEndGerm_injective :
    Function.Injective finiteAbscissaLSeriesToUpperEndGerm := by
  intro f g hfg
  change (↑(fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) :
      Germ upperEndFilter ℂ) =
    (↑(fun z : ℂ => LSeries (fun n => g.1 n) (-Complex.I * z)) :
      Germ upperEndFilter ℂ) at hfg
  rw [Germ.coe_eq] at hfg
  change ∀ᶠ z in upperEndFilter,
    LSeries (fun n => f.1 n) (-Complex.I * z) =
      LSeries (fun n => g.1 n) (-Complex.I * z) at hfg
  rw [upperEndFilter_basis.eventually_iff] at hfg
  obtain ⟨H0, htrivial, hL⟩ := hfg
  have hevent : (fun x : ℝ => LSeries (fun n => f.1 n) (x : ℂ)) =ᶠ[atTop]
      (fun x : ℝ => LSeries (fun n => g.1 n) (x : ℂ)) := by
    filter_upwards [eventually_gt_atTop H0] with x hx
    have hz := hL (show Complex.I * (x : ℂ) ∈ upperTail H0 by
      simpa [upperTail, Complex.mul_im] using hx)
    have hrot : -Complex.I * (Complex.I * (x : ℂ)) = (x : ℂ) := by
      calc
        -Complex.I * (Complex.I * (x : ℂ)) =
            (-Complex.I * Complex.I) * (x : ℂ) := (mul_assoc _ _ _).symm
        _ = (x : ℂ) := by rw [neg_mul, Complex.I_mul_I]; ring
    simpa only [hrot] using hz
  obtain ⟨Hf, hHf⟩ := finiteAbscissaArithmetic_abscissa_le f
  obtain ⟨Hg, hHg⟩ := finiteAbscissaArithmetic_abscissa_le g
  apply Subtype.ext
  apply ArithmeticFunction.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero]
  · exact LSeries.eq_of_LSeries_eventually_eq
      (hHf.trans_lt (EReal.coe_lt_top Hf))
      (hHg.trans_lt (EReal.coe_lt_top Hg)) hevent hn

/-- Dirichlet-variable translation becomes upper-end translation by `I a` after the rotation
`s = -I z`. -/
theorem finiteAbscissaLSeriesToUpperEndGerm_dirichletShift
    (a : ℂ) (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaLSeriesToUpperEndGerm (finiteAbscissaDirichletShift a f) =
      upperEndTranslateGerm (Complex.I * a)
        (finiteAbscissaLSeriesToUpperEndGerm f) := by
  change (↑(fun z : ℂ =>
      LSeries (fun n => dirichletShift a f.1 n) (-Complex.I * z)) :
        Germ upperEndFilter ℂ) =
    upperEndTranslateGerm (Complex.I * a)
      (↑(fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) :
        Germ upperEndFilter ℂ)
  rw [upperEndTranslateGerm_coe, Germ.coe_eq]
  exact Filter.Eventually.of_forall fun z => by
    change LSeries (fun n => dirichletShift a f.1 n) (-Complex.I * z) =
      LSeries (fun n => f.1 n) (-Complex.I * (z + Complex.I * a))
    rw [LSeries_dirichletShift]
    congr 1
    have hI : -Complex.I * Complex.I = (1 : ℂ) := by
      rw [neg_mul, Complex.I_mul_I]
      norm_num
    calc
      -Complex.I * z + a =
          -Complex.I * z + (-Complex.I * Complex.I) * a := by simp [hI]
      _ = -Complex.I * (z + Complex.I * a) := by ring

/-- Differentiating a finite-abscissa upper-end L-series germ is exactly the germ of its rotated
logarithmic coefficient derivative. -/
theorem upperEndGermDeriv_finiteAbscissaLSeries
    (f : finiteAbscissaArithmeticSubalgebra) :
    upperEndGermDeriv (finiteAbscissaLSeriesToUpperEndGerm f) =
      finiteAbscissaLSeriesToUpperEndGerm (finiteAbscissaRotatedDeriv f) := by
  change upperEndGermDeriv
      (↑(fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z)) :
        Germ upperEndFilter ℂ) =
    (↑(fun z : ℂ =>
      LSeries (fun n => (finiteAbscissaRotatedDeriv f).1 n) (-Complex.I * z)) :
      Germ upperEndFilter ℂ)
  rw [upperEndGermDeriv_coe, Germ.coe_eq]
  change ∀ᶠ z in upperEndFilter,
    deriv (fun w : ℂ => LSeries (fun n => f.1 n) (-Complex.I * w)) z =
      LSeries (fun n => (finiteAbscissaRotatedDeriv f).1 n) (-Complex.I * z)
  rw [upperEndFilter_basis.eventually_iff]
  obtain ⟨H, hH⟩ := finiteAbscissaArithmetic_abscissa_le f
  refine ⟨H + 1, trivial, fun z hz => ?_⟩
  have hlt : LSeries.abscissaOfAbsConv (fun n => f.1 n) <
      (((-Complex.I * z).re : ℝ) : EReal) := by
    have hre : (-Complex.I * z).re = z.im := by simp [Complex.mul_re]
    rw [hre]
    exact lt_of_le_of_lt hH (EReal.coe_lt_coe_iff.mpr
      ((lt_add_one H).trans (by simpa [upperTail] using hz)))
  have houter := LSeries_hasDerivAt
    (s := -Complex.I * z) (f := fun n => f.1 n)
    (by simpa only using hlt)
  have hinner : HasDerivAt (fun w : ℂ => -Complex.I * w) (-Complex.I) z := by
    simpa only [mul_one] using (hasDerivAt_id z).const_mul (-Complex.I)
  have hcomp := houter.comp z hinner
  have hderiv :
      deriv (fun w : ℂ => LSeries (fun n => f.1 n) (-Complex.I * w)) z =
        (-LSeries (LSeries.logMul (fun n => f.1 n)) (-Complex.I * z)) *
          (-Complex.I) := by
    simpa only [Function.comp_apply] using hcomp.deriv
  rw [hderiv]
  have hcoeff : (fun n => (finiteAbscissaRotatedDeriv f).1 n) =
      Complex.I • (fun n => logWeight f.1 n) := by
    funext n
    simp only [finiteAbscissaRotatedDeriv_apply, Pi.smul_apply, smul_eq_mul,
      logWeight_apply]
    ring
  rw [hcoeff, LSeries_smul, ← lSeries_logMul_eq_logWeight]
  ring

/-- The L-series realization intertwines every finite iterate of the rotated coefficient
derivation with the corresponding analytic derivative iterate. -/
theorem finiteAbscissaLSeriesToUpperEndGerm_iteratedDeriv
    (f : finiteAbscissaArithmeticSubalgebra) (k : ℕ) :
    finiteAbscissaLSeriesToUpperEndGerm ((finiteAbscissaRotatedDeriv^[k]) f) =
      (upperEndGermDeriv^[k]) (finiteAbscissaLSeriesToUpperEndGerm f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ← upperEndGermDeriv_finiteAbscissaLSeries, ih]

end

end GaloisForLFunctions.HTGeometry
