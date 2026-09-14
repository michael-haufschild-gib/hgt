import GaloisForLFunctions.RHTower.ArithmeticDirichletTwistedBoundary
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Units and scalar evaluations of the finite-abscissa arithmetic algebra

An arithmetic coefficient family with some finite absolute-convergence abscissa
is a unit in that same algebra exactly when its coefficient at one is nonzero.
In particular its canonical formal Dirichlet inverse still has finite abscissa.
Every complex algebra homomorphism on the whole algebra is evaluation at one;
no continuity or shift-invariance hypothesis is needed.

Normalize the first coefficient to one. The absolute-coefficient tail has an
L-series tending to zero as the real argument tends to infinity. A sufficiently
large coefficient shift therefore makes its total absolute mass at most one.
Strong induction in the proper-divisor inverse recursion bounds every inverse
coefficient by one. Shifting back and undoing the scalar normalization gives the
unit criterion. Subtracting the proposed scalar value then proves the evaluation
classification.

The inverse need not preserve each original convergence point. This is a result
about the union of all finite-abscissa domains, not about evaluation on a fixed
half-plane or analytic continuation with its individual domains retained. It
excludes the proposed scalar-point construction on that whole algebra; it does
not locate zeta zeros or supply a new RH route.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.FiniteAbscissaUnits
noncomputable section
abbrev A := ArithmeticFunction ℂ

private theorem norm_inverse_le_one (f : A) (hf : f 1 = 1)
    (hs : Summable (fun n => if n = 1 then (0 : ℝ) else ‖f n‖))
    (ht : (∑' n, if n = 1 then (0 : ℝ) else ‖f n‖) ≤ 1) :
    ∃ g : A, f * g = 1 ∧ ∀ n, ‖g n‖ ≤ 1 := by
  classical
  let hi : Invertible (f 1) := ⟨1, by rw [hf, one_mul], by rw [hf, one_mul]⟩
  refine ⟨ArithmeticFunction.dirichletInverse f hi,
    ArithmeticFunction.self_mul_dirichletInverse f hi, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n; simp only [ArithmeticFunction.map_zero, norm_zero, zero_le_one]
    by_cases hn1 : n = 1
    · subst n
      change ‖ArithmeticFunction.dirichletInverseFun f hi 1‖ ≤ 1
      rw [ArithmeticFunction.dirichletInverseFun_apply_one]
      exact (norm_one : ‖(1 : ℂ)‖ = 1).le
    change ‖ArithmeticFunction.dirichletInverseFun f hi n‖ ≤ 1
    rw [ArithmeticFunction.dirichletInverseFun_apply_ne f hi hn0 hn1]
    change ‖-(1 : ℂ) * ∑ d ∈ n.properDivisors,
      f (n / d) * ArithmeticFunction.dirichletInverseFun f hi d‖ ≤ 1
    rw [neg_one_mul, norm_neg]
    calc
      _ ≤ ∑ d ∈ n.properDivisors,
          ‖f (n / d) * ArithmeticFunction.dirichletInverseFun f hi d‖ :=
        norm_sum_le _ _
      _ ≤ ∑ d ∈ n.properDivisors, ‖f (n / d)‖ := by
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (ih d (Nat.mem_properDivisors.mp hd).2)
      _ = ∑ d ∈ n.properDivisors,
          (if n / d = 1 then (0 : ℝ) else ‖f (n / d)‖) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [if_neg (Nat.ne_of_gt (Nat.one_lt_div_of_mem_properDivisors hd))]
      _ = ∑ q ∈ n.properDivisors.image (fun d => n / d),
          (if q = 1 then (0 : ℝ) else ‖f q‖) := by
        symm
        apply Finset.sum_image
        intro a ha b hb hab
        have ha' := Nat.div_div_self (Nat.mem_properDivisors.mp ha).1 hn0
        have hb' := Nat.div_div_self (Nat.mem_properDivisors.mp hb).1 hn0
        exact ha'.symm.trans ((congrArg (fun d => n / d) hab).trans hb')
      _ ≤ ∑' q, if q = 1 then (0 : ℝ) else ‖f q‖ :=
        hs.sum_le_tsum _ (fun q _ => by split_ifs; exact le_rfl; exact norm_nonneg _)
      _ ≤ 1 := ht

private def normCoefficients (f : A) : A :=
  ⟨fun n => (‖f n‖ : ℂ), by simp only [ArithmeticFunction.map_zero, norm_zero, Complex.ofReal_zero]⟩

private theorem normCoefficients_apply (f : A) (n : ℕ) :
    normCoefficients f n = (‖f n‖ : ℂ) := rfl

private theorem normCoefficients_mem (f : finiteAbscissaArithmeticSubalgebra) :
    normCoefficients f.1 ∈ finiteAbscissaArithmeticSubalgebra := by
  obtain ⟨H, hH⟩ := f.2
  refine ⟨H, fun y hy => ?_⟩
  apply (hH y hy).norm.of_norm_bounded
  intro n
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp only [normCoefficients_apply, Complex.norm_real, norm_norm, le_refl]

private theorem term_normCoefficients (f : A) (b : ℝ) (n : ℕ) :
    LSeries.term (fun n => normCoefficients f n) (b : ℂ) n =
      (‖dirichletShift (b : ℂ) f n‖ : ℂ) := by
  by_cases hn : n = 0
  · subst n
    rw [LSeries.term_zero, ArithmeticFunction.map_zero, norm_zero, Complex.ofReal_zero]
  rw [LSeries.term_of_ne_zero hn, normCoefficients_apply,
    ArithmeticTwistedBoundary.twist_apply, norm_mul,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.neg_re,
    Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n)]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n),
    ← Complex.ofReal_div]
  congr 1
  exact div_eq_inv_mul _ _

private theorem exists_summable_small_shift (f : finiteAbscissaArithmeticSubalgebra)
    (hf : f.1 1 = 0) :
    ∃ b : ℝ, Summable (fun n => ‖dirichletShift (b : ℂ) f.1 n‖) ∧
      (∑' n, ‖dirichletShift (b : ℂ) f.1 n‖) ≤ 1 := by
  obtain ⟨H, hH⟩ := normCoefficients_mem f
  have hc := (hH (H + 1) (lt_add_one H)).abscissaOfAbsConv_le
  have habs : LSeries.abscissaOfAbsConv (fun n => normCoefficients f.1 n) < ⊤ :=
    hc.trans_lt (EReal.coe_lt_top _)
  have hlim := (Complex.continuous_re.tendsto _).comp (LSeries.tendsto_atTop habs)
  simp only [normCoefficients_apply, hf, norm_zero, Complex.ofReal_zero,
    Complex.zero_re] at hlim
  have hsmall := hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one))
  obtain ⟨b, hb, hsmall⟩ := ((eventually_gt_atTop H).and hsmall).exists
  have hs : Summable (fun n => ‖dirichletShift (b : ℂ) f.1 n‖) := by
    apply (hH b hb).norm.congr
    intro n
    rw [term_normCoefficients, Complex.norm_real, norm_norm]
  refine ⟨b, hs, ?_⟩
  calc
    _ = (LSeries (fun n => normCoefficients f.1 n) (b : ℂ)).re := by
      rw [LSeries, Complex.re_tsum (hH b hb)]
      apply tsum_congr
      intro n
      rw [term_normCoefficients, Complex.ofReal_re]
    _ ≤ 1 := hsmall.le

private theorem isUnit_of_one (f : finiteAbscissaArithmeticSubalgebra) (hf : f.1 1 = 1) :
    IsUnit f := by
  let h : finiteAbscissaArithmeticSubalgebra := f - 1
  have hh : h.1 1 = 0 := by
    change f.1 1 - (1 : A) 1 = 0
    rw [hf, ArithmeticFunction.one_one, sub_self]
  obtain ⟨b, hs, ht⟩ := exists_summable_small_shift h hh
  let w := finiteAbscissaDirichletShift (b : ℂ) f
  have hw : w.1 1 = 1 := by
    change dirichletShift (b : ℂ) f.1 1 = 1
    rw [ArithmeticTwistedBoundary.twist_one_coefficient, hf]
  have hshift : dirichletShift (b : ℂ) h.1 = w.1 - 1 := by
    change (ArithmeticTwistedBoundary.twistHom (b : ℂ)) (f.1 - 1) =
      (ArithmeticTwistedBoundary.twistHom (b : ℂ)) f.1 - 1
    exact (map_sub (ArithmeticTwistedBoundary.twistHom (b : ℂ)) f.1 1).trans
      (congrArg (fun a : A => w.1 - a) (map_one (ArithmeticTwistedBoundary.twistHom (b : ℂ))))
  have heq : (fun n => if n = 1 then (0 : ℝ) else ‖w.1 n‖) =
      (fun n => ‖dirichletShift (b : ℂ) h.1 n‖) := by
    funext n
    have he : dirichletShift (b : ℂ) h.1 n = w.1 n - (1 : A) n :=
      congrArg (fun a : A => a n) hshift
    by_cases hn : n = 1
    · rw [if_pos hn, he, hn, hw, ArithmeticFunction.one_one, sub_self, norm_zero]
    · rw [if_neg hn, he, ArithmeticFunction.one_apply_ne hn, sub_zero]
  obtain ⟨g, hfg, hbound⟩ := norm_inverse_le_one w.1 hw
    (by rw [heq]; exact hs) (by rw [heq]; exact ht)
  have hg : g ∈ finiteAbscissaArithmeticSubalgebra := by
    refine ⟨1, fun y hy => ?_⟩
    exact LSeriesSummable_of_bounded_of_one_lt_real (fun n _ => hbound n) hy
  let v := finiteAbscissaDirichletShift (-(b : ℂ)) ⟨g, hg⟩
  have hfv : f * v = 1 := by
    apply Subtype.ext
    let e := ArithmeticTwistedBoundary.twistEquiv (-(b : ℂ))
    have he : e w.1 * e g = 1 :=
      (e.map_mul w.1 g).symm.trans ((congrArg e hfg).trans e.map_one)
    change dirichletShift (-(b : ℂ)) (dirichletShift (b : ℂ) f.1) *
      dirichletShift (-(b : ℂ)) g = 1 at he
    have hi := ArithmeticTwistedBoundary.twist_neg_twist (b : ℂ) f.1
    exact (congrArg (fun a : A => a * dirichletShift (-(b : ℂ)) g) hi).symm.trans he
  exact ⟨⟨f, v, hfv, by rw [mul_comm, hfv]⟩, rfl⟩

/-- A finite-abscissa source is a unit precisely when its first coefficient is nonzero. -/
theorem isUnit_iff (f : finiteAbscissaArithmeticSubalgebra) :
    IsUnit f ↔ f.1 1 ≠ 0 := by
  constructor
  · intro hf
    have h := hf.map (arithmeticFunctionAugmentation.comp finiteAbscissaArithmeticSubalgebra.val)
    exact isUnit_iff_ne_zero.mp h
  · intro hf
    let u := algebraMap ℂ finiteAbscissaArithmeticSubalgebra (f.1 1)⁻¹ * f
    have hu : u.1 1 = 1 := by
      change ((algebraMap ℂ A (f.1 1)⁻¹) * f.1) 1 = 1
      rw [ArithmeticFunction.mul_apply_one, ArithmeticFunction.algebraMap_apply_one]
      exact inv_mul_cancel₀ hf
    exact isUnit_of_mul_isUnit_right (isUnit_of_one u hu)

/-- The canonical formal Dirichlet inverse remains in the finite-abscissa source algebra. -/
theorem dirichletInverse_mem (f : finiteAbscissaArithmeticSubalgebra)
    (hf : Invertible (f.1 1)) :
    ArithmeticFunction.dirichletInverse f.1 hf ∈ finiteAbscissaArithmeticSubalgebra := by
  letI := hf
  obtain ⟨u, hu⟩ := (isUnit_iff f).mpr
    (isUnit_iff_ne_zero.mp (isUnit_of_invertible (f.1 1)))
  let g : finiteAbscissaArithmeticSubalgebra := ↑(u⁻¹)
  have hfg : f.1 * g.1 = 1 :=
    congrArg (fun a : finiteAbscissaArithmeticSubalgebra => a.1) (u.mul_inv_of_eq hu)
  have heq : ArithmeticFunction.dirichletInverse f.1 hf = g.1 := by
    exact left_inv_eq_right_inv (ArithmeticFunction.dirichletInverse_mul_self f.1 hf) hfg
  rw [heq]
  exact g.2

/-- Every complex algebra map on the whole finite-abscissa algebra reads coefficient one. -/
theorem algHom_apply (φ : finiteAbscissaArithmeticSubalgebra →ₐ[ℂ] ℂ)
    (f : finiteAbscissaArithmeticSubalgebra) : φ f = f.1 1 := by
  by_contra h
  have hu : IsUnit (f - algebraMap ℂ finiteAbscissaArithmeticSubalgebra (φ f)) := by
    apply (isUnit_iff _).mpr
    change f.1 1 - (algebraMap ℂ A (φ f)) 1 ≠ 0
    rw [ArithmeticFunction.algebraMap_apply_one]
    exact sub_ne_zero.mpr fun he => h he.symm
  have he : φ (f - algebraMap ℂ finiteAbscissaArithmeticSubalgebra (φ f)) = 0 := by
    rw [_root_.map_sub φ f (algebraMap ℂ finiteAbscissaArithmeticSubalgebra (φ f)),
      φ.commutes]
    exact sub_self (φ f)
  exact isUnit_iff_ne_zero.mp (hu.map φ) he

/-- No shift-invariance or continuity assumption is needed for this scalar classification. -/
theorem algHom_eq_augmentation (φ : finiteAbscissaArithmeticSubalgebra →ₐ[ℂ] ℂ) :
    φ = arithmeticFunctionAugmentation.comp finiteAbscissaArithmeticSubalgebra.val := by
  exact AlgHom.ext (algHom_apply φ)

end
end RHTower.FiniteAbscissaUnits
