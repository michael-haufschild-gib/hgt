import GaloisForLFunctions.RHTower.ArithmeticDilationTraceClass
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Exact zero set of the arithmetic dilation Fredholm product

Absolute summability rules out a spurious zero caused by infinitely many nonzero factors.  Hence
the bare determinant `∏ n, (1 + z g n)` vanishes exactly when one of its linear factors vanishes.
For the constrained-prolate arithmetic spectrum, whose entries are all strictly positive, this
identifies the complete zero set with the advertised negative reciprocal spectrum.
-/

noncomputable section

open Filter Set

namespace RHTower

/-- An absolutely summable bare Fredholm product vanishes exactly when one of its factors does. -/
theorem arithmeticDiagonalFredholmDeterminant_eq_zero_iff
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖) (z : ℂ) :
    arithmeticDiagonalFredholmDeterminant g z = 0 ↔
      ∃ n : ℕ, 1 + z * g n = 0 := by
  rw [arithmeticDiagonalFredholmDeterminant]
  constructor
  · intro hzero
    by_contra hfactor
    simp only [not_exists] at hfactor
    have hsum : Summable fun n : ℕ => ‖z * g n‖ := by
      simpa [norm_mul] using hg.mul_left ‖z‖
    exact (tprod_one_add_ne_zero_of_summable hfactor hsum) hzero
  · rintro ⟨n, hn⟩
    exact tprod_of_exists_eq_zero ⟨n, hn⟩

/-- **Complete zero classification for the constrained-prolate arithmetic determinant.**
There are no zeros beyond the negative reciprocals of the explicit positive eigenvalues. -/
theorem constrainedProlateArithmeticFredholmDeterminant_eq_zero_iff (z : ℂ) :
    constrainedProlateArithmeticFredholmDeterminant z = 0 ↔
      ∃ n : ℕ, z =
        -(GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ)⁻¹ := by
  rw [constrainedProlateArithmeticFredholmDeterminant,
    arithmeticDiagonalFredholmDeterminant_eq_zero_iff _
      summable_norm_constrainedProlateArithmeticEigenvalue_complex]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hk : (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt
        (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_pos n)
    apply (mul_right_cancel₀ hk)
    field_simp
    linear_combination hn
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hk : (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt
        (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_pos n)
    field_simp
    ring

/-! ## Strict decrease of the explicit arithmetic spectrum -/

/-- Continuous profile underlying the arithmetic eigenvalue sequence. -/
def arithmeticEigenvalueProfile (x : ℝ) : ℝ :=
  Real.log x / x * Real.arcsin (1 / x)

/-- Elementary tangent envelope used to control the profile derivative. -/
theorem sqrt_sub_one_mul_arcsin_one_div_le_one {x : ℝ} (hx : 1 < x) :
    Real.sqrt (x ^ (2 : ℕ) - 1) * Real.arcsin (1 / x) ≤ 1 := by
  have hx0 : 0 < x := one_pos.trans hx
  have ht0 : 0 ≤ 1 / x := by positivity
  have ht1 : 1 / x < 1 := (div_lt_one hx0).mpr hx
  have htan := Real.le_tan (Real.arcsin_nonneg.mpr ht0)
    (Real.arcsin_lt_pi_div_two.mpr ht1)
  rw [Real.tan_arcsin] at htan
  have harg : 0 < x ^ (2 : ℕ) - 1 := by nlinarith
  have hspos : 0 < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.2 harg
  have hsquare : Real.sqrt (1 - (1 / x) ^ (2 : ℕ)) = Real.sqrt (x ^ (2 : ℕ) - 1) / x := by
    rw [show 1 - (1 / x) ^ (2 : ℕ) = (x ^ (2 : ℕ) - 1) / x ^ (2 : ℕ) by field_simp]
    rw [Real.sqrt_div (le_of_lt harg), Real.sqrt_sq_eq_abs, abs_of_pos hx0]
  rw [hsquare] at htan
  have hbound : Real.arcsin (1 / x) ≤ 1 / Real.sqrt (x ^ (2 : ℕ) - 1) := by
    convert htan using 1
    field_simp
  simpa [mul_comm] using (le_div_iff₀ hspos).mp hbound

theorem hasDerivAt_arithmeticEigenvalueProfile {x : ℝ} (hx : 1 < x) :
    HasDerivAt arithmeticEigenvalueProfile
      (Real.arcsin (1 / x) * (1 - Real.log x) / x ^ (2 : ℕ) -
        Real.log x / (x ^ (2 : ℕ) * Real.sqrt (x ^ (2 : ℕ) - 1))) x := by
  have hx0 : x ≠ 0 := ne_of_gt (one_pos.trans hx)
  have htneg : 1 / x ≠ -1 := by
    have : 0 < 1 / x := by positivity
    linarith
  have htone : 1 / x ≠ 1 := ne_of_lt ((div_lt_one (one_pos.trans hx)).mpr hx)
  have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ (2 : ℕ)) x := by
    simpa [div_eq_mul_inv] using hasDerivAt_inv hx0
  have harc : HasDerivAt (fun y : ℝ => Real.arcsin (1 / y))
      ((1 / Real.sqrt (1 - (1 / x) ^ (2 : ℕ))) * (-1 / x ^ (2 : ℕ))) x :=
    (Real.hasDerivAt_arcsin htneg htone).comp x hinv
  have hmain := ((Real.hasDerivAt_log hx0).div (hasDerivAt_id x) hx0).mul harc
  have hraw : HasDerivAt arithmeticEigenvalueProfile
      (((x⁻¹ * x - Real.log x) / x ^ (2 : ℕ)) * Real.arcsin (1 / x) +
        (Real.log x / x) * ((1 / Real.sqrt (1 - (1 / x) ^ (2 : ℕ))) * (-1 / x ^ (2 : ℕ)))) x := by
    have hfun := hmain.congr_of_eventuallyEq (f₁ := arithmeticEigenvalueProfile)
      (Filter.Eventually.of_forall fun _ => rfl)
    simpa using hfun
  have harg : 0 < x ^ (2 : ℕ) - 1 := by nlinarith
  have hsquare : Real.sqrt (1 - (1 / x) ^ (2 : ℕ)) = Real.sqrt (x ^ (2 : ℕ) - 1) / x := by
    rw [show 1 - (1 / x) ^ (2 : ℕ) = (x ^ (2 : ℕ) - 1) / x ^ (2 : ℕ) by field_simp]
    rw [Real.sqrt_div (le_of_lt harg), Real.sqrt_sq_eq_abs,
      abs_of_pos (one_pos.trans hx)]
  convert hraw using 1
  rw [hsquare]
  field_simp
  ring

theorem arithmeticEigenvalueProfile_deriv_neg {x : ℝ} (hx : 2 ≤ x) :
    Real.arcsin (1 / x) * (1 - Real.log x) / x ^ (2 : ℕ) -
        Real.log x / (x ^ (2 : ℕ) * Real.sqrt (x ^ (2 : ℕ) - 1)) < 0 := by
  have hx1 : 1 < x := lt_of_lt_of_le one_lt_two hx
  have hx0 : 0 < x := one_pos.trans hx1
  have harg : 0 < x ^ (2 : ℕ) - 1 := by nlinarith
  have hspos : 0 < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.2 harg
  have hloghalf : (1 / 2 : ℝ) < Real.log x := by
    have htwo : (1 / 2 : ℝ) < Real.log 2 :=
      (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
    exact htwo.trans_le (Real.log_le_log zero_lt_two hx)
  have hprod : Real.sqrt (x ^ (2 : ℕ) - 1) * Real.arcsin (1 / x) ≤ 1 :=
    sqrt_sub_one_mul_arcsin_one_div_le_one hx1
  have hnum : Real.sqrt (x ^ (2 : ℕ) - 1) * Real.arcsin (1 / x) *
        (1 - Real.log x) - Real.log x < 0 := by
    by_cases hsign : 0 ≤ 1 - Real.log x
    · have hmul := mul_le_mul_of_nonneg_right hprod hsign
      linarith
    · have harc0 : 0 ≤ Real.arcsin (1 / x) := Real.arcsin_nonneg.mpr (by positivity)
      have hpa : 0 ≤ Real.sqrt (x ^ (2 : ℕ) - 1) * Real.arcsin (1 / x) :=
        mul_nonneg (Real.sqrt_nonneg _) harc0
      have hmul : Real.sqrt (x ^ (2 : ℕ) - 1) * Real.arcsin (1 / x) *
          (1 - Real.log x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpa (le_of_not_ge hsign)
      linarith
  rw [show Real.arcsin (1 / x) * (1 - Real.log x) / x ^ (2 : ℕ) -
        Real.log x / (x ^ (2 : ℕ) * Real.sqrt (x ^ (2 : ℕ) - 1)) =
      (Real.sqrt (x ^ (2 : ℕ) - 1) * Real.arcsin (1 / x) * (1 - Real.log x) -
        Real.log x) / (x ^ (2 : ℕ) * Real.sqrt (x ^ (2 : ℕ) - 1)) by field_simp]
  exact div_neg_of_neg_of_pos hnum (mul_pos (sq_pos_of_pos hx0) hspos)

/-- The real profile `log x · arcsin(1/x) / x` is strictly decreasing on `[2,∞)`. -/
theorem strictAntiOn_arithmeticEigenvalueProfile :
    StrictAntiOn arithmeticEigenvalueProfile (Ici 2) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 2)
  · intro x hx
    have hx2 : 2 ≤ x := hx
    exact (hasDerivAt_arithmeticEigenvalueProfile (by linarith)).continuousAt.continuousWithinAt
  · intro x hx
    have hx2 : 2 ≤ x := by
      rw [interior_Ici] at hx
      exact hx.le
    rw [(hasDerivAt_arithmeticEigenvalueProfile
      (lt_of_lt_of_le one_lt_two hx2)).deriv]
    exact arithmeticEigenvalueProfile_deriv_neg hx2

/-- The explicit constrained-prolate arithmetic eigenvalues are pairwise distinct, in their
natural strict decreasing order. -/
theorem constrainedProlateArithmeticEigenvalue_strictAnti :
    StrictAnti GaloisForLFunctions.constrainedProlateArithmeticEigenvalue := by
  intro n m hnm
  rw [GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_eq,
    GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_eq]
  dsimp only
  apply mul_lt_mul_of_pos_left
  · exact strictAntiOn_arithmeticEigenvalueProfile
      (by change (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ); exact_mod_cast Nat.le_add_left 2 n)
      (by change (2 : ℝ) ≤ ((m + 2 : ℕ) : ℝ); exact_mod_cast Nat.le_add_left 2 m)
      (by exact_mod_cast (Nat.add_lt_add_right hnm 2))
  · positivity

theorem constrainedProlateArithmeticEigenvalue_injective :
    Function.Injective GaloisForLFunctions.constrainedProlateArithmeticEigenvalue :=
  constrainedProlateArithmeticEigenvalue_strictAnti.injective

/-! ## Entire product and exact simple zeros -/

/-- An absolutely summable bare Fredholm product is an entire function. -/
theorem arithmeticDiagonalFredholmDeterminant_differentiable
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖) :
    Differentiable ℂ (arithmeticDiagonalFredholmDeterminant g) := by
  let F : Finset ℕ → ℂ → ℂ := fun s z => ∏ n ∈ s, (1 + z * g n)
  have hlocal : TendstoLocallyUniformlyOn F
      (arithmeticDiagonalFredholmDeterminant g) atTop (Set.univ : Set ℂ) := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    simpa only [F] using
      (hasProdUniformlyOn_arithmeticDiagonalFredholmDeterminant g hg K hK).tendstoUniformlyOn
  have hdiff : ∀ᶠ s : Finset ℕ in atTop,
      DifferentiableOn ℂ (F s) (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall fun s => ?_
    intro z _
    simp only [F]
    fun_prop
  exact differentiableOn_univ.mp (hlocal.differentiableOn hdiff isOpen_univ)

/-- Product with the `n`-th linear factor removed. -/
def arithmeticDiagonalFredholmCofactor (g : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  arithmeticDiagonalFredholmDeterminant (fun m => if m = n then 0 else g m) z

theorem summable_norm_arithmeticDiagonalMask
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖) (n : ℕ) :
    Summable fun m => ‖if m = n then (0 : ℂ) else g m‖ := by
  exact hg.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => by
    by_cases h : m = n <;> simp [h])

theorem arithmeticDiagonalFredholmDeterminant_factor
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖) (n : ℕ) (z : ℂ) :
    arithmeticDiagonalFredholmDeterminant g z =
      (1 + z * g n) * arithmeticDiagonalFredholmCofactor g n z := by
  let f : ℕ → ℂ := fun m => 1 + z * g m
  let p : ℕ → ℂ := fun m => if m = n then f m else 1
  let q : ℕ → ℂ := fun m => if m = n then 1 else f m
  have hp : Multipliable p := by
    apply multipliable_of_ne_finset_one (s := {n})
    intro m hm
    simp only [Finset.mem_singleton] at hm
    simp [p, hm]
  have hmask := multipliable_arithmeticDiagonalFredholmDeterminant
    (fun m => if m = n then 0 else g m) (summable_norm_arithmeticDiagonalMask g hg n) z
  have hq : Multipliable q := by
    exact hmask.congr fun m => by
      by_cases h : m = n
      · simp [q, f, h]
      · simp [q, f, h]
  rw [arithmeticDiagonalFredholmDeterminant]
  calc
    tprod (fun m : ℕ => 1 + z * g m) = tprod (fun m : ℕ => p m * q m) := by
      apply tprod_congr
      intro m
      by_cases h : m = n <;> simp [p, q, f, h]
    _ = tprod p * tprod q := hp.tprod_mul hq
    _ = (1 + z * g n) * arithmeticDiagonalFredholmCofactor g n z := by
      congr 1
      · rw [show tprod p = p n from
          tprod_eq_mulSingle n fun m hm => by simp [hm]]
        simp [p, f]
      · rw [arithmeticDiagonalFredholmCofactor, arithmeticDiagonalFredholmDeterminant]
        apply tprod_congr
        intro m
        by_cases h : m = n <;> simp [f, h]

theorem arithmeticDiagonalFredholmCofactor_neg_inv_ne_zero
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖)
    (hinj : Function.Injective g) (n : ℕ) (hn : g n ≠ 0) :
    arithmeticDiagonalFredholmCofactor g n (-(g n)⁻¹) ≠ 0 := by
  intro hzero
  rw [arithmeticDiagonalFredholmCofactor,
    arithmeticDiagonalFredholmDeterminant_eq_zero_iff _
      (summable_norm_arithmeticDiagonalMask g hg n)] at hzero
  obtain ⟨m, hm⟩ := hzero
  by_cases hmn : m = n
  · subst m
    simp at hm
  · simp only [if_neg hmn] at hm
    have hgm : g m = g n := by
      apply (mul_left_cancel₀ hn)
      field_simp at hm ⊢
      linear_combination -hm
    exact hmn (hinj hgm)

theorem arithmeticDiagonalFredholmCofactor_differentiable
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖) (n : ℕ) :
    Differentiable ℂ (arithmeticDiagonalFredholmCofactor g n) := by
  exact arithmeticDiagonalFredholmDeterminant_differentiable _
    (summable_norm_arithmeticDiagonalMask g hg n)

theorem arithmeticDiagonalFredholmDeterminant_hasDerivAt_neg_inv
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖) (n : ℕ) (hn : g n ≠ 0) :
    HasDerivAt (arithmeticDiagonalFredholmDeterminant g)
      (g n * arithmeticDiagonalFredholmCofactor g n (-(g n)⁻¹)) (-(g n)⁻¹) := by
  let z0 : ℂ := -(g n)⁻¹
  have hlin : HasDerivAt (fun z : ℂ => 1 + z * g n) (g n) z0 := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id z0).mul_const (g n)).const_add 1
  have hq := (arithmeticDiagonalFredholmCofactor_differentiable g hg n z0).hasDerivAt
  have hprod := hlin.mul hq
  have hprod' : HasDerivAt
      (fun z => (1 + z * g n) * arithmeticDiagonalFredholmCofactor g n z)
      (g n * arithmeticDiagonalFredholmCofactor g n z0 +
        (1 + z0 * g n) * deriv (arithmeticDiagonalFredholmCofactor g n) z0) z0 := by
    exact hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  have heq : arithmeticDiagonalFredholmDeterminant g =
      fun z => (1 + z * g n) * arithmeticDiagonalFredholmCofactor g n z := by
    funext z
    exact arithmeticDiagonalFredholmDeterminant_factor g hg n z
  have hzfac : 1 + z0 * g n = 0 := by
    dsimp only [z0]
    field_simp
    ring
  rw [heq]
  exact hprod'.congr_deriv (by rw [hzfac, zero_mul, add_zero])

/-- The constrained-prolate arithmetic determinant is entire. -/
theorem constrainedProlateArithmeticFredholmDeterminant_differentiable :
    Differentiable ℂ constrainedProlateArithmeticFredholmDeterminant := by
  exact arithmeticDiagonalFredholmDeterminant_differentiable _
    summable_norm_constrainedProlateArithmeticEigenvalue_complex

/-- Every advertised reciprocal zero has nonzero complex derivative, hence analytic multiplicity
exactly one. -/
theorem constrainedProlateArithmeticFredholmDeterminant_deriv_neg_inv_ne_zero (n : ℕ) :
    deriv constrainedProlateArithmeticFredholmDeterminant
      (-(GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ)⁻¹) ≠ 0 := by
  let g : ℕ → ℂ := fun m =>
    (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue m : ℂ)
  have hginj : Function.Injective g := by
    intro i j hij
    dsimp only [g] at hij
    apply constrainedProlateArithmeticEigenvalue_injective
    exact_mod_cast hij
  have hn : g n ≠ 0 := by
    dsimp only [g]
    exact_mod_cast ne_of_gt
      (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_pos n)
  have hderiv := arithmeticDiagonalFredholmDeterminant_hasDerivAt_neg_inv
    g summable_norm_constrainedProlateArithmeticEigenvalue_complex n hn
  rw [show constrainedProlateArithmeticFredholmDeterminant =
      arithmeticDiagonalFredholmDeterminant g from rfl, hderiv.deriv]
  exact mul_ne_zero hn
    (arithmeticDiagonalFredholmCofactor_neg_inv_ne_zero g
      summable_norm_constrainedProlateArithmeticEigenvalue_complex hginj n hn)

/-- Each zero is indexed by a unique arithmetic eigenvalue. -/
theorem constrainedProlateArithmeticFredholmDeterminant_eq_zero_iff_existsUnique (z : ℂ) :
    constrainedProlateArithmeticFredholmDeterminant z = 0 ↔
      ∃! n : ℕ, z =
        -(GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ)⁻¹ := by
  rw [constrainedProlateArithmeticFredholmDeterminant_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, hn, ?_⟩
    intro m hm
    have hinv :
        (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue m : ℂ)⁻¹ =
          (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ)⁻¹ := by
      exact neg_injective (hm.symm.trans hn)
    have heig : GaloisForLFunctions.constrainedProlateArithmeticEigenvalue m =
        GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n := by
      exact_mod_cast inv_injective hinv
    exact constrainedProlateArithmeticEigenvalue_injective heig
  · rintro ⟨n, hn, _⟩
    exact ⟨n, hn⟩

/-- Complete simple-zero statement: the reciprocal spectral point is a zero and its derivative
does not vanish. -/
theorem constrainedProlateArithmeticFredholmDeterminant_simpleZero (n : ℕ) :
    constrainedProlateArithmeticFredholmDeterminant
        (-(GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ)⁻¹) = 0 ∧
      deriv constrainedProlateArithmeticFredholmDeterminant
        (-(GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ)⁻¹) ≠ 0 :=
  ⟨constrainedProlateArithmeticFredholmDeterminant_neg_inv_eq_zero n,
    constrainedProlateArithmeticFredholmDeterminant_deriv_neg_inv_ne_zero n⟩

end RHTower

end
