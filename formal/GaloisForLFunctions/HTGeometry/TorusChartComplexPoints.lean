import GaloisForLFunctions.HTGeometry.AlgebraSpectrumEquiv
import GaloisForLFunctions.HTGeometry.FundamentalGroupTopologicalGroup
import GaloisForLFunctions.HTGeometry.LocalizationTwoPrimeUnits

/-!
# Complex points of the torus-affine chart

The complex points of the localization of a polynomial ring at its first two coordinates are
canonically homeomorphic to `(ℂˣ)² × ℂᵏ`.  Both topology directions are proved from pointwise
convergence: polynomial evaluation is continuous, and evaluation of a fixed localized element is a
quotient of two fixed polynomial evaluations with nowhere-zero denominator.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

private abbrev TorusPolynomial (k : ℕ) := MvPolynomial (Fin (k + 2)) ℂ

private noncomputable def torusChartFirstUnit (k : ℕ) : (TorusChart ℂ k)ˣ :=
  (isUnit_algebraMap_left (A := TorusPolynomial k) (R := TorusChart ℂ k)
    (X (0 : Fin (k + 2))) (X (1 : Fin (k + 2)))).unit

private noncomputable def torusChartSecondUnit (k : ℕ) : (TorusChart ℂ k)ˣ :=
  (isUnit_algebraMap_right (A := TorusPolynomial k) (R := TorusChart ℂ k)
    (X (0 : Fin (k + 2))) (X (1 : Fin (k + 2)))).unit

private theorem torusChartFirstUnit_coe (k : ℕ) :
    (torusChartFirstUnit k : TorusChart ℂ k) =
      algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X 0) := by
  unfold torusChartFirstUnit
  exact IsUnit.unit_spec _

private theorem torusChartSecondUnit_coe (k : ℕ) :
    (torusChartSecondUnit k : TorusChart ℂ k) =
      algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X 1) := by
  unfold torusChartSecondUnit
  exact IsUnit.unit_spec _

private def torusChartAssignment (k : ℕ) (x : ComplexTorusAffineChart k) :
    Fin (k + 2) → ℂ :=
  Fin.cases (x.1 : ℂ) (Fin.cases (x.2.1 : ℂ) (fun i => x.2.2 i))

private theorem torusChartAssignment_zero (k : ℕ) (x : ComplexTorusAffineChart k) :
    torusChartAssignment k x 0 = (x.1 : ℂ) := rfl

private theorem torusChartAssignment_one (k : ℕ) (x : ComplexTorusAffineChart k) :
    torusChartAssignment k x 1 = (x.2.1 : ℂ) := rfl

private theorem torusChartAssignment_succ_succ (k : ℕ) (x : ComplexTorusAffineChart k)
    (i : Fin k) : torusChartAssignment k x i.succ.succ = x.2.2 i := rfl

private def torusChartAeval (k : ℕ) (x : ComplexTorusAffineChart k) :
    TorusPolynomial k →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval (torusChartAssignment k x)

private theorem torusChartAeval_isUnit_powers (k : ℕ) (x : ComplexTorusAffineChart k)
    (y : Submonoid.powers (X 0 * X 1 : TorusPolynomial k)) :
    IsUnit (torusChartAeval k x y) := by
  obtain ⟨n, hn⟩ := y.property
  rw [← hn, map_pow]
  apply IsUnit.pow
  simp only [torusChartAeval, map_mul, MvPolynomial.aeval_X,
    torusChartAssignment_zero, torusChartAssignment_one]
  exact x.1.isUnit.mul x.2.1.isUnit

private def torusChartAlgPoint (k : ℕ) (x : ComplexTorusAffineChart k) :
    AlgSpec (TorusChart ℂ k) :=
  AlgHom.mk (IsLocalization.lift (torusChartAeval_isUnit_powers k x)) fun c => by
    change IsLocalization.lift (torusChartAeval_isUnit_powers k x)
        (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (C c)) = c
    rw [IsLocalization.lift_eq]
    simp [torusChartAeval]

private def torusChartCoordinates (k : ℕ) (chi : AlgSpec (TorusChart ℂ k)) :
    ComplexTorusAffineChart k :=
  (Units.map chi.toMonoidHom (torusChartFirstUnit k),
    Units.map chi.toMonoidHom (torusChartSecondUnit k),
    fun i => chi (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X i.succ.succ)))

private theorem torusChartCoordinates_algPoint (k : ℕ) (x : ComplexTorusAffineChart k) :
    torusChartCoordinates k (torusChartAlgPoint k x) = x := by
  apply Prod.ext
  · apply Units.ext
    change torusChartAlgPoint k x (torusChartFirstUnit k) = (x.1 : ℂ)
    rw [torusChartFirstUnit_coe]
    change IsLocalization.lift (torusChartAeval_isUnit_powers k x)
      (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X 0)) = (x.1 : ℂ)
    rw [IsLocalization.lift_eq]
    simp [torusChartAeval, torusChartAssignment_zero]
  · apply Prod.ext
    · apply Units.ext
      change torusChartAlgPoint k x (torusChartSecondUnit k) = (x.2.1 : ℂ)
      rw [torusChartSecondUnit_coe]
      change IsLocalization.lift (torusChartAeval_isUnit_powers k x)
        (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X 1)) = (x.2.1 : ℂ)
      rw [IsLocalization.lift_eq]
      simp [torusChartAeval, torusChartAssignment_one]
    · apply Multiplicative.toAdd.injective
      funext i
      change IsLocalization.lift (torusChartAeval_isUnit_powers k x)
        (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X i.succ.succ)) = x.2.2 i
      rw [IsLocalization.lift_eq]
      simp [torusChartAeval, torusChartAssignment_succ_succ]

private theorem torusChartAlgPoint_coordinates (k : ℕ)
    (chi : AlgSpec (TorusChart ℂ k)) :
    torusChartAlgPoint k (torusChartCoordinates k chi) = chi := by
  apply IsLocalization.algHom_ext (Submonoid.powers (X 0 * X 1 : TorusPolynomial k))
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
  · change IsLocalization.lift
        (torusChartAeval_isUnit_powers k (torusChartCoordinates k chi))
        (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X 0)) =
      chi (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X 0))
    rw [IsLocalization.lift_eq]
    simp [torusChartAeval, torusChartCoordinates, torusChartAssignment_zero,
      torusChartFirstUnit_coe]
    rfl
  · change IsLocalization.lift
        (torusChartAeval_isUnit_powers k (torusChartCoordinates k chi))
        (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X 1)) =
      chi (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X 1))
    rw [IsLocalization.lift_eq]
    simp [torusChartAeval, torusChartCoordinates, torusChartAssignment_one,
      torusChartSecondUnit_coe]
    rfl
  · change IsLocalization.lift
        (torusChartAeval_isUnit_powers k (torusChartCoordinates k chi))
        (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X l.succ.succ)) =
      chi (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X l.succ.succ))
    rw [IsLocalization.lift_eq]
    simp [torusChartAeval, torusChartCoordinates, torusChartAssignment_succ_succ]

private theorem continuous_torusChartCoordinates (k : ℕ) :
    Continuous (torusChartCoordinates k) := by
  apply Continuous.prodMk
  · rw [Units.continuous_iff]
    constructor
    · change Continuous fun chi : AlgSpec (TorusChart ℂ k) =>
        chi (torusChartFirstUnit k)
      exact AlgSpec.continuous_eval (B := TorusChart ℂ k) (torusChartFirstUnit k)
    · convert AlgSpec.continuous_eval (B := TorusChart ℂ k)
        ((↑((torusChartFirstUnit k)⁻¹) : TorusChart ℂ k)) using 1
      funext chi
      simp
      rfl
  · apply Continuous.prodMk
    · rw [Units.continuous_iff]
      constructor
      · change Continuous fun chi : AlgSpec (TorusChart ℂ k) =>
          chi (torusChartSecondUnit k)
        exact AlgSpec.continuous_eval (B := TorusChart ℂ k) (torusChartSecondUnit k)
      · convert AlgSpec.continuous_eval (B := TorusChart ℂ k)
          ((↑((torusChartSecondUnit k)⁻¹) : TorusChart ℂ k)) using 1
        funext chi
        simp
        rfl
    · exact continuous_pi fun i =>
        AlgSpec.continuous_eval
          (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X i.succ.succ))

private theorem continuous_torusChartAssignment_apply (k : ℕ) (i : Fin (k + 2)) :
    Continuous fun x : ComplexTorusAffineChart k => torusChartAssignment k x i := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
  · change Continuous fun x : ComplexTorusAffineChart k => (x.1 : ℂ)
    fun_prop
  · change Continuous fun x : ComplexTorusAffineChart k => (x.2.1 : ℂ)
    fun_prop
  · change Continuous fun x : ComplexTorusAffineChart k => x.2.2 l
    fun_prop

private theorem continuous_torusChartAeval (k : ℕ) (p : TorusPolynomial k) :
    Continuous fun x : ComplexTorusAffineChart k => torusChartAeval k x p := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa [torusChartAeval] using
      (continuous_const : Continuous fun _ : ComplexTorusAffineChart k => c)
  | add p q hp hq =>
      rw [show (fun x => torusChartAeval k x (p + q)) =
          (fun x => torusChartAeval k x p) +
            (fun x => torusChartAeval k x q) by
        funext x
        exact map_add (torusChartAeval k x) p q]
      exact hp.add hq
  | mul_X p i hp =>
      rw [show (fun x => torusChartAeval k x (p * X i)) =
          (fun x => torusChartAeval k x p) *
            (fun x => torusChartAssignment k x i) by
        funext x
        change torusChartAeval k x (p * X i) =
          torusChartAeval k x p * torusChartAssignment k x i
        rw [map_mul]
        congr 1
        exact MvPolynomial.aeval_X (torusChartAssignment k x) i]
      exact hp.mul (continuous_torusChartAssignment_apply k i)

private theorem continuous_torusChartAlgPoint (k : ℕ) :
    Continuous (torusChartAlgPoint k) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  let M := Submonoid.powers (X 0 * X 1 : TorusPolynomial k)
  let s := IsLocalization.sec M b
  have hden : Continuous fun x : ComplexTorusAffineChart k =>
      torusChartAeval k x (s.2 : TorusPolynomial k) :=
    continuous_torusChartAeval k _
  have hnum : Continuous fun x : ComplexTorusAffineChart k =>
      torusChartAeval k x s.1 :=
    continuous_torusChartAeval k _
  have hden_ne (x : ComplexTorusAffineChart k) :
      torusChartAeval k x (s.2 : TorusPolynomial k) ≠ 0 :=
    (torusChartAeval_isUnit_powers k x s.2).ne_zero
  have hvalue (x : ComplexTorusAffineChart k) :
      torusChartAlgPoint k x b =
        torusChartAeval k x s.1 / torusChartAeval k x (s.2 : TorusPolynomial k) := by
    apply (eq_div_iff (hden_ne x)).2
    have h := congrArg (fun z => torusChartAlgPoint k x z)
      (IsLocalization.sec_spec M b)
    have h' : torusChartAlgPoint k x b *
        torusChartAlgPoint k x
          (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (s.2 : TorusPolynomial k)) =
        torusChartAlgPoint k x
          (algebraMap (TorusPolynomial k) (TorusChart ℂ k) s.1) := by
      simpa only [map_mul] using h
    have hs : torusChartAlgPoint k x
        (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (s.2 : TorusPolynomial k)) =
        torusChartAeval k x (s.2 : TorusPolynomial k) := by
      change IsLocalization.lift (torusChartAeval_isUnit_powers k x)
          (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (s.2 : TorusPolynomial k)) = _
      rw [IsLocalization.lift_eq]
      rfl
    have hn : torusChartAlgPoint k x
        (algebraMap (TorusPolynomial k) (TorusChart ℂ k) s.1) =
        torusChartAeval k x s.1 := by
      change IsLocalization.lift (torusChartAeval_isUnit_powers k x)
          (algebraMap (TorusPolynomial k) (TorusChart ℂ k) s.1) = _
      rw [IsLocalization.lift_eq]
      rfl
    rw [hs, hn] at h'
    exact h'
  convert hnum.div₀ hden hden_ne using 1
  funext x
  exact hvalue x

/-- **Complex points of the torus-affine coordinate ring are the analytic torus-affine chart.** -/
noncomputable def torusChartComplexPointHomeomorph (k : ℕ) :
    AlgSpec (TorusChart ℂ k) ≃ₜ ComplexTorusAffineChart k where
  toFun := torusChartCoordinates k
  invFun := torusChartAlgPoint k
  left_inv := torusChartAlgPoint_coordinates k
  right_inv := torusChartCoordinates_algPoint k
  continuous_toFun := continuous_torusChartCoordinates k
  continuous_invFun := continuous_torusChartAlgPoint k

/-- The first analytic torus coordinate is evaluation of the first localized polynomial
coordinate. -/
theorem torusChartComplexPointHomeomorph_first_val (k : ℕ)
    (chi : AlgSpec (TorusChart ℂ k)) :
    ((torusChartComplexPointHomeomorph k chi).1 : ℂ) =
      chi (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X 0)) := by
  change chi (torusChartFirstUnit k) = _
  rw [torusChartFirstUnit_coe]

/-- The second analytic torus coordinate is evaluation of the second localized polynomial
coordinate. -/
theorem torusChartComplexPointHomeomorph_second_val (k : ℕ)
    (chi : AlgSpec (TorusChart ℂ k)) :
    ((torusChartComplexPointHomeomorph k chi).2.1 : ℂ) =
      chi (algebraMap (TorusPolynomial k) (TorusChart ℂ k) (X 1)) := by
  change chi (torusChartSecondUnit k) = _
  rw [torusChartSecondUnit_coe]

end

end GaloisForLFunctions.HTGeometry
