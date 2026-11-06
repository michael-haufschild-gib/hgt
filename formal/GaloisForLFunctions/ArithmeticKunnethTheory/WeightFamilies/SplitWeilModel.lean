import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.GoldenInvariantWeights

/-!
# Full special-linear monodromy with arbitrary fixed-determinant Frobenius

The group `SL₂(ℂ) × ℤ` acts on the plane by `(g,n) ↦ c^n g`. Its degree-zero image is
all of `SL₂`, and its degree-one image is exactly the matrices of determinant `c²`.
The action normalizes the degree-zero image and has the prescribed invariant tensor
characters. In particular, the Golden Frobenius admits such a lift.

This constructs an abstract group representation. It supplies no arithmetic base
or global cohomological trace formula.
-/

open Matrix
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

/-- A split group extension with special-linear kernel and integer quotient. -/
abbrev SplitWeilModel := Matrix.SpecialLinearGroup (Fin 2) ℂ × Multiplicative ℤ

/-- The integer quotient coordinate. -/
def splitDegree (g : SplitWeilModel) : ℤ := Multiplicative.toAdd g.2

/-- Scalar twist of the standard special-linear representation. -/
def splitAction (c : ℂ) (hc : c ≠ 0) :
    SplitWeilModel →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun g := c ^ splitDegree g • (g.1 : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := by simp [splitDegree]
  map_mul' g h := by
    change c ^ (splitDegree g + splitDegree h) •
      ((g.1 : Matrix (Fin 2) (Fin 2) ℂ) * (h.1 : Matrix (Fin 2) (Fin 2) ℂ)) = _
    rw [zpow_add₀ hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem splitDegree_mul (g h : SplitWeilModel) :
    splitDegree (g * h) = splitDegree g + splitDegree h := rfl

theorem splitDegree_inv (g : SplitWeilModel) : splitDegree g⁻¹ = -splitDegree g := rfl

theorem splitDegree_conjugate (g h : SplitWeilModel) :
    splitDegree (g * h * g⁻¹) = splitDegree h := by
  rw [splitDegree_mul, splitDegree_mul, splitDegree_inv]
  omega

theorem splitDegree_surjective : Function.Surjective splitDegree :=
  fun n => ⟨(1, Multiplicative.ofAdd n), rfl⟩

/-- The determinant is determined entirely by the integer degree. -/
theorem splitAction_det (c : ℂ) (hc : c ≠ 0) (g : SplitWeilModel) :
    (splitAction c hc g).det = (c ^ splitDegree g) ^ 2 := by
  change ((c ^ splitDegree g) • (g.1 : Matrix (Fin 2) (Fin 2) ℂ)).det = _
  rw [Matrix.det_smul]
  simp only [Fintype.card_fin, g.1.property, mul_one]

/-- The geometric image is the entire determinant-one group. -/
theorem splitAction_degree_zero_iff (c : ℂ) (hc : c ≠ 0)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (∃ g : SplitWeilModel, splitDegree g = 0 ∧ splitAction c hc g = A) ↔ A.det = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [splitAction_det, hg, zpow_zero, one_pow]
  · intro hA
    refine ⟨(⟨A, hA⟩, Multiplicative.ofAdd 0), rfl, ?_⟩
    change c ^ (0 : ℤ) • A = A
    rw [zpow_zero, one_smul]

/-- The determinant is the only restriction on a degree-one Frobenius matrix. -/
theorem splitAction_degree_one_iff (c : ℂ) (hc : c ≠ 0)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (∃ g : SplitWeilModel, splitDegree g = 1 ∧ splitAction c hc g = A) ↔ A.det = c ^ 2 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [splitAction_det, hg, zpow_one]
  · intro hA
    have hd : (c⁻¹ • A).det = 1 := by
      rw [Matrix.det_smul, hA]
      simp only [Fintype.card_fin, inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero _ hc)
    refine ⟨(⟨c⁻¹ • A, hd⟩, Multiplicative.ofAdd 1), rfl, ?_⟩
    change c ^ (1 : ℤ) • (c⁻¹ • A) = A
    rw [zpow_one, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- Every group element intertwines the full geometric image with itself. -/
theorem splitAction_normalizes (c : ℂ) (hc : c ≠ 0) (g : SplitWeilModel)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 1) :
    ∃ h : SplitWeilModel, splitDegree h = 0 ∧
      splitAction c hc g * M = splitAction c hc h * splitAction c hc g := by
  obtain ⟨n, hn, hMn⟩ := (splitAction_degree_zero_iff c hc M).mpr hM
  refine ⟨g * n * g⁻¹, by rw [splitDegree_conjugate, hn], ?_⟩
  rw [← hMn, ← map_mul, ← map_mul]
  congr 1
  group

/-- Invariant forms see only the scalar character and the tensor degree. -/
theorem splitAction_invariant (c : ℂ) (hc : c ≠ 0) (g : SplitWeilModel)
    (n : ℕ) (f : invariantForms n) (v : Fin n → Plane) :
    f.val (fun i => (splitAction c hc g).mulVec (v i)) =
      (c ^ splitDegree g) ^ n * f.val v :=
  invariant_scalar_mul n f _ _ g.1.property v

/-- The impure Golden Frobenius occurs in a degree-one lift with full geometric image. -/
theorem goldenFrobenius_has_split_lift :
    ∃ g : SplitWeilModel, splitDegree g = 1 ∧
      (Real.sqrt 5 : ℂ) ^ splitDegree g • (g.1 : Matrix (Fin 2) (Fin 2) ℂ) =
        goldenFrobenius := by
  have hc : (Real.sqrt 5 : ℂ) ≠ 0 := by
    have hr : Real.sqrt (5 : ℝ) ≠ 0 := by positivity
    exact_mod_cast hr
  apply (splitAction_degree_one_iff _ hc goldenFrobenius).mpr
  rw [goldenFrobenius_det, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
