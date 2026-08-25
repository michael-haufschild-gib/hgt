import GaloisForLFunctions.RHTower.PrimeAFMatrixOperatorKOne
import GaloisForLFunctions.HTGeometry.UnitaryConjugationMatrixUnits
import GaloisForLFunctions.HTGeometry.UnitaryLocalLogNullhomotopy
import GaloisForLFunctions.HTGeometry.LoopOpenCoverDecomposition
import GaloisForLFunctions.HTGeometry.FiniteUnitaryDeterminantExponential
import GaloisForLFunctions.HTGeometry.ContinuousIntegerLatticeRigidity
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryLocalLogNullhomotopy
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryRotatedLogNullhomotopy
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryNormalization

open GaloisForLFunctions.HTGeometry

namespace PrimeQuasiLocalCharge

noncomputable section

@[simp] theorem unitsHomeomorphNeZero_symm_coe
    (z : {w : ℂ // w ≠ 0}) :
    ((unitsHomeomorphNeZero (G₀ := ℂ)).symm z : ℂ) = z := by
  have h := (unitsHomeomorphNeZero (G₀ := ℂ)).apply_symm_apply z
  exact congrArg Subtype.val h

@[simp] theorem unitsHomeomorphNeZero_coe (z : Units ℂ) :
    ((unitsHomeomorphNeZero (G₀ := ℂ) z : {w : ℂ // w ≠ 0}) : ℂ) = z := by
  have h := (unitsHomeomorphNeZero (G₀ := ℂ)).symm_apply_apply z
  have hv := congrArg (fun u : Units ℂ ↦ (u : ℂ)) h
  rw [unitsHomeomorphNeZero_symm_coe] at hv
  exact hv

/-- Radial projection of a nonzero complex scalar to unit modulus. -/
def complexUnitsPhase (z : Units ℂ) : ℂ := (z : ℂ) / ‖(z : ℂ)‖

@[simp] theorem norm_complexUnitsPhase (z : Units ℂ) :
    ‖complexUnitsPhase z‖ = 1 := by
  rw [complexUnitsPhase, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), div_self]
  exact norm_ne_zero_iff.mpr (Units.ne_zero z)

theorem complexUnitsPhase_ne_zero (z : Units ℂ) : complexUnitsPhase z ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_complexUnitsPhase]; exact one_ne_zero)

theorem continuous_complexUnitsPhase :
    Continuous (complexUnitsPhase : Units ℂ → ℂ) := by
  unfold complexUnitsPhase
  have hden : Continuous (fun z : Units ℂ ↦
      Complex.ofReal ‖(z : ℂ)‖) := by fun_prop
  have hnum : Continuous (fun z : Units ℂ ↦ (z : ℂ)) := by
    fun_prop
  have hquot := Continuous.div₀ hnum hden (fun z ↦ by
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Units.ne_zero z)))
  simpa only using hquot

/-- Radial phase, retained as a complex unit. -/
def complexUnitsPhaseUnits (z : Units ℂ) : Units ℂ :=
  (unitsHomeomorphNeZero (G₀ := ℂ)).symm
    ⟨complexUnitsPhase z, complexUnitsPhase_ne_zero z⟩

@[simp] theorem complexUnitsPhaseUnits_coe (z : Units ℂ) :
    (complexUnitsPhaseUnits z : ℂ) = complexUnitsPhase z := by
  have h := (unitsHomeomorphNeZero (G₀ := ℂ)).apply_symm_apply
    ⟨complexUnitsPhase z, complexUnitsPhase_ne_zero z⟩
  exact congrArg Subtype.val h

theorem continuous_complexUnitsPhaseUnits :
    Continuous (complexUnitsPhaseUnits : Units ℂ → Units ℂ) := by
  apply (unitsHomeomorphNeZero (G₀ := ℂ)).symm.continuous.comp
  apply continuous_induced_rng.2
  exact continuous_complexUnitsPhase

@[simp] theorem complexUnitsPhaseUnits_one : complexUnitsPhaseUnits 1 = 1 := by
  apply Units.ext
  simp [complexUnitsPhase]

/-- Diagonal unitary carrying the radial phase in its first coordinate. -/
def complexUnitsPhaseDiagonal (n : ℕ) (z : Units ℂ) :
    Matrix.unitaryGroup (Fin (n + 1)) ℂ :=
  ⟨Matrix.diagonal (fun i ↦ if i = 0 then complexUnitsPhase z else 1),
    GaloisForLFunctions.EquivariantCausalizer.mem_unitaryGroup_diagonal _ (by
      intro i
      by_cases hi : i = 0
      · simp [hi]
      · simp [hi])⟩

theorem continuous_complexUnitsPhaseDiagonal (n : ℕ) :
    Continuous (complexUnitsPhaseDiagonal n : Units ℂ →
      Matrix.unitaryGroup (Fin (n + 1)) ℂ) := by
  apply continuous_induced_rng.2
  change Continuous (fun z : Units ℂ ↦
    Matrix.diagonal (fun i : Fin (n + 1) ↦
      if i = 0 then complexUnitsPhase z else 1))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    by_cases hi : i = 0
    · simp [hi, continuous_complexUnitsPhase]
    · simpa [hi] using (continuous_const : Continuous (fun _ : Units ℂ ↦ (1 : ℂ)))
  · simpa [Matrix.diagonal_apply, hij] using
      (continuous_const : Continuous (fun _ : Units ℂ ↦ (0 : ℂ)))

@[simp] theorem complexUnitsPhaseDiagonal_one (n : ℕ) :
    complexUnitsPhaseDiagonal n 1 = 1 := by
  apply Subtype.ext
  ext i j
  simp [complexUnitsPhaseDiagonal, complexUnitsPhase, Matrix.one_apply]

/-- Determinant of the diagonal phase lift is radial projection. -/
theorem unitaryDeterminantUnits_complexUnitsPhaseDiagonal (n : ℕ) (z : Units ℂ) :
    unitaryDeterminantUnits (complexUnitsPhaseDiagonal n z) =
      complexUnitsPhaseUnits z := by
  apply Units.ext
  rw [unitaryDeterminantUnits_coe, complexUnitsPhaseUnits_coe]
  change Matrix.det (Matrix.diagonal
      (fun i : Fin (n + 1) ↦ if i = 0 then complexUnitsPhase z else 1)) =
    complexUnitsPhase z
  rw [Matrix.det_diagonal, Fin.prod_univ_succ]
  simp

/-- Positive radial coefficient interpolating from a complex unit to its phase. -/
def complexUnitsRadialCoefficient (t : unitInterval) (z : Units ℂ) : ℝ :=
  (((1 - (t : ℝ)) * ‖(z : ℂ)‖ + (t : ℝ)) / ‖(z : ℂ)‖)

theorem complexUnitsRadialCoefficient_pos (t : unitInterval) (z : Units ℂ) :
    0 < complexUnitsRadialCoefficient t z := by
  have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero z)
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have ht1 : (t : ℝ) ≤ 1 := t.property.2
  have hfirst : 0 ≤ (1 - (t : ℝ)) * ‖(z : ℂ)‖ :=
    mul_nonneg (sub_nonneg.mpr ht1) (le_of_lt hz)
  have hnum : 0 < (1 - (t : ℝ)) * ‖(z : ℂ)‖ + (t : ℝ) := by
    by_cases ht : (t : ℝ) = 0
    · simp [ht, hz]
    · exact add_pos_of_nonneg_of_pos hfirst (lt_of_le_of_ne ht0 (Ne.symm ht))
  exact div_pos hnum hz

/-- Radial deformation through nonzero complex scalars. -/
def complexUnitsRadialValue (p : unitInterval × Units ℂ) : ℂ :=
  (complexUnitsRadialCoefficient p.1 p.2 : ℂ) * (p.2 : ℂ)

theorem complexUnitsRadialValue_ne_zero (p : unitInterval × Units ℂ) :
    complexUnitsRadialValue p ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt (complexUnitsRadialCoefficient_pos p.1 p.2)
  · exact Units.ne_zero p.2

theorem continuous_complexUnitsRadialValue :
    Continuous complexUnitsRadialValue := by
  unfold complexUnitsRadialValue complexUnitsRadialCoefficient
  have hval : Continuous (fun p : unitInterval × Units ℂ ↦ (p.2 : ℂ)) := by
    fun_prop
  have hnorm : Continuous (fun p : unitInterval × Units ℂ ↦ ‖(p.2 : ℂ)‖) :=
    continuous_norm.comp hval
  have hcoeff : Continuous (fun p : unitInterval × Units ℂ ↦
      (((1 - (p.1 : ℝ)) * ‖(p.2 : ℂ)‖ + (p.1 : ℝ)) / ‖(p.2 : ℂ)‖)) := by
    apply Continuous.div₀
    · fun_prop
    · exact hnorm
    · intro p
      exact norm_ne_zero_iff.mpr (Units.ne_zero p.2)
  exact (Complex.continuous_ofReal.comp hcoeff).mul hval

/-- Radial deformation, as a path through complex units. -/
def complexUnitsRadialHomotopyMap : C(unitInterval × Units ℂ, Units ℂ) :=
  ⟨fun p ↦ (unitsHomeomorphNeZero (G₀ := ℂ)).symm
      ⟨complexUnitsRadialValue p, complexUnitsRadialValue_ne_zero p⟩,
    (unitsHomeomorphNeZero (G₀ := ℂ)).symm.continuous.comp
      (continuous_induced_rng.2 continuous_complexUnitsRadialValue)⟩

@[simp] theorem complexUnitsRadialHomotopyMap_zero (z : Units ℂ) :
    complexUnitsRadialHomotopyMap (0, z) = z := by
  apply (unitsHomeomorphNeZero (G₀ := ℂ)).injective
  apply Subtype.ext
  simp [complexUnitsRadialHomotopyMap, complexUnitsRadialValue,
    complexUnitsRadialCoefficient, norm_ne_zero_iff.mpr (Units.ne_zero z)]

@[simp] theorem complexUnitsRadialHomotopyMap_one (z : Units ℂ) :
    complexUnitsRadialHomotopyMap (1, z) = complexUnitsPhaseUnits z := by
  apply Units.ext
  simp [complexUnitsRadialHomotopyMap, complexUnitsRadialValue,
    complexUnitsRadialCoefficient, complexUnitsPhase, div_eq_inv_mul]

@[simp] theorem complexUnitsRadialHomotopyMap_base (t : unitInterval) :
    complexUnitsRadialHomotopyMap (t, 1) = 1 := by
  apply Units.ext
  simp [complexUnitsRadialHomotopyMap, complexUnitsRadialValue,
    complexUnitsRadialCoefficient]

/-- Based radial homotopy from identity on `ℂˣ` to phase projection. -/
def complexUnitsRadialHomotopy :
    (ContinuousMap.id (Units ℂ)).Homotopy
      ⟨complexUnitsPhaseUnits, continuous_complexUnitsPhaseUnits⟩ where
  toContinuousMap := complexUnitsRadialHomotopyMap
  map_zero_left := complexUnitsRadialHomotopyMap_zero
  map_one_left := complexUnitsRadialHomotopyMap_one

/-- Explicit endpoint-rewritten map of a based path. -/
def basedMapPath {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y) (hbase : f x = y) (p : Path x x) :
    Path y y where
  toFun := fun t ↦ f (p t)
  continuous_toFun := f.continuous.comp p.continuous
  source' := by simpa using hbase
  target' := by simpa using hbase

/-- Endpoint-rewritten based path maps preserve endpoint-fixed homotopy. -/
theorem basedMapPath_homotopic {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y) (hbase : f x = y)
    {p q : Path x x} (hpq : p.Homotopic q) :
    (basedMapPath f x y hbase p).Homotopic
      (basedMapPath f x y hbase q) := by
  rcases hpq with ⟨H⟩
  let Kmap : C(unitInterval × unitInterval, Y) :=
    ⟨fun st ↦ f (H.toFun st), f.continuous.comp H.continuous⟩
  let K : (basedMapPath f x y hbase p).toContinuousMap.Homotopy
      (basedMapPath f x y hbase q).toContinuousMap :=
    { toContinuousMap := Kmap
      map_zero_left := by
        intro t
        exact congrArg f (H.map_zero_left t)
      map_one_left := by
        intro t
        exact congrArg f (H.map_one_left t) }
  refine ⟨K, ?_⟩
  intro t z hz
  exact congrArg f (H.prop' t z hz)

/-- Radial phase projection of a based loop, with endpoints rewritten to the basepoint. -/
def complexUnitsPhasePath (p : Path (1 : Units ℂ) 1) :
    Path (1 : Units ℂ) (1 : Units ℂ) :=
  basedMapPath
    ⟨complexUnitsPhaseUnits, continuous_complexUnitsPhaseUnits⟩ 1 1
    complexUnitsPhaseUnits_one p

/-- Radial deformation of a based loop is endpoint-fixed. -/
def complexUnitsRadialPathHomotopy (p : Path (1 : Units ℂ) 1) :
    p.Homotopy (complexUnitsPhasePath p) := by
  let Hmap : C(unitInterval × unitInterval, Units ℂ) :=
    ⟨fun q ↦ complexUnitsRadialHomotopyMap (q.1, p q.2), by
      apply complexUnitsRadialHomotopyMap.continuous.comp
      fun_prop⟩
  let H : p.toContinuousMap.Homotopy
      (complexUnitsPhasePath p).toContinuousMap :=
    { toContinuousMap := Hmap
      map_zero_left := by
        intro t
        simp [Hmap]
      map_one_left := by
        intro t
        simp [Hmap, complexUnitsPhasePath, basedMapPath] }
  refine ⟨H, ?_⟩
  intro t x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · subst x
    change complexUnitsRadialHomotopyMap (t, p 0) = p 0
    simp
  · subst x
    change complexUnitsRadialHomotopyMap (t, p 1) = p 1
    simp

/-- Phase projection on based path-homotopy classes, with endpoints fixed explicitly. -/
def complexUnitsPhaseKOneMap :
    FundamentalGroup (Units ℂ) 1 → FundamentalGroup (Units ℂ) 1 :=
  Quotient.map complexUnitsPhasePath (fun _ _ h ↦
    basedMapPath_homotopic _ _ _ _ h)

/-- Radial phase projection is identity on based path-homotopy classes. -/
theorem complexUnitsPhaseKOneMap_apply
    (q : FundamentalGroup (Units ℂ) 1) : complexUnitsPhaseKOneMap q = q := by
  refine Quotient.inductionOn q ?_
  intro p
  apply Quotient.sound
  exact ⟨(complexUnitsRadialPathHomotopy p).symm⟩

/-- Determinant sends a based finite-unitary loop to a based nonzero scalar loop. -/
def finiteUnitaryDeterminantPath (n : ℕ)
    (p : Path (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1) :
    Path (1 : Units ℂ) 1 :=
  basedMapPath
    ⟨unitaryDeterminantUnits, continuous_unitaryDeterminantUnits⟩ 1 1
    unitaryDeterminantUnits_one p

theorem finiteUnitaryDeterminantPath_homotopic {n : ℕ}
    {p q : Path (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1}
    (h : p.Homotopic q) :
    (finiteUnitaryDeterminantPath n p).Homotopic
      (finiteUnitaryDeterminantPath n q) := by
  exact basedMapPath_homotopic _ _ _ _ h

/-- Literal determinant map on finite matrix-stage `K₁`, with no dependent basepoint cast. -/
def finiteUnitaryDeterminantKOneMap (n : ℕ) :
    FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 →
      FundamentalGroup (Units ℂ) 1 :=
  Quotient.map (finiteUnitaryDeterminantPath n)
    (fun _ _ h ↦ finiteUnitaryDeterminantPath_homotopic h)

/-- Diagonal phase lift sends a based scalar loop to a based finite-unitary loop. -/
def complexUnitsPhaseDiagonalPath (n : ℕ) (p : Path (1 : Units ℂ) 1) :
    Path (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 :=
  basedMapPath
    ⟨complexUnitsPhaseDiagonal n, continuous_complexUnitsPhaseDiagonal n⟩ 1 1
    (complexUnitsPhaseDiagonal_one n) p

theorem complexUnitsPhaseDiagonalPath_homotopic {n : ℕ}
    {p q : Path (1 : Units ℂ) 1} (h : p.Homotopic q) :
    (complexUnitsPhaseDiagonalPath n p).Homotopic
      (complexUnitsPhaseDiagonalPath n q) := by
  exact basedMapPath_homotopic _ _ _ _ h

/-- Diagonal phase lift on finite-stage `K₁`. -/
def complexUnitsPhaseDiagonalKOneMap (n : ℕ) :
    FundamentalGroup (Units ℂ) 1 →
      FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 :=
  Quotient.map (complexUnitsPhaseDiagonalPath n)
    (fun _ _ h ↦ complexUnitsPhaseDiagonalPath_homotopic h)

/-- Determinant after diagonal phase lift is radial phase projection. -/
theorem finiteUnitaryDeterminantKOneMap_phaseDiagonal (n : ℕ)
    (q : FundamentalGroup (Units ℂ) 1) :
    finiteUnitaryDeterminantKOneMap n
        (complexUnitsPhaseDiagonalKOneMap n q) = q := by
  refine Quotient.inductionOn q ?_
  intro p
  have hpath : finiteUnitaryDeterminantPath n
      (complexUnitsPhaseDiagonalPath n p) = complexUnitsPhasePath p := by
    ext t
    exact congrArg (fun u : Units ℂ ↦ (u : ℂ))
      (unitaryDeterminantUnits_complexUnitsPhaseDiagonal n (p t))
  change Quotient.mk _ (finiteUnitaryDeterminantPath n
      (complexUnitsPhaseDiagonalPath n p)) = Quotient.mk _ p
  rw [hpath]
  apply Quotient.sound
  exact ⟨(complexUnitsRadialPathHomotopy p).symm⟩

/-- Finite-stage determinant is surjective on literal operator-`K₁`. -/
theorem finiteUnitaryDeterminantKOneMap_surjective (n : ℕ) :
    Function.Surjective (finiteUnitaryDeterminantKOneMap n) := by
  intro q
  exact ⟨complexUnitsPhaseDiagonalKOneMap n q,
    finiteUnitaryDeterminantKOneMap_phaseDiagonal n q⟩

theorem norm_unitaryMatrix_det {n : ℕ}
    (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
    ‖(U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).det‖ = 1 := by
  have hdet : star (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).det *
      (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).det = 1 :=
    (Unitary.mem_iff.mp (Matrix.det_of_mem_unitary U.2)).1
  have hnorm := congrArg norm hdet
  rw [norm_mul, norm_star, norm_one] at hnorm
  nlinarith [norm_nonneg
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).det]

theorem complexUnitsPhase_unitaryDeterminantUnits {n : ℕ}
    (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
    complexUnitsPhase (unitaryDeterminantUnits U) =
      (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).det := by
  rw [complexUnitsPhase, unitaryDeterminantUnits_coe,
    norm_unitaryMatrix_det]
  norm_num

theorem complexUnitsPhaseDiagonal_unitaryDeterminantUnits {n : ℕ}
    (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
    complexUnitsPhaseDiagonal n (unitaryDeterminantUnits U) =
      unitaryDeterminantSection (0 : Fin (n + 1))
        (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).det
        ((Unitary.mem_iff.mp (Matrix.det_of_mem_unitary U.2)).1) := by
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0
    · subst i
      simp [complexUnitsPhaseDiagonal, unitaryDeterminantSection,
        complexUnitsPhase_unitaryDeterminantUnits]
    · simp [complexUnitsPhaseDiagonal, unitaryDeterminantSection, hi]
  · simp [complexUnitsPhaseDiagonal, unitaryDeterminantSection, hij]

/-- Pointwise exact factorization into determinant-normalized special-unitary part and diagonal
determinant section. -/
theorem specialUnitaryNormalize_mul_phaseDiagonal {n : ℕ}
    (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
    specialUnitaryToUnitary
        (specialUnitaryNormalize (0 : Fin (n + 1)) U) *
      complexUnitsPhaseDiagonal n (unitaryDeterminantUnits U) = U := by
  apply Subtype.ext
  unfold specialUnitaryNormalize specialUnitaryToUnitary
  let D : Matrix.unitaryGroup (Fin (n + 1)) ℂ :=
    unitaryDeterminantSection (0 : Fin (n + 1))
      (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).det
      ((Unitary.mem_iff.mp (Matrix.det_of_mem_unitary U.2)).1)
  change ((U * D⁻¹ : Matrix.unitaryGroup (Fin (n + 1)) ℂ) *
    complexUnitsPhaseDiagonal n (unitaryDeterminantUnits U) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = U
  rw [complexUnitsPhaseDiagonal_unitaryDeterminantUnits]
  change ((U * D⁻¹ : Matrix.unitaryGroup (Fin (n + 1)) ℂ) * D :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = U
  have hD : star D * D = (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) := by
    simp
  have hDcoe := congrArg Subtype.val hD
  have hDmatrix :
      ((star D : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * D = 1 := by
    change ((star D : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * D = 1 at hDcoe
    exact hDcoe
  change (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *
    ((star D : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * D = U
  rw [Matrix.mul_assoc, hDmatrix, Matrix.mul_one]

theorem continuous_specialUnitaryToUnitary {n : ℕ} :
    Continuous (specialUnitaryToUnitary :
      Matrix.specialUnitaryGroup (Fin (n + 1)) ℂ →
        Matrix.unitaryGroup (Fin (n + 1)) ℂ) := by
  apply continuous_induced_rng.2
  exact continuous_subtype_val

@[simp] theorem specialUnitaryNormalize_one {n : ℕ} :
    specialUnitaryNormalize (0 : Fin (n + 1))
      (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) = 1 := by
  apply Subtype.ext
  have h := congrArg Subtype.val (specialUnitaryNormalize_eq_of_det_eq_one
    (0 : Fin (n + 1)) (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (by simp))
  exact h

/-- Determinant normalization of a based finite-unitary loop, as a literal based `SU` loop. -/
def finiteUnitarySpecialNormalizePath (n : ℕ)
    (p : Path (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1) :
    Path (1 : Matrix.specialUnitaryGroup (Fin (n + 1)) ℂ) 1 :=
  basedMapPath
    ⟨specialUnitaryNormalize (0 : Fin (n + 1)),
      continuous_specialUnitaryNormalize (0 : Fin (n + 1))⟩
    1 1 specialUnitaryNormalize_one p

/-- Include a based finite special-unitary loop into the finite unitary group. -/
def finiteSpecialUnitaryInclusionPath (n : ℕ)
    (p : Path (1 : Matrix.specialUnitaryGroup (Fin (n + 1)) ℂ) 1) :
    Path (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 :=
  basedMapPath
    ⟨specialUnitaryToUnitary, continuous_specialUnitaryToUnitary⟩
    1 1 (by rfl) p

/-- Normalization followed by inclusion, at path level. -/
def finiteUnitarySpecialNormalizeInclusionPath (n : ℕ)
    (p : Path (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1) :
    Path (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 :=
  finiteSpecialUnitaryInclusionPath n (finiteUnitarySpecialNormalizePath n p)

theorem finiteUnitarySpecialNormalizeInclusionPath_homotopic {n : ℕ}
    {p q : Path (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1}
    (h : p.Homotopic q) :
    (finiteUnitarySpecialNormalizeInclusionPath n p).Homotopic
      (finiteUnitarySpecialNormalizeInclusionPath n q) := by
  unfold finiteUnitarySpecialNormalizeInclusionPath
  unfold finiteSpecialUnitaryInclusionPath finiteUnitarySpecialNormalizePath
  refine basedMapPath_homotopic _ 1 1 (by rfl) ?_
  exact basedMapPath_homotopic _ 1 1 specialUnitaryNormalize_one h

/-- Every finite-unitary loop is pointwise its normalized `SU` loop times its diagonal determinant
loop. -/
theorem finiteUnitary_normalize_mul_determinant_path (n : ℕ)
    (p : Path (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1) :
    GaloisForLFunctions.HTGeometry.loopPointwiseMulPath
      (finiteUnitarySpecialNormalizeInclusionPath n p)
      (complexUnitsPhaseDiagonalPath n (finiteUnitaryDeterminantPath n p)) = p := by
  ext t i j
  have ht := congrArg Subtype.val
    (specialUnitaryNormalize_mul_phaseDiagonal (p t))
  exact congrFun (congrFun ht i) j

/-- Normalization-inclusion on finite-unitary path-homotopy classes. -/
def finiteUnitarySpecialNormalizeInclusionKOneMap (n : ℕ) :
    FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 →
      FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 :=
  Quotient.map (finiteUnitarySpecialNormalizeInclusionPath n)
    (fun _ _ h ↦ finiteUnitarySpecialNormalizeInclusionPath_homotopic h)

/-- Exact quotient-level factorization into the `SU` kernel part and determinant section. -/
theorem finiteUnitaryKOne_eq_normalize_pointwiseMul_determinant (n : ℕ)
    (q : FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1) :
    q = GaloisForLFunctions.HTGeometry.fundamentalGroupPointwiseMul
      (finiteUnitarySpecialNormalizeInclusionKOneMap n q)
      (complexUnitsPhaseDiagonalKOneMap n
        (finiteUnitaryDeterminantKOneMap n q)) := by
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
      change Path.Homotopic.Quotient.mk p =
        GaloisForLFunctions.HTGeometry.fundamentalGroupPointwiseMul
          (Path.Homotopic.Quotient.mk
            (finiteUnitarySpecialNormalizeInclusionPath n p))
          (Path.Homotopic.Quotient.mk
            (complexUnitsPhaseDiagonalPath n (finiteUnitaryDeterminantPath n p)))
      rw [GaloisForLFunctions.HTGeometry.fundamentalGroupPointwiseMul_mk]
      exact congrArg Path.Homotopic.Quotient.mk
        (finiteUnitary_normalize_mul_determinant_path n p).symm

/-- A determinant-trivial class equals its normalized special-unitary inclusion. -/
theorem finiteUnitaryKOne_eq_normalize_of_determinant_eq_one (n : ℕ)
    (q : FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1)
    (hq : finiteUnitaryDeterminantKOneMap n q = 1) :
    q = finiteUnitarySpecialNormalizeInclusionKOneMap n q := by
  have hone : complexUnitsPhaseDiagonalKOneMap n 1 = 1 := by
    change Path.Homotopic.Quotient.mk
      (complexUnitsPhaseDiagonalPath n (Path.refl 1)) =
        Path.Homotopic.Quotient.mk (Path.refl 1)
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    simp [complexUnitsPhaseDiagonalPath, basedMapPath]
  calc
    q = GaloisForLFunctions.HTGeometry.fundamentalGroupPointwiseMul
        (finiteUnitarySpecialNormalizeInclusionKOneMap n q)
        (complexUnitsPhaseDiagonalKOneMap n
          (finiteUnitaryDeterminantKOneMap n q)) :=
      finiteUnitaryKOne_eq_normalize_pointwiseMul_determinant n q
    _ = GaloisForLFunctions.HTGeometry.fundamentalGroupPointwiseMul
        (finiteUnitarySpecialNormalizeInclusionKOneMap n q)
        (complexUnitsPhaseDiagonalKOneMap n 1) := by rw [hq]
    _ =
    GaloisForLFunctions.HTGeometry.fundamentalGroupPointwiseMul
        (finiteUnitarySpecialNormalizeInclusionKOneMap n q)
        (1 : FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1) := by rw [hone]
    _ = finiteUnitarySpecialNormalizeInclusionKOneMap n q :=
      GaloisForLFunctions.HTGeometry.fundamentalGroupPointwiseMul_one_right _

theorem finiteUnitarySpecialNormalizePath_homotopic {n : ℕ}
    {p q : Path (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1}
    (h : p.Homotopic q) :
    (finiteUnitarySpecialNormalizePath n p).Homotopic
      (finiteUnitarySpecialNormalizePath n q) := by
  exact basedMapPath_homotopic _ _ _ _ h

theorem finiteSpecialUnitaryInclusionPath_homotopic {n : ℕ}
    {p q : Path (1 : Matrix.specialUnitaryGroup (Fin (n + 1)) ℂ) 1}
    (h : p.Homotopic q) :
    (finiteSpecialUnitaryInclusionPath n p).Homotopic
      (finiteSpecialUnitaryInclusionPath n q) := by
  exact basedMapPath_homotopic _ _ _ _ h

/-- Determinant normalization from finite-unitary loop classes to literal finite `SU` loop
classes. -/
def finiteUnitarySpecialNormalizeKOneMap (n : ℕ) :
    FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 →
      FundamentalGroup (Matrix.specialUnitaryGroup (Fin (n + 1)) ℂ) 1 :=
  Quotient.map (finiteUnitarySpecialNormalizePath n)
    (fun _ _ h ↦ finiteUnitarySpecialNormalizePath_homotopic h)

/-- Inclusion from literal finite `SU` loop classes to finite-unitary loop classes. -/
def finiteSpecialUnitaryInclusionKOneMap (n : ℕ) :
    FundamentalGroup (Matrix.specialUnitaryGroup (Fin (n + 1)) ℂ) 1 →
      FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 :=
  Quotient.map (finiteSpecialUnitaryInclusionPath n)
    (fun _ _ h ↦ finiteSpecialUnitaryInclusionPath_homotopic h)

theorem finiteUnitarySpecialNormalizeInclusionKOneMap_eq (n : ℕ)
    (q : FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1) :
    finiteUnitarySpecialNormalizeInclusionKOneMap n q =
      finiteSpecialUnitaryInclusionKOneMap n
        (finiteUnitarySpecialNormalizeKOneMap n q) := by
  induction q using Path.Homotopic.Quotient.ind with
  | mk p => rfl

/-- Normalization retracts inclusion on literal finite `SU` loop classes. -/
theorem finiteUnitarySpecialNormalizeKOneMap_inclusion (n : ℕ)
    (q : FundamentalGroup (Matrix.specialUnitaryGroup (Fin (n + 1)) ℂ) 1) :
    finiteUnitarySpecialNormalizeKOneMap n
      (finiteSpecialUnitaryInclusionKOneMap n q) = q := by
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
      change Path.Homotopic.Quotient.mk
        (finiteUnitarySpecialNormalizePath n
          (finiteSpecialUnitaryInclusionPath n p)) =
        Path.Homotopic.Quotient.mk p
      apply congrArg Path.Homotopic.Quotient.mk
      ext t i j
      have ht := congrArg Subtype.val
        (specialUnitaryNormalize_toUnitary (0 : Fin (n + 1)) (p t))
      exact congrFun (congrFun ht i) j

/-- Determinant kills the included literal finite `SU` loop classes. -/
theorem finiteUnitaryDeterminantKOneMap_inclusion (n : ℕ)
    (q : FundamentalGroup (Matrix.specialUnitaryGroup (Fin (n + 1)) ℂ) 1) :
    finiteUnitaryDeterminantKOneMap n
      (finiteSpecialUnitaryInclusionKOneMap n q) = 1 := by
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
      change Path.Homotopic.Quotient.mk
        (finiteUnitaryDeterminantPath n
          (finiteSpecialUnitaryInclusionPath n p)) =
        Path.Homotopic.Quotient.mk (Path.refl 1)
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      change (unitaryDeterminantUnits (specialUnitaryToUnitary (p t)) : ℂ) = 1
      rw [unitaryDeterminantUnits_coe]
      exact (Matrix.mem_specialUnitaryGroup_iff.mp (p t).2).2

/-- Exact kernel identification: every determinant-trivial finite-unitary loop class is inclusion
of its literal normalized special-unitary loop class. -/
theorem finiteUnitaryKOne_eq_inclusion_normalize_of_determinant_eq_one (n : ℕ)
    (q : FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1)
    (hq : finiteUnitaryDeterminantKOneMap n q = 1) :
    q = finiteSpecialUnitaryInclusionKOneMap n
      (finiteUnitarySpecialNormalizeKOneMap n q) := by
  rw [← finiteUnitarySpecialNormalizeInclusionKOneMap_eq]
  exact finiteUnitaryKOne_eq_normalize_of_determinant_eq_one n q hq

@[simp] theorem finiteUnitaryDeterminantKOneMap_one (n : ℕ) :
    finiteUnitaryDeterminantKOneMap n 1 = 1 := by
  change Path.Homotopic.Quotient.mk
      (finiteUnitaryDeterminantPath n (Path.refl 1)) =
    Path.Homotopic.Quotient.mk (Path.refl 1)
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  simp [finiteUnitaryDeterminantPath, basedMapPath]

/-- Exact finite-stage obstruction: determinant is injective precisely when every literal
special-unitary loop class dies after inclusion. Since normalization retracts inclusion, this is
equivalent to `π₁(SU(n+1))` being trivial. -/
theorem finiteUnitaryDeterminantKOneMap_injective_iff_inclusion_eq_one (n : ℕ) :
    Function.Injective (finiteUnitaryDeterminantKOneMap n) ↔
      ∀ q : FundamentalGroup
        (Matrix.specialUnitaryGroup (Fin (n + 1)) ℂ) 1,
        finiteSpecialUnitaryInclusionKOneMap n q = 1 := by
  constructor
  · intro hinj q
    apply hinj
    rw [finiteUnitaryDeterminantKOneMap_inclusion,
      finiteUnitaryDeterminantKOneMap_one]
  · intro hkill x y hxy
    rw [finiteUnitaryKOne_eq_normalize_pointwiseMul_determinant n x,
      finiteUnitarySpecialNormalizeInclusionKOneMap_eq,
      hkill,
      GaloisForLFunctions.HTGeometry.fundamentalGroupPointwiseMul_one_left,
      finiteUnitaryKOne_eq_normalize_pointwiseMul_determinant n y,
      finiteUnitarySpecialNormalizeInclusionKOneMap_eq,
      hkill,
      GaloisForLFunctions.HTGeometry.fundamentalGroupPointwiseMul_one_left,
      hxy]

@[simp] theorem finiteSpecialUnitaryInclusionKOneMap_one (n : ℕ) :
    finiteSpecialUnitaryInclusionKOneMap n 1 = 1 := by
  change Path.Homotopic.Quotient.mk
      (finiteSpecialUnitaryInclusionPath n (Path.refl 1)) =
    Path.Homotopic.Quotient.mk (Path.refl 1)
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- Finite-stage determinant injectivity is exactly triviality of the literal fundamental group
of `SU(n+1)`; no surrogate winding interface remains. -/
theorem finiteUnitaryDeterminantKOneMap_injective_iff_subsingleton_specialUnitary (n : ℕ) :
    Function.Injective (finiteUnitaryDeterminantKOneMap n) ↔
      Subsingleton (FundamentalGroup
        (Matrix.specialUnitaryGroup (Fin (n + 1)) ℂ) 1) := by
  rw [finiteUnitaryDeterminantKOneMap_injective_iff_inclusion_eq_one]
  constructor
  · intro hkill
    constructor
    intro x y
    have hxy : finiteSpecialUnitaryInclusionKOneMap n x =
        finiteSpecialUnitaryInclusionKOneMap n y := by rw [hkill x, hkill y]
    have hnorm := congrArg (finiteUnitarySpecialNormalizeKOneMap n) hxy
    simpa [finiteUnitarySpecialNormalizeKOneMap_inclusion] using hnorm
  · intro hsub q
    rw [show q = 1 from hsub.elim q 1, finiteSpecialUnitaryInclusionKOneMap_one]

end

end PrimeQuasiLocalCharge
