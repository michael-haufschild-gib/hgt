import GaloisForLFunctions.HTGeometry.DifferentialVariationalBuildingCarrier

/-!
# Standard apartment of the differential variational building

The embedded inverse derivative `∂⁻¹` is a canonical uniformizer of the completed
pseudodifferential skew field.  Its coordinatewise integer powers move the standard valuation
lattice through the standard apartment.  Common translation of every exponent is exactly global
right homothety, so coweights modulo the diagonal translation map canonically to the building
carrier.  Differential coefficient automorphisms fix this entire apartment pointwise.
-/

open scoped Differential
open nonZeroDivisors OreLocalization

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

/-- The rational pseudodifferential derivative `∂`. -/
def pseudoDiffOpDerivative : PseudoDiffOp K := numeratorRingHom (mono 1 (1 : K))

theorem pseudoDiffOpDerivative_ne_zero : pseudoDiffOpDerivative (K := K) ≠ 0 := by
  exact fun h => mono_one_ne_zero 1
    (numeratorRingHom_injective (h.trans (map_zero _).symm))

/-- The derivative as a unit of the rational pseudodifferential division ring. -/
def pseudoDiffOpDerivativeUnit : (PseudoDiffOp K)ˣ :=
  Units.mk0 pseudoDiffOpDerivative pseudoDiffOpDerivative_ne_zero

/-- The derivative unit with its order-valued topology. -/
def pseudoDiffOpDerivativeWithValUnit :
    (WithVal (pseudoDiffOpValuation (K := K)))ˣ :=
  Units.map (WithVal.equiv (pseudoDiffOpValuation (K := K))).symm.toMonoidHom
    pseudoDiffOpDerivativeUnit

/-- The derivative unit embedded into the completed skew field. -/
def completedPseudoDiffOpDerivativeUnit : (CompletedPseudoDiffOp K)ˣ :=
  Units.map UniformSpace.Completion.coeRingHom.toMonoidHom
    pseudoDiffOpDerivativeWithValUnit

/-- Canonical uniformizer `∂⁻¹` of the completed pseudodifferential skew field. -/
def completedPseudoDiffOpUniformizerUnit : (CompletedPseudoDiffOp K)ˣ :=
  completedPseudoDiffOpDerivativeUnit⁻¹

/-- Additive coordinate of the completed multiplicative valuation. -/
def completedPseudoDiffOpAddValue (x : CompletedPseudoDiffOp K) : WithTop ℤ :=
  Multiplicative.toAdd (completedPseudoDiffOpValuation x)

/-- The embedded derivative has additive valuation `-1`. -/
theorem completedPseudoDiffOpAddValue_derivative :
    completedPseudoDiffOpAddValue
        (completedPseudoDiffOpDerivativeUnit (K := K) : CompletedPseudoDiffOp K) =
      (-1 : WithTop ℤ) := by
  change Multiplicative.toAdd
      (completedPseudoDiffOpValuation
        ((WithVal.toVal (pseudoDiffOpValuation (K := K))
          (pseudoDiffOpDerivative (K := K)) :
          WithVal (pseudoDiffOpValuation (K := K))) : CompletedPseudoDiffOp K)) = _
  rw [completedPseudoDiffOpValuation_apply_coe]
  exact pseudoDiffOpAddValuation_numerator_mono_one 1

/-- The inverse derivative is a genuine uniformizer: its additive valuation is exactly `1`. -/
theorem completedPseudoDiffOpAddValue_uniformizer :
    completedPseudoDiffOpAddValue
        (completedPseudoDiffOpUniformizerUnit (K := K) : CompletedPseudoDiffOp K) =
      (1 : WithTop ℤ) := by
  rw [completedPseudoDiffOpUniformizerUnit]
  unfold completedPseudoDiffOpAddValue
  rw [Units.val_inv_eq_inv_val]
  change Multiplicative.toAdd
      (completedPseudoDiffOpValuation
        ((completedPseudoDiffOpDerivativeUnit (K := K) : CompletedPseudoDiffOp K)⁻¹)) = _
  rw [Valuation.map_inv]
  change -completedPseudoDiffOpAddValue
      (completedPseudoDiffOpDerivativeUnit (K := K) : CompletedPseudoDiffOp K) =
        (1 : WithTop ℤ)
  rw [completedPseudoDiffOpAddValue_derivative]
  rfl

/-- A nonzero completed pseudodifferential operator has finite additive valuation. -/
theorem completedPseudoDiffOpAddValue_ne_top_of_ne_zero
    {x : CompletedPseudoDiffOp K} (hx : x ≠ 0) :
    completedPseudoDiffOpAddValue x ≠ ⊤ := by
  intro h
  have hv : completedPseudoDiffOpValuation x = 0 := h
  exact (Valuation.ne_zero_iff completedPseudoDiffOpValuation).2 hx hv

/-- Integer additive valuation of a unit of the completed skew field. -/
def completedPseudoDiffOpUnitAddValue (a : (CompletedPseudoDiffOp K)ˣ) : ℤ :=
  (completedPseudoDiffOpAddValue (a : CompletedPseudoDiffOp K)).untop
    (completedPseudoDiffOpAddValue_ne_top_of_ne_zero (Units.ne_zero a))

theorem completedPseudoDiffOpAddValue_unit_eq_coe
    (a : (CompletedPseudoDiffOp K)ˣ) :
    completedPseudoDiffOpAddValue (a : CompletedPseudoDiffOp K) =
      (completedPseudoDiffOpUnitAddValue a : WithTop ℤ) := by
  exact WithTop.coe_untop _ _ |>.symm

@[simp]
theorem completedPseudoDiffOpAddValue_one :
    completedPseudoDiffOpAddValue (1 : CompletedPseudoDiffOp K) = 0 := by
  unfold completedPseudoDiffOpAddValue
  rw [Valuation.map_one]
  rfl

theorem completedPseudoDiffOpAddValue_mul (x y : CompletedPseudoDiffOp K) :
    completedPseudoDiffOpAddValue (x * y) =
      completedPseudoDiffOpAddValue x + completedPseudoDiffOpAddValue y := by
  unfold completedPseudoDiffOpAddValue
  rw [Valuation.map_mul]
  rfl

@[simp]
theorem completedPseudoDiffOpUnitAddValue_one :
    completedPseudoDiffOpUnitAddValue (1 : (CompletedPseudoDiffOp K)ˣ) = 0 := by
  apply WithTop.coe_injective
  rw [← completedPseudoDiffOpAddValue_unit_eq_coe]
  exact completedPseudoDiffOpAddValue_one

theorem completedPseudoDiffOpUnitAddValue_mul
    (a b : (CompletedPseudoDiffOp K)ˣ) :
    completedPseudoDiffOpUnitAddValue (a * b) =
      completedPseudoDiffOpUnitAddValue a + completedPseudoDiffOpUnitAddValue b := by
  apply WithTop.coe_injective
  calc
    (completedPseudoDiffOpUnitAddValue (a * b) : WithTop ℤ) =
        completedPseudoDiffOpAddValue ((a * b : (CompletedPseudoDiffOp K)ˣ) :
          CompletedPseudoDiffOp K) :=
      (completedPseudoDiffOpAddValue_unit_eq_coe (a * b)).symm
    _ = completedPseudoDiffOpAddValue
        ((a : CompletedPseudoDiffOp K) * (b : CompletedPseudoDiffOp K)) := rfl
    _ = completedPseudoDiffOpAddValue (a : CompletedPseudoDiffOp K) +
        completedPseudoDiffOpAddValue (b : CompletedPseudoDiffOp K) :=
      completedPseudoDiffOpAddValue_mul _ _
    _ = (completedPseudoDiffOpUnitAddValue a : WithTop ℤ) +
        (completedPseudoDiffOpUnitAddValue b : WithTop ℤ) := by
      rw [completedPseudoDiffOpAddValue_unit_eq_coe,
        completedPseudoDiffOpAddValue_unit_eq_coe]
    _ = (completedPseudoDiffOpUnitAddValue a +
        completedPseudoDiffOpUnitAddValue b : ℤ) :=
      (WithTop.coe_add _ _).symm

/-- Unit valuation as a multiplicative homomorphism into the multiplicative copy of `ℤ`. -/
def completedPseudoDiffOpUnitAddValueHom :
    (CompletedPseudoDiffOp K)ˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (completedPseudoDiffOpUnitAddValue a)
  map_one' := congrArg Multiplicative.ofAdd completedPseudoDiffOpUnitAddValue_one
  map_mul' a b :=
    congrArg Multiplicative.ofAdd (completedPseudoDiffOpUnitAddValue_mul a b)

theorem completedPseudoDiffOpUnitAddValue_zpow
    (a : (CompletedPseudoDiffOp K)ˣ) (z : ℤ) :
    completedPseudoDiffOpUnitAddValue (a ^ z) =
      z * completedPseudoDiffOpUnitAddValue a := by
  have h := MonoidHom.map_zpow completedPseudoDiffOpUnitAddValueHom a z
  exact congrArg Multiplicative.toAdd h

/-- The canonical uniformizer has unit valuation coordinate one. -/
theorem completedPseudoDiffOpUnitAddValue_uniformizer :
    completedPseudoDiffOpUnitAddValue
        (completedPseudoDiffOpUniformizerUnit (K := K)) = 1 := by
  apply WithTop.coe_injective
  rw [← completedPseudoDiffOpAddValue_unit_eq_coe]
  exact completedPseudoDiffOpAddValue_uniformizer

/-- Every integral power of the canonical uniformizer has its exponent as valuation. -/
theorem completedPseudoDiffOpUnitAddValue_uniformizer_zpow (z : ℤ) :
    completedPseudoDiffOpUnitAddValue
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ z) = z := by
  rw [completedPseudoDiffOpUnitAddValue_zpow,
    completedPseudoDiffOpUnitAddValue_uniformizer, mul_one]

/-- Membership in the completed valuation ring is nonnegativity of additive valuation. -/
theorem mem_completedPseudoDiffOpInteger_iff_addValue_nonneg
    (x : CompletedPseudoDiffOp K) :
    x ∈ CompletedPseudoDiffOpInteger (K := K) ↔
      0 ≤ completedPseudoDiffOpAddValue x := by
  rw [Valuation.mem_integer_iff]
  rfl

theorem coe_unit_mem_completedPseudoDiffOpInteger_iff
    (a : (CompletedPseudoDiffOp K)ˣ) :
    (a : CompletedPseudoDiffOp K) ∈ CompletedPseudoDiffOpInteger (K := K) ↔
      0 ≤ completedPseudoDiffOpUnitAddValue a := by
  rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
    completedPseudoDiffOpAddValue_unit_eq_coe]
  norm_cast

theorem completedPseudoDiffOpUnitAddValue_inv
    (a : (CompletedPseudoDiffOp K)ˣ) :
    completedPseudoDiffOpUnitAddValue a⁻¹ = -completedPseudoDiffOpUnitAddValue a := by
  have h := completedPseudoDiffOpUnitAddValue_zpow a (-1)
  simpa using h

/-- Differential coefficient automorphisms fix the embedded derivative. -/
theorem mapCompletedPseudoRingEquiv_derivative (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    mapCompletedPseudoRingEquiv σ hσ
        (completedPseudoDiffOpDerivativeUnit (K := K) : CompletedPseudoDiffOp K) =
      (completedPseudoDiffOpDerivativeUnit (K := K) : CompletedPseudoDiffOp K) := by
  change mapCompletedPseudoRingEquiv σ hσ
      ((WithVal.toVal (pseudoDiffOpValuation (K := K))
        (pseudoDiffOpDerivative (K := K)) :
        WithVal (pseudoDiffOpValuation (K := K))) : CompletedPseudoDiffOp K) = _
  rw [mapCompletedPseudoRingEquiv_coe]
  apply congrArg (fun x : WithVal (pseudoDiffOpValuation (K := K)) =>
    (x : CompletedPseudoDiffOp K))
  apply WithVal.ofVal_injective
  change mapPseudoRingEquiv σ hσ (pseudoDiffOpDerivative (K := K)) =
    pseudoDiffOpDerivative (K := K)
  rw [pseudoDiffOpDerivative, mapPseudoRingEquiv_numerator]
  congr 1
  ext n
  rw [mapRingEquiv_apply, coeff_map]
  by_cases hn : 1 = n
  · subst n
    simp
  · have hc : coeff (mono 1 (1 : K)) n = 0 := coeff_mono_of_ne (1 : K) hn
    rw [hc, map_zero]

/-- Differential coefficient automorphisms fix the derivative unit. -/
theorem mapCompletedPseudoDiffOpUnit_derivative (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    mapCompletedPseudoDiffOpUnit σ hσ (completedPseudoDiffOpDerivativeUnit (K := K)) =
      completedPseudoDiffOpDerivativeUnit (K := K) := by
  apply Units.ext
  exact mapCompletedPseudoRingEquiv_derivative σ hσ

/-- Differential coefficient automorphisms fix the canonical uniformizer. -/
theorem mapCompletedPseudoDiffOpUnit_uniformizer (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    mapCompletedPseudoDiffOpUnit σ hσ (completedPseudoDiffOpUniformizerUnit (K := K)) =
      completedPseudoDiffOpUniformizerUnit (K := K) := by
  rw [completedPseudoDiffOpUniformizerUnit, map_inv,
    mapCompletedPseudoDiffOpUnit_derivative]

variable {ι : Type*}

/-- Coordinatewise right multiplication by nonzero skew scalars, linear over the valuation ring. -/
def diagonalRightMulCompletedPseudoIntegerVecLinearEquiv
    (a : ι → (CompletedPseudoDiffOp K)ˣ) :
    (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOpInteger (K := K)]
      (ι → CompletedPseudoDiffOp K) where
  toFun v i := v i * a i
  invFun v i := v i * (a i)⁻¹
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext i
    simp
  map_add' v w := by
    funext i
    exact add_mul (v i) (w i) (a i)
  map_smul' c v := by
    funext i
    exact mul_assoc (c : CompletedPseudoDiffOp K) (v i) (a i)

/-- Coordinatewise right multiplication by nonzero skew scalars, linear over the completed skew
field. -/
def diagonalRightMulCompletedPseudoVecLinearEquiv
    (a : ι → (CompletedPseudoDiffOp K)ˣ) :
    (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K) where
  toFun v i := v i * a i
  invFun v i := v i * (a i)⁻¹
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext i
    simp
  map_add' v w := by
    funext i
    exact add_mul (v i) (w i) (a i)
  map_smul' c v := by
    funext i
    exact mul_assoc c (v i) (a i)

/-- Diagonal right scaling preserves the finite-generation and full-span lattice conditions. -/
def diagonalScaleCompletedPseudoDiffOpLattice (a : ι → (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) : CompletedPseudoDiffOpLattice K ι where
  carrier := L.carrier.map
    (diagonalRightMulCompletedPseudoIntegerVecLinearEquiv a).toLinearMap
  fg := L.fg.map (diagonalRightMulCompletedPseudoIntegerVecLinearEquiv a).toLinearMap
  full := by
    rw [Submodule.eq_top_iff']
    intro y
    let x := (diagonalRightMulCompletedPseudoVecLinearEquiv a).symm y
    have hx : x ∈ Submodule.span (CompletedPseudoDiffOp K)
        (L.carrier : Set (ι → CompletedPseudoDiffOp K)) := by
      rw [L.full]
      trivial
    have himage : diagonalRightMulCompletedPseudoVecLinearEquiv a x ∈
        Submodule.map (diagonalRightMulCompletedPseudoVecLinearEquiv a).toLinearMap
          (Submodule.span (CompletedPseudoDiffOp K)
            (L.carrier : Set (ι → CompletedPseudoDiffOp K))) := ⟨x, hx, rfl⟩
    rw [Submodule.map_span] at himage
    have hsubset : diagonalRightMulCompletedPseudoVecLinearEquiv a ''
          (L.carrier : Set (ι → CompletedPseudoDiffOp K)) ⊆
        (L.carrier.map
            (diagonalRightMulCompletedPseudoIntegerVecLinearEquiv a).toLinearMap :
          Set (ι → CompletedPseudoDiffOp K)) := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    have hy := Submodule.span_mono hsubset himage
    simpa [x] using hy

theorem mem_diagonalScaleCompletedPseudoDiffOpLattice_iff
    (a : ι → (CompletedPseudoDiffOp K)ˣ) (L : CompletedPseudoDiffOpLattice K ι)
    (y : ι → CompletedPseudoDiffOp K) :
    y ∈ (diagonalScaleCompletedPseudoDiffOpLattice a L).carrier ↔
      ∃ x ∈ L.carrier,
        diagonalRightMulCompletedPseudoIntegerVecLinearEquiv a x = y := by
  constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, rfl⟩

/-- Successive diagonal right scalings multiply coordinatewise. -/
theorem diagonalScaleCompletedPseudoDiffOpLattice_mul
    (a b : ι → (CompletedPseudoDiffOp K)ˣ) (L : CompletedPseudoDiffOpLattice K ι) :
    diagonalScaleCompletedPseudoDiffOpLattice b
        (diagonalScaleCompletedPseudoDiffOpLattice a L) =
      diagonalScaleCompletedPseudoDiffOpLattice (a * b) L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  simp only [mem_diagonalScaleCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨z, ⟨x, hx, hzx⟩, hyz⟩
    refine ⟨x, hx, ?_⟩
    rw [← hyz, ← hzx]
    funext i
    exact (mul_assoc (x i) (a i) (b i)).symm
  · rintro ⟨x, hx, hyx⟩
    let z := diagonalRightMulCompletedPseudoIntegerVecLinearEquiv a x
    refine ⟨z, ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyx]
    funext i
    exact mul_assoc (x i) (a i) (b i)

/-- A constant diagonal scaling is global lattice homothety. -/
theorem diagonalScaleCompletedPseudoDiffOpLattice_const
    (a : (CompletedPseudoDiffOp K)ˣ) (L : CompletedPseudoDiffOpLattice K ι) :
    diagonalScaleCompletedPseudoDiffOpLattice (fun _ => a) L =
      rightScaleCompletedPseudoDiffOpLattice a L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_diagonalScaleCompletedPseudoDiffOpLattice_iff,
    mem_rightScaleCompletedPseudoDiffOpLattice_iff]
  rfl

/-- Diagonal powers of the canonical uniformizer attached to an integral coweight. -/
def completedPseudoDiffOpUniformizerCoweight (m : ι → ℤ) :
    ι → (CompletedPseudoDiffOp K)ˣ :=
  fun i => completedPseudoDiffOpUniformizerUnit (K := K) ^ m i

theorem completedPseudoDiffOpUniformizerCoweight_add (m n : ι → ℤ) :
    completedPseudoDiffOpUniformizerCoweight (K := K) (m + n) =
      completedPseudoDiffOpUniformizerCoweight m *
        completedPseudoDiffOpUniformizerCoweight n := by
  funext i
  exact zpow_add _ _ _

/-- Coefficient transport intertwines diagonal scaling coordinatewise. -/
theorem map_diagonalScaleCompletedPseudoDiffOpLattice (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (a : ι → (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) :
    mapCompletedPseudoDiffOpLattice σ hσ (diagonalScaleCompletedPseudoDiffOpLattice a L) =
      diagonalScaleCompletedPseudoDiffOpLattice
        (fun i => mapCompletedPseudoDiffOpUnit σ hσ (a i))
        (mapCompletedPseudoDiffOpLattice σ hσ L) := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_mapCompletedPseudoDiffOpLattice_iff,
    mem_diagonalScaleCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨z, hz, hyz⟩
    rw [mem_diagonalScaleCompletedPseudoDiffOpLattice_iff] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    refine ⟨mapCompletedPseudoIntegerVecLinearMap (ι := ι) σ hσ x,
      ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyz, ← hzx]
    funext i
    exact ((mapCompletedPseudoRingEquiv σ hσ).map_mul (x i) (a i)).symm
  · rintro ⟨z, hz, hyz⟩
    rw [mem_mapCompletedPseudoDiffOpLattice_iff] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    refine ⟨diagonalRightMulCompletedPseudoIntegerVecLinearEquiv a x,
      ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyz, ← hzx]
    funext i
    exact (mapCompletedPseudoRingEquiv σ hσ).map_mul (x i) (a i)

/-- Differential coefficient automorphisms fix every uniformizer coweight. -/
theorem map_completedPseudoDiffOpUniformizerCoweight (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (m : ι → ℤ) :
    (fun i => mapCompletedPseudoDiffOpUnit σ hσ
      (completedPseudoDiffOpUniformizerCoweight m i)) =
      completedPseudoDiffOpUniformizerCoweight m := by
  funext i
  rw [completedPseudoDiffOpUniformizerCoweight, MonoidHom.map_zpow,
    mapCompletedPseudoDiffOpUnit_uniformizer]

/-- Two integral coweights represent the same type-A apartment point exactly when they differ by
a common integral translation. -/
def CoweightDiffersByConstant (m n : ι → ℤ) : Prop :=
  ∃ c : ℤ, n = m + fun _ => c

theorem CoweightDiffersByConstant.refl (m : ι → ℤ) : CoweightDiffersByConstant m m := by
  refine ⟨0, ?_⟩
  funext i
  simp

theorem CoweightDiffersByConstant.symm {m n : ι → ℤ}
    (h : CoweightDiffersByConstant m n) : CoweightDiffersByConstant n m := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨-c, ?_⟩
  funext i
  simp

theorem CoweightDiffersByConstant.trans {m n p : ι → ℤ}
    (hmn : CoweightDiffersByConstant m n) (hnp : CoweightDiffersByConstant n p) :
    CoweightDiffersByConstant m p := by
  obtain ⟨c, rfl⟩ := hmn
  obtain ⟨d, rfl⟩ := hnp
  refine ⟨c + d, ?_⟩
  funext i
  simp [add_assoc]

/-- Translation setoid on integral coweights. -/
def coweightTranslationSetoid : Setoid (ι → ℤ) where
  r := CoweightDiffersByConstant
  iseqv := ⟨CoweightDiffersByConstant.refl, CoweightDiffersByConstant.symm,
    CoweightDiffersByConstant.trans⟩

variable [Fintype ι]

/-- Standard lattice moved to integral coweight `m`. -/
def standardCompletedPseudoDiffOpLatticeAtCoweight
    (m : ι → ℤ) : CompletedPseudoDiffOpLattice K ι :=
  diagonalScaleCompletedPseudoDiffOpLattice
    (completedPseudoDiffOpUniformizerCoweight m)
    (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι))

/-- Membership in the standard lattice is coordinatewise valuation-ring membership. -/
theorem mem_standardCompletedPseudoDiffOpLattice_iff
    (x : ι → CompletedPseudoDiffOp K) :
    x ∈ (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)).carrier ↔
      ∀ i, x i ∈ CompletedPseudoDiffOpInteger (K := K) := by
  constructor
  · intro hx i
    have hxi := hx i (Set.mem_univ i)
    change x i ∈ (completedPseudoDiffOpIntegerEmbedding K).range at hxi
    obtain ⟨c, hc⟩ := hxi
    rw [← hc]
    exact c.property
  · intro hx i hi
    change x i ∈ (completedPseudoDiffOpIntegerEmbedding K).range
    exact ⟨⟨x i, hx i⟩, rfl⟩

/-- Membership in a diagonal coweight lattice is the exact coordinatewise shifted-valuation
condition. -/
theorem mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff
    (m : ι → ℤ) (y : ι → CompletedPseudoDiffOp K) :
    y ∈ (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).carrier ↔
      ∀ i, y i * ((completedPseudoDiffOpUniformizerCoweight m i)⁻¹ :
          (CompletedPseudoDiffOp K)ˣ) ∈ CompletedPseudoDiffOpInteger (K := K) := by
  rw [standardCompletedPseudoDiffOpLatticeAtCoweight,
    mem_diagonalScaleCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    rw [mem_standardCompletedPseudoDiffOpLattice_iff] at hx
    simpa [diagonalRightMulCompletedPseudoIntegerVecLinearEquiv, mul_assoc] using hx i
  · intro hy
    let x : ι → CompletedPseudoDiffOp K := fun i =>
      y i * ((completedPseudoDiffOpUniformizerCoweight m i)⁻¹ :
        (CompletedPseudoDiffOp K)ˣ)
    refine ⟨x, ?_, ?_⟩
    · rw [mem_standardCompletedPseudoDiffOpLattice_iff]
      exact hy
    · funext i
      simp [x, diagonalRightMulCompletedPseudoIntegerVecLinearEquiv]

/-- Coordinate basis vector at coweight `m`. -/
def completedPseudoDiffOpCoweightBasisVector
    (m : ι → ℤ) (i : ι) : ι → CompletedPseudoDiffOp K :=
  diagonalRightMulCompletedPseudoIntegerVecLinearEquiv
    (completedPseudoDiffOpUniformizerCoweight m)
    (Pi.basisFun (CompletedPseudoDiffOp K) ι i)

theorem completedPseudoDiffOpCoweightBasisVector_mem (m : ι → ℤ) (i : ι) :
    completedPseudoDiffOpCoweightBasisVector (K := K) m i ∈
      (standardCompletedPseudoDiffOpLatticeAtCoweight m).carrier := by
  rw [standardCompletedPseudoDiffOpLatticeAtCoweight,
    mem_diagonalScaleCompletedPseudoDiffOpLattice_iff]
  exact ⟨Pi.basisFun (CompletedPseudoDiffOp K) ι i,
    basisFun_mem_completedPseudoDiffOpIntegralCarrier i, rfl⟩

/-- One inclusion forced by a global right homothety of diagonal coweight lattices. -/
theorem coweight_le_add_unit_of_rightScale_eq (m n : ι → ℤ)
    (a : (CompletedPseudoDiffOp K)ˣ)
    (hscale : rightScaleCompletedPseudoDiffOpLattice a
        (standardCompletedPseudoDiffOpLatticeAtCoweight m) =
      standardCompletedPseudoDiffOpLatticeAtCoweight n) (i : ι) :
    n i ≤ m i + completedPseudoDiffOpUnitAddValue a := by
  classical
  let v := completedPseudoDiffOpCoweightBasisVector (K := K) m i
  have hv : v ∈ (standardCompletedPseudoDiffOpLatticeAtCoweight m).carrier :=
    completedPseudoDiffOpCoweightBasisVector_mem m i
  have hva : rightMulCompletedPseudoIntegerVecLinearEquiv (ι := ι) a v ∈
      (rightScaleCompletedPseudoDiffOpLattice a
        (standardCompletedPseudoDiffOpLatticeAtCoweight m)).carrier :=
    (mem_rightScaleCompletedPseudoDiffOpLattice_iff a _ _).2 ⟨v, hv, rfl⟩
  rw [hscale] at hva
  have hi := (mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff n _).1 hva i
  let u : (CompletedPseudoDiffOp K)ˣ :=
    completedPseudoDiffOpUniformizerUnit (K := K) ^ m i * a *
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ n i)⁻¹
  have hu : (u : CompletedPseudoDiffOp K) ∈ CompletedPseudoDiffOpInteger (K := K) := by
    simpa [u, v, completedPseudoDiffOpCoweightBasisVector,
      rightMulCompletedPseudoIntegerVecLinearEquiv,
      diagonalRightMulCompletedPseudoIntegerVecLinearEquiv,
      completedPseudoDiffOpUniformizerCoweight, mul_assoc] using hi
  rw [coe_unit_mem_completedPseudoDiffOpInteger_iff] at hu
  dsimp [u] at hu
  rw [completedPseudoDiffOpUnitAddValue_mul,
    completedPseudoDiffOpUnitAddValue_mul,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow,
    completedPseudoDiffOpUnitAddValue_inv,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at hu
  omega

/-- Integral type-A coweight carrier modulo common translations. -/
abbrev DifferentialVariationalStandardApartmentCarrier (ι : Type*) [Fintype ι] :=
  Quotient (coweightTranslationSetoid (ι := ι))

/-- Every rank-one coweight differs from every other by a common translation. -/
theorem finOne_coweightDiffersByConstant (m n : Fin 1 → ℤ) :
    CoweightDiffersByConstant m n := by
  refine ⟨n 0 - m 0, ?_⟩
  funext i
  fin_cases i
  simp

/-- The type-`A₀` standard apartment has one point. -/
instance differentialVariationalStandardApartmentCarrierFinOne_subsingleton :
    Subsingleton (DifferentialVariationalStandardApartmentCarrier (Fin 1)) where
  allEq x y := by
    induction x using Quotient.inductionOn with
    | _ m =>
        induction y using Quotient.inductionOn with
        | _ n => exact Quotient.sound (finOne_coweightDiffersByConstant m n)

/-- The first nonzero balanced coweight, in rank two. -/
def rankTwoBalancedCoweight : Fin 2 → ℤ := ![1, -1]

theorem rankTwoBalancedCoweight_sum_eq_zero :
    ∑ i, rankTwoBalancedCoweight i = 0 := by
  simp [rankTwoBalancedCoweight, Fin.sum_univ_two]

theorem not_coweightDiffersByConstant_zero_rankTwoBalancedCoweight :
    ¬ CoweightDiffersByConstant (fun _ : Fin 2 => 0) rankTwoBalancedCoweight := by
  rintro ⟨c, h⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [rankTwoBalancedCoweight] at h0 h1
  omega

theorem rankTwoBalancedApartmentPoint_ne_base :
    (Quotient.mk (coweightTranslationSetoid (ι := Fin 2)) rankTwoBalancedCoweight :
        DifferentialVariationalStandardApartmentCarrier (Fin 2)) ≠
      Quotient.mk (coweightTranslationSetoid (ι := Fin 2)) (fun _ => 0) := by
  intro h
  apply not_coweightDiffersByConstant_zero_rankTwoBalancedCoweight
  exact CoweightDiffersByConstant.symm (Quotient.exact h)

/-- Adding a common coweight translates a diagonal lattice by global homothety. -/
theorem standardCompletedPseudoDiffOpLatticeAtCoweight_add_const
    (m : ι → ℤ) (c : ℤ) :
    rightScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ c)
        (standardCompletedPseudoDiffOpLatticeAtCoweight m) =
      standardCompletedPseudoDiffOpLatticeAtCoweight (m + fun _ => c) := by
  rw [← diagonalScaleCompletedPseudoDiffOpLattice_const,
    standardCompletedPseudoDiffOpLatticeAtCoweight,
    diagonalScaleCompletedPseudoDiffOpLattice_mul]
  have hconst : (fun _ : ι => completedPseudoDiffOpUniformizerUnit (K := K) ^ c) =
      completedPseudoDiffOpUniformizerCoweight (K := K) (fun _ => c) := rfl
  rw [hconst, ← completedPseudoDiffOpUniformizerCoweight_add]
  rfl

/-- Exact diagonal classification: two coweight lattices are homothetic precisely when their
weights differ by one common integer. -/
theorem standardCompletedPseudoDiffOpLattices_homothetic_iff_coweightDiffersByConstant
    (m n : ι → ℤ) :
    (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).Homothetic
        (standardCompletedPseudoDiffOpLatticeAtCoweight n) ↔
      CoweightDiffersByConstant m n := by
  constructor
  · rintro ⟨a, hscale⟩
    let c := completedPseudoDiffOpUnitAddValue a
    have hle : ∀ i, n i ≤ m i + c :=
      fun i => coweight_le_add_unit_of_rightScale_eq m n a hscale i
    have hinv : rightScaleCompletedPseudoDiffOpLattice a⁻¹
        (standardCompletedPseudoDiffOpLatticeAtCoweight n) =
          standardCompletedPseudoDiffOpLatticeAtCoweight m := by
      calc
        rightScaleCompletedPseudoDiffOpLattice a⁻¹
            (standardCompletedPseudoDiffOpLatticeAtCoweight n) =
          rightScaleCompletedPseudoDiffOpLattice a⁻¹
            (rightScaleCompletedPseudoDiffOpLattice a
              (standardCompletedPseudoDiffOpLatticeAtCoweight m)) := by rw [hscale]
        _ = rightScaleCompletedPseudoDiffOpLattice (a * a⁻¹)
              (standardCompletedPseudoDiffOpLatticeAtCoweight m) :=
          rightScaleCompletedPseudoDiffOpLattice_mul a a⁻¹ _
        _ = standardCompletedPseudoDiffOpLatticeAtCoweight m := by
          rw [show a * a⁻¹ = 1 by simp, rightScaleCompletedPseudoDiffOpLattice_one]
    have hge : ∀ i, m i ≤ n i - c := by
      intro i
      have h := coweight_le_add_unit_of_rightScale_eq n m a⁻¹ hinv i
      rw [completedPseudoDiffOpUnitAddValue_inv] at h
      exact h
    refine ⟨c, ?_⟩
    funext i
    dsimp
    have h1 := hle i
    have h2 := hge i
    omega
  · rintro ⟨c, rfl⟩
    exact ⟨completedPseudoDiffOpUniformizerUnit (K := K) ^ c,
      standardCompletedPseudoDiffOpLatticeAtCoweight_add_const m c⟩

/-- Canonical standard-apartment map into the homothety-class building carrier. -/
def differentialVariationalStandardApartmentMap :
    DifferentialVariationalStandardApartmentCarrier ι →
      DifferentialVariationalBuildingCarrier K ι :=
  Quotient.map (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)) (by
    intro m n h
    change CoweightDiffersByConstant m n at h
    change (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).Homothetic
      (standardCompletedPseudoDiffOpLatticeAtCoweight n)
    obtain ⟨c, rfl⟩ := h
    exact ⟨completedPseudoDiffOpUniformizerUnit (K := K) ^ c,
      standardCompletedPseudoDiffOpLatticeAtCoweight_add_const m c⟩)

/-- Standard-apartment map is injective: no coweight identifications occur beyond common
translation. -/
theorem differentialVariationalStandardApartmentMap_injective :
    Function.Injective
      (differentialVariationalStandardApartmentMap (K := K) (ι := ι)) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ m =>
      induction y using Quotient.inductionOn with
      | _ n =>
          apply Quotient.sound
          change CoweightDiffersByConstant m n
          apply
            (standardCompletedPseudoDiffOpLattices_homothetic_iff_coweightDiffersByConstant
              (K := K) m n).mp
          exact Quotient.exact hxy

/-- Rank two contains a non-base balanced building point. -/
theorem rankTwoBalancedBuildingPoint_ne_base :
    differentialVariationalStandardApartmentMap (K := K)
        (Quotient.mk (coweightTranslationSetoid (ι := Fin 2)) rankTwoBalancedCoweight) ≠
      differentialVariationalStandardApartmentMap
        (Quotient.mk (coweightTranslationSetoid (ι := Fin 2)) (fun _ => 0)) := by
  intro h
  exact rankTwoBalancedApartmentPoint_ne_base
    (differentialVariationalStandardApartmentMap_injective h)

/-- Differential coefficient automorphisms fix every diagonal coweight lattice. -/
theorem map_standardCompletedPseudoDiffOpLatticeAtCoweight (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (m : ι → ℤ) :
    mapCompletedPseudoDiffOpLattice σ hσ
        (standardCompletedPseudoDiffOpLatticeAtCoweight m) =
      standardCompletedPseudoDiffOpLatticeAtCoweight m := by
  rw [standardCompletedPseudoDiffOpLatticeAtCoweight,
    map_diagonalScaleCompletedPseudoDiffOpLattice,
    map_completedPseudoDiffOpUniformizerCoweight,
    map_standardCompletedPseudoDiffOpLattice]

/-- Differential coefficient automorphisms fix the standard apartment pointwise. -/
theorem map_differentialVariationalStandardApartmentMap (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (x : DifferentialVariationalStandardApartmentCarrier ι) :
    mapDifferentialVariationalBuildingCarrier σ hσ
        (differentialVariationalStandardApartmentMap (K := K) x) =
      differentialVariationalStandardApartmentMap x := by
  induction x using Quotient.inductionOn with
  | _ m =>
      apply Quotient.sound
      rw [map_standardCompletedPseudoDiffOpLatticeAtCoweight]

end

end DiffOp

end GaloisForLFunctions.HTGeometry
