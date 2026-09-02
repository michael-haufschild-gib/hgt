import GaloisForLFunctions.HTGeometry.DifferentialVariationalBuildingCarrier

open scoped Differential
open nonZeroDivisors OreLocalization

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section
variable {K : Type u} [Field K] [Differential K]

def derivativeQ : PseudoDiffOp K := numeratorRingHom (mono 1 (1 : K))

theorem derivativeQ_ne_zero : derivativeQ (K := K) ≠ 0 := by
  exact fun h => mono_one_ne_zero 1
    (numeratorRingHom_injective (h.trans (map_zero _).symm))

def derivativeQUnit : (PseudoDiffOp K)ˣ := Units.mk0 derivativeQ derivativeQ_ne_zero

def derivativeWithValUnit :
    (WithVal (pseudoDiffOpValuation (K := K)))ˣ :=
  Units.map (WithVal.equiv (pseudoDiffOpValuation (K := K))).symm.toMonoidHom
    derivativeQUnit

def completedDerivativeUnit : (CompletedPseudoDiffOp K)ˣ :=
  Units.map UniformSpace.Completion.coeRingHom.toMonoidHom derivativeWithValUnit

def completedUniformizerUnit : (CompletedPseudoDiffOp K)ˣ :=
  completedDerivativeUnit⁻¹

/-- Additive coordinate of the completed multiplicative valuation. -/
def completedPseudoDiffOpAddValue (x : CompletedPseudoDiffOp K) : WithTop ℤ :=
  Multiplicative.toAdd (completedPseudoDiffOpValuation x)

theorem completedPseudoDiffOpAddValue_derivative :
    completedPseudoDiffOpAddValue
        (completedDerivativeUnit (K := K) : CompletedPseudoDiffOp K) = (-1 : WithTop ℤ) := by
  change Multiplicative.toAdd
      (completedPseudoDiffOpValuation
        ((WithVal.toVal (pseudoDiffOpValuation (K := K)) (derivativeQ (K := K)) :
          WithVal (pseudoDiffOpValuation (K := K))) : CompletedPseudoDiffOp K)) = _
  rw [completedPseudoDiffOpValuation_apply_coe]
  exact pseudoDiffOpAddValuation_numerator_mono_one 1

theorem completedPseudoDiffOpAddValue_uniformizer :
    completedPseudoDiffOpAddValue
        (completedUniformizerUnit (K := K) : CompletedPseudoDiffOp K) = (1 : WithTop ℤ) := by
  rw [completedUniformizerUnit]
  unfold completedPseudoDiffOpAddValue
  rw [Units.val_inv_eq_inv_val]
  change Multiplicative.toAdd
      (completedPseudoDiffOpValuation
        ((completedDerivativeUnit (K := K) : CompletedPseudoDiffOp K)⁻¹)) = _
  rw [Valuation.map_inv]
  change -completedPseudoDiffOpAddValue
      (completedDerivativeUnit (K := K) : CompletedPseudoDiffOp K) = (1 : WithTop ℤ)
  rw [completedPseudoDiffOpAddValue_derivative]
  rfl

theorem completedPseudoDiffOpAddValue_ne_top_of_ne_zero
    {x : CompletedPseudoDiffOp K} (hx : x ≠ 0) :
    completedPseudoDiffOpAddValue x ≠ ⊤ := by
  intro h
  have hv : completedPseudoDiffOpValuation x = 0 := h
  exact (Valuation.ne_zero_iff completedPseudoDiffOpValuation).2 hx hv

def completedPseudoDiffOpUnitAddValue (a : (CompletedPseudoDiffOp K)ˣ) : ℤ :=
  (completedPseudoDiffOpAddValue (a : CompletedPseudoDiffOp K)).untop
    (completedPseudoDiffOpAddValue_ne_top_of_ne_zero (Units.ne_zero a))

theorem completedPseudoDiffOpAddValue_unit_eq_coe
    (a : (CompletedPseudoDiffOp K)ˣ) :
    completedPseudoDiffOpAddValue (a : CompletedPseudoDiffOp K) =
      (completedPseudoDiffOpUnitAddValue a : WithTop ℤ) := by
  exact WithTop.coe_untop _ _ |>.symm

@[simp] theorem completedPseudoDiffOpAddValue_one :
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

@[simp] theorem completedPseudoDiffOpUnitAddValue_one :
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

def completedPseudoDiffOpUnitAddValueHom :
    (CompletedPseudoDiffOp K)ˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (completedPseudoDiffOpUnitAddValue a)
  map_one' := congrArg Multiplicative.ofAdd completedPseudoDiffOpUnitAddValue_one
  map_mul' a b := congrArg Multiplicative.ofAdd (completedPseudoDiffOpUnitAddValue_mul a b)

theorem completedPseudoDiffOpUnitAddValue_zpow
    (a : (CompletedPseudoDiffOp K)ˣ) (z : ℤ) :
    completedPseudoDiffOpUnitAddValue (a ^ z) =
      z * completedPseudoDiffOpUnitAddValue a := by
  have h := MonoidHom.map_zpow completedPseudoDiffOpUnitAddValueHom a z
  exact congrArg Multiplicative.toAdd h

theorem completedPseudoDiffOpUnitAddValue_uniformizer :
    completedPseudoDiffOpUnitAddValue (completedUniformizerUnit (K := K)) = 1 := by
  apply WithTop.coe_injective
  rw [← completedPseudoDiffOpAddValue_unit_eq_coe]
  exact completedPseudoDiffOpAddValue_uniformizer

theorem completedPseudoDiffOpUnitAddValue_uniformizer_zpow (z : ℤ) :
    completedPseudoDiffOpUnitAddValue
        (completedUniformizerUnit (K := K) ^ z) = z := by
  rw [completedPseudoDiffOpUnitAddValue_zpow,
    completedPseudoDiffOpUnitAddValue_uniformizer, mul_one]

theorem mem_completedPseudoDiffOpInteger_iff_addValue_nonneg
    (x : CompletedPseudoDiffOp K) :
    x ∈ CompletedPseudoDiffOpInteger (K := K) ↔ 0 ≤ completedPseudoDiffOpAddValue x := by
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

theorem mapCompletedPseudoRingEquiv_derivative (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    mapCompletedPseudoRingEquiv σ hσ
        (completedDerivativeUnit (K := K) : CompletedPseudoDiffOp K) =
      (completedDerivativeUnit (K := K) : CompletedPseudoDiffOp K) := by
  change mapCompletedPseudoRingEquiv σ hσ
      ((WithVal.toVal (pseudoDiffOpValuation (K := K)) (derivativeQ (K := K)) :
        WithVal (pseudoDiffOpValuation (K := K))) : CompletedPseudoDiffOp K) = _
  rw [mapCompletedPseudoRingEquiv_coe]
  apply congrArg (fun x : WithVal (pseudoDiffOpValuation (K := K)) =>
    (x : CompletedPseudoDiffOp K))
  apply WithVal.ofVal_injective
  change mapPseudoRingEquiv σ hσ (derivativeQ (K := K)) = derivativeQ (K := K)
  rw [derivativeQ, mapPseudoRingEquiv_numerator]
  congr 1
  ext n
  rw [mapRingEquiv_apply, coeff_map]
  by_cases hn : 1 = n
  · subst n
    simp
  · have hc : coeff (mono 1 (1 : K)) n = 0 := coeff_mono_of_ne (1 : K) hn
    rw [hc, map_zero]

theorem mapCompletedPseudoDiffOpUnit_derivative (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    mapCompletedPseudoDiffOpUnit σ hσ (completedDerivativeUnit (K := K)) =
      completedDerivativeUnit (K := K) := by
  apply Units.ext
  exact mapCompletedPseudoRingEquiv_derivative σ hσ

theorem mapCompletedPseudoDiffOpUnit_uniformizer (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) :
    mapCompletedPseudoDiffOpUnit σ hσ (completedUniformizerUnit (K := K)) =
      completedUniformizerUnit (K := K) := by
  rw [completedUniformizerUnit, map_inv, mapCompletedPseudoDiffOpUnit_derivative]

variable {ι : Type*}

def diagonalRightMulIntegerVecLinearEquiv (a : ι → (CompletedPseudoDiffOp K)ˣ) :
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

def diagonalRightMulVecLinearEquiv (a : ι → (CompletedPseudoDiffOp K)ˣ) :
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

def diagonalScaleLattice (a : ι → (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) : CompletedPseudoDiffOpLattice K ι where
  carrier := L.carrier.map (diagonalRightMulIntegerVecLinearEquiv a).toLinearMap
  fg := L.fg.map (diagonalRightMulIntegerVecLinearEquiv a).toLinearMap
  full := by
    rw [Submodule.eq_top_iff']
    intro y
    let x := (diagonalRightMulVecLinearEquiv a).symm y
    have hx : x ∈ Submodule.span (CompletedPseudoDiffOp K)
        (L.carrier : Set (ι → CompletedPseudoDiffOp K)) := by
      rw [L.full]
      trivial
    have himage : diagonalRightMulVecLinearEquiv a x ∈
        Submodule.map (diagonalRightMulVecLinearEquiv a).toLinearMap
          (Submodule.span (CompletedPseudoDiffOp K)
            (L.carrier : Set (ι → CompletedPseudoDiffOp K))) := ⟨x, hx, rfl⟩
    rw [Submodule.map_span] at himage
    have hsubset : diagonalRightMulVecLinearEquiv a ''
          (L.carrier : Set (ι → CompletedPseudoDiffOp K)) ⊆
        (L.carrier.map (diagonalRightMulIntegerVecLinearEquiv a).toLinearMap :
          Set (ι → CompletedPseudoDiffOp K)) := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    have hy := Submodule.span_mono hsubset himage
    simpa [x] using hy

theorem mem_diagonalScaleLattice_iff (a : ι → (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) (y : ι → CompletedPseudoDiffOp K) :
    y ∈ (diagonalScaleLattice a L).carrier ↔
      ∃ x ∈ L.carrier, diagonalRightMulIntegerVecLinearEquiv a x = y := by
  constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, rfl⟩

theorem diagonalScaleLattice_mul (a b : ι → (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) :
    diagonalScaleLattice b (diagonalScaleLattice a L) =
      diagonalScaleLattice (a * b) L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  simp only [mem_diagonalScaleLattice_iff]
  constructor
  · rintro ⟨z, ⟨x, hx, hzx⟩, hyz⟩
    refine ⟨x, hx, ?_⟩
    rw [← hyz, ← hzx]
    funext i
    exact (mul_assoc (x i) (a i) (b i)).symm
  · rintro ⟨x, hx, hyx⟩
    let z := diagonalRightMulIntegerVecLinearEquiv a x
    refine ⟨z, ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyx]
    funext i
    exact mul_assoc (x i) (a i) (b i)

theorem diagonalScaleLattice_const (a : (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) :
    diagonalScaleLattice (fun _ => a) L = rightScaleCompletedPseudoDiffOpLattice a L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_diagonalScaleLattice_iff, mem_rightScaleCompletedPseudoDiffOpLattice_iff]
  rfl

def uniformizerCoweight (m : ι → ℤ) : ι → (CompletedPseudoDiffOp K)ˣ :=
  fun i => completedUniformizerUnit (K := K) ^ m i

theorem uniformizerCoweight_add (m n : ι → ℤ) :
    uniformizerCoweight (K := K) (m + n) =
      uniformizerCoweight m * uniformizerCoweight n := by
  funext i
  exact zpow_add _ _ _

variable [Fintype ι]

def standardLatticeAtCoweight (m : ι → ℤ) : CompletedPseudoDiffOpLattice K ι :=
  diagonalScaleLattice (uniformizerCoweight m)
    (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι))

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

theorem mem_standardLatticeAtCoweight_iff (m : ι → ℤ)
    (y : ι → CompletedPseudoDiffOp K) :
    y ∈ (standardLatticeAtCoweight (K := K) m).carrier ↔
      ∀ i, y i * ((uniformizerCoweight m i)⁻¹ :
          (CompletedPseudoDiffOp K)ˣ) ∈
        CompletedPseudoDiffOpInteger (K := K) := by
  rw [standardLatticeAtCoweight, mem_diagonalScaleLattice_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    rw [mem_standardCompletedPseudoDiffOpLattice_iff] at hx
    simpa [diagonalRightMulIntegerVecLinearEquiv, mul_assoc] using hx i
  · intro hy
    let x : ι → CompletedPseudoDiffOp K := fun i =>
      y i * ((uniformizerCoweight m i)⁻¹ : (CompletedPseudoDiffOp K)ˣ)
    refine ⟨x, ?_, ?_⟩
    · rw [mem_standardCompletedPseudoDiffOpLattice_iff]
      exact hy
    · funext i
      simp [x, diagonalRightMulIntegerVecLinearEquiv, mul_assoc]

def coweightBasisVector (m : ι → ℤ) (i : ι) : ι → CompletedPseudoDiffOp K :=
  diagonalRightMulIntegerVecLinearEquiv (uniformizerCoweight m)
    (Pi.basisFun (CompletedPseudoDiffOp K) ι i)

theorem coweightBasisVector_mem (m : ι → ℤ) (i : ι) :
    coweightBasisVector (K := K) m i ∈ (standardLatticeAtCoweight m).carrier := by
  rw [standardLatticeAtCoweight, mem_diagonalScaleLattice_iff]
  exact ⟨Pi.basisFun (CompletedPseudoDiffOp K) ι i,
    basisFun_mem_completedPseudoDiffOpIntegralCarrier i, rfl⟩

theorem coweight_le_add_unit_of_rightScale_eq (m n : ι → ℤ)
    (a : (CompletedPseudoDiffOp K)ˣ)
    (hscale : rightScaleCompletedPseudoDiffOpLattice a (standardLatticeAtCoweight m) =
      standardLatticeAtCoweight n) (i : ι) :
    n i ≤ m i + completedPseudoDiffOpUnitAddValue a := by
  classical
  let v := coweightBasisVector (K := K) m i
  have hv : v ∈ (standardLatticeAtCoweight m).carrier := coweightBasisVector_mem m i
  have hva : rightMulCompletedPseudoIntegerVecLinearEquiv (ι := ι) a v ∈
      (rightScaleCompletedPseudoDiffOpLattice a (standardLatticeAtCoweight m)).carrier :=
    (mem_rightScaleCompletedPseudoDiffOpLattice_iff a _ _).2 ⟨v, hv, rfl⟩
  rw [hscale] at hva
  have hi := (mem_standardLatticeAtCoweight_iff n _).1 hva i
  let u : (CompletedPseudoDiffOp K)ˣ :=
    completedUniformizerUnit (K := K) ^ m i * a *
      (completedUniformizerUnit (K := K) ^ n i)⁻¹
  have hu : (u : CompletedPseudoDiffOp K) ∈ CompletedPseudoDiffOpInteger (K := K) := by
    simpa [u, v, coweightBasisVector, rightMulCompletedPseudoIntegerVecLinearEquiv,
      diagonalRightMulIntegerVecLinearEquiv, uniformizerCoweight, mul_assoc] using hi
  rw [coe_unit_mem_completedPseudoDiffOpInteger_iff] at hu
  dsimp [u] at hu
  rw [completedPseudoDiffOpUnitAddValue_mul,
    completedPseudoDiffOpUnitAddValue_mul,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow,
    completedPseudoDiffOpUnitAddValue_inv,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at hu
  omega

def CoweightDiffersByConstant (m n : ι → ℤ) : Prop :=
  ∃ c : ℤ, n = m + fun _ => c

theorem standardLatticeAtCoweight_add_const (m : ι → ℤ) (c : ℤ) :
    rightScaleCompletedPseudoDiffOpLattice
        (completedUniformizerUnit (K := K) ^ c) (standardLatticeAtCoweight m) =
      standardLatticeAtCoweight (m + fun _ => c) := by
  rw [← diagonalScaleLattice_const, standardLatticeAtCoweight,
    diagonalScaleLattice_mul]
  have hconst : (fun _ : ι => completedUniformizerUnit (K := K) ^ c) =
      uniformizerCoweight (K := K) (fun _ => c) := rfl
  rw [hconst, ← uniformizerCoweight_add]
  rfl

theorem standardLattices_homothetic_iff_coweightDiffersByConstant (m n : ι → ℤ) :
    (standardLatticeAtCoweight (K := K) m).Homothetic (standardLatticeAtCoweight n) ↔
      CoweightDiffersByConstant m n := by
  constructor
  · rintro ⟨a, hscale⟩
    let c := completedPseudoDiffOpUnitAddValue a
    have hle : ∀ i, n i ≤ m i + c :=
      fun i => coweight_le_add_unit_of_rightScale_eq m n a hscale i
    have hinv : rightScaleCompletedPseudoDiffOpLattice a⁻¹ (standardLatticeAtCoweight n) =
        standardLatticeAtCoweight m := by
      calc
        rightScaleCompletedPseudoDiffOpLattice a⁻¹ (standardLatticeAtCoweight n) =
            rightScaleCompletedPseudoDiffOpLattice a⁻¹
              (rightScaleCompletedPseudoDiffOpLattice a
                (standardLatticeAtCoweight m)) := by rw [hscale]
        _ = rightScaleCompletedPseudoDiffOpLattice (a * a⁻¹)
              (standardLatticeAtCoweight m) :=
          rightScaleCompletedPseudoDiffOpLattice_mul a a⁻¹ _
        _ = standardLatticeAtCoweight m := by
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
    exact ⟨completedUniformizerUnit (K := K) ^ c,
      standardLatticeAtCoweight_add_const m c⟩

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

def coweightTranslationSetoid : Setoid (ι → ℤ) where
  r := CoweightDiffersByConstant
  iseqv := ⟨CoweightDiffersByConstant.refl, CoweightDiffersByConstant.symm,
    CoweightDiffersByConstant.trans⟩

abbrev StandardApartmentCarrier (ι : Type*) [Fintype ι] :=
  Quotient (coweightTranslationSetoid (ι := ι))

def standardApartmentMap : StandardApartmentCarrier ι →
    DifferentialVariationalBuildingCarrier K ι :=
  Quotient.map (standardLatticeAtCoweight (K := K)) (by
    intro m n h
    change CoweightDiffersByConstant m n at h
    change (standardLatticeAtCoweight (K := K) m).Homothetic
      (standardLatticeAtCoweight n)
    obtain ⟨c, rfl⟩ := h
    exact ⟨completedUniformizerUnit (K := K) ^ c,
      standardLatticeAtCoweight_add_const m c⟩)

theorem standardApartmentMap_injective :
    Function.Injective (standardApartmentMap (K := K) (ι := ι)) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ m =>
      induction y using Quotient.inductionOn with
      | _ n =>
          apply Quotient.sound
          change CoweightDiffersByConstant m n
          apply (standardLattices_homothetic_iff_coweightDiffersByConstant (K := K) m n).mp
          exact Quotient.exact hxy

theorem map_diagonalScaleLattice (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (a : ι → (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K ι) :
    mapCompletedPseudoDiffOpLattice σ hσ (diagonalScaleLattice a L) =
      diagonalScaleLattice (fun i => mapCompletedPseudoDiffOpUnit σ hσ (a i))
        (mapCompletedPseudoDiffOpLattice σ hσ L) := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_mapCompletedPseudoDiffOpLattice_iff, mem_diagonalScaleLattice_iff]
  constructor
  · rintro ⟨z, hz, hyz⟩
    rw [mem_diagonalScaleLattice_iff] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    refine ⟨mapCompletedPseudoIntegerVecLinearMap (ι := ι) σ hσ x,
      ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyz, ← hzx]
    funext i
    exact ((mapCompletedPseudoRingEquiv σ hσ).map_mul (x i) (a i)).symm
  · rintro ⟨z, hz, hyz⟩
    rw [mem_mapCompletedPseudoDiffOpLattice_iff] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    refine ⟨diagonalRightMulIntegerVecLinearEquiv a x, ⟨x, hx, rfl⟩, ?_⟩
    rw [← hyz, ← hzx]
    funext i
    exact (mapCompletedPseudoRingEquiv σ hσ).map_mul (x i) (a i)

theorem map_uniformizerCoweight (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (m : ι → ℤ) :
    (fun i => mapCompletedPseudoDiffOpUnit σ hσ (uniformizerCoweight m i)) =
      uniformizerCoweight m := by
  funext i
  rw [uniformizerCoweight, MonoidHom.map_zpow,
    mapCompletedPseudoDiffOpUnit_uniformizer]

theorem map_standardLatticeAtCoweight (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (m : ι → ℤ) :
    mapCompletedPseudoDiffOpLattice σ hσ (standardLatticeAtCoweight m) =
      standardLatticeAtCoweight m := by
  rw [standardLatticeAtCoweight, map_diagonalScaleLattice,
    map_uniformizerCoweight, map_standardCompletedPseudoDiffOpLattice]

theorem map_standardApartmentMap (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (a′) = (σ a)′) (x : StandardApartmentCarrier ι) :
    mapDifferentialVariationalBuildingCarrier σ hσ (standardApartmentMap (K := K) x) =
      standardApartmentMap x := by
  induction x using Quotient.inductionOn with
  | _ m =>
      apply Quotient.sound
      rw [map_standardLatticeAtCoweight]

end
end GaloisForLFunctions.HTGeometry.DiffOp
