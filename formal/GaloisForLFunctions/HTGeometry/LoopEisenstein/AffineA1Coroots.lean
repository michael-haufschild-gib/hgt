import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2WeylLifts
import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentTameNormalization

/-!
# Simple coroots of the Laurent central extension

The two simple coroots are constructed from canonical root words. The affine
coroot satisfies `h₀(a) = z(a) h₁(a⁻¹)`, fixing the sign of the central coordinate.
Together with the center, the finite coroot gives an injective two-dimensional
Cartan torus over the coefficient field.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

@[simp] theorem laurentConstantUnit_one : laurentConstantUnit F 1 = 1 :=
  map_one (Units.map ((HahnSeries.ofPowerSeries ℤ F).comp PowerSeries.C).toMonoidHom)

@[simp] theorem laurentConstantUnit_mul (a b : Fˣ) :
    laurentConstantUnit F (a * b) = laurentConstantUnit F a * laurentConstantUnit F b :=
  map_mul (Units.map ((HahnSeries.ofPowerSeries ℤ F).comp PowerSeries.C).toMonoidHom) a b

@[simp] theorem laurentConstantUnit_inv (a : Fˣ) :
    laurentConstantUnit F a⁻¹ = (laurentConstantUnit F a)⁻¹ :=
  map_inv (Units.map ((HahnSeries.ofPowerSeries ℤ F).comp PowerSeries.C).toMonoidHom) a

theorem laurentConstantUnit_injective : Function.Injective (laurentConstantUnit F) := by
  intro a b h
  simpa only [laurentTameSymbol_constant_X] using
    congrArg (fun u => laurentTameSymbol F u (laurentXUnit F)) h

/-- The extension has no torus defect on coefficient constants. -/
theorem laurentTameSymbol_constants (a b : Fˣ) :
    laurentTameSymbol F (laurentConstantUnit F a) (laurentConstantUnit F b) = 1 := by
  have hk (u : Fˣ) : laurentConstantUnit F u ∈
      (tameValHom (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))).ker := by
    rw [tameValHom_mem_ker_iff, coe_laurentConstantUnit]
    exact laurent_valuation_coe_powerSeries_eq_one_of_constantCoeff_ne_zero F
      (by simpa only [PowerSeries.constantCoeff_C] using u.ne_zero)
  rw [laurentTameSymbol,
    (tameDataOfValuation
      (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))).tame_eq_one_of_mem_ker
        (hk a) (hk b)]
  exact map_one (Units.map (ABHN.laurentSeriesResidueFieldEquiv F).toMonoidHom)

namespace LoopSL2

/-- The finite simple coroot, defined by its relative Weyl word. -/
def finiteCorootElement (a : Fˣ) : LoopSL2 F :=
  SL2SymbolExtension.weylLower (laurentTameHom F) (laurentConstantUnit F a⁻¹) *
    (SL2SymbolExtension.weylLower (laurentTameHom F) 1)⁻¹

/-- The affine simple coroot uses the lower root at degree one. -/
def affineCorootElement (a : Fˣ) : LoopSL2 F :=
  SL2SymbolExtension.weylLower (laurentTameHom F)
      (laurentConstantUnit F a * laurentXUnit F) *
    (SL2SymbolExtension.weylLower (laurentTameHom F) (laurentXUnit F))⁻¹

theorem finiteCorootElement_eq_diagonal (a : Fˣ) :
    finiteCorootElement F a = diagonalSection F (laurentConstantUnit F a) := by
  have h := SL2SymbolExtension.weylLower_relative (laurentTameHom F)
    (laurentConstantUnit F a⁻¹) 1
  rw [mul_one, milnorSym2_one_right, map_zero] at h
  have hz : SL2SymbolExtension.centralEmbedding (laurentTameHom F)
      (Multiplicative.ofAdd (0 : Additive Fˣ)) = 1 := map_one _
  rw [hz, one_mul, laurentConstantUnit_inv, inv_inv] at h
  exact h

/-- The affine simple coroot contains one positive copy of the center. -/
theorem affineCorootElement_eq_central_finite (a : Fˣ) :
    affineCorootElement F a = centralEmbedding F a * finiteCorootElement F a⁻¹ := by
  rw [finiteCorootElement_eq_diagonal, laurentConstantUnit_inv]
  have h := SL2SymbolExtension.weylLower_relative (laurentTameHom F)
    (laurentConstantUnit F a) (laurentXUnit F)
  rw [laurentTameHom_symbol, laurentTameSymbol_constant_X] at h
  exact h

/-- The finite coroot is multiplicative because the tame symbol of constants is one. -/
def finiteCoroot : Fˣ →* LoopSL2 F where
  toFun := finiteCorootElement F
  map_one' := by
    rw [finiteCorootElement_eq_diagonal, laurentConstantUnit_one]
    apply SL2SymbolExtension.ext
    · apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [diagonalSection, SL2SymbolExtension.sectionOf, sl2Diagonal]
    · rfl
  map_mul' a b := by
    simp only [finiteCorootElement_eq_diagonal, laurentConstantUnit_mul]
    rw [diagonalSection_mul, laurentTameSymbol_constants, inv_one, map_one, one_mul]

@[simp] theorem finiteCoroot_apply (a : Fˣ) :
    finiteCoroot F a = diagonalSection F (laurentConstantUnit F a) :=
  finiteCorootElement_eq_diagonal F a

private theorem central_commute (c : Fˣ) (g : LoopSL2 F) :
    centralEmbedding F c * g = g * centralEmbedding F c :=
  SL2SymbolExtension.centralEmbedding_commute
    (Multiplicative.ofAdd (Additive.ofMul c)) g

/-- Central and finite coordinates give the actual affine Cartan torus. -/
def cartanEmbedding : Fˣ × Fˣ →* LoopSL2 F where
  toFun p := centralEmbedding F p.1 * finiteCoroot F p.2
  map_one' := by
    change centralEmbedding F 1 * finiteCoroot F 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' p q := by
    change centralEmbedding F (p.1 * q.1) * finiteCoroot F (p.2 * q.2) = _
    rw [map_mul, map_mul]
    calc
      _ = centralEmbedding F p.1 * (centralEmbedding F q.1 * finiteCoroot F p.2) *
          finiteCoroot F q.2 := by simp only [mul_assoc]
      _ = centralEmbedding F p.1 * (finiteCoroot F p.2 * centralEmbedding F q.1) *
          finiteCoroot F q.2 := by rw [central_commute F q.1 (finiteCoroot F p.2)]
      _ = _ := by simp only [mul_assoc]

@[simp] theorem projection_cartanEmbedding (p : Fˣ × Fˣ) :
    projection F (cartanEmbedding F p) = sl2Diagonal (laurentConstantUnit F p.2) := by
  change projection F (centralEmbedding F p.1 * finiteCoroot F p.2) = _
  rw [map_mul, projection_centralEmbedding, one_mul, finiteCoroot_apply]
  rfl

/-- Both Cartan coordinates can be recovered uniquely from the loop-group element. -/
theorem cartanEmbedding_injective : Function.Injective (cartanEmbedding F) := by
  intro p q h
  have hb := congrArg (projection F) h
  rw [projection_cartanEmbedding, projection_cartanEmbedding] at hb
  have ha : p.2 = q.2 := laurentConstantUnit_injective F (Units.ext
    (congrArg (fun g : SL2 (LaurentSeries F) => g 0 0) hb))
  have hc : p.1 = q.1 := by
    apply centralEmbedding_injective F
    change centralEmbedding F p.1 * finiteCoroot F p.2 =
      centralEmbedding F q.1 * finiteCoroot F q.2 at h
    rw [ha] at h
    exact mul_right_cancel h
  exact Prod.ext hc ha

/-- The affine simple coroot as a multiplicative map. -/
def affineCoroot : Fˣ →* LoopSL2 F where
  toFun := affineCorootElement F
  map_one' := by
    rw [affineCorootElement_eq_central_finite, inv_one]
    change centralEmbedding F 1 * finiteCoroot F 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' a b := by
    simp only [affineCorootElement_eq_central_finite]
    change cartanEmbedding F (a * b, (a * b)⁻¹) =
      cartanEmbedding F (a, a⁻¹) * cartanEmbedding F (b, b⁻¹)
    rw [← map_mul]
    congr 1
    exact Prod.ext rfl (by
      change (a * b)⁻¹ = a⁻¹ * b⁻¹
      simp only [mul_inv_rev, mul_comm])

/-- The affine Cartan relation `h₀ = c - h₁`, expressed multiplicatively. -/
theorem affineCoroot_eq_central_finite (a : Fˣ) :
    affineCoroot F a = centralEmbedding F a * finiteCoroot F a⁻¹ :=
  affineCorootElement_eq_central_finite F a

/-- Products of the two simple coroots have central/finite coordinates `(a,b/a)`. -/
theorem simpleCoroots_eq_cartan (a b : Fˣ) :
    affineCoroot F a * finiteCoroot F b = cartanEmbedding F (a, b / a) := by
  rw [affineCoroot_eq_central_finite]
  change centralEmbedding F a * finiteCoroot F a⁻¹ * finiteCoroot F b =
    centralEmbedding F a * finiteCoroot F (b / a)
  rw [mul_assoc, ← map_mul]
  congr 2
  simp only [div_eq_mul_inv, mul_comm]

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
