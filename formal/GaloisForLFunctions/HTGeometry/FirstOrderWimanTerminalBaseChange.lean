import GaloisForLFunctions.HTGeometry.FirstOrderWimanTerminalStateEmbedding
import GaloisForLFunctions.HTGeometry.HahnDilation

/-!
# Functorial base change of the prescribed terminal Wiman branch

The two Laurent variables in the local Wiman branch must be reused by successive layers of the
actual cascade, rather than replaced by unrelated roots.  This module maps the algebraic inner
coefficient field into an algebraic closure of an arbitrary target field and then applies that map
coefficientwise to the outer Laurent field.  Both Laurent uniformizers, every polynomial root, and
every named coefficient are preserved exactly.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Polynomial PowerSeries

noncomputable section

/-- Extend a map from the inner Laurent field to the algebraic coefficient field used at the next
terminal stage. -/
noncomputable def firstOrderTerminalCoefficientBaseChange
    {K : Type*} [Field K] (φ : LaurentSeries ℂ →+* K) :
    FirstOrderTerminalCoefficientField →+* AlgebraicClosure K := by
  letI : Algebra (LaurentSeries ℂ) (AlgebraicClosure K) :=
    ((algebraMap K (AlgebraicClosure K)).comp φ).toAlgebra
  exact (IsAlgClosed.lift :
    FirstOrderTerminalCoefficientField →ₐ[LaurentSeries ℂ] AlgebraicClosure K).toRingHom

/-- The coefficient-field lift extends the prescribed inner Laurent map literally. -/
theorem firstOrderTerminalCoefficientBaseChange_algebraMap
    {K : Type*} [Field K] (φ : LaurentSeries ℂ →+* K) (x : LaurentSeries ℂ) :
    firstOrderTerminalCoefficientBaseChange φ
        (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField x) =
      algebraMap K (AlgebraicClosure K) (φ x) := by
  letI : Algebra (LaurentSeries ℂ) (AlgebraicClosure K) :=
    ((algebraMap K (AlgebraicClosure K)).comp φ).toAlgebra
  change (IsAlgClosed.lift :
      FirstOrderTerminalCoefficientField →ₐ[LaurentSeries ℂ] AlgebraicClosure K)
        (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField x) = _
  exact (IsAlgClosed.lift :
    FirstOrderTerminalCoefficientField →ₐ[LaurentSeries ℂ] AlgebraicClosure K).commutes x

/-- Coefficientwise base change on the outer terminal Laurent field. -/
noncomputable def firstOrderTerminalLaurentBaseChange
    {K : Type*} [Field K] (φ : LaurentSeries ℂ →+* K) :
    FirstOrderTerminalLaurentField →+* LaurentSeries (AlgebraicClosure K) :=
  hahnMapRingHom (Γ := ℤ) (firstOrderTerminalCoefficientBaseChange φ)

/-- Base change fixes the outer Laurent grade and maps only its coefficient. -/
theorem firstOrderTerminalLaurentBaseChange_single
    {K : Type*} [Field K] (φ : LaurentSeries ℂ →+* K)
    (e : ℤ) (c : FirstOrderTerminalCoefficientField) :
    firstOrderTerminalLaurentBaseChange φ (HahnSeries.single e c) =
      HahnSeries.single e (firstOrderTerminalCoefficientBaseChange φ c) := by
  exact HahnSeries.map_single (firstOrderTerminalCoefficientBaseChange φ).toZeroHom

/-- Every coefficient of an outer Laurent series is transported by the inner field lift. -/
theorem coeff_firstOrderTerminalLaurentBaseChange
    {K : Type*} [Field K] (φ : LaurentSeries ℂ →+* K)
    (x : FirstOrderTerminalLaurentField) (e : ℤ) :
    (firstOrderTerminalLaurentBaseChange φ x).coeff e =
      firstOrderTerminalCoefficientBaseChange φ (x.coeff e) := by
  exact coeff_hahnMapRingHom (firstOrderTerminalCoefficientBaseChange φ) x e

/-- Terminal Laurent base change is faithful. -/
theorem firstOrderTerminalLaurentBaseChange_injective
    {K : Type*} [Field K] (φ : LaurentSeries ℂ →+* K) :
    Function.Injective (firstOrderTerminalLaurentBaseChange φ) := by
  intro x y hxy
  ext e
  apply (firstOrderTerminalCoefficientBaseChange φ).injective
  rw [← coeff_firstOrderTerminalLaurentBaseChange φ x e,
    ← coeff_firstOrderTerminalLaurentBaseChange φ y e, hxy]

/-- Constants of the outer Laurent field are transported as constants. -/
theorem firstOrderTerminalLaurentBaseChange_algebraMap
    {K : Type*} [Field K] (φ : LaurentSeries ℂ →+* K)
    (c : FirstOrderTerminalCoefficientField) :
    firstOrderTerminalLaurentBaseChange φ
        (algebraMap FirstOrderTerminalCoefficientField
          FirstOrderTerminalLaurentField c) =
      algebraMap (AlgebraicClosure K) (LaurentSeries (AlgebraicClosure K))
        (firstOrderTerminalCoefficientBaseChange φ c) := by
  change firstOrderTerminalLaurentBaseChange φ
      (HahnSeries.ofPowerSeries ℤ FirstOrderTerminalCoefficientField
        (PowerSeries.C c)) =
    HahnSeries.ofPowerSeries ℤ (AlgebraicClosure K)
      (PowerSeries.C (firstOrderTerminalCoefficientBaseChange φ c))
  rw [HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_C,
    HahnSeries.C_apply, HahnSeries.C_apply,
    firstOrderTerminalLaurentBaseChange_single]

/-- The inner Laurent coordinate, viewed as an outer constant, is sent through the chosen inner
map and remains an outer constant. -/
theorem firstOrderTerminalLaurentBaseChange_inner_algebraMap
    {K : Type*} [Field K] (φ : LaurentSeries ℂ →+* K) (x : LaurentSeries ℂ) :
    firstOrderTerminalLaurentBaseChange φ
        (algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField
          (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField x)) =
      algebraMap (AlgebraicClosure K) (LaurentSeries (AlgebraicClosure K))
        (algebraMap K (AlgebraicClosure K) (φ x)) := by
  rw [firstOrderTerminalLaurentBaseChange_algebraMap,
    firstOrderTerminalCoefficientBaseChange_algebraMap]

/-- Polynomial roots survive terminal Laurent base change exactly. -/
theorem firstOrderTerminalLaurentBaseChange_isRoot
    {K : Type*} [Field K] (φ : LaurentSeries ℂ →+* K)
    {p : Polynomial FirstOrderTerminalLaurentField}
    {x : FirstOrderTerminalLaurentField} (hx : p.IsRoot x) :
    (p.map (firstOrderTerminalLaurentBaseChange φ)).IsRoot
      (firstOrderTerminalLaurentBaseChange φ x) :=
  hx.map

/-- A named outer coefficient remains the corresponding lifted coefficient after base change. -/
theorem coeff_firstOrderTerminalLaurentBaseChange_eq
    {K : Type*} [Field K] (φ : LaurentSeries ℂ →+* K)
    (x : FirstOrderTerminalLaurentField) (e : ℤ)
    (c : FirstOrderTerminalCoefficientField) (hxe : x.coeff e = c) :
    (firstOrderTerminalLaurentBaseChange φ x).coeff e =
      firstOrderTerminalCoefficientBaseChange φ c := by
  rw [coeff_firstOrderTerminalLaurentBaseChange, hxe]

end


end GaloisForLFunctions.HTGeometry
