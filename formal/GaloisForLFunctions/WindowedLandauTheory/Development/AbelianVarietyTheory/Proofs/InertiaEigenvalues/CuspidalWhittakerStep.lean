import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.HarishChandraCuspidalRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColumnTranslations
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColumnWeightVectors
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCharacter
import GaloisForLFunctions.HTGeometry.AddCharFinset

/-! A Whittaker weight on the trailing block extends by one column when
the corresponding parabolic radical has no nonzero fixed vectors. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions.HTGeometry RHTower.Sieve

namespace GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

omit [Fact g.Prime] in
private theorem rho_mul_apply {n : ℕ} (V : FDRep ℂ (Gn g n)) (x y : Gn g n) (v : V) :
    V.ρ (x * y) v = V.ρ x (V.ρ y v) :=
  congrArg (fun f : Module.End ℂ V => f v) (map_mul V.ρ x y)

variable {a b : ℕ}

local notation "Col" => (Fin (a + 1) → ZMod g)
local notation "Rect" => Matrix (Fin (a + 1)) (Fin (b + 1)) (ZMod g)
local notation "U" => upperUnitriangular g (b + 1)
local notation "GL" => Gn g (a + 1 + (b + 1))

/-- Fourier projection on the first rectangle column, followed by a change of
basis in the leading block, extends the standard Whittaker weight. -/
theorem exists_extended_whittaker_vector (V : FDRep ℂ GL)
    (h0 : res (a + 1) (b + 1) V.character 1 1 = 0) (v : V) (hv : v ≠ 0)
    (hvTail : ∀ (X : Rect) (D : U), (∀ i, X i 0 = 0) →
      V.ρ (upperBlockUnit 1 X D.val) v = (whittakerCharacter ZMod.stdAddChar (b + 1) D : ℂ) • v) :
    ∃ z : V, z ≠ 0 ∧ ∀ (X : Rect) (D : U),
      V.ρ (upperBlockUnit 1 X D.val) z =
        (ZMod.stdAddChar (X (Fin.last a) 0) * (whittakerCharacter ZMod.stdAddChar (b + 1) D : ℂ)) • z := by
  let B (X : Rect) (D : U) : GL := upperBlockUnit 1 X D.val
  let C := columnTranslation g (a + 1) b
  let tailWeight (D : U) : ℂ := whittakerCharacter ZMod.stdAddChar (b + 1) D
  let S : Submodule ℂ V :=
    { carrier := {w | ∀ (X : Rect) (D : U), (∀ i, X i 0 = 0) → V.ρ (B X D) w = tailWeight D • w}
      add_mem' := fun h₁ h₂ X D hX => by rw [map_add, h₁ X D hX, h₂ X D hX, smul_add]
      zero_mem' := fun X D _ => by rw [map_zero, smul_zero]
      smul_mem' := fun c w hw X D hX => by rw [map_smul, hw X D hX, smul_comm c (tailWeight D)] }
  have hD₀ (D : U) : D.val.val 0 0 = 1 := (mem_upperUnitriangular.mp D.property 0 0).2 rfl
  have hS : ∀ x w, w ∈ S → V.ρ (C (Multiplicative.ofAdd x)) w ∈ S := by
    intro x w hw X D hX
    let c := C (Multiplicative.ofAdd x)
    obtain ⟨Y, hY, he⟩ := move_columnTranslation_left x X D.val (hD₀ D) hX
    change V.ρ (B X D) (V.ρ c w) = tailWeight D • V.ρ c w
    rw [← rho_mul_apply, show B X D * c = c * B Y D from he, rho_mul_apply,
      hw Y D hY, map_smul]
  obtain ⟨ξ, w, hw, hwS, hwC⟩ := exists_column_weight V.ρ C S hS v hv hvTail
  have hξ : ξ ≠ 0 := by
    intro h
    subst ξ
    have ht (x : Col) : V.ρ (C (Multiplicative.ofAdd x)) w = w := by
      simpa [finiteProductCharacter] using hwC x
    apply hw (eq_zero_of_leviKernel_fixed V.ρ h0 w ?_)
    intro r
    obtain ⟨X, rfl⟩ := twoBlockRadicalEquiv.surjective r
    change V.ρ (B X.toAdd 1) w = w
    obtain ⟨Y, hY, he⟩ := factor_first_column X.toAdd (1 : Gn g (b + 1)) (hD₀ (1 : U))
    rw [show B X.toAdd 1 = C (Multiplicative.ofAdd (fun i => X.toAdd i 0)) * B Y 1 from he,
      rho_mul_apply, hwS Y 1 hY]
    have hOne : tailWeight 1 = 1 := by simp [tailWeight]
    rw [hOne, one_smul, ht]
  obtain ⟨A, hA⟩ := exists_GL_with_row (Fin.last a) ξ hξ
  let L : GL := upperBlockUnit A (0 : Rect) 1
  let z : V := V.ρ L w
  have hz : z ≠ 0 := by
    intro h
    apply hw
    calc
      w = V.ρ 1 w := (congrArg (fun f : Module.End ℂ V => f w) (map_one V.ρ)).symm
      _ = V.ρ (L⁻¹ * L) w := (congrArg (fun t : GL => V.ρ t w) (inv_mul_cancel L)).symm
      _ = 0 := by rw [rho_mul_apply, show V.ρ L w = 0 from h, map_zero]
  have hzS : z ∈ S := by
    intro X D hX
    let Y : Rect := A.inv * X
    have hY (i : Fin (a + 1)) : Y i 0 = 0 := by
      simp [Y, Matrix.mul_apply, hX]
    have hAY : A.val * Y = X := by
      change A.val * (A.inv * X) = X
      rw [← Matrix.mul_assoc, A.val_inv, Matrix.one_mul]
    have he : L * B Y D = B X D * L :=
      (move_diagonal_right A Y D.val).trans
        (congrArg (fun X => B X D * L) hAY)
    change V.ρ (B X D) (V.ρ L w) = tailWeight D • V.ρ L w
    rw [← rho_mul_apply, ← he, rho_mul_apply, hwS Y D hY, map_smul]
  have hzC (x : Col) : V.ρ (C (Multiplicative.ofAdd x)) z = ZMod.stdAddChar (x (Fin.last a)) • z := by
    let y : Col := A.inv.mulVec x
    have hy : A.val.mulVec y = x := by
      change A.val.mulVec (A.inv.mulVec x) = x
      rw [Matrix.mulVec_mulVec, A.val_inv, Matrix.one_mulVec]
    have he : L * C (Multiplicative.ofAdd y) = C (Multiplicative.ofAdd x) * L :=
      (move_diagonal_column A y).trans (congrArg (fun t => C (Multiplicative.ofAdd t) * L) hy)
    have hwt : finiteProductCharacter g (a + 1) ξ y = ZMod.stdAddChar (x (Fin.last a)) := by
      rw [← congrFun hy (Fin.last a)]
      unfold finiteProductCharacter
      rw [Matrix.mulVec, dotProduct, addChar_map_finsetSum]
      exact Finset.prod_congr rfl fun j _ => congrArg ZMod.stdAddChar (congrArg (· * y j) (hA j).symm)
    change V.ρ (C (Multiplicative.ofAdd x)) (V.ρ L w) = _
    rw [← rho_mul_apply, ← he, rho_mul_apply, hwC y, hwt, map_smul]
  refine ⟨z, hz, fun X D => ?_⟩
  obtain ⟨Y, hY, he⟩ := factor_first_column X D.val (hD₀ D)
  change V.ρ (B X D) z = (ZMod.stdAddChar (X (Fin.last a) 0) * tailWeight D) • z
  rw [show B X D = C (Multiplicative.ofAdd (fun i => X i 0)) * B Y D from he,
    rho_mul_apply, hzS Y D hY, map_smul, hzC, smul_smul, mul_comm]

end GlobalTheory.GLq
