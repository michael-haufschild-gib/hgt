import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicFourierExpansion

/-! The nonzero-frequency term of mirabolic Fourier inversion is ordinary
induction from the inverse image of the next mirabolic subgroup. -/

noncomputable section
open Matrix GaloisForLFunctions
open scoped Classical

namespace GlobalTheory.GLq

variable {g m : ℕ} [Fact g.Prime]

/-- The inverse image of the next mirabolic subgroup under the leading-block map. -/
def mirabolicInducingSubgroup (g m : ℕ) [Fact g.Prime] :
    Subgroup (mirabolicSubgroup g (m + 1)) :=
  (mirabolicSubgroup g m).comap mirabolicLevi

local notation "M" => mirabolicSubgroup g (m + 1)
local notation "K" => mirabolicInducingSubgroup g m
local notation "Col" => (Fin (m + 1) → ZMod g)

private def lastCovector (g m : ℕ) : Fin (m + 1) → ZMod g := Pi.single (Fin.last m) 1

/-- On the inducing subgroup the last coordinate of the final column is additive. -/
def mirabolicLastCharacter (ψ : AddChar (ZMod g) ℂ) : K →* ℂˣ := by
  let ρ : K →* Multiplicative (ZMod g) :=
    { toFun := fun u => Multiplicative.ofAdd (lastCovector g m ⬝ᵥ mirabolicColumn u.val)
      map_one' := by
        change lastCovector g m ⬝ᵥ mirabolicColumn (1 : M) = 0
        have h : mirabolicUnit (1 : Gn g (m + 1)) 0 = 1 := Subtype.ext mirabolicBlock_one
        rw [← h, mirabolicColumn_unit, dotProduct_zero]
      map_mul' := by
        intro u v
        let A := mirabolicLevi u.val
        let B := mirabolicLevi v.val
        let x := mirabolicColumn u.val
        let y := mirabolicColumn v.val
        have hu : mirabolicUnit A x = u.val := mirabolicCoordinates.left_inv u.val
        have hv : mirabolicUnit B y = v.val := mirabolicCoordinates.left_inv v.val
        have hxy : u.val * v.val = mirabolicUnit (A * B) (A.val.mulVec y + x) := by
          rw [← hu, ← hv, mirabolicUnit_mul]
        have hfix : lastCovector g m ᵥ* A.val = lastCovector g m := u.property
        change lastCovector g m ⬝ᵥ mirabolicColumn (u.val * v.val) =
          lastCovector g m ⬝ᵥ x + lastCovector g m ⬝ᵥ y
        rw [hxy, mirabolicColumn_unit, dotProduct_add, dotProduct_mulVec, hfix, add_comm] }
  exact (ψ.toMonoidHom.comp ρ).toHomUnits

theorem mirabolicLastCharacter_apply (ψ : AddChar (ZMod g) ℂ) (u : K) :
    (mirabolicLastCharacter ψ u : ℂ) =
      ψ (Pi.single (Fin.last m) 1 ⬝ᵥ mirabolicColumn u.val) := rfl

/-- The inducing subgroup projects to the smaller mirabolic subgroup. -/
def mirabolicInducingLevi : K →* mirabolicSubgroup g m where
  toFun x := ⟨mirabolicLevi x.val, x.property⟩
  map_one' := Subtype.ext (map_one mirabolicLevi)
  map_mul' x y := Subtype.ext (map_mul mirabolicLevi x.val y.val)

/-- Extend by the column character and induce to the next mirabolic rank. -/
def mirabolicInduce (ψ : AddChar (ZMod g) ℂ) (F : mirabolicSubgroup g m → ℂ) : M → ℂ :=
  inducedFunction K (fun x => (mirabolicLastCharacter ψ x : ℂ) * F (mirabolicInducingLevi x))

/-- The next mirabolic Fourier coefficient, evaluated at the last coordinate covector. -/
def mirabolicTail (ψ : AddChar (ZMod g) ℂ) (F : Gn g (m + 2) → ℂ) (A : Gn g (m + 1)) : ℂ :=
  mirabolicFourier ψ F A (lastCovector g m)

theorem mirabolicTail_isMirabolicClass (ψ : AddChar (ZMod g) ℂ)
    {F : Gn g (m + 2) → ℂ} (hF : IsMirabolicClass F) : IsMirabolicClass (mirabolicTail ψ F) :=
  mirabolicFourier_last_isMirabolicClass ψ hF

private def inducingCoordinates : K ≃ mirabolicSubgroup g m × Col where
  toFun x := (⟨mirabolicLevi x.val, x.property⟩, mirabolicColumn x.val)
  invFun x := ⟨mirabolicUnit x.1.val x.2,
    show mirabolicLevi (mirabolicUnit x.1.val x.2) ∈ mirabolicSubgroup g m from
      (mirabolicLevi_unit x.1.val x.2).symm ▸ x.1.property⟩
  left_inv x := Subtype.ext (mirabolicCoordinates.left_inv x.val)
  right_inv x := Prod.ext (Subtype.ext (mirabolicLevi_unit x.1.val x.2))
    (mirabolicColumn_unit x.1.val x.2)

/-- The inducing sum depends on the leading block of each conjugator.
The column above a fixed last covector contributes the given additive phase. -/
theorem mirabolicInduce_apply (ψ : AddChar (ZMod g) ℂ)
    (f₀ : mirabolicSubgroup g m → ℂ) (A : Gn g (m + 1)) (v : Col) :
    mirabolicInduce ψ f₀ (mirabolicUnit A v) =
    (Nat.card (mirabolicSubgroup g m) : ℂ)⁻¹ * ∑ B : Gn g (m + 1),
      if h : B * A * B⁻¹ ∈ mirabolicSubgroup g m then
        f₀ ⟨B * A * B⁻¹, h⟩ * ψ (Pi.single (Fin.last m) 1 ⬝ᵥ B.val.mulVec v) else 0 := by
  let φ (x : K) := (mirabolicLastCharacter ψ x : ℂ) * f₀ (mirabolicInducingLevi x)
  let f (B : Gn g (m + 1)) :=
    if h : B * A * B⁻¹ ∈ mirabolicSubgroup g m then
      f₀ ⟨B * A * B⁻¹, h⟩ * ψ (lastCovector g m ⬝ᵥ B.val.mulVec v) else 0
  let a := mirabolicUnit A v
  have hf (B : Gn g (m + 1)) (w : Col) :
      extendByZero K φ (mirabolicUnit B w * a * (mirabolicUnit B w)⁻¹) = f B := by
    let C := B * A * B⁻¹
    let z := B.val.mulVec v + w - C.val.mulVec w
    have hconj : mirabolicUnit B w * a * (mirabolicUnit B w)⁻¹ = mirabolicUnit C z :=
      Subtype.ext (mirabolicBlock_conj A B v w)
    have hm : mirabolicUnit C z ∈ K ↔ C ∈ mirabolicSubgroup g m := by
      change mirabolicLevi (mirabolicUnit C z) ∈ mirabolicSubgroup g m ↔ _
      rw [mirabolicLevi_unit]
    rw [hconj]
    by_cases hC : C ∈ mirabolicSubgroup g m
    · rw [extendByZero_of_mem _ _ (hm.mpr hC)]
      change (mirabolicLastCharacter ψ ⟨mirabolicUnit C z, hm.mpr hC⟩ : ℂ) *
        f₀ (mirabolicInducingLevi ⟨mirabolicUnit C z, hm.mpr hC⟩) = f B
      have hL : mirabolicInducingLevi ⟨mirabolicUnit C z, hm.mpr hC⟩ = ⟨C, hC⟩ :=
        Subtype.ext (mirabolicLevi_unit C z)
      have hfix : lastCovector g m ᵥ* C.val = lastCovector g m := hC
      have hz : lastCovector g m ⬝ᵥ z = lastCovector g m ⬝ᵥ B.val.mulVec v := by
        dsimp only [z]
        rw [dotProduct_sub, dotProduct_add, dotProduct_mulVec _ C.val, hfix, add_sub_cancel_right]
      rw [mirabolicLastCharacter_apply, hL]
      change ψ (lastCovector g m ⬝ᵥ mirabolicColumn (mirabolicUnit C z)) *
        f₀ ⟨C, hC⟩ = f B
      rw [mirabolicColumn_unit, hz]
      change ψ (lastCovector g m ⬝ᵥ B.val.mulVec v) * f₀ ⟨C, hC⟩ =
        if h : C ∈ mirabolicSubgroup g m then
          f₀ ⟨C, h⟩ * ψ (lastCovector g m ⬝ᵥ B.val.mulVec v) else 0
      rw [dif_pos hC, mul_comm]
    · rw [extendByZero_of_notMem _ _ (fun h => hC (hm.mp h))]
      change 0 = if h : C ∈ mirabolicSubgroup g m then
        f₀ ⟨C, h⟩ * ψ (lastCovector g m ⬝ᵥ B.val.mulVec v) else 0
      rw [dif_neg hC]
  have hsum :
      (∑ x : M, extendByZero K φ (x * a * x⁻¹)) = (Nat.card Col : ℂ) * ∑ B, f B := by
    calc
      _ = ∑ q : Gn g (m + 1) × Col, f q.1 :=
        Fintype.sum_equiv mirabolicCoordinates _ _ fun x => by
          obtain ⟨B, w, h⟩ := exists_mirabolicBlock x.property
          rw [show x = mirabolicUnit B w from Subtype.ext h]
          change _ = f (mirabolicLevi (mirabolicUnit B w))
          rw [mirabolicLevi_unit]
          exact hf B w
      _ = _ := by
        rw [Fintype.sum_prod_type, Nat.card_eq_fintype_card]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  change inducedFunction K φ a = (Nat.card (mirabolicSubgroup g m) : ℂ)⁻¹ * ∑ B, f B
  rw [inducedFunction, hsum, Nat.card_congr (inducingCoordinates (g := g) (m := m)),
    Nat.card_prod, Nat.cast_mul, mul_inv, mul_assoc,
    inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]

/-- At a diagonal block the column phase is trivial and the average is
ordinary induction from the smaller mirabolic subgroup. -/
theorem mirabolicInduce_diag (ψ : AddChar (ZMod g) ℂ)
    (f : mirabolicSubgroup g m → ℂ) (A : Gn g (m + 1)) :
    mirabolicInduce ψ f (mirabolicUnit A 0) =
      inducedFunction (mirabolicSubgroup g m) f A := by
  rw [mirabolicInduce_apply, inducedFunction]
  simp only [Matrix.mulVec_zero, dotProduct_zero, AddChar.map_zero_eq_one, mul_one]
  congr 1

/-- Mirabolic restriction is the sum of its untwisted column mean and
induction of the nonzero column Fourier coefficient. -/
theorem mirabolic_eq_mean_add_induced (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    {F : Gn g (m + 2) → ℂ} (hF : IsMirabolicClass F) (u : M) :
    F u.val = mirabolicFourier ψ F (mirabolicLevi u) 0 +
      inducedFunction K (fun x => (mirabolicLastCharacter ψ x : ℂ) * mirabolicTail ψ F
        (mirabolicLevi x.val)) u := by
  obtain ⟨A, v, h⟩ := exists_mirabolicBlock u.property
  rw [show u = mirabolicUnit A v from Subtype.ext h, mirabolicLevi_unit]
  change F (mirabolicBlock A v) = mirabolicFourier ψ F A 0 +
    mirabolicInduce ψ (fun B => mirabolicTail ψ F B.val) (mirabolicUnit A v)
  rw [mirabolicInduce_apply, mirabolicBlock_eq_fourier_average ψ hψ hF A v]
  congr 2

end GlobalTheory.GLq
