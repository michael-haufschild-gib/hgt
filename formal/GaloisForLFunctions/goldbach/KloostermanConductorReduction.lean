import GaloisForLFunctions.RHTower.KloostermanComposite
import GaloisForLFunctions.RHTower.QuadraticGaussSumFourthPower
import GaloisForLFunctions.RHTower.WeilKloostermanArtinSchreier
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic

/-!
# Removing a common factor from a Kloosterman phase

Unit reduction has constant fibres. A phase whose two coefficients share
the modulus factor descends to the smaller modulus, with exactly that
fibre multiplicity. Quotient labels bound the multiplicity by the factor.
-/

namespace GaloisForLFunctions.Goldbach

open Finset RHTower.Sieve
open scoped BigOperators

noncomputable section
set_option autoImplicit false

/-- Reduction from the product modulus to its first positive factor. -/
def kloostermanUnitReduction (q d : ℕ+) :
    (ZMod ((q : ℕ) * (d : ℕ)))ˣ →* (ZMod (q : ℕ))ˣ :=
  ZMod.unitsMap (dvd_mul_right (q : ℕ) (d : ℕ))

/-- The exact multiplicity of a unit lifted through modulus reduction. -/
def kloostermanLiftMultiplicity (q d : ℕ+) : ℕ :=
  Fintype.card (kloostermanUnitReduction q d).ker

theorem kloostermanUnitReduction_surjective (q d : ℕ+) :
    Function.Surjective (kloostermanUnitReduction q d) :=
  ZMod.unitsMap_surjective (dvd_mul_right (q : ℕ) (d : ℕ))

/-- A lifted unit is determined by its residue and its quotient label. -/
theorem kloostermanLiftMultiplicity_le (q d : ℕ+) :
    kloostermanLiftMultiplicity q d ≤ (d : ℕ) := by
  let N : ℕ := (q : ℕ) * (d : ℕ)
  let f : (kloostermanUnitReduction q d).ker → Fin (d : ℕ) := fun u =>
    ⟨((u.1 : ZMod N).val / (q : ℕ)),
      Nat.div_lt_of_lt_mul (ZMod.val_lt (u.1 : ZMod N))⟩
  have hf : Function.Injective f := by
    intro u v huv
    have hquot : (u.1 : ZMod N).val / (q : ℕ) =
        (v.1 : ZMod N).val / (q : ℕ) := congrArg Fin.val huv
    have hred : kloostermanUnitReduction q d u.1 =
        kloostermanUnitReduction q d v.1 := u.2.trans v.2.symm
    have hcast : (((u.1 : ZMod N).val : ℕ) : ZMod (q : ℕ)) =
        (((v.1 : ZMod N).val : ℕ) : ZMod (q : ℕ)) := by
      have hval := congrArg Units.val hred
      change ZMod.castHom (dvd_mul_right (q : ℕ) (d : ℕ)) (ZMod (q : ℕ))
          (u.1 : ZMod N) =
        ZMod.castHom (dvd_mul_right (q : ℕ) (d : ℕ)) (ZMod (q : ℕ))
          (v.1 : ZMod N) at hval
      rwa [← ZMod.natCast_zmod_val (u.1 : ZMod N),
        ← ZMod.natCast_zmod_val (v.1 : ZMod N), map_natCast, map_natCast] at hval
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ (q : ℕ)).mp hcast
    apply Subtype.ext
    apply Units.ext
    apply ZMod.val_injective
    rw [← Nat.mod_add_div (u.1 : ZMod N).val (q : ℕ),
      ← Nat.mod_add_div (v.1 : ZMod N).val (q : ℕ), hquot, hmod]
  simpa only [kloostermanLiftMultiplicity, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

/-- Multiplying the phase by the second modulus factor removes that factor. -/
theorem stdAddChar_factor_reduction (q d : ℕ+)
    (z : ZMod ((q : ℕ) * (d : ℕ))) :
    ZMod.stdAddChar (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * z) =
      ZMod.stdAddChar
        (ZMod.castHom (dvd_mul_right (q : ℕ) (d : ℕ)) (ZMod (q : ℕ)) z) := by
  have h := RHTower.HalfWeight.stdAddChar_intCast_mul
    (N := (q : ℕ) * (d : ℕ)) (d := (q : ℕ)) (e := (d : ℕ))
    (by push_cast; rfl) (z.val : ℤ)
  have hz : ZMod.castHom (dvd_mul_right (q : ℕ) (d : ℕ))
      (ZMod (q : ℕ)) z = (z.val : ZMod (q : ℕ)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  rw [hz]
  simpa only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm] using h

/-- Every observation of the reduced unit has the same exact lift multiplicity. -/
theorem sum_kloostermanUnitReduction (q d : ℕ+)
    (f : (ZMod (q : ℕ))ˣ → ℂ) :
    (∑ x : (ZMod ((q : ℕ) * (d : ℕ)))ˣ,
      f (kloostermanUnitReduction q d x)) =
        (kloostermanLiftMultiplicity q d : ℂ) * ∑ y : (ZMod (q : ℕ))ˣ, f y := by
  classical
  let π := kloostermanUnitReduction q d
  let φ : Additive (ZMod ((q : ℕ) * (d : ℕ)))ˣ →+
      Additive (ZMod (q : ℕ))ˣ :=
    { toFun := fun x => Additive.ofMul (π (Additive.toMul x))
      map_zero' := π.map_one
      map_add' := π.map_mul }
  have h := RHTower.WeilKloosterman.sum_comp_eq_card_ker_mul φ
    (fun y => f (Additive.toMul y))
  have hi : univ.image φ = univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨x, hx⟩ := kloostermanUnitReduction_surjective q d (Additive.toMul y)
    exact mem_image.mpr ⟨Additive.ofMul x, mem_univ _, hx⟩
  have hk : (univ.filter (fun x => φ x = 0)).card =
      kloostermanLiftMultiplicity q d := by
    rw [kloostermanLiftMultiplicity, Fintype.card_subtype]
    apply card_bij (fun x _ => Additive.toMul x)
    · intro x hx
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩
    · intro x _ y _ hxy
      exact hxy
    · intro y hy
      exact ⟨Additive.ofMul y,
        mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2⟩, rfl⟩
  rw [hi, hk] at h
  let EA : Additive (ZMod ((q : ℕ) * (d : ℕ)))ˣ ≃
      (ZMod ((q : ℕ) * (d : ℕ)))ˣ :=
    ⟨Additive.toMul, Additive.ofMul, fun _ => rfl, fun _ => rfl⟩
  let EB : Additive (ZMod (q : ℕ))ˣ ≃ (ZMod (q : ℕ))ˣ :=
    ⟨Additive.toMul, Additive.ofMul, fun _ => rfl, fun _ => rfl⟩
  have hsA := Fintype.sum_equiv EA (fun a => f (Additive.toMul (φ a)))
    (fun x => f (kloostermanUnitReduction q d x)) (fun _ => rfl)
  have hsB := Fintype.sum_equiv EB (fun b => f (Additive.toMul b)) f (fun _ => rfl)
  rw [hsA, hsB] at h
  simpa only [nsmul_eq_mul] using h

/-- A common coefficient factor descends with the exact unit-fibre multiplicity. -/
theorem kloostermanSum_factor_lift (q d : ℕ+) (m n : ℤ) :
    kloostermanSum ((q : ℕ) * (d : ℕ))
      (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * (m : ZMod ((q : ℕ) * (d : ℕ))))
      (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * (n : ZMod ((q : ℕ) * (d : ℕ)))) =
        (kloostermanLiftMultiplicity q d : ℂ) *
          kloostermanSum (q : ℕ) (m : ZMod (q : ℕ)) (n : ZMod (q : ℕ)) := by
  have hphase (x : (ZMod ((q : ℕ) * (d : ℕ)))ˣ) :
      kloostermanPhase ((q : ℕ) * (d : ℕ))
        (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * m)
        (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * n) x =
      kloostermanPhase (q : ℕ) m n (kloostermanUnitReduction q d x) := by
    unfold kloostermanPhase
    rw [show (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * m) * x +
        (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * n) * ↑x⁻¹ =
        ((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) *
          ((m : ZMod ((q : ℕ) * (d : ℕ))) * x + n * ↑x⁻¹) by ring]
    rw [stdAddChar_factor_reduction]
    apply congrArg ZMod.stdAddChar
    simp only [map_add, map_mul, map_intCast]
    change (m : ZMod (q : ℕ)) * ↑(kloostermanUnitReduction q d x) +
        (n : ZMod (q : ℕ)) * ↑(kloostermanUnitReduction q d x⁻¹) = _
    rw [map_inv]
  unfold kloostermanSum
  simp_rw [hphase]
  exact sum_kloostermanUnitReduction q d
    (kloostermanPhase (q : ℕ) (m : ZMod (q : ℕ)) (n : ZMod (q : ℕ)))

/-- Descending a common coefficient factor costs at most that factor. -/
theorem norm_kloostermanSum_factor_lift_le (q d : ℕ+) (m n : ℤ) :
    ‖kloostermanSum ((q : ℕ) * (d : ℕ))
      (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * (m : ZMod ((q : ℕ) * (d : ℕ))))
      (((d : ℕ) : ZMod ((q : ℕ) * (d : ℕ))) * (n : ZMod ((q : ℕ) * (d : ℕ))))‖ ≤
        (d : ℕ) * ‖kloostermanSum (q : ℕ) (m : ZMod (q : ℕ)) (n : ZMod (q : ℕ))‖ := by
  rw [kloostermanSum_factor_lift, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (kloostermanLiftMultiplicity_le q d)) (norm_nonneg _)

end
end GaloisForLFunctions.Goldbach
