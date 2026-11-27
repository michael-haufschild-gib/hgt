import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularBlockCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerClassFunctions

/-! Applying Whittaker traces on both sides of a Levi fibre is the
Whittaker pairing on the full unipotent group with the boundary root omitted. -/

noncomputable section
open GaloisForLFunctions
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

/-- The product of the two block Whittaker characters on the full unitriangular group. -/
def cutWhittakerCharacter (ψ : AddChar (ZMod g) ℂ) (a b : ℕ) :
    LinearCharacter (upperUnitriangular g (a + b)) :=
  ((whittakerCharacter ψ a).comp ((MonoidHom.fst _ _).comp unitriangularLevi)) *
  ((whittakerCharacter ψ b).comp ((MonoidHom.snd _ _).comp unitriangularLevi))

omit [Fact g.Prime] in
private theorem card_rect :
    Nat.card (Matrix (Fin a) (Fin b) (ZMod g)) = g ^ (a * b) := by
  change Nat.card (Fin a → Fin b → ZMod g) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, Nat.card_zmod, ← pow_mul, Nat.mul_comm b a]

/-- The double Whittaker trace of Harish–Chandra restriction is a single
unitriangular character pairing. -/
theorem wh_res_wh_eq_pairing (ψ : AddChar (ZMod g) ℂ) (χ : Gn g (a + b) → ℂ) :
    wh ψ (fun A => wh ψ (res a b χ A)) =
      characterPairing (upperUnitriangular g (a + b))
        (fun u => (cutWhittakerCharacter ψ a b u : ℂ)) (fun u => χ u.val) := by
  let U := upperUnitriangular g (a + b)
  let V := upperUnitriangular g a
  let W := upperUnitriangular g b
  let R := Matrix (Fin a) (Fin b) (ZMod g)
  let e : U ≃ (V × W) × R := unitriangularBlockEquiv
  let B (A : V) (D : W) (X : R) :=
    χ (upperBlockUnit A.val X D.val) * (whittakerCharacter ψ a A⁻¹ : ℂ) *
      (whittakerCharacter ψ b D⁻¹ : ℂ)
  have hc : (Nat.card U : ℂ) = (Nat.card V : ℂ) * (Nat.card W : ℂ) * (g : ℂ) ^ (a * b) := by
    rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.cast_mul, Nat.cast_mul,
      show Nat.card R = g ^ (a * b) from card_rect, Nat.cast_pow]
  have hs :
      (∑ u : U, χ u.val * (cutWhittakerCharacter ψ a b u⁻¹ : ℂ)) =
        ∑ A : V, ∑ D : W, ∑ X : R, B A D X := by
    calc
      _ = ∑ z : (V × W) × R, B z.1.1 z.1.2 z.2 := by
        symm
        refine Fintype.sum_equiv e.symm _ _ fun ⟨⟨A, D⟩, X⟩ => ?_
        change B A D X = χ (upperBlockUnit A.val X D.val) *
          (cutWhittakerCharacter ψ a b ((unitriangularBlock A X D)⁻¹) : ℂ)
        have hu := (map_inv unitriangularLevi (unitriangularBlock A X D)).trans
          (congrArg Inv.inv (unitriangularLevi_block A X D))
        change B A D X = χ (upperBlockUnit A.val X D.val) *
          ((whittakerCharacter ψ a (unitriangularLevi (unitriangularBlock A X D)⁻¹).1 : ℂ) *
            (whittakerCharacter ψ b (unitriangularLevi (unitriangularBlock A X D)⁻¹).2 : ℂ))
        rw [hu]
        exact mul_assoc _ _ _
      _ = _ := by rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [wh_eq_restricted_pairing_of_function, characterPairing, characterPairing]
  simp_rw [wh_eq_restricted_pairing_of_function, characterPairing, res_eq_sum_rectangle]
  change (Nat.card V : ℂ)⁻¹ * (∑ A : V, ((Nat.card W : ℂ)⁻¹ *
      ∑ D : W, (((g : ℂ) ^ (a * b))⁻¹ * ∑ X : R, χ (upperBlockUnit A.val X D.val)) *
        (whittakerCharacter ψ b D⁻¹ : ℂ)) * (whittakerCharacter ψ a A⁻¹ : ℂ)) =
    (Nat.card U : ℂ)⁻¹ * ∑ u : U, χ u.val * (cutWhittakerCharacter ψ a b u⁻¹ : ℂ)
  rw [hc, hs, mul_inv, mul_inv]
  simp only [Finset.mul_sum, Finset.sum_mul, B]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun D _ => Finset.sum_congr rfl fun X _ => ?_
  ring

/-- The double Whittaker trace of a derivative of a genuine character is a dimension. -/
theorem wh_der_eq_nat (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (ha : a ≤ n)
    (χ : Gn g n → ℂ) (hχ : IsChar χ) : ∃ d : ℕ, wh ψ (der ψ a χ) = d := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  change ∃ d : ℕ, wh ψ (fun A : Gn g a => wh ψ (res a (a + b - a) χ A)) = (d : ℂ)
  rw [Nat.add_sub_cancel_left, wh_res_wh_eq_pairing]
  obtain ⟨V, hV⟩ := hχ
  let U := upperUnitriangular g (a + b)
  let θ := cutWhittakerCharacter ψ a b
  let ρ : Representation ℂ U V := (V.ρ : Representation ℂ (Gn g (a + b)) V).comp U.subtype
  have hr : ρ.character = fun u : U => χ u.val := funext fun u => hV u.val
  have he : (linearCharacterRepresentation θ).character = fun u : U => (θ u : ℂ) :=
    funext (linearCharacterRepresentation_character θ)
  rw [← hr, ← he, representationCharacterPairing_eq_finrank]
  exact ⟨_, rfl⟩

private theorem res_zero_left {g n : ℕ} [Fact g.Prime] (χ : Gn g n → ℂ) (u : Gn g 0) :
    res 0 n χ u = χ := by
  funext v
  have hP (M : Mt g n) : InPar 0 M := fun i j hj _ => (Nat.not_lt_zero _ hj).elim
  have hL (M : Mt g n) : tl 0 M = (u : Mt g 0) := Subsingleton.elim _ _
  have hR (M : Mt g n) : br 0 n M = M := by
    ext i j
    simp [br, WindowedLandauTheory.MainNotions.ArithmeticCylinders.entN, i.isLt, j.isLt]
  simp only [res, Nat.zero_mul, pow_zero, inv_one, one_mul, hP, hL, hR, true_and,
    ← Units.ext_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The derivative retaining rank zero has Whittaker trace equal to the original trace. -/
theorem wh_der_zero (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (χ : Gn g n → ℂ) :
    wh ψ (der ψ 0 χ) = wh ψ χ := by
  have he : der ψ 0 χ = fun _ => wh ψ χ := by
    funext u
    simp only [der, Nat.sub_zero, res_zero_left]
  rw [he, wh_rank_zero]

end GlobalTheory.GLq
