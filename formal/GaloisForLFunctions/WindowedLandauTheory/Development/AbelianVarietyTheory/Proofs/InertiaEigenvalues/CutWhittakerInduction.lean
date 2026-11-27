import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDerivativeTrace
import GaloisForLFunctions.RHTower.Artin.ArtinMonomialSpan

/-! The character induced from a Whittaker character with one simple root
omitted is the Harish–Chandra product of two Gelfand–Graev characters. -/

noncomputable section
open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

private theorem inducedFunction_prod {A B : Type*} [Group A] [Group B] [Fintype A] [Fintype B]
    (H : Subgroup A) (K : Subgroup B) (f : H → ℂ) (h : K → ℂ) (x : A × B) :
    inducedFunction (H.prod K)
      (fun u => f ⟨u.val.1, u.property.1⟩ * h ⟨u.val.2, u.property.2⟩) x =
        inducedFunction H f x.1 * inducedFunction K h x.2 := by
  let e : H.prod K ≃ H × K :=
    ⟨fun u => (⟨u.val.1, u.property.1⟩, ⟨u.val.2, u.property.2⟩),
      fun u => ⟨(u.1.val, u.2.val), ⟨u.1.property, u.2.property⟩⟩,
      fun _ => rfl, fun _ => rfl⟩
  have he (y : A × B) :
      extendByZero (H.prod K) (fun u => f ⟨u.val.1, u.property.1⟩ * h ⟨u.val.2, u.property.2⟩) y =
        extendByZero H f y.1 * extendByZero K h y.2 := by
    by_cases h₁ : y.1 ∈ H <;> by_cases h₂ : y.2 ∈ K <;>
      simp [extendByZero, Subgroup.mem_prod, h₁, h₂]
  unfold inducedFunction
  simp only [he, Nat.card_congr e, Nat.card_prod, Nat.cast_mul, mul_inv]
  rw [Fintype.sum_prod_type]
  change ((Nat.card H : ℂ)⁻¹ * (Nat.card K : ℂ)⁻¹) *
    (∑ a : A, ∑ b : B, extendByZero H f (a * x.1 * a⁻¹) *
      extendByZero K h (b * x.2 * b⁻¹)) = _
  rw [← Finset.sum_mul_sum]
  ring

variable {g a b : ℕ} [Fact g.Prime]

/-- Gelfand–Graev induction gives a genuine representation character. -/
theorem isChar_gg (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : IsChar (gg ψ n) := by
  rw [gg_eq_monomialCharacter]
  let U := upperUnitriangular g n
  let θ := whittakerCharacter ψ n
  exact ⟨FDRep.of (Representation.ind U.subtype (linearCharacterRepresentation θ)), fun x =>
    (monomialGenuineCharacter_apply (Gn g n) U θ x).symm⟩

/-- Inducing the cut Whittaker character first through the two-block
parabolic gives separate Gelfand–Graev inductions in its two blocks. -/
theorem hc_gg_gg_eq_induced_cutWhittaker (ψ : AddChar (ZMod g) ℂ) :
    hc a b (gg ψ a) (gg ψ b) (a + b) =
      inducedFunction (upperUnitriangular g (a + b))
        (fun u => (cutWhittakerCharacter ψ a b u : ℂ)) := by
  let P := twoBlockParabolic g a b
  let A := upperUnitriangular g a
  let B := upperUnitriangular g b
  let U := upperUnitriangular g (a + b)
  let H := A.prod B
  let π : P →* Gn g a × Gn g b := twoBlockLevi
  let Q := H.comap π
  let f (z : H) : ℂ :=
    (whittakerCharacter ψ a ⟨z.val.1, z.property.1⟩ : ℂ) *
      (whittakerCharacter ψ b ⟨z.val.2, z.property.2⟩ : ℂ)
  let φ (x : Q) : ℂ := f ⟨π x.val, x.property⟩
  have hπ : Function.Surjective π := by
    rintro ⟨u, v⟩
    exact ⟨⟨upperBlockUnit u 0 v, inPar_upperBlockMatrix u.val 0 v.val⟩,
      twoBlockLevi_upperBlockUnit u 0 v⟩
  have h (p : P) : inducedFunction Q φ p = gg ψ a (π p).1 * gg ψ b (π p).2 := by
    rw [show inducedFunction Q φ p = inducedFunction H f (π p) from
      inducedFunction_comap π hπ H f p, gg_eq_inducedFunction, gg_eq_inducedFunction]
    exact inducedFunction_prod A B _ _ (π p)
  have hQ : Q.map P.subtype = U := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      change IsUniUp p.val.val
      rw [← upperBlockUnit_eq_of_mem_parabolic p]
      exact isUniUp_upperBlockMatrix_of_blocks _ _ _ hp.1 hp.2
    · intro hx
      let u : U := ⟨x, hx⟩
      refine ⟨⟨x, upperUnitriangular_le_twoBlockParabolic hx⟩, ?_, rfl⟩
      exact ⟨(unitriangularLevi u).1.property, (unitriangularLevi u).2.property⟩
  let θ (x : Gn g (a + b)) :=
    ψ (∑ j ∈ Finset.range (a - 1), entN (tl a x.val) j (j + 1)) *
    ψ (∑ j ∈ Finset.range (b - 1), entN (br a b x.val) j (j + 1))
  rw [hc_eq_inducedFunction, ← funext h, inducedFunction_inducedFunction]
  let e := Q.equivMapOfInjective P.subtype P.subtype_injective
  have he (z : Q.map P.subtype) : (e.symm z).val.val = z.val :=
    congrArg (fun y : Q.map P.subtype => y.val) (e.apply_symm_apply z)
  have hv (z : Q.map P.subtype) : φ (e.symm z) = θ z.val :=
    (show φ (e.symm z) = θ (e.symm z).val.val from rfl).trans (congrArg θ (he z))
  change inducedFunction (Q.map P.subtype) (fun z => φ (e.symm z)) =
    inducedFunction U (fun z => θ z.val)
  simp only [hv]
  exact congrArg (fun S : Subgroup (Gn g (a + b)) => inducedFunction S (fun z => θ z.val)) hQ

/-- Frobenius reciprocity computes the derivative multiplicity by pairing
with the Harish–Chandra product of two Gelfand–Graev characters. -/
theorem wh_der_eq_pairing_hc_gg_gg (ψ : AddChar (ZMod g) ℂ)
    (χ : Gn g (a + b) → ℂ) (hχ : IsChar χ) :
    wh ψ (der ψ a χ) =
      characterPairing (Gn g (a + b)) χ (hc a b (gg ψ a) (gg ψ b) (a + b)) := by
  let U := upperUnitriangular g (a + b)
  let θ := cutWhittakerCharacter ψ a b
  obtain ⟨V, hV⟩ := hχ
  let ρ : Representation ℂ (Gn g (a + b)) V := V.ρ
  have he : (linearCharacterRepresentation θ).character = fun u => (θ u : ℂ) :=
    funext (linearCharacterRepresentation_character θ)
  have hr : Representation.character (ρ.comp U.subtype) = fun u : U => χ u.val :=
    funext fun u => hV u.val
  have hρ : ρ.character = χ := funext hV
  have h := characterPairing_induced_restricted U.subtype (linearCharacterRepresentation θ) ρ
  rw [induced_character_eq_inducedFunction U, he, hρ, hr,
    ← hc_gg_gg_eq_induced_cutWhittaker (a := a) (b := b) ψ] at h
  change wh ψ (fun A : Gn g a => wh ψ (res a (a + b - a) χ A)) = _
  rw [Nat.add_sub_cancel_left, wh_res_wh_eq_pairing, ← h]
  exact characterPairing_comm _ _ _

end GlobalTheory.GLq
