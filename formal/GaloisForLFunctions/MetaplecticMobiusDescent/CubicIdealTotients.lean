/-
Ideal totient cardinalities adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicAdmissibleResidueCounts

/-!
# Ideal totient powers and Chinese remainders

Fibres of quotient homomorphisms give the exact cardinality of unit lifts.
Consequently `φ(I^(n+1))=N(I)^n φ(I)` for nonzero ideals, and coprime
products split multiplicatively. Cubic residue counts inherit these laws.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

private def predicateFiberEquiv {R S : Type*} (f : R → S) (P : S → Prop) :
    {x : R // P (f x)} ≃ Σ y : {y : S // P y}, {x : R // f x=y.1} where
  toFun x := ⟨⟨f x.1,x.2⟩,⟨x.1,rfl⟩⟩
  invFun y := ⟨y.2.1,by rw [y.2.2]; exact y.1.2⟩
  left_inv x := rfl
  right_inv y := by
    rcases y with ⟨⟨y,hy⟩,x,hx⟩
    dsimp at hx
    cases hx
    rfl

private def predicateKernelEquiv {R S : Type*} [AddGroup R] [AddGroup S]
    (f : R →+ S) (hf : Function.Surjective f) (P : S → Prop) :
    {x : R // P (f x)} ≃ {y : S // P y} × f.ker :=
  (predicateFiberEquiv f P).trans
    ((Equiv.sigmaCongrRight (fun y : {y : S // P y} =>
      AddMonoidHom.fiberEquivKerOfSurjective hf y.1)).trans (Equiv.sigmaEquivProd _ _))

lemma card_ring_eq_card_mul_kernel {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) :
    Nat.card R=Nat.card S*Nat.card f.toAddMonoidHom.ker := by
  have h := Nat.card_congr (predicateKernelEquiv f.toAddMonoidHom hf (fun _ => True))
  simpa only [Nat.card_prod,Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => True.intro))] using h

lemma card_units_eq_card_mul_kernel {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hunit : ∀x, IsUnit (f x) ↔ IsUnit x) :
    Nat.card Rˣ=Nat.card Sˣ*Nat.card f.toAddMonoidHom.ker := by
  let e : Rˣ ≃ {x : R // IsUnit (f x)} :=
    (unitsSubtypeEquiv R).trans (Equiv.subtypeEquivRight (fun x => (hunit x).symm))
  calc
    _ = Nat.card ({y : S // IsUnit y} × f.toAddMonoidHom.ker) :=
      Nat.card_congr (e.trans (predicateKernelEquiv f.toAddMonoidHom hf IsUnit))
    _ = Nat.card {y : S // IsUnit y} * Nat.card f.toAddMonoidHom.ker := Nat.card_prod _ _
    _ = _ := by rw [← Nat.card_congr (unitsSubtypeEquiv S)]

lemma card_units_mul_card_target {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hunit : ∀x, IsUnit (f x) ↔ IsUnit x) :
    Nat.card S*Nat.card Rˣ=Nat.card R*Nat.card Sˣ := by
  rw [card_units_eq_card_mul_kernel f hf hunit,card_ring_eq_card_mul_kernel f hf]
  ring

theorem idealTotient_pow_succ (I : Ideal O) (hI : I ≠ 0) (n : ℕ) :
    idealTotient (I^(n+1))=Ideal.absNorm I^n*idealTotient I := by
  let f : (O ⧸ I^(n+1)) →+* (O ⧸ I) :=
    Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero n))
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective _
  have hu (x : O ⧸ I^(n+1)) : IsUnit (f x) ↔ IsUnit x := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk I (Nat.succ_ne_zero n)).symm
  have h := card_units_mul_card_target f hf hu
  change Ideal.absNorm I*idealTotient (I^(n+1))=
    Ideal.absNorm (I^(n+1))*idealTotient I at h
  rw [map_pow] at h
  have hpos : 0<Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    _ = Ideal.absNorm I^(n+1)*idealTotient I := h
    _ = _ := by ring

theorem idealTotient_cube (I : Ideal O) (hI : I ≠ 0) :
    idealTotient (I^3)=Ideal.absNorm I^2*idealTotient I :=
  idealTotient_pow_succ I hI 2

def unitsRingEquiv {R S : Type*} [Monoid R] [Monoid S] (e : R ≃* S) : Rˣ ≃ Sˣ :=
  (unitsSubtypeEquiv R).trans
    ((e.toEquiv.subtypeEquiv (fun _x => (MulEquiv.isUnit_map e).symm)).trans
      (unitsSubtypeEquiv S).symm)

theorem idealTotient_mul (I J : Ideal O) (hIJ : IsCoprime I J) :
    idealTotient (I*J)=idealTotient I*idealTotient J := by
  change Nat.card (O ⧸ I*J)ˣ=Nat.card (O ⧸ I)ˣ*Nat.card (O ⧸ J)ˣ
  calc
    _ = Nat.card ((O ⧸ I)ˣ × (O ⧸ J)ˣ) :=
      Nat.card_congr ((unitsRingEquiv
        (Ideal.quotientMulEquivQuotientProd I J hIJ).toMulEquiv).trans MulEquiv.prodUnits.toEquiv)
    _ = _ := Nat.card_prod _ _

theorem card_admissible_cube_product (n : ℕ) (a : O) (ha : a ≠ 0)
    (hcop : IsCoprime a (3:O)) :
    Nat.card (AdmissibleResidue (lambda^(3*n)*a^3)) =
      3^(3*n)*Ideal.absNorm (Ideal.span {a})^2*idealTotient (Ideal.span {a}) := by
  rw [card_admissible_lambda_pow_mul (3*n) (a^3) hcop.pow_left,
    ← Ideal.span_singleton_pow,idealTotient_cube _ (Ideal.span_singleton_eq_bot.not.mpr ha)]
  ring


#print axioms idealTotient_pow_succ
#print axioms idealTotient_mul
#print axioms card_admissible_cube_product
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
