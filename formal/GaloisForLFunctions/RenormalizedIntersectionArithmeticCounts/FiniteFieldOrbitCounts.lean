import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Extension

/-!
# Independent Frobenius orbit counts

Transporter torsors give an orbit-counting identity for equivariant maps.
Normal bases identify permutation-twisted Frobenius tuples with unrestricted
base-field coordinates. The finite extension of degree equal to the acting
group order therefore has exactly q^n Frobenius-stable tuple orbits.
-/

noncomputable section
open Finset Function MulAction
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
variable {G X : Type*} [Group G] [MulAction G X]

/-- Transporters from a point to its image form a stabilizer torsor. -/
def transporterStabilizerEquiv (φ : X → X) (x : X) (h : φ x ∈ orbit G x) :
    {g : G // g • x = φ x} ≃ stabilizer G x := by
  let a := h.choose
  have ha : a • x = φ x := h.choose_spec
  exact {
    toFun := fun g => ⟨a⁻¹ * g.val, by
      change (a⁻¹ * g.val) • x = x
      rw [mul_smul, g.property, ← ha, inv_smul_smul]⟩
    invFun := fun g => ⟨a * g.val, by
      rw [mul_smul, g.property, ha]⟩
    left_inv := fun g => Subtype.ext (by simp only [mul_inv_cancel_left])
    right_inv := fun g => Subtype.ext (by simp only [inv_mul_cancel_left]) }

/-- Equivariance makes the existence of a transporter constant on every orbit. -/
theorem transporter_exists_on_orbit (φ : X →[G] X) {x y : X}
    (hy : y ∈ orbit G x) : φ y ∈ orbit G y ↔ φ x ∈ orbit G x := by
  obtain ⟨a, rfl⟩ := hy
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨a⁻¹ * b * a, ?_⟩
    change (a⁻¹ * b * a) • x = φ x
    change b • (a • x) = φ (a • x) at hb
    rw [mul_smul, mul_smul, hb, φ.map_smul, inv_smul_smul]
  · rintro ⟨b, hb⟩
    refine ⟨a * b * a⁻¹, ?_⟩
    change (a * b * a⁻¹) • (a • x) = φ (a • x)
    change b • x = φ x at hb
    rw [mul_smul, mul_smul, inv_smul_smul, hb, φ.map_smul]

/-- Actual Frobenius-compatible transporters over one orbit. -/
abbrev orbitTransporters (φ : X →[G] X) (q : Quotient (orbitRel G X)) :=
  (x : orbit G q.out) × {g : G // g • x.val = φ x.val}

/-- Every fixed orbit contributes exactly the group order to the twisted count. -/
def orbitTransportersEquiv (φ : X →[G] X) (q : Quotient (orbitRel G X))
    (h : φ q.out ∈ orbit G q.out) : orbitTransporters φ q ≃ G :=
  (Equiv.sigmaCongrRight fun (x : orbit G q.out) =>
    transporterStabilizerEquiv φ x.val ((transporter_exists_on_orbit φ x.property).mpr h)).trans
  ((Equiv.sigmaCongrRight fun (x : orbit G q.out) =>
    (stabilizerEquivStabilizerOfOrbitRel x.property).toEquiv).trans
  ((Equiv.sigmaEquivProd _ _).trans (orbitProdStabilizerEquivGroup G q.out)))

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset Function MulAction
variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]

/-- Orbits preserved by the given equivariant arithmetic map. -/
def equivariantFixedOrbits (φ : X →[G] X) : Finset (Quotient (orbitRel G X)) := by
  classical
  exact univ.filter (fun q => φ q.out ∈ orbit G q.out)

/-- Twisted Burnside counting, with all arithmetic fixed orbits retained. -/
theorem sum_card_transporters (φ : X →[G] X) :
    (∑ g : G, Nat.card {x : X // g • x = φ x}) =
      (equivariantFixedOrbits φ).card * Fintype.card G := by
  classical
  let Ω := Quotient (orbitRel G X)
  let e : (Σ g : G, {x : X // g • x = φ x}) ≃ Σ q : Ω, orbitTransporters φ q :=
    calc
      (Σ g : G, {x : X // g • x = φ x}) ≃ {gx : G × X // gx.1 • gx.2 = φ gx.2} :=
        (Equiv.subtypeProdEquivSigmaSubtype (fun (g : G) (x : X) => g • x = φ x)).symm
      _ ≃ {xg : X × G // xg.2 • xg.1 = φ xg.1} :=
        (Equiv.prodComm G X).subtypeEquiv (fun _ => Iff.rfl)
      _ ≃ Σ x : X, {g : G // g • x = φ x} :=
        Equiv.subtypeProdEquivSigmaSubtype (fun (x : X) (g : G) => g • x = φ x)
      _ ≃ Σ qx : Σ q : Ω, orbit G q.out, {g : G // g • qx.2.val = φ qx.2.val} :=
        (selfEquivSigmaOrbits G X).sigmaCongrLeft'
      _ ≃ Σ q : Ω, orbitTransporters φ q :=
        Equiv.sigmaAssoc fun (q : Ω) (x : orbit G q.out) => {g : G // g • x.val = φ x.val}
  simp only [Nat.card_eq_fintype_card]
  rw [← Fintype.card_sigma, Fintype.card_congr e, Fintype.card_sigma]
  have hc (q : Ω) : Fintype.card (orbitTransporters φ q) =
      if φ q.out ∈ orbit G q.out then Fintype.card G else 0 := by
    by_cases h : φ q.out ∈ orbit G q.out
    · rw [if_pos h]
      exact Fintype.card_congr (orbitTransportersEquiv φ q h)
    · rw [if_neg h]
      letI : IsEmpty (orbitTransporters φ q) := ⟨fun t =>
        h ((transporter_exists_on_orbit φ t.1.property).mp ⟨t.2.val, t.2.property⟩)⟩
      exact Fintype.card_eq_zero
  rw [sum_congr rfl (fun q _ => hc q), ← sum_filter, sum_const, nsmul_eq_mul]
  rfl

#print axioms transporterStabilizerEquiv
#print axioms transporter_exists_on_orbit
#print axioms orbitTransportersEquiv
#print axioms sum_card_transporters
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

noncomputable section
open Finset Module
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
variable (F E I : Type*) [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E] [Fintype I]
  [MulAction Gal(E/F) I]

/-- The actual tuples compatible with all Galois automorphisms. -/
abbrev galoisCompatibleTuples :=
  {x : I → E // ∀ (σ : Gal(E/F)) (i : I), x (σ • i) = σ (x i)}

private theorem normalBasis_map (σ τ : Gal(E/F)) :
    σ (IsGalois.normalBasis F E τ) = IsGalois.normalBasis F E (σ * τ) := by
  rw [IsGalois.normalBasis_apply τ, IsGalois.normalBasis_apply (σ * τ)]
  rfl

/-- Summing the regular Galois orbit of a coefficient tuple produces a compatible tuple. -/
def normalBasisTuple (a : I → F) : I → E := fun i =>
  ∑ σ : Gal(E/F), a (σ⁻¹ • i) • IsGalois.normalBasis F E σ

omit [Fintype I] in
private theorem normalBasisTuple_equivariant (a : I → F) (τ : Gal(E/F)) (i : I) :
    normalBasisTuple F E I a (τ • i) = τ (normalBasisTuple F E I a i) := by
  classical
  simp only [normalBasisTuple, map_sum, map_smul, normalBasis_map]
  symm
  apply Fintype.sum_equiv (Equiv.mulLeft τ)
  intro σ
  change a (σ⁻¹ • i) • IsGalois.normalBasis F E (τ * σ) =
    a ((τ * σ)⁻¹ • (τ • i)) • IsGalois.normalBasis F E (τ * σ)
  simp only [mul_inv_rev, mul_smul, inv_smul_smul]

omit [Fintype I] in
private theorem normalBasisTuple_repr (a : I → F) (i : I) (σ : Gal(E/F)) :
    (IsGalois.normalBasis F E).repr (normalBasisTuple F E I a i) σ = a (σ⁻¹ • i) := by
  classical
  simp [normalBasisTuple, Finsupp.single_apply]

private theorem normalBasis_repr_map (x : E) (σ τ : Gal(E/F)) :
    (IsGalois.normalBasis F E).repr (σ x) τ =
      (IsGalois.normalBasis F E).repr x (σ⁻¹ * τ) := by
  classical
  let b := IsGalois.normalBasis F E
  conv_lhs => rw [← b.sum_repr x]
  dsimp only [b]
  simp only [map_sum, map_smul, normalBasis_map]
  have hm (γ : Gal(E/F)) : σ * γ = τ ↔ γ = σ⁻¹ * τ := by
    constructor <;> intro h
    · simpa only [inv_mul_cancel_left] using congrArg (σ⁻¹ * ·) h
    · simpa only [mul_inv_cancel_left] using congrArg (σ * ·) h
  simp [Finsupp.single_apply, hm]

/-- Galois-compatible tuples have one unrestricted base-field coordinate per label. -/
def galoisCompatibleTuplesEquiv : galoisCompatibleTuples F E I ≃ (I → F) where
  toFun := fun x i => (IsGalois.normalBasis F E).repr (x.val i) 1
  invFun := fun a => ⟨normalBasisTuple F E I a, normalBasisTuple_equivariant F E I a⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    apply (IsGalois.normalBasis F E).repr.injective
    ext σ
    rw [normalBasisTuple_repr]
    change (IsGalois.normalBasis F E).repr (x.val (σ⁻¹ • i)) 1 = _
    rw [x.property, normalBasis_repr_map]
    simp only [inv_inv, mul_one]
  right_inv := by
    intro a
    funext i
    change (IsGalois.normalBasis F E).repr (normalBasisTuple F E I a i) 1 = a i
    rw [normalBasisTuple_repr]
    simp only [inv_one, one_smul]

/-- An independent finite-field count, obtained from an actual normal-basis bijection. -/
theorem galoisCompatibleTuples_card [Fintype F] :
    Nat.card (galoisCompatibleTuples F E I) = Fintype.card F ^ Fintype.card I := by
  classical
  rw [Nat.card_congr (galoisCompatibleTuplesEquiv F E I), Nat.card_eq_fintype_card,
    Fintype.card_fun]

#print axioms galoisCompatibleTuplesEquiv
#print axioms galoisCompatibleTuples_card
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open FiniteField Module
variable (F E : Type*) [Field F] [Field E] [Algebra F E] [Fintype F] [Finite E]

private theorem frobenius_generates (σ : Gal(E/F)) :
    σ ∈ Subgroup.zpowers (frobeniusAlgEquivOfAlgebraic F E) := by
  obtain ⟨n, hn⟩ := (bijective_frobeniusAlgEquivOfAlgebraic_pow F E).surjective σ
  exact ⟨(n.val : ℤ), by simpa only [zpow_natCast] using hn⟩

/-- The cyclic Galois group acts through any group element of compatible order. -/
def frobeniusTwistHom {G : Type*} [Group G] (g : G)
    (hg : orderOf g ∣ finrank F E) : Gal(E/F) →* G :=
  monoidHomOfForallMemZpowers (frobenius_generates F E)
    (by simpa only [orderOf_frobeniusAlgEquivOfAlgebraic] using hg)

private theorem frobeniusTwistHom_generator {G : Type*} [Group G] (g : G)
    (hg : orderOf g ∣ finrank F E) :
    frobeniusTwistHom F E g hg (frobeniusAlgEquivOfAlgebraic F E) = g :=
  monoidHomOfForallMemZpowers_apply_gen _ _

variable (G I : Type*) [Group G] [MulAction G I] [Fintype I]

/-- The actual permutation-twisted Frobenius equations. -/
abbrev frobeniusTwistedTuples (g : G) :=
  {x : I → E // ∀ i, x (g • i) = x i ^ Fintype.card F}

omit [Fintype I] in
private theorem frobeniusTwistedTuples_pow (g : G) (x : frobeniusTwistedTuples F E G I g)
    (n : ℕ) (i : I) :
    x.val ((g ^ n) • i) = (frobeniusAlgEquivOfAlgebraic F E ^ n) (x.val i) := by
  induction n with
  | zero => simp only [pow_zero, one_smul, AlgEquiv.one_apply]
  | succ n ih =>
    rw [pow_succ', mul_smul, x.property, ih, pow_succ']
    rfl

/-- Each permutation twist is a descended tuple for an explicitly constructed cyclic action. -/
def frobeniusTwistedTuplesEquiv (g : G) (hg : orderOf g ∣ finrank F E) :
    frobeniusTwistedTuples F E G I g ≃ (I → F) := by
  let ρ := frobeniusTwistHom F E g hg
  letI : MulAction Gal(E/F) I := MulAction.compHom I ρ
  let e : frobeniusTwistedTuples F E G I g ≃ galoisCompatibleTuples F E I := {
    toFun := fun x => ⟨x.val, by
      intro σ i
      obtain ⟨n, rfl⟩ := (bijective_frobeniusAlgEquivOfAlgebraic_pow F E).surjective σ
      change x.val ((ρ (frobeniusAlgEquivOfAlgebraic F E ^ n.val)) • i) = _
      rw [map_pow, frobeniusTwistHom_generator]
      exact frobeniusTwistedTuples_pow F E G I g x n.val i⟩
    invFun := fun x => ⟨x.val, by
      intro i
      have h := x.property (frobeniusAlgEquivOfAlgebraic F E) i
      change x.val ((ρ (frobeniusAlgEquivOfAlgebraic F E)) • i) = _ at h
      rw [frobeniusTwistHom_generator] at h
      exact h⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact e.trans (galoisCompatibleTuplesEquiv F E I)

/-- Every compatible permutation twist has exactly one free base-field coordinate per label. -/
theorem frobeniusTwistedTuples_card (g : G) (hg : orderOf g ∣ finrank F E) :
    Nat.card (frobeniusTwistedTuples F E G I g) = Fintype.card F ^ Fintype.card I := by
  classical
  rw [Nat.card_congr (frobeniusTwistedTuplesEquiv F E G I g hg), Nat.card_eq_fintype_card,
    Fintype.card_fun]

#print axioms frobeniusTwistedTuplesEquiv
#print axioms frobeniusTwistedTuples_card
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset MulAction Module
variable (F E G I : Type*) [Field F] [Field E] [Algebra F E]
  [Fintype F] [Fintype E] [Group G] [Fintype G] [Fintype I] [MulAction G I]

/-- Permuting tuple labels by the inverse gives a left group action. -/
abbrev permutationTupleAction : MulAction G (I → E) where
  smul g x i := x (g⁻¹ • i)
  one_smul x := funext fun i => congrArg x (by rw [inv_one, one_smul])
  mul_smul g h x := funext fun i => congrArg x (by rw [mul_inv_rev, mul_smul])

local instance : MulAction G (I → E) := permutationTupleAction E G I

/-- The arithmetic Frobenius commutes with every permutation of the labels. -/
def tupleFrobenius : (I → E) →[G] (I → E) where
  toFun x i := x i ^ Fintype.card F
  map_smul' _ _ := rfl

/-- Frobenius-stable orbits of actual extension-field tuples. -/
def frobeniusTupleOrbits : Finset (Quotient (orbitRel G (I → E))) :=
  by
    classical
    exact equivariantFixedOrbits (tupleFrobenius F E G I)

/-- If the extension degree contains all group orders, the orbit count is affine-space size. -/
theorem frobeniusTupleOrbits_card (hd : Fintype.card G ∣ finrank F E) :
    (frobeniusTupleOrbits F E G I).card = Fintype.card F ^ Fintype.card I := by
  classical
  have ht (g : G) : Nat.card {x : I → E // g • x = tupleFrobenius F E G I x} =
      Fintype.card F ^ Fintype.card I := by
    let e : {x : I → E // g • x = tupleFrobenius F E G I x} ≃
        frobeniusTwistedTuples F E G I g⁻¹ :=
      Equiv.subtypeEquivRight (fun _ => funext_iff)
    rw [Nat.card_congr e]
    have ho : orderOf (g⁻¹) ∣ Fintype.card G := by
      simpa only [Fintype.card_eq_nat_card] using (orderOf_dvd_natCard (x := g⁻¹))
    exact frobeniusTwistedTuples_card F E G I g⁻¹ (ho.trans hd)
  have h := sum_card_transporters (tupleFrobenius F E G I)
  rw [sum_congr rfl (fun g _ => ht g), sum_const, card_univ, nsmul_eq_mul] at h
  apply Nat.eq_of_mul_eq_mul_right (Fintype.card_pos (α := G))
  change (equivariantFixedOrbits (tupleFrobenius F E G I)).card * Fintype.card G = _
  calc
    _ = Fintype.card G * (Fintype.card F ^ Fintype.card I) := by
      simpa only [Nat.cast_id] using h.symm
    _ = _ := Nat.mul_comm _ _

#print axioms frobeniusTupleOrbits_card
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open FiniteField
variable (F : Type*) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]
  (G I : Type*) [Group G] [Fintype G] [Fintype I] [MulAction G I]

/-- The finite arithmetic orbits in the extension whose degree is the acting group order. -/
def arithmeticFrobeniusOrbits :=
  let E := Extension F p (Fintype.card G)
  letI : Fintype E := Fintype.ofFinite E
  frobeniusTupleOrbits F E G I

/-- An unconditional independent count for every finite permutation action. -/
theorem arithmeticFrobeniusOrbits_card :
    (arithmeticFrobeniusOrbits F p G I).card = Fintype.card F ^ Fintype.card I := by
  letI : Fintype (Extension F p (Fintype.card G)) := Fintype.ofFinite _
  unfold arithmeticFrobeniusOrbits
  apply frobeniusTupleOrbits_card
  simpa only [finrank_extension] using (dvd_rfl : Fintype.card G ∣ Fintype.card G)

#print axioms arithmeticFrobeniusOrbits_card
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
