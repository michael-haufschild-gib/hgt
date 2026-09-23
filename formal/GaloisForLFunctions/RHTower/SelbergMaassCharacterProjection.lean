import GaloisForLFunctions.RHTower.SelbergMaassUnipotentFourier
import GaloisForLFunctions.RHTower.ConnesCharacterProjection

/-!
# Complete original unipotent character projections and inversion

The finite character-average construction is instantiated in the actual congruence deck
representation. Its full residue family is a self-adjoint orthogonal resolution of the
identity with exact norm-square decomposition. Literal modular inversion conjugates each
lower-character projector to the upper projector at the opposite residue. The original
Maass source therefore retains every character energy, with its actual transformed height.
-/

open Complex Set UpperHalfPlane ModularGroup
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassCharacterProjection
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassUnipotentBlocks
open GaloisForLFunctions.HTGeometry
noncomputable section

local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

/-- The standard residue character on the literal unipotent parameter group. -/
def residueCharacter (N : ℕ) (r : ZMod (N+1)) (j : Multiplicative (ZMod (N+1))) : ℂ :=
  ZMod.stdAddChar (r*j.toAdd)

/-- The actual residue phase is multiplicative on the unipotent parameter group. -/
theorem residueCharacter_mul (N : ℕ) (r : ZMod (N+1))
    (j k : Multiplicative (ZMod (N+1))) :
    residueCharacter N r (j*k)=residueCharacter N r j*residueCharacter N r k := by
  simp [residueCharacter,mul_add,AddChar.map_add_eq_mul]

/-- Every original residue phase is unitary. -/
theorem residueCharacter_unit (N : ℕ) (r : ZMod (N+1))
    (j : Multiplicative (ZMod (N+1))) :
    (starRingEnd ℂ) (residueCharacter N r j)*residueCharacter N r j=1 := by
  unfold residueCharacter
  rw [← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv,
    ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

/-- The literal finite regular action of a unipotent parameter homomorphism. -/
def blockAction (N : ℕ) (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (j : Multiplicative (ZMod (N+1))) :
    EuclideanSpace ℂ (Deck N) →ₗ[ℂ] EuclideanSpace ℂ (Deck N) :=
  (finiteRegularUnitary (p j)).toLinearEquiv.toLinearMap

/-- The actual block action satisfies the representation law. -/
theorem blockAction_mul (N : ℕ) (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (j k : Multiplicative (ZMod (N+1))) :
    blockAction N p (j*k)=(blockAction N p j).comp (blockAction N p k) := by
  ext v q
  change v (q*p (j*k))=v ((q*p j)*p k)
  rw [map_mul,mul_assoc]

/-- The corpus character-average projector in the actual congruence deck space. -/
def characterProjection (N : ℕ) (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) : EuclideanSpace ℂ (Deck N) →ₗ[ℂ] EuclideanSpace ℂ (Deck N) :=
  connesCharacterProjector (blockAction N p) (residueCharacter N r)

/-- The complete normalized character average, with the exact positive level. -/
theorem characterProjection_apply (N : ℕ) (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (v : EuclideanSpace ℂ (Deck N)) :
    characterProjection N p r v = ((N+1 : ℕ) : ℂ)⁻¹ •
      ∑ j : Multiplicative (ZMod (N+1)),
        (starRingEnd ℂ) (residueCharacter N r j) • finiteRegularUnitary (p j) v := by
  rw [characterProjection,connesCharacterProjector_apply]
  congr 1
  rw [Fintype.card_congr Multiplicative.toAdd,ZMod.card]

/-- Every coordinate is the literal weighted original deck sum. -/
theorem characterProjection_coord (N : ℕ) (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (v : EuclideanSpace ℂ (Deck N)) (q : Deck N) :
    characterProjection N p r v q = ((N+1 : ℕ) : ℂ)⁻¹ *
      ∑ j : Multiplicative (ZMod (N+1)),
        (starRingEnd ℂ) (residueCharacter N r j) * v (q*p j) := by
  rw [characterProjection_apply]
  change ((N+1 : ℕ) : ℂ)⁻¹ *
    (∑ j : Multiplicative (ZMod (N+1)),
      (starRingEnd ℂ) (residueCharacter N r j) • finiteRegularUnitary (p j) v) q= _
  simp only [WithLp.ofLp_sum,Finset.sum_apply]
  rfl

/-- Each projected component lies in its exact unipotent character eigenspace. -/
theorem characterProjection_intertwine (N : ℕ) (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (j : Multiplicative (ZMod (N+1))) (v : EuclideanSpace ℂ (Deck N)) :
    finiteRegularUnitary (p j) (characterProjection N p r v)=
      residueCharacter N r j • characterProjection N p r v :=
  connes_characterProjector_intertwine (blockAction_mul N p)
    (residueCharacter_mul N r) (residueCharacter_unit N r) j v

/-- Actual-source instantiation of the corpus character-projector idempotence theorem. -/
theorem characterProjection_idempotent (N : ℕ) (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (v : EuclideanSpace ℂ (Deck N)) :
    characterProjection N p r (characterProjection N p r v)=characterProjection N p r v :=
  connes_characterProjector_idem (blockAction_mul N p)
    (residueCharacter_mul N r) (residueCharacter_unit N r) v

/-- Complete residue phases are exactly orthogonal at every positive composite or prime level. -/
theorem residueCharacter_orthogonality (N : ℕ) (r s : ZMod (N+1)) :
    (∑ j : Multiplicative (ZMod (N+1)),
      (starRingEnd ℂ) (residueCharacter N r j)*residueCharacter N s j) =
      if r=s then (N+1 : ℂ) else 0 := by
  classical
  have he (j : Multiplicative (ZMod (N+1))) :
      (starRingEnd ℂ) (residueCharacter N r j)*residueCharacter N s j =
      ZMod.stdAddChar ((s-r)*j.toAdd) := by
    unfold residueCharacter
    rw [← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [he]
  rw [Equiv.sum_comp Multiplicative.toAdd (fun j : ZMod (N+1) => ZMod.stdAddChar ((s-r)*j))]
  have h := AddChar.sum_mulShift (s-r) (ZMod.isPrimitive_stdAddChar (N+1))
  simpa only [mul_comm,sub_eq_zero,eq_comm,Nat.cast_ite,Nat.cast_zero,ZMod.card,
    Nat.cast_add,Nat.cast_one] using h

/-- Distinct character projections annihilate one another. -/
theorem characterProjection_pair (N : ℕ) (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r s : ZMod (N+1)) (v : EuclideanSpace ℂ (Deck N)) :
    characterProjection N p r (characterProjection N p s v)=
      if r=s then characterProjection N p s v else 0 := by
  classical
  rw [characterProjection_apply]
  simp_rw [characterProjection_intertwine,smul_smul]
  rw [← Finset.sum_smul,residueCharacter_orthogonality]
  by_cases h : r=s
  · simp only [h,ite_true,smul_smul,Nat.cast_add,Nat.cast_one]
    rw [inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero N : (N+1 : ℂ)≠0),one_smul]
  · simp [h]

/-- The sum of all residue characters singles out the identity parameter. -/
theorem residueCharacter_sum (N : ℕ) (j : Multiplicative (ZMod (N+1))) :
    (∑ r : ZMod (N+1), (starRingEnd ℂ) (residueCharacter N r j)) =
      if j=1 then (N+1 : ℂ) else 0 := by
  classical
  rw [← map_sum]
  have h := AddChar.sum_mulShift j.toAdd (ZMod.isPrimitive_stdAddChar (N+1))
  change (∑ r : ZMod (N+1), ZMod.stdAddChar (r*j.toAdd)) = _ at h
  unfold residueCharacter
  rw [h]
  simp only [ZMod.card]
  change (starRingEnd ℂ) (↑(if j=1 then N+1 else 0) : ℂ) = _
  split_ifs <;> simp

/-- The full residue family reconstructs every original deck vector. -/
theorem sum_characterProjection (N : ℕ) (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (v : EuclideanSpace ℂ (Deck N)) :
    ∑ r : ZMod (N+1), characterProjection N p r v=v := by
  classical
  ext q
  change (∑ r : ZMod (N+1), characterProjection N p r v).ofLp q=v q
  simp only [WithLp.ofLp_sum,Finset.sum_apply,characterProjection_coord]
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [← Finset.sum_mul,residueCharacter_sum]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,map_one,mul_one]
  rw [← mul_assoc]
  simp only [Nat.cast_add,Nat.cast_one]
  rw [inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero N : (N+1 : ℂ)≠0),one_mul]

/-- Actual unitarity makes distinct character components orthogonal in the physical deck inner product. -/
theorem characterProjection_inner_eq_zero (N : ℕ)
    (p : Multiplicative (ZMod (N+1)) →* Deck N) (r s : ZMod (N+1)) (hrs : r≠s)
    (v w : EuclideanSpace ℂ (Deck N)) :
    inner ℂ (characterProjection N p r v) (characterProjection N p s w)=0 := by
  by_contra hi
  let j : Multiplicative (ZMod (N+1)) := Multiplicative.ofAdd 1
  have hU := (finiteRegularUnitary (p j)).inner_map_map
    (characterProjection N p r v) (characterProjection N p s w)
  rw [characterProjection_intertwine,characterProjection_intertwine,
    inner_smul_left,inner_smul_right] at hU
  have hc : (starRingEnd ℂ) (residueCharacter N r j)*residueCharacter N s j=1 := by
    apply mul_right_cancel₀ hi
    simpa only [mul_assoc,one_mul] using hU
  have hu := residueCharacter_unit N r j
  have hne : (starRingEnd ℂ) (residueCharacter N r j)≠0 := by
    intro hz
    rw [hz,zero_mul] at hu
    exact zero_ne_one hu
  have he : residueCharacter N r j=residueCharacter N s j :=
    mul_left_cancel₀ hne (hu.trans hc.symm)
  have hx : ZMod.stdAddChar r=ZMod.stdAddChar s := by simpa [residueCharacter,j] using he
  exact hrs (ZMod.injective_stdAddChar hx)


/-- Only the matching character component contributes to the projected inner product. -/
theorem characterProjection_inner_left (N : ℕ)
    (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1))
    (v w : EuclideanSpace ℂ (Deck N)) :
    inner ℂ (characterProjection N p r v) w =
      inner ℂ (characterProjection N p r v) (characterProjection N p r w) := by
  classical
  conv_lhs => rw [← sum_characterProjection N p w]
  rw [inner_sum]
  apply Finset.sum_eq_single r
  · intro s _ hsr
    exact characterProjection_inner_eq_zero N p r s (Ne.symm hsr) v w
  · simp

/-- Each actual character-average projector is self-adjoint. -/
theorem characterProjection_self_adjoint (N : ℕ)
    (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1))
    (v w : EuclideanSpace ℂ (Deck N)) :
    inner ℂ (characterProjection N p r v) w=inner ℂ v (characterProjection N p r w) := by
  rw [characterProjection_inner_left]
  conv_rhs => rw [← sum_characterProjection N p v]
  rw [sum_inner]
  symm
  apply Finset.sum_eq_single r
  · intro s _ hsr
    exact characterProjection_inner_eq_zero N p s r hsr v w
  · simp

/-- Exact energy decomposition over every residue channel. -/
theorem sum_characterProjection_norm_sq (N : ℕ)
    (p : Multiplicative (ZMod (N+1)) →* Deck N) (v : EuclideanSpace ℂ (Deck N)) :
    (∑ r : ZMod (N+1), ‖characterProjection N p r v‖^(2 : ℕ))=‖v‖^(2 : ℕ) := by
  have he (r : ZMod (N+1)) : ‖characterProjection N p r v‖^(2 : ℕ) =
      (inner ℂ (characterProjection N p r v) v).re := by
    rw [characterProjection_inner_left]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
  simp_rw [he]
  have hs : (∑ r : ZMod (N+1), (inner ℂ (characterProjection N p r v) v).re) =
      (inner ℂ (∑ r : ZMod (N+1), characterProjection N p r v) v).re := by
    rw [sum_inner]
    simp
  rw [hs,sum_characterProjection]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) v

open SelbergMaassUnipotentPaths GaloisForLFunctions.HTGeometry.FiniteRingSl2

/-- Every integer upper motion reduces to its literal finite residue parameter. -/
theorem upperBlock_intCast (N : ℕ) (j : ℤ) :
    upperBlock N (Multiplicative.ofAdd (j : ZMod (N+1)))=QuotientGroup.mk (upper j) := by
  apply (deckResidueEquiv N).injective
  rw [deckResidueEquiv_mk]
  simp only [upperBlock,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply,upperHom,MonoidHom.coe_mk,OneHom.coe_mk,map_upper]
  rfl

/-- The actual lower block is conjugated upper motion with inverted parameter. -/
theorem lowerBlock_conjugate (N : ℕ) (j : Multiplicative (ZMod (N+1))) :
    lowerBlock N j=(QuotientGroup.mk S : Deck N)*upperBlock N j⁻¹*QuotientGroup.mk (S⁻¹) := by
  rw [lowerBlock_eq_mk,lower_eq_conjugate_upper,QuotientGroup.mk_mul,QuotientGroup.mk_mul,
    ← upperBlock_intCast N (-(j.toAdd.val : ℤ))]
  congr 2
  simp

/-- Modular inversion conjugates lower residue r to upper residue minus r. -/
theorem characterProjection_lower_conjugate (N : ℕ) (r : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    characterProjection N (lowerBlock N) r v =
      finiteRegularUnitary (QuotientGroup.mk S : Deck N)
        (characterProjection N (upperBlock N) (-r)
          (finiteRegularUnitary (QuotientGroup.mk (S⁻¹) : Deck N) v)) := by
  classical
  ext q
  change characterProjection N (lowerBlock N) r v q =
    characterProjection N (upperBlock N) (-r)
      (finiteRegularUnitary (QuotientGroup.mk (S⁻¹) : Deck N) v)
      (q*QuotientGroup.mk S)
  rw [characterProjection_coord,characterProjection_coord]
  congr 1
  have he := Equiv.sum_comp (Equiv.inv (Multiplicative (ZMod (N+1))))
    (fun j : Multiplicative (ZMod (N+1)) =>
      (starRingEnd ℂ) (residueCharacter N r j)*v (q*lowerBlock N j))
  rw [← he]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Equiv.inv_apply,lowerBlock_conjugate,inv_inv,finiteRegularUnitary_apply]
  congr 1
  · simp [residueCharacter,mul_neg,neg_mul]
  · simp only [mul_assoc]

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- The actual source lower-character field is the inverted original upper-character field. -/
theorem source_lower_character (r : ZMod (N+1)) (z : ℍ) :
    characterProjection N (lowerBlock N) r (sourceVector N f z) =
      finiteRegularUnitary (QuotientGroup.mk S : Deck N)
        (characterProjection N (upperBlock N) (-r) (sourceVector N f (S⁻¹ • z))) := by
  rw [characterProjection_lower_conjugate,sourceVector_pullback]

/-- Exact source character energy transport, with the actual inverted point retained. -/
theorem source_lower_character_norm_sq (r : ZMod (N+1)) (z : ℍ) :
    ‖characterProjection N (lowerBlock N) r (sourceVector N f z)‖^(2 : ℕ) =
      ‖characterProjection N (upperBlock N) (-r) (sourceVector N f (S⁻¹ • z))‖^(2 : ℕ) := by
  rw [source_lower_character,LinearIsometryEquiv.norm_map]

/-- Every actual source density is the sum of all original block-character energies. -/
theorem source_character_energy_sum (p : Multiplicative (ZMod (N+1)) →* Deck N) (z : ℍ) :
    (∑ r : ZMod (N+1), ‖characterProjection N p r (sourceVector N f z)‖^(2 : ℕ))=
      density N f z := by
  rw [sum_characterProjection_norm_sq,sourceVector_norm_sq]

end
end GaloisForLFunctions.RHTower.SelbergMaassCharacterProjection
