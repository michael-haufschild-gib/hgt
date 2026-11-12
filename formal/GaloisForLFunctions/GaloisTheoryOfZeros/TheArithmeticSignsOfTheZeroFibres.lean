import GaloisForLFunctions.GaloisTheoryOfZeros.TheSignedPermutationsOfTheZeroFibres
import GaloisForLFunctions.GaloisTheoryOfZeros.TheSourceNormsOfTheZeroWidthSquares

/-!
# Arithmetic signs of complete zero fibres

The product of squared widths in each complete analytic-multiplicity block lies
in the source field. Its square class is the global width class to the number
of conjugate pairs. Odd blocks therefore split the entire width restriction. Their sign characters
act on explicit nonzero radicals and determine exact quadratic source fields.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped IntermediateField
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local instance : DecidableEq ℂ := Classical.decEq ℂ
local instance (t : ℝ) (m : ℕ) : Fintype (FibrePositivePairs t m) := Fintype.ofFinite _

/-- The internal even-width field embeds in the entire centered zero field. -/
def evenWidthInZeroField : evenWidthInReal →ₐ[fullFibreSourceField] fullFibreZeroExtension :=
  (IntermediateField.inclusion evenWidthField_le_zeroExtension).comp evenWidthInRealEquiv.toAlgHom

private theorem fibre_square_mem_even (t : ℝ) (z : ↥(fibreZeroSupport t)) :
    ((z : ℂ).im : ℂ)^2 ∈ evenWidthField := by
  obtain ⟨q,_,hq⟩ := Finset.mem_image.mp z.property
  rw [← hq,pow_two]
  exact zeroWidth_mul_mem_evenWidthField q q

/-- The squared width of a support point, in the actual even-width field. -/
def fibreWidthSquare (t : ℝ) (z : ↥(fibreZeroSupport t)) : evenWidthInReal :=
  ⟨⟨((z : ℂ).im : ℂ)^2,evenWidthField_le_realWidthField (fibre_square_mem_even t z)⟩,
    fibre_square_mem_even t z⟩

/-- Squared widths are unchanged by conjugation of their support points. -/
theorem fibreWidthSquare_conjugation (t : ℝ) (z : ↥(fibreZeroSupport t)) :
    fibreWidthSquare t (fibreConjugation t z) = fibreWidthSquare t z := by
  apply Subtype.ext
  apply Subtype.ext
  change ((fibreConjugation t z : ℂ).im : ℂ)^2 = ((z : ℂ).im : ℂ)^2
  rw [fibreConjugation_im,ofReal_neg,neg_sq]

private theorem complex_squared_width (z : ℂ) :
    ((z.im : ℂ)^2) = -((z-(starRingEnd ℂ) z)/2)^2 := by
  have ho : (z-(starRingEnd ℂ) z)/2 = I*(z.im : ℂ) := by
    apply Complex.ext <;> simp
  rw [ho]
  simp only [pow_two]
  calc
    (z.im : ℂ)*(z.im : ℂ) = -(I*I)*((z.im : ℂ)*(z.im : ℂ)) := by rw [I_mul_I]; ring
    _ = -(I*(z.im : ℂ)*(I*(z.im : ℂ))) := by ring

/-- Squared widths are algebraic functions of a root and its central conjugation. -/
theorem fibreWidthSquare_offset (t : ℝ) (z : ↥(fibreZeroSupport t)) :
    evenWidthInZeroField (fibreWidthSquare t z) =
      -((fibreRootInField t z-fullFibreZeroConjugation (fibreRootInField t z))/2)^2 := by
  apply Subtype.ext
  exact complex_squared_width (z : ℂ)

private theorem fibre_root_aut (t : ℝ)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    (z : ↥(fibreZeroSupport t)) :
    fibreRootInField t (fibrePermutation t σ z) = σ (fibreRootInField t z) := Subtype.ext rfl

/-- The squared-width function is equivariant for the full source Galois action. -/
theorem fibreWidthSquare_aut (t : ℝ)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    (z : ↥(fibreZeroSupport t)) :
    σ (evenWidthInZeroField (fibreWidthSquare t z)) =
      evenWidthInZeroField (fibreWidthSquare t (fibrePermutation t σ z)) := by
  have hc : σ (fullFibreZeroConjugation (fibreRootInField t z)) =
      fullFibreZeroConjugation (σ (fibreRootInField t z)) :=
    congrArg (fun τ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension =>
      τ (fibreRootInField t z)) (fullFibreZeroConjugation_central σ)
  rw [fibreWidthSquare_offset,fibreWidthSquare_offset,map_neg,map_pow,map_div₀,map_sub,map_ofNat,
    hc,fibre_root_aut]

/-- The pair permutation controls squared widths; its independent signs disappear. -/
theorem fibreWidthSquare_pair_permutation (t : ℝ) (m : ℕ)
    (π : fibreDivisorSymmetries t) (p : FibrePositivePairs t m) :
    fibreWidthSquare t (π.val p.val) =
      fibreWidthSquare t ((fibreSignedCoordinates t m π).perm p).val := by
  let a := fibreSignedCoordinates t m π
  have he := fibrePairPermutation_value t m π (p,1)
  rw [← fibreSignedCoordinates_action] at he
  change (fibrePairEquiv t m (a.perm p,a.sign (a.perm p)*1)).val =
    π.val (fibrePairEquiv t m (p,1)).val at he
  rw [mul_one,fibrePairEquiv_pos] at he
  rcases Int.units_eq_one_or (a.sign (a.perm p)) with hp | hn
  · rw [hp,fibrePairEquiv_pos] at he
    exact congrArg (fibreWidthSquare t) he.symm
  · rw [hn,fibrePairEquiv_neg] at he
    rw [← he,fibreWidthSquare_conjugation]

private theorem fibre_pair_square_ne_zero (t : ℝ) (m : ℕ) (p : FibrePositivePairs t m) :
    fibreWidthSquare t p.val ≠ 0 := by
  intro h
  have he := congrArg (fun a : evenWidthInReal => ((a : realWidthField) : ℂ)) h
  have hp : ((p.val : ℂ).im : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt p.property.1
  exact (pow_ne_zero 2 hp) he

/-- A nonreal conjugate pair supplies a nonzero squared-width unit. -/
def fibrePairSquareUnit (t : ℝ) (m : ℕ) (p : FibrePositivePairs t m) : evenWidthInRealˣ :=
  Units.mk0 (fibreWidthSquare t p.val) (fibre_pair_square_ne_zero t m p)

/-- Every pair-square factor represents the same global width class. -/
theorem fibrePairSquareUnit_class (t : ℝ) (m : ℕ) (p : FibrePositivePairs t m) :
    sourceSquareClassProjection evenWidthInReal (fibrePairSquareUnit t m p) =
      globalWidthSquareClass := by
  obtain ⟨q,_,hq⟩ := Finset.mem_image.mp p.val.property
  have hp : ((p.val : ℂ).im : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt p.property.1
  have hq0 : zeroWidth q ≠ 0 := by simpa only [zeroWidth,hq] using hp
  have he : fibrePairSquareUnit t m p = widthSquareUnit q hq0 := by
    apply Units.ext
    apply Subtype.ext
    apply Subtype.ext
    change ((p.val : ℂ).im : ℂ)^2 = zeroWidth q^2
    rw [zeroWidth,hq]
  rw [he]
  exact (globalWidthSquareClass_eq q hq0).symm

/-- The product of squared widths of all distinct conjugate pairs of one analytic multiplicity. -/
def fibreBlockSquareUnit (t : ℝ) (m : ℕ) : evenWidthInRealˣ :=
  ∏ p : FibrePositivePairs t m, fibrePairSquareUnit t m p

private theorem fibreBlockSquareUnit_image (t : ℝ) (m : ℕ) :
    evenWidthInZeroField (fibreBlockSquareUnit t m : evenWidthInReal) =
      ∏ p : FibrePositivePairs t m,
        evenWidthInZeroField (fibrePairSquareUnit t m p : evenWidthInReal) := by
  let v : evenWidthInRealˣ →* fullFibreZeroExtension :=
    evenWidthInZeroField.toMonoidHom.comp
      { toFun := fun a => (a : evenWidthInReal), map_one' := rfl, map_mul' := fun _ _ => rfl }
  exact map_prod v (fibrePairSquareUnit t m) Finset.univ

/-- Complete pair-block products are fixed by every automorphism of the whole zero field. -/
theorem fibreBlockSquareUnit_fixed (t : ℝ) (m : ℕ)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :
    σ (evenWidthInZeroField (fibreBlockSquareUnit t m : evenWidthInReal)) =
      evenWidthInZeroField (fibreBlockSquareUnit t m : evenWidthInReal) := by
  let π := fibreDivisorAction t σ
  let a := fibreSignedCoordinates t m π
  have hp (p : FibrePositivePairs t m) :
      σ (evenWidthInZeroField (fibrePairSquareUnit t m p : evenWidthInReal)) =
        evenWidthInZeroField (fibrePairSquareUnit t m (a.perm p) : evenWidthInReal) := by
    change σ (evenWidthInZeroField (fibreWidthSquare t p.val)) =
      evenWidthInZeroField (fibreWidthSquare t (a.perm p).val)
    rw [fibreWidthSquare_aut]
    exact congrArg evenWidthInZeroField (fibreWidthSquare_pair_permutation t m π p)
  simp only [fibreBlockSquareUnit_image,map_prod]
  calc
    ∏ p : FibrePositivePairs t m,
        σ (evenWidthInZeroField (fibrePairSquareUnit t m p : evenWidthInReal)) =
      ∏ p : FibrePositivePairs t m,
        evenWidthInZeroField (fibrePairSquareUnit t m (a.perm p) : evenWidthInReal) :=
      Finset.prod_congr rfl (fun p _ => hp p)
    _ = ∏ p : FibrePositivePairs t m,
        evenWidthInZeroField (fibrePairSquareUnit t m p : evenWidthInReal) :=
      Fintype.prod_equiv a.perm
        (fun p => evenWidthInZeroField (fibrePairSquareUnit t m (a.perm p) : evenWidthInReal))
        (fun p => evenWidthInZeroField (fibrePairSquareUnit t m p : evenWidthInReal)) (fun _ => rfl)

/-- The complete block product is a genuine source-field unit. -/
theorem fibreBlockSquareUnit_from_source (t : ℝ) (m : ℕ) :
    ∃ a : fullFibreSourceFieldˣ,
      Units.map (algebraMap fullFibreSourceField evenWidthInReal).toMonoidHom a =
        fibreBlockSquareUnit t m := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  obtain ⟨a,ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
    (evenWidthInZeroField (fibreBlockSquareUnit t m : evenWidthInReal))).mpr
      (fibreBlockSquareUnit_fixed t m)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h,map_zero] at ha
    have hb : (fibreBlockSquareUnit t m : evenWidthInReal) = 0 :=
      evenWidthInZeroField.injective (ha.symm.trans (map_zero evenWidthInZeroField).symm)
    exact (fibreBlockSquareUnit t m).ne_zero hb
  refine ⟨Units.mk0 a ha0,Units.ext ?_⟩
  apply evenWidthInZeroField.injective
  exact (evenWidthInZeroField.commutes a).trans ha

/-- The source unit obtained from a complete analytic-multiplicity block. -/
def fibreBlockSourceUnit (t : ℝ) (m : ℕ) : fullFibreSourceFieldˣ :=
  (fibreBlockSquareUnit_from_source t m).choose

theorem fibreBlockSourceUnit_spec (t : ℝ) (m : ℕ) :
    Units.map (algebraMap fullFibreSourceField evenWidthInReal).toMonoidHom
      (fibreBlockSourceUnit t m) = fibreBlockSquareUnit t m :=
  (fibreBlockSquareUnit_from_source t m).choose_spec

/-- A complete pair block represents the global width class to its number of distinct pairs. -/
theorem fibreBlockSourceUnit_class (t : ℝ) (m : ℕ) :
    sourceSquareClassMap (algebraMap fullFibreSourceField evenWidthInReal)
      (sourceSquareClassProjection fullFibreSourceField (fibreBlockSourceUnit t m)) =
        globalWidthSquareClass ^ Nat.card (FibrePositivePairs t m) := by
  rw [sourceSquareClassMap_projection,fibreBlockSourceUnit_spec]
  change sourceSquareClassProjection evenWidthInReal
    (∏ p : FibrePositivePairs t m, fibrePairSquareUnit t m p) = _
  rw [map_prod]
  calc
    ∏ p : FibrePositivePairs t m,
        sourceSquareClassProjection evenWidthInReal (fibrePairSquareUnit t m p) =
      ∏ _p : FibrePositivePairs t m, globalWidthSquareClass :=
      Finset.prod_congr rfl (fun p _ => fibrePairSquareUnit_class t m p)
    _ = globalWidthSquareClass ^ Nat.card (FibrePositivePairs t m) := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_eq_nat_card]

/-- An odd complete multiplicity block splits the entire infinite width restriction continuously. -/
theorem widthRestrictionSplits_of_odd_fibre_pairs (t : ℝ) (m : ℕ)
    (hodd : Odd (Nat.card (FibrePositivePairs t m))) : WidthRestrictionSplits := by
  apply globalWidthSquareClass_descent_iff.mpr
  refine ⟨sourceSquareClassProjection fullFibreSourceField (fibreBlockSourceUnit t m),?_⟩
  rw [fibreBlockSourceUnit_class]
  obtain ⟨k,hk⟩ := hodd
  have hn : Nat.card (FibrePositivePairs t m) = 2*k+1 := by omega
  rw [hn,pow_add,pow_mul,sourceSquareClass_sq,one_pow,one_mul,pow_one]

/-- Nonsplitting forces even pair counts in every complete ordinate and analytic-multiplicity block. -/
theorem fibre_pair_count_dichotomy :
    WidthRestrictionSplits ∨ ∀ (t : ℝ) (m : ℕ), 2 ∣ Nat.card (FibrePositivePairs t m) := by
  classical
  by_cases hs : WidthRestrictionSplits
  · exact Or.inl hs
  · right
    intro t m
    refine ⟨Nat.card (FibrePositivePairs t m)/2,?_⟩
    by_contra hn
    apply hs
    apply widthRestrictionSplits_of_odd_fibre_pairs t m
    exact ⟨Nat.card (FibrePositivePairs t m)/2,by omega⟩

namespace FibreSignedPerm

/-- Multiplying the independent pair signs gives a character of the signed permutation group. -/
def signProduct {α : Type*} [Fintype α] : FibreSignedPerm α →* ℤˣ where
  toFun a := ∏ p, a.sign p
  map_one' := by simp only [one_sign,Finset.prod_const_one]
  map_mul' a b := by
    change (∏ p, a.sign p*b.sign (a.perm⁻¹ p)) = (∏ p, a.sign p)*(∏ p, b.sign p)
    rw [Finset.prod_mul_distrib]
    exact congrArg (fun z : ℤˣ => (∏ p, a.sign p)*z) (Equiv.prod_comp a.perm⁻¹ b.sign)

end FibreSignedPerm

/-- The arithmetic sign character of one complete analytic-multiplicity block. -/
def fibreBlockSignCharacter (t : ℝ) (m : ℕ) :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →* ℤˣ :=
  FibreSignedPerm.signProduct.comp ((fibreSignedCoordinates t m).comp (fibreDivisorAction t))

/-- Each block character is continuous on the entire Krull Galois group. -/
theorem fibreBlockSignCharacter_continuous (t : ℝ) (m : ℕ) :
    Continuous (fibreBlockSignCharacter t m) := by
  have hc : Continuous ((FibreSignedPerm.signProduct (α := FibrePositivePairs t m)).comp
      (fibreSignedCoordinates t m)) := continuous_of_discreteTopology
  exact hc.comp (fibreDivisorAction_continuous t)

/-- Conjugation is detected by a block character exactly through its pair-count parity. -/
theorem fibreBlockSignCharacter_conjugation (t : ℝ) (m : ℕ) :
    fibreBlockSignCharacter t m fullFibreZeroConjugation =
      (-1 : ℤˣ)^Nat.card (FibrePositivePairs t m) := by
  have he := congrArg (fun a : ∀ (t : ℝ) (m : ℕ), FibreSignedPerm (FibrePositivePairs t m) => a t m)
    allSignedFibreAction_conjugation
  change fibreSignedCoordinates t m (fibreDivisorAction t fullFibreZeroConjugation) =
    FibreSignedPerm.uniformFlip (FibrePositivePairs t m) at he
  change FibreSignedPerm.signProduct
    (fibreSignedCoordinates t m (fibreDivisorAction t fullFibreZeroConjugation)) = _
  rw [he]
  change (∏ _p : FibrePositivePairs t m, (-1 : ℤˣ)) = _
  rw [Finset.prod_const,Finset.card_univ,Fintype.card_eq_nat_card]
  rfl

/-- The imaginary offset is defined inside the centered zero field without adjoining `i`. -/
def fibreImaginaryOffset (t : ℝ) (z : ↥(fibreZeroSupport t)) : fullFibreZeroExtension :=
  (fibreRootInField t z-fullFibreZeroConjugation (fibreRootInField t z))/2

private theorem fibreImaginaryOffset_conjugation (t : ℝ) (z : ↥(fibreZeroSupport t)) :
    fibreImaginaryOffset t (fibreConjugation t z) = -fibreImaginaryOffset t z := by
  apply Subtype.ext
  change ((starRingEnd ℂ) (z : ℂ)-(starRingEnd ℂ) ((starRingEnd ℂ) (z : ℂ)))/2 =
    -(((z : ℂ)-(starRingEnd ℂ) (z : ℂ))/2)
  have hc : (starRingEnd ℂ) ((starRingEnd ℂ) (z : ℂ)) = (z : ℂ) := star_star (z : ℂ)
  rw [hc]
  ring

private theorem fibreImaginaryOffset_aut (t : ℝ)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    (z : ↥(fibreZeroSupport t)) :
    σ (fibreImaginaryOffset t z) = fibreImaginaryOffset t (fibrePermutation t σ z) := by
  have hc : σ (fullFibreZeroConjugation (fibreRootInField t z)) =
      fullFibreZeroConjugation (σ (fibreRootInField t z)) :=
    congrArg (fun τ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension =>
      τ (fibreRootInField t z)) (fullFibreZeroConjugation_central σ)
  unfold fibreImaginaryOffset
  rw [map_div₀,map_sub,map_ofNat,hc,fibre_root_aut]

private theorem fibreImaginaryOffset_pair_permutation (t : ℝ) (m : ℕ)
    (π : fibreDivisorSymmetries t) (p : FibrePositivePairs t m) :
    fibreImaginaryOffset t (π.val p.val) =
      (((fibreSignedCoordinates t m π).sign ((fibreSignedCoordinates t m π).perm p) : ℤ) :
        fullFibreZeroExtension)*
      fibreImaginaryOffset t ((fibreSignedCoordinates t m π).perm p).val := by
  let a := fibreSignedCoordinates t m π
  have he := fibrePairPermutation_value t m π (p,1)
  rw [← fibreSignedCoordinates_action] at he
  change (fibrePairEquiv t m (a.perm p,a.sign (a.perm p)*1)).val =
    π.val (fibrePairEquiv t m (p,1)).val at he
  rw [mul_one,fibrePairEquiv_pos] at he
  rcases Int.units_eq_one_or (a.sign (a.perm p)) with hp | hn
  · rw [hp,fibrePairEquiv_pos] at he
    change fibreImaginaryOffset t (π.val p.val) =
      ((a.sign (a.perm p) : ℤ) : fullFibreZeroExtension)*fibreImaginaryOffset t (a.perm p).val
    rw [← he,hp]
    simp only [Units.val_one,Int.cast_one,one_mul]
  · rw [hn,fibrePairEquiv_neg] at he
    change fibreImaginaryOffset t (π.val p.val) =
      ((a.sign (a.perm p) : ℤ) : fullFibreZeroExtension)*fibreImaginaryOffset t (a.perm p).val
    rw [← he,fibreImaginaryOffset_conjugation,hn]
    change -fibreImaginaryOffset t (a.perm p).val =
      ((-1 : ℤ) : fullFibreZeroExtension)*fibreImaginaryOffset t (a.perm p).val
    rw [Int.cast_neg,Int.cast_one,neg_one_mul]

/-- Multiplying imaginary offsets gives a radical for the block's source sign character. -/
def fibreBlockRadical (t : ℝ) (m : ℕ) : fullFibreZeroExtension :=
  ∏ p : FibrePositivePairs t m, fibreImaginaryOffset t p.val

/-- The arithmetic block character is the actual action on its offset radical. -/
theorem fibreBlockRadical_aut (t : ℝ) (m : ℕ)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :
    σ (fibreBlockRadical t m) =
      ((fibreBlockSignCharacter t m σ : ℤ) : fullFibreZeroExtension)*fibreBlockRadical t m := by
  let π := fibreDivisorAction t σ
  let a := fibreSignedCoordinates t m π
  let v : ℤˣ →* fullFibreZeroExtension := (Int.castRingHom fullFibreZeroExtension).toMonoidHom.comp
    { toFun := fun u => (u : ℤ), map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hp (p : FibrePositivePairs t m) :
      σ (fibreImaginaryOffset t p.val) =
        v (a.sign (a.perm p))*fibreImaginaryOffset t (a.perm p).val := by
    rw [fibreImaginaryOffset_aut]
    exact fibreImaginaryOffset_pair_permutation t m π p
  change σ (∏ p : FibrePositivePairs t m, fibreImaginaryOffset t p.val) =
    v (∏ p : FibrePositivePairs t m, a.sign p)*
      (∏ p : FibrePositivePairs t m, fibreImaginaryOffset t p.val)
  rw [map_prod]
  calc
    ∏ p : FibrePositivePairs t m, σ (fibreImaginaryOffset t p.val) =
      ∏ p : FibrePositivePairs t m, v (a.sign (a.perm p))*fibreImaginaryOffset t (a.perm p).val :=
      Finset.prod_congr rfl (fun p _ => hp p)
    _ = (∏ p : FibrePositivePairs t m, v (a.sign (a.perm p)))*
        (∏ p : FibrePositivePairs t m, fibreImaginaryOffset t (a.perm p).val) :=
      Finset.prod_mul_distrib
    _ = v (∏ p : FibrePositivePairs t m, a.sign p)*
        (∏ p : FibrePositivePairs t m, fibreImaginaryOffset t p.val) := by
      rw [← map_prod,Equiv.prod_comp a.perm a.sign,
        Equiv.prod_comp a.perm (fun p => fibreImaginaryOffset t p.val)]

/-- The square of the radical is the source product with its exact conjugation sign. -/
theorem fibreBlockRadical_sq (t : ℝ) (m : ℕ) :
    (fibreBlockRadical t m)^2 =
      (-1 : fullFibreZeroExtension)^Nat.card (FibrePositivePairs t m)*
        algebraMap fullFibreSourceField fullFibreZeroExtension (fibreBlockSourceUnit t m : fullFibreSourceField) := by
  have hp (p : FibrePositivePairs t m) : (fibreImaginaryOffset t p.val)^2 =
      (-1 : fullFibreZeroExtension)*evenWidthInZeroField (fibrePairSquareUnit t m p : evenWidthInReal) := by
    change (fibreImaginaryOffset t p.val)^2 =
      (-1 : fullFibreZeroExtension)*evenWidthInZeroField (fibreWidthSquare t p.val)
    rw [fibreWidthSquare_offset]
    change (fibreImaginaryOffset t p.val)^2 = -1*(-(fibreImaginaryOffset t p.val)^2)
    ring
  have ha : evenWidthInZeroField (fibreBlockSquareUnit t m : evenWidthInReal) =
      algebraMap fullFibreSourceField fullFibreZeroExtension (fibreBlockSourceUnit t m : fullFibreSourceField) := by
    have he := congrArg (fun u : evenWidthInRealˣ => evenWidthInZeroField (u : evenWidthInReal))
      (fibreBlockSourceUnit_spec t m)
    exact he.symm.trans (evenWidthInZeroField.commutes (fibreBlockSourceUnit t m : fullFibreSourceField))
  change (∏ p : FibrePositivePairs t m, fibreImaginaryOffset t p.val)^2 = _
  rw [← Finset.prod_pow]
  calc
    ∏ p : FibrePositivePairs t m, (fibreImaginaryOffset t p.val)^2 =
      ∏ p : FibrePositivePairs t m,
        (-1 : fullFibreZeroExtension)*evenWidthInZeroField (fibrePairSquareUnit t m p : evenWidthInReal) :=
      Finset.prod_congr rfl (fun p _ => hp p)
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_eq_nat_card,
        ← fibreBlockSquareUnit_image,ha]

/-- The block radical is nonzero, including the empty block whose product is one. -/
theorem fibreBlockRadical_ne_zero (t : ℝ) (m : ℕ) : fibreBlockRadical t m ≠ 0 := by
  have ha : algebraMap fullFibreSourceField fullFibreZeroExtension
      (fibreBlockSourceUnit t m : fullFibreSourceField) ≠ 0 := by
    intro h
    apply (fibreBlockSourceUnit t m).ne_zero
    exact (algebraMap fullFibreSourceField fullFibreZeroExtension).injective
      (h.trans (map_zero _).symm)
  intro h
  have he := fibreBlockRadical_sq t m
  rw [h,zero_pow (by norm_num)] at he
  exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ha) he.symm

/-- The character kernel consists exactly of automorphisms fixing its nonzero radical. -/
theorem fibreBlockSignCharacter_eq_one_iff (t : ℝ) (m : ℕ)
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :
    fibreBlockSignCharacter t m σ = 1 ↔ σ (fibreBlockRadical t m) = fibreBlockRadical t m := by
  constructor
  · intro h
    rw [fibreBlockRadical_aut,h,Units.val_one,Int.cast_one,one_mul]
  · intro h
    have he : ((fibreBlockSignCharacter t m σ : ℤ) : fullFibreZeroExtension)*fibreBlockRadical t m =
        1*fibreBlockRadical t m := by rw [one_mul,← fibreBlockRadical_aut,h]
    have hc := mul_right_cancel₀ (fibreBlockRadical_ne_zero t m) he
    rcases Int.units_eq_one_or (fibreBlockSignCharacter t m σ) with h1 | hn
    · exact h1
    · rw [hn] at hc
      norm_num at hc

/-- The simple source extension generated by a complete block's offset radical. -/
def fibreBlockCharacterField (t : ℝ) (m : ℕ) :
    IntermediateField fullFibreSourceField fullFibreZeroExtension :=
  fullFibreSourceField⟮fibreBlockRadical t m⟯

/-- The character kernel fixes exactly its radical-generated intermediate field. -/
theorem fibreBlockSignCharacter_kernel (t : ℝ) (m : ℕ) :
    (fibreBlockSignCharacter t m).ker = (fibreBlockCharacterField t m).fixingSubgroup := by
  apply le_antisymm
  · apply (IntermediateField.le_iff_le _ _).mp
    apply IntermediateField.adjoin_simple_le_iff.mpr
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact (fibreBlockSignCharacter_eq_one_iff t m σ).mp hσ
  · intro σ hσ
    change fibreBlockSignCharacter t m σ = 1
    apply (fibreBlockSignCharacter_eq_one_iff t m σ).mpr
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ (fibreBlockRadical t m)
      (IntermediateField.mem_adjoin_simple_self fullFibreSourceField (fibreBlockRadical t m))

/-- Infinite Galois correspondence identifies the exact field detected by the block character. -/
theorem fibreBlockCharacterField_fixedField (t : ℝ) (m : ℕ) :
    IntermediateField.fixedField (fibreBlockSignCharacter t m).ker = fibreBlockCharacterField t m := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  rw [fibreBlockSignCharacter_kernel,InfiniteGalois.fixedField_fixingSubgroup]

private theorem fibreBlockRadical_square_source (t : ℝ) (m : ℕ) :
    fibreBlockRadical t m*fibreBlockRadical t m =
      algebraMap fullFibreSourceField fullFibreZeroExtension
        ((-1 : fullFibreSourceField)^Nat.card (FibrePositivePairs t m)*
          (fibreBlockSourceUnit t m : fullFibreSourceField)) := by
  rw [← pow_two,map_mul,map_pow,map_neg,map_one]
  exact fibreBlockRadical_sq t m

/-- Each complete block detects a source extension of degree one or two. -/
theorem fibreBlockCharacterField_degree (t : ℝ) (m : ℕ) :
    Module.finrank fullFibreSourceField (fibreBlockCharacterField t m) = 1 ∨
      Module.finrank fullFibreSourceField (fibreBlockCharacterField t m) = 2 := by
  classical
  by_cases hb : fibreBlockRadical t m ∈
      (⊥ : IntermediateField fullFibreSourceField fullFibreZeroExtension)
  · left
    apply IntermediateField.finrank_eq_one_iff.mpr
    exact le_antisymm (IntermediateField.adjoin_simple_le_iff.mpr hb) bot_le
  · right
    exact HTGeometry.finrank_adjoin_eq_two (fibreBlockRadical_square_source t m) hb

/-- Odd pair count makes conjugation act nontrivially on the block's source character. -/
theorem fibreBlockSignCharacter_conjugation_of_odd (t : ℝ) (m : ℕ)
    (hodd : Odd (Nat.card (FibrePositivePairs t m))) :
    fibreBlockSignCharacter t m fullFibreZeroConjugation = -1 := by
  obtain ⟨k,hk⟩ := hodd
  have hn : Nat.card (FibrePositivePairs t m) = 2*k+1 := by omega
  rw [fibreBlockSignCharacter_conjugation,hn]
  apply Units.ext
  change (-1 : ℤ)^(2*k+1) = -1
  rw [pow_add,pow_mul]
  norm_num

/-- An odd complete block gives a genuine quadratic source field on which conjugation is nontrivial. -/
theorem fibreBlockCharacterField_degree_two_of_odd (t : ℝ) (m : ℕ)
    (hodd : Odd (Nat.card (FibrePositivePairs t m))) :
    Module.finrank fullFibreSourceField (fibreBlockCharacterField t m) = 2 := by
  apply HTGeometry.finrank_adjoin_eq_two (fibreBlockRadical_square_source t m)
  intro hb
  obtain ⟨a,ha⟩ := IntermediateField.mem_bot.mp hb
  have hfix : fullFibreZeroConjugation (fibreBlockRadical t m) = fibreBlockRadical t m := by
    rw [← ha]
    exact fullFibreZeroConjugation.commutes a
  have hχ := (fibreBlockSignCharacter_eq_one_iff t m fullFibreZeroConjugation).mpr hfix
  rw [fibreBlockSignCharacter_conjugation_of_odd t m hodd] at hχ
  have he := congrArg (fun u : ℤˣ => (u : ℤ)) hχ
  norm_num at he

end GaloisForLFunctions.GaloisTheoryOfZeros
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibreWidthSquare_aut
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibreBlockSquareUnit_from_source
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibreBlockSourceUnit_class
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthRestrictionSplits_of_odd_fibre_pairs
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibre_pair_count_dichotomy
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibreBlockSignCharacter_continuous
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibreBlockSignCharacter_conjugation
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibreBlockRadical_aut
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibreBlockRadical_sq
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibreBlockRadical_ne_zero
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibreBlockSignCharacter_eq_one_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibreBlockCharacterField_fixedField
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibreBlockCharacterField_degree
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibreBlockCharacterField_degree_two_of_odd
