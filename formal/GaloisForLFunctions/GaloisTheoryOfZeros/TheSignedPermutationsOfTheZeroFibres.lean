import GaloisForLFunctions.GaloisTheoryOfZeros.TheFiniteSourceCompositaOfTheZeros

/-!
# Signed coordinates on the complete zero fibres

Choosing the positive-imaginary representative of each conjugate pair exposes
its independent sign and pair permutation. Analytic multiplicity separates the
permutation blocks; a fibre's possible real root contributes no symmetry.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- A pair permutation and one sign per output pair. -/
@[ext] structure FibreSignedPerm (α : Type*) where
  perm : Equiv.Perm α
  sign : α → ℤˣ

namespace FibreSignedPerm
variable {α : Type*}

private theorem perm_mul_apply (a b : Equiv.Perm α) (x : α) : (a*b) x = a (b x) := rfl

private theorem perm_inv_apply_apply (a : Equiv.Perm α) (x : α) : a⁻¹ (a x) = x := by
  change (a⁻¹*a) x = x
  rw [inv_mul_cancel]
  rfl

private theorem perm_apply_inv_apply (a : Equiv.Perm α) (x : α) : a (a⁻¹ x) = x := by
  change (a*a⁻¹) x = x
  rw [mul_inv_cancel]
  rfl

instance : Mul (FibreSignedPerm α) where
  mul a b := ⟨a.perm*b.perm,fun x => a.sign x*b.sign (a.perm⁻¹ x)⟩

instance : One (FibreSignedPerm α) where
  one := ⟨1,fun _ => 1⟩

instance : Inv (FibreSignedPerm α) where
  inv a := ⟨a.perm⁻¹,fun x => (a.sign (a.perm x))⁻¹⟩

@[simp] theorem mul_perm (a b : FibreSignedPerm α) : (a*b).perm = a.perm*b.perm := rfl
@[simp] theorem mul_sign (a b : FibreSignedPerm α) (x : α) :
    (a*b).sign x = a.sign x*b.sign (a.perm⁻¹ x) := rfl
@[simp] theorem one_perm : (1 : FibreSignedPerm α).perm = 1 := rfl
@[simp] theorem one_sign (x : α) : (1 : FibreSignedPerm α).sign x = 1 := rfl
@[simp] theorem inv_perm (a : FibreSignedPerm α) : (a⁻¹).perm = a.perm⁻¹ := rfl
@[simp] theorem inv_sign (a : FibreSignedPerm α) (x : α) :
    (a⁻¹).sign x = (a.sign (a.perm x))⁻¹ := rfl

/-- Output signs compose by the permutation action on their index set. -/
instance : Group (FibreSignedPerm α) where
  mul_assoc a b c := by
    apply FibreSignedPerm.ext
    · exact mul_assoc a.perm b.perm c.perm
    · funext x
      simp only [mul_sign,mul_perm,mul_inv_rev,perm_mul_apply,mul_assoc]
  one_mul a := by
    apply FibreSignedPerm.ext
    · exact one_mul a.perm
    · funext x
      change (1 : ℤˣ)*a.sign ((1 : Equiv.Perm α)⁻¹ x) = a.sign x
      rw [inv_one]
      exact one_mul (a.sign x)
  mul_one a := by
    apply FibreSignedPerm.ext
    · exact mul_one a.perm
    · funext x
      exact mul_one (a.sign x)
  inv_mul_cancel a := by
    apply FibreSignedPerm.ext
    · exact inv_mul_cancel a.perm
    · funext x
      change (a.sign (a.perm x))⁻¹*a.sign ((a.perm⁻¹)⁻¹ x) = 1
      rw [inv_inv,inv_mul_cancel]

/-- The usual signed action on labelled two-point pairs. -/
def pairPerm (a : FibreSignedPerm α) : Equiv.Perm (α×ℤˣ) where
  toFun x := (a.perm x.1,a.sign (a.perm x.1)*x.2)
  invFun x := (a.perm⁻¹ x.1,(a.sign x.1)⁻¹*x.2)
  left_inv x := by
    rcases x with ⟨x,u⟩
    apply Prod.ext
    · exact perm_inv_apply_apply a.perm x
    · change (a.sign (a.perm x))⁻¹*(a.sign (a.perm x)*u) = u
      rw [← mul_assoc,inv_mul_cancel,one_mul]
  right_inv x := by
    rcases x with ⟨x,u⟩
    apply Prod.ext
    · exact perm_apply_inv_apply a.perm x
    · change a.sign (a.perm (a.perm⁻¹ x))*((a.sign x)⁻¹*u) = u
      rw [perm_apply_inv_apply,← mul_assoc,mul_inv_cancel,one_mul]

/-- Signed coordinates give a faithful permutation representation. -/
def pairAction : FibreSignedPerm α →* Equiv.Perm (α×ℤˣ) where
  toFun := pairPerm
  map_one' := by
    apply Equiv.ext
    rintro ⟨x,u⟩
    apply Prod.ext
    · rfl
    · exact one_mul u
  map_mul' a b := by
    apply Equiv.ext
    rintro ⟨x,u⟩
    apply Prod.ext
    · rfl
    · change (a.sign (a.perm (b.perm x))*b.sign (a.perm⁻¹ (a.perm (b.perm x))))*u =
        a.sign (a.perm (b.perm x))*(b.sign (b.perm x)*u)
      rw [perm_inv_apply_apply,mul_assoc]

theorem pairAction_injective : Function.Injective (pairAction (α := α)) := by
  intro a b h
  have hp : a.perm = b.perm := by
    apply Equiv.ext
    intro x
    have he := congrArg (fun e : Equiv.Perm (α×ℤˣ) => e (x,1)) h
    exact congrArg Prod.fst he
  apply FibreSignedPerm.ext hp
  funext x
  have he := congrArg (fun e : Equiv.Perm (α×ℤˣ) => e (a.perm⁻¹ x,1)) h
  have hs := congrArg Prod.snd he
  change a.sign (a.perm (a.perm⁻¹ x))*1 = b.sign (b.perm (a.perm⁻¹ x))*1 at hs
  rwa [← hp,perm_apply_inv_apply,mul_one,mul_one] at hs

/-- The common involution swaps the two points of every pair. -/
def pairFlip (α : Type*) : Equiv.Perm (α×ℤˣ) where
  toFun x := (x.1,-x.2)
  invFun x := (x.1,-x.2)
  left_inv x := by rcases x with ⟨x,u⟩; simp
  right_inv x := by rcases x with ⟨x,u⟩; simp

private theorem unit_mul_neg (u v : ℤˣ) : u*(-v) = -(u*v) := by
  apply Units.ext
  change (u : ℤ)*(-(v : ℤ)) = -((u : ℤ)*(v : ℤ))
  exact mul_neg _ _

/-- Every signed permutation commutes with the common pair swap. -/
theorem pairAction_commutes (a : FibreSignedPerm α) :
    pairAction a * pairFlip α = pairFlip α * pairAction a := by
  apply Equiv.ext
  rintro ⟨x,u⟩
  apply Prod.ext
  · rfl
  · exact unit_mul_neg (a.sign (a.perm x)) u

private theorem pair_formula (π : Equiv.Perm (α×ℤˣ))
    (hc : π*pairFlip α = pairFlip α*π) (x : α) (u : ℤˣ) :
    π (x,u) = ((π (x,1)).1,(π (x,1)).2*u) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [mul_one]
  · have he := congrArg (fun e : Equiv.Perm (α×ℤˣ) => e (x,1)) hc
    change π (x,-1) = ((π (x,1)).1,-(π (x,1)).2) at he
    rw [he]
    apply Prod.ext
    · rfl
    · have hn : (π (x,1)).2*(-1) = -(π (x,1)).2 := by
        rw [unit_mul_neg,mul_one]
      exact hn.symm

private theorem pair_base_injective (π : Equiv.Perm (α×ℤˣ))
    (hc : π*pairFlip α = pairFlip α*π) :
    Function.Injective (fun x : α => (π (x,1)).1) := by
  intro x y hxy
  let u : ℤˣ := (π (y,1)).2⁻¹*(π (x,1)).2
  have he : π (x,1) = π (y,u) := by
    rw [pair_formula π hc x 1,pair_formula π hc y u]
    apply Prod.ext
    · exact hxy
    · dsimp only [u]
      rw [mul_one,← mul_assoc,mul_inv_cancel,one_mul]
  exact congrArg Prod.fst (π.injective he)

private theorem pair_base_surjective (π : Equiv.Perm (α×ℤˣ))
    (hc : π*pairFlip α = pairFlip α*π) :
    Function.Surjective (fun x : α => (π (x,1)).1) := by
  intro x
  obtain ⟨⟨y,u⟩,hy⟩ := π.surjective (x,1)
  rw [pair_formula π hc y u] at hy
  exact ⟨y,congrArg Prod.fst hy⟩

private def pairBasePerm (π : Equiv.Perm (α×ℤˣ))
    (hc : π*pairFlip α = pairFlip α*π) : Equiv.Perm α :=
  Equiv.ofBijective (fun x => (π (x,1)).1)
    ⟨pair_base_injective π hc,pair_base_surjective π hc⟩

/-- Commutation with the pair swap supplies both pair permutation and output signs. -/
def ofPairPerm (π : Equiv.Perm (α×ℤˣ))
    (hc : π*pairFlip α = pairFlip α*π) : FibreSignedPerm α where
  perm := pairBasePerm π hc
  sign x := (π ((pairBasePerm π hc).symm x,1)).2

/-- Signed coordinates recover every permutation commuting with the pair swap. -/
theorem pairAction_ofPairPerm (π : Equiv.Perm (α×ℤˣ))
    (hc : π*pairFlip α = pairFlip α*π) : pairAction (ofPairPerm π hc) = π := by
  apply Equiv.ext
  rintro ⟨x,u⟩
  change ((pairBasePerm π hc) x,
    (π ((pairBasePerm π hc).symm ((pairBasePerm π hc) x),1)).2*u) = π (x,u)
  rw [Equiv.symm_apply_apply]
  exact (pair_formula π hc x u).symm

/-- The common swap centralizer is exactly the signed permutation group. -/
theorem mem_pairAction_range_iff (π : Equiv.Perm (α×ℤˣ)) :
    π ∈ Set.range (pairAction (α := α)) ↔ π*pairFlip α = pairFlip α*π := by
  constructor
  · rintro ⟨a,rfl⟩
    exact pairAction_commutes a
  · intro hc
    exact ⟨ofPairPerm π hc,pairAction_ofPairPerm π hc⟩


/-- Reverse every pair without permuting the pair labels. -/
def uniformFlip (α : Type*) : FibreSignedPerm α := ⟨1,fun _ => -1⟩

/-- The uniform negative sign is the common pair swap. -/
theorem pairAction_uniformFlip (α : Type*) : pairAction (uniformFlip α) = pairFlip α := by
  apply Equiv.ext
  rintro ⟨x,u⟩
  apply Prod.ext
  · rfl
  · apply Units.ext
    change (-1 : ℤ)*(u : ℤ) = -(u : ℤ)
    exact neg_one_mul (u : ℤ)

end FibreSignedPerm

/-- Every support point has the ordinate labelling its complete fibre. -/
theorem fibreZeroSupport_re (t : ℝ) (z : ↥(fibreZeroSupport t)) : (z : ℂ).re = t := by
  classical
  obtain ⟨q,hq,hqz⟩ := Finset.mem_image.mp z.property
  rw [← hqz]
  exact (mem_ordinateFibreCopies t q).mp hq

/-- The support involution is actual complex conjugation. -/
theorem fibreConjugation_coe (t : ℝ) (z : ↥(fibreZeroSupport t)) :
    (fibreConjugation t z : ℂ) = (starRingEnd ℂ) (z : ℂ) := rfl

/-- Conjugation reverses the signed width. -/
theorem fibreConjugation_im (t : ℝ) (z : ↥(fibreZeroSupport t)) :
    (fibreConjugation t z : ℂ).im = -(z : ℂ).im := rfl

/-- Conjugating twice fixes every support point. -/
theorem fibreConjugation_involutive (t : ℝ) : Function.Involutive (fibreConjugation t) := by
  intro z
  apply Subtype.ext
  rw [fibreConjugation_coe,fibreConjugation_coe]
  exact star_star (z : ℂ)

/-- The fixed support points are precisely the real zeros. -/
theorem fibreConjugation_fixed_iff (t : ℝ) (z : ↥(fibreZeroSupport t)) :
    fibreConjugation t z = z ↔ (z : ℂ).im = 0 := by
  constructor
  · intro h
    have hi := congrArg (fun u : ↥(fibreZeroSupport t) => (u : ℂ).im) h
    rw [fibreConjugation_im] at hi
    linarith only [hi]
  · intro h
    apply Subtype.ext
    apply Complex.ext
    · rfl
    · rw [fibreConjugation_im,h,neg_zero]

/-- A complete ordinate fibre has at most one real support point. -/
theorem fibre_real_root_unique (t : ℝ) (z u : ↥(fibreZeroSupport t))
    (hz : (z : ℂ).im = 0) (hu : (u : ℂ).im = 0) : z = u := by
  apply Subtype.ext
  apply Complex.ext
  · exact (fibreZeroSupport_re t z).trans (fibreZeroSupport_re t u).symm
  · exact hz.trans hu.symm

/-- Conjugate roots have equal analytic multiplicity. -/
theorem fibreConjugation_multiplicity (t : ℝ) (z : ↥(fibreZeroSupport t)) :
    fibreMultiplicity t (fibreConjugation t z) = fibreMultiplicity t z :=
  fibrePermutation_preserves_multiplicity t fullFibreZeroConjugation z

/-- The nonreal roots in a fixed analytic-multiplicity class. -/
def FibreNonrealBlock (t : ℝ) (m : ℕ) :=
  {z : ↥(fibreZeroSupport t) // (z : ℂ).im ≠ 0 ∧ fibreMultiplicity t z = m}

/-- Positive-imaginary representatives of the conjugate pairs of multiplicity `m`. -/
def FibrePositivePairs (t : ℝ) (m : ℕ) :=
  {z : ↥(fibreZeroSupport t) // 0 < (z : ℂ).im ∧ fibreMultiplicity t z = m}

private def fibrePairRoot (t : ℝ) (m : ℕ) (p : FibrePositivePairs t m × ℤˣ) :
    FibreNonrealBlock t m := by
  classical
  exact if p.2 = 1 then ⟨p.1.val,ne_of_gt p.1.property.1,p.1.property.2⟩
    else ⟨fibreConjugation t p.1.val,by
      rw [fibreConjugation_im]
      exact neg_ne_zero.mpr (ne_of_gt p.1.property.1),by
      rw [fibreConjugation_multiplicity]
      exact p.1.property.2⟩

private theorem fibrePairRoot_pos (t : ℝ) (m : ℕ) (p : FibrePositivePairs t m) :
    (fibrePairRoot t m (p,1)).val = p.val := by
  classical
  simp [fibrePairRoot]

private theorem fibrePairRoot_neg (t : ℝ) (m : ℕ) (p : FibrePositivePairs t m) :
    (fibrePairRoot t m (p,-1)).val = fibreConjugation t p.val := by
  classical
  have h : (-1 : ℤˣ) ≠ 1 := by intro h; have := congrArg (fun u : ℤˣ => (u : ℤ)) h; norm_num at this
  simp only [fibrePairRoot,if_neg h]

private theorem fibrePairRoot_injective (t : ℝ) (m : ℕ) :
    Function.Injective (fibrePairRoot t m) := by
  rintro ⟨p,u⟩ ⟨q,v⟩ h
  have hv := congrArg (fun z : FibreNonrealBlock t m => z.val) h
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl
  · rw [fibrePairRoot_pos,fibrePairRoot_pos] at hv
    exact Prod.ext (Subtype.ext hv) rfl
  · rw [fibrePairRoot_pos,fibrePairRoot_neg] at hv
    have hi := congrArg (fun z : ↥(fibreZeroSupport t) => (z : ℂ).im) hv
    rw [fibreConjugation_im] at hi
    linarith only [hi,p.property.1,q.property.1]
  · rw [fibrePairRoot_neg,fibrePairRoot_pos] at hv
    have hi := congrArg (fun z : ↥(fibreZeroSupport t) => (z : ℂ).im) hv
    rw [fibreConjugation_im] at hi
    linarith only [hi,p.property.1,q.property.1]
  · rw [fibrePairRoot_neg,fibrePairRoot_neg] at hv
    exact Prod.ext (Subtype.ext ((fibreConjugation t).injective hv)) rfl

private theorem fibrePairRoot_surjective (t : ℝ) (m : ℕ) :
    Function.Surjective (fibrePairRoot t m) := by
  intro z
  rcases lt_or_gt_of_ne z.property.1 with hn | hp
  · let p : FibrePositivePairs t m := ⟨fibreConjugation t z.val,by
      rw [fibreConjugation_im]
      exact neg_pos.mpr hn,by
      rw [fibreConjugation_multiplicity]
      exact z.property.2⟩
    refine ⟨(p,-1),Subtype.ext ?_⟩
    rw [fibrePairRoot_neg]
    exact fibreConjugation_involutive t z.val
  · let p : FibrePositivePairs t m := ⟨z.val,hp,z.property.2⟩
    exact ⟨(p,1),Subtype.ext (fibrePairRoot_pos t m p)⟩

/-- Every nonreal multiplicity block is exactly its positive representatives times two signs. -/
def fibrePairEquiv (t : ℝ) (m : ℕ) :
    (FibrePositivePairs t m × ℤˣ) ≃ FibreNonrealBlock t m :=
  Equiv.ofBijective (fibrePairRoot t m)
    ⟨fibrePairRoot_injective t m,fibrePairRoot_surjective t m⟩

/-- The common sign flip corresponds to complex conjugation on each analytic block. -/
theorem fibrePairEquiv_flip (t : ℝ) (m : ℕ) (p : FibrePositivePairs t m × ℤˣ) :
    (fibrePairEquiv t m (FibreSignedPerm.pairFlip _ p)).val =
      fibreConjugation t (fibrePairEquiv t m p).val := by
  rcases p with ⟨p,u⟩
  rcases Int.units_eq_one_or u with rfl | rfl
  · change (fibrePairRoot t m (p,-1)).val = fibreConjugation t (fibrePairRoot t m (p,1)).val
    rw [fibrePairRoot_neg,fibrePairRoot_pos]
  · change (fibrePairRoot t m (p,-(-1))).val = fibreConjugation t (fibrePairRoot t m (p,-1)).val
    rw [neg_neg,fibrePairRoot_pos,fibrePairRoot_neg,fibreConjugation_involutive]

private theorem fibre_symmetry_real_iff (t : ℝ) (π : fibreDivisorSymmetries t)
    (z : ↥(fibreZeroSupport t)) : (π.val z : ℂ).im = 0 ↔ (z : ℂ).im = 0 := by
  rw [← fibreConjugation_fixed_iff,← fibreConjugation_fixed_iff]
  have he := DFunLike.congr_fun π.property.1 z
  change π.val (fibreConjugation t z) = fibreConjugation t (π.val z) at he
  rw [← he]
  exact π.val.injective.eq_iff

/-- Every multiplicity-preserving fibre symmetry fixes its possible real root. -/
theorem fibre_symmetry_fixes_real (t : ℝ) (π : fibreDivisorSymmetries t)
    (z : ↥(fibreZeroSupport t)) (hz : (z : ℂ).im = 0) : π.val z = z :=
  fibre_real_root_unique t (π.val z) z ((fibre_symmetry_real_iff t π z).mpr hz) hz

/-- Restriction to the nonreal roots of one analytic multiplicity. -/
def fibreBlockAction (t : ℝ) (m : ℕ) :
    fibreDivisorSymmetries t →* Equiv.Perm (FibreNonrealBlock t m) where
  toFun π := π.val.subtypePerm fun z => by
    rw [π.property.2 z]
    exact and_congr (not_congr (fibre_symmetry_real_iff t π z)) Iff.rfl
  map_one' := rfl
  map_mul' _ _ := rfl

private def permutationTransport {A B : Type*} (e : A ≃ B) :
    Equiv.Perm A →* Equiv.Perm B where
  toFun := e.permCongr
  map_one' := by
    apply Equiv.ext
    intro x
    exact e.apply_symm_apply x
  map_mul' a b := by
    apply Equiv.ext
    intro x
    change e (a (b (e.symm x))) = e (a (e.symm (e (b (e.symm x)))))
    rw [e.symm_apply_apply]

/-- The block action in positive-root and sign coordinates. -/
def fibrePairPermutation (t : ℝ) (m : ℕ) :
    fibreDivisorSymmetries t →* Equiv.Perm (FibrePositivePairs t m × ℤˣ) :=
  (permutationTransport (fibrePairEquiv t m).symm).comp (fibreBlockAction t m)

private theorem fibrePairPermutation_value (t : ℝ) (m : ℕ)
    (π : fibreDivisorSymmetries t) (p : FibrePositivePairs t m × ℤˣ) :
    (fibrePairEquiv t m (fibrePairPermutation t m π p)).val =
      π.val (fibrePairEquiv t m p).val := by
  change ((fibrePairEquiv t m) ((fibrePairEquiv t m).symm
    (fibreBlockAction t m π (fibrePairEquiv t m p)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Conjugation becomes the common sign flip, so block actions are signed permutations. -/
theorem fibrePairPermutation_commutes (t : ℝ) (m : ℕ) (π : fibreDivisorSymmetries t) :
    fibrePairPermutation t m π * FibreSignedPerm.pairFlip _ =
      FibreSignedPerm.pairFlip _ * fibrePairPermutation t m π := by
  apply Equiv.ext
  intro p
  apply (fibrePairEquiv t m).injective
  apply Subtype.ext
  change (fibrePairEquiv t m (fibrePairPermutation t m π (FibreSignedPerm.pairFlip _ p))).val =
    (fibrePairEquiv t m (FibreSignedPerm.pairFlip _ (fibrePairPermutation t m π p))).val
  rw [fibrePairPermutation_value,fibrePairEquiv_flip,fibrePairEquiv_flip,fibrePairPermutation_value]
  exact DFunLike.congr_fun π.property.1 (fibrePairEquiv t m p).val

/-- Exact signed coordinates of a multiplicity-preserving complete-fibre symmetry. -/
def fibreSignedCoordinates (t : ℝ) (m : ℕ) :
    fibreDivisorSymmetries t →* FibreSignedPerm (FibrePositivePairs t m) where
  toFun π := FibreSignedPerm.ofPairPerm (fibrePairPermutation t m π)
    (fibrePairPermutation_commutes t m π)
  map_one' := by
    apply FibreSignedPerm.pairAction_injective
    rw [FibreSignedPerm.pairAction_ofPairPerm,map_one,map_one]
  map_mul' π τ := by
    apply FibreSignedPerm.pairAction_injective
    rw [FibreSignedPerm.pairAction_ofPairPerm]
    rw [(FibreSignedPerm.pairAction (α := FibrePositivePairs t m)).map_mul]
    rw [FibreSignedPerm.pairAction_ofPairPerm,FibreSignedPerm.pairAction_ofPairPerm,
      (fibrePairPermutation t m).map_mul]

/-- The signed coordinates reproduce the original nonreal-block action. -/
theorem fibreSignedCoordinates_action (t : ℝ) (m : ℕ) (π : fibreDivisorSymmetries t) :
    FibreSignedPerm.pairAction (fibreSignedCoordinates t m π) = fibrePairPermutation t m π :=
  FibreSignedPerm.pairAction_ofPairPerm _ _

/-- All analytic multiplicity blocks together determine the entire fibre symmetry. -/
theorem fibreSignedCoordinates_injective (t : ℝ) :
    Function.Injective (fun π : fibreDivisorSymmetries t => fun m => fibreSignedCoordinates t m π) := by
  intro π τ h
  apply Subtype.ext
  apply Equiv.ext
  intro z
  by_cases hz : (z : ℂ).im = 0
  · rw [fibre_symmetry_fixes_real t π z hz,fibre_symmetry_fixes_real t τ z hz]
  · let m := fibreMultiplicity t z
    let v : FibreNonrealBlock t m := ⟨z,hz,rfl⟩
    let p := (fibrePairEquiv t m).symm v
    have he := congrArg (fun a : FibreSignedPerm (FibrePositivePairs t m) =>
      FibreSignedPerm.pairAction a p) (congrFun h m)
    rw [fibreSignedCoordinates_action,fibreSignedCoordinates_action] at he
    have hv := congrArg (fun q => (fibrePairEquiv t m q).val) he
    rw [fibrePairPermutation_value,fibrePairPermutation_value] at hv
    have hp : (fibrePairEquiv t m p).val = z :=
      congrArg (fun q : FibreNonrealBlock t m => q.val) ((fibrePairEquiv t m).apply_symm_apply v)
    rwa [hp] at hv

/-- The disjoint union of nonreal multiplicity blocks is the whole nonreal support. -/
private def fibreBlockDecomposition (t : ℝ) :
    (Σ m : ℕ, FibreNonrealBlock t m) ≃
      {z : ↥(fibreZeroSupport t) // (z : ℂ).im ≠ 0} where
  toFun z := ⟨z.2.val,z.2.property.1⟩
  invFun z := ⟨fibreMultiplicity t z.val,⟨z.val,z.property,rfl⟩⟩
  left_inv z := by
    rcases z with ⟨m,z,hz,hm⟩
    cases hm
    rfl
  right_inv _ := rfl

private def fibreBlockFrame (t : ℝ) :
    ({z : ↥(fibreZeroSupport t) // (z : ℂ).im = 0} ⊕ Σ m : ℕ, FibreNonrealBlock t m) ≃
      ↥(fibreZeroSupport t) := by
  classical
  exact (Equiv.sumCongr (Equiv.refl _) (fibreBlockDecomposition t)).trans
    (Equiv.sumCompl fun z : ↥(fibreZeroSupport t) => (z : ℂ).im = 0)

private def sumSigmaAction {R : Type*} {B : ℕ → Type*} :
    (∀ m, Equiv.Perm (B m)) →* Equiv.Perm (R ⊕ Σ m, B m) where
  toFun f := Equiv.sumCongr (Equiv.refl R) (Equiv.sigmaCongrRight f)
  map_one' := by
    apply Equiv.ext
    rintro (r | ⟨m,x⟩) <;> rfl
  map_mul' _ _ := by
    apply Equiv.ext
    rintro (r | ⟨m,x⟩) <;> rfl

private theorem permutationTransport_apply {A B : Type*} (e : A ≃ B)
    (π : Equiv.Perm A) (x : A) : permutationTransport e π (e x) = e (π x) := by
  change e (π (e.symm (e x))) = e (π x)
  rw [e.symm_apply_apply]

/-- Assemble independent signed block actions into a permutation of the entire fibre. -/
def fibreAssembledPermutation (t : ℝ)
    (a : ∀ m : ℕ, FibreSignedPerm (FibrePositivePairs t m)) : Equiv.Perm ↥(fibreZeroSupport t) :=
  permutationTransport (fibreBlockFrame t)
    (sumSigmaAction fun m => permutationTransport (fibrePairEquiv t m)
      (FibreSignedPerm.pairAction (a m)))

private theorem fibreAssembledPermutation_real (t : ℝ)
    (a : ∀ m : ℕ, FibreSignedPerm (FibrePositivePairs t m))
    (z : ↥(fibreZeroSupport t)) (hz : (z : ℂ).im = 0) :
    fibreAssembledPermutation t a z = z := by
  exact permutationTransport_apply (fibreBlockFrame t)
    (sumSigmaAction fun m => permutationTransport (fibrePairEquiv t m)
      (FibreSignedPerm.pairAction (a m))) (Sum.inl ⟨z,hz⟩)

private theorem fibreAssembledPermutation_block (t : ℝ)
    (a : ∀ m : ℕ, FibreSignedPerm (FibrePositivePairs t m))
    (m : ℕ) (p : FibrePositivePairs t m × ℤˣ) :
    fibreAssembledPermutation t a (fibrePairEquiv t m p).val =
      (fibrePairEquiv t m (FibreSignedPerm.pairAction (a m) p)).val := by
  have h := permutationTransport_apply (fibreBlockFrame t)
    (sumSigmaAction fun k => permutationTransport (fibrePairEquiv t k)
      (FibreSignedPerm.pairAction (a k))) (Sum.inr ⟨m,fibrePairEquiv t m p⟩)
  change fibreAssembledPermutation t a (fibrePairEquiv t m p).val =
    (permutationTransport (fibrePairEquiv t m) (FibreSignedPerm.pairAction (a m))
      (fibrePairEquiv t m p)).val at h
  rw [permutationTransport_apply] at h
  exact h

private theorem fibreAssembledPermutation_multiplicity (t : ℝ)
    (a : ∀ m : ℕ, FibreSignedPerm (FibrePositivePairs t m))
    (z : ↥(fibreZeroSupport t)) :
    fibreMultiplicity t (fibreAssembledPermutation t a z) = fibreMultiplicity t z := by
  by_cases hz : (z : ℂ).im = 0
  · rw [fibreAssembledPermutation_real t a z hz]
  · let m := fibreMultiplicity t z
    let v : FibreNonrealBlock t m := ⟨z,hz,rfl⟩
    obtain ⟨p,hp⟩ := (fibrePairEquiv t m).surjective v
    have hval : (fibrePairEquiv t m p).val = z := congrArg Subtype.val hp
    rw [← hval,fibreAssembledPermutation_block]
    exact ((fibrePairEquiv t m (FibreSignedPerm.pairAction (a m) p)).property.2).trans
      (fibrePairEquiv t m p).property.2.symm

private theorem fibreAssembledPermutation_commutes (t : ℝ)
    (a : ∀ m : ℕ, FibreSignedPerm (FibrePositivePairs t m)) :
    fibreAssembledPermutation t a * fibreConjugation t =
      fibreConjugation t * fibreAssembledPermutation t a := by
  apply Equiv.ext
  intro z
  change fibreAssembledPermutation t a (fibreConjugation t z) =
    fibreConjugation t (fibreAssembledPermutation t a z)
  by_cases hz : (z : ℂ).im = 0
  · rw [(fibreConjugation_fixed_iff t z).mpr hz,fibreAssembledPermutation_real t a z hz]
    exact ((fibreConjugation_fixed_iff t z).mpr hz).symm
  · let m := fibreMultiplicity t z
    let v : FibreNonrealBlock t m := ⟨z,hz,rfl⟩
    obtain ⟨p,hp⟩ := (fibrePairEquiv t m).surjective v
    have hval : (fibrePairEquiv t m p).val = z := congrArg Subtype.val hp
    rw [← hval,← fibrePairEquiv_flip,fibreAssembledPermutation_block,
      fibreAssembledPermutation_block,← fibrePairEquiv_flip]
    exact congrArg (fun q => (fibrePairEquiv t m q).val)
      (DFunLike.congr_fun (FibreSignedPerm.pairAction_commutes (a m)) p)

/-- Independent signed blocks preserve the complete analytic fibre divisor. -/
def fibreAssembledSymmetry (t : ℝ)
    (a : ∀ m : ℕ, FibreSignedPerm (FibrePositivePairs t m)) : fibreDivisorSymmetries t :=
  ⟨fibreAssembledPermutation t a,
    fibreAssembledPermutation_commutes t a,fibreAssembledPermutation_multiplicity t a⟩

/-- Every family of signed block permutations occurs in the ambient fibre symmetry group. -/
theorem fibreSignedCoordinates_surjective (t : ℝ) :
    Function.Surjective (fun π : fibreDivisorSymmetries t => fun m => fibreSignedCoordinates t m π) := by
  intro a
  refine ⟨fibreAssembledSymmetry t a,?_⟩
  funext m
  apply FibreSignedPerm.pairAction_injective
  rw [fibreSignedCoordinates_action]
  apply Equiv.ext
  intro p
  apply (fibrePairEquiv t m).injective
  apply Subtype.ext
  rw [fibrePairPermutation_value]
  exact fibreAssembledPermutation_block t a m p

/-- Signed coordinates in all analytic multiplicity blocks at once. -/
def fibreSignedCoordinateFamily (t : ℝ) :
    fibreDivisorSymmetries t →* ∀ m : ℕ, FibreSignedPerm (FibrePositivePairs t m) where
  toFun π m := fibreSignedCoordinates t m π
  map_one' := by funext m; exact (fibreSignedCoordinates t m).map_one
  map_mul' π τ := by funext m; exact (fibreSignedCoordinates t m).map_mul π τ

/-- The exact weighted centralizer is the product of its signed pair-permutation groups. -/
def fibreSignedEquiv (t : ℝ) :
    fibreDivisorSymmetries t ≃* ∀ m : ℕ, FibreSignedPerm (FibrePositivePairs t m) :=
  MulEquiv.ofBijective (fibreSignedCoordinateFamily t)
    ⟨fibreSignedCoordinates_injective t,fibreSignedCoordinates_surjective t⟩

/-- Each signed permutation group is finite when its pair set is finite. -/
instance {α : Type*} [Finite α] : Finite (FibreSignedPerm α) :=
  Finite.of_injective FibreSignedPerm.pairAction FibreSignedPerm.pairAction_injective

instance (t : ℝ) (m : ℕ) : Finite (FibrePositivePairs t m) := by
  unfold FibrePositivePairs
  infer_instance

instance (α : Type*) : TopologicalSpace (FibreSignedPerm α) := ⊥
instance (α : Type*) : DiscreteTopology (FibreSignedPerm α) := ⟨rfl⟩

/-- The full infinite source group in weighted signed-permutation coordinates. -/
def allSignedFibreAction :
    (fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) →*
      (∀ (t : ℝ) (m : ℕ), FibreSignedPerm (FibrePositivePairs t m)) where
  toFun σ t m := fibreSignedCoordinates t m (fibreDivisorAction t σ)
  map_one' := by
    funext t m
    change fibreSignedCoordinates t m (fibreDivisorAction t 1) = 1
    rw [map_one,map_one]
  map_mul' σ τ := by
    funext t m
    change fibreSignedCoordinates t m (fibreDivisorAction t (σ*τ)) =
      fibreSignedCoordinates t m (fibreDivisorAction t σ) *
        fibreSignedCoordinates t m (fibreDivisorAction t τ)
    rw [map_mul,map_mul]

/-- Signed coordinates retain the action on the entire zero field. -/
theorem allSignedFibreAction_injective : Function.Injective allSignedFibreAction := by
  intro σ τ h
  apply allFibreDivisorAction_injective
  funext t
  exact fibreSignedCoordinates_injective t (congrFun h t)

/-- Every signed coordinate is continuous, hence so is the action on all fibres. -/
theorem allSignedFibreAction_continuous : Continuous allSignedFibreAction := by
  apply continuous_pi
  intro t
  apply continuous_pi
  intro m
  have hc : Continuous (fibreSignedCoordinates t m) := continuous_of_discreteTopology
  exact hc.comp (fibreDivisorAction_continuous t)

/-- Arithmetic relations cut out a closed subgroup of the full weighted signed product. -/
theorem allSignedFibreAction_range_isClosed : IsClosed (Set.range allSignedFibreAction) := by
  letI : IsGalois fullFibreSourceField fullFibreZeroExtension := ⟨⟩
  exact (isCompact_range allSignedFibreAction_continuous).isClosed

/-- Signed families extend exactly when their inverse-coordinate divisor families extend. -/
theorem allSignedFibreAction_mem_range_iff
    (a : ∀ (t : ℝ) (m : ℕ), FibreSignedPerm (FibrePositivePairs t m)) :
    a ∈ Set.range allSignedFibreAction ↔
      (fun t => (fibreSignedEquiv t).symm (a t)) ∈ Set.range allFibreDivisorAction := by
  constructor
  · rintro ⟨σ,rfl⟩
    refine ⟨σ,funext fun t => ?_⟩
    exact ((fibreSignedEquiv t).symm_apply_apply (fibreDivisorAction t σ)).symm
  · rintro ⟨σ,hσ⟩
    refine ⟨σ,funext fun t => ?_⟩
    have ht := congrArg (fibreSignedEquiv t) (congrFun hσ t)
    rw [MulEquiv.apply_symm_apply] at ht
    exact ht


/-- Source equations decide extension of a full signed family through all finite composita. -/
theorem allSignedFibreAction_source_compatibility
    (a : ∀ (t : ℝ) (m : ℕ), FibreSignedPerm (FibrePositivePairs t m)) :
    a ∈ Set.range allSignedFibreAction ↔
      ∀ S : Finset ℝ, FiniteSourceCompatibility
        (fun t => (fibreSignedEquiv t).symm (a t)) S := by
  rw [allSignedFibreAction_mem_range_iff,allFibreDivisorAction_source_compatibility]


/-- Centered conjugation is the uniform sign reversal in every nonreal multiplicity block. -/
theorem allSignedFibreAction_conjugation :
    allSignedFibreAction fullFibreZeroConjugation =
      fun t m => FibreSignedPerm.uniformFlip (FibrePositivePairs t m) := by
  funext t m
  apply FibreSignedPerm.pairAction_injective
  change FibreSignedPerm.pairAction
      (fibreSignedCoordinates t m (fibreDivisorAction t fullFibreZeroConjugation)) =
    FibreSignedPerm.pairAction (FibreSignedPerm.uniformFlip (FibrePositivePairs t m))
  rw [fibreSignedCoordinates_action,FibreSignedPerm.pairAction_uniformFlip]
  apply Equiv.ext
  intro p
  apply (fibrePairEquiv t m).injective
  apply Subtype.ext
  rw [fibrePairPermutation_value,fibrePairEquiv_flip]
  rfl

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibrePairEquiv

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fibreSignedEquiv

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.allSignedFibreAction_injective

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.allSignedFibreAction_continuous

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.allSignedFibreAction_range_isClosed

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.allSignedFibreAction_mem_range_iff

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.allSignedFibreAction_source_compatibility

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.allSignedFibreAction_conjugation
