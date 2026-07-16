import GaloisForLFunctions.HTGeometry.FiniteQuotientInteractionCohomology
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

def primeUnitResidueProfile (q : ℕ) [NeZero q] (p : Nat.Primes) : (ZMod q)ˣ :=
  if hp : IsUnit (p : ZMod q) then hp.unit else 1

theorem primeUnitResidueProfile_eq_of_cast_eq
    (q : ℕ) [NeZero q] (p : Nat.Primes) (a : (ZMod q)ˣ)
    (hpa : (p : ZMod q) = (a : ZMod q)) :
    primeUnitResidueProfile q p = a := by
  have hp : IsUnit (p : ZMod q) := hpa ▸ a.isUnit
  rw [primeUnitResidueProfile, dif_pos hp]
  apply Units.ext
  rw [IsUnit.unit_spec, hpa]

theorem recurringValueSet_primeUnitResidueProfile
    (q : ℕ) [NeZero q] :
    recurringValueSet (primeUnitResidueProfile q) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  change {p : Nat.Primes | primeUnitResidueProfile q p = a}.Infinite
  let S : Set ℕ := {n | n.Prime ∧ (n : ZMod q) = (a : ZMod q)}
  have hS : S.Infinite := Nat.infinite_setOf_prime_and_eq_mod a.isUnit
  let f : S → Nat.Primes := fun n => ⟨n.1, n.2.1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Nat.Primes => z.1) hxy
  haveI : Infinite S := hS.to_subtype
  apply Set.infinite_of_injective_forall_mem hf
  intro n
  exact primeUnitResidueProfile_eq_of_cast_eq q (f n) a n.2.2

theorem cofiniteTailDenseOn_primeUnitResidueProfile
    (q : ℕ) [NeZero q] :
    CofiniteTailDenseOn (primeUnitResidueProfile q) Set.univ :=
  cofiniteTailDenseOn_univ_of_recurringValueSet_eq_univ _
    (recurringValueSet_primeUnitResidueProfile q)

noncomputable def coprimeUnitChineseRemainderEquiv
    (m n : ℕ) (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
    MulEquiv.prodUnits

noncomputable def coprimePrimeUnitResidueProfile
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) :
    Nat.Primes → (ZMod m)ˣ × (ZMod n)ˣ := by
  letI : NeZero (m * n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  exact fun p => coprimeUnitChineseRemainderEquiv m n h
    (primeUnitResidueProfile (m * n) p)

theorem cofiniteTailDenseOn_coprimePrimeUnitResidueProfile
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) :
    CofiniteTailDenseOn (coprimePrimeUnitResidueProfile m n h) Set.univ := by
  letI : NeZero (m * n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  let e := coprimeUnitChineseRemainderEquiv m n h
  have ht := cofiniteTailDenseOn_comp_continuous
    (primeUnitResidueProfile (m * n)) Set.univ
    (cofiniteTailDenseOn_primeUnitResidueProfile (m * n))
    e continuous_of_discreteTopology
  simpa [coprimePrimeUnitResidueProfile, e, Function.comp_def] using ht

def productFstSetoid (A B : Type*) : Setoid (A × B) := Setoid.ker Prod.fst

def productSndSetoid (A B : Type*) : Setoid (A × B) := Setoid.ker Prod.snd

def productMarginalObservableSubmodule (A B : Type*) :
    Submodule ℂ (FullValueSubtype (A × B) → ℂ) :=
  ClassInvariantRestricted (productFstSetoid A B) ⊔
    ClassInvariantRestricted (productSndSetoid A B)

/-- The identity-anchored interaction space: interactions vanish on the distinguished row and
column through `(1,1)`.  For unit groups this is a canonical, closed-form representative of the
row/column interaction quotient. -/
def productAnchoredInteractionSubmodule
    (A B : Type*) [One A] [One B] :
    Submodule ℂ (FullValueSubtype (A × B) → ℂ) where
  carrier := {f | (∀ a, f ⟨(a, 1), Set.mem_univ _⟩ = 0) ∧
    ∀ b, f ⟨(1, b), Set.mem_univ _⟩ = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hfrow, hfcol⟩ ⟨hgrow, hgcol⟩
    constructor
    · intro a
      simp [hfrow a, hgrow a]
    · intro b
      simp [hfcol b, hgcol b]
  smul_mem' := by
    rintro c f ⟨hfrow, hfcol⟩
    constructor
    · intro a
      simp [hfrow a]
    · intro b
      simp [hfcol b]

def productRowPart
    (A B : Type*) [One B]
    (f : FullValueSubtype (A × B) → ℂ) :
    FullValueSubtype (A × B) → ℂ :=
  fun x => f ⟨(x.1.1, 1), Set.mem_univ _⟩

def productColumnPart
    (A B : Type*) [One A] [One B]
    (f : FullValueSubtype (A × B) → ℂ) :
    FullValueSubtype (A × B) → ℂ :=
  fun x => f ⟨(1, x.1.2), Set.mem_univ _⟩ -
    f ⟨(1, 1), Set.mem_univ _⟩

def productAnchoredInteractionPart
    (A B : Type*) [One A] [One B]
    (f : FullValueSubtype (A × B) → ℂ) :
    FullValueSubtype (A × B) → ℂ :=
  fun x => f x - productRowPart A B f x - productColumnPart A B f x

theorem productRowPart_mem_fst
    (A B : Type*) [One B]
    (f : FullValueSubtype (A × B) → ℂ) :
    productRowPart A B f ∈ ClassInvariantRestricted (productFstSetoid A B) := by
  intro x y hxy
  change x.1.1 = y.1.1 at hxy
  apply congrArg f
  apply Subtype.ext
  exact Prod.ext hxy rfl

theorem productColumnPart_mem_snd
    (A B : Type*) [One A] [One B]
    (f : FullValueSubtype (A × B) → ℂ) :
    productColumnPart A B f ∈ ClassInvariantRestricted (productSndSetoid A B) := by
  intro x y hxy
  simp only [productColumnPart]
  rw [hxy]

theorem productAnchoredInteractionPart_mem
    (A B : Type*) [One A] [One B]
    (f : FullValueSubtype (A × B) → ℂ) :
    productAnchoredInteractionPart A B f ∈
      productAnchoredInteractionSubmodule A B := by
  constructor
  · intro a
    simp [productAnchoredInteractionPart, productRowPart, productColumnPart]
  · intro b
    simp [productAnchoredInteractionPart, productRowPart, productColumnPart]

theorem product_decompose_row_column_anchored
    (A B : Type*) [One A] [One B]
    (f : FullValueSubtype (A × B) → ℂ) :
    productRowPart A B f + productColumnPart A B f +
      productAnchoredInteractionPart A B f = f := by
  funext x
  simp [productAnchoredInteractionPart]

theorem productFstSetoid_inf_productSndSetoid
    (A B : Type*) :
    productFstSetoid A B ⊓ productSndSetoid A B = ⊥ := by
  ext x y
  change (x.1 = y.1 ∧ x.2 = y.2) ↔ x = y
  exact Prod.ext_iff.symm

theorem productFstSetoid_sup_productSndSetoid
    (A B : Type*) [Nonempty A] [Nonempty B] :
    productFstSetoid A B ⊔ productSndSetoid A B = ⊤ := by
  apply top_unique
  intro x y _
  let z : A × B := (x.1, y.2)
  have hxz : (productFstSetoid A B ⊔ productSndSetoid A B) x z :=
    (show productFstSetoid A B ≤
      productFstSetoid A B ⊔ productSndSetoid A B from le_sup_left)
        (show productFstSetoid A B x z by rfl)
  have hzy : (productFstSetoid A B ⊔ productSndSetoid A B) z y :=
    (show productSndSetoid A B ≤
      productFstSetoid A B ⊔ productSndSetoid A B from le_sup_right)
        (show productSndSetoid A B z y by rfl)
  exact (productFstSetoid A B ⊔ productSndSetoid A B).trans hxz hzy

theorem classInvariantRestricted_product_inf_eq_top
    (A B : Type*) :
    ClassInvariantRestricted
      (productFstSetoid A B ⊓ productSndSetoid A B) = ⊤ := by
  rw [productFstSetoid_inf_productSndSetoid]
  apply top_unique
  intro f _ x y hxy
  have hval : x.1 = y.1 := hxy
  exact congrArg f (Subtype.ext hval)

theorem productAnchoredInteractionSubmodule_isCompl
    (A B : Type*) [One A] [One B] :
    Disjoint (productMarginalObservableSubmodule A B)
        (productAnchoredInteractionSubmodule A B) ∧
      productMarginalObservableSubmodule A B ⊔
          productAnchoredInteractionSubmodule A B =
        ClassInvariantRestricted
          (productFstSetoid A B ⊓ productSndSetoid A B) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro f hfMarginal hfAnchored
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hfMarginal
    apply funext
    intro x
    let row : FullValueSubtype (A × B) :=
      ⟨(x.1.1, 1), Set.mem_univ _⟩
    let col : FullValueSubtype (A × B) :=
      ⟨(1, x.1.2), Set.mem_univ _⟩
    let base : FullValueSubtype (A × B) :=
      ⟨(1, 1), Set.mem_univ _⟩
    have huxrow : u x = u row := hu x row (by rfl)
    have hvxcol : v x = v col := hv x col (by rfl)
    have hvrowbase : v row = v base := hv row base (by rfl)
    have hucolbase : u col = u base := hu col base (by rfl)
    have hrowzero : f row = 0 := hfAnchored.1 x.1.1
    have hcolzero : f col = 0 := hfAnchored.2 x.1.2
    have hbasezero : f base = 0 := hfAnchored.1 1
    have hrow : u row + v base = 0 := by
      rw [← hvrowbase]
      simpa [Pi.add_apply] using (congrFun huv row).trans hrowzero
    have hcol : u base + v col = 0 := by
      rw [← hucolbase]
      simpa [Pi.add_apply] using (congrFun huv col).trans hcolzero
    have hbase : u base + v base = 0 := by
      simpa [Pi.add_apply] using (congrFun huv base).trans hbasezero
    have hxsum : u row + v col = 0 := by
      linear_combination hrow + hcol - hbase
    calc
      f x = u x + v x := by
        simpa [Pi.add_apply] using congrFun huv.symm x
      _ = u row + v col := by rw [huxrow, hvxcol]
      _ = 0 := hxsum
  · apply le_antisymm
    · rw [classInvariantRestricted_product_inf_eq_top]
      exact le_top
    · intro f _
      let row := productRowPart A B f
      let col := productColumnPart A B f
      let interaction := productAnchoredInteractionPart A B f
      have hrow : row ∈ ClassInvariantRestricted (productFstSetoid A B) :=
        productRowPart_mem_fst A B f
      have hcol : col ∈ ClassInvariantRestricted (productSndSetoid A B) :=
        productColumnPart_mem_snd A B f
      have hinteraction : interaction ∈ productAnchoredInteractionSubmodule A B :=
        productAnchoredInteractionPart_mem A B f
      have hmarginal : row + col ∈ productMarginalObservableSubmodule A B :=
        Submodule.mem_sup.mpr ⟨row, hrow, col, hcol, rfl⟩
      apply Submodule.mem_sup.mpr
      exact ⟨row + col, hmarginal, interaction, hinteraction,
        product_decompose_row_column_anchored A B f⟩


noncomputable instance productFstQuotientFintype
    (A B : Type*) [Fintype A] [Fintype B] :
    Fintype (FiniteQuotientType (productFstSetoid A B)) :=
  Fintype.ofFinite _

noncomputable instance productSndQuotientFintype
    (A B : Type*) [Fintype A] [Fintype B] :
    Fintype (FiniteQuotientType (productSndSetoid A B)) :=
  Fintype.ofFinite _

noncomputable instance productInfQuotientFintype
    (A B : Type*) [Fintype A] [Fintype B] :
    Fintype (FiniteQuotientType
      (productFstSetoid A B ⊓ productSndSetoid A B)) :=
  Fintype.ofFinite _

noncomputable instance productSupQuotientFintype
    (A B : Type*) [Fintype A] [Fintype B] :
    Fintype (FiniteQuotientType
      (productFstSetoid A B ⊔ productSndSetoid A B)) :=
  Fintype.ofFinite _

noncomputable def productFstQuotientEquiv
    (A B : Type*) [Nonempty B] :
    FiniteQuotientType (productFstSetoid A B) ≃ A :=
  Setoid.quotientKerEquivOfSurjective Prod.fst Prod.fst_surjective

noncomputable def productSndQuotientEquiv
    (A B : Type*) [Nonempty A] :
    FiniteQuotientType (productSndSetoid A B) ≃ B :=
  Setoid.quotientKerEquivOfSurjective Prod.snd Prod.snd_surjective

theorem productFstQuotient_card
    (A B : Type*) [Fintype A] [Fintype B] [Nonempty B] :
    Fintype.card (FiniteQuotientType (productFstSetoid A B)) = Fintype.card A :=
  Fintype.card_congr (productFstQuotientEquiv A B)

theorem productSndQuotient_card
    (A B : Type*) [Fintype A] [Fintype B] [Nonempty A] :
    Fintype.card (FiniteQuotientType (productSndSetoid A B)) = Fintype.card B :=
  Fintype.card_congr (productSndQuotientEquiv A B)

theorem productInfQuotient_card
    (A B : Type*) [Fintype A] [Fintype B] :
    Fintype.card (FiniteQuotientType
      (productFstSetoid A B ⊓ productSndSetoid A B)) =
        Fintype.card A * Fintype.card B := by
  let e₀ : FiniteQuotientType
      (productFstSetoid A B ⊓ productSndSetoid A B) ≃
      Quotient (Setoid.ker (id : A × B → A × B)) :=
    Quotient.congrRight (fun x y => by
      change (x.1 = y.1 ∧ x.2 = y.2) ↔ x = y
      exact Prod.ext_iff.symm)
  let e : FiniteQuotientType
      (productFstSetoid A B ⊓ productSndSetoid A B) ≃ A × B :=
    e₀.trans (Setoid.quotientKerEquivOfSurjective id Function.surjective_id)
  calc
    _ = Fintype.card (A × B) := Fintype.card_congr e
    _ = _ := Fintype.card_prod A B

theorem productSupQuotient_card
    (A B : Type*) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    Fintype.card (FiniteQuotientType
      (productFstSetoid A B ⊔ productSndSetoid A B)) = 1 := by
  let e₀ : FiniteQuotientType
      (productFstSetoid A B ⊔ productSndSetoid A B) ≃
      Quotient (Setoid.ker (fun _ : A × B => ())) :=
    Quotient.congrRight (fun x y => by
      have htop : (productFstSetoid A B ⊔ productSndSetoid A B) = ⊤ :=
        productFstSetoid_sup_productSndSetoid A B
      rw [htop]
      simp)
  let e : FiniteQuotientType
      (productFstSetoid A B ⊔ productSndSetoid A B) ≃ Unit :=
    e₀.trans (Setoid.quotientKerEquivOfSurjective (fun _ => ())
      (fun _ => ⟨Classical.choice inferInstance, rfl⟩))
  calc
    _ = Fintype.card Unit := Fintype.card_congr e
    _ = 1 := Fintype.card_unit

theorem nat_mul_sub_interaction_identity
    {a b : ℕ} (hb : 1 ≤ b) :
    a * b - (a + b - 1) = (a - 1) * (b - 1) := by
  calc
    a * b - (a + b - 1) = a * b - (a + (b - 1)) := by
      rw [Nat.add_sub_assoc hb a]
    _ = (a * b - a) - (b - 1) := (Nat.sub_sub _ _ _).symm
    _ = a * (b - 1) - (b - 1) := by rw [Nat.mul_sub]; simp
    _ = (a - 1) * (b - 1) := by rw [Nat.sub_mul]; simp

theorem productFiniteQuotientInteractionDefect_eq
    (A B : Type*) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    finiteQuotientInteractionDefect
      (productFstSetoid A B) (productSndSetoid A B) =
        (Fintype.card A - 1) * (Fintype.card B - 1) := by
  rw [finiteQuotientInteractionDefect_eq_euler,
    productInfQuotient_card, productFstQuotient_card,
    productSndQuotient_card, productSupQuotient_card]
  exact nat_mul_sub_interaction_identity
    (Fintype.card_pos_iff.mpr inferInstance)

/-- Actual coprime prime residues carry a relative HT interaction block of exact totient-product
rank over the two separate-modulus fields. -/
theorem cofiniteTailDenseOn_exists_coprimePrimeResidueInteractionComplement
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) (a : ℂ) :
    ∃ Q : Submodule ℂ
        (FullValueSubtype ((ZMod m)ˣ × (ZMod n)ˣ) → ℂ),
      ∃ q : Fin (Module.finrank ℂ Q) → (ZMod m)ˣ × (ZMod n)ˣ → ℂ,
        Module.finrank ℂ Q =
            (m.totient - 1) * (n.totient - 1) ∧
        Nonempty
          (FiniteQuotientInteractionCohomology
              (productFstSetoid (ZMod m)ˣ (ZMod n)ˣ)
              (productSndSetoid (ZMod m)ˣ (ZMod n)ˣ) ≃ₗ[ℂ] Q) ∧
        GaloisForLFunctions.DifferentialIndependent
          (↥(primeFiniteQuotientShiftField
                (coprimePrimeUnitResidueProfile m n h)
                (productFstSetoid (ZMod m)ˣ (ZMod n)ˣ) a ⊔
              primeFiniteQuotientShiftField
                (coprimePrimeUnitResidueProfile m n h)
                (productSndSetoid (ZMod m)ˣ (ZMod n)ˣ) a))
          (fun j => tailDenseObservableShiftCarrier
            (coprimePrimeUnitResidueProfile m n h) (q j) a) ∧
        (primeFiniteQuotientShiftField
              (coprimePrimeUnitResidueProfile m n h)
              (productFstSetoid (ZMod m)ˣ (ZMod n)ˣ) a ⊔
            primeFiniteQuotientShiftField
              (coprimePrimeUnitResidueProfile m n h)
              (productSndSetoid (ZMod m)ˣ (ZMod n)ˣ) a) ⊔
            tailDenseObservableShiftField
              (coprimePrimeUnitResidueProfile m n h) q a =
          primeFiniteQuotientShiftField
            (coprimePrimeUnitResidueProfile m n h)
            (productFstSetoid (ZMod m)ˣ (ZMod n)ˣ ⊓
              productSndSetoid (ZMod m)ˣ (ZMod n)ˣ) a := by
  let y := coprimePrimeUnitResidueProfile m n h
  let r := productFstSetoid (ZMod m)ˣ (ZMod n)ˣ
  let s := productSndSetoid (ZMod m)ˣ (ZMod n)ˣ
  have hy : CofiniteTailDenseOn y Set.univ :=
    cofiniteTailDenseOn_coprimePrimeUnitResidueProfile m n h
  obtain ⟨Q, q, hQV, hUQ, hsup, hrank, hcoh, hLI, hspan, hDI, hfield⟩ :=
    cofiniteTailDenseOn_exists_primeFiniteQuotientInteractionComplement
      y hy r s a
  refine ⟨Q, q, ?_, ?_, ?_, ?_⟩
  · rw [hrank, productFiniteQuotientInteractionDefect_eq,
      ZMod.card_units_eq_totient, ZMod.card_units_eq_totient]
  · exact hcoh
  · exact hDI
  · exact hfield

/-- The coprime prime-residue interaction block has a canonical representative: the joint
observables whose distinguished identity row and identity column vanish. -/
theorem cofiniteTailDenseOn_coprimePrimeResidueAnchoredInteraction
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) (a : ℂ) :
    let A := (ZMod m)ˣ
    let B := (ZMod n)ˣ
    let Q := productAnchoredInteractionSubmodule A B
    ∃ q : Fin (Module.finrank ℂ Q) → A × B → ℂ,
      Disjoint (productMarginalObservableSubmodule A B) Q ∧
      productMarginalObservableSubmodule A B ⊔ Q =
        ClassInvariantRestricted
          (productFstSetoid A B ⊓ productSndSetoid A B) ∧
      Module.finrank ℂ Q = (m.totient - 1) * (n.totient - 1) ∧
      Nonempty
        (FiniteQuotientInteractionCohomology
            (productFstSetoid A B) (productSndSetoid A B) ≃ₗ[ℂ] Q) ∧
      GaloisForLFunctions.DifferentialIndependent
        (↥(primeFiniteQuotientShiftField
              (coprimePrimeUnitResidueProfile m n h)
              (productFstSetoid A B) a ⊔
            primeFiniteQuotientShiftField
              (coprimePrimeUnitResidueProfile m n h)
              (productSndSetoid A B) a))
        (fun j => tailDenseObservableShiftCarrier
          (coprimePrimeUnitResidueProfile m n h) (q j) a) ∧
      (primeFiniteQuotientShiftField
            (coprimePrimeUnitResidueProfile m n h)
            (productFstSetoid A B) a ⊔
          primeFiniteQuotientShiftField
            (coprimePrimeUnitResidueProfile m n h)
            (productSndSetoid A B) a) ⊔
          tailDenseObservableShiftField
            (coprimePrimeUnitResidueProfile m n h) q a =
        primeFiniteQuotientShiftField
          (coprimePrimeUnitResidueProfile m n h)
          (productFstSetoid A B ⊓ productSndSetoid A B) a := by
  dsimp only
  let A := (ZMod m)ˣ
  let B := (ZMod n)ˣ
  let y := coprimePrimeUnitResidueProfile m n h
  let r := productFstSetoid A B
  let s := productSndSetoid A B
  let Ur := ClassInvariantRestricted r
  let Us := ClassInvariantRestricted s
  let U := Ur ⊔ Us
  let V := ClassInvariantRestricted (r ⊓ s)
  let Q := productAnchoredInteractionSubmodule A B
  have hy : CofiniteTailDenseOn y Set.univ :=
    cofiniteTailDenseOn_coprimePrimeUnitResidueProfile m n h
  have hcompl := productAnchoredInteractionSubmodule_isCompl A B
  have hUQ : Disjoint U Q := hcompl.1
  have hsup : U ⊔ Q = V := hcompl.2
  have hQV : Q ≤ V := by
    rw [← hsup]
    exact le_sup_right
  letI : FiniteDimensional ℂ Ur :=
    classInvariantRestrictedFiniteDimensional r
  letI : FiniteDimensional ℂ Us :=
    classInvariantRestrictedFiniteDimensional s
  letI : FiniteDimensional ℂ V :=
    classInvariantRestrictedFiniteDimensional (r ⊓ s)
  letI : FiniteDimensional ℂ Q := Submodule.finiteDimensional_of_le hQV
  have hrpos : 0 < Module.finrank ℂ Ur := by
    rw [classInvariantRestricted_finrank]
    exact Fintype.card_pos_iff.mpr ((nonempty_quotient_iff r).mpr inferInstance)
  have hUpos : 0 < Module.finrank ℂ U := by
    have hle := Submodule.finrank_mono (show Ur ≤ U from le_sup_left)
    omega
  let q : Fin (Module.finrank ℂ Q) → A × B → ℂ :=
    finiteSubmoduleObservable Q
  have hfield :
      primeFiniteQuotientShiftField y r a ⊔
          primeFiniteQuotientShiftField y s a =
        primeObservableSubspaceShiftField y U a :=
    cofiniteTailDenseOn_primeFiniteQuotientField_sup_eq_interactionField
      y hy r s a
  have hQfield :
      primeObservableSubspaceShiftField y Q a =
        tailDenseObservableShiftField y q a :=
    primeObservableSubspaceShiftField_eq_basis y Q a
  refine ⟨q, hUQ, hsup, ?_, ?_, ?_, ?_⟩
  · calc
      Module.finrank ℂ Q = Module.finrank ℂ V - Module.finrank ℂ U :=
        complement_finrank_eq_sub U Q V hUQ hsup
      _ = finiteQuotientInteractionDefect r s := rfl
      _ = (Fintype.card A - 1) * (Fintype.card B - 1) :=
        productFiniteQuotientInteractionDefect_eq A B
      _ = (m.totient - 1) * (n.totient - 1) := by
        rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient]
  · exact ⟨finiteQuotientInteractionCohomologyEquivComplement
      r s Q hQV hUQ hsup⟩
  · have hDI := cofiniteTailDenseOn_complementObservable_differentialIndependent
      y hy U Q hUpos hUQ a
    rw [← hfield] at hDI
    exact hDI
  · calc
      (primeFiniteQuotientShiftField y r a ⊔
          primeFiniteQuotientShiftField y s a) ⊔
          tailDenseObservableShiftField y q a =
        primeObservableSubspaceShiftField y U a ⊔
          primeObservableSubspaceShiftField y Q a := by rw [hfield, hQfield]
      _ = primeObservableSubspaceShiftField y (U ⊔ Q) a :=
        (primeObservableSubspaceShiftField_sup y U Q a).symm
      _ = primeObservableSubspaceShiftField y V a := by rw [hsup]
      _ = primeFiniteQuotientShiftField y (r ⊓ s) a :=
        cofiniteTailDenseOn_primeObservableClassInvariantField_eq y hy (r ⊓ s) a

end

end GaloisForLFunctions.HTGeometry
