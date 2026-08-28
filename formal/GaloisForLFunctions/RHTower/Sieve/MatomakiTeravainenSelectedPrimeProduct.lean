import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIPrimeProduct

/-!
# Enumeration of selected Type-II block subsets

Proposition 2.2 indexes its selected blocks by natural numbers.  Active Buchstab chains use
`Fin t`.  Canonical increasing enumeration transports every selected finite subset between those
two presentations without changing its block convolution or scale product.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Increasing enumeration of a finite set. -/
def mtFinsetEnumeration {α : Type*} [LinearOrder α] (S : Finset α) : Fin S.card → α :=
  fun i => ((S.orderIsoOfFin rfl) i).1

theorem mtFinsetEnumeration_mem {α : Type*} [LinearOrder α]
    (S : Finset α) (i : Fin S.card) :
    mtFinsetEnumeration S i ∈ S :=
  ((S.orderIsoOfFin rfl) i).2

theorem mtFinsetEnumeration_injective {α : Type*} [LinearOrder α]
    (S : Finset α) : Function.Injective (mtFinsetEnumeration S) := by
  intro i j hij
  apply (S.orderIsoOfFin rfl).injective
  exact Subtype.ext hij

/-- A selected block family, reindexed by its increasing enumeration. -/
def mtEnumeratedBlock {α : Type*} [LinearOrder α]
    (block : α → Finset ℕ) (S : Finset α) : Fin S.card → Finset ℕ :=
  fun i => block (mtFinsetEnumeration S i)

/-- A selected real scale family, reindexed by the same enumeration. -/
def mtEnumeratedScale {α : Type*} [LinearOrder α]
    (Q : α → ℝ) (S : Finset α) : Fin S.card → ℝ :=
  fun i => Q (mtFinsetEnumeration S i)

theorem fin_prod_mtEnumeratedBlock_eq_finset_prod
    {α : Type*} [LinearOrder α]
    (block : α → Finset ℕ) (S : Finset α) :
    (∏ i : Fin S.card, mtPrimeBlockAF (mtEnumeratedBlock block S i)) =
      ∏ i ∈ S, mtPrimeBlockAF (block i) := by
  let e : Fin S.card ≃ S := (S.orderIsoOfFin rfl).toEquiv
  calc
    (∏ i : Fin S.card, mtPrimeBlockAF (mtEnumeratedBlock block S i)) =
        ∏ i : S, mtPrimeBlockAF (block i.1) := by
      simpa [mtEnumeratedBlock, mtFinsetEnumeration, e] using
        e.prod_comp (fun i : S => mtPrimeBlockAF (block i.1))
    _ = ∏ i ∈ S, mtPrimeBlockAF (block i) := by
      simpa using (Finset.prod_attach S (fun i => mtPrimeBlockAF (block i)))

theorem fin_prod_mtEnumeratedScale_eq_finset_prod
    {α : Type*} [LinearOrder α] (Q : α → ℝ) (S : Finset α) :
    (∏ i : Fin S.card, mtEnumeratedScale Q S i) = ∏ i ∈ S, Q i := by
  let e : Fin S.card ≃ S := (S.orderIsoOfFin rfl).toEquiv
  calc
    (∏ i : Fin S.card, mtEnumeratedScale Q S i) = ∏ i : S, Q i.1 := by
      simpa [mtEnumeratedScale, mtFinsetEnumeration, e] using
        e.prod_comp (fun i : S => Q i.1)
    _ = ∏ i ∈ S, Q i := by
      simpa using (Finset.prod_attach S Q)

/-- Any selected finite block product has Proposition 2.2's literal coefficient presentation. -/
theorem mtPrimeBlockFamilyAF_eq_enumeratedTypeIIPrimeCoefficientAF
    {t : ℕ} (block : Fin t → Finset ℕ) (S : Finset (Fin t))
    (hpos : ∀ i ∈ S, ∀ m ∈ block i, 0 < m) :
    mtPrimeBlockFamilyAF block S =
      mtCoefficientAF
        (mtTypeIIPrimeCoefficient (Finset.range S.card)
          (mtFinBlockToNat (mtEnumeratedBlock block S))) := by
  rw [mtPrimeBlockFamilyAF, ← fin_prod_mtEnumeratedBlock_eq_finset_prod block S]
  exact fin_prod_mtPrimeBlockAF_eq_typeIIPrimeCoefficientAF
    (mtEnumeratedBlock block S) (by
      intro i m hm
      exact hpos (mtFinsetEnumeration S i) (mtFinsetEnumeration_mem S i) m hm)

/-- Extend an enumerated real scale by zero outside its proposition index set. -/
def mtEnumeratedScaleToNat {α : Type*} [LinearOrder α]
    (Q : α → ℝ) (S : Finset α) (i : ℕ) : ℝ :=
  if hi : i < S.card then mtEnumeratedScale Q S ⟨i, hi⟩ else 0

@[simp] theorem mtEnumeratedScaleToNat_apply
    {α : Type*} [LinearOrder α]
    (Q : α → ℝ) (S : Finset α) (i : Fin S.card) :
    mtEnumeratedScaleToNat Q S i.1 = mtEnumeratedScale Q S i := by
  simp [mtEnumeratedScaleToNat, i.2]

@[simp] theorem mtEnumeratedScaleToNat_apply_range
    {α : Type*} [LinearOrder α]
    (Q : α → ℝ) (S : Finset α)
    (i : (Finset.range S.card : Finset ℕ)) :
    mtEnumeratedScaleToNat Q S i.1 =
      mtEnumeratedScale Q S (mtRangeEquivFin S.card i) := by
  simp [mtEnumeratedScaleToNat, mtRangeEquivFin, Finset.mem_range.mp i.2]

theorem prod_rangeSubtype_mtEnumeratedScaleToNat
    {α : Type*} [LinearOrder α] (Q : α → ℝ) (S : Finset α) :
    (∏ i : (Finset.range S.card : Finset ℕ), mtEnumeratedScaleToNat Q S i.1) =
      ∏ i ∈ S, Q i := by
  let e := mtRangeEquivFin S.card
  calc
    (∏ i : (Finset.range S.card : Finset ℕ), mtEnumeratedScaleToNat Q S i.1) =
        ∏ i : Fin S.card, mtEnumeratedScale Q S i := by
      simpa only [e, mtEnumeratedScaleToNat_apply_range] using
        e.prod_comp (mtEnumeratedScale Q S)
    _ = ∏ i ∈ S, Q i := fin_prod_mtEnumeratedScale_eq_finset_prod Q S

end

end RHTower.Sieve
