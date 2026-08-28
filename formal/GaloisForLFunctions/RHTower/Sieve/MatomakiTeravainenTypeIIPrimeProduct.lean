import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMinimalGeometricSchedule
import GaloisForLFunctions.HTGeometry.ArithmeticFunctionDeterminantCoefficient

/-!
# Exact equation-(2.11) coefficient of a finite prime-block product

This identifies a finite Dirichlet-convolution product of block indicators with Proposition 2.2's
literal ordered-tuple coefficient.  Finite block indices are enumerated by `Fin q`; the proposition
uses the canonically matching natural index set `range q`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction GaloisForLFunctions

noncomputable section

/-- Extend a `Fin q`-indexed block family by the empty set outside `range q`. -/
def mtFinBlockToNat {q : ℕ} (block : Fin q → Finset ℕ) (i : ℕ) : Finset ℕ :=
  if hi : i < q then block ⟨i, hi⟩ else ∅

@[simp] theorem mtFinBlockToNat_apply {q : ℕ} (block : Fin q → Finset ℕ) (i : Fin q) :
    mtFinBlockToNat block i.1 = block i := by
  simp [mtFinBlockToNat, i.2]

/-- Canonical equivalence between the subtype of `range q` and `Fin q`. -/
def mtRangeEquivFin (q : ℕ) : {i : ℕ // i ∈ Finset.range q} ≃ Fin q where
  toFun i := ⟨i.1, Finset.mem_range.mp i.2⟩
  invFun i := ⟨i.1, Finset.mem_range.mpr i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem mtFinBlockToNat_apply_range {q : ℕ}
    (block : Fin q → Finset ℕ) (i : {i : ℕ // i ∈ Finset.range q}) :
    mtFinBlockToNat block i.1 = block (mtRangeEquivFin q i) := by
  simp [mtFinBlockToNat, mtRangeEquivFin, Finset.mem_range.mp i.2]

private def mtValidBlockFactorData {q n : ℕ} (block : Fin q → Finset ℕ) :=
  {d : DirichletFactorData q n // ∀ i, d.factors i ∈ block i}

private noncomputable instance mtValidBlockFactorDataFintype
    {q n : ℕ} (block : Fin q → Finset ℕ) :
    Fintype (mtValidBlockFactorData (n := n) block) :=
  Fintype.ofInjective (fun d : mtValidBlockFactorData (n := n) block => d.1)
    Subtype.val_injective

private theorem mtValidBlockFactorData_fintypeCard_eq_typeIITuples_card
    {q n : ℕ} (block : Fin q → Finset ℕ)
    (hpos : ∀ i, ∀ m ∈ block i, 0 < m) (hn : 0 < n) :
    Fintype.card (mtValidBlockFactorData (n := n) block) =
      (mtTypeIIPrimeTuples (Finset.range q) (mtFinBlockToNat block) n).card := by
  classical
  let e := mtRangeEquivFin q
  let toTuple : mtValidBlockFactorData (n := n) block →
      {v // v ∈ mtTypeIIPrimeTuples (Finset.range q) (mtFinBlockToNat block) n} :=
    fun d => ⟨fun i => d.1.factors (e i), by
      rw [mem_mtTypeIIPrimeTuples]
      constructor
      · intro i
        have hi := d.2 (e i)
        simpa only [e, mtFinBlockToNat_apply_range] using hi
      · calc
          ∏ i, d.1.factors (e i) = ∏ j, d.1.factors j := e.prod_comp d.1.factors
          _ = n := d.1.prod_factors⟩
  have htoInjective : Function.Injective toTuple := by
    intro d r hdr
    apply Subtype.ext
    apply DirichletFactorData.factors_injective hn
    funext i
    have hpoint := congrFun (congrArg Subtype.val hdr) (e.symm i)
    simpa [toTuple] using hpoint
  have htoSurjective : Function.Surjective toTuple := by
    intro v
    let factors : Fin q → ℕ := fun i => v.1 (e.symm i)
    have hv := mem_mtTypeIIPrimeTuples.mp v.2
    have hfactorPos : ∀ i, 0 < factors i := by
      intro i
      apply hpos i
      have hi := hv.1 (e.symm i)
      have hi' : v.1 (e.symm i) ∈ block (e (e.symm i)) := by
        simpa only [e, mtFinBlockToNat_apply_range] using hi
      rw [e.apply_symm_apply] at hi'
      exact hi'
    have hfactorProd : (∏ i, factors i) = n := by
      calc
        ∏ i, factors i = ∏ k, v.1 k := e.symm.prod_comp v.1
        _ = n := hv.2
    obtain ⟨d, hd⟩ :=
      exists_dirichletFactorData_factors_eq factors hfactorPos hfactorProd
    have hdValid : ∀ i, d.factors i ∈ block i := by
      intro i
      rw [congrFun hd i]
      have hi := hv.1 (e.symm i)
      have hi' : v.1 (e.symm i) ∈ block (e (e.symm i)) := by
        simpa only [e, mtFinBlockToNat_apply_range] using hi
      rw [e.apply_symm_apply] at hi'
      exact hi'
    refine ⟨⟨d, hdValid⟩, ?_⟩
    apply Subtype.ext
    funext i
    change d.factors (e i) = v.1 i
    rw [congrFun hd (e i)]
    simp [factors]
  let equiv : mtValidBlockFactorData (n := n) block ≃
      {v // v ∈ mtTypeIIPrimeTuples (Finset.range q) (mtFinBlockToNat block) n} :=
    Equiv.ofBijective toTuple ⟨htoInjective, htoSurjective⟩
  calc
    Fintype.card (mtValidBlockFactorData (n := n) block) =
        Fintype.card
          {v // v ∈ mtTypeIIPrimeTuples (Finset.range q) (mtFinBlockToNat block) n} :=
      Fintype.card_congr equiv
    _ = (mtTypeIIPrimeTuples (Finset.range q) (mtFinBlockToNat block) n).card := by
      simp

/-- A finite block-indicator product is exactly the literal equation-(2.11) coefficient. -/
theorem fin_prod_mtPrimeBlockAF_apply_eq_typeIIPrimeCoefficient
    {q n : ℕ} (block : Fin q → Finset ℕ)
    (hpos : ∀ i, ∀ m ∈ block i, 0 < m) (hn : 0 < n) :
    (∏ i, mtPrimeBlockAF (block i)) n =
      mtTypeIIPrimeCoefficient (Finset.range q) (mtFinBlockToNat block) n := by
  classical
  rw [arithmeticFunction_fin_prod_apply]
  calc
    (∑ d : DirichletFactorData q n,
        ∏ i, mtPrimeBlockAF (block i) (d.factors i)) =
        ∑ d : DirichletFactorData q n,
          if (∀ i, d.factors i ∈ block i) then (1 : ℂ) else 0 := by
      apply Fintype.sum_congr
      intro d
      have hfactorPos : ∀ i, 0 < d.factors i := d.factor_pos hn
      by_cases hd : ∀ i, d.factors i ∈ block i
      · rw [if_pos hd]
        apply Finset.prod_eq_one
        intro i hi
        rw [mtPrimeBlockAF_apply_of_pos _ (hfactorPos i)]
        simp [hd i]
      · rw [if_neg hd]
        push Not at hd
        obtain ⟨i, hi⟩ := hd
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        rw [mtPrimeBlockAF_apply_of_pos _ (hfactorPos i)]
        simp [hi]
    _ = (Fintype.card (mtValidBlockFactorData (n := n) block) : ℂ) := by
      have hcard :
          (Finset.univ.filter fun d : DirichletFactorData q n =>
            ∀ i, d.factors i ∈ block i).card =
            Fintype.card (mtValidBlockFactorData (n := n) block) := by
        calc
          (Finset.univ.filter fun d : DirichletFactorData q n =>
              ∀ i, d.factors i ∈ block i).card =
              Fintype.card
                {d : DirichletFactorData q n // ∀ i, d.factors i ∈ block i} :=
            (Fintype.card_ofFinset
              (p := {d : DirichletFactorData q n | ∀ i, d.factors i ∈ block i})
              (Finset.univ.filter fun d : DirichletFactorData q n =>
                ∀ i, d.factors i ∈ block i) (by simp)).symm
          _ = Fintype.card (mtValidBlockFactorData (n := n) block) :=
            Fintype.card_congr (Equiv.refl _)
      calc
        (∑ d : DirichletFactorData q n,
            if (∀ i, d.factors i ∈ block i) then (1 : ℂ) else 0) =
            ((Finset.univ.filter fun d : DirichletFactorData q n =>
              ∀ i, d.factors i ∈ block i).card : ℂ) := by simp
        _ = (Fintype.card (mtValidBlockFactorData (n := n) block) : ℂ) := by
          exact_mod_cast hcard
    _ = ((mtTypeIIPrimeTuples (Finset.range q) (mtFinBlockToNat block) n).card : ℂ) := by
      rw [mtValidBlockFactorData_fintypeCard_eq_typeIITuples_card block hpos hn]
    _ = mtTypeIIPrimeCoefficient (Finset.range q) (mtFinBlockToNat block) n := by
      simp [mtTypeIIPrimeCoefficient]

/-- Arithmetic-function form of the exact finite block-product identity. -/
theorem fin_prod_mtPrimeBlockAF_eq_typeIIPrimeCoefficientAF
    {q : ℕ} (block : Fin q → Finset ℕ)
    (hpos : ∀ i, ∀ m ∈ block i, 0 < m) :
    (∏ i, mtPrimeBlockAF (block i)) =
      mtCoefficientAF
        (mtTypeIIPrimeCoefficient (Finset.range q) (mtFinBlockToNat block)) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [mtCoefficientAF]
  · rw [mtCoefficientAF_apply_of_pos _ (Nat.pos_of_ne_zero hn)]
    exact fin_prod_mtPrimeBlockAF_apply_eq_typeIIPrimeCoefficient
      block hpos (Nat.pos_of_ne_zero hn)

end

end RHTower.Sieve
