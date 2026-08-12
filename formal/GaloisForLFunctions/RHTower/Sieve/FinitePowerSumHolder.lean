import GaloisForLFunctions.RHTower.Sieve.FinitePowerSumFourier
import GaloisForLFunctions.RHTower.Sieve.FiniteFiberCorrelation

namespace RHTower.Sieve

open scoped BigOperators ComplexConjugate

noncomputable section

def finiteLeadTailSignature {L A : Type*}
    (q k b : ℕ) [NeZero q]
    (lead : L → Fin k → ZMod q) (atom : A → Fin k → ZMod q) :
    L × (Fin b → A) → Fin k → ZMod q :=
  fun z => lead z.1 + ∑ i : Fin b, atom (z.2 i)

theorem finiteProductCharacter_sum (q k b : ℕ) [NeZero q]
    (ξ : Fin k → ZMod q) (atom : Fin b → Fin k → ZMod q) :
    finiteProductCharacter q k ξ (∑ i : Fin b, atom i) =
      ∏ i : Fin b, finiteProductCharacter q k ξ (atom i) := by
  induction b with
  | zero => simp [finiteProductCharacter]
  | succ b ih =>
      rw [Fin.sum_univ_succ, finiteProductCharacter_add, ih]
      rw [Fin.prod_univ_succ]

theorem finiteCharacterSum_leadTail_factor
    {L A : Type*} [Fintype L] [Fintype A]
    (q k b : ℕ) [NeZero q]
    (lead : L → Fin k → ZMod q) (atom : A → Fin k → ZMod q)
    (ξ : Fin k → ZMod q) :
    finiteCharacterSum q k (finiteLeadTailSignature q k b lead atom) ξ =
      finiteCharacterSum q k lead ξ *
        finiteCharacterSum q k atom ξ ^ b := by
  unfold finiteCharacterSum finiteLeadTailSignature
  rw [Fintype.sum_prod_type]
  simp_rw [finiteProductCharacter_add, finiteProductCharacter_sum]
  rw [← Finset.sum_mul_sum]
  congr 1
  rw [Fintype.sum_pow]

theorem sum_normSq_finiteCharacterSum_eq_finiteFiberEnergy
    {α : Type*} [Fintype α] (q k : ℕ) [NeZero q]
    (f : α → Fin k → ZMod q) :
    (∑ ξ : Fin k → ZMod q, ‖finiteCharacterSum q k f ξ‖ ^ 2) =
      (q ^ k : ℝ) * finiteFiberEnergy f := by
  apply Complex.ofReal_injective
  rw [sum_normSq_finiteCharacterSum_eq_energy]
  push_cast
  rw [finiteFiberEnergy_eq_card]

def finiteClassCharacterSum {A ι : Type*}
    [Fintype A] [Fintype ι] [DecidableEq ι]
    (q k : ℕ) [NeZero q] (atom : A → Fin k → ZMod q)
    (c : A → ι) (i : ι) (ξ : Fin k → ZMod q) : ℂ :=
  ∑ a : {a : A // c a = i}, finiteProductCharacter q k ξ (atom a.1)

theorem finiteCharacterSum_eq_sum_classes
    {A ι : Type*} [Fintype A] [Fintype ι] [DecidableEq ι]
    (q k : ℕ) [NeZero q] (atom : A → Fin k → ZMod q)
    (c : A → ι) (ξ : Fin k → ZMod q) :
    finiteCharacterSum q k atom ξ =
      ∑ i : ι, finiteClassCharacterSum q k atom c i ξ := by
  unfold finiteCharacterSum finiteClassCharacterSum
  exact (Fintype.sum_fiberwise c
    (fun a => finiteProductCharacter q k ξ (atom a))).symm

theorem norm_finiteCharacterSum_pow_le_classes
    {A ι : Type*} [Fintype A] [Fintype ι] [DecidableEq ι]
    (q k b : ℕ) [NeZero q] (hb : b ≠ 0)
    (atom : A → Fin k → ZMod q) (c : A → ι)
    (ξ : Fin k → ZMod q) :
    ‖finiteCharacterSum q k atom ξ‖ ^ (2 * b) ≤
      (Fintype.card ι : ℝ) ^ (2 * b - 1) *
        ∑ i : ι, ‖finiteClassCharacterSum q k atom c i ξ‖ ^ (2 * b) := by
  rw [finiteCharacterSum_eq_sum_classes (ι := ι) q k atom c ξ]
  calc
    ‖∑ i : ι, finiteClassCharacterSum q k atom c i ξ‖ ^ (2 * b) ≤
        (∑ i : ι, ‖finiteClassCharacterSum q k atom c i ξ‖) ^ (2 * b) :=
      pow_le_pow_left₀ (norm_nonneg _) (by
        simpa using norm_sum_le Finset.univ
          (fun i : ι => finiteClassCharacterSum q k atom c i ξ)) _
    _ ≤ (Fintype.card ι : ℝ) ^ (2 * b - 1) *
        ∑ i : ι, ‖finiteClassCharacterSum q k atom c i ξ‖ ^ (2 * b) := by
      have h := pow_sum_le_card_mul_sum_pow
        (s := Finset.univ)
        (f := fun i : ι => ‖finiteClassCharacterSum q k atom c i ξ‖)
        (fun _ _ => norm_nonneg _) (2 * b - 1)
      have hexp : 2 * b - 1 + 1 = 2 * b := by omega
      simpa only [Finset.card_univ, hexp] using h

theorem normSq_finiteCharacterSum_leadTail_le_classes
    {L A ι : Type*} [Fintype L] [Fintype A] [Fintype ι]
    [DecidableEq ι]
    (q k b : ℕ) [NeZero q] (hb : b ≠ 0)
    (lead : L → Fin k → ZMod q) (atom : A → Fin k → ZMod q)
    (c : A → ι) (ξ : Fin k → ZMod q) :
    ‖finiteCharacterSum q k
        (finiteLeadTailSignature q k b lead atom) ξ‖ ^ 2 ≤
      (Fintype.card ι : ℝ) ^ (2 * b - 1) *
        ∑ i : ι, ‖finiteCharacterSum q k
          (finiteLeadTailSignature q k b lead
            (fun a : {a : A // c a = i} => atom a.1)) ξ‖ ^ 2 := by
  let Lead := finiteCharacterSum q k lead ξ
  let Atom := finiteCharacterSum q k atom ξ
  let Class : ι → ℂ := fun i => finiteClassCharacterSum q k atom c i ξ
  have htotal := finiteCharacterSum_leadTail_factor q k b lead atom ξ
  have hclass : ∀ i : ι,
      finiteCharacterSum q k
        (finiteLeadTailSignature q k b lead
          (fun a : {a : A // c a = i} => atom a.1)) ξ =
        Lead * Class i ^ b := by
    intro i
    rw [finiteCharacterSum_leadTail_factor]
    rfl
  rw [htotal]
  simp_rw [hclass]
  simp only [norm_mul, norm_pow]
  have hatom := norm_finiteCharacterSum_pow_le_classes
    (ι := ι) q k b hb atom c ξ
  calc
    (‖Lead‖ * ‖Atom‖ ^ b) ^ 2 =
        ‖Lead‖ ^ 2 * ‖Atom‖ ^ (2 * b) := by
      simp [mul_pow, pow_mul, mul_comm]
    _ ≤ ‖Lead‖ ^ 2 * ((Fintype.card ι : ℝ) ^ (2 * b - 1) *
        ∑ i : ι, ‖Class i‖ ^ (2 * b)) :=
      mul_le_mul_of_nonneg_left hatom (sq_nonneg _)
    _ = (Fintype.card ι : ℝ) ^ (2 * b - 1) *
        ∑ i : ι, (‖Lead‖ * ‖Class i‖ ^ b) ^ 2 := by
      simp_rw [Finset.mul_sum, mul_pow, pow_mul]
      ring_nf

theorem finiteFiberEnergy_le_residueClasses
    {L A ι : Type*} [Fintype L] [Fintype A] [Fintype ι]
    [DecidableEq ι]
    (q k b : ℕ) [NeZero q] (hb : b ≠ 0)
    (lead : L → Fin k → ZMod q) (atom : A → Fin k → ZMod q)
    (c : A → ι) :
    finiteFiberEnergy (finiteLeadTailSignature q k b lead atom) ≤
      Fintype.card ι ^ (2 * b - 1) *
        ∑ i : ι, finiteFiberEnergy
          (finiteLeadTailSignature q k b lead
            (fun a : {a : A // c a = i} => atom a.1)) := by
  have hfourier :
      (∑ ξ : Fin k → ZMod q,
        ‖finiteCharacterSum q k
          (finiteLeadTailSignature q k b lead atom) ξ‖ ^ 2) ≤
      (Fintype.card ι : ℝ) ^ (2 * b - 1) *
        ∑ i : ι, ∑ ξ : Fin k → ZMod q,
          ‖finiteCharacterSum q k
            (finiteLeadTailSignature q k b lead
              (fun a : {a : A // c a = i} => atom a.1)) ξ‖ ^ 2 := by
    calc
      (∑ ξ : Fin k → ZMod q,
          ‖finiteCharacterSum q k
            (finiteLeadTailSignature q k b lead atom) ξ‖ ^ 2) ≤
          ∑ ξ : Fin k → ZMod q,
            (Fintype.card ι : ℝ) ^ (2 * b - 1) *
              ∑ i : ι, ‖finiteCharacterSum q k
                (finiteLeadTailSignature q k b lead
                  (fun a : {a : A // c a = i} => atom a.1)) ξ‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro ξ _
        exact normSq_finiteCharacterSum_leadTail_le_classes
          q k b hb lead atom c ξ
      _ = (Fintype.card ι : ℝ) ^ (2 * b - 1) *
          ∑ i : ι, ∑ ξ : Fin k → ZMod q,
            ‖finiteCharacterSum q k
              (finiteLeadTailSignature q k b lead
                (fun a : {a : A // c a = i} => atom a.1)) ξ‖ ^ 2 := by
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_comm]
  simp_rw [sum_normSq_finiteCharacterSum_eq_finiteFiberEnergy] at hfourier
  have hqpos : (0 : ℝ) < q ^ k := by
    exact_mod_cast pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) k
  have hcancel :
      (finiteFiberEnergy (finiteLeadTailSignature q k b lead atom) : ℝ) ≤
        (Fintype.card ι : ℝ) ^ (2 * b - 1) *
          ∑ i : ι, finiteFiberEnergy
            (finiteLeadTailSignature q k b lead
              (fun a : {a : A // c a = i} => atom a.1)) := by
    apply le_of_mul_le_mul_left ?_ hqpos
    calc
      (q ^ k : ℝ) *
          finiteFiberEnergy (finiteLeadTailSignature q k b lead atom) ≤
          (Fintype.card ι : ℝ) ^ (2 * b - 1) *
            ∑ i : ι, (q ^ k : ℝ) * finiteFiberEnergy
              (finiteLeadTailSignature q k b lead
                (fun a : {a : A // c a = i} => atom a.1)) := hfourier
      _ = (q ^ k : ℝ) * ((Fintype.card ι : ℝ) ^ (2 * b - 1) *
          ∑ i : ι, finiteFiberEnergy
            (finiteLeadTailSignature q k b lead
              (fun a : {a : A // c a = i} => atom a.1))) := by
        push_cast
        simp_rw [Finset.mul_sum]
        ring_nf
  exact_mod_cast hcancel

end

end RHTower.Sieve

