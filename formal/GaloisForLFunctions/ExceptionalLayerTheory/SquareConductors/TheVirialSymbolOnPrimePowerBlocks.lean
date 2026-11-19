import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePivotalBlockAtTheUnitaryMidpoint
import Mathlib.Data.Real.Basic

/-!
# Virial coercivity on the prime-power block cube

Kwak and Muñoz (arXiv:2611.23995, Lemma 6.2) identify a cubic Fourier
symbol whose continuum threshold occurs at squared frequency three.
A block flip has eigenvalue twice the Walsh rank. This lattice misses the
continuum zero. The half-divisor contrast also removes every even rank.
-/

open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
noncomputable section

/-- Cubic virial symbol at squared spatial frequency `x`. -/
def blockVirialSymbol (γ x : ℝ) : ℝ := (1+x) * (γ*x^2 + (3*γ-1)*x + 1)

private theorem symbol_shift (a b x : ℝ) :
    blockVirialSymbol b x = blockVirialSymbol a x + (b-a)*((1+x)*x*(x+3)) := by
  unfold blockVirialSymbol
  ring

private theorem symbol_mono {a b x : ℝ} (hab : a ≤ b) (hx : 0 ≤ x) :
    blockVirialSymbol a x ≤ blockVirialSymbol b x := by
  rw [symbol_shift a b x]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hab) (by positivity))

/-- The continuum virial form has the sharp threshold one ninth. -/
theorem blockVirial_continuum (γ : ℝ) :
    (∀ x : ℝ, 0 ≤ x → 0 ≤ blockVirialSymbol γ x) ↔ 1/9 ≤ γ := by
  constructor
  · intro h
    have ht := h 3 (by norm_num)
    unfold blockVirialSymbol at ht
    linarith only [ht]
  · intro h x hx
    apply le_trans _ (symbol_mono h hx)
    rw [show blockVirialSymbol (1/9) x = (1+x)*(x-3)^2/9 by unfold blockVirialSymbol; ring]
    positivity

/-- On all cube modes the sharp threshold is three twenty-eighths.
The only neutral rank at that coupling is two. -/
theorem blockVirial_cube_threshold (γ : ℝ) :
    (∀ j : ℕ, 0 ≤ blockVirialSymbol γ (2*j)) ↔ 3/28 ≤ γ := by
  constructor
  · intro h
    have ht := h 2
    norm_num [blockVirialSymbol] at ht
    linarith only [ht]
  · intro h j
    apply le_trans _ (symbol_mono h (by positivity))
    have he (x : ℝ) : blockVirialSymbol (3/28) x = (1+x)*(x-4)*(3*x-7)/28 := by
      unfold blockVirialSymbol
      ring
    rcases j with _ | j
    · norm_num [blockVirialSymbol]
    rcases j with _ | j
    · norm_num [blockVirialSymbol]
    rw [he]
    have hj : (2:ℝ)*((j+2 : ℕ):ℝ) ≥ 4 := by push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) j]
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith only [hj]))
      (by linarith only [hj])) (by norm_num)

/-- On odd Walsh ranks the threshold drops to one tenth, with equality
only in the one-block modes. -/
theorem blockVirial_odd_threshold (γ : ℝ) :
    (∀ j : ℕ, 0 ≤ blockVirialSymbol γ (2*(2*j+1))) ↔ 1/10 ≤ γ := by
  constructor
  · intro h
    have ht := h 0
    norm_num [blockVirialSymbol] at ht
    linarith only [ht]
  · intro h j
    apply le_trans _ (symbol_mono h (by positivity))
    cases j with
    | zero => norm_num [blockVirialSymbol]
    | succ j =>
      have he (x : ℝ) : blockVirialSymbol (1/10) x = (1+x)*(x-2)*(x-5)/10 := by
        unfold blockVirialSymbol
        ring
      rw [he]
      have hj : 6 ≤ (2:ℝ)*(2*((j+1:ℕ):ℝ)+1) := by push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) j]
      exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith only [hj]))
        (by linarith only [hj])) (by norm_num)

/-- Walsh character on subsets of the full prime-power blocks. -/
def blockCharacter (T S : Finset ℕ) : ℤ := ∏ p ∈ T, if p ∈ S then -1 else 1

/-- The unnormalized cube Laplacian adds or removes one prime-power block. -/
def blockFlipLaplacian (k : ℕ) (f : Finset ℕ → ℤ) (S : Finset ℕ) : ℤ :=
  ∑ p ∈ k.primeFactors, (f S - f (if p ∈ S then S.erase p else insert p S))

private theorem character_flip (T S : Finset ℕ) (p : ℕ) :
    blockCharacter T (if p ∈ S then S.erase p else insert p S) =
      (if p ∈ T then -1 else 1) * blockCharacter T S := by
  have h (q : ℕ) :
      (if q ∈ (if p ∈ S then S.erase p else insert p S) then (-1:ℤ) else 1) =
      (if q=p then -1 else 1) * (if q ∈ S then -1 else 1) := by
    by_cases hq : q=p <;> by_cases hp : p ∈ S <;> simp_all
  simp only [blockCharacter, h, prod_mul_distrib, prod_ite_eq']

/-- Each Walsh character is an eigenvector, with eigenvalue twice its rank. -/
theorem blockFlipLaplacian_character (k : ℕ) {T : Finset ℕ} (hT : T ⊆ k.primeFactors)
    (S : Finset ℕ) :
    blockFlipLaplacian k (blockCharacter T) S = 2*T.card*blockCharacter T S := by
  unfold blockFlipLaplacian
  simp_rw [character_flip]
  have term (p : ℕ) : blockCharacter T S - (if p ∈ T then -1 else 1)*blockCharacter T S =
      (if p ∈ T then 2*blockCharacter T S else 0) := by split_ifs <;> ring
  simp_rw [term]
  rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hT, sum_const, nsmul_eq_mul]
  ring

/-- Odd part of the square-root cut in the Walsh direction `T`.
Each small divisor is measured against its complementary divisor. -/
def unitaryWalshContrast (k : ℕ) (T : Finset ℕ) : ℤ :=
  ∑ S ∈ smallUnitarySubsets k, (blockCharacter T S - blockCharacter T (k.primeFactors \ S))

private theorem character_complement {k : ℕ} {T : Finset ℕ} (hT : T ⊆ k.primeFactors)
    (S : Finset ℕ) :
    blockCharacter T (k.primeFactors \ S) = (-1:ℤ)^T.card * blockCharacter T S := by
  unfold blockCharacter
  rw [← prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun p hp => ?_
  by_cases h : p ∈ S <;> simp [h, hT hp]

/-- Complementation removes every even interaction from the signed cut. -/
theorem unitaryWalshContrast_even {k : ℕ} {T : Finset ℕ}
    (hT : T ⊆ k.primeFactors) (he : Even T.card) : unitaryWalshContrast k T = 0 := by
  simp [unitaryWalshContrast, character_complement hT, he.neg_one_pow]

/-- The highest odd Walsh mode is twice the midpoint coefficient. -/
theorem unitaryWalshContrast_top {k : ℕ} (ho : Odd k.primeFactors.card) :
    unitaryWalshContrast k k.primeFactors = 2*unitaryHalfWeight k := by
  rw [unitaryWalshContrast, unitaryHalfWeight, mul_sum]
  refine sum_congr rfl fun S hS => ?_
  have hs := mem_powerset.mp (mem_filter.mp hS).1
  have hc : blockCharacter k.primeFactors S = (-1:ℤ)^S.card := by
    unfold blockCharacter
    rw [prod_ite, filter_mem_eq_inter, inter_eq_right.mpr hs]
    simp
  rw [character_complement (Subset.rfl), ho.neg_one_pow, hc]
  ring

#print axioms blockVirial_continuum
#print axioms blockVirial_cube_threshold
#print axioms blockVirial_odd_threshold
#print axioms blockFlipLaplacian_character
#print axioms unitaryWalshContrast_even
#print axioms unitaryWalshContrast_top

/-- The virial form of the half-divisor contrast, in unnormalized Walsh
coordinates on the finite cube. -/
def unitaryVirialEnergy (γ : ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ k.primeFactors.powerset,
    blockVirialSymbol γ (2*T.card) * (unitaryWalshContrast k T : ℝ)^2

private theorem contrast_term_nonneg {γ : ℝ} (hγ : 1/10 ≤ γ) {k : ℕ} {T : Finset ℕ}
    (hT : T ⊆ k.primeFactors) :
    0 ≤ blockVirialSymbol γ (2*T.card) * (unitaryWalshContrast k T : ℝ)^2 := by
  rcases Nat.even_or_odd T.card with he | ⟨j,hj⟩
  · simp [unitaryWalshContrast_even hT he]
  · have hn := (blockVirial_odd_threshold γ).mpr hγ j
    have hc : (T.card:ℝ) = 2*(j:ℝ)+1 := by exact_mod_cast hj
    rw [hc]
    exact mul_nonneg hn (sq_nonneg _)

private theorem prime_virial {p : ℕ} (hp : p.Prime) (γ : ℝ) :
    unitaryVirialEnergy γ p = 4*blockVirialSymbol γ 2 := by
  have ho : Odd p.primeFactors.card := by simp [hp.primeFactors]
  have ht := unitaryWalshContrast_top ho
  rw [unitary_half_weight_singleton hp.one_lt hp.primeFactors, hp.primeFactors] at ht
  have hz : unitaryWalshContrast p ∅ = 0 :=
    unitaryWalshContrast_even (empty_subset _) (by simp)
  rw [unitaryVirialEnergy, hp.primeFactors]
  rw [show ({p} : Finset ℕ) = insert p ∅ from rfl, sum_powerset_insert (notMem_empty _)]
  simp [ht, hz]
  ring

/-- One tenth is necessary and sufficient for every arithmetic half-divisor
contrast to have nonnegative virial energy. Every prime tests necessity. -/
theorem unitaryVirialEnergy_nonneg_iff (γ : ℝ) :
    (∀ k : ℕ, 0 ≤ unitaryVirialEnergy γ k) ↔ 1/10 ≤ γ := by
  constructor
  · intro h
    have ht := h 2
    rw [prime_virial Nat.prime_two] at ht
    unfold blockVirialSymbol at ht
    linarith only [ht]
  · intro h k
    exact sum_nonneg fun T hT => contrast_term_nonneg h (mem_powerset.mp hT)

private theorem virial_high_rank {j : ℕ} (hj : 3 ≤ j) :
    14/5 ≤ blockVirialSymbol (1/10) (2*j) := by
  have h : (6:ℝ) ≤ 2*j := by exact_mod_cast (show 6 ≤ 2*j by omega)
  have a : 7 ≤ 1+2*(j:ℝ) := by linarith only [h]
  have b : 4 ≤ 2*(j:ℝ)-2 := by linarith only [h]
  have c : 1 ≤ 2*(j:ℝ)-5 := by linarith only [h]
  have hprod := mul_le_mul (mul_le_mul a b (by norm_num) (by positivity)) c
    (by norm_num) (mul_nonneg (by positivity) (by linarith only [b]))
  unfold blockVirialSymbol
  linarith only [hprod]

/-- The third rank sets the sharp uniform cost of the squared rank excess
on all ranks at least three. -/
theorem blockVirial_rank_excess {j : ℕ} (hj : 3 ≤ j) :
    7/10*((j:ℝ)-1)^2 ≤ blockVirialSymbol (1/10) (2*j) := by
  have h : (3:ℝ) ≤ j := by exact_mod_cast hj
  have factor : blockVirialSymbol (1/10) (2*j) - 7/10*((j:ℝ)-1)^2 =
      ((j:ℝ)-3)*((j:ℝ)-1)*(8*(j:ℝ)+1)/10 := by
    unfold blockVirialSymbol
    ring
  exact sub_nonneg.mp (factor ▸ div_nonneg
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr h) (by linarith only [h])) (by positivity))
    (by norm_num))

/-- At the sharp coupling every odd rank of at least three pays for the
square of the actual midpoint coefficient. The constant is the third-rank
symbol multiplied by the square of the complement factor two. -/
theorem unitaryVirialEnergy_pays_midpoint {k : ℕ} (ho : Odd k.primeFactors.card)
    (hk : 3 ≤ k.primeFactors.card) :
    56/5*(unitaryHalfWeight k : ℝ)^2 ≤ unitaryVirialEnergy (1/10) k := by
  have ht := single_le_sum (s := k.primeFactors.powerset)
    (f := fun T : Finset ℕ => blockVirialSymbol (1/10) (2*T.card) * (unitaryWalshContrast k T : ℝ)^2)
    (fun T hT => contrast_term_nonneg le_rfl (mem_powerset.mp hT)) (mem_powerset.mpr Subset.rfl)
  apply le_trans _ ht
  rw [unitaryWalshContrast_top ho, Int.cast_mul, Int.cast_ofNat]
  have h := mul_le_mul_of_nonneg_right (virial_high_rank hk) (sq_nonneg (2*(unitaryHalfWeight k:ℝ)))
  linarith only [h]

#print axioms unitaryVirialEnergy_nonneg_iff
#print axioms unitaryVirialEnergy_pays_midpoint
#print axioms blockVirial_rank_excess
end
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
