import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Divisible symbol counts and twisted orthogonality

The symbol-count and polarization arguments of Heng–Xie, Theorems 23 and 27
(arXiv:2611.13963), work for every nonidentity field endomorphism. A code
containing the constant word has divisible symbol counts whenever its weights
are divisible by the characteristic. Consequently every unary moment vanishes.
Polarization converts these diagonal identities into twisted orthogonality.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes

variable {K ι : Type*} [Field K] [Fintype ι]

/-- Number of nonzero coordinates. -/
def weight (c : ι → K) : ℕ := (Finset.univ.filter fun i => c i ≠ 0).card

/-- Number of occurrences of a specified symbol. -/
def symbolCount (c : ι → K) (a : K) : ℕ :=
  (Finset.univ.filter fun i => c i = a).card

/-- Divisibility of every word's Hamming weight. -/
def Divisible (p : ℕ) (C : Submodule K (ι → K)) : Prop :=
  ∀ c ∈ C, p ∣ weight c

/-- The coordinate pairing twisted by a field endomorphism. -/
def twistedPair (σ : K →+* K) (c d : ι → K) : K := ∑ i, c i * σ (d i)

/-- Every pair of words is orthogonal for the specified twist. -/
def SelfOrthogonal (σ : K →+* K) (C : Submodule K (ι → K)) : Prop :=
  ∀ c ∈ C, ∀ d ∈ C, twistedPair σ c d = 0

theorem weight_one : weight (fun _ : ι => (1 : K)) = Fintype.card ι := by
  simp [weight]

/-- Translating by a symbol partitions the coordinates into its fiber and its complement. -/
theorem symbolCount_add_weight_sub (c : ι → K) (a : K) :
    symbolCount c a + weight (fun i => c i - a) = Fintype.card ι := by
  simpa only [symbolCount, weight, sub_ne_zero, Finset.card_univ] using
    Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i => c i = a)

/-- Divisibility and the constant word force each symbol count to vanish in the field. -/
theorem symbolCount_cast_eq_zero (p : ℕ) [CharP K p]
    (C : Submodule K (ι → K)) (h1 : (fun _ => (1 : K)) ∈ C)
    (hC : Divisible p C) (c : ι → K) (hc : c ∈ C) (a : K) :
    (symbolCount c a : K) = 0 := by
  have hn : (Fintype.card ι : K) = 0 :=
    (CharP.cast_eq_zero_iff K p _).mpr (by simpa only [weight_one] using hC _ h1)
  have hd : (weight (fun i => c i - a) : K) = 0 :=
    (CharP.cast_eq_zero_iff K p _).mpr (hC _ (C.sub_mem hc (by
      simpa only [Pi.smul_def, smul_eq_mul, mul_one] using C.smul_mem a h1)))
  have h := congrArg (Nat.cast : ℕ → K) (symbolCount_add_weight_sub c a)
  rw [Nat.cast_add, hn, hd, add_zero] at h
  exact h

/-- Grouping coordinates by their symbol gives the full unary moment identity. -/
theorem sum_eq_sum_symbolCount [Fintype K] (c : ι → K) (f : K → K) :
    ∑ i, f (c i) = ∑ a : K, (symbolCount c a : K) * f a := by
  classical
  symm
  calc
    _ = ∑ a : K, ∑ i ∈ Finset.univ.filter (fun i => c i = a), f (c i) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [show (∑ i ∈ Finset.univ.filter (fun i => c i = a), f (c i)) =
          ∑ _i ∈ Finset.univ.filter (fun i => c i = a), f a from
        Finset.sum_congr rfl (fun i hi => congrArg f (Finset.mem_filter.mp hi).2)]
      simp only [Finset.sum_const, nsmul_eq_mul, symbolCount]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _

/-- Every unary observable has zero sum on a divisible word in a code containing one. -/
theorem sum_observable_eq_zero [Fintype K] (p : ℕ) [CharP K p]
    (C : Submodule K (ι → K)) (h1 : (fun _ => (1 : K)) ∈ C)
    (hC : Divisible p C) (c : ι → K) (hc : c ∈ C) (f : K → K) :
    ∑ i, f (c i) = 0 := by
  rw [sum_eq_sum_symbolCount]
  exact Finset.sum_eq_zero fun a _ => by
    rw [symbolCount_cast_eq_zero p C h1 hC c hc a, zero_mul]

/-- Expansion of the diagonal form separates its two mixed terms. -/
theorem twistedPair_add_smul (σ : K →+* K) (c d : ι → K) (a : K) :
    twistedPair σ (c + a • d) (c + a • d) =
      twistedPair σ c c + a * twistedPair σ d c +
      σ a * twistedPair σ c d + a * σ a * twistedPair σ d d := by
  simp only [twistedPair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A nonidentity twist recovers the entire pairing from its diagonal on a subspace. -/
theorem selfOrthogonal_of_diagonal (σ : K →+* K) (hσ : σ ≠ RingHom.id K)
    (C : Submodule K (ι → K))
    (hC : ∀ c ∈ C, twistedPair σ c c = 0) : SelfOrthogonal σ C := by
  have hex : ∃ a, σ a ≠ a := by
    by_contra! h
    exact hσ (RingHom.ext h)
  obtain ⟨a, ha⟩ := hex
  intro c hc d hd
  have hmix (b : K) :
      b * twistedPair σ d c + σ b * twistedPair σ c d = 0 := by
    have h := hC (c + b • d) (C.add_mem hc (C.smul_mem b hd))
    rw [twistedPair_add_smul, hC c hc, hC d hd, zero_add, mul_zero, add_zero] at h
    exact h
  have hone : twistedPair σ d c + twistedPair σ c d = 0 := by
    simpa only [map_one, one_mul] using hmix 1
  have hz : (σ a - a) * twistedPair σ c d = 0 := by
    linear_combination hmix a - a * hone
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

/-- Heng–Xie's Hermitian and Galois criteria for an arbitrary nonidentity twist. -/
theorem divisible_selfOrthogonal [Fintype K] (p : ℕ) [CharP K p]
    (σ : K →+* K) (hσ : σ ≠ RingHom.id K)
    (C : Submodule K (ι → K)) (h1 : (fun _ => (1 : K)) ∈ C)
    (hC : Divisible p C) : SelfOrthogonal σ C := by
  apply selfOrthogonal_of_diagonal σ hσ C
  intro c hc
  exact sum_observable_eq_zero p C h1 hC c hc (fun a => a * σ a)

#print axioms divisible_selfOrthogonal

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
