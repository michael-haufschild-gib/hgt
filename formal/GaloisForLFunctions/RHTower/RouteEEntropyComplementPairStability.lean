import GaloisForLFunctions.RHTower.RouteEEntropyComplementBreadthMixture
import GaloisForLFunctions.RHTower.MobiusParityCoalescedProductLaws

/-!
# Entropy-complement endpoint pair-stability and seam localization

The low/rough factorization used by the live entropy-complement Route E relation is intrinsic to
each squarefree endpoint. This module proves that on the friable sector, a symmetric physical
shell and freshness condition make adjacent-grade upward and downward certificates exact endpoint
reversals. It then proves the sharp boundary for a target-friable seam relation: reverse
certification fails exactly when the original source is nonfriable.

No short-interval token count, load estimate, Möbius cancellation, or RH premise is assumed.
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset ArithmeticFunction

namespace RHTower

noncomputable section

/-! ## Intrinsic low/rough factorization -/

/-- Prime factors at or below the source-predeclared entropy-complement cutoff. -/
def routeELowPrimeFactors (P n : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p => p ≤ P

/-- Prime factors strictly above the source-predeclared entropy-complement cutoff. -/
def routeERoughPrimeFactors (P n : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p => P < p

/-- Intrinsic low-prime part of a squarefree endpoint. -/
def routeELowPart (P n : ℕ) : ℕ :=
  ∏ p ∈ routeELowPrimeFactors P n, p

/-- Intrinsic rough-prime part of a squarefree endpoint. -/
def routeERoughPart (P n : ℕ) : ℕ :=
  ∏ p ∈ routeERoughPrimeFactors P n, p

/-- Low and rough supports partition the complete prime support. -/
theorem routeE_lowPrimeFactors_union_roughPrimeFactors (P n : ℕ) :
    routeELowPrimeFactors P n ∪ routeERoughPrimeFactors P n = n.primeFactors := by
  ext p
  simp only [routeELowPrimeFactors, routeERoughPrimeFactors, mem_union, mem_filter]
  constructor
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  · intro hp
    by_cases hle : p ≤ P
    · exact Or.inl ⟨hp, hle⟩
    · exact Or.inr ⟨hp, Nat.lt_of_not_ge hle⟩

/-- Low and rough supports are disjoint. -/
theorem routeE_lowPrimeFactors_disjoint_roughPrimeFactors (P n : ℕ) :
    Disjoint (routeELowPrimeFactors P n) (routeERoughPrimeFactors P n) := by
  rw [Finset.disjoint_left]
  intro p hpLow hpRough
  rw [routeELowPrimeFactors, Finset.mem_filter] at hpLow
  rw [routeERoughPrimeFactors, Finset.mem_filter] at hpRough
  omega

/-- Every squarefree endpoint is exactly the product of its intrinsic low and rough parts. -/
theorem routeE_lowPart_mul_roughPart_eq_of_squarefree
    (P : ℕ) {n : ℕ} (hn : Squarefree n) :
    routeELowPart P n * routeERoughPart P n = n := by
  rw [routeELowPart, routeERoughPart,
    ← Finset.prod_union (routeE_lowPrimeFactors_disjoint_roughPrimeFactors P n),
    routeE_lowPrimeFactors_union_roughPrimeFactors, Nat.prod_primeFactors_of_squarefree hn]

/-- Intrinsic low and rough breadths add to the endpoint's distinct-prime breadth. -/
theorem routeE_lowBreadth_add_roughBreadth_eq (P n : ℕ) :
    (routeELowPrimeFactors P n).card + (routeERoughPrimeFactors P n).card =
      n.primeFactors.card := by
  rw [← Finset.card_union_of_disjoint
    (routeE_lowPrimeFactors_disjoint_roughPrimeFactors P n),
    routeE_lowPrimeFactors_union_roughPrimeFactors]

/-! ## Exact pair-stability on the friable sector -/

/-- Every prime factor of `n` lies at or below the moving seam `z`. -/
def routeEPrimeSupportFriable (z n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ≤ z

/-- Upward adjacent-grade entropy-complement relation on the two-sided friable sector. -/
def routeEEntropyComplementUpRelation
    (z : ℕ) (shell : ℕ → ℕ → Prop) (n q : ℕ) : Prop :=
  Squarefree n ∧ Squarefree q ∧
    routeEPrimeSupportFriable z n ∧ routeEPrimeSupportFriable z q ∧
    Nat.Coprime n q ∧ shell n q ∧ cardFactors q = cardFactors n + 1

/-- Downward adjacent-grade entropy-complement relation on the two-sided friable sector. -/
def routeEEntropyComplementDownRelation
    (z : ℕ) (shell : ℕ → ℕ → Prop) (n q : ℕ) : Prop :=
  Squarefree n ∧ Squarefree q ∧
    routeEPrimeSupportFriable z n ∧ routeEPrimeSupportFriable z q ∧
    Nat.Coprime n q ∧ shell n q ∧ cardFactors n = cardFactors q + 1

/-- With a symmetric physical shell, upward and downward certificates are exact endpoint swaps.
Freshness reverses by coprimality symmetry, and the complementary breadth equation needs no new
reservoir choice because each endpoint has its own intrinsic low/rough split. -/
theorem routeE_entropyComplement_up_iff_down_swap
    (z : ℕ) (shell : ℕ → ℕ → Prop)
    (hshell : ∀ a b, shell a b ↔ shell b a) (n q : ℕ) :
    routeEEntropyComplementUpRelation z shell n q ↔
      routeEEntropyComplementDownRelation z shell q n := by
  constructor
  · rintro ⟨hn, hq, hfn, hfq, hfresh, hs, hgrade⟩
    exact ⟨hq, hn, hfq, hfn, hfresh.symm, (hshell n q).mp hs, hgrade⟩
  · rintro ⟨hq, hn, hfq, hfn, hfresh, hs, hgrade⟩
    exact ⟨hn, hq, hfn, hfq, hfresh.symm, (hshell q n).mp hs, hgrade⟩

/-- Target factorization in the upward relation is the intrinsic cutoff split. -/
theorem routeE_entropyComplement_up_target_intrinsicFactorization
    (P z : ℕ) (shell : ℕ → ℕ → Prop) {n q : ℕ}
    (h : routeEEntropyComplementUpRelation z shell n q) :
    q = routeELowPart P q * routeERoughPart P q := by
  exact (routeE_lowPart_mul_roughPart_eq_of_squarefree P h.2.1).symm

/-- Source factorization used after reversal is likewise intrinsic, rather than reuse of the
forward endpoint's inserted reservoir. -/
theorem routeE_entropyComplement_up_source_intrinsicFactorization
    (P z : ℕ) (shell : ℕ → ℕ → Prop) {n q : ℕ}
    (h : routeEEntropyComplementUpRelation z shell n q) :
    n = routeELowPart P n * routeERoughPart P n := by
  exact (routeE_lowPart_mul_roughPart_eq_of_squarefree P h.1).symm

/-- Every upward pair-stable certificate reverses squarefree Möbius sign. -/
theorem routeE_entropyComplement_up_reverses_moebius
    (z : ℕ) (shell : ℕ → ℕ → Prop) {n q : ℕ}
    (h : routeEEntropyComplementUpRelation z shell n q) :
    (μ q : ℤ) = -(μ n : ℤ) := by
  exact moebius_eq_neg_of_cardFactors_succ h.1 h.2.1 h.2.2.2.2.2.2

/-- Symmetric physical window requiring each endpoint to admit the other's displacement. -/
def routeESymmetricRadiusShell (h : ℕ → ℕ) (n q : ℕ) : Prop :=
  Nat.dist n q ≤ h n ∧ Nat.dist n q ≤ h q

theorem routeE_symmetricRadiusShell_comm (h : ℕ → ℕ) (n q : ℕ) :
    routeESymmetricRadiusShell h n q ↔ routeESymmetricRadiusShell h q n := by
  simp only [routeESymmetricRadiusShell, Nat.dist_comm]
  exact and_comm

/-- Exact pair-stability for the endpoint-symmetric radius shell. -/
theorem routeE_entropyComplement_radius_up_iff_down_swap
    (z : ℕ) (h : ℕ → ℕ) (n q : ℕ) :
    routeEEntropyComplementUpRelation z (routeESymmetricRadiusShell h) n q ↔
      routeEEntropyComplementDownRelation z (routeESymmetricRadiusShell h) q n :=
  routeE_entropyComplement_up_iff_down_swap z _
    (routeE_symmetricRadiusShell_comm h) n q

/-! ## Exact one-large-prime seam localization -/

/-- Upward seam relation: terminal is friable, while source may carry the large seam prime. -/
def routeEEntropyComplementSeamUpRelation
    (z : ℕ) (shell : ℕ → ℕ → Prop) (n q : ℕ) : Prop :=
  Squarefree n ∧ Squarefree q ∧ routeEPrimeSupportFriable z q ∧
    Nat.Coprime n q ∧ shell n q ∧ cardFactors q = cardFactors n + 1

/-- Downward seam relation with a friable target. -/
def routeEEntropyComplementSeamDownRelation
    (z : ℕ) (shell : ℕ → ℕ → Prop) (n q : ℕ) : Prop :=
  Squarefree n ∧ Squarefree q ∧ routeEPrimeSupportFriable z q ∧
    Nat.Coprime n q ∧ shell n q ∧ cardFactors n = cardFactors q + 1

/-- For a target-friable seam edge, reverse certification exists exactly when its source is also
friable. Thus endpoint factorization asymmetry is localized to the literal nonfriable sector. -/
theorem routeE_entropyComplement_seam_reverse_iff_sourceFriable
    (z : ℕ) (shell : ℕ → ℕ → Prop)
    (hshell : ∀ a b, shell a b ↔ shell b a) {n q : ℕ}
    (h : routeEEntropyComplementSeamUpRelation z shell n q) :
    routeEEntropyComplementSeamDownRelation z shell q n ↔
      routeEPrimeSupportFriable z n := by
  constructor
  · intro hreverse
    exact hreverse.2.2.1
  · intro hnFriable
    exact ⟨h.2.1, h.1, hnFriable, h.2.2.2.1.symm,
      (hshell n q).mp h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Non-reversal is therefore exactly nonfriability of the original source. -/
theorem routeE_entropyComplement_seam_not_reverse_iff_sourceNonfriable
    (z : ℕ) (shell : ℕ → ℕ → Prop)
    (hshell : ∀ a b, shell a b ↔ shell b a) {n q : ℕ}
    (h : routeEEntropyComplementSeamUpRelation z shell n q) :
    ¬routeEEntropyComplementSeamDownRelation z shell q n ↔
      ¬routeEPrimeSupportFriable z n := by
  rw [routeE_entropyComplement_seam_reverse_iff_sourceFriable z shell hshell h]

end

end RHTower
