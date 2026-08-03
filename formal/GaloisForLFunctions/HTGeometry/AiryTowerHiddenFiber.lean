import GaloisForLFunctions.HTGeometry.AiryTowerFiniteFiber
import GaloisForLFunctions.HTGeometry.AiryTowerSeparatedCore

/-!
# Exact hidden fibres on the leading-separated locus

The core sees the first factor of each ordered factorization and forgets its complete tail.  This
file packages tails including the empty factorization of one, constructs the corresponding full
divisor chains, proves injectivity of the construction, and proves the exact product cardinality
for a finite labelled family.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

/-- Ordered multiplicative tail, allowing the unique empty factorization of one. -/
@[ext] structure OrderedFactorizationTail (R : ℕ) where
  factors : List ℕ
  factor_ge_two : ∀ a ∈ factors, 2 ≤ a
  prod_eq : factors.prod = R

namespace OrderedFactorizationTail

/-- A nonempty tail is an ordinary ordered factorization. -/
def toOrderedFactorization {R : ℕ} (t : OrderedFactorizationTail R)
    (hne : t.factors ≠ []) : OrderedFactorization R where
  factors := t.factors
  nonempty := hne
  factor_ge_two := t.factor_ge_two
  prod_eq := t.prod_eq

/-- Ordinary ordered factorizations embed as nonempty tails. -/
def ofOrderedFactorization {R : ℕ} (f : OrderedFactorization R) :
    OrderedFactorizationTail R where
  factors := f.factors
  factor_ge_two := f.factor_ge_two
  prod_eq := f.prod_eq

/-- Empty tail of the unit ramification. -/
def unit : OrderedFactorizationTail 1 where
  factors := []
  factor_ge_two := by simp
  prod_eq := by simp

/-- Ordered factorizations at fixed ramification form a finite type. -/
theorem finite_orderedFactorization (R : ℕ) : Finite (OrderedFactorization R) := by
  letI : Finite (StrictDivisorChain R) := finite_strictDivisorChain R
  apply Finite.of_injective OrderedFactorization.toStrictDivisorChain
  intro f g h
  apply OrderedFactorization.ext
  have := congrArg StrictDivisorChain.factors h
  simpa using this

/-- A tail is either the empty factorization of one or a nonempty ordered factorization. -/
def encode {R : ℕ} (t : OrderedFactorizationTail R) :
    { _u : Unit // R = 1 } ⊕ OrderedFactorization R := by
  by_cases hne : t.factors ≠ []
  · exact Sum.inr (t.toOrderedFactorization hne)
  · have hempty : t.factors = [] := not_ne_iff.mp hne
    left
    refine ⟨(), ?_⟩
    rw [← t.prod_eq, hempty]
    simp

/-- Tail encoding is injective. -/
theorem encode_injective {R : ℕ} : Function.Injective (@encode R) := by
  intro s t h
  by_cases hs : s.factors ≠ []
  · by_cases ht : t.factors ≠ []
    · have hst : s.toOrderedFactorization hs = t.toOrderedFactorization ht := by
        simpa [encode, hs, ht] using h
      apply OrderedFactorizationTail.ext
      exact congrArg OrderedFactorization.factors hst
    · simp [encode, hs, ht] at h
  · by_cases ht : t.factors ≠ []
    · simp [encode, hs, ht] at h
    · apply OrderedFactorizationTail.ext
      rw [not_ne_iff.mp hs, not_ne_iff.mp ht]

/-- Ordered tails at fixed product form a finite type. -/
theorem finite (R : ℕ) : Finite (OrderedFactorizationTail R) := by
  letI : Finite (OrderedFactorization R) := finite_orderedFactorization R
  apply Finite.of_injective encode
  exact encode_injective

attribute [local instance] OrderedFactorizationTail.finite

/-- Airy-tower count, with the empty tail at ramification one included. -/
noncomputable def airyTowerCount (R : ℕ) : ℕ := Nat.card (OrderedFactorizationTail R)

theorem airyTowerCount_one : airyTowerCount 1 = 1 := by
  have hsubsingleton : Subsingleton (OrderedFactorizationTail 1) := by
    constructor
    intro s t
    apply OrderedFactorizationTail.ext
    have hallOne : ∀ a ∈ s.factors, a = 1 := by
      intro a ha
      have hdvd : a ∣ 1 := by rw [← s.prod_eq]; exact List.dvd_prod ha
      exact Nat.eq_one_of_dvd_one hdvd
    have sempty : s.factors = [] := by
      by_contra hs
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil s.factors hs
      have htwo := s.factor_ge_two a ha
      have hone := hallOne a ha
      omega
    have tempty : t.factors = [] := by
      by_contra ht
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil t.factors ht
      have hdvd : a ∣ 1 := by rw [← t.prod_eq]; exact List.dvd_prod ha
      have hone := Nat.eq_one_of_dvd_one hdvd
      have htwo := t.factor_ge_two a ha
      omega
    rw [sempty, tempty]
  rw [airyTowerCount, Nat.card_eq_one_iff_unique]
  exact ⟨hsubsingleton, ⟨unit⟩⟩

/-- Above ramification one, allowing an empty tail adds nothing. -/
def equivOrderedFactorization {R : ℕ} (hR : 1 < R) :
    OrderedFactorizationTail R ≃ OrderedFactorization R where
  toFun t := t.toOrderedFactorization (by
    intro hempty
    have hprod := t.prod_eq
    rw [hempty] at hprod
    simp at hprod
    omega)
  invFun := ofOrderedFactorization
  left_inv := by
    intro t
    apply OrderedFactorizationTail.ext
    rfl
  right_inv := by
    intro f
    apply OrderedFactorization.ext
    rfl

/-- Tail count agrees with ordinary nonempty ordered-factorization count above one. -/
theorem airyTowerCount_eq_orderedFactorization {R : ℕ} (hR : 1 < R) :
    airyTowerCount R = Nat.card (OrderedFactorization R) := by
  rw [airyTowerCount, Nat.card_congr (equivOrderedFactorization hR)]

end OrderedFactorizationTail

/-- Labelled leading-separated data, with `Rᵢ = aᵢ qᵢ`. -/
structure SeparatedFiberDatum (n : ℕ) where
  ramification : Fin n → ℕ
  firstFactor : Fin n → ℕ
  tailRamification : Fin n → ℕ
  firstFactor_ge_two : ∀ i, 2 ≤ firstFactor i
  ramification_eq : ∀ i, ramification i = firstFactor i * tailRamification i

namespace SeparatedFiberDatum

/-- The first quotient in the factor list is exactly the first factor stored by `toAiryHead`. -/
theorem headD_factors_eq_toAiryHead_firstFactor {R : ℕ} (chain : StrictDivisorChain R) :
    chain.factors.headD 1 = chain.toAiryHead.firstFactor := by
  cases chain <;> simp [StrictDivisorChain.factors, StrictDivisorChain.toAiryHead]

/-- Complete hidden choices of all ordered factorization tails. -/
def HiddenFiber {n : ℕ} (d : SeparatedFiberDatum n) : Type :=
  ∀ i, OrderedFactorizationTail (d.tailRamification i)

instance {n : ℕ} (d : SeparatedFiberDatum n) : Finite d.HiddenFiber := by
  letI tailFinite (i : Fin n) : Finite (OrderedFactorizationTail (d.tailRamification i)) :=
    OrderedFactorizationTail.finite _
  unfold HiddenFiber
  infer_instance

/-- Full ordered factorization at a label, obtained by adjoining the visible first factor. -/
def fullFactorization {n : ℕ} (d : SeparatedFiberDatum n) (h : d.HiddenFiber) (i : Fin n) :
    OrderedFactorization (d.ramification i) where
  factors := d.firstFactor i :: (h i).factors
  nonempty := by simp
  factor_ge_two := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact d.firstFactor_ge_two i
    · exact (h i).factor_ge_two a ha
  prod_eq := by
    simp only [List.prod_cons, (h i).prod_eq]
    exact (d.ramification_eq i).symm

/-- Full strict divisor chain represented by a hidden tail. -/
def fullChain {n : ℕ} (d : SeparatedFiberDatum n) (h : d.HiddenFiber) (i : Fin n) :
    StrictDivisorChain (d.ramification i) :=
  (d.fullFactorization h i).toStrictDivisorChain

/-- Extracting factors from the constructed chain returns visible head followed by exact tail. -/
@[simp] theorem factors_fullChain {n : ℕ} (d : SeparatedFiberDatum n)
    (h : d.HiddenFiber) (i : Fin n) :
    (d.fullChain h i).factors = d.firstFactor i :: (h i).factors := by
  exact (d.fullFactorization h i).factors_toStrictDivisorChain

/-- The visible first factor of every constructed full chain is the prescribed one. -/
@[simp] theorem fullChain_firstFactor {n : ℕ} (d : SeparatedFiberDatum n)
    (h : d.HiddenFiber) (i : Fin n) :
    (d.fullChain h i).toAiryHead.firstFactor = d.firstFactor i := by
  rw [← headD_factors_eq_toAiryHead_firstFactor, d.factors_fullChain]
  simp

/-- Complete labelled divisor-chain families remember every hidden tail. -/
theorem fullChain_injective {n : ℕ} (d : SeparatedFiberDatum n) :
    Function.Injective (fun h : d.HiddenFiber => fun i => d.fullChain h i) := by
  intro s t hst
  funext i
  apply OrderedFactorizationTail.ext
  have hi := congrFun hst i
  have hfactors := congrArg StrictDivisorChain.factors hi
  simpa using hfactors

/-- Leading-separated core matrix; only visible first factors enter. -/
def coreEdge {n : ℕ} (d : SeparatedFiberDatum n) (i j : Fin n) : ℕ :=
  d.ramification i * d.ramification j / min (d.firstFactor i) (d.firstFactor j)

/-- Core edge actually computed from the full hidden divisor chains. -/
def realizedCoreEdge {n : ℕ} (d : SeparatedFiberDatum n) (h : d.HiddenFiber)
    (i j : Fin n) : ℕ :=
  separatedEdge (d.fullChain h i).toAiryHead (d.fullChain h j).toAiryHead

/-- Every full hidden realization computes the prescribed visible reciprocal-min core. -/
theorem realizedCoreEdge_eq_coreEdge {n : ℕ} (d : SeparatedFiberDatum n)
    (h : d.HiddenFiber) (i j : Fin n) :
    d.realizedCoreEdge h i j = d.coreEdge i j := by
  simp [realizedCoreEdge, coreEdge, separatedEdge]

/-- Hidden tails leave every actually computed leading-separated core edge unchanged. -/
theorem realizedCoreEdge_independent_of_hidden {n : ℕ} (d : SeparatedFiberDatum n)
    (s t : d.HiddenFiber) (i j : Fin n) :
    d.realizedCoreEdge s i j = d.realizedCoreEdge t i j := by
  rw [d.realizedCoreEdge_eq_coreEdge, d.realizedCoreEdge_eq_coreEdge]

/-- Exact separated hidden-fibre product law. -/
theorem hiddenFiber_card {n : ℕ} (d : SeparatedFiberDatum n) :
    Nat.card d.HiddenFiber = ∏ i, OrderedFactorizationTail.airyTowerCount (d.tailRamification i) := by
  rw [HiddenFiber, Nat.card_pi]
  rfl

end SeparatedFiberDatum

end IrregularStokes
end GaloisForLFunctions
